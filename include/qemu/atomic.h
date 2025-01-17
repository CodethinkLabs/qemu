/*
 * Simple interface for atomic operations.
 *
 * Copyright (C) 2013 Red Hat, Inc.
 *
 * Author: Paolo Bonzini <pbonzini@redhat.com>
 *
 * This work is licensed under the terms of the GNU GPL, version 2 or later.
 * See the COPYING file in the top-level directory.
 *
 */

#ifndef __QEMU_ATOMIC_H
#define __QEMU_ATOMIC_H 1

#include "qemu/compiler.h"

/* For C11 atomic ops */

/* Compiler barrier */
#define barrier()   ({ asm volatile("" ::: "memory"); (void)0; })

#ifndef __ATOMIC_RELAXED

/*
 * We use GCC builtin if it's available, as that can use mfence on
 * 32-bit as well, e.g. if built with -march=pentium-m. However, on
 * i386 the spec is buggy, and the implementation followed it until
 * 4.3 (http://gcc.gnu.org/bugzilla/show_bug.cgi?id=36793).
 */
#if defined(__i386__) || defined(__x86_64__)
#if !QEMU_GNUC_PREREQ(4, 4)
#if defined __x86_64__
#define smp_mb()    ({ asm volatile("mfence" ::: "memory"); (void)0; })
#else
#define smp_mb()    ({ asm volatile("lock; addl $0,0(%%esp) " ::: "memory"); (void)0; })
#endif
#endif
#endif


#ifdef __alpha__
#define smp_read_barrier_depends()   asm volatile("mb":::"memory")
#endif

#if defined(__i386__) || defined(__x86_64__) || defined(__s390x__)

/*
 * Because of the strongly ordered storage model, wmb() and rmb() are nops
 * here (a compiler barrier only).  QEMU doesn't do accesses to write-combining
 * qemu memory or non-temporal load/stores from C code.
 */
#define smp_wmb()   barrier()
#define smp_rmb()   barrier()

/*
 * __sync_lock_test_and_set() is documented to be an acquire barrier only,
 * but it is a full barrier at the hardware level.  Add a compiler barrier
 * to make it a full barrier also at the compiler level.
 */
#define atomic_xchg(ptr, i)    (barrier(), __sync_lock_test_and_set(ptr, i))

/*
 * Load/store with Java volatile semantics.
 */
#define atomic_mb_set(ptr, i)  ((void)atomic_xchg(ptr, i))

#elif defined(_ARCH_PPC)

/*
 * We use an eieio() for wmb() on powerpc.  This assumes we don't
 * need to order cacheable and non-cacheable stores with respect to
 * each other.
 *
 * smp_mb has the same problem as on x86 for not-very-new GCC
 * (http://patchwork.ozlabs.org/patch/126184/, Nov 2011).
 */
#define smp_wmb()   ({ asm volatile("eieio" ::: "memory"); (void)0; })
#if defined(__powerpc64__)
#define smp_rmb()   ({ asm volatile("lwsync" ::: "memory"); (void)0; })
#else
#define smp_rmb()   ({ asm volatile("sync" ::: "memory"); (void)0; })
#endif
#define smp_mb()    ({ asm volatile("sync" ::: "memory"); (void)0; })

#endif /* _ARCH_PPC */

#endif /* __ATOMIC_RELAXED (C11 atomics) */
/*
 * For (host) platforms we don't have explicit barrier definitions
 * for, we use the gcc __sync_synchronize() primitive to generate a
 * full barrier.  This should be safe on all platforms, though it may
 * be overkill for smp_wmb() and smp_rmb().
 */
#ifndef smp_mb
#define smp_mb()    __sync_synchronize()
#endif

#ifndef smp_wmb
#ifdef __ATOMIC_RELEASE
/* __atomic_thread_fence does not include a compiler barrier; instead,
 * the barrier is part of __atomic_load/__atomic_store's "volatile-like"
 * semantics. If smp_wmb() is a no-op, absence of the barrier means that
 * the compiler is free to reorder stores on each side of the barrier.
 * Add one here, and similarly in smp_rmb() and smp_read_barrier_depends().
 */
#define smp_wmb()   ({ barrier(); __atomic_thread_fence(__ATOMIC_RELEASE); barrier(); })
#else
#define smp_wmb()   __sync_synchronize()
#endif
#endif

#ifndef smp_rmb
#ifdef __ATOMIC_ACQUIRE
#define smp_rmb()   ({ barrier(); __atomic_thread_fence(__ATOMIC_ACQUIRE); barrier(); })
#else
#define smp_rmb()   __sync_synchronize()
#endif
#endif

#ifndef smp_read_barrier_depends
#ifdef __ATOMIC_CONSUME
#define smp_read_barrier_depends()   ({ barrier(); __atomic_thread_fence(__ATOMIC_CONSUME); barrier(); })
#else
#define smp_read_barrier_depends()   barrier()
#endif
#endif

/* While aligned reads should be atomic we need to use an explicit
 * builtin when running under ThreadSanitizer so it knows what is
 * safely atomic.
 */
#ifndef atomic_read
#ifdef __USING_TSAN
#define atomic_read(ptr)                          \
    ({                                            \
    typeof(*ptr) _val;                            \
     __atomic_load(ptr, &_val, __ATOMIC_CONSUME); \
    _val;                                         \
    })
#else
#define atomic_read(ptr)       (*(__typeof__(*ptr) volatile*) (ptr))
#endif
#endif

#ifndef atomic_set
#if __USING_TSAN
#define atomic_set(ptr, i)  do {                        \
    typeof(*ptr) _val = (i);                            \
    __atomic_store(ptr, &_val, __ATOMIC_RELEASE);       \
} while(0)
#else
#define atomic_set(ptr, i)     ((*(__typeof__(*ptr) volatile*) (ptr)) = (i))
#endif
#endif

/**
 * atomic_rcu_read - reads a RCU-protected pointer to a local variable
 * into a RCU read-side critical section. The pointer can later be safely
 * dereferenced within the critical section.
 *
 * This ensures that the pointer copy is invariant thorough the whole critical
 * section.
 *
 * Inserts memory barriers on architectures that require them (currently only
 * Alpha) and documents which pointers are protected by RCU.
 *
 * Unless the __ATOMIC_CONSUME memory order is available, atomic_rcu_read also
 * includes a compiler barrier to ensure that value-speculative optimizations
 * (e.g. VSS: Value Speculation Scheduling) does not perform the data read
 * before the pointer read by speculating the value of the pointer.  On new
 * enough compilers, atomic_load takes care of such concern about
 * dependency-breaking optimizations.
 *
 * Should match atomic_rcu_set(), atomic_xchg(), atomic_cmpxchg().
 */
#ifndef atomic_rcu_read
#ifdef __ATOMIC_CONSUME
#define atomic_rcu_read(ptr)    ({                \
    typeof(*ptr) _val;                            \
     __atomic_load(ptr, &_val, __ATOMIC_CONSUME); \
    _val;                                         \
})
#else
#define atomic_rcu_read(ptr)    ({                \
    typeof(*ptr) _val = atomic_read(ptr);         \
    smp_read_barrier_depends();                   \
    _val;                                         \
})
#endif
#endif

/**
 * atomic_rcu_set - assigns (publicizes) a pointer to a new data structure
 * meant to be read by RCU read-side critical sections.
 *
 * Documents which pointers will be dereferenced by RCU read-side critical
 * sections and adds the required memory barriers on architectures requiring
 * them. It also makes sure the compiler does not reorder code initializing the
 * data structure before its publication.
 *
 * Should match atomic_rcu_read().
 */
#ifndef atomic_rcu_set
#ifdef __ATOMIC_RELEASE
#define atomic_rcu_set(ptr, i)  do {              \
    typeof(*ptr) _val = (i);                      \
    __atomic_store(ptr, &_val, __ATOMIC_RELEASE); \
} while(0)
#else
#define atomic_rcu_set(ptr, i)  do {              \
    smp_wmb();                                    \
    atomic_set(ptr, i);                           \
} while (0)
#endif
#endif

/* These have the same semantics as Java volatile variables.
 * See http://gee.cs.oswego.edu/dl/jmm/cookbook.html:
 * "1. Issue a StoreStore barrier (wmb) before each volatile store."
 *  2. Issue a StoreLoad barrier after each volatile store.
 *     Note that you could instead issue one before each volatile load, but
 *     this would be slower for typical programs using volatiles in which
 *     reads greatly outnumber writes. Alternatively, if available, you
 *     can implement volatile store as an atomic instruction (for example
 *     XCHG on x86) and omit the barrier. This may be more efficient if
 *     atomic instructions are cheaper than StoreLoad barriers.
 *  3. Issue LoadLoad and LoadStore barriers after each volatile load."
 *
 * If you prefer to think in terms of "pairing" of memory barriers,
 * an atomic_mb_read pairs with an atomic_mb_set.
 *
 * And for the few ia64 lovers that exist, an atomic_mb_read is a ld.acq,
 * while an atomic_mb_set is a st.rel followed by a memory barrier.
 *
 * These are a bit weaker than __atomic_load/store with __ATOMIC_SEQ_CST
 * (see docs/atomics.txt), and I'm not sure that __ATOMIC_ACQ_REL is enough.
 * Just always use the barriers manually by the rules above.
 */
#ifndef atomic_mb_read
#define atomic_mb_read(ptr)    ({           \
    typeof(*ptr) _val = atomic_read(ptr);   \
    smp_rmb();                              \
    _val;                                   \
})
#endif

#ifndef atomic_mb_set
#define atomic_mb_set(ptr, i)  do {         \
    smp_wmb();                              \
    atomic_set(ptr, i);                     \
    smp_mb();                               \
} while (0)
#endif

#ifndef atomic_xchg
#if defined(__clang__)
#define atomic_xchg(ptr, i)    __sync_swap(ptr, i)
#elif defined(__ATOMIC_SEQ_CST)
/* Q: does __ATOMIC_SEQ_CST imply memory ordering with non-atomic
 * operations? */
#define atomic_xchg(ptr, i)    ({                           \
    typeof(*ptr) _new = (i), _old;                          \
    __atomic_exchange(ptr, &_new, &_old, __ATOMIC_SEQ_CST); \
    _old;                                                   \
})
#else
/* __sync_lock_test_and_set() is documented to be an acquire barrier only.  */
#define atomic_xchg(ptr, i)    (smp_mb(), __sync_lock_test_and_set(ptr, i))
#endif
#endif

/* Provide shorter names for GCC atomic builtins.  */
#define atomic_fetch_inc(ptr)  __sync_fetch_and_add(ptr, 1)
#define atomic_fetch_dec(ptr)  __sync_fetch_and_add(ptr, -1)
#define atomic_fetch_add       __sync_fetch_and_add
#define atomic_fetch_sub       __sync_fetch_and_sub
#define atomic_fetch_and       __sync_fetch_and_and
#define atomic_fetch_or        __sync_fetch_and_or
#define atomic_cmpxchg         __sync_val_compare_and_swap

/* And even shorter names that return void.  */
#define atomic_inc(ptr)        ((void) __sync_fetch_and_add(ptr, 1))
#define atomic_dec(ptr)        ((void) __sync_fetch_and_add(ptr, -1))
#define atomic_add(ptr, n)     ((void) __sync_fetch_and_add(ptr, n))
#define atomic_sub(ptr, n)     ((void) __sync_fetch_and_sub(ptr, n))
#define atomic_and(ptr, n)     ((void) __sync_fetch_and_and(ptr, n))
#define atomic_or(ptr, n)      ((void) __sync_fetch_and_or(ptr, n))

#endif
