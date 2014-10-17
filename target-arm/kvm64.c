/*
 * ARM implementation of KVM hooks, 64 bit specific code
 *
 * Copyright Mian-M. Hamayun 2013, Virtual Open Systems
 * Copyright Alex Bennée 2014, Linaro
 *
 * This work is licensed under the terms of the GNU GPL, version 2 or later.
 * See the COPYING file in the top-level directory.
 *
 */

#include <stdio.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <asm/ptrace.h>

#include <linux/elf.h>
#include <linux/kvm.h>

#include "config-host.h"
#include "qemu-common.h"
#include "qemu/timer.h"
#include "qemu/host-utils.h"
#include "qemu/error-report.h"
#include "exec/gdbstub.h"
#include "sysemu/sysemu.h"
#include "sysemu/kvm.h"
#include "kvm_arm.h"
#include "cpu.h"
#include "internals.h"
#include "hw/arm/arm.h"

static bool have_guest_debug;
/* Max and current break/watch point counts */
int max_hw_bp, max_hw_wp;
int cur_hw_bp, cur_hw_wp;
struct kvm_guest_debug_arch guest_debug_registers;

/**
 * kvm_arm_init_debug() - check for guest debug capabilities
 * @cs: CPUState
 *
 * kvm_check_extension returns 0 if we have no debug registers or the
 * number we have.
 *
 */
static void kvm_arm_init_debug(CPUState *cs)
{
    have_guest_debug = kvm_check_extension(cs->kvm_state,
                                           KVM_CAP_SET_GUEST_DEBUG);
    max_hw_wp = kvm_check_extension(cs->kvm_state, KVM_CAP_GUEST_DEBUG_HW_WPS);
    max_hw_bp = kvm_check_extension(cs->kvm_state, KVM_CAP_GUEST_DEBUG_HW_BPS);
    return;
}

/**
 * insert_hw_breakpoint()
 * @addr: address of breakpoint
 *
 * See ARM ARM D2.9.1 for details but here we are only going to create
 * simple un-linked breakpoints (i.e. we don't chain breakpoints
 * together to match address and context or vmid). The hardware is
 * capable of fancier matching but that will require exposing that
 * fanciness to GDB's interface
 *
 * D7.3.2 DBGBCR<n>_EL1, Debug Breakpoint Control Registers
 *
 *  31  24 23  20 19   16 15 14  13  12   9 8   5 4    3 2   1  0
 * +------+------+-------+-----+----+------+-----+------+-----+---+
 * | RES0 |  BT  |  LBN  | SSC | HMC| RES0 | BAS | RES0 | PMC | E |
 * +------+------+-------+-----+----+------+-----+------+-----+---+
 *
 * BT: Breakpoint type (0 = unlinked address match)
 * LBN: Linked BP number (0 = unused)
 * SSC/HMC/PMC: Security, Higher and Priv access control (Table D-12)
 * BAS: Byte Address Select (RES1 for AArch64)
 * E: Enable bit
 */
static int insert_hw_breakpoint(target_ulong addr)
{
    uint32_t bcr = 0x1; /* E=1, enable */
    if (cur_hw_bp >= max_hw_bp) {
        return -ENOBUFS;
    }
    bcr = deposit32(bcr, 1, 2, 0x3);   /* PMC = 11 */
    bcr = deposit32(bcr, 5, 4, 0xf);   /* BAS = RES1 */
    guest_debug_registers.dbg_bcr[cur_hw_bp] = bcr;
    guest_debug_registers.dbg_bvr[cur_hw_bp] = addr;
    cur_hw_bp++;
    return 0;
}

/**
 * delete_hw_breakpoint()
 * @pc: address of breakpoint
 *
 * Delete a breakpoint and shuffle any above down
 */

static int delete_hw_breakpoint(target_ulong pc)
{
    int i;
    for (i = 0; i < cur_hw_bp; i++) {
      if (guest_debug_registers.dbg_bvr[i] == pc) {
          while (i < cur_hw_bp) {
              if (i == max_hw_bp) {
                  guest_debug_registers.dbg_bvr[i] = 0;
                  guest_debug_registers.dbg_bcr[i] = 0;
              } else {
                  guest_debug_registers.dbg_bvr[i] =
                      guest_debug_registers.dbg_bvr[i + 1];
                  guest_debug_registers.dbg_bcr[i] =
                      guest_debug_registers.dbg_bcr[i + 1];
              }
              i++;
          }
          cur_hw_bp--;
          return 0;
      }
    }
    return -ENOENT;
}

/**
 * insert_hw_watchpoint()
 * @addr: address of watch point
 * @len: size of area
 * @type: type of watch point
 *
 * See ARM ARM D2.10. As with the breakpoints we can do some advanced
 * stuff if we want to. The watch points can be linked with the break
 * points above to make them context aware. However for simplicity
 * currently we only deal with simple read/write watch points.
 *
 * D7.3.11 DBGWCR<n>_EL1, Debug Watchpoint Control Registers
 *
 *  31  29 28   24 23  21  20  19 16 15 14  13   12  5 4   3 2   1  0
 * +------+-------+------+----+-----+-----+-----+-----+-----+-----+---+
 * | RES0 |  MASK | RES0 | WT | LBN | SSC | HMC | BAS | LSC | PAC | E |
 * +------+-------+------+----+-----+-----+-----+-----+-----+-----+---+
 *
 * MASK: num bits addr mask (0=none,01/10=res,11=3 bits (8 bytes))
 * WT: 0 - unlinked, 1 - linked (not currently used)
 * LBN: Linked BP number (not currently used)
 * SSC/HMC/PAC: Security, Higher and Priv access control (Table D-12)
 * BAS: Byte Address Select
 * LSC: Load/Store control (01: load, 10: store, 11: both)
 * E: Enable
 *
 * The bottom 2 bits of the value register are masked. Therefor to
 * break on an sizes smaller than unaligned byte you need to set
 * MASK=0, BAS=bit per byte in question. For larger regions (^2) you
 * need to ensure you mask the address as required and set BAS=0xff
 */

static int insert_hw_watchpoint(target_ulong addr,
                                target_ulong len, int type)
{
    uint32_t dbgwcr = 1; /* E=1, enable */
    uint64_t dbgwvr = addr & (~0x7ULL);

    if (cur_hw_wp >= max_hw_wp) {
        return -ENOBUFS;
    }

    /* PAC 00 is reserved, assume EL1 exception */
    dbgwcr = deposit32(dbgwcr, 1, 2, 1);

    switch (type) {
    case GDB_WATCHPOINT_READ:
        dbgwcr = deposit32(dbgwcr, 3, 2, 1);
        break;
    case GDB_WATCHPOINT_WRITE:
        dbgwcr = deposit32(dbgwcr, 3, 2, 2);
        break;
    case GDB_WATCHPOINT_ACCESS:
        dbgwcr = deposit32(dbgwcr, 3, 2, 3);
        break;
    default:
        g_assert_not_reached();
        break;
    }
    if (len <= 8) {
        /* we align the address and set the bits in BAS */
        int off = addr & 0x7;
        int bas = (1 << len)-1;
        dbgwcr = deposit32(dbgwcr, 5+off, 8-off, bas);
    } else {
        /* For ranges above 8 bytes we need to be a power of 2 */
        if (ctpop64(len)==1) {
            int bits = ctz64(len);
            dbgwvr &= ~((1 << bits)-1);
            dbgwcr = deposit32(dbgwcr, 24, 4, bits);
            dbgwcr = deposit32(dbgwcr, 5, 8, 0xff);
        } else {
            return -ENOBUFS;
        }
    }

    guest_debug_registers.dbg_wcr[cur_hw_wp] = dbgwcr;
    guest_debug_registers.dbg_wvr[cur_hw_wp] = dbgwvr;
    cur_hw_wp++;
    return 0;
}


static bool check_watchpoint_in_range(int i, target_ulong addr)
{
    uint32_t dbgwcr = guest_debug_registers.dbg_wcr[i];
    uint64_t addr_top, addr_bottom = guest_debug_registers.dbg_wvr[i];
    int bas = extract32(dbgwcr, 5, 8);
    int mask = extract32(dbgwcr, 24, 4);

    if (mask) {
        addr_top = addr_bottom + (1 << mask);
    } else {
        /* BAS must be contiguous but can offset against the base
         * address in DBGWVR */
        addr_bottom = addr_bottom + ctz32(bas);
        addr_top = addr_bottom + clo32(bas);
    }

    if (addr >= addr_bottom && addr <= addr_top ) {
        return true;
    }

    return false;
}

/**
 * delete_hw_watchpoint()
 * @addr: address of breakpoint
 *
 * Delete a breakpoint and shuffle any above down
 */

static int delete_hw_watchpoint(target_ulong addr,
                                target_ulong len, int type)
{
    int i;
    for (i = 0; i < cur_hw_wp; i++) {
        if (check_watchpoint_in_range(i, addr)) {
            while (i < cur_hw_wp) {
                if (i == max_hw_wp) {
                    guest_debug_registers.dbg_wvr[i] = 0;
                    guest_debug_registers.dbg_wcr[i] = 0;
                } else {
                    guest_debug_registers.dbg_wvr[i] =
                        guest_debug_registers.dbg_wvr[i + 1];
                    guest_debug_registers.dbg_wcr[i] =
                        guest_debug_registers.dbg_wcr[i + 1];
                }
                i++;
            }
            cur_hw_wp--;
            return 0;
        }
    }
    return -ENOENT;
}


int kvm_arch_insert_hw_breakpoint(target_ulong addr,
                                  target_ulong len, int type)
{
    switch (type) {
    case GDB_BREAKPOINT_HW:
        return insert_hw_breakpoint(addr);
        break;
    case GDB_WATCHPOINT_READ:
    case GDB_WATCHPOINT_WRITE:
    case GDB_WATCHPOINT_ACCESS:
        return insert_hw_watchpoint(addr, len, type);
    default:
        return -ENOSYS;
    }
}

int kvm_arch_remove_hw_breakpoint(target_ulong addr,
                                  target_ulong len, int type)
{
    switch (type) {
    case GDB_BREAKPOINT_HW:
        return delete_hw_breakpoint(addr);
        break;
    case GDB_WATCHPOINT_READ:
    case GDB_WATCHPOINT_WRITE:
    case GDB_WATCHPOINT_ACCESS:
        return delete_hw_watchpoint(addr, len, type);
    default:
        return -ENOSYS;
    }
}


void kvm_arch_remove_all_hw_breakpoints(void)
{
    memset((void *)&guest_debug_registers, 0, sizeof(guest_debug_registers));
    cur_hw_bp = 0;
    cur_hw_wp = 0;
}

void kvm_copy_hw_debug_data(struct kvm_guest_debug_arch *ptr)
{
    /* Compile time assert? */
    g_assert(sizeof(struct kvm_guest_debug_arch) == sizeof(guest_debug_registers));
    memcpy(ptr, &guest_debug_registers, sizeof(guest_debug_registers));
}

bool kvm_arm_hw_debug_active(CPUState *cs)
{
    return ( (cur_hw_bp > 0) || (cur_hw_wp >0) ) ? TRUE:FALSE;
}

bool kvm_arm_find_hw_breakpoint(CPUState *cpu, target_ulong pc)
{
  if (kvm_arm_hw_debug_active(cpu)) {
    int i;
    for (i=0; i<cur_hw_bp; i++) {
      if (guest_debug_registers.dbg_bvr[i] == pc) {
        return true;
      }
    }
  }
  return false;
}

bool kvm_arm_find_hw_watchpoint(CPUState *cpu, target_ulong addr)
{
  if (kvm_arm_hw_debug_active(cpu)) {
    int i;
    for (i=0; i<cur_hw_wp; i++) {
        if (check_watchpoint_in_range(i, addr)) {
                return true;
        }
    }
  }
  return false;
}


static inline void set_feature(uint64_t *features, int feature)
{
    *features |= 1ULL << feature;
}

bool kvm_arm_get_host_cpu_features(ARMHostCPUClass *ahcc)
{
    /* Identify the feature bits corresponding to the host CPU, and
     * fill out the ARMHostCPUClass fields accordingly. To do this
     * we have to create a scratch VM, create a single CPU inside it,
     * and then query that CPU for the relevant ID registers.
     * For AArch64 we currently don't care about ID registers at
     * all; we just want to know the CPU type.
     */
    int fdarray[3];
    uint64_t features = 0;
    /* Old kernels may not know about the PREFERRED_TARGET ioctl: however
     * we know these will only support creating one kind of guest CPU,
     * which is its preferred CPU type. Fortunately these old kernels
     * support only a very limited number of CPUs.
     */
    static const uint32_t cpus_to_try[] = {
        KVM_ARM_TARGET_AEM_V8,
        KVM_ARM_TARGET_FOUNDATION_V8,
        KVM_ARM_TARGET_CORTEX_A57,
        QEMU_KVM_ARM_TARGET_NONE
    };
    struct kvm_vcpu_init init;

    if (!kvm_arm_create_scratch_host_vcpu(cpus_to_try, fdarray, &init)) {
        return false;
    }

    ahcc->target = init.target;
    ahcc->dtb_compatible = "arm,arm-v8";

    kvm_arm_destroy_scratch_host_vcpu(fdarray);

   /* We can assume any KVM supporting CPU is at least a v8
     * with VFPv4+Neon; this in turn implies most of the other
     * feature bits.
     */
    set_feature(&features, ARM_FEATURE_V8);
    set_feature(&features, ARM_FEATURE_VFP4);
    set_feature(&features, ARM_FEATURE_NEON);
    set_feature(&features, ARM_FEATURE_AARCH64);

    ahcc->features = features;

    return true;
}

int kvm_arch_init_vcpu(CPUState *cs)
{
    int ret;
    ARMCPU *cpu = ARM_CPU(cs);

    if (cpu->kvm_target == QEMU_KVM_ARM_TARGET_NONE ||
        !object_dynamic_cast(OBJECT(cpu), TYPE_AARCH64_CPU)) {
        fprintf(stderr, "KVM is not supported for this guest CPU type\n");
        return -EINVAL;
    }

    /* Determine init features for this CPU */
    memset(cpu->kvm_init_features, 0, sizeof(cpu->kvm_init_features));
    if (cpu->start_powered_off) {
        cpu->kvm_init_features[0] |= 1 << KVM_ARM_VCPU_POWER_OFF;
    }
    if (kvm_check_extension(cs->kvm_state, KVM_CAP_ARM_PSCI_0_2)) {
        cpu->psci_version = 2;
        cpu->kvm_init_features[0] |= 1 << KVM_ARM_VCPU_PSCI_0_2;
    }
    if (!arm_feature(&cpu->env, ARM_FEATURE_AARCH64)) {
        cpu->kvm_init_features[0] |= 1 << KVM_ARM_VCPU_EL1_32BIT;
    }

    /* Do KVM_ARM_VCPU_INIT ioctl */
    ret = kvm_arm_vcpu_init(cs);
    if (ret) {
        return ret;
    }

    kvm_arm_init_debug(cs);

    return kvm_arm_init_cpreg_list(cpu);
}

bool kvm_arm_reg_syncs_via_cpreg_list(uint64_t regidx)
{
    /* Return true if the regidx is a register we should synchronize
     * via the cpreg_tuples array (ie is not a core reg we sync by
     * hand in kvm_arch_get/put_registers())
     */
    switch (regidx & KVM_REG_ARM_COPROC_MASK) {
    case KVM_REG_ARM_CORE:
        return false;
    default:
        return true;
    }
}

#define AARCH64_CORE_REG(x)   (KVM_REG_ARM64 | KVM_REG_SIZE_U64 | \
                 KVM_REG_ARM_CORE | KVM_REG_ARM_CORE_REG(x))

#define AARCH64_SIMD_CORE_REG(x)   (KVM_REG_ARM64 | KVM_REG_SIZE_U128 | \
                 KVM_REG_ARM_CORE | KVM_REG_ARM_CORE_REG(x))

#define AARCH64_SIMD_CTRL_REG(x)   (KVM_REG_ARM64 | KVM_REG_SIZE_U32 | \
                 KVM_REG_ARM_CORE | KVM_REG_ARM_CORE_REG(x))

int kvm_arch_put_registers(CPUState *cs, int level)
{
    struct kvm_one_reg reg;
    uint32_t fpr;
    uint64_t val;
    int i;
    int ret;
    unsigned int el;

    ARMCPU *cpu = ARM_CPU(cs);
    CPUARMState *env = &cpu->env;

    /* If we are in AArch32 mode then we need to copy the AArch32 regs to the
     * AArch64 registers before pushing them out to 64-bit KVM.
     */
    if (!is_a64(env)) {
        aarch64_sync_32_to_64(env);
    }

    for (i = 0; i < 31; i++) {
        reg.id = AARCH64_CORE_REG(regs.regs[i]);
        reg.addr = (uintptr_t) &env->xregs[i];
        ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
        if (ret) {
            return ret;
        }
    }

    /* KVM puts SP_EL0 in regs.sp and SP_EL1 in regs.sp_el1. On the
     * QEMU side we keep the current SP in xregs[31] as well.
     */
    aarch64_save_sp(env, 1);

    reg.id = AARCH64_CORE_REG(regs.sp);
    reg.addr = (uintptr_t) &env->sp_el[0];
    ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    reg.id = AARCH64_CORE_REG(sp_el1);
    reg.addr = (uintptr_t) &env->sp_el[1];
    ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    /* Note that KVM thinks pstate is 64 bit but we use a uint32_t */
    if (is_a64(env)) {
        val = pstate_read(env);
    } else {
        val = cpsr_read(env);
    }
    reg.id = AARCH64_CORE_REG(regs.pstate);
    reg.addr = (uintptr_t) &val;
    ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    reg.id = AARCH64_CORE_REG(regs.pc);
    reg.addr = (uintptr_t) &env->pc;
    ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    reg.id = AARCH64_CORE_REG(elr_el1);
    reg.addr = (uintptr_t) &env->elr_el[1];
    ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    /* Saved Program State Registers
     *
     * Before we restore from the banked_spsr[] array we need to
     * ensure that any modifications to env->spsr are correctly
     * reflected in the banks.
     */
    el = arm_current_el(env);
    if (el > 0 && !is_a64(env)) {
        i = bank_number(env->uncached_cpsr & CPSR_M);
        env->banked_spsr[i] = env->spsr;
    }

    /* KVM 0-4 map to QEMU banks 1-5 */
    for (i = 0; i < KVM_NR_SPSR; i++) {
        reg.id = AARCH64_CORE_REG(spsr[i]);
        reg.addr = (uintptr_t) &env->banked_spsr[i + 1];
        ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
        if (ret) {
            return ret;
        }
    }

    /* Advanced SIMD and FP registers
     * We map Qn = regs[2n+1]:regs[2n]
     */
    for (i = 0; i < 32; i++) {
        int rd = i << 1;
        uint64_t fp_val[2];
#ifdef HOST_WORDS_BIGENDIAN
        fp_val[0] = env->vfp.regs[rd + 1];
        fp_val[1] = env->vfp.regs[rd];
#else
        fp_val[1] = env->vfp.regs[rd + 1];
        fp_val[0] = env->vfp.regs[rd];
#endif
        reg.id = AARCH64_SIMD_CORE_REG(fp_regs.vregs[i]);
        reg.addr = (uintptr_t)(&fp_val);
        ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
        if (ret) {
            return ret;
        }
    }

    reg.addr = (uintptr_t)(&fpr);
    fpr = vfp_get_fpsr(env);
    reg.id = AARCH64_SIMD_CTRL_REG(fp_regs.fpsr);
    ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    fpr = vfp_get_fpcr(env);
    reg.id = AARCH64_SIMD_CTRL_REG(fp_regs.fpcr);
    ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    if (!write_list_to_kvmstate(cpu)) {
        return EINVAL;
    }

    kvm_arm_sync_mpstate_to_kvm(cpu);

    return ret;
}

int kvm_arch_get_registers(CPUState *cs)
{
    struct kvm_one_reg reg;
    uint64_t val;
    uint32_t fpr;
    unsigned int el;
    int i;
    int ret;

    ARMCPU *cpu = ARM_CPU(cs);
    CPUARMState *env = &cpu->env;

    for (i = 0; i < 31; i++) {
        reg.id = AARCH64_CORE_REG(regs.regs[i]);
        reg.addr = (uintptr_t) &env->xregs[i];
        ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
        if (ret) {
            return ret;
        }
    }

    reg.id = AARCH64_CORE_REG(regs.sp);
    reg.addr = (uintptr_t) &env->sp_el[0];
    ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    reg.id = AARCH64_CORE_REG(sp_el1);
    reg.addr = (uintptr_t) &env->sp_el[1];
    ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    reg.id = AARCH64_CORE_REG(regs.pstate);
    reg.addr = (uintptr_t) &val;
    ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    env->aarch64 = ((val & PSTATE_nRW) == 0);
    if (is_a64(env)) {
        pstate_write(env, val);
    } else {
        env->uncached_cpsr = val & CPSR_M;
        cpsr_write(env, val, 0xffffffff);
    }

    /* KVM puts SP_EL0 in regs.sp and SP_EL1 in regs.sp_el1. On the
     * QEMU side we keep the current SP in xregs[31] as well.
     */
    aarch64_restore_sp(env, 1);

    reg.id = AARCH64_CORE_REG(regs.pc);
    reg.addr = (uintptr_t) &env->pc;
    ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    /* If we are in AArch32 mode then we need to sync the AArch32 regs with the
     * incoming AArch64 regs received from 64-bit KVM.
     * We must perform this after all of the registers have been acquired from
     * the kernel.
     */
    if (!is_a64(env)) {
        aarch64_sync_64_to_32(env);
    }

    reg.id = AARCH64_CORE_REG(elr_el1);
    reg.addr = (uintptr_t) &env->elr_el[1];
    ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }

    /* Fetch the SPSR registers
     *
     * KVM SPSRs 0-4 map to QEMU banks 1-5
     */
    for (i = 0; i < KVM_NR_SPSR; i++) {
        reg.id = AARCH64_CORE_REG(spsr[i]);
        reg.addr = (uintptr_t) &env->banked_spsr[i + 1];
        ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
        if (ret) {
            return ret;
        }
    }

    el = arm_current_el(env);
    if (el > 0 && !is_a64(env)) {
        i = bank_number(env->uncached_cpsr & CPSR_M);
        env->spsr = env->banked_spsr[i];
    }

    /* Advanced SIMD and FP registers
     * We map Qn = regs[2n+1]:regs[2n]
     */
    for (i = 0; i < 32; i++) {
        uint64_t fp_val[2];
        reg.id = AARCH64_SIMD_CORE_REG(fp_regs.vregs[i]);
        reg.addr = (uintptr_t)(&fp_val);
        ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
        if (ret) {
            return ret;
        } else {
            int rd = i << 1;
#ifdef HOST_WORDS_BIGENDIAN
            env->vfp.regs[rd + 1] = fp_val[0];
            env->vfp.regs[rd] = fp_val[1];
#else
            env->vfp.regs[rd + 1] = fp_val[1];
            env->vfp.regs[rd] = fp_val[0];
#endif
        }
    }

    reg.addr = (uintptr_t)(&fpr);
    reg.id = AARCH64_SIMD_CTRL_REG(fp_regs.fpsr);
    ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }
    vfp_set_fpsr(env, fpr);

    reg.id = AARCH64_SIMD_CTRL_REG(fp_regs.fpcr);
    ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
    if (ret) {
        return ret;
    }
    vfp_set_fpcr(env, fpr);

    if (!write_kvmstate_to_list(cpu)) {
        return EINVAL;
    }
    /* Note that it's OK to have registers which aren't in CPUState,
     * so we can ignore a failure return here.
     */
    write_list_to_cpustate(cpu);

    kvm_arm_sync_mpstate_to_qemu(cpu);

    /* TODO: other registers */
    return ret;
}
