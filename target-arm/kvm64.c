/*
 * ARM implementation of KVM hooks, 64 bit specific code
 *
 * Copyright Mian-M. Hamayun 2013, Virtual Open Systems
 *
 * This work is licensed under the terms of the GNU GPL, version 2 or later.
 * See the COPYING file in the top-level directory.
 *
 */

#include <stdio.h>
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/mman.h>

#include <linux/kvm.h>

#include "qemu-common.h"
#include "qemu/timer.h"
#include "sysemu/sysemu.h"
#include "sysemu/kvm.h"
#include "kvm_arm.h"
#include "cpu.h"
#include "internals.h"
#include "hw/arm/arm.h"

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

/* The linux headers don't define a 128 bit wide SIMD macro for us */
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
     * reflected and map aarch64 exception levels if required.
     */
    el = arm_current_el(env);
    if (el > 0) {
        if (is_a64(env)) {
            g_assert(el == 1);
            env->banked_spsr[0] = env->spsr;
            /* QEMUs AARCH64 EL1 SPSR is in bank 0, so map it to
             * KVM_SPSR_SVC for syncing to KVM */
            env->banked_spsr[1] = env->banked_spsr[0];
        } else {
            i = bank_number(env->uncached_cpsr & CPSR_M);
            env->banked_spsr[i] = env->spsr;
        }
    }

    for (i = 0; i < KVM_NR_SPSR; i++) {
        reg.id = AARCH64_CORE_REG(spsr[i]);
        reg.addr = (uintptr_t) &env->banked_spsr[i+1];
        ret = kvm_vcpu_ioctl(cs, KVM_SET_ONE_REG, &reg);
        if (ret) {
            return ret;
        }
    }

    /* Advanced SIMD and FP registers */
    for (i = 0; i < 32; i++) {
        reg.id = AARCH64_SIMD_CORE_REG(fp_regs.vregs[i]);
        reg.addr = (uintptr_t)(&env->vfp.regs[i]);
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
     * KVM has an array of state indexed for all the possible aarch32
     * privilege levels. These map onto QEMUs aarch32 banks 1 - 4.
     */
    for (i = 0; i < KVM_NR_SPSR; i++) {
        reg.id = AARCH64_CORE_REG(spsr[i]);
        reg.addr = (uintptr_t) &env->banked_spsr[i+1];
        ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
        if (ret) {
            return ret;
        }
    }

    el = arm_current_el(env);
    if (el > 0) {
        if (is_a64(env)) {
            g_assert(el == 1);
            /* KVM_SPSR_SVC holds the AARCH64 EL1 SPSR which QEMU
             * keeps in bank 0 so copy it across. */
            env->banked_spsr[0] = env->banked_spsr[1];
            i = aarch64_banked_spsr_index(el);
        } else {
            i = bank_number(env->uncached_cpsr & CPSR_M);
        }
        env->spsr = env->banked_spsr[i];
    }

    /* Advanced SIMD and FP registers */
    for (i = 0; i < 32; i++) {
        reg.id = AARCH64_SIMD_CORE_REG(fp_regs.vregs[i]);
        reg.addr = (uintptr_t)(&env->vfp.regs[i]);
        ret = kvm_vcpu_ioctl(cs, KVM_GET_ONE_REG, &reg);
        if (ret) {
            return ret;
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
