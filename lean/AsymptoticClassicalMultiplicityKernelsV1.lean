module

public import AsymptoticClassicalMultiplicityMixedTraceV1
public import AsymptoticClassicalFrickeNewV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- Changing the presentation of the trace target does not change its kernel. -/
theorem arithmeticTrace_kernel_group_congr
    {G H J : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [H.HasDetOne] [J.HasDetOne]
    [G.IsArithmetic] [H.IsArithmetic] [J.IsArithmetic] (k : ℤ) (he : H = J) :
    LinearMap.ker (arithmeticTrace G H k) = LinearMap.ker (arithmeticTrace G J k) := by
  subst J
  rfl

/-- The two actual trace kernels, with the second old direction written
 using the ordinary dilation group. -/
def twoTraceKernel (N M q : ℕ) [NeZero N] [NeZero M] (hq : 0 < q) (k : ℤ) :
    Submodule ℂ (CuspForm (level N) k) :=
  LinearMap.ker (arithmeticTrace (level N) (level M) k) ⊓
    LinearMap.ker (arithmeticTrace (level N) (dilationLevel M q hq) k)

/-- The dilation presentation is exactly the original prime trace kernel. -/
theorem primeTraceKernel_eq_twoTraceKernel (N : ℕ) [NeZero N] (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) :
    letI : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
      p.property.1.pos).ne'⟩
    primeTraceKernel N hN k p = twoTraceKernel N (N / p.val) p.val p.property.1.pos k := by
  let : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
    p.property.1.pos).ne'⟩
  have hmul : p.val * (N / p.val) = N := Nat.mul_div_cancel' p.property.2
  have hgroup : frickeOldLevel N (N / p.val) hN =
      dilationLevel (N / p.val) p.val p.property.1.pos := by
    have he := frickeOldLevel_eq_dilationLevel (N / p.val) p.val
      (Nat.div_pos (Nat.le_of_dvd hN p.property.2) p.property.1.pos) p.property.1.pos
    simpa only [hmul] using he
  exact congrArg (fun V : Submodule ℂ (CuspForm (level N) k) =>
    LinearMap.ker (arithmeticTrace (level N) (level (N / p.val)) k) ⊓ V)
    (arithmeticTrace_kernel_group_congr k hgroup)

/-- Ordinary p restriction preserves the full actual q trace kernel. -/
theorem restrict_mem_cross_twoTraceKernel (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hc : p.Coprime q) (k : ℤ)
    (f : CuspForm (level (q * M)) k) (hf : f ∈ twoTraceKernel (q * M) M q hq.pos k) :
    restrict k (level_antitone (Nat.dvd_mul_left (q * M) p)) f ∈
      twoTraceKernel (p * (q * M)) (p * M) q hq.pos k :=
  ordinary_restrict_cross_new M p q hM hp hq hc k f hf.1 hf.2

/-- Fricke preserves each individual prime trace kernel, so it also
 preserves partial intersections over any chosen set of bad primes. -/
theorem frickeOperator_mem_primeTraceKernel (N : ℕ) (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) (f : CuspForm (level N) k)
    (hf : f ∈ primeTraceKernel N hN k p) :
    frickeOperator N hN k f ∈ primeTraceKernel N hN k p := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
    p.property.1.pos).ne'⟩
  change arithmeticTrace (level N) (level (N / p.val)) k f = 0 ∧
    arithmeticTrace (level N) (frickeOldLevel N (N / p.val) hN) k f = 0 at hf
  change arithmeticTrace (level N) (level (N / p.val)) k (frickeOperator N hN k f) = 0 ∧
    arithmeticTrace (level N) (frickeOldLevel N (N / p.val) hN) k (frickeOperator N hN k f) = 0
  refine ⟨(fricke_trace_swap_zero_iff N (N / p.val) hN k f).mpr hf.2, ?_⟩
  apply (fricke_trace_swap_zero_iff N (N / p.val) hN k (frickeOperator N hN k f)).mp
  rw [frickeOperator_square, map_smul, hf.1, smul_zero]

#print axioms arithmeticTrace_kernel_group_congr
#print axioms primeTraceKernel_eq_twoTraceKernel
#print axioms restrict_mem_cross_twoTraceKernel
#print axioms frickeOperator_mem_primeTraceKernel

end AsymptoticClassicalCusp
