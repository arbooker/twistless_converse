module

public import AsymptoticClassicalFrickeTraceSwapV1
public import AsymptoticClassicalEigenCommutantV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

theorem fricke_trace_swap_zero_iff (N M : ℕ) [NeZero N] [NeZero M]
    (hN : 0 < N) (k : ℤ) (f : CuspForm (level N) k) :
    arithmeticTrace (level N) (level M) k (frickeOperator N hN k f) = 0 ↔
      arithmeticTrace (level N) (frickeOldLevel N M hN) k f = 0 := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (N : ℂ)^(1-(k : ℂ)/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hNC)
  have he := fricke_trace_swap N M hN k f
  constructor
  · intro hz
    rw [hz] at he
    have hslash : ((arithmeticTrace (level N) (frickeOldLevel N M hN) k f : ℍ → ℂ)
        ∣[k] frickeReal N hN) = 0 := by
      exact (smul_eq_zero.mp he.symm).resolve_left hc
    exact DFunLike.coe_injective ((SlashAction.slash_eq_zero_iff k (frickeReal N hN) _).mp hslash)
  · intro hz
    rw [hz] at he
    apply DFunLike.coe_injective
    simpa only [FunLike.coe_zero, SlashAction.zero_slash, smul_zero] using he

/-- Fricke preserves the actual newspace by interchanging its two
lower-level trace equations at every bad prime. -/
theorem frickeOperator_mem_newSpace (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : CuspForm (level N) k) (hf : f ∈ newSpace N hN k) :
    frickeOperator N hN k f ∈ newSpace N hN k := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [mem_newSpace] at hf ⊢
  intro p
  let : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
    p.property.1.pos).ne'⟩
  have hfp := hf p
  change arithmeticTrace (level N) (level (N / p.val)) k f = 0 ∧
    arithmeticTrace (level N) (frickeOldLevel N (N / p.val) hN) k f = 0 at hfp
  change arithmeticTrace (level N) (level (N / p.val)) k (frickeOperator N hN k f) = 0 ∧
    arithmeticTrace (level N) (frickeOldLevel N (N / p.val) hN) k (frickeOperator N hN k f) = 0
  refine ⟨(fricke_trace_swap_zero_iff N (N / p.val) hN k f).mpr hfp.2, ?_⟩
  apply (fricke_trace_swap_zero_iff N (N / p.val) hN k (frickeOperator N hN k f)).mp
  rw [frickeOperator_square, map_smul, hfp.1, smul_zero]

/-- The normalized global Fricke endomorphism restricted to the concrete
newspace; preservation is proved from its defining trace kernels. -/
def newFrickeOperator (N : ℕ) (hN : 0 < N) (k : ℤ) :
    newSpace N hN k →ₗ[ℂ] newSpace N hN k :=
  (frickeOperator N hN k).restrict (fun f hf => frickeOperator_mem_newSpace N hN k f hf)

@[simp] theorem newFrickeOperator_val (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : newSpace N hN k) :
    (newFrickeOperator N hN k f).val = frickeOperator N hN k f.val := rfl

theorem newFrickeOperator_involutive (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : Even k) :
    Function.Involutive (newFrickeOperator N hN (k : ℤ)) := by
  intro f
  apply Subtype.val_injective
  exact frickeOperator_involutive N hN k hk f.val

#print axioms fricke_trace_swap_zero_iff
#print axioms frickeOperator_mem_newSpace
#print axioms newFrickeOperator
#print axioms newFrickeOperator_involutive

end AsymptoticClassicalCusp
