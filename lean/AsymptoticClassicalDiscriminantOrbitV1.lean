module

public import AsymptoticClassicalDiscriminantStabilizerV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane Matrix AsymptoticClassicalCusp AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups Manifold

variable (N : ℕ) (hN : 0 < N)

theorem translate_eq_iff (A B : SL(2, ℤ)) :
    (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A⁻¹ =
      (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] B⁻¹ ↔
        A⁻¹ * B ∈ CongruenceSubgroup.Gamma0 N := by
  constructor
  · intro he
    apply (stabilizer_iff N hN (A⁻¹ * B)).mp
    have hh := congrArg (fun f : ℍ → ℂ => f ∣[(12 : ℤ)] B) he
    simpa only [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one] using hh
  · intro he
    have hh := congrArg (fun f : ℍ → ℂ => f ∣[(12 : ℤ)] B⁻¹)
      ((stabilizer_iff N hN (A⁻¹ * B)).mpr he)
    simpa only [← SlashAction.slash_mul, mul_inv_cancel_right] using hh

/-- The finite family of translates indexed by the actual integral
 congruence cosets. -/
def orbit (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : ℍ → ℂ :=
  Quotient.liftOn q (fun A => (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A⁻¹)
    (fun A B h => (translate_eq_iff N hN A B).mpr
      ((QuotientGroup.leftRel_apply).mp h))

@[simp] theorem orbit_mk (A : SL(2, ℤ)) :
    orbit N hN (QuotientGroup.mk A) = (atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A⁻¹ := rfl

theorem orbit_injective : Function.Injective (orbit N hN) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h A =>
    induction r using Quotient.inductionOn with
    | h B =>
      intro he
      exact QuotientGroup.eq.mpr ((translate_eq_iff N hN A B).mp he)

theorem orbit_holomorphic (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : MDiff (orbit N hN q) := by
  induction q using Quotient.inductionOn with
  | h A => exact (atLevel N hN).holo'.slash 12 (SpecialLinearGroup.mapGL ℝ A⁻¹)

/-- A finite collection of distinct holomorphic functions can be
 simultaneously separated by evaluation at one point. -/
theorem exists_separating_point {ι : Type*} [Fintype ι] (f : ι → ℍ → ℂ)
    (hf : ∀ i, MDiff (f i)) (hinj : Function.Injective f) :
    ∃ z : ℍ, Function.Injective (fun i => f i z) := by
  classical
  let s : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have hp : (∏ p ∈ s, (f p.1 - f p.2)) ≠ (0 : ℍ → ℂ) := by
    intro hz
    obtain ⟨p, hp, he⟩ := (UpperHalfPlane.prod_eq_zero_iff
      (f := fun p : ι × ι => f p.1 - f p.2) (fun p _ => (hf p.1).sub (hf p.2))).mp hz
    exact (Finset.mem_filter.mp hp).2 (hinj (sub_eq_zero.mp he))
  obtain ⟨z, hz⟩ : ∃ z : ℍ, (∏ p ∈ s, (f p.1 - f p.2)) z ≠ 0 := by
    by_contra! h
    exact hp (funext h)
  refine ⟨z, ?_⟩
  intro i j he
  by_contra hij
  have hpij : (i, j) ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  have hz' : (∏ p ∈ s, (f p.1 z - f p.2 z)) ≠ 0 := by
    simpa only [Finset.prod_apply, Pi.sub_apply] using hz
  exact (Finset.prod_ne_zero_iff.mp hz' (i, j) hpij) (sub_eq_zero.mpr he)

/-- All congruence coset translates of Delta(N*z) are separated at a
 common point; in particular their Vandermonde matrix is nonsingular there. -/
theorem orbit_separating_point :
    ∃ z : ℍ, Function.Injective (fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N => orbit N hN q z) := by
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  exact exists_separating_point (orbit N hN) (orbit_holomorphic N hN) (orbit_injective N hN)

#print axioms translate_eq_iff
#print axioms orbit_injective
#print axioms orbit_holomorphic
#print axioms exists_separating_point
#print axioms orbit_separating_point

end AsymptoticClassicalDiscriminant
