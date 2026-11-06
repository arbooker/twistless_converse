module

public import AsymptoticClassicalHolomorphicVandermondeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- Restriction of modular forms along an inclusion of groups. -/
def restrictModular {G H : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [H.HasDetOne] (k : ℤ) (h : G ≤ H) :
    ModularForm H k →ₗ[ℂ] ModularForm G k where
  toFun f := {
    toFun := f
    slash_action_eq' := fun g hg => f.slash_action_eq' g (h hg)
    holo' := f.holo'
    bdd_at_cusps' := fun hc => f.bdd_at_cusps' (hc.mono h) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictModular_apply {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] (k : ℤ) (h : G ≤ H) (f : ModularForm H k) (z : ℍ) :
    restrictModular k h f z = f z := rfl

end AsymptoticClassicalCusp

namespace AsymptoticClassicalDiscriminant

open UpperHalfPlane AsymptoticClassicalCusp
open scoped ModularForm MatrixGroups

/-- Powers commute with the determinant-one slash action. -/
theorem pow_slash_SL2 (k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) (n : ℕ) :
    (f ^ n) ∣[(n : ℤ) * k] A = (f ∣[k] A) ^ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    exact ModularForm.is_invariant_one A
  | succ n ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      ModularForm.mul_slash_SL2, ih, pow_succ]

/-- A family of cusp forms of one common weight, constructed from
 Delta(z) and Delta(N*z). -/
def family (N : ℕ) (hN : 0 < N) (n : ℕ) (j : Fin n) :
    CuspForm (level N) (12 * (n : ℤ)) :=
  CuspForm.mcast (by have := j.isLt; simp only [Fin.val_rev]; omega)
    (((restrict 12 (level_le_SL N) CuspForm.discriminant).mulModularForm
      ((CuspForm.toModularFormₗ (atLevel N hN)).pow j.val)).mulModularForm
        ((CuspForm.toModularFormₗ (restrict 12 (level_le_SL N) CuspForm.discriminant)).pow j.rev.val))

@[simp] theorem family_apply (N : ℕ) (hN : 0 < N) (n : ℕ) (j : Fin n) (z : ℍ) :
    family N hN n j z = ModularForm.discriminant z * atLevel N hN z ^ j.val *
      ModularForm.discriminant z ^ j.rev.val := by
  change ((restrict 12 (level_le_SL N) CuspForm.discriminant) z *
    ((CuspForm.toModularFormₗ (atLevel N hN)).pow j.val) z) *
      ((CuspForm.toModularFormₗ (restrict 12 (level_le_SL N) CuspForm.discriminant)).pow j.rev.val) z = _
  simp only [ModularForm.coe_pow, Pi.pow_apply, restrict_apply]
  rfl

theorem discriminant_slash (A : SL(2, ℤ)) :
    ModularForm.discriminant ∣[(12 : ℤ)] A = ModularForm.discriminant := by
  exact CuspForm.discriminant.slash_action_eq' (Matrix.SpecialLinearGroup.mapGL ℝ A) ⟨A, rfl⟩

/-- The slash translates of the common-weight family form a Vandermonde
 system, multiplied by nowhere-zero powers of the level-one discriminant. -/
theorem family_slash (N : ℕ) (hN : 0 < N) (n : ℕ) (j : Fin n)
    (A : SL(2, ℤ)) :
    (family N hN n j : ℍ → ℂ) ∣[12 * (n : ℤ)] A =
      ModularForm.discriminant * ((atLevel N hN : ℍ → ℂ) ∣[(12 : ℤ)] A) ^ j.val *
        ModularForm.discriminant ^ j.rev.val := by
  have hw : 12 * (n : ℤ) = (12 + (j.val : ℤ) * 12) + (j.rev.val : ℤ) * 12 := by
    have := j.isLt
    simp only [Fin.val_rev]
    omega
  have hf : (family N hN n j : ℍ → ℂ) =
      ModularForm.discriminant * (atLevel N hN : ℍ → ℂ) ^ j.val *
        ModularForm.discriminant ^ j.rev.val := funext (family_apply N hN n j)
  rw [hf, hw, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2,
    pow_slash_SL2, pow_slash_SL2, discriminant_slash]

#print axioms pow_slash_SL2
#print axioms family_apply
#print axioms family_slash

end AsymptoticClassicalDiscriminant
