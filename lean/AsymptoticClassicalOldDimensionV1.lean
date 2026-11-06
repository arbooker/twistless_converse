module

public import AsymptoticClassicalTranslateEquivV1
public import AsymptoticClassicalNewOrthogonalV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane ConjAct
open scoped ModularForm Pointwise

theorem frickeReal_det (N : ℕ) (hN : 0 < N) : (frickeReal N hN).det.val = (N : ℝ) := by
  change ((!![(0 : ℚ) * N, 0 * N * 0 - 1; (N : ℚ), N * 0]).map (fun a : ℚ => (a : ℝ))).det = _
  simp [Matrix.det_fin_two]

/-- The second old trace target is linearly equivalent to the ordinary
 lower-level cusp space. -/
def frickeOldEquiv (N M : ℕ) (hN : 0 < N) (k : ℤ) :
    CuspForm (level M) k ≃ₗ[ℂ] CuspForm (frickeOldLevel N M hN) k := by
  have hp : 0 < ((frickeReal N hN)⁻¹).det.val := by
    simp only [map_inv, Units.val_inv_eq_inv_val, frickeReal_det]
    exact inv_pos.mpr (by exact_mod_cast hN)
  let E := translateEquiv (level M) k (frickeReal N hN)⁻¹ hp
  have he : frickeOldLevel N M hN = toConjAct ((frickeReal N hN)⁻¹)⁻¹ • level M := by
    simp only [inv_inv]
    rfl
  let C : CuspForm (toConjAct ((frickeReal N hN)⁻¹)⁻¹ • level M) k ≃ₗ[ℂ]
      CuspForm (frickeOldLevel N M hN) k := {
    toFun := fun f => CuspForm.mcast rfl f he
    invFun := fun f => CuspForm.mcast rfl f he.symm
    left_inv := fun f => CuspForm.ext (fun _ => rfl)
    right_inv := fun f => CuspForm.ext (fun _ => rfl)
    map_add' := fun f g => CuspForm.ext (fun _ => rfl)
    map_smul' := fun c f => CuspForm.ext (fun _ => rfl) }
  exact E.trans C

instance frickeOld_cusp_finite (N M : ℕ) (hN : 0 < N) [NeZero M] (k : ℤ) :
    Module.Finite ℂ (CuspForm (frickeOldLevel N M hN) k) :=
  Module.Finite.of_surjective (frickeOldEquiv N M hN k).toLinearMap
    (frickeOldEquiv N M hN k).surjective

theorem frickeOld_finrank (N M : ℕ) (hN : 0 < N) (k : ℤ) :
    Module.finrank ℂ (CuspForm (frickeOldLevel N M hN) k) =
      Module.finrank ℂ (CuspForm (level M) k) :=
  (frickeOldEquiv N M hN k).finrank_eq.symm

/-- The intersection of the two prime-old images, retained explicitly
 for the oldspace multiplicity calculation. -/
def primeOldIntersection (N : ℕ) (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) : Submodule ℂ (CuspForm (level N) k) :=
  LinearMap.range (restrict k (level_antitone (Nat.div_dvd_of_dvd p.property.2))) ⊓
    LinearMap.range (restrict k (level_le_frickeOldLevel hN (Nat.div_dvd_of_dvd p.property.2)))

/-- The exact dimension identity for the two old images, before
 identifying their overlap. -/
theorem primeOld_finrank (N : ℕ) (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) :
    Module.finrank ℂ (primeOldSpace N hN k p) +
      Module.finrank ℂ (primeOldIntersection N hN k p) =
        2 * Module.finrank ℂ (CuspForm (level (N / p.val)) k) := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
    p.property.1.pos).ne'⟩
  unfold primeOldSpace primeOldIntersection
  rw [Submodule.finrank_sup_add_finrank_inf_eq,
    LinearMap.finrank_range_of_inj (restrict_injective k _),
    LinearMap.finrank_range_of_inj (restrict_injective k _), frickeOld_finrank]
  omega

/-- The prime trace kernel has the expected codimension, expressed
 exactly in terms of the still explicit old-image intersection. -/
theorem primeKernel_finrank (N : ℕ) (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) :
    Module.finrank ℂ (primeTraceKernel N hN k p) +
      2 * Module.finrank ℂ (CuspForm (level (N / p.val)) k) =
        Module.finrank ℂ (CuspForm (level N) k) +
          Module.finrank ℂ (primeOldIntersection N hN k p) := by
  let : NeZero N := ⟨hN.ne'⟩
  have ho := (primeOldSpace N hN k p).finrank_add_finrank_orthogonal
  rw [← primeTraceKernel_eq_orthogonal] at ho
  have hp := primeOld_finrank N hN k p
  omega

#print axioms frickeReal_det
#print axioms frickeOld_finrank
#print axioms primeOld_finrank
#print axioms primeKernel_finrank

end AsymptoticClassicalCusp
