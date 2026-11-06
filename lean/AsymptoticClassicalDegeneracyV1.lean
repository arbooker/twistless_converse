module

public import AsymptoticClassicalFiniteDimensionV1
public import AsymptoticDegeneracyGroupV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels AsymptoticRationalFreeness
open scoped ModularForm MatrixGroups Pointwise

def dilationReal (p : ℕ) (hp : 0 < p) : GL (Fin 2) ℝ :=
  (dilationGL p hp).map (Rat.castHom ℝ)

theorem dilationReal_det (p : ℕ) (hp : 0 < p) : (dilationReal p hp).det.val = (p : ℝ) := by
  change ((!![(p : ℚ), 0; 0, 1]).map (fun a : ℚ => (a : ℝ))).det = _
  simp [Matrix.det_fin_two]

theorem dilationReal_denom (p : ℕ) (hp : 0 < p) (z : ℍ) : denom (dilationReal p hp) z = 1 := by
  simp [denom, dilationReal, dilationGL, GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero]

/-- The integral conjugate by diag(p,1) of a matrix at level p*M. -/
def dilationConjugate (M p : ℕ) (A : SL(2, ℤ)) (c : ℤ)
    (hc : A 1 0 = (p : ℤ) * (M : ℤ) * c) : SL(2, ℤ) :=
  ⟨!![A 0 0, (p : ℤ) * A 0 1; (M : ℤ) * c, A 1 1], by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd ⊢
    change A 0 0 * A 1 1 - ((p : ℤ) * A 0 1) * ((M : ℤ) * c) = 1
    rw [hc] at hd
    nlinarith [hd]⟩

theorem dilationConjugate_mem (M p : ℕ) (A : SL(2, ℤ)) (c : ℤ)
    (hc : A 1 0 = (p : ℤ) * (M : ℤ) * c) :
    dilationConjugate M p A c hc ∈ CongruenceSubgroup.Gamma0 M := by
  rw [gamma0_mem_dvd]
  exact ⟨c, rfl⟩

theorem dilation_intertwine (M p : ℕ) (hp : 0 < p) (A : SL(2, ℤ)) (c : ℤ)
    (hc : A 1 0 = (p : ℤ) * (M : ℤ) * c) :
    dilationReal p hp * SpecialLinearGroup.mapGL ℝ A =
      SpecialLinearGroup.mapGL ℝ (dilationConjugate M p A c hc) * dilationReal p hp := by
  apply Units.ext
  change (dilationReal p hp).val * A.val.map (fun z : ℤ => (z : ℝ)) =
    (dilationConjugate M p A c hc).val.map (fun z : ℤ => (z : ℝ)) * (dilationReal p hp).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationReal, dilationGL, GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
      dilationConjugate, Matrix.mul_apply, Fin.sum_univ_two, hc]
  all_goals ring

/-- The actual congruence inclusion needed to translate lower-level
 cusp forms by a dilation. -/
theorem level_le_dilation_conjugate (M p : ℕ) (hp : 0 < p) :
    level (p * M) ≤ toConjAct (dilationReal p hp)⁻¹ • level M := by
  rintro g ⟨A, hA, rfl⟩
  obtain ⟨c, hc⟩ := (gamma0_mem_dvd (p * M) A).mp hA
  have hc' : A 1 0 = (p : ℤ) * (M : ℤ) * c := by simpa only [Nat.cast_mul] using hc
  have hb : SpecialLinearGroup.mapGL ℝ (dilationConjugate M p A c hc') ∈ level M :=
    ⟨_, dilationConjugate_mem M p A c hc', rfl⟩
  have he : toConjAct (dilationReal p hp)⁻¹ •
      SpecialLinearGroup.mapGL ℝ (dilationConjugate M p A c hc') = SpecialLinearGroup.mapGL ℝ A := by
    change (dilationReal p hp)⁻¹ * SpecialLinearGroup.mapGL ℝ (dilationConjugate M p A c hc') *
      ((dilationReal p hp)⁻¹)⁻¹ = _
    rw [inv_inv, mul_assoc, ← dilation_intertwine M p hp A c hc', inv_mul_cancel_left]
  rw [← he]
  exact Subgroup.smul_mem_pointwise_smul_iff.mpr hb

/-- The translated cusp form with the determinant normalization chosen
 so that its value is literally f(p*z). -/
def degeneracyForm (M p : ℕ) (hp : 0 < p) (k : ℤ) (f : CuspForm (level M) k) :
    CuspForm (level (p * M)) k :=
  (p : ℂ) ^ (1 - k) • restrict k (level_le_dilation_conjugate M p hp)
    (CuspForm.translate f (dilationReal p hp))

theorem degeneracyForm_apply (M p : ℕ) (hp : 0 < p) (k : ℤ)
    (f : CuspForm (level M) k) (z : ℍ) :
    degeneracyForm M p hp k f z = f (dilationReal p hp • z) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  change (p : ℂ) ^ (1 - k) * ((f : ℍ → ℂ) ∣[k] dilationReal p hp) z = _
  simp only [ModularForm.slash_def]
  rw [dilationReal_denom, dilationReal_det]
  simp only [σ, dilationReal_det, hpR, ite_true, ContinuousAlgEquiv.refl_apply,
    abs_of_pos hpR, Complex.ofReal_natCast, _root_.one_zpow, mul_one]
  calc
    _ = ((p : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 1)) * f (dilationReal p hp • z) := by ring
    _ = _ := by rw [← zpow_add₀ hpC]; simp

/-- The normalized degeneracy map between the actual classical cusp spaces. -/
def degeneracy (M p : ℕ) (hp : 0 < p) (k : ℤ) :
    CuspForm (level M) k →ₗ[ℂ] CuspForm (level (p * M)) k where
  toFun := degeneracyForm M p hp k
  map_add' f g := by
    ext z
    simp only [degeneracyForm_apply, _root_.add_apply]
  map_smul' c f := by
    ext z
    simp only [degeneracyForm_apply, _root_.smul_apply, RingHom.id_apply]

@[simp] theorem degeneracy_apply (M p : ℕ) (hp : 0 < p) (k : ℤ)
    (f : CuspForm (level M) k) (z : ℍ) :
    degeneracy M p hp k f z = f (dilationReal p hp • z) := degeneracyForm_apply M p hp k f z

theorem degeneracy_injective (M p : ℕ) (hp : 0 < p) (k : ℤ) :
    Function.Injective (degeneracy M p hp k) := by
  intro f g he
  ext z
  have hz := congrArg (fun h : CuspForm (level (p * M)) k => h ((dilationReal p hp)⁻¹ • z)) he
  simpa only [degeneracy_apply, smul_inv_smul] using hz

#print axioms dilationReal_det
#print axioms dilationReal_denom
#print axioms dilationConjugate_mem
#print axioms dilation_intertwine
#print axioms level_le_dilation_conjugate
#print axioms degeneracyForm_apply
#print axioms degeneracy_injective

end AsymptoticClassicalCusp
