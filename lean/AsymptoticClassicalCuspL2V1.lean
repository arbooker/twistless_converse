module

public import AsymptoticClassicalHolomorphicDensityV1
public import AsymptoticClassicalFiniteDimensionV1
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane MeasureTheory Filter AsymptoticClassicalCusp
open scoped Topology ComplexConjugate

/-- The positive weight used to realize the Petersson norm in an L² space. -/
def weighted (k : ℤ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (Real.sqrt (z.im ^ k) : ℂ) * f z

theorem weight_ne_zero (k : ℤ) (z : ℍ) :
    (Real.sqrt (z.im ^ k) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (zpow_pos z.im_pos k)).ne'

theorem weighted_continuous (k : ℤ) {f : ℍ → ℂ} (hf : Continuous f) :
    Continuous (weighted k f) := by
  apply Continuous.mul _ hf
  apply Complex.continuous_ofReal.comp
  exact (continuous_im.zpow₀ k (fun z => Or.inl z.im_ne_zero)).sqrt

theorem weighted_norm_sq (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    ‖weighted k f z‖ ^ 2 = ‖petersson k f f z‖ := by
  rw [weighted, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (zpow_pos z.im_pos k).le]
  simp [petersson, abs_of_pos z.im_pos, pow_two, mul_comm, mul_left_comm, mul_assoc]

variable (N : ℕ) [NeZero N] (k : ℤ)

theorem weighted_memLp (f : CuspForm (level N) k) :
    MemLp (weighted k f) 2 (quotientMeasure N) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (level N) f f
  apply MemLp.of_bound (weighted_continuous k f.holo'.continuous).aestronglyMeasurable
    (Real.sqrt C)
  apply Eventually.of_forall
  intro z
  apply Real.le_sqrt_of_sq_le
  rw [weighted_norm_sq]
  exact hC z

/-- The actual weighted cusp-function embedding into the quotient L² space. -/
def embedding : CuspForm (level N) k →ₗ[ℂ] Lp ℂ 2 (quotientMeasure N) where
  toFun f := (weighted_memLp N k f).toLp (weighted k f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(weighted_memLp N k (f + g)).coeFn_toLp,
      (weighted_memLp N k f).coeFn_toLp, (weighted_memLp N k g).coeFn_toLp,
      Lp.coeFn_add ((weighted_memLp N k f).toLp _) ((weighted_memLp N k g).toLp _)]
      with z hfg hf hg ha
    simp only [hfg, ha, hf, hg, weighted, add_apply, mul_add, Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(weighted_memLp N k (c • f)).coeFn_toLp,
      (weighted_memLp N k f).coeFn_toLp,
      Lp.coeFn_smul c ((weighted_memLp N k f).toLp _)] with z hcf hf hs
    simp only [RingHom.id_apply, hcf, hs, hf, weighted, smul_apply, smul_eq_mul,
      Pi.smul_apply]
    ring

theorem embedding_coeFn (f : CuspForm (level N) k) :
    embedding N k f =ᵐ[quotientMeasure N] weighted k f :=
  (weighted_memLp N k f).coeFn_toLp

theorem embedding_injective : Function.Injective (embedding N k) := by
  intro f g he
  have ha : (fun z : ℍ => f z - g z) =ᵐ[quotientMeasure N] 0 := by
    filter_upwards [embedding_coeFn N k f, embedding_coeFn N k g] with z hf hg
    have hh : weighted k f z = weighted k g z := by rw [← hf, he, hg]
    exact sub_eq_zero.mpr (mul_left_cancel₀ (weight_ne_zero k z) hh)
  have hz := eq_zero_of_ae_quotient N (f.holo'.sub g.holo') ha
  exact CuspForm.ext (fun z => sub_eq_zero.mp (congrFun hz z))

#print axioms weight_ne_zero
#print axioms weighted_continuous
#print axioms weighted_norm_sq
#print axioms weighted_memLp
#print axioms embedding_coeFn
#print axioms embedding_injective

end AsymptoticClassicalPetersson
