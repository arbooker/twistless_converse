module

public import AsymptoticL2MultiplierV1
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.MeasureTheory.Group.Action

set_option autoImplicit false
@[expose] public section

namespace AsymptoticHyperbolicSlash

open MeasureTheory UpperHalfPlane Filter

noncomputable abbrev Space := Lp ℂ 2 (volume : Measure ℍ)

/-- The weight-dependent part of the normalized slash action has modulus
one. All radial growth has been removed by multiplying F by y^(k/2). -/
noncomputable def phase (g : GL (Fin 2) ℝ) (k : ℕ) (z : ℍ) : ℂ :=
  ((‖denom g z‖:ℂ)/denom g z)^k

theorem phase_continuous (g : GL (Fin 2) ℝ) (k : ℕ) : Continuous (phase g k) := by
  have hd : Continuous (fun z : ℍ => denom g z) := by unfold denom; fun_prop
  exact ((Complex.continuous_ofReal.comp hd.norm).div₀ hd (denom_ne_zero g)).pow k

theorem phase_norm (g : GL (Fin 2) ℝ) (k : ℕ) (z : ℍ) : ‖phase g k z‖=1 := by
  rw [phase,norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (denom_ne_zero g z)),one_pow]

/-- Pullback by the actual real Möbius action preserves hyperbolic L². -/
noncomputable def pullback (g : GL (Fin 2) ℝ) : Space →ₗᵢ[ℂ] Space :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℍ => g • z) (measurePreserving_smul g volume)

theorem pullback_coeFn (g : GL (Fin 2) ℝ) (f : Space) :
    pullback g f =ᵐ[volume] (fun z => f (g • z)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_smul g volume)

/-- The concrete normalized slash operator, including its unit phase. -/
noncomputable def operator (g : GL (Fin 2) ℝ) (k : ℕ) : Space →L[ℂ] Space :=
  (AsymptoticL2Multiplier.operator (phase g k) (phase_continuous g k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => (phase_norm g k z).le))).comp
      (pullback g).toContinuousLinearMap

theorem operator_coeFn (g : GL (Fin 2) ℝ) (k : ℕ) (f : Space) :
    operator g k f =ᵐ[volume] (fun z => phase g k z*f (g • z)) := by
  have hp := AsymptoticL2Multiplier.operator_coeFn (phase g k)
    (phase_continuous g k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => (phase_norm g k z).le)) (pullback g f)
  filter_upwards [hp,pullback_coeFn g f] with z hz hf
  exact hz.trans (congrArg (fun w => phase g k z*w) hf)

theorem operator_norm_map (g : GL (Fin 2) ℝ) (k : ℕ) (f : Space) :
    ‖operator g k f‖=‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← (pullback g).norm_map f]
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral,AsymptoticL2Multiplier.norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [operator_coeFn g k f,pullback_coeFn g f] with z hz hf
  rw [hz,hf,norm_mul,phase_norm,one_mul]

theorem operator_norm_le (g : GL (Fin 2) ℝ) (k : ℕ) : ‖operator g k‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp only [operator_norm_map,one_mul,le_refl]

/-- The slash phases obey the genuine Möbius cocycle. This is the
identity used to remove weight-dependent phases on a free rational orbit. -/
theorem phase_mul (g h : GL (Fin 2) ℝ) (hh : 0<h.det.val) (k : ℕ) (z : ℍ) :
    phase (g*h) k z=phase g k (h • z)*phase h k z := by
  have hd : denom (g*h) z=denom g (h • z : ℍ)*denom h z := by
    rw [coe_smul_of_det_pos hh]
    exact denom_cocycle g h z.im_ne_zero
  simp only [phase,hd,norm_mul,Complex.ofReal_mul,mul_div_mul_comm,mul_pow]

theorem phase_one (k : ℕ) (z : ℍ) : phase 1 k z=1 := by
  simp [phase,denom]

/-- Composition is the right slash action, with all phases retained. -/
theorem operator_comp (g h : GL (Fin 2) ℝ) (hh : 0<h.det.val) (k : ℕ) :
    (operator h k).comp (operator g k)=operator (g*h) k := by
  ext1 f
  apply Lp.ext
  have hp := (measurePreserving_smul h (volume : Measure ℍ)).quasiMeasurePreserving.ae
    (operator_coeFn g k f)
  filter_upwards [operator_coeFn h k (operator g k f),operator_coeFn (g*h) k f,hp]
    with z h₁ h₂ h₃
  change operator h k (operator g k f) z=operator (g*h) k f z
  rw [h₁,h₂,h₃,phase_mul g h hh,mul_smul]
  ring

theorem operator_one (k : ℕ) : operator 1 k=ContinuousLinearMap.id ℂ Space := by
  ext1 f
  apply Lp.ext
  filter_upwards [operator_coeFn 1 k f] with z hz
  simpa only [phase_one,one_smul,one_mul,ContinuousLinearMap.id_apply] using hz

theorem scalar_det_pos (u : ℝˣ) :
    0<(Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val := by
  simpa only [Matrix.GeneralLinearGroup.det_scalar,Fintype.card_fin,Units.val_pow_eq_pow_val]
    using sq_pos_of_ne_zero u.ne_zero

theorem phase_scalar (u : ℝˣ) (m : ℕ) (z : ℍ) :
    phase (Matrix.GeneralLinearGroup.scalar (Fin 2) u) (2*m) z=1 := by
  have hd : denom (Matrix.GeneralLinearGroup.scalar (Fin 2) u) z=(u.val:ℂ) := by
    simp [denom,Matrix.GeneralLinearGroup.coe_scalar,Matrix.scalar_apply]
  rw [phase,hd,pow_mul,div_pow,Complex.norm_real,Real.norm_eq_abs,
    ← Complex.ofReal_pow,sq_abs,Complex.ofReal_pow,
    div_self (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr u.ne_zero)),one_pow]

theorem scalar_smul (u : ℝˣ) (z : ℍ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u • z=z := by
  apply forall_smul_eq_self_iff_mem_center.mpr _ z
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u,rfl⟩

theorem operator_scalar (u : ℝˣ) (m : ℕ) :
    operator (Matrix.GeneralLinearGroup.scalar (Fin 2) u) (2*m)=ContinuousLinearMap.id ℂ Space := by
  ext1 f
  apply Lp.ext
  filter_upwards [operator_coeFn (Matrix.GeneralLinearGroup.scalar (Fin 2) u) (2*m) f] with z hz
  simpa only [phase_scalar,scalar_smul,one_mul,ContinuousLinearMap.id_apply] using hz

/-- Even-weight slash operators are independent of the scalar matrix
representative. Thus the geometric branches really belong to PGL. -/
theorem operator_projective_eq {g h : GL (Fin 2) ℝ}
    (hgh : Matrix.ProjGenLinGroup.mk g=Matrix.ProjGenLinGroup.mk h) (m : ℕ) :
    operator g (2*m)=operator h (2*m) := by
  obtain ⟨u,rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hgh
  rw [← operator_comp g _ (scalar_det_pos u),operator_scalar]
  rfl

/-- Exact agreement with the classical even-weight slash formula for
positive determinant. This prevents replacing the slash phase by its
absolute value in the later observation operators. -/
theorem normalized_slash (g : GL (Fin 2) ℝ) (hg : 0<g.det.val) (m : ℕ)
    (F : ℍ → ℂ) (z : ℍ) :
    phase g (2*m) z*((g • z).im:ℂ)^m*F (g • z)=
      (z.im:ℂ)^m*(g.det.val:ℂ)^m/(denom g z)^(2*m)*F (g • z) := by
  have hd := denom_ne_zero g z
  have hn : ‖denom g z‖≠0 := norm_ne_zero_iff.mpr hd
  rw [phase,z.im_smul_eq_div_normSq,abs_of_pos hg,Complex.normSq_eq_norm_sq]
  push_cast
  simp only [div_pow,mul_pow,pow_mul]
  field_simp

/-- Every finite stack of unweighted branch terms has a bound independent
of the holomorphic weight. Compact restrictions and bounded coefficients
can be composed with the same operators. -/
theorem finite_sum_norm_le {ι : Type*} (s : Finset ι)
    (g : ι → GL (Fin 2) ℝ) (a : ι → ℂ) (k : ℕ) :
    ‖∑ i∈s,a i • operator (g i) k‖≤∑ i∈s,‖a i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (operator_norm_le (g i) k) (norm_nonneg (a i))

#print axioms pullback
#print axioms operator_norm_map
#print axioms phase_mul
#print axioms operator_comp
#print axioms operator_projective_eq
#print axioms normalized_slash
#print axioms finite_sum_norm_le

end AsymptoticHyperbolicSlash
