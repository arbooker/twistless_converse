module

public import QuantitativeArithmeticSmallLevelThirteenIndependenceV1
public import QuantitativeArithmeticSmallLevelThirteenDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

def diagScale (r : ℝ) (hr : r≠0) : GL (Fin 2) ℝ :=
  matrix r 0 0 r⁻¹ (by simp [hr])

theorem diagScale_det (r : ℝ) (hr : r≠0) :
    (GeneralLinearGroup.det (diagScale r hr):ℝ)=1 := matrix_det _ _ _ _ _

theorem diagScale_point (r : ℝ) (hr : 0<r) (z : ℍ) :
    ((diagScale r hr.ne' • z:ℍ):ℂ)=(r:ℂ)^2*(z:ℂ) := by
  rw [coe_smul_of_det_pos (by rw [diagScale_det]; norm_num)]
  change ((r:ℂ)*z+0)/(0*z+(r⁻¹:ℝ))=_
  push_cast
  simp only [zero_mul,add_zero,zero_add,div_inv_eq_mul]
  ring

/-- A holomorphic form invariant under a positive diagonal matrix has
an ordinary dilation-invariant weight-corrected function. -/
theorem diagonal_weighted_invariant (m : ℕ) (H : ℍ → ℂ) (r : ℝ) (hr : 0<r)
    (hinv : H ∣[((2*m:ℕ):ℤ)] diagScale r hr.ne'=H) :
    ∀ z : ℂ, 0<z.im →
      (((r:ℂ)^2*z)^m*H (ofComplex ((r:ℂ)^2*z)))=z^m*H (ofComplex z) := by
  intro z hz
  let w : ℍ := ⟨z,hz⟩
  have hh := congrFun hinv w
  rw [det_one_slash _ (diagScale_det _ _)] at hh
  have hd : denom (diagScale r hr.ne') w=(r:ℂ)⁻¹ := by
    change 0*(w:ℂ)+(r⁻¹:ℝ)=(r:ℂ)⁻¹
    simp
  rw [hd,inv_zpow,zpow_neg,zpow_natCast,inv_inv] at hh
  have hw : H (diagScale r hr.ne' • w)=H (ofComplex ((r:ℂ)^2*z)) := by
    rw [← diagScale_point r hr w]
    simp
  rw [hw] at hh
  have hwo : H w=H (ofComplex z) := by
    change H w=H (ofComplex (w:ℂ))
    simp
  rw [hwo] at hh
  calc
    ((r:ℂ)^2*z)^m*H (ofComplex ((r:ℂ)^2*z)) =
        z^m*(H (ofComplex ((r:ℂ)^2*z))*(r:ℂ)^(2*m)) := by ring
    _ = z^m*H (ofComplex z) := by rw [hh]

/-- Two independent positive diagonal automorphisms determine a
holomorphic function explicitly up to one scalar. -/
theorem diagonal_classification (m : ℕ) (H : ℍ → ℂ) (hhol : MDiff H)
    (ha : H ∣[((2*m:ℕ):ℤ)] diagScale scaleA scaleA_pos.ne'=H)
    (hb : H ∣[((2*m:ℕ):ℤ)] diagScale scaleB scaleB_pos.ne'=H) :
    ∃ C : ℂ, ∀ z : ℍ, (z:ℂ)^m*H z=C := by
  let L : ℂ → ℂ := fun z => z^m*H (ofComplex z)
  have hL : AnalyticOnNhd ℂ L {z : ℂ | 0<z.im} := by
    exact (analyticOnNhd_id.pow m).mul
      ((UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet)
  have hlog : Irrational ((2*Real.log scaleA)/(2*Real.log scaleB)) := by
    convert irrational_scale_logs using 1
    ring
  have he (r : ℝ) (hr : 0<r) : (Real.exp (2*Real.log r):ℂ)=(r:ℂ)^2 := by
    rw [show 2*Real.log r=Real.log r+Real.log r by ring,Real.exp_add,Real.exp_log hr]
    push_cast
    ring
  have hconst := constant_of_two_periods hL hlog
    (by intro z hz; rw [he _ scaleA_pos]; exact diagonal_weighted_invariant m H _ scaleA_pos ha z hz)
    (by intro z hz; rw [he _ scaleB_pos]; exact diagonal_weighted_invariant m H _ scaleB_pos hb z hz)
  refine ⟨L Complex.I,?_⟩
  intro z
  simpa [L] using hconst (z:ℂ) z.im_pos

#print axioms diagonal_weighted_invariant
#print axioms diagonal_classification
end QuantitativeArithmeticSmallLevelThirteen
