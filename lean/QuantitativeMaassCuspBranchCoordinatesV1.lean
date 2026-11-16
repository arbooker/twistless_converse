module

public import QuantitativeMaassCuspHeckeEquivarianceV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace QuantitativeMaass

theorem cuspBranchGL_det (N p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) :
    (cuspBranchGL N p j).det.val = (p:ℝ) := by
  change ((cuspBranch N p j).map (Int.castRingHom ℝ)).det = _
  have hm : ((cuspBranch N p j).map (Int.castRingHom ℝ)).det =
      ((cuspBranch N p j).det : ℝ) := by simp [Matrix.det_fin_two]
  rw [hm,cuspBranch_det]
  simp

theorem cuspBranchGL_none_point (N p : ℕ) [Fact p.Prime] (x y : ℝ) (hy : 0<y) :
    cuspBranchGL N p none • horocyclePoint x y hy =
      horocyclePoint ((p:ℝ)*x) ((p:ℝ)*y)
        (mul_pos (by exact_mod_cast (Fact.out : p.Prime).pos) hy) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by
    rw [cuspBranchGL_det]; exact_mod_cast (Fact.out : p.Prime).pos)]
  simp [UpperHalfPlane.num,UpperHalfPlane.denom,cuspBranchGL,cuspBranch,
    horocyclePoint]
  apply Complex.ext <;> simp

theorem cuspBranchGL_some_point (N p : ℕ) [Fact p.Prime] (u : ZMod p)
    (x y : ℝ) (hy : 0<y) :
    cuspBranchGL N p (some u) • horocyclePoint x y hy =
      horocyclePoint ((x+(N:ℝ)*u.val)/p) (y/p)
        (div_pos hy (by exact_mod_cast (Fact.out : p.Prime).pos)) := by
  have hp : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by
    rw [cuspBranchGL_det]; exact_mod_cast (Fact.out : p.Prime).pos)]
  simp [UpperHalfPlane.num,UpperHalfPlane.denom,cuspBranchGL,cuspBranch,
    horocyclePoint]
  apply Complex.ext <;> simp [Complex.div_re,Complex.div_im]
  all_goals field_simp

#print axioms cuspBranchGL_none_point
#print axioms cuspBranchGL_some_point

end QuantitativeMaass
