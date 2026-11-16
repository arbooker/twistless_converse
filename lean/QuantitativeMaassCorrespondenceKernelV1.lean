module

public import QuantitativeMaassIntegralProductsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology ENNReal MatrixGroups

namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- The actual integral product is nonscalar. This tests the product with
its congruence representative, not the fixed matrix alone. -/
def integralProductNonscalar (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (γ : gamma N) : Prop :=
  ((representative γ).val*M) 1 0≠0 ∨
    ((representative γ).val*M) 1 1≠((representative γ).val*M) 0 0 ∨
    ((representative γ).val*M) 0 1≠0

/-- Scalar integral products give the actual identity transformation. -/
theorem congruence_product_fixed_of_scalar (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0<M.det) (γ : gamma N) (hne : ¬integralProductNonscalar N M γ) (z : ℍ) :
    γ • (positiveIntegralGL M hM • z)=z := by
  let P := (representative γ).val*M
  have hp : 0<P.det := by rw [congruence_product_det];exact hM
  change ¬(P 1 0≠0 ∨ P 1 1≠P 0 0 ∨ P 0 1≠0) at hne
  push Not at hne
  have ha : (P 0 0:ℂ)≠0 := by
    simpa only [hne.1,hne.2.1,Int.cast_zero,zero_mul,zero_add] using
      QuantitativeArithmetic.integer_matrix_denominator_ne_zero P hp.ne' I
  rw [← congruence_positiveIntegralGL_action N γ M hM hp]
  apply UpperHalfPlane.ext
  rw [positiveIntegralGL_fractional]
  change ((P 0 0:ℂ)*(z:ℂ)+P 0 1)/((P 1 0:ℂ)*(z:ℂ)+P 1 1)=(z:ℂ)
  simp only [hne.1,hne.2.1,hne.2.2,Int.cast_zero,zero_mul,zero_add,add_zero,
    mul_div_cancel_left₀ _ ha]

/-- Every positive-determinant real matrix preserves hyperbolic distance,
by its actual determinant-one normalization. -/
theorem positiveGL_action_dist (g : GL (Fin 2) ℝ) (hg : 0<g.det.val) (z w : ℍ) :
    dist (g•z) (g•w)=dist z w := by
  let r := Real.sqrt g.det.val
  have hr : 0<r := Real.sqrt_pos.mpr hg
  have hrsq : r^2=g.det.val := Real.sq_sqrt hg.le
  let S : SL(2,ℝ) := ⟨r⁻¹ • g.val,by
    rw [Matrix.det_smul,Fintype.card_fin]
    change r⁻¹^2*g.det.val=1
    rw [← hrsq,inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]⟩
  have he (x : ℍ) : S•x=g•x := by
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply,coe_smul_of_det_pos hg]
    change (((r⁻¹*g.val 0 0:ℝ):ℂ)*(x:ℂ)+((r⁻¹*g.val 0 1:ℝ):ℂ))/
      (((r⁻¹*g.val 1 0:ℝ):ℂ)*(x:ℂ)+((r⁻¹*g.val 1 1:ℝ):ℂ))=
      ((g.val 0 0:ℂ)*(x:ℂ)+(g.val 0 1:ℂ))/((g.val 1 0:ℂ)*(x:ℂ)+(g.val 1 1:ℂ))
    push_cast
    have hrc : (r:ℂ)⁻¹≠0 := inv_ne_zero (by exact_mod_cast hr.ne')
    calc
      _ = ((r:ℂ)⁻¹*((g.val 0 0:ℂ)*(x:ℂ)+(g.val 0 1:ℂ)))/
          ((r:ℂ)⁻¹*((g.val 1 0:ℂ)*(x:ℂ)+(g.val 1 1:ℂ))) := by congr 1 <;> ring
      _ = _ := mul_div_mul_left _ _ hrc
  rw [← he z,← he w]
  exact dist_smul S z w

/-- Finite propagation for a fixed correspondence matrix: the orbit radius
has just the additional displacement of the base point under that matrix. -/
theorem correspondence_displacement_in_diagonalOrbitSet (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (o x : ℍ) (L R : ℝ) (hx : dist x o≤L) (γ : gamma N)
    (hγ : dist (γ • (positiveIntegralGL M hM • x)) x≤R) :
    γ∈diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • o) o) := by
  apply (mem_diagonalOrbitSet N o _ γ).mpr
  let G := positiveIntegralGL M hM
  have h1 := dist_triangle (γ•o) (γ•(G•o)) o
  have h2 := dist_triangle (γ•(G•o)) (γ•(G•x)) o
  have h3 := dist_triangle (γ•(G•x)) x o
  rw [congruence_action_dist,dist_comm o (G•o)] at h1
  have hg : 0<G.det.val := by rw [positiveIntegralGL_det];exact_mod_cast hM
  rw [congruence_action_dist,positiveGL_action_dist G hg,dist_comm o x] at h2
  change dist (γ • (G•x)) x≤R at hγ
  change dist (γ•o) o≤R+2*L+dist (G•o) o
  linarith

/-- Literal nonscalar part of the periodized kernel along a correspondence. -/
def radialIntegralRemainder (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (g : ℝ → ℂ) (x : ℍ) : ℂ := by
  classical
  exact ∑' γ : gamma N,if integralProductNonscalar N M γ then
    g (Real.cosh (dist (γ • (positiveIntegralGL M hM • x)) x)) else 0

/-- Exact finite expansion of the nonscalar remainder, uniformly on a ball. -/
theorem radialIntegralRemainder_eq_finite (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (o x : ℍ) (L : ℝ) (hx : dist x o≤L) :
    radialIntegralRemainder N M hM g x=
      ∑ γ∈(diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • o) o)).filter
        (integralProductNonscalar N M),g (Real.cosh (dist (γ • (positiveIntegralGL M hM • x)) x)) := by
  classical
  unfold radialIntegralRemainder
  rw [tsum_eq_sum (s:=(diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • o) o)).filter
    (integralProductNonscalar N M)) (fun γ hγ => ?_)]
  · apply Finset.sum_congr rfl
    intro γ hγ
    exact ite_eq_left (Finset.mem_filter.mp hγ).2
  · by_cases hn : integralProductNonscalar N M γ
    · rw [ite_eq_left hn]
      by_contra hnonzero
      have hd : dist (γ • (positiveIntegralGL M hM • x)) x≤R := by
        have hh := Real.cosh_le_cosh.mp (hs hnonzero)
        simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] using hh
      exact hγ (Finset.mem_filter.mpr
        ⟨correspondence_displacement_in_diagonalOrbitSet N M hM o x L R hx γ hd,hn⟩)
    · exact ite_eq_right hn

/-- The full actual correspondence kernel has the same finite orbit support. -/
theorem radialIntegralKernel_eq_finite (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (o x : ℍ) (L : ℝ) (hx : dist x o≤L) :
    radialPoincareKernel N g x (positiveIntegralGL M hM • x)=
      ∑ γ∈diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • o) o),
        g (Real.cosh (dist (γ • (positiveIntegralGL M hM • x)) x)) := by
  classical
  simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
  apply tsum_eq_sum
  intro γ hγ
  by_contra hn
  have hd : dist (γ • (positiveIntegralGL M hM • x)) x≤R := by
    have hh := Real.cosh_le_cosh.mp (hs hn)
    simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] using hh
  exact hγ (correspondence_displacement_in_diagonalOrbitSet N M hM o x L R hx γ hd)

/-- Exact split into scalar identity branches and the genuine nonscalar
remainder. The finite identity count will be identified arithmetically. -/
theorem radialIntegralKernel_scalar_split (N : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (o x : ℍ) (L : ℝ) (hx : dist x o≤L) :
    radialPoincareKernel N g x (positiveIntegralGL M hM • x)=
      (∑ γ∈diagonalOrbitSet N o (R+2*L+dist (positiveIntegralGL M hM • o) o),
        if integralProductNonscalar N M γ then 0 else g 1)+radialIntegralRemainder N M hM g x := by
  classical
  rw [radialIntegralKernel_eq_finite N M hM g R hR hs o x L hx,
    radialIntegralRemainder_eq_finite N M hM g R hR hs o x L hx,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro γ _
  by_cases hn : integralProductNonscalar N M γ
  · simp only [hn,ite_true,zero_add]
  · rw [congruence_product_fixed_of_scalar N M hM γ hn x]
    simp only [hn,ite_false,dist_self,Real.cosh_zero,add_zero]

#print axioms positiveGL_action_dist
#print axioms congruence_product_fixed_of_scalar
#print axioms correspondence_displacement_in_diagonalOrbitSet
#print axioms radialIntegralRemainder_eq_finite
#print axioms radialIntegralKernel_eq_finite
#print axioms radialIntegralKernel_scalar_split

end QuantitativeMaass
