module

public import QuantitativeMaassLVDeficitWideFamilyV1
public import QuantitativeMaassDeepLVDeficitScaleV1
public import QuantitativeMaassStrongUniformCentreV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap
namespace QuantitativeMaass.Strong

/-- The actual LV deficit is negligible on a whole exponentially growing
cuspidal band, with one common deep degree and all squared-triplelog losses.
The only width hypothesis is the original epsilon times triple-log divergence. -/
theorem weighted_wide_LV_deficit_family_density (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (U W : ℝ) (hU : 0≤U) (ε : ℝ→ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ G : ℝ→ℝ,Tendsto (fun t => Real.exp (W*strongScale t)*G t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ {ι : Type*} [Fintype ι] (v : ι→AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ (r τ : ι→ℝ),
      (∀ i,r i∈Icc (t-Real.exp (U*strongScale t)) (t+Real.exp (U*strongScale t))) →
      (∀ i,FriedrichsGraph N (v i) (((1/4+(r i)^2:ℝ):ℂ) • v i)) →
      (∀ i,HeckeL2.operator N p hN hpN a b hab (v i)=(τ i:ℂ) • v i) →
      (∑ i,(lvDeficitMultiplier p (deepLVDegree t) (r i) (τ i))^2)≤G t := by
  obtain ⟨B,J,A,C,D,E,hB,hJ,hA,hC,hD,hE,hbound⟩ := cuspidal_wide_LV_deficit_family N hN K he hc hK hm
  let m := ∫ x,|x|^2*K x
  have hm0 : 0≤m := integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hK x))
  let R := 4*(m+1)
  have hR1 : 1≤R := by dsimp only [R];linarith only [hm0]
  have hR : 0<R := lt_of_lt_of_le zero_lt_one hR1
  have hhalf : m/(R*(1/4))^2≤1/2 := by
    rw [show R*(1/4)=m+1 by dsimp only [R];ring]
    apply (div_le_iff₀ (by positivity : 0<(m+1)^2)).mpr
    nlinarith only [sq_nonneg m]
  have hcoef : 1/4≤(1-m/(R*(1/4))^2)^2 := by nlinarith only [hhalf]
  let V := B*R+2
  have hV : 0≤V := by dsimp only [V];positivity
  let H := fun t => Real.exp (V+(deepLVDegree t:ℝ))
  let P := 2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|
  let G := fun t => (32*D)*t*Real.exp (U*strongScale t)*lvSphericalDeficit p (2*deepLVDegree t)+
    (16*C*Real.sqrt 2)*Real.sqrt t*Real.exp (U*strongScale t)*
      Real.exp (A*R+30*Real.log (E*(H t+3)^2)+(2*P)*(deepLVDegree t:ℝ))+
    (32*J)*t*Real.exp (U*strongScale t)/H t
  refine ⟨G,?_,?_⟩
  · have hmain := (deepLV_deficit_decay p ε (W+U) hε hproduct).const_mul (32*D)
    have hgeo := deepLV_cutoff_geometric_decay ε (16*C*Real.sqrt 2) (A*R) E V (2*P) (W+U)
      (by positivity) (lt_of_lt_of_le zero_lt_one hE) hV hε hproduct
    have htail := (deepLV_cutoff_tail_decay ε (W+U) V hV hε hproduct).const_mul (32*J)
    have hh := (hmain.add hgeo).add htail
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp only [G,H]
    rw [show (W+U)*strongScale t=W*strongScale t+U*strongScale t by ring]
    simp only [Real.exp_add]
    field_simp
  · filter_upwards [exponential_band_width_quarter U hU,eventually_ge_atTop (6:ℝ)] with t hwidth ht
    intro ι _ v hv hcus r τ hr hgraph heigen
    have hHt : 2≤H t := by
      have hh := Real.add_one_le_exp (V+(deepLVDegree t:ℝ))
      dsimp only [H,V] at *
      have hpos : 0≤B*R+(deepLVDegree t:ℝ) := by positivity
      linarith only [hh,hpos]
    have hheight : B*R<Real.log (H t) := by
      dsimp only [H]
      rw [Real.log_exp]
      dsimp only [V]
      have hn := Nat.cast_nonneg (deepLVDegree t) (α:=ℝ)
      linarith only [hn]
    have hh := hbound p hpN hNp hpres a b hab R hR hR1 (hhalf.trans (by norm_num))
      t (H t) (Real.exp (U*strongScale t)) ht hHt hwidth.1 hwidth.2 hheight
      (deepLVDegree t) (deepLVDegree_pos t) v hv hcus r τ hr hgraph heigen
    have hsum : 0≤∑ i,(lvDeficitMultiplier p (deepLVDegree t) (r i) (τ i))^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hco := mul_le_mul_of_nonneg_right hcoef hsum
    have hupper := hco.trans hh
    have heq : 4*(4*Real.exp (U*strongScale t)*(D*(2*t)*lvSphericalDeficit p (2*deepLVDegree t)+
        C*Real.sqrt (2*t)*Real.exp (A*R+30*Real.log (E*(H t+3)^2)+P*((2*deepLVDegree t:ℕ):ℝ))+
        J*(2*t)/H t))=G t := by
      dsimp only [G]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
      push_cast
      ring
    have hs := mul_le_mul_of_nonneg_left hupper (by norm_num : (0:ℝ)≤4)
    change 4*((1/4)*(∑ i,(lvDeficitMultiplier p (deepLVDegree t) (r i) (τ i))^2))≤_ at hs
    rw [heq] at hs
    nlinarith only [hs]

#print axioms weighted_wide_LV_deficit_family_density
end QuantitativeMaass.Strong
