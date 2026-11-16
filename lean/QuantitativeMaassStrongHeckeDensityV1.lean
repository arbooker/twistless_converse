module

public import QuantitativeMaassHeckeExceptionalFamilyV1
public import QuantitativeMaassGrowingCuspLimitV1
public import QuantitativeMaassStrongCuspLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap

namespace QuantitativeMaass.Strong

/-- Every finite orthonormal family of actual cuspidal joint eigenvectors
whose classical Hecke eigenvalues exceed a fixed threshold above two has
cardinality o(t epsilon(t) exp(-W slowScale(t))), uniformly over families
in the unit window. The exponential weight pays for growing reconstruction words. -/
theorem weighted_cuspidal_hecke_exceptional_family_density (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (u v : ℤ) (huv : (p:ℤ)*u+(N:ℤ)*v=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (q : ℝ) (hq : 2<q) (W : ℝ) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ g : ℝ → ℝ,Tendsto (fun t => Real.exp (W*strongScale t)*g t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ {ι : Type*} [Fintype ι] (f : ι→AutomorphicSpace N),Orthonormal ℂ f →
      (∀ i,f i∈localCuspidalSpace N hN) → ∀ (r τ : ι→ℝ),
      (∀ i,r i∈Icc (t-1/2) (t+1/2)) →
      (∀ i,FriedrichsGraph N (f i) (((1/4+(r i)^2:ℝ):ℂ) • f i)) →
      (∀ i,HeckeL2.operator N p hN hpN u v huv (f i)=(τ i:ℂ) • f i) →
      (∀ i,q≤|τ i|) → (Fintype.card ι:ℝ)≤g t := by
  obtain ⟨B,J,A,C,D,E,hB,hJ,hA,hC,hD,hE,hbound⟩ :=
    cuspidal_hecke_exceptional_family_bound N hN K he hc hK hm
  let m := ∫ x,|x|^2*K x
  have hm0 : 0≤m := integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hK x))
  let R := 4*(m+1)
  have hR1 : 1≤R := by dsimp only [R];linarith only [hm0]
  have hR : 0<R := lt_of_lt_of_le zero_lt_one hR1
  have hhalf : m/(R*(1/4))^2≤1/2 := by
    have heq : R*(1/4)=m+1 := by dsimp only [R];ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0<(m+1)^2)).mpr
    nlinarith only [sq_nonneg m]
  have hcoef : 1/4≤(1-m/(R*(1/4))^2)^2 := by nlinarith only [hhalf]
  have hqp : 0<q := by linarith only [hq]
  have hpp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  let a := ((2:ℝ)/q)^2
  let b := (heckeWordErrorGrowth p/q)^2
  let c := ((((p:ℝ)+1)/Real.sqrt (p:ℝ))/q)^2
  have ha : 0<a := by dsimp only [a];positivity
  have ha1 : a<1 := by
    have hh : (2:ℝ)/q<1 := (div_lt_one hqp).mpr hq
    have hp : 0<(2:ℝ)/q := by positivity
    dsimp only [a]
    nlinarith only [hh,hp]
  have hb : 0<b := by dsimp only [b,heckeWordErrorGrowth];positivity
  have hc0 : 0<c := by dsimp only [c];positivity
  let L := 1+|Real.log c|
  let V := B*R+2
  have hL : 0<L := (growing_cusp_slope c hc0).1
  have hdecay : c*Real.exp (-L)<1 := (growing_cusp_slope c hc0).2
  have hV : 0≤V := by dsimp only [V];positivity
  let H (t : ℝ) := Real.exp (V+L*(growingLVDegree t:ℝ))
  let g (t : ℝ) :=
    (4*D)*t*a^(growingLVDegree t)+
    (4*C)*Real.sqrt t*b^(growingLVDegree t)*Real.exp (A*R+30*Real.log (E*(H t+3)^2))+
    (4*J)*t*c^(growingLVDegree t)/H t
  refine ⟨g,?_,?_⟩
  · have hmain : Tendsto (fun t => Real.exp (W*strongScale t)*(4*D)*t*a^(growingLVDegree t)/(t*ε t)) atTop (𝓝 0) := by
      have hh := (weighted_growingMomentDegree_decay ε a W ha ha1 hε hproduct).const_mul (4*D)
      simp only [mul_zero] at hh
      apply hh.congr'
      filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
      field_simp
    have hgeo := weighted_growing_cusp_geometric_limit ε b (4*C) (A*R) E V L W hb (by positivity)
      (lt_of_lt_of_le zero_lt_one hE) hV hL.le hε hproduct
    have htail := weighted_growing_cusp_tail_limit ε c (4*J) V L W hc0 hdecay hε hproduct
    have hsum := (hmain.add hgeo).add htail
    simp only [add_zero] at hsum
    convert hsum using 1
    funext t
    dsimp only [g,H]
    ring
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    intro ι _ f hf hcus r τ hr hgraph heigen hτ
    let d := growingLVDegree t
    have hHt : 2≤H t := by
      have hh := Real.add_one_le_exp (V+L*(d:ℝ))
      change 2≤Real.exp (V+L*(d:ℝ))
      have hv2 : 2≤V+L*(d:ℝ) := by
        have hp : 0≤B*R+L*(d:ℝ) := by positivity
        dsimp only [V]
        linarith only [hp]
      linarith only [hh,hv2]
    have hheight : B*R<Real.log (H t) := by
      dsimp only [H]
      rw [Real.log_exp]
      dsimp only [V]
      have hn : 0≤L*(growingLVDegree t:ℝ) := by positivity
      linarith only [hn]
    have hh := hbound p hpN hNp u v huv R hR hR1 (hhalf.trans (by norm_num))
      t (H t) ht hHt hheight f hf hcus r τ hr hgraph heigen q hqp.le hτ d
    have hcard : (q^(2*d)/4)*(Fintype.card ι:ℝ)≤
        D*t*(2:ℝ)^(2*d)+C*(heckeWordErrorGrowth p)^(2*d)*Real.sqrt t*
          Real.exp (A*R+30*Real.log (E*(H t+3)^2))+
        (((p:ℝ)+1)/Real.sqrt (p:ℝ))^(2*d)*(J*t/H t) := by
      apply le_trans _ hh
      have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity : 0≤q^(2*d)))
        (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ)≤Fintype.card ι)
      convert hb using 1
      ring
    have heq : q^(2*d)/4*g t=
        D*t*(2:ℝ)^(2*d)+C*(heckeWordErrorGrowth p)^(2*d)*Real.sqrt t*
          Real.exp (A*R+30*Real.log (E*(H t+3)^2))+
        (((p:ℝ)+1)/Real.sqrt (p:ℝ))^(2*d)*(J*t/H t) := by
      dsimp only [g,a,b,c]
      change q^(2*d)/4*((4*D)*t*((2/q)^2)^d+
        (4*C)*Real.sqrt t*((heckeWordErrorGrowth p/q)^2)^d*Real.exp (A*R+30*Real.log (E*(H t+3)^2))+
        (4*J)*t*(((((p:ℝ)+1)/Real.sqrt (p:ℝ))/q)^2)^d/H t)=_
      simp only [←pow_mul,div_pow]
      field_simp
    rw [←heq] at hcard
    exact le_of_mul_le_mul_left hcard (by positivity : 0<q^(2*d)/4)

#print axioms weighted_cuspidal_hecke_exceptional_family_density

end QuantitativeMaass.Strong
