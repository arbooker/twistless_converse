module

public import QuantitativeMaassUnitBandCoverV1
public import QuantitativeMaassUniformCentreBoundsV1
public import QuantitativeMaassWeightedHeckeDensityV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- The actual exceptional-family estimate remains negligible on an
exponentially growing spectral band. All uniformity over the many unit
windows is derived from the previously proved common majorant. -/
theorem weighted_wide_hecke_exceptional_family_density (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (u v : ℤ) (huv : (p:ℤ)*u+(N:ℤ)*v=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (q : ℝ) (hq : 2<q) (D W : ℝ) (hD : 0≤D) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ G : ℝ → ℝ,Tendsto (fun t => Real.exp (W*fourthRootScale t)*G t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ {ι : Type*} [Fintype ι] (f : ι → AutomorphicSpace N),Orthonormal ℂ f →
      (∀ i,f i∈localCuspidalSpace N hN) → ∀ (r τ : ι → ℝ),
      (∀ i,r i∈Icc (t-Real.exp (D*fourthRootScale t)) (t+Real.exp (D*fourthRootScale t))) →
      (∀ i,FriedrichsGraph N (f i) (((1/4+(r i)^2:ℝ):ℂ) • f i)) →
      (∀ i,HeckeL2.operator N p hN hpN u v huv (f i)=(τ i:ℂ) • f i) →
      (∀ i,q≤|τ i|) → (Fintype.card ι:ℝ)≤G t := by
  let A := 2*(|W|+D+1)
  have hA : 0≤A := by dsimp only [A]; positivity
  obtain ⟨g,hg,hunit⟩ := weighted_cuspidal_hecke_exceptional_family_density N p hN hpN hNp
    u v huv K he hc hK hm q hq A (fun _ => 1)
    (Eventually.of_forall (fun _ => by norm_num)) (by simpa only [one_mul] using slowScale_tendsto)
  simp only [mul_one] at hg
  obtain ⟨T,hT⟩ := eventually_atTop.mp hunit
  let G := fun t => 8*t*Real.exp ((D-A/2)*fourthRootScale t)
  refine ⟨G,?_,?_⟩
  · have hlim := (fourthRoot_exponential_div_width ε hε hproduct).const_mul 8
    simp only [mul_zero] at hlim
    apply squeeze_zero' _ _ hlim
    · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
      dsimp only [G]
      positivity
    · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
      have hroot : 0≤fourthRootScale t := Real.sqrt_nonneg _
      have hexp : W*fourthRootScale t+(D-A/2)*fourthRootScale t≤-fourthRootScale t := by
        have hh := mul_le_mul_of_nonneg_right (le_abs_self W) hroot
        dsimp only [A]
        nlinarith only [hh]
      have hid : Real.exp (W*fourthRootScale t)*G t/(t*ε t)=
          8*(Real.exp (W*fourthRootScale t+(D-A/2)*fourthRootScale t)/ε t) := by
        dsimp only [G]
        rw [Real.exp_add]
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) heps.le) (by norm_num)
  · filter_upwards [weighted_decay_finite_cover g A D 4 hA hg,
      exponential_band_width_quarter D hD,eventually_ge_atTop (6:ℝ),
      eventually_ge_atTop (2*T)] with t hwide hwidth ht htT
    intro ι _ f hf hcus r τ hr hgraph heigen hτ
    classical
    obtain ⟨n,hn,s,hs,hcover⟩ := unit_band_cover t (Real.exp (D*fourthRootScale t))
      ht hwidth.1 hwidth.2
    let P := fun j : Fin n => fun i : ι => r i∈Icc (s j-1/2) (s j+1/2)
    have hbound (j : Fin n) : (Fintype.card {i // P j i}:ℝ)≤g (s j) := by
      have hjT : T≤s j := by have hh := (hs j).1; linarith
      exact hT (s j) hjT (fun i : {i // P j i} => f i)
        (hf.comp Subtype.val Subtype.val_injective) (fun i => hcus i)
        (fun i => r i) (fun i => τ i) (fun i => i.property)
        (fun i => hgraph i) (fun i => heigen i) (fun i => hτ i)
    have hcard := finite_cover_card_le P (fun i => hcover (r i) (hr i))
    calc
      (Fintype.card ι:ℝ) ≤ ∑ j : Fin n,(Fintype.card {i // P j i}:ℝ) := by
        exact_mod_cast hcard
      _ ≤ ∑ j : Fin n,g (s j) := Finset.sum_le_sum (fun j _ => hbound j)
      _ ≤ G t := by
        have hh := hwide s hs (by simpa only [Fintype.card_fin] using hn)
        simpa only [G,show (2:ℝ)*4=8 by norm_num] using hh

#print axioms weighted_wide_hecke_exceptional_family_density

end QuantitativeMaass
