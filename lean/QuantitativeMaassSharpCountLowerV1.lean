module

public import QuantitativeMaassSharpLVLowerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- A bounded weight on the finite literal spectral window is bounded by
its actual cardinality. -/
theorem principalWindowWeight_le_card {ι : Type*} (e w : ι → ℝ) (a b : ℝ)
    (hf : (principalWindowIndices e a b).Finite) (hw : ∀ i,w i≤1) :
    principalWindowWeight e w a b≤(Nat.card (principalWindowIndices e a b):ℝ) := by
  let S := principalWindowIndices e a b
  let : Fintype S := hf.fintype
  change (∑' i : S,w i.val)≤(Nat.card S:ℝ)
  rw [tsum_fintype,Nat.card_eq_fintype_card]
  calc
    _ ≤ ∑ _i : S,(1:ℝ) := Finset.sum_le_sum (fun i _ => hw i.val)
    _ = _ := by simp

theorem principalWindowWeight_add {ι : Type*} (e w z : ι → ℝ) (a b : ℝ)
    (hf : (principalWindowIndices e a b).Finite) :
    principalWindowWeight e (fun i => w i+z i) a b=
      principalWindowWeight e w a b+principalWindowWeight e z a b := by
  let : Fintype (principalWindowIndices e a b) := hf.fintype
  exact Summable.tsum_add Summable.of_finite Summable.of_finite

/-- Summing the two genuine parity LV lower bounds gives the full-volume
sharp cusp counting lower coefficient. This does not assert the upper bound. -/
theorem principal_sharp_count_eventual_lower {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,(quotientMeasure N).real univ/(2*Real.pi)-η<
      (Nat.card (principalWindowIndices e t (t+ε t)):ℝ)/(t*ε t) := by
  obtain ⟨d,hd,hbound⟩ := exists_parity_LV_sharp_window_lower N p hN hpN hNp hpres a b hab
    basis e henergy hgraph (η/2) (by positivity)
  have ho : Orthonormal ℂ (fun j => (basis j:AutomorphicSpace N)) :=
    basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let w := fun σ j => (inner ℂ
    (actualLVFilter N p hN hpN a b hab d (parityProjection N σ (basis j:AutomorphicSpace N)))
    (parityProjection N σ (basis j:AutomorphicSpace N))).re
  have hw (j : κ) : w 1 j+w (-1) j≤1 := by
    have hs := congrArg Complex.re (actualLVFilter_parity_split N p hN hpN hNp a b hab d 1 (by norm_num)
      (basis j:AutomorphicSpace N))
    rw [Complex.add_re] at hs
    have hu := (actualLVFilter_cusp_weight_bounds N p hN hpN hNp hpres a b hab d
      (basis j:AutomorphicSpace N) (basis j).property (ho.norm_eq_one j)).2
    change _=w 1 j+w (-1) j at hs
    linarith only [hs,hu]
  filter_upwards [hbound 1 (by norm_num) ε hε hproduct,
    hbound (-1) (by norm_num) ε hε hproduct,hε,eventually_gt_atTop (0:ℝ)] with t hpos hneg het ht
  have hf := principalWindowIndices_finite N hN _ ho (fun j => (basis j).property) e henergy hgraph t (t+ε t)
  have hc := principalWindowWeight_le_card e (fun j => w 1 j+w (-1) j) t (t+ε t) hf hw
  rw [principalWindowWeight_add e (w 1) (w (-1)) t (t+ε t) hf] at hc
  have hh := div_le_div_of_nonneg_right hc (mul_pos ht het.1).le
  rw [add_div] at hh
  change (quotientMeasure N).real univ/(4*Real.pi)-η/2<principalWindowWeight e (w 1) t (t+ε t)/(t*ε t) at hpos
  change (quotientMeasure N).real univ/(4*Real.pi)-η/2<principalWindowWeight e (w (-1)) t (t+ε t)/(t*ε t) at hneg
  have hconst : (quotientMeasure N).real univ/(2*Real.pi)-η=
      ((quotientMeasure N).real univ/(4*Real.pi)-η/2)+
      ((quotientMeasure N).real univ/(4*Real.pi)-η/2) := by ring
  rw [hconst]
  linarith only [hpos,hneg,hh]

#print axioms principalWindowWeight_le_card
#print axioms principalWindowWeight_add
#print axioms principal_sharp_count_eventual_lower

end QuantitativeMaass
