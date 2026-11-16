module

public import QuantitativeMaassSpectralPartitionV1
public import QuantitativeMaassWindowSpectralScalarV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The weighted sum over the literal principal spectral interval. Its
finiteness for actual cusp eigenfamilies is proved independently. -/
def principalWindowWeight {ι : Type*} (e w : ι → ℝ) (a b : ℝ) : ℝ :=
  ∑' i : principalWindowIndices e a b,w i.val

/-- Any [0,1]-weighted actual cusp spectrum admits a sharp interval
comparison. Both error terms are literal unweighted spectral sums. -/
theorem window_weighted_sharp_comparison {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he0 : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (w : ι → ℝ) (hw : ∀ i,w i∈Icc (0:ℝ) 1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (t ε δ R : ℝ) (ht : 0<t) (hε : ε≤1) (hδ : 0<δ) (hδ1 : δ≤1) (hR : 0<R) :
    let m := fun i => ‖smoothPacketMultiplier
      (windowTimeSchwartz K hc R hR (t+δ) (t+ε-δ)) (e i)‖^2
    Summable (fun i => m i*w i) ∧
    (∑' i,m i*w i)≤principalWindowWeight e w t (t+ε)+
      (∑' i : {i // 1/4≤e i ∧ Real.sqrt (e i-1/4)∉Icc t (t+ε)},
        (smoothedWindow K R (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ)))
          (Real.sqrt (e i.val-1/4)))^2)+
      (∑' i : {i // e i≤1/4},m i.val) := by
  let S := principalWindowIndices e t (t+ε)
  let T := {i | 1/4≤e i ∧ Real.sqrt (e i-1/4)∉Icc t (t+ε)}
  let U := {i | e i≤1/4}
  let m := fun i => ‖smoothPacketMultiplier
    (windowTimeSchwartz K hc R hR (t+δ) (t+ε-δ)) (e i)‖^2
  let g := fun i => (smoothedWindow K R
    (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) (Real.sqrt (e i-1/4)))^2
  have hid (i : ι) (hi : 1/4≤e i) : m i=g i :=
    windowTimeSchwartz_principal_norm_square K he hc R hR _ _ (by positivity) _ hi
  have hcover (i : ι) : i∈S ∨ i∈T ∨ i∈U := by
    by_cases hi : 1/4≤e i
    · by_cases hr : Real.sqrt (e i-1/4)∈Icc t (t+ε)
      · exact Or.inl ⟨hi,hr⟩
      · exact Or.inr (Or.inl ⟨hi,hr⟩)
    · exact Or.inr (Or.inr (le_of_not_ge hi))
  obtain ⟨C,hC,hleak⟩ := principal_trimmed_window_leakage N hN
  have hT : Summable (fun i : T => g i.val) :=
    (hleak ι v hv hcusp e he0 hgraph K hK t ε δ R ht hε hδ hδ1 hR).1
  have hU : Summable (fun i : U => m i.val) :=
    exceptional_window_scalar_summable N hN v hv hcusp e he0 hgraph K hc R hR _ _
  apply spectral_partition_majorant S T U hcover
    (principalWindowIndices_finite N hN v hv hcusp e he0 hgraph _ _) (fun i => m i*w i) w g m
    (fun i => mul_nonneg (sq_nonneg _) (hw i).1) (fun i => (hw i).1)
    (fun i => sq_nonneg _) (fun i => sq_nonneg _) _ _ _ hT hU
  · intro i hi
    rw [hid i hi.1]
    have hb := (smoothedWindow_square_mem_unit K hK hm R hR
      (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) (Real.sqrt (e i-1/4))).2
    exact mul_le_of_le_one_left (hw i).1 hb
  · intro i hi
    rw [hid i hi.1]
    exact mul_le_of_le_one_right (sq_nonneg _) (hw i).2
  · intro i _
    exact mul_le_of_le_one_right (sq_nonneg _) (hw i).2

#print axioms window_weighted_sharp_comparison

end QuantitativeMaass
