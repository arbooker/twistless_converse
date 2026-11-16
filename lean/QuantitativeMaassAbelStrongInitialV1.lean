module

public import QuantitativeMaassAbelInitialEnergyV1
public import QuantitativeMaassPoincareBoundedV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Strong initial convergence on the actual dense smooth seed family. -/
theorem abelNormalizedOperator_tendsto_seed {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) [NeZero N] (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (u : SmoothUpperSeed) :
    Tendsto (fun i => abelNormalizedOperator N (R i) (hR i) (poincareSeedVector N u))
      l (𝓝 (poincareSeedVector N u)) := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
  obtain ⟨B,hB,hb⟩ := poincareSeed_representative_bounded N u
  exact abelNormalizedOperator_tendsto_of_representative l N R hR hlim
    (poincareSeedVector N u) (poincareSum (G:=gamma N) (upperFunction u.toFun))
    (poincareSum_continuous _ u.compact (upperFunction_continuous u.smooth))
    (fun γ y => poincareSum_invariant _ γ y) (poincareSeed_representative N u).2.2
    (poincareSeedVector_coeFn N u) B hB hb

/-- The normalized geometric Abel operators converge strongly to identity
on the entire actual quotient L2 space. The extension uses the proved dense
seed family and the uniform contraction bound, with no regularity premise
on the final input vector. -/
theorem abelNormalizedOperator_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) [NeZero N] (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (f : AutomorphicSpace N) :
    Tendsto (fun i => abelNormalizedOperator N (R i) (hR i) f) l (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0<ε/3 := by positivity
  obtain ⟨u,hu⟩ := Metric.denseRange_iff.mp (poincareSeedVector_dense N) f (ε/3) he
  let v := poincareSeedVector N u
  have hv : ‖f-v‖<ε/3 := by simpa only [dist_eq_norm] using hu
  have ht := abelNormalizedOperator_tendsto_seed l N R hR hlim u
  filter_upwards [Metric.tendsto_nhds.mp ht (ε/3) he] with i hi
  let K := abelNormalizedOperator N (R i) (hR i)
  have hmid : ‖K v-v‖<ε/3 := by simpa only [dist_eq_norm] using hi
  have hd : K f-f=K (f-v)+(K v-v)+(v-f) := by
    rw [map_sub]
    abel
  rw [dist_eq_norm]
  change ‖K f-f‖<ε
  rw [hd]
  calc
    _ ≤ (‖K (f-v)‖+‖K v-v‖)+‖v-f‖ := by
      have h1 := norm_add_le (K (f-v)) (K v-v)
      have h2 := norm_add_le (K (f-v)+(K v-v)) (v-f)
      linarith
    _ ≤ (‖f-v‖+‖K v-v‖)+‖v-f‖ := by
      have h := abelNormalizedOperator_apply_norm N (R i) (hR i) (f-v)
      change ‖K (f-v)‖≤‖f-v‖ at h
      linarith
    _ < ε := by rw [norm_sub_rev v f]; linarith

#print axioms abelNormalizedOperator_tendsto_seed
#print axioms abelNormalizedOperator_tendsto

end QuantitativeMaass
