module

public import QuantitativeMaassSpectralCutoffOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The explicitly constructed continuous cutoffs converge strongly to the
identity. Dense range excludes a zero-resolvent component; no discrete
spectral decomposition or eigenbasis is used. -/
theorem resolventCutoffOperator_tendsto {ι : Type*} (l : Filter ι)
    (A : H →L[ℂ] H) (hp : A.IsPositive) (hn : ‖A‖≤1) (hd : DenseRange A)
    (ε : ι → ℝ) (hε : ∀ᶠ i in l,0<ε i) (hε0 : Tendsto ε l (𝓝 0)) (v : H) :
    Tendsto (fun i => resolventCutoffOperator A (ε i) v) l (𝓝 v) := by
  have hz : Tendsto (fun i => (resolventCutoffOperator A (ε i)-1) v) l (𝓝 0) := by
    apply tendsto_zero_of_dense_range_eventually A hd
    · filter_upwards [hε] with i hi
      have h1 := resolventCutoffOperator_norm_le A (ε i) hi
      have h2 : ‖(1:H →L[ℂ] H)‖≤1 := ContinuousLinearMap.norm_id_le
      exact (norm_sub_le _ _).trans (by linarith)
    · intro w
      apply squeeze_zero_norm'
      · filter_upwards [hε] with i hi
        change ‖((resolventCutoffOperator A (ε i)-1)*A) w‖≤ε i*‖w‖
        exact (((resolventCutoffOperator A (ε i)-1)*A).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (resolventCutoffOperator_residual_norm A hp hn (ε i) hi)
            (norm_nonneg _))
      · simpa only [zero_mul] using hε0.mul_const ‖w‖
  have h := hz.add_const v
  simpa only [sub_apply,one_apply_eq_self,sub_add_cancel,zero_add] using h

theorem friedrichsCutoff_tendsto {ι : Type*} (l : Filter ι) (N : ℕ)
    (ε : ι → ℝ) (hε : ∀ᶠ i in l,0<ε i) (hε0 : Tendsto ε l (𝓝 0)) (v : AutomorphicSpace N) :
    Tendsto (fun i => resolventCutoffOperator (friedrichsResolvent N) (ε i) v) l (𝓝 v) :=
  resolventCutoffOperator_tendsto l _ (friedrichsResolvent_isPositive N)
    (friedrichsResolvent_opNorm_le N) (friedrichsResolvent_denseRange N) ε hε hε0 v

theorem friedrichsCutoff_preserves_graph (N : ℕ) (ε : ℝ)
    {x y : AutomorphicSpace N} (h : FriedrichsGraph N x y) :
    FriedrichsGraph N (resolventCutoffOperator (friedrichsResolvent N) ε x)
      (resolventCutoffOperator (friedrichsResolvent N) ε y) := by
  let P := resolventCutoffOperator (friedrichsResolvent N) ε
  have hc := congrArg (fun B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => B (x+y))
    (resolventCutoffOperator_commute (friedrichsResolvent N) (friedrichsResolvent_isSelfAdjoint N) ε).eq
  change P (friedrichsResolvent N (x+y))=friedrichsResolvent N (P (x+y)) at hc
  change friedrichsResolvent N (P x+P y)=P x
  rw [← map_add,← hc,h]

/-- On every full Friedrichs graph pair, applying the cutoff turns the
unbounded Laplacian into the constructed bounded regularized operator. -/
theorem friedrichsCutoff_generator_on_graph (N : ℕ) (ε : ℝ) (hε : 0<ε)
    {x y : AutomorphicSpace N} (h : FriedrichsGraph N x y) :
    resolventCutoffOperator (friedrichsResolvent N) ε y=
      boundedResolventOperator (friedrichsResolvent N) ε
        (resolventCutoffOperator (friedrichsResolvent N) ε x) := by
  have h1 := friedrichsCutoff_graph N ε hε x
  have h2 := friedrichsCutoff_preserves_graph N ε h
  have he := (friedrichsResolvent_injective N) (h1.trans h2.symm)
  exact (add_left_cancel he).symm

#print axioms resolventCutoffOperator_tendsto
#print axioms friedrichsCutoff_tendsto
#print axioms friedrichsCutoff_generator_on_graph

end QuantitativeMaass.Wave
