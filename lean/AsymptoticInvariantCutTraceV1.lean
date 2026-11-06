module

public import AsymptoticInvariantCutSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCoordinateCut

open MeasureTheory Filter AsymptoticRegularTrace AsymptoticOrbitDiagonal
open scoped lp ENNReal Topology

variable {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]

/-- Exhausting coordinate cuts recover the trace of a finite invariant
ambient space. The proof uses its integrable rooted diagonal directly. -/
theorem trace_cutSpace_tendsto (μ : Measure α)
    (U : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)]
    (hm : Measurable (fun x => matrix (U x).starProjection 1 1))
    (s : ℕ → Set α) (hs : ∀ n,MeasurableSet (s n))
    (hinv : ∀ n x v,v∈U x → corner (s n) x v∈U x)
    (hexhaust : ∀ x,∀ᶠ n in atTop,x∈s n)
    (hfin : trace μ (fun x => (U x).starProjection)<∞) :
    Tendsto (fun n => trace μ (fun x => (cutSpace (U x) (s n) x).starProjection)) atTop
      (𝓝 (trace μ (fun x => (U x).starProjection))) := by
  let b : α → ℝ≥0∞ := fun x => ENNReal.ofReal (matrix (U x).starProjection 1 1).re
  have hb : Measurable b := (Complex.continuous_re.measurable.comp hm).ennreal_ofReal
  have he (n : ℕ) (x : α) :
      ENNReal.ofReal (matrix (cutSpace (U x) (s n) x).starProjection 1 1).re=
        (s n).indicator b x := by
    rw [cutSpace_root (U x) (s n) x (hinv n x)]
    classical
    by_cases hx : x∈s n <;> simp [hx,b]
  unfold trace
  simp_rw [he]
  apply tendsto_lintegral_of_dominated_convergence b
  · intro n
    exact hb.indicator (hs n)
  · intro n
    apply Eventually.of_forall
    intro x
    classical
    by_cases hx : x∈s n <;> simp [hx]
  · exact hfin.ne
  · apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [hexhaust x] with n hn
    exact (Set.indicator_of_mem hn b).symm

theorem trace_toReal_cutSpace_tendsto (μ : Measure α)
    (U : α → Submodule ℂ ℓ²(G,ℂ)) [∀ x,CompleteSpace (U x)]
    (hm : Measurable (fun x => matrix (U x).starProjection 1 1))
    (s : ℕ → Set α) (hs : ∀ n,MeasurableSet (s n))
    (hinv : ∀ n x v,v∈U x → corner (s n) x v∈U x)
    (hexhaust : ∀ x,∀ᶠ n in atTop,x∈s n)
    (hfin : trace μ (fun x => (U x).starProjection)<∞) :
    Tendsto (fun n => (trace μ (fun x => (cutSpace (U x) (s n) x).starProjection)).toReal) atTop
      (𝓝 (trace μ (fun x => (U x).starProjection)).toReal) :=
  (ENNReal.tendsto_toReal hfin.ne).comp
    (trace_cutSpace_tendsto μ U hm s hs hinv hexhaust hfin)

#print axioms trace_cutSpace_tendsto
#print axioms trace_toReal_cutSpace_tendsto

end AsymptoticCoordinateCut
