module

public import QuantitativeNinaMaassEigenSolutionsV1
public import QuantitativeMaassWindowConsequencesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter QuantitativeConcreteGoals
open scoped Topology
namespace QuantitativeMaass

/-- Two sharp lower bounds and a sharp upper bound on their sum force
both individual limits. No regularity of the window width is required. -/
theorem parity_limits_of_total_upper (f g u : ℝ→ℝ) (a : ℝ)
    (hf : ∀ c<a,∀ᶠ t in atTop,c≤f t)
    (hg : ∀ c<a,∀ᶠ t in atTop,c≤g t)
    (hu : Tendsto u atTop (𝓝 (2*a)))
    (hs : ∀ᶠ t in atTop,f t+g t≤u t) :
    Tendsto f atTop (𝓝 a) ∧ Tendsto g atTop (𝓝 a) := by
  have hsingle (f g : ℝ→ℝ)
      (hf : ∀ c<a,∀ᶠ t in atTop,c≤f t)
      (hg : ∀ c<a,∀ᶠ t in atTop,c≤g t)
      (hs : ∀ᶠ t in atTop,f t+g t≤u t) : Tendsto f atTop (𝓝 a) := by
    apply tendsto_order.mpr
    constructor
    · intro c hc
      filter_upwards [hf ((c+a)/2) (by linarith)] with t ht
      linarith
    · intro c hc
      have hup := hu.eventually (gt_mem_nhds (show 2*a<(3*a+c)/2 by linarith))
      filter_upwards [hg ((3*a-c)/2) (by linarith),hup,hs] with t hg hu hs
      linarith
  exact ⟨hsingle f g hf hg hs,hsingle g f hg hf (hs.mono (fun _ h => by linarith))⟩

/-- The literal original count needs only the combined upper estimate:
the already proved newform injection supplies both parity lower bounds.
This is an assembly lemma; its upper estimate remains an explicit input. -/
theorem maassWindow_claims_of_total_upper (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (U : ℝ→ℝ)
    (hU : Tendsto (fun t => U t/(t*ε t)) atTop
      (𝓝 (2*AsymptoticTotalNewCorner.arithmeticCoefficient N)))
    (hfinite : ∀ᶠ t in atTop,(maassWindow N 0 t (ε t)).Finite ∧ (maassWindow N 1 t (ε t)).Finite)
    (hbound : ∀ᶠ t in atTop,((maassWindow N 0 t (ε t)).ncard:ℝ)+
      ((maassWindow N 1 t (ε t)).ncard:ℝ)≤U t) :
    MaassWindowClaim N 0 ε ∧ MaassWindowClaim N 1 ε := by
  let f := fun σ t => ((maassWindow N σ t (ε t)).ncard:ℝ)/(t*ε t)
  have hlower (σ : ℕ) (hσ : σ=0 ∨ σ=1)
      (hf : ∀ᶠ t in atTop,(maassWindow N σ t (ε t)).Finite)
      (c : ℝ) (hc : c<AsymptoticTotalNewCorner.arithmeticCoefficient N) :
      ∀ᶠ t in atTop,c≤f σ t := by
    filter_upwards [QuantitativeNinaMaass.original_maass_solution_ncard_lower N hN σ hσ ε hε hp hf c hc,
      hε,eventually_gt_atTop (0:ℝ)] with t ht he ht0
    exact (le_div_iff₀ (mul_pos ht0 he.1)).mpr ht
  have hsum : ∀ᶠ t in atTop,f 0 t+f 1 t≤U t/(t*ε t) := by
    filter_upwards [hbound,hε,eventually_gt_atTop (0:ℝ)] with t ht he ht0
    dsimp only [f]
    rw [←add_div]
    exact div_le_div_of_nonneg_right ht (mul_pos ht0 he.1).le
  have hh := parity_limits_of_total_upper (f 0) (f 1) (fun t => U t/(t*ε t))
    (AsymptoticTotalNewCorner.arithmeticCoefficient N)
    (hlower 0 (Or.inl rfl) (hfinite.mono (fun _ h => h.1)))
    (hlower 1 (Or.inr rfl) (hfinite.mono (fun _ h => h.2))) hU hsum
  exact ⟨⟨hfinite.mono (fun _ h => h.1),hh.1⟩,⟨hfinite.mono (fun _ h => h.2),hh.2⟩⟩

#print axioms parity_limits_of_total_upper
#print axioms maassWindow_claims_of_total_upper
end QuantitativeMaass
