module

public import QuantitativeMaassEulerLevelOneParityCountV1
public import QuantitativeMaassParityShortWeylV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeConcreteGoals AsymptoticClassicalPetersson
open scoped Topology

namespace QuantitativeMaass

theorem level_one_cusp_parity_coefficient :
    (quotientMeasure 1).real univ/(4*Real.pi)=1/12 := by
  rw [Measure.real,quotientMeasure_univ 1 (by norm_num),Subgroup.relIndex_self,
    Nat.cast_one,one_mul,ENNReal.toReal_ofReal (by positivity)]
  field_simp
  ring

/-- Sharp upper coefficient for the literal original level-one Euler window.
The finite window, actual cusp eigenvectors, parity and matching genuine
short-interval Weyl upper bound are all proved inputs. The reverse count
from normalized Hecke eigenforms is still required for the full limit. -/
theorem originalLevelOneWindow_eventual_upper (σ : ℕ) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,((maassWindow 1 σ t (ε t)).ncard:ℝ)/(t*ε t)<1/12+η := by
  obtain ⟨κ,basis,e,henergy,hgraph,_⟩ :=
    QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis 1 (by norm_num)
  have hs : ((-1:ℝ)^σ)^2=1 := by rw [pow_right_comm]; norm_num
  have hw := cuspParityWindow_short_interval_weyl 1 (by norm_num) basis e henergy hgraph
    ((-1:ℝ)^σ) hs ε hε hproduct
  rw [level_one_cusp_parity_coefficient] at hw
  have hu := (tendsto_order.mp hw).2 (1/12+η) (by linarith)
  filter_upwards [hu,hε,eventually_gt_atTop (0:ℝ)] with t ht hεt ht0
  have hc := (originalLevelOneWindow_parity_count basis e henergy hgraph σ t (ε t)).2
  have hcr : ((maassWindow 1 σ t (ε t)).ncard:ℝ)≤
      (Module.finrank ℂ (LinearMap.range (cuspWindowParity 1 (by norm_num) basis e henergy hgraph
        t (t+ε t) ((-1:ℝ)^σ))):ℝ) := by exact_mod_cast hc
  exact (div_le_div_of_nonneg_right hcr (mul_pos ht0 hεt.1).le).trans_lt ht

#print axioms level_one_cusp_parity_coefficient
#print axioms originalLevelOneWindow_eventual_upper

end QuantitativeMaass
