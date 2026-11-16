module

public import QuantitativeMaassBoundedConjugationV1
public import QuantitativeMaassCappedWeightV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
  (μ : Measure α) (l : α → ℝ) (hl : Measurable l)
  (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)

/-- Finite propagation on an actual L2 space, stated using its measurable
support projections. -/
def HasMetricPropagation (R : ℝ) : Prop :=
  ∀ (s u : Set α) (hs : MeasurableSet s) (hu : MeasurableSet u),
    (∀ x∈s,∀ y∈u,R<dist x y) → ∀ f : Lp ℂ 2 μ,
      AsymptoticRegionL2.projection μ s hs (T (AsymptoticRegionL2.projection μ u hu f))=0

/-- A Lipschitz logarithmic weight turns geometric propagation into a
finite integer band width. -/
theorem band_propagation_of_metric (L R : ℝ) (hL : 0≤L)
    (hlip : ∀ x y,|l x-l y|≤L*dist x y) (hT : HasMetricPropagation μ T R) :
    HasBandPropagation μ l hl T ⌈L*R+1⌉₊ := by
  intro n m hnm f
  apply hT (region l n) (region l m) (region_measurable l hl n) (region_measurable l hl m)
  intro x hx y hy
  by_contra hdist
  have hd := (hlip x y).trans (mul_le_mul_of_nonneg_left (le_of_not_gt hdist) hL)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hd
  have hsep : |(n:ℝ)-(m:ℝ)|<L*R+1 :=
    abs_lt.mpr ⟨by linarith [hx.2,hy.1],by linarith [hx.1,hy.2]⟩
  have hnm' : (⌈L*R+1⌉₊:ℝ) < |(n:ℝ)-(m:ℝ)| := by exact_mod_cast hnm
  have hc : L*R+1≤(⌈L*R+1⌉₊:ℝ) := Nat.le_ceil _
  linarith

def metricConjugation (L R : ℝ) (hL : 0≤L)
    (hlip : ∀ x y,|l x-l y|≤L*dist x y) (hT : HasMetricPropagation μ T R) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  boundedConjugation μ l hl T ⌈L*R+1⌉₊ (band_propagation_of_metric μ l hl T L R hL hlip hT)

/-- The complete finite-propagation weight-band estimate, with explicit
absolute constant 5. No boundedness of the inverse weight is assumed. -/
theorem metricConjugation_norm_bound (L R : ℝ) (hL : 0≤L) (hR : 0≤R)
    (hlip : ∀ x y,|l x-l y|≤L*dist x y) (hT : HasMetricPropagation μ T R) :
    ‖metricConjugation μ l hl T L R hL hlip hT‖≤
      5*(1+L*R)*Real.exp (L*R+3)*‖T‖ := by
  have h := boundedConjugation_norm_bound μ l hl T ⌈L*R+1⌉₊
    (band_propagation_of_metric μ l hl T L R hL hlip hT)
  apply h.trans
  have hc : (⌈L*R+1⌉₊:ℝ)<L*R+2 := by
    have hceil := Nat.ceil_lt_add_one (show 0≤L*R+1 by positivity)
    linarith
  have hLR : 0≤L*R := mul_nonneg hL hR
  have hmult : ((2*⌈L*R+1⌉₊+1:ℕ):ℝ)≤5*(1+L*R) := by
    push_cast
    linarith
  have hexp : Real.exp ((⌈L*R+1⌉₊:ℝ)+1)≤Real.exp (L*R+3) :=
    Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hmult hexp (Real.exp_pos _).le (by positivity)) (norm_nonneg T)

#print axioms band_propagation_of_metric
#print axioms metricConjugation_norm_bound

end QuantitativeMaass.LogBands
