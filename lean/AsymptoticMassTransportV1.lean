module

public import AsymptoticRationalGroupV1
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
@[expose] public section

namespace AsymptoticMassTransport

open MeasureTheory Set UpperHalfPlane
open scoped ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
variable {μ : Measure α}

/-- Nonnegative mass transport for a countable measure-preserving group
action. Infinite rows and columns are allowed by Tonelli's theorem. -/
theorem indexed_transport (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (K : G → α → ℝ≥0∞) (hK : ∀ g, Measurable (K g)) :
    (∫⁻ x,∑' g,K g x ∂μ)=(∫⁻ x,∑' g,K g⁻¹ (g • x) ∂μ) := by
  have hK' (g : G) : AEMeasurable (fun x : α => K g⁻¹ (g • x)) μ :=
    ((hK g⁻¹).comp (hmp g).measurable).aemeasurable
  rw [lintegral_tsum (μ := μ) (fun g => (hK g).aemeasurable),
    lintegral_tsum (μ := μ) hK']
  have he (g : G) : (∫⁻ x,K g⁻¹ (g • x) ∂μ)=∫⁻ x,K g⁻¹ x ∂μ :=
    (hmp g).lintegral_comp (hK g⁻¹)
  simp_rw [he]
  exact ((Equiv.inv G).tsum_eq (fun g => ∫⁻ x,K g x ∂μ)).symm

/-- A branch is retained only when both its source and target belong to
the selected measurable region, such as the translation strip. -/
noncomputable def restrictedKernel (s : Set α) (F : α → α → ℝ≥0∞) (g : G) (x : α) : ℝ≥0∞ :=
  (s∩(fun y => g • y) ⁻¹' s).indicator (fun y => F y (g • y)) x

omit [Countable G] in
theorem restrictedKernel_measurable
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    {s : Set α} (hs : MeasurableSet s) (F : α → α → ℝ≥0∞)
    (hF : Measurable (fun p : α×α => F p.1 p.2)) (g : G) :
    Measurable (restrictedKernel s F g) :=
  (hF.comp (measurable_id.prodMk (hmp g).measurable)).indicator
    (hs.inter (hs.preimage (hmp g).measurable))

/-- Mass transport remains valid after restricting to the translation
strip. On the conull free set, each retained projective label represents
one distinct point of the rational orbit. -/
theorem restricted_transport
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    {s : Set α} (hs : MeasurableSet s) (F : α → α → ℝ≥0∞)
    (hF : Measurable (fun p : α×α => F p.1 p.2)) :
    (∫⁻ x,∑' g : G,restrictedKernel s F g x ∂μ)=
      (∫⁻ x,∑' g : G,restrictedKernel s (fun y z => F z y) g x ∂μ) := by
  classical
  rw [indexed_transport hmp _ (restrictedKernel_measurable hmp hs F hF)]
  apply lintegral_congr
  intro x
  apply tsum_congr
  intro g
  simp only [restrictedKernel,Set.indicator_apply,Set.mem_inter_iff,Set.mem_preimage,
    inv_smul_smul,and_comm]

/-- The actual rational-projective action satisfies the transport
identity with hyperbolic area, without finite-support assumptions. -/
theorem rational_transport {s : Set ℍ} (hs : MeasurableSet s) (F : ℍ → ℍ → ℝ≥0∞)
    (hF : Measurable (fun p : ℍ×ℍ => F p.1 p.2)) :
    (∫⁻ x,∑' g : AsymptoticRationalGroup.Group,restrictedKernel s F g x)=
      (∫⁻ x,∑' g : AsymptoticRationalGroup.Group,restrictedKernel s (fun y z => F z y) g x) :=
  restricted_transport AsymptoticRationalGroup.measurePreserving hs F hF

/-- The half-open fundamental strip for integral translations. -/
def strip : Set ℍ := {z | z.re∈Set.Ico 0 1}

theorem strip_measurable : MeasurableSet strip :=
  measurableSet_Ico.preimage continuous_re.measurable

theorem strip_transport (F : ℍ → ℍ → ℝ≥0∞)
    (hF : Measurable (fun p : ℍ×ℍ => F p.1 p.2)) :
    (∫⁻ x,∑' g : AsymptoticRationalGroup.Group,restrictedKernel strip F g x)=
      (∫⁻ x,∑' g : AsymptoticRationalGroup.Group,
        restrictedKernel strip (fun y z => F z y) g x) :=
  rational_transport strip_measurable F hF

#print axioms indexed_transport
#print axioms restricted_transport
#print axioms rational_transport
#print axioms strip_transport

end AsymptoticMassTransport
