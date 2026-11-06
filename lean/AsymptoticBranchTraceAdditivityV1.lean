module

public import AsymptoticConcreteRationalBranchV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open MeasureTheory UpperHalfPlane Set Filter ContinuousLinearMap InnerProductSpace
open AsymptoticStripCoordinates
open AsymptoticHyperbolicSlash (Space)
open scoped InnerProduct

/-- The exact branch integral formula also supplies summability of the
actual diagonal, needed before distributing a finite branch sum. -/
theorem branch_diagonal_summable (h : ℕ) {ε Y H C : ℝ} (hε : 0<ε) (hY : 0<Y) (hC : 0≤C)
    (W : Space →L[ℂ] Space) (S : Set ℍ) (hS : MeasurableSet S)
    (hstrip : S⊆AsymptoticMassTransport.strip) [IsFiniteMeasure ((volume : Measure ℍ).restrict S)]
    (u : ℍ → ℍ) (hu : Measurable u) (c : ℍ → ℂ)
    (hcmeas : AEStronglyMeasurable c ((volume : Measure ℍ).restrict S))
    (hc : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),‖c z‖≤C)
    (hregion : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      Y≤(u z).im ∧ Y≤z.im ∧ (u z).im≤H ∧ z.im≤H)
    (hact : ∀ n,W (liftedMode h n hε) =ᵐ[volume] S.indicator
      (fun z => c z*(u z).im*unitRepresentative (2*h) 0 n ε (cylinder (u z)))) :
    Summable (fun n => (⟪W (liftedMode h n hε),liftedMode h n hε⟫_ℂ).re) := by
  have hh := hasSum_integral_kernel h hε hY hC u id hu measurable_id c hcmeas hc hregion
  have hr := (Complex.hasSum_re hh).summable
  apply hr.congr
  intro n
  calc
    (∫ z in S,c z*hyperbolicKernelTerm h n ε (u z) z).re =
        (⟪liftedMode h n hε,W (liftedMode h n hε)⟫_ℂ).re :=
      (congrArg Complex.re (branch_diagonal_integral h n hε W S hS hstrip u c (hact n))).symm
    _ = _ := inner_re_symm (𝕜:=ℂ) _ _

theorem liftedTrace_add (h : ℕ) {ε : ℝ} (hε : 0<ε) (W V : Space →L[ℂ] Space)
    (hW : Summable (fun n => (⟪W (liftedMode h n hε),liftedMode h n hε⟫_ℂ).re))
    (hV : Summable (fun n => (⟪V (liftedMode h n hε),liftedMode h n hε⟫_ℂ).re)) :
    liftedTrace h hε (W+V)=liftedTrace h hε W+liftedTrace h hε V := by
  simp only [liftedTrace_eq_sum,add_apply,inner_add_left,Complex.add_re]
  exact hW.tsum_add hV

theorem liftedTrace_list_sum (h : ℕ) {ε : ℝ} (hε : 0<ε) (l : List (Space →L[ℂ] Space))
    (hl : ∀ W∈l,Summable (fun n => (⟪W (liftedMode h n hε),liftedMode h n hε⟫_ℂ).re)) :
    liftedTrace h hε l.sum=(l.map (liftedTrace h hε)).sum := by
  induction l with
  | nil => simp [liftedTrace_eq_sum]
  | cons W l ih =>
    have hW := hl W List.mem_cons_self
    have htail := fun V hV => hl V (List.mem_cons_of_mem W hV)
    have hs : Summable (fun n => (⟪l.sum (liftedMode h n hε),liftedMode h n hε⟫_ℂ).re) := by
      clear ih hl hW W
      induction l with
      | nil => simp
      | cons V l ih =>
        have hv := htail V List.mem_cons_self
        have ht := ih (fun U hU => htail U (List.mem_cons_of_mem V hU))
        simpa only [List.sum_cons,add_apply,inner_add_left,Complex.add_re] using hv.add ht
    simp only [List.sum_cons,List.map_cons]
    rw [liftedTrace_add h hε W l.sum hW hs,ih htail]

#print axioms branch_diagonal_summable
#print axioms liftedTrace_add
#print axioms liftedTrace_list_sum

end AsymptoticUnweightedKernel
