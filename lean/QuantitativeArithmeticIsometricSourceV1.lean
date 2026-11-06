module

public import QuantitativeEulerEndpointIsometricImageV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticIsometricSource
open ContinuousLinearMap QuantitativeEulerEndpointIsometricImage
open AsymptoticRegularTrace MeasureTheory
open scoped lp

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : H →L[ℂ] H) (T : Submodule ℂ H) [CompleteSpace T]
  (hi : ∀v∈T,‖U v‖=‖v‖) (hg : U.adjoint.comp U=T.starProjection)

include hg

/-- The actual adjoint inverts a partial isometry on its closed image. -/
theorem inverse_image {y : H} (hy : y∈imageSpace U T hi) :
    U.adjoint y∈T ∧ U (U.adjoint y)=y ∧ ‖U.adjoint y‖=‖y‖ := by
  rcases hy with ⟨v,he⟩
  have hv : (v : H)∈T := v.property
  have hleft : U.adjoint (U v)=(v : H) :=
    (congrArg (fun B : H →L[ℂ] H => B v) hg).trans (T.starProjection_eq_self_iff.mpr hv)
  have hinv : U.adjoint y=(v : H) := (congrArg U.adjoint he).symm.trans hleft
  rw [hinv]
  exact ⟨hv,he,(hi v hv).symm.trans (congrArg norm he)⟩

variable (V : Submodule ℂ H) [CompleteSpace V] (hV : V ≤ imageSpace U T hi)

def pullback : Submodule ℂ H :=
  imageSpace U.adjoint V (fun _y hy => (inverse_image U T hi hg (hV hy)).2.2)

instance pullback_complete : CompleteSpace (pullback U T hi hg V hV) :=
  imageSpace_complete _ _ _

theorem pullback_projection :
    (pullback U T hi hg V hV).starProjection=U.adjoint.comp (V.starProjection.comp U) := by
  exact (image_projection _ _ _).trans (by rw [adjoint_adjoint])

theorem pullback_le : pullback U T hi hg V hV≤T := by
  rintro v ⟨y,he⟩
  exact he ▸ (inverse_image U T hi hg (hV y.property)).1

theorem pullback_forward {v : H} (hv : v∈pullback U T hi hg V hV) :
    U v∈V ∧ ‖U v‖=‖v‖ := by
  rcases hv with ⟨y,he⟩
  have hinv := inverse_image U T hi hg (hV y.property)
  have hy : U v=(y : H) := (congrArg U he).symm.trans hinv.2.1
  exact ⟨hy.symm ▸ y.property,(congrArg norm hy).trans (hinv.2.2.symm.trans (congrArg norm he))⟩
end Hilbert

section Regular
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
variable (U : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (T V : α → Submodule ℂ ℓ²(G,ℂ)) [∀x,CompleteSpace (T x)] [∀x,CompleteSpace (V x)]
  (hi : ∀x v,v∈T x → ‖U x v‖=‖v‖)
  (hg : ∀x,(U x).adjoint.comp (U x)=(T x).starProjection)
  (hV : ∀x,V x ≤ imageSpace (U x) (T x) (hi x))
  (hmU : ∀g h,Measurable (fun x => matrix (U x) g h)) (hcU : Covariant U)
  (hmV : ∀g h,Measurable (fun x => matrix (V x).starProjection g h))
  (hcV : Covariant (fun x => (V x).starProjection))

include hmU hcU hmV hcV

theorem pullback_regular :
    (∀g h,Measurable (fun x => matrix (pullback (U x) (T x) (hi x) (hg x) (V x) (hV x)).starProjection g h)) ∧
    Covariant (fun x => (pullback (U x) (T x) (hi x) (hg x) (V x) (hV x)).starProjection) := by
  simp only [pullback_projection]
  exact ⟨matrix_comp_measurable _ _ (matrix_adjoint_measurable _ hmU)
      (matrix_comp_measurable _ _ hmV hmU),
    covariant_comp _ _ (covariant_adjoint _ hcU) (covariant_comp _ _ hcV hcU)⟩

theorem pullback_trace (μ : Measure α)
    (hmp : ∀g : G,MeasurePreserving (fun x : α => g • x) μ μ) :
    trace μ (fun x => (pullback (U x) (T x) (hi x) (hg x) (V x) (hV x)).starProjection)=
      trace μ (fun x => (V x).starProjection) :=
  image_trace μ hmp (fun x => (U x).adjoint) V
    (fun x _y hy => (inverse_image (U x) (T x) (hi x) (hg x) (hV x hy)).2.2)
    (matrix_adjoint_measurable _ hmU) (covariant_adjoint _ hcU) hmV hcV
end Regular

#print axioms inverse_image
#print axioms pullback_projection
#print axioms pullback_le
#print axioms pullback_forward
#print axioms pullback_regular
#print axioms pullback_trace
end QuantitativeArithmeticIsometricSource
