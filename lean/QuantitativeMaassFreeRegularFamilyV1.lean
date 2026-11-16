module

public import QuantitativeMaassRegularWeightedExcessV1
public import AsymptoticRationalGroupV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open scoped lp ENNReal
namespace QuantitativeMaass.FreeRegularFamily
abbrev Group := AsymptoticRationalGroup.Group
abbrev Space := ℓ²(Group,ℂ)
attribute [local instance] Classical.propDecidable

def free (x : ℍ) : Prop := Function.Injective (fun a : Group => a • x)

theorem free_measurable : MeasurableSet {x : ℍ | free x} := by
  have hm (a b : Group) : MeasurableSet {x : ℍ | a • x=b • x → a=b} := by
    by_cases hab : a=b
    · simp only [hab,imp_self,Set.ofPred_true]
      exact MeasurableSet.univ
    · simp only [hab,imp_false]
      exact (measurableSet_eq_fun (AsymptoticRationalGroup.measurePreserving a).measurable
        (AsymptoticRationalGroup.measurePreserving b).measurable).compl
  simp only [free,Function.Injective,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun a => MeasurableSet.iInter (hm a))

theorem free_smul_iff (x : ℍ) (b : Group) : free (b • x) ↔ free x := by
  constructor
  · intro h a c hac
    have hh := @h (a*b⁻¹) (c*b⁻¹) (by simpa only [mul_smul,inv_smul_smul] using hac)
    exact mul_right_cancel hh
  · intro h a c hac
    have hh := @h (a*b) (c*b) (by simpa only [mul_smul] using hac)
    exact mul_right_cancel hh

theorem free_ae : ∀ᵐ x : ℍ ∂volume,free x := AsymptoticRationalGroup.ae_orbit_injective

def family (T : ℍ→Space→L[ℂ]Space) (x : ℍ) : Space→L[ℂ]Space := if free x then T x else 0

theorem family_ae (T : ℍ→Space→L[ℂ]Space) : family T=ᵐ[volume]T := by
  filter_upwards [free_ae] with x hx
  exact ite_eq_left hx

theorem family_matrix (T : ℍ→Space→L[ℂ]Space) (x : ℍ) (a b : Group) :
    matrix (family T x) a b=if free x then matrix (T x) a b else 0 := by
  by_cases hx : free x <;> simp [family,hx,matrix]

theorem family_regular (T : ℍ→Space→L[ℂ]Space)
    (hm : ∀ a b,Measurable (fun x => matrix (T x) a b)) (hc : Covariant T) :
    (∀ a b,Measurable (fun x => matrix (family T x) a b)) ∧ Covariant (family T) := by
  constructor
  · intro a b
    simp only [family_matrix]
    exact Measurable.ite free_measurable (hm a b) measurable_const
  · intro x a b c
    simp only [family_matrix,free_smul_iff]
    by_cases hx : free x
    · simpa only [ite_eq_left hx] using hc x a b c
    · simp only [ite_eq_right hx]

theorem family_trace (T : ℍ→Space→L[ℂ]Space) : trace volume (family T)=trace volume T := by
  unfold trace
  apply lintegral_congr_ae
  filter_upwards [family_ae T] with x hx
  rw [hx]

theorem family_signedTrace (T : ℍ→Space→L[ℂ]Space) : signedTrace volume (family T)=signedTrace volume T := by
  unfold signedTrace
  apply integral_congr_ae
  filter_upwards [family_ae T] with x hx
  rw [hx]

theorem family_projection (T : ℍ→Space→L[ℂ]Space) (hp : ∀ x,IsStarProjection (T x)) (x : ℍ) :
    IsStarProjection (family T x) := by
  by_cases hx : free x
  · simpa only [family,ite_eq_left hx] using hp x
  · simpa only [family,ite_eq_right hx] using (IsStarProjection.zero _ : IsStarProjection (0 : Space→L[ℂ]Space))

theorem family_order (T : ℍ→Space→L[ℂ]Space) (hp : ∀ x,0≤T x ∧ T x≤1) (x : ℍ) :
    0≤family T x ∧ family T x≤1 := by
  by_cases hx : free x
  · simpa only [family,ite_eq_left hx] using hp x
  · simp only [family,ite_eq_right hx,le_refl,true_and]
    exact zero_le_one

theorem family_fix (F E : ℍ→Space→L[ℂ]Space) {δ : ℝ} (hδ : 0≤δ)
    (hfix : ∀ x,free x → ‖F x*E x-E x‖≤δ) (x : ℍ) :
    ‖family F x*family E x-family E x‖≤δ := by
  by_cases hx : free x
  · simpa only [family,ite_eq_left hx] using hfix x hx
  · simpa only [family,ite_eq_right hx,zero_mul,sub_zero,norm_zero] using hδ

#print axioms free_measurable
#print axioms free_smul_iff
#print axioms family_regular
#print axioms family_trace
#print axioms family_signedTrace
#print axioms family_projection
#print axioms family_order
#print axioms family_fix
end QuantitativeMaass.FreeRegularFamily
