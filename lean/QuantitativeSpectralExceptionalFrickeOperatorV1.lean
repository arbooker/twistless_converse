module

public import QuantitativeNewGapFrickeSignV1
public import QuantitativeSpectralObservabilityOldResidualV1
public import QuantitativeSpectralObservabilityOldTailRankV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalFricke

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticRegularTrace QuantitativeNewGap QuantitativeSpectralObservability
open AsymptoticFreshMatrices
open scoped lp ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

def countingRow (N : ℕ) (hN : 0<N) (s : ℝ) : ℓ²(Classes N,ℂ) →L[ℂ] ℓ²(Classes N,ℂ) :=
  permutationOperator (globalFrickeEquiv N hN)-(s:ℂ) • 1

theorem countingRow_apply (N : ℕ) (hN : 0<N) (s : ℝ) (f : ℓ²(Classes N,ℂ))
    (g : OrbitGroup) : countingRow N hN s f (classOf N g)=
      f (classOf N (frickeLabel N hN*g))-(s:ℂ)*f (classOf N g) := rfl

theorem countingRow_matrix (N : ℕ) (hN : 0<N) (s : ℝ) (g k : OrbitGroup) :
    matrix (countingRow N hN s) (classOf N g) (classOf N k)=
      (if classOf N (frickeLabel N hN*g)=classOf N k then 1 else 0)-
      (s:ℂ)*(if classOf N g=classOf N k then 1 else 0) := by
  classical
  rw [matrix,countingRow_apply]
  simp [delta,lp.single_apply,Pi.single_apply,eq_comm]

def weightedRow (N : ℕ) (hN : 0<N) (s : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  compression N hε ht (countingRow N hN s) x

theorem weightedRow_induction (N : ℕ) (hN : 0<N) (s : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (f : ℓ²(Classes N,ℂ)) :
    weightedRow N hN s hε ht x (induction N hε ht x f)=
      induction N hε ht x (countingRow N hN s f) := by
  have hi := congrArg (fun T : ℓ²(Classes N,ℂ) →L[ℂ] ℓ²(Classes N,ℂ) => T f)
    (induction N hε ht x).adjoint_comp_self
  change (induction N hε ht x).toContinuousLinearMap.adjoint
    (induction N hε ht x f)=f at hi
  change induction N hε ht x (countingRow N hN s
    ((induction N hε ht x).toContinuousLinearMap.adjoint (induction N hε ht x f)))=_
  rw [hi]

theorem weightedRow_range (N : ℕ) (hN : 0<N) (s : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (u : ℓ²(OrbitGroup,ℂ)) :
    weightedRow N hN s hε ht x u∈quotientSpace N hε ht x := ⟨_,rfl⟩

theorem weightedRow_coordinate (N : ℕ) (hN : 0<N) (s : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (u : ℓ²(OrbitGroup,ℂ))
    (hu : u∈quotientSpace N hε ht x) (g : OrbitGroup) :
    coordinate N ε t x g (weightedRow N hN s hε ht x u)=
      coordinate N ε t x (frickeLabel N hN*g) u-(s:ℂ)*coordinate N ε t x g u := by
  obtain ⟨f,rfl⟩ := hu
  change coordinate N ε t x g (weightedRow N hN s hε ht x (induction N hε ht x f))=
    coordinate N ε t x (frickeLabel N hN*g) (induction N hε ht x f)-
      (s:ℂ)*coordinate N ε t x g (induction N hε ht x f)
  rw [weightedRow_induction,coordinate_induction,coordinate_induction,coordinate_induction]
  exact countingRow_apply N hN s f g

theorem weightedRow_norm (N : ℕ) (hN : 0<N) (s : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖weightedRow N hN s hε ht x‖≤‖countingRow N hN s‖ := by
  let J := (induction N hε ht x).toContinuousLinearMap
  have hJ : ‖J‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro f
    change ‖induction N hε ht x f‖≤1*‖f‖
    rw [(induction N hε ht x).norm_map,one_mul]
  have ha : ‖J.adjoint‖≤1 := by simpa only [adjoint.norm_map] using hJ
  change ‖(J.comp (countingRow N hN s)).comp J.adjoint‖≤_
  calc
    _ ≤ (‖J‖*‖countingRow N hN s‖)*‖J.adjoint‖ :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1*‖countingRow N hN s‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)) ha (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem weightedRow_regular (N : ℕ) (hN : 0<N) (s : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix (weightedRow N hN s hε ht x) g k)) ∧
      Covariant (weightedRow N hN s hε ht) := by
  constructor
  · intro g k
    simp only [weightedRow,compression_matrix]
    exact (((amplitude_measurable N ε t).comp
      (AsymptoticRationalGroup.measurePreserving g).measurable).mul
      (Complex.continuous_conj.measurable.comp ((amplitude_measurable N ε t).comp
        (AsymptoticRationalGroup.measurePreserving k).measurable))).mul_const _
  · intro x a g k
    simp only [weightedRow,compression_matrix,mul_smul,countingRow_matrix]
    have he (g' k' : OrbitGroup) : classOf N (g'*a)=classOf N (k'*a) ↔
        classOf N g'=classOf N k' := by
      change AsymptoticNestedQuotients.classOf (gamma N) (g'*a)=
        AsymptoticNestedQuotients.classOf (gamma N) (k'*a) ↔
        AsymptoticNestedQuotients.classOf (gamma N) g'=
        AsymptoticNestedQuotients.classOf (gamma N) k'
      simp only [AsymptoticNestedQuotients.classOf_eq_iff,mul_inv_rev,mul_assoc,mul_inv_cancel_left]
    rw [← mul_assoc (frickeLabel N hN) g a]
    simp only [he]

#print axioms weightedRow_coordinate
#print axioms weightedRow_norm
#print axioms weightedRow_regular

end QuantitativeSpectralExceptionalFricke
