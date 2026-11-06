module

public import QuantitativeSpectralExceptionalFrickeOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalFricke

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticRegularTrace
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open AsymptoticFreshMatrices
open scoped MatrixGroups lp ENNReal

attribute [local instance] Classical.propDecidable

def branches (N : ℕ) (hN : 0<N) : Bool → Branch
  | true => projectiveBranch (frickeLabel N hN)
  | false => projectiveBranch 1

def coefficients (s : ℝ) : Bool → ℂ
  | true => 1
  | false => -(s:ℂ)

theorem weightedRow_coordinate_sum (N : ℕ) (hN : 0<N) (s : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (u : ℓ²(OrbitGroup,ℂ))
    (hu : u∈quotientSpace N hε ht x) (g : OrbitGroup) :
    coordinate N ε t x g (weightedRow N hN s hε ht x u)=
      ∑ i, coefficients s i*coordinate N ε t x (label (branches N hN i)*g) u := by
  rw [weightedRow_coordinate N hN s hε ht x u hu g]
  simp only [Fintype.sum_bool,branches,coefficients,projectiveBranch_label,one_mul]
  ring

/-- The literal signed global Fricke row of the actual normalized quotient
sample is a polynomially bounded recombination of its compact rational
row and fixed Gamma0 defects, plus the actual quotient tail. -/
theorem exists_weightedRow_residual (N : ℕ) (hN : 0<N) (sign : ℝ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    ∃ C B L K : ℝ, ∃ n : ℕ, ∃ w : Fin n → Bool → List SL(2,ℤ),
      ∃ _hw : ∀ j i a, a∈w j i → a∈signedGenerators S,
      0<C ∧ 0<B ∧ 1≤L ∧ 1≤K ∧
      ∀ H : ℝ, B≤H → ∀ (ε : ℝ) (hε : 0<ε) (t : ℕ) (ht : 1≤t) (x : ℍ),
        let hs := wideCompactCover_compact N hN (H/C)
        let D := commonResidualStack (signedGenerators S) (branches N hN) w (coefficients sign) hs hε t x
        ∃ R : GeneratorData (signedGenerators S) →L[ℂ] ℓ²(OrbitGroup,ℂ),
          ‖R‖≤L*(1+ε*K*(H/C+3)^2)^(2*t) ∧
          ∀ v : ℓ²(OrbitGroup,ℂ),
            weightedRow N hN sign hε ht x (fundamentalSampling N hN H hε ht x v)=R (D v)+
              fundamentalSubsetProjection N hε ht (fundamentalTail N (H/C)) x
                (weightedRow N hN sign hε ht x (fundamentalSampling N hN H hε ht x v)) := by
  obtain ⟨C,B,L,K,n,w,hw,E,hC,hB,hL,hK,_hΓ,_hE,_hd,hall⟩ :=
    exists_quantitative_actual_quotient_residual N hN S hS (branches N hN) (coefficients sign)
  refine ⟨C,B,L,K,n,w,hw,hC,hB,hL,hK,?_⟩
  intro H hH ε hε t ht x
  obtain ⟨_hcover,_hsub,_hred,hrow⟩ := hall H hH
  obtain ⟨hbound,_hfac,hcoord⟩ := hrow ε hε t x
  let hs := wideCompactCover_compact N hN (H/C)
  let A := selectedGeneratorRecombine (signedGenerators S) (branches N hN) w hw (coefficients sign)
    (E H) hs hε t (QuantitativeSpectralExceptionalUnweight.data hs hε t)
    (fun i => QuantitativeSpectralExceptionalUnweight.data (image_compact (branches N hN i) hs) hε t) x
  refine ⟨retainedRecombiner N hε ht (H/C) x A,
    (retainedRecombiner_norm N hε ht (H/C) x A).trans hbound,?_⟩
  intro v
  by_cases hx : fundamentalGood N x
  · apply quotient_row_decompose N hε ht (H/C) x hx
    · exact weightedRow_range N hN sign hε ht x _
    · intro g hg
      have ho := weightedRow_coordinate_sum N hN sign hε ht x
        (fundamentalSampling N hN H hε ht x v) (fundamentalSampling_range N hN H hε ht x v) g
      have hc := hcoord ht hx v g
      simp only [ite_eq_left hg] at hc
      exact ho.trans hc.symm
  · simp only [fundamentalSampling,retainedRecombiner,fundamentalTransfer,
      dite_eq_right hx,zero_comp,zero_apply,map_zero,add_zero]

def sampledRow (N : ℕ) (hN : 0<N) (s Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) : ℓ²(OrbitGroup,ℂ) →L[ℂ] ℓ²(OrbitGroup,ℂ) :=
  (weightedRow N hN s hε ht x).comp (fundamentalSampling N hN Y hε ht x)

theorem sampledRow_regular (N : ℕ) (hN : 0<N) (s Y : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (∀ g k, Measurable (fun x => matrix (sampledRow N hN s Y hε ht x) g k)) ∧
      Covariant (sampledRow N hN s Y hε ht) := by
  have hr := weightedRow_regular N hN s hε ht
  have hs := fundamentalSampling_regular N hN Y hε ht
  exact ⟨matrix_comp_measurable _ _ hr.1 hs.1,covariant_comp _ _ hr.2 hs.2⟩

theorem sampledRow_norm (N : ℕ) (hN : 0<N) (s Y : ℝ) (hY : 0≤Y)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) :
    ‖sampledRow N hN s Y hε ht x‖≤‖countingRow N hN s‖*
      (QuantitativeSpectralObservabilitySampling.samplingBound N hN Y ε t*
        (8*QuantitativeSpectralCoverUnweight.coverBound N hN*(Y+3)+5)) := by
  apply (opNorm_comp_le _ _).trans
  exact mul_le_mul (weightedRow_norm N hN s hε ht x)
    (fundamentalSampling_norm N hN Y hY hε ht x) (norm_nonneg _) (norm_nonneg _)

/-- The discarded signed Fricke row has actual input support rank O(1/H),
not merely output rank; all regularity requirements are discharged. -/
theorem sampledTail_source_rank (N : ℕ) (hN : 0<N) (s : ℝ) {Y : ℝ} (hY : 0≤Y)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) {H : ℝ} (hH : 0<H) :
    trace volume (fun x => ((fundamentalSubsetProjection N hε ht (fundamentalTail N H) x).comp
      (sampledRow N hN s Y hε ht x)).kerᗮ.starProjection)≤
      (CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal H⁻¹) := by
  have hr := sampledRow_regular N hN s Y hε ht
  exact fundamentalTail_source_rank N hN hε ht hH _ hr.1 hr.2 _
    (sampledRow_norm N hN s Y hY hε ht)

#print axioms exists_weightedRow_residual
#print axioms sampledRow_regular
#print axioms sampledTail_source_rank

end QuantitativeSpectralExceptionalFricke
