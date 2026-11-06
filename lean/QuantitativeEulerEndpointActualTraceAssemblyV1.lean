module

public import QuantitativeEulerEndpointActualTerminalExpressionCostV1
public import QuantitativeEulerEndpointBoundedPrimeCostV1
public import QuantitativeEulerEndpointActualSectorTraceV1
public import QuantitativeEulerEndpointActualTerminalTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open AsymptoticSectorSigns FinitenessCertificate FinitenessGlobalHeight QuantitativeHolomorphic
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial AsymptoticFiniteBranch
open scoped Classical MatrixGroups

/-- One literal finite filter with a common fixed accuracy: regular approximation,
physical positive contraction, full actual sector preservation, and explicit
complexity. All original physical equations are discharged. -/
theorem exists_actual_trace_filter {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A) (hN2 : 2≤N)
    (sector : Sector N) (threshold : ℕ) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let excluded := reconstructionExclusions N Q
    let G := generatorTransportConstant (QuantitativeEulerEndpointPrepared.prepared N hN2 excluded threshold)
    let P' := AsymptoticReconstructedCount.parameters A P
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ),1≤Bobs ∧
      ∃ Bg : ℝ,1≤Bg ∧ ∃ D : ℝ,1≤D ∧ ∃ C : ℝ,1≤C ∧ ∃ Kobs : ℝ,0≤Kobs ∧
      ∀ H₀ : ℝ,max P'.ε⁻¹ 4≤H₀ →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H₀) →
      ∃ Ka Kc : ℝ,0≤Ka ∧ 0≤Kc ∧ ∀ n : ℕ,
      let H := H₀*(4:ℝ)^n
      let b := actualBlock A P hN2 excluded threshold sector S hS W Bobs Bg D H₀ G C Kobs n
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P'.epsilon_pos (by omega : 1≤P'.s+4)+H⁻¹
      ∃ (F : ℕ → Algebra A P) (z : ℕ → ℝ[X]),F 0=1 ∧
        (∀ j,j≤n → Valid A P sector n b j (F j)) ∧
        (∀ j,j<n → Step A P sector n b target j (F j) (z j) ∧
          F (j+1)=nextAt A P sector n b j (F j) (z j)) ∧
        (∀ E : Algebra A P,
          (∀ j,j<n → ∀ i : Fin ((b j).primes.length+1),∀ x,
            normalizedCombinedRows A P sector (b j).compact (b j).primes i x*rep A P E x=0) →
          ∀ j,j≤n → F j*E=E) ∧
        tr A P (F n)≤target+Real.exp ((8:ℝ)/3+8)*
          (P'.ε⁻¹+4*(1+P'.ε⁻¹*Real.log 2))/(4:ℝ)^n ∧
        let T := actualFiniteExpression A P sector hN2 excluded threshold S hS W Bobs Bg D H₀ G C Kobs
          n (Real.exp ((Ka+1)*(4:ℝ)^n)) z
        expressionBound T≤Real.exp (Real.exp (Kc*(4:ℝ)^n)) ∧
        ExpressionMatrixBound T (Real.exp (Real.exp (Kc*(4:ℝ)^n))) ∧
        (∀ x,‖rep A P (F n) x-regularSum T x‖≤2/(4:ℝ)^n) ∧
        (‖tr A P (F n)-AsymptoticRegularTrace.signedTrace MeasureTheory.volume (regularSum T)‖≤
          (2/(4:ℝ)^n)*P'.ε⁻¹) ∧
        ∀ h : ℕ,
          let U := holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) (h+1)
          let V := holomorphicSum T (h+1)
          let E := QuantitativeEulerEndpointSector.normalizedPhysicalSectorProjection A P (NeZero.pos N) h sector
          (0≤V ∧ V≤1 ∧ V≤U ∧ U*V=V ∧ V*U=V) ∧ ‖V*E-E‖≤2/(4:ℝ)^n ∧
          let X := AsymptoticCylinder.holomorphicSpace (2*h) (P'.s+4)
            (by positivity : 0<4*Real.pi) P'.epsilon_pos
          let fb := AsymptoticCylinder.fourierBasis (2*h) (P'.s+4)
            (by positivity : 0<4*Real.pi) P'.epsilon_pos
          (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) sector):ℝ)≤
            AsymptoticDiagonalTrace.trace fb (AsymptoticObservation.compressedSandwich
              (normalizedCountReconstruction A (NeZero.pos N) P h sector)
              (QuantitativeEulerEndpointApproximateTrace.terminalCompression A P V) X) := by
  intro excluded G P'
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,hfilters⟩ :=
    exists_actual_common_filter A P hN2 sector threshold S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,?_⟩
  intro H₀ hH₀ hdata
  obtain ⟨Ka,Kc,hKa,hKc,hall⟩ := hfilters H₀ hH₀ hdata
  refine ⟨Ka,Kc,hKa,hKc,?_⟩
  intro n H b target
  obtain ⟨F,z,hi,hvalid,hrec,hfix,htrace,hcost,hmatrix,happrox,hphysical⟩ := hall n
  refine ⟨F,z,hi,hvalid,hrec,hfix,htrace,hcost,hmatrix,happrox,?_,?_⟩
  · apply QuantitativeEulerEndpointTerminalExpression.trace_error A P (F n) _ _ _ happrox
    exact QuantitativeEulerEndpointTerminalExpression.iterate_regular_right_support A P _ _ z n
  · intro h
    have hp := hphysical h
    refine ⟨hp.1,hp.2,?_⟩
    exact QuantitativeEulerEndpointApproximateTrace.ambient_sector_finrank_mul_le_trace
      A P (NeZero.pos N) h sector _ hp.1.1 _ hp.2

#print axioms exists_actual_trace_filter
end QuantitativeEulerEndpointBoundedIteration
