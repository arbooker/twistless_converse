module

public import QuantitativeEulerEndpointActualTerminalExpressionCostV1
public import QuantitativeEulerEndpointBoundedPrimeCostV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open AsymptoticSectorSigns FinitenessCertificate FinitenessGlobalHeight QuantitativeHolomorphic
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial AsymptoticFiniteBranch
open scoped Classical MatrixGroups

/-- Actual full-terminal regular filters and their literal finite branch
approximants, with paid error and complexity, retaining the trace estimate
and common-kernel preservation of the original normalized iteration. -/
theorem exists_actual_finite_filter {N Q : ℕ} [NeZero N] {hQ : 0<Q}
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
        ∀ x,‖rep A P (F n) x-regularSum T x‖≤2/(4:ℝ)^n := by
  intro excluded G P'
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,hiteration⟩ :=
    exists_bounded_prime_block_cost A P hN2 sector threshold S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,?_⟩
  intro H₀ hH₀ hdata
  have hH₀0 : 0≤H₀ := by have h4 := (le_max_right P'.ε⁻¹ 4).trans hH₀; linarith
  have hG : 0≤G := (generatorTransportConstant_pos _).le
  obtain ⟨Ka,hKa,happrox⟩ := exists_actual_finite_approximation A P sector hN2 excluded threshold S hS W
    Bobs Bg D H₀ G C Kobs (by linarith) (by linarith) hH₀0 hG (by linarith) hKobs
  obtain ⟨Kc,hKc,hcost⟩ := exists_actual_terminal_expression_cost A P sector hN2 excluded threshold S hS W
    Bobs Bg D H₀ G C Kobs (by linarith) (by linarith) hH₀0 hG (by linarith) hKobs hKa
  obtain ⟨_,_,hfilters⟩ := hiteration H₀ hH₀ hdata
  refine ⟨Ka,Kc,hKa,hKc,?_⟩
  intro n H b target
  obtain ⟨F,z,hi,hvalid,hrec,hfix,htrace,_⟩ := hfilters n
  have hd (j : ℕ) (hj : j<n) : (z j).natDegree≤16*(sharpnessAt A P sector n b (j+1))^5+1 :=
    (hrec j hj).1.degree
  have hm (j : ℕ) (hj : j<n) : (∑ i∈(z j).support,|(z j).coeff i|)≤
      (((16*(sharpnessAt A P sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P sector n b (j+1))^5) :=
    (hrec j hj).1.mass
  have hc := hcost n z hd hm
  refine ⟨F,z,hi,hvalid,hrec,hfix,htrace,hc.1,hc.2,?_⟩
  exact happrox n F z hi (fun j hj => ⟨(hvalid j hj.le).nonneg,(hvalid j hj.le).le_one⟩)
    (fun j hj => (hrec j hj).2) (fun j hj => (hrec j hj).1.scalar) hd hm

#print axioms exists_actual_finite_filter
end QuantitativeEulerEndpointBoundedIteration
