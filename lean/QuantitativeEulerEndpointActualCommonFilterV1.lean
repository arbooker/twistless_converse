module

public import QuantitativeEulerEndpointActualTerminalExpressionCostV1
public import QuantitativeEulerEndpointBoundedPrimeCostV1
public import QuantitativeEulerEndpointActualSectorPreservationV1

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
theorem exists_actual_common_filter {N Q : ℕ} [NeZero N] {hQ : 0<Q}
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
        ∀ h : ℕ,
          let U := holomorphicSum (QuantitativeEulerEndpointTerminalExpression.unit A P) (h+1)
          let V := holomorphicSum T (h+1)
          let E := QuantitativeEulerEndpointSector.normalizedPhysicalSectorProjection A P (NeZero.pos N) h sector
          (0≤V ∧ V≤1 ∧ V≤U ∧ U*V=V ∧ V*U=V) ∧ ‖V*E-E‖≤2/(4:ℝ)^n := by
  intro excluded G P'
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,hiteration⟩ :=
    exists_bounded_prime_block_cost A P hN2 sector threshold S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,?_⟩
  intro H₀ hH₀ hdata
  have hH₀0 : 0≤H₀ := by have h4 := (le_max_right P'.ε⁻¹ 4).trans hH₀; linarith
  have hG : 0≤G := (generatorTransportConstant_pos _).le
  obtain ⟨Ka,hKa,hbudget⟩ := exists_actual_comparison_bound A P hN2 excluded threshold sector S hS W
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
  have hq := fun j hj => (hrec j hj).1.scalar
  refine ⟨F,z,hi,hvalid,hrec,hfix,htrace,hc.1,hc.2,?_,?_⟩
  · intro x
    have he := actualFiniteExpression_error A P sector hN2 excluded threshold S hS W Bobs Bg D H₀ G C Kobs
      n (Real.exp ((Ka+1)*(4:ℝ)^n)) F z hi
      (fun j hj => ⟨(hvalid j hj.le).nonneg,(hvalid j hj.le).le_one⟩)
      (fun j hj => (hrec j hj).2) hq x
    have hp := QuantitativeEulerEndpointCommonReconstruction.amplified_error_le hKa
      (one_le_pow₀ (by norm_num : (1:ℝ)≤4) (n:=n)) (hbudget n z hd hm)
    apply he.trans
    rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
    nlinarith only [hp]
  · intro h
    exact ⟨actualFiniteExpression_physical_order A P sector hN2 excluded threshold S hS W Bobs Bg D H₀ G C Kobs
        n h (Real.exp ((Ka+1)*(4:ℝ)^n)) z hq,
      actualFiniteExpression_sector_paid A P sector hN2 excluded threshold S hS W Bobs Bg D H₀ G C Kobs
        n h hKa z hq (hbudget n z hd hm)⟩

#print axioms exists_actual_common_filter
end QuantitativeEulerEndpointBoundedIteration
