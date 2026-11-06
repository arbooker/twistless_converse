module

public import QuantitativeEulerEndpointBoundedActualResidualV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open AsymptoticSectorSigns FinitenessCertificate FinitenessGlobalHeight QuantitativeHolomorphic
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial
open QuantitativeEulerEndpointNestedExpression QuantitativeEulerEndpointExponentialParameters
open scoped Classical MatrixGroups

/-- Actual full-terminal filters, their regular trace estimate, and uniform
polynomial degree/depth and coefficient budgets. The exact normalized
reconstruction still requires finite-branch approximation before this can
become a finite-weight count estimate. -/
theorem exists_bounded_prime_block_cost {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : Certificate N Q hQ) (P : Parameters A)
    (hN2 : 2≤N) (sector : Sector N) (threshold₀ : ℕ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let excluded := reconstructionExclusions N Q
    let G := generatorTransportConstant (QuantitativeEulerEndpointPrepared.prepared N hN2 excluded threshold₀)
    let P' := AsymptoticReconstructedCount.parameters A P
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ),1≤Bobs ∧
      ∃ Bg : ℝ,1≤Bg ∧ ∃ D : ℝ,1≤D ∧ ∃ C : ℝ,1≤C ∧ ∃ Kobs : ℝ,0≤Kobs ∧
      ∀ H₀ : ℝ,max P'.ε⁻¹ 4≤H₀ →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H₀) →
      ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      let H := H₀*(4:ℝ)^n
      let b := actualBlock A P hN2 excluded threshold₀ sector S hS W Bobs Bg D H₀ G C Kobs n
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
        (∑ j∈Finset.range n,logarithmicCost (fun i => power (effortAt A P sector n b i)) z j)≤K*(4:ℝ)^n ∧
        (budget (fun i => power (effortAt A P sector n b i)) z n:ℝ)≤Real.exp (K*(4:ℝ)^n) ∧
        (∀ j,j<n → (∑ i∈(z j).support,|(z j).coeff i|)≤Real.exp (Real.exp (K*(4:ℝ)^n))) ∧
        QuantitativeEulerEndpointResidual.errorBudget
          (fun i => power (effortAt A P sector n b i)) z n≤Real.exp (Real.exp (K*(4:ℝ)^n)) := by
  intro excluded G P'
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,hiteration⟩ :=
    exists_bounded_prime_block_iteration A P hN2 sector threshold₀ S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C,hC,Kobs,hKobs,?_⟩
  intro H₀ hH₀ hdata
  have hH₀0 : 0≤H₀ := by have h4 := (le_max_right P'.ε⁻¹ 4).trans hH₀; linarith
  have hG : 0≤G := (generatorTransportConstant_pos _).le
  obtain ⟨Kl,hKl,hlog⟩ := exists_actual_logarithmic_cost A P hN2 excluded threshold₀ sector S hS W
    Bobs Bg D H₀ G C Kobs (by linarith) (by linarith) hH₀0 hG (by linarith) hKobs
  obtain ⟨Kc,hKc,hcoef⟩ := exists_actual_coefficient_bound A P hN2 excluded threshold₀ sector S hS W
    Bobs Bg D H₀ G C Kobs (by linarith) (by linarith) hH₀0 hG (by linarith) hKobs
  obtain ⟨Kr,hKr,hres⟩ := exists_actual_residual_bound A P hN2 excluded threshold₀ sector S hS W
    Bobs Bg D H₀ G C Kobs (by linarith) (by linarith) hH₀0 hG (by linarith) hKobs
  refine ⟨Kl+Kc+Kr,by positivity,?_⟩
  intro n H b target
  have hHH : H₀≤H := by
    have hp : (1:ℝ)≤4^n := one_le_pow₀ (by norm_num)
    dsimp only [H]
    nlinarith
  obtain ⟨F,z,hF,hvalid,hrec,hfix,htrace⟩ :=
    hiteration n (fun _ => C) (fun _ _ => le_rfl) H (hH₀.trans hHH) (fun i => (hdata i).trans hHH)
  have hdeg (j : ℕ) (hj : j<n) : (z j).natDegree≤16*(sharpnessAt A P sector n b (j+1))^5+1 :=
    (hrec j hj).1.degree
  have hmass (j : ℕ) (hj : j<n) : (∑ i∈(z j).support,|(z j).coeff i|)≤
      (((16*(sharpnessAt A P sector n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P sector n b (j+1))^5) :=
    (hrec j hj).1.mass
  have hl := hlog n z hdeg
  have hc := hcoef n z hmass
  have hr := hres n z hdeg hmass
  have hle : Kl*(4:ℝ)^n≤(Kl+Kc+Kr)*(4:ℝ)^n := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤4) n]
  have hce : Kc*(4:ℝ)^n≤(Kl+Kc+Kr)*(4:ℝ)^n := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤4) n]
  have hre : Kr*(4:ℝ)^n≤(Kl+Kc+Kr)*(4:ℝ)^n := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤4) n]
  exact ⟨F,z,hF,hvalid,hrec,hfix,htrace,hl.1.trans hle,
    hl.2.trans (Real.exp_le_exp.mpr hle),
    (fun j hj => (hc j hj).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hce))),
    hr.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hre))⟩

#print axioms exists_bounded_prime_block_cost
end QuantitativeEulerEndpointBoundedIteration
