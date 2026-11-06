module

public import QuantitativeEulerEndpointFixedMultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane CongruenceSubgroup QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack
open scoped Classical MatrixGroups

/-- A finite family of literal Gamma1 defects and fixed ring multipliers
admits one height and one squared-norm constant, chosen before the fresh
prime, uniformly over every member on the same observation region. -/
theorem gamma1_finite_multiplier_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    {ι : Type*} [Fintype ι] (γ : ι → SL(2,ℤ)) (hγ : ∀ i, γ i∈Gamma1 N) (E : ι → Ring) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (i : ι) (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖compactAction hs hε t x ((symbol (integralLabel (γ i))-1)*E i) v‖^2≤
      K*((integerCompactDistortion L H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t j x) v‖^2) := by
  choose B hB K hK hb using fun i => gamma1_fixed_multiplier_stack_bound P (γ i) (hγ i) (E i)
  let B₀ := 1+∑ i, B i
  let K₀ := ∑ i, K i
  have hBn (i : ι) : 0≤B i := zero_le_one.trans (hB i)
  have hB₀ : 1≤B₀ := by
    dsimp only [B₀]
    linarith [Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset ι)) => hBn i)]
  have hBB (i : ι) : B i≤B₀ := by
    have hi := Finset.single_le_sum (fun j _ => hBn j) (Finset.mem_univ i)
    dsimp only [B₀]
    linarith
  have hKK (i : ι) : K i≤K₀ :=
    Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)
  refine ⟨B₀,hB₀,K₀,Finset.sum_nonneg (fun i _ => hK i),?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro i w hw s hs ε Y H hε hY hre hlo him t x v
  obtain ⟨_hqN,hi⟩ := hb i C ((hBB i).trans hBC) q hqGood
  exact (hi w hw hs hε hY hre hlo him t x v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hKK i) (sq_nonneg _))
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))

#print axioms gamma1_finite_multiplier_stack_bound
end QuantitativeEulerEndpointPrepared
