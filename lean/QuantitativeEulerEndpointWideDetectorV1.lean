module

public import QuantitativeEulerEndpointWideGamma0WordsV1
public import QuantitativeSpectralExceptionalStackDetectorV1


set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- The actual full finite Gamma0 generator detector is bounded by the
original untwisted row, the original fixed-prime averaged-row stack, and
the actual shifted fresh-prime stack, on ONE shared observation region.
Every row is a literal Gamma0(N) element; no generating hypothesis is needed. -/
theorem wide_gamma0_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (A : Finset SL(2,ℤ)) (hA : ∀ γ∈A, γ∈CongruenceSubgroup.Gamma0 N) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε W₀ Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤W₀) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖stack (fun γ : ↥A =>
        AsymptoticCongruenceDefect.operator γ.val hs hε t x) v‖^2≤
      K*((wideDistortion L W₀ H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
          ‖fixedPrimeStack N w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
          ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (wideFreshRegion_compact L W₀ H hY) hε t i x) v‖^2) := by
  obtain ⟨B,hB,K,hK,hbound⟩ := wide_gamma0_finite_original_control P (fun γ : ↥A => γ.val)
    (fun γ => hA γ.val γ.property) (fun _ => 1)
  let n := Fintype.card ↥A
  refine ⟨B,hB,(n : ℝ)*K,mul_nonneg (Nat.cast_nonneg _) hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε W₀ Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let Q := K*((wideDistortion L W₀ H)^t)^2*
    (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
      ‖fixedPrimeStack N w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
      ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
        (wideFreshRegion_compact L W₀ H hY) hε t i x) v‖^2)
  have hterm (γ : ↥A) :
      ‖AsymptoticCongruenceDefect.operator γ.val hs hε t x v‖^2≤Q := by
    obtain ⟨_hqN,hγ⟩ := hbound γ C hBC q hqGood
    have hh := hγ w hw hs hε hY hre hlo him t x v
    simpa only [map_one,mul_one,compactAction_congruence] using hh
  rw [PiLp.norm_sq_eq_of_L2]
  have hsum := Finset.sum_le_sum (fun γ (_ : γ∈(Finset.univ : Finset ↥A)) => hterm γ)
  exact hsum.trans_eq (by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    dsimp only [Q,n]
    ring)

#print axioms wide_gamma0_stack_bound

/-- Exact splitting of the enlarged detector energy into its original
rational rows and its actual congruence rows. -/
theorem enlarged_detector_energy {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]
    (A : Finset SL(2,ℤ)) (b : ∀ j, I j → AsymptoticRegularBranchFamily.Branch)
    (c : ∀ j, I j → ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖QuantitativeSpectralExceptionalReducedRows.enlargedDetector A b c hs hε t x v‖^2 =
      (∑ j, ‖AsymptoticRegularBranchFamily.family (b j) (c j) hs hε t x v‖^2)+
      ‖stack (fun a : ↥A => AsymptoticCongruenceDefect.operator a.val hs hε t x) v‖^2 := by
  rw [QuantitativeSpectralExceptionalReducedRows.enlargedDetector_norm_apply]
  simp only [PiLp.norm_sq_eq_of_L2,Fintype.sum_sum_type]
  rfl

/-- The generator part of the ACTUAL enlarged detector is controlled by
original untwisted/fixed-prime rows and the shifted fresh-prime stack.
Original rational rows are retained explicitly, including oldform rows. -/
theorem wide_enlarged_detector_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (A : Finset SL(2,ℤ)) (hA : ∀ γ∈A, γ∈CongruenceSubgroup.Gamma0 N) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ {J : Type} [Fintype J] {I : J → Type} [∀ j, Fintype (I j)]
        (b : ∀ j, I j → AsymptoticRegularBranchFamily.Branch) (c : ∀ j, I j → ℂ)
        (w : ℂ) (_hw : w*w=1) {s : Set ℍ} (hs : IsCompact s)
        {ε W₀ Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤W₀) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖QuantitativeSpectralExceptionalReducedRows.enlargedDetector A b c hs hε t x v‖^2≤
      (∑ j, ‖AsymptoticRegularBranchFamily.family (b j) (c j) hs hε t x v‖^2)+
      K*((wideDistortion L W₀ H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
          ‖fixedPrimeStack N w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
          ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (wideFreshRegion_compact L W₀ H hY) hε t i x) v‖^2) := by
  obtain ⟨B,hB,K,hK,hbound⟩ := wide_gamma0_stack_bound P A hA
  refine ⟨B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := hbound C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro J _ I _ b c w hw s hs ε W₀ Y H hε hY hre hlo him t x v
  dsimp only
  rw [enlarged_detector_energy]
  exact add_le_add le_rfl (hqbound w hw hs hε hY hre hlo him t x v)

#print axioms enlarged_detector_energy
#print axioms wide_enlarged_detector_bound

end QuantitativeEulerEndpointPrepared
