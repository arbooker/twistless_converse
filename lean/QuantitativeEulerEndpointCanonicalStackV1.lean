module

public import QuantitativeEulerEndpointFreshTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode QuantitativeEulerDiamondPolynomial
open QuantitativeArithmeticDiamondLabels AsymptoticCongruenceLabels
open AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- The actual canonical matrix at a fixed prime, followed by any fixed
projective label, is controlled by the original q=1 and fixed-prime average
and the actual fresh-prime stack. Every term uses one common region; only
the original source is assumed to lie in the unit strip. -/
theorem fixed_canonical_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ℓ∣N) (j : Fin (ℓ-1)) (g : G) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖compactAction hs hε t x
        ((symbol (integralLabel (swappedCanonical N ℓ hℓ j))-1)*symbol g) v‖^2≤
      K*((integerCompactDistortion L H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖twist N ℓ (NeZero.pos N) (Fact.out : ℓ.Prime).pos w
            (freshObservationRegion_compact L H hY) hε t x v‖^2+
          ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (freshObservationRegion_compact L H hY) hε t i x) v‖^2) := by
  let E := symbol ((defectLabel N ℓ (NeZero.pos N) hℓ j)⁻¹*g)
  let F := Polynomial.aeval (primeX ℓ) (correctionPolynomial ℓ)
  obtain ⟨B₁,hB₁,K₁,hK₁,h₁⟩ := fixed_ring_fresh_bound E
  obtain ⟨B₂,_hB₂,K₂,hK₂,h₂⟩ := fixed_ring_fresh_bound (primeInverse ℓ*E)
  obtain ⟨B₃,_hB₃,K₃,hK₃,h₃⟩ := fixed_prime_corrections_stack_bound P ℓ hℓ
    (primeInverse ℓ*E) (F*E)
  let B := max B₁ (max B₂ B₃)
  let K := 3*(K₁^2+K₂^2+K₃)
  have hb₁ : B₁≤B := le_max_left _ _
  have hb₂ : B₂≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hb₃ : B₃≤B := (le_max_right _ _).trans (le_max_right _ _)
  have hB : 1≤B := hB₁.trans hb₁
  refine ⟨B,hB,K,mul_nonneg (by norm_num) (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hK₃),?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := h₃ C (hb₃.trans hBC) q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  have hCL : C≤L := fresh_transport_height_dominates P C (zero_le_one.trans (hB.trans hBC)) q
    (Fact.out : q.Prime).one_le
  let D := (integerCompactDistortion L H)^t
  have hD : 0≤D := by dsimp only [D]; unfold integerCompactDistortion; positivity
  let a := ‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w
    (freshObservationRegion_compact L H hY) hε t x v‖
  let b := ‖twist N ℓ (NeZero.pos N) (Fact.out : ℓ.Prime).pos w
    (freshObservationRegion_compact L H hY) hε t x v‖
  let c := ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
    (freshObservationRegion_compact L H hY) hε t i x) v‖
  let S := D^2*(a^2+b^2+c^2)
  let u := compactAction hs hε t x (frickeRow N (NeZero.pos N) w*E) v
  let z := compactAction hs hε t x (primeAverage N ℓ (NeZero.pos N) hℓ w*(primeInverse ℓ*E)) v
  let r := compactAction hs hε t x
    (primeCongruenceCorrection N ℓ (NeZero.pos N) hℓ w j*(primeInverse ℓ*E)+
      primePeriodCorrection N ℓ (NeZero.pos N) hℓ w j*(F*E)) v
  have hu : ‖u‖≤K₁*D*a := by
    have hh := h₁ L ((hb₁.trans hBC).trans hCL) (frickeRow N (NeZero.pos N) w)
      hs hε hY hre hlo him t x v
    rw [frickeRow,compactAction_untwisted] at hh
    exact hh
  have hz : ‖z‖≤K₂*D*b := by
    have hh := h₂ L ((hb₂.trans hBC).trans hCL) (primeAverage N ℓ (NeZero.pos N) hℓ w)
      hs hε hY hre hlo him t x v
    rw [compactAction_primeAverage,_root_.neg_apply,norm_neg] at hh
    exact hh
  have hr : ‖r‖^2≤K₃*D^2*(a^2+c^2) := hqbound j w hw hs hε hY hre hlo him t x v
  have hua : ‖u‖^2≤K₁^2*S := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hK₁ hD) (norm_nonneg _))).2 hu
    calc
      _ ≤ (K₁*D*a)^2 := hh
      _ = K₁^2*(D^2*a^2) := by ring
      _ ≤ K₁^2*S := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg b,sq_nonneg c])
          (sq_nonneg D)) (sq_nonneg K₁)
  have hzb : ‖z‖^2≤K₂^2*S := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hK₂ hD) (norm_nonneg _))).2 hz
    calc
      _ ≤ (K₂*D*b)^2 := hh
      _ = K₂^2*(D^2*b^2) := by ring
      _ ≤ K₂^2*S := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg a,sq_nonneg c])
          (sq_nonneg D)) (sq_nonneg K₂)
  have hrc : ‖r‖^2≤K₃*S := by
    apply hr.trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (by nlinarith only [sq_nonneg b] : a^2+c^2≤a^2+b^2+c^2) (sq_nonneg D)) hK₃
  have ht := (three_vector_squared u z r).trans
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hua hzb) hrc) (by norm_num : (0 : ℝ)≤3))
  have hwNorm : ‖w‖^2=1 := by simpa only [norm_mul,norm_one,pow_two] using congrArg norm hw
  have he := congrArg (fun T : Space →L[ℂ] Space => ‖T v‖^2)
    (compact_canonical_recovery_right N ℓ (NeZero.pos N) hℓ w hw j g hs hε t x)
  simp only [_root_.smul_apply,norm_smul,mul_pow,norm_neg,hwNorm,one_mul,
    _root_.sub_apply,_root_.add_apply] at he
  have hscalar : 3*(K₁^2*S+K₂^2*S+K₃*S)=K*D^2*(a^2+b^2+c^2) := by
    dsimp only [K,S]
    ring
  exact he.trans_le (ht.trans_eq hscalar)

#print axioms fixed_canonical_stack_bound
end QuantitativeEulerEndpointPrepared
