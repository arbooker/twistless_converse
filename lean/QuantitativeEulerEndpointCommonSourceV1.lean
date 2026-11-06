module

public import QuantitativeEulerEndpointCompressedSourceV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic QuantitativeEulerDensityGenerators
open QuantitativeSpectralObservability AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- All good primes q<=X use ONE geometric region and ONE compressed
baseline source. The adjustable transport constant absorbs (X/q)^4;
no comparison between different compressed spectral spaces is used. -/
theorem common_baseline_source_observability {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ ∃ M : ℝ, 0≤M ∧
      ∀ C : ℝ, B≤C → ∀ X : ℝ, ∀ (q : ℕ) [Fact q.Prime], P.Good q → (q : ℝ)≤X →
      ∃ hqN : ¬q∣N, ∀ H : ℝ, max ε⁻¹ 4≤H → ∀ w : ℂ, w*w=1 →
      ∀ (t : ℕ) (ht : 1≤t) (x : ℍ), fundamentalGood N x →
      let L := (2*generatorTransportConstant P*C)*X^4
      let R := K*((integerCompactDistortion L H)^t)^2
      let hs := freshObservationRegion_compact L H hε
      ∀ v : Space, v∈baselineSurvivor N H w hs hε t x (2*(1+R))⁻¹ →
      ‖v‖^2≤2*M*‖fundamentalSampling N (NeZero.pos N) H hε ht x v‖^2+
        2*R*‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w hs hε t i x) v‖^2 := by
  obtain ⟨B,hB,K,hK,M,hM,hbound⟩ := compressed_baseline_source_observability P hε
  refine ⟨B,hB,K,hK,M,hM,?_⟩
  intro C hBC X q hqPrime hqGood hqX
  have hqp : 0<(q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hr : 1≤X/(q : ℝ) := (le_div_iff₀ hqp).2 (by simpa using hqX)
  have hp : 1≤(X/(q : ℝ))^4 := one_le_pow₀ hr
  let Cq := C*(X/(q : ℝ))^4
  have hCq : B≤Cq := hBC.trans (by
    simpa only [mul_one,Cq] using mul_le_mul_of_nonneg_left hp
      (le_trans zero_le_one (hB.trans hBC)))
  obtain ⟨hqN,hqbound⟩ := hbound Cq hCq q hqGood
  refine ⟨hqN,?_⟩
  intro H hH w hw t ht x hx
  have he : (2*generatorTransportConstant P*Cq)*(q : ℝ)^4=
      (2*generatorTransportConstant P*C)*X^4 := by
    dsimp only [Cq]
    rw [div_pow]
    field_simp [ne_of_gt hqp]
  simpa only [he] using hqbound H hH w hw t ht x hx

#print axioms common_baseline_source_observability
end QuantitativeEulerEndpointPrepared
