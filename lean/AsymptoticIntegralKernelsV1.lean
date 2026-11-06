module

public import AsymptoticIntegralCertificateV1
public import AsymptoticRegularInfiniteKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticIntegralSubgroup

open AsymptoticSubgroupSupport AsymptoticRegularObservation AsymptoticRegularReconstruction
open AsymptoticRegularCertificate AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight UpperHalfPlane ContinuousLinearMap
open AsymptoticCompactObservationCount (Row)

variable (q : ℕ) [Fact q.Prime]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)
variable {ι : Type*} [Fintype ι]

omit A in
theorem observation_gram_supported (hN : 0<N) (hqN : ¬q∣N)
    (r : ι → Row N) (hf : ∀ i,Fresh q (r i)) (s : ι → Set ℍ)
    (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε) (t : ℕ) (e : Sector N) (z : ℍ) :
    Supported (integralGroup q) (gram hN r s hs hε t e z) :=
  supported_stackGram _ _ (fun i => row_supported q hN hqN (r i) (hf i) e (hs i) hε t z)

theorem wholeNormal_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (r : ι → Row N) (hf : ∀ i,Fresh q (r i)) (s : ι → Set ℍ)
    (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    Supported (integralGroup q) (wholeNormal A hN P r s hs e z) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hR := includedFull_supported q A hN hqN hqQ P' (multiplier e) z
    (lt_trans (parameters_contraction A hN P (multiplier e) (fun p _ => multiplier_norm e p) z) (by norm_num))
  rw [wholeNormal_formula]
  apply supported_add
  · apply supported_comp _ _ _ (supported_adjoint _ _ hR)
    apply supported_comp _ _ _ _ hR
    exact supported_add _ _ _ (supported_one _)
      (observation_gram_supported q hN hqN r hf s hs P'.epsilon_pos (P'.s+4) e z)
  · exact supported_add _ _ _ (supported_one _)
      (supported_smul _ _ (supported_corner _ _ _) _)

theorem wholeInverse_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (r : ι → Row N) (hf : ∀ i,Fresh q (r i)) (s : ι → Set ℍ)
    (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    Supported (integralGroup q) (wholeInverse A hN P r s hs e z) :=
  supported_inverse _ _ (wholeNormal_supported q A hN hqN hqQ P r hf s hs e z) _
    (wholeNormal_norm_le A hN P r s hs e z) (wholeNormal_coercive A hN P r s hs e z)

theorem positive_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (r : ι → Row N) (hf : ∀ i,Fresh q (r i)) (s : ι → Set ℍ)
    (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    Supported (integralGroup q) (positive A hN P r s hs e z) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hR := includedFull_supported q A hN hqN hqQ P' (multiplier e) z
    (lt_trans (parameters_contraction A hN P (multiplier e) (fun p _ => multiplier_norm e p) z) (by norm_num))
  rw [positive_eq_whole]
  exact supported_comp _ _ _ hR (supported_comp _ _ _
    (wholeInverse_supported q A hN hqN hqQ P r hf s hs e z) (supported_adjoint _ _ hR))

/-- The actual finite joint kernel is integral whenever the prime
avoids the certificate and the finitely many earlier twist moduli. -/
theorem jointKernelProjection_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (r : ι → Row N) (hf : ∀ i,Fresh q (r i)) (s : ι → Set ℍ)
    (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    Supported (integralGroup q) (jointKernelProjection A hN P r s hs e z) := by
  apply supported_strong_limit _ (fun n => repeatedPositive A hN P r s hs e n z) _ _
    (repeatedPositive_strong_limit A hN P r s hs e z)
  intro n
  exact positive_supported q A hN hqN hqQ P
    (fun j : Fin ((n+1)^2) × ι => r j.2) (fun j => hf j.2)
    (fun j => s j.2) (fun j => hs j.2) e z

omit [Fintype ι] in
/-- Strong limits preserve integrality for global kernels as well. The
freshness condition concerns every earlier equation in this family. -/
theorem infiniteKernelProjection_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (r : ℕ → Row N) (hf : ∀ i,Fresh q (r i)) (s : ℕ → Set ℍ)
    (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    Supported (integralGroup q) (infiniteKernelProjection A hN P r s hs e z) := by
  apply supported_strong_limit _
    (fun n => jointKernelProjection A hN P (fun i : Fin n => r i)
      (fun i => s i) (fun i => hs i) e z) _ _
    (finiteKernelProjection_strong_limit A hN P r s hs e z)
  intro n
  exact jointKernelProjection_supported q A hN hqN hqQ P
    (fun i : Fin n => r i) (fun i => hf i) (fun i => s i) (fun i => hs i) e z

#print axioms observation_gram_supported
#print axioms wholeNormal_supported
#print axioms wholeInverse_supported
#print axioms positive_supported
#print axioms jointKernelProjection_supported
#print axioms infiniteKernelProjection_supported

end AsymptoticIntegralSubgroup
