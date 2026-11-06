module

public import AsymptoticIntegralObservationsV1
public import AsymptoticRegularIncludedReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticIntegralSubgroup

open AsymptoticSubgroupSupport AsymptoticRegularCertificate AsymptoticCertificateBranches
open AsymptoticRegularReconstruction AsymptoticRationalBranches
open FinitenessCertificate FinitenessGlobalHeight UpperHalfPlane ContinuousLinearMap

variable (q : ℕ) [Fact q.Prime]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

omit [Fact q.Prime] in
theorem certificate_modulus_fresh (hqQ : ¬q∣Q) (v : Index A) : ¬q∣modulus A v :=
  fun h => hqQ (h.trans v.2.1.val.property.1)

theorem certificate_input_integral (hqQ : ¬q∣Q) (v : Index A) :
    padicNorm q (inputShiftQ A v)≤1 := by
  unfold inputShiftQ
  rw [padicNorm.div,(padicNorm.nat_eq_one_iff Q).mpr hqQ,div_one]
  exact padicNorm.sub.trans (max_le (padicNorm.of_int _) (padicNorm.of_nat _))

theorem certificate_output_integral (hqQ : ¬q∣Q) (v : Index A) :
    padicNorm q (outputShiftQ A v)≤1 := by
  unfold outputShiftQ
  rw [padicNorm.div,(padicNorm.nat_eq_one_iff (modulus A v)).mpr
    (certificate_modulus_fresh q A hqQ v),div_one]
  exact padicNorm.of_nat _

/-- Every actual reconstruction branch and every integer fold lies in
the fresh-prime subgroup; the certificate supplies all denominators. -/
theorem certificate_fold_integral (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (v : Index A) (n : ℤ) :
    fold (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v) n∈integralGroup q := by
  apply ofMatrix_mem
  apply reconstruction_integral q (Nat.lcm N ((modulus A v)^2))
    (Nat.lcm_pos hN (pow_pos (modulus_pos A v) 2)).ne'
    (not_dvd_level q N (modulus A v) hqN (certificate_modulus_fresh q A hqQ v))
  · exact certificate_input_integral q A hqQ v
  · exact padicNorm.sub.trans (max_le (certificate_output_integral q A hqQ v) (padicNorm.of_int n))

theorem lowPart_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) {t : ℕ} (ht : 1≤t) (v : Index A) (z : ℍ) :
    Supported (integralGroup q) (lowPart A hN P t v z) := by
  apply supported_tsum
  · exact Summable.of_norm (AsymptoticRegularFoldedLow.term_norm_summable _ _ _ _ _ _ _ _ _ ht z)
  · intro n
    exact supported_weighted_branch _ _ (certificate_fold_integral q A hN hqN hqQ v n) _ _ _ z

theorem terminalPart_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) {t : ℕ} (ht : 2≤t) (v : Index A) (z : ℍ) :
    Supported (integralGroup q) (terminalPart A hN P ht v z) := by
  apply supported_tsum
  · exact Summable.of_norm (AsymptoticRegularFoldedTerminal.term_norm_summable _ _ _ _ _ _ _ _ _ _ ht z)
  · intro n
    exact supported_weighted_branch _ _ (certificate_fold_integral q A hN hqN hqQ v n) _ _ _ z

theorem low_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Supported (integralGroup q) (AsymptoticRegularCertificate.low A hN P χ t z) := by
  apply supported_finsetSum
  intro v _
  exact supported_smul _ _ (lowPart_supported q A hN hqN hqQ P ht v z) _

theorem terminal_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t) (z : ℍ) :
    Supported (integralGroup q) (terminal A hN P χ ht z) := by
  apply supported_finsetSum
  intro v _
  exact supported_smul _ _ (terminalPart_supported q A hN hqN hqQ P ht v z) _

/-- The bounded Neumann reconstruction preserves q-integral support. -/
theorem full_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖AsymptoticRegularCertificate.low A hN P χ (P.s+3) z‖<1) :
    Supported (integralGroup q) (full A hN P χ z) := by
  apply supported_comp
  · apply supported_add _ _ _ (supported_one _)
    apply supported_comp
    · apply supported_tsum _ _ (summable_geometric_of_norm_lt_one hK)
      intro n
      exact supported_pow _ _ (low_supported q A hN hqN hqQ P χ (by omega) z) n
    · exact terminal_supported q A hN hqN hqQ P χ (by omega) z
  · exact supported_corner _ _ _

theorem includedFull_supported (hN : 0<N) (hqN : ¬q∣N) (hqQ : ¬q∣Q)
    (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖AsymptoticRegularCertificate.low A hN P χ (P.s+3) z‖<1) :
    Supported (integralGroup q) (includedFull A hN P χ z) := by
  apply supported_comp
  · exact supported_weighted_branch _ 1 (integralGroup q).one_mem _ _ _ z
  · exact full_supported q A hN hqN hqQ P χ z hK

#print axioms certificate_modulus_fresh
#print axioms certificate_input_integral
#print axioms certificate_output_integral
#print axioms certificate_fold_integral
#print axioms lowPart_supported
#print axioms terminalPart_supported
#print axioms low_supported
#print axioms terminal_supported
#print axioms full_supported
#print axioms includedFull_supported

end AsymptoticIntegralSubgroup
