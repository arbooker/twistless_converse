module

public import AsymptoticIntegralMatricesV1
public import AsymptoticIntegralBranchSupportV1
public import AsymptoticRegularObservationRowsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticIntegralSubgroup

open AsymptoticRegularObservationRows AsymptoticSubgroupSupport
open AsymptoticRegularBranchFamily AsymptoticCompactObservationCount
open AsymptoticSectorSigns UpperHalfPlane

variable (q : ℕ) [Fact q.Prime]

theorem not_dvd_level (N r : ℕ) (hN : ¬q∣N) (hr : ¬q∣r) : ¬q∣Nat.lcm N (r^2) := by
  intro hd
  have hl : Nat.lcm N (r^2)∣N*r^2 := Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)
  rcases (Fact.out : q.Prime).dvd_mul.mp (hd.trans hl) with h | h
  · exact hN h
  · exact hr ((Fact.out : q.Prime).dvd_of_dvd_pow h)

theorem twistBranches_integral (N r : ℕ) (hN : 0<N) (hr : 0<r) (hqN : ¬q∣N) (hqr : ¬q∣r)
    (i : AsymptoticCertificateBranches.residues r ⊕ AsymptoticCertificateBranches.residues r) :
    (twistBranches N r hN hr i).matrix∈integralGL q := by
  cases i with
  | inl a =>
    exact translation_fraction_integral q (a.val:ℤ) r hqr
  | inr a =>
    apply reconstruction_integral q (Nat.lcm N (r^2)) (Nat.lcm_pos hN (pow_pos hr 2)).ne'
      (not_dvd_level q N r hqN hqr) 0 ((a.val:ℚ)/r)
    · simp
    · rw [padicNorm.div,(padicNorm.nat_eq_one_iff r).mpr hqr,div_one]
      exact padicNorm.of_nat _

theorem ramifiedBranches_integral (N p : ℕ) (hp : 0<p) (hpN : p∣N) (hqN : ¬q∣N)
    (i : Fin p ⊕ Unit) : (ramifiedBranches p hp i).matrix∈integralGL q := by
  cases i with
  | inl a => exact ramified_integral q p a.val hp.ne' (fun h => hqN (h.trans hpN))
  | inr u => exact (translation_integral_iff q 0).mpr (by simp)

/-- A prime is fresh for an earlier row if it avoids that row's twist
modulus. Avoiding the conductor handles every ramified row at once. -/
def Fresh {N : ℕ} (r : Row N) : Prop :=
  match r with
  | .twist m _ => ¬q∣m
  | .ramified _ _ _ => True

theorem row_supported {N : ℕ} (hN : 0<N) (hqN : ¬q∣N) (r : Row N) (hf : Fresh q r)
    (e : Sector N) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    Supported (integralGroup q) (row hN r e hs hε t x) := by
  cases r with
  | twist m hm => exact compact_family_supported q _ _ (twistBranches_integral q N m hN hm hqN hf) hs hε t x
  | ramified p hp hpN => exact compact_family_supported q _ _ (ramifiedBranches_integral q N p hp.pos hpN hqN) hs hε t x

#print axioms not_dvd_level
#print axioms twistBranches_integral
#print axioms ramifiedBranches_integral
#print axioms row_supported

end AsymptoticIntegralSubgroup
