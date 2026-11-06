module

public import QuantitativeArithmeticCertificateV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmetic

open QuantitativeHolomorphic

/-- A determinant-one first column rules out a zero upper-right residue.
Primality is unnecessary: q > 1 suffices. -/
theorem canonical_upper_right_not_dvd (q B N d D : ℤ) (hq : 1 < q)
    (hdet : q*D-N*d*B = 1) : ¬q ∣ B := by
  intro hB
  have hdiv : q ∣ q*D-N*d*B :=
    dvd_sub (dvd_mul_right q D) (dvd_mul_of_dvd_right hB (N*d))
  rw [hdet] at hdiv
  have hle := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hdiv
  omega

/-- Choose the canonical residue beta and its integral translation.
The weighted bound on l is tailored to an O(q^2) bound on B. -/
theorem exists_canonical_residue (q B N d D : ℤ) (hq : 1 < q)
    (hdet : q*D-N*d*B = 1) :
    ∃ β l : ℤ, 1 ≤ β ∧ β < q ∧ B+q*l = -β ∧ q*|l| ≤ |B|+q := by
  let β := (-B)%q
  let l := (-B)/q
  have hqpos : 0 < q := by omega
  have hβnonneg : 0 ≤ β := Int.emod_nonneg _ (by omega)
  have hβlt : β < q := Int.emod_lt_of_pos _ hqpos
  have hβne : β ≠ 0 := by
    intro hz
    have hb : q ∣ -B := Int.dvd_of_emod_eq_zero hz
    exact canonical_upper_right_not_dvd q B N d D hq hdet (by simpa using hb)
  have hβpos : 1 ≤ β := by omega
  have heq : B+q*l = -β := by
    have he := Int.emod_add_ediv_mul (-B) q
    change β+l*q = -B at he
    nlinarith [he]
  refine ⟨β, l, hβpos, hβlt, heq, ?_⟩
  calc
    q*|l| = |q*l| := by rw [abs_mul, abs_of_pos hqpos]
    _ = |-β-B| := by congr 1; linarith
    _ ≤ |-β|+|-B| := abs_add_le _ _
    _ = β+|B| := by rw [abs_neg, abs_neg, abs_of_nonneg hβnonneg]
    _ ≤ |B|+q := by omega

theorem canonical_translation_linear_bound (q B l A : ℤ) (hq : 0 < q)
    (hB : |B| ≤ A*q^2) (hl : q*|l| ≤ |B|+q) :
    |l| ≤ (A+1)*q := by
  have hqone : 1 ≤ q := hq
  have h := mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ q-1 by omega)
  nlinarith

/-- The congruence used to choose the divisor transports a Bezout identity. -/
theorem divisor_bezout (N Q c d x y : ℤ)
    (hcop : x*N+y*c = 1) (hcong : N*Q ∣ d-c) :
    ∃ x' : ℤ, x'*N+y*d = 1 := by
  obtain ⟨t, ht⟩ := hcong
  refine ⟨x-y*Q*t, ?_⟩
  calc
    (x-y*Q*t)*N+y*d = x*N+y*c+y*((d-c)-N*Q*t) := by ring
    _ = 1 := by rw [ht, sub_self, mul_zero, add_zero, hcop]

theorem shear_exponent_bound (Q c d q r : ℤ) (hQ : 0 < Q)
    (hd : 0 ≤ d) (hdq : d ≤ q) (hr : d = c+r*Q) :
    |r| ≤ q+|c| := by
  have hQone : 1 ≤ Q := hQ
  have hmul : |r| ≤ |r| * Q := by nlinarith [abs_nonneg r]
  calc
    |r| ≤ |r| * Q := hmul
    _ = |r*Q| := by rw [abs_mul, abs_of_pos hQ]
    _ = |d-c| := by rw [hr]; congr 1; ring
    _ ≤ |d|+|c| := by simpa [sub_eq_add_neg] using abs_add_le d (-c)
    _ ≤ q+|c| := by rw [abs_of_nonneg hd]; omega

theorem shear_second_exponent_bound (Q N d q s : ℤ) (hQ : 0 < Q)
    (hN : 0 < N) (hd : 0 < d) (hQq : Q ≤ q)
    (hs : q = Q+N*s*d) : 0 ≤ s ∧ s ≤ q := by
  have hNd : 0 < N*d := mul_pos hN hd
  have hprod : (N*d)*s = q-Q := by nlinarith [hs]
  have hsnonneg : 0 ≤ s := by nlinarith
  have hNdone : 1 ≤ N*d := hNd
  constructor
  · exact hsnonneg
  · nlinarith [mul_nonneg (show 0 ≤ N*d-1 by omega) hsnonneg]

/-- Produce both integral shear exponents directly from the chosen divisor,
with explicit linear bounds. The divisor existence remains an input. -/
theorem exists_bounded_shear_witnesses (Q N c d q x y : ℤ)
    (hQ : 0 < Q) (hN : 0 < N) (hd : 0 < d) (hdq : d ≤ q) (hQq : Q ≤ q)
    (hcop : x*N+y*c = 1) (hcong : N*Q ∣ d-c)
    (hNdiv : N ∣ q-Q) (hddiv : d ∣ q-Q) :
    ∃ r s : ℤ, d = c+r*Q ∧ q = Q+N*s*d ∧ |r| ≤ q+|c| ∧ 0 ≤ s ∧ s ≤ q := by
  obtain ⟨r, hr⟩ := shear_witness_of_congruence N Q c d hcong
  obtain ⟨x', hx'⟩ := divisor_bezout N Q c d x y hcop hcong
  obtain ⟨s, hs⟩ := product_divides_of_bezout N d (q-Q) x' y hx' hNdiv hddiv
  have hs' : q = Q+N*s*d := by nlinarith [hs]
  have hb := shear_second_exponent_bound Q N d q s hQ hN hd hQq hs'
  exact ⟨r, s, hr, hs', shear_exponent_bound Q c d q r hQ (by omega) hdq hr,
    hb.1, hb.2⟩

/-- An actual canonical determinant-one matrix, including bounded choices of
both shears and the final translation. This uses no density assertion. -/
theorem exists_canonical_certificate (Q B N c D d q x y : ℤ)
    (hQ : 0 < Q) (hN : 0 < N) (hd : 0 < d) (hdq : d < q) (hQq : Q ≤ q)
    (hq : 1 < q) (hdet : Q*D-N*c*B = 1)
    (hcop : x*N+y*c = 1) (hcong : N*Q ∣ d-c)
    (hNdiv : N ∣ q-Q) (hddiv : d ∣ q-Q) :
    ∃ r s β l B' D' : ℤ,
      |r| ≤ q+|c| ∧ 0 ≤ s ∧ s ≤ q ∧ 1 ≤ β ∧ β < q ∧ q*|l| ≤ |B'|+q ∧
      upperUnipotent s * lowerUnipotent N r * certificateMatrix Q B N c D =
        certificateMatrix q B' N d D' ∧
      lowerUnipotent N (-1) * certificateMatrix q B' N d D' * upperUnipotent l =
        !![q, -β; -N*(q-d), D'+N*d*l+N*β] ∧
      q*(D'+N*d*l+N*β) = 1+N*(q-d)*β := by
  obtain ⟨r, s, hr, hs, hrbound, hsnonneg, hsbound⟩ :=
    exists_bounded_shear_witnesses Q N c d q x y hQ hN hd (by omega) hQq
      hcop hcong hNdiv hddiv
  let B' := B+s*(N*r*B+D)
  let D' := N*r*B+D
  have hshear := certificate_shear_of_witnesses Q B N c D r s d q hr hs
  have hdet' : q*D'-N*d*B' = 1 := by
    have he := certificate_shear_det Q B N c D r s
    rw [← hr, ← hs, certificate_det, certificate_det] at he
    exact he.trans hdet
  obtain ⟨β, l, hβpos, hβlt, hβeq, hlbound⟩ :=
    exists_canonical_residue q B' N d D' hq hdet'
  exact ⟨r, s, β, l, B', D', hrbound, hsnonneg, hsbound, hβpos, hβlt,
    hlbound, hshear, canonical_conversion q B' N d D' l β hβeq,
    canonical_bottom_right q B' N d D' l β hdet' hβeq⟩

#print axioms exists_canonical_residue
#print axioms canonical_translation_linear_bound
#print axioms exists_bounded_shear_witnesses
#print axioms exists_canonical_certificate

end QuantitativeArithmetic
