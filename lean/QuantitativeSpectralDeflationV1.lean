module

public import AsymptoticBlockLossV1

set_option autoImplicit false
@[expose] public section

/-!
Quantitative scalar bookkeeping for spectral deflation. Unlike the original
kernel deflation, the sharp spectral comparison loses a factor two. Operator
spectral-compression and fresh-coset hypotheses have not been instantiated here;
this module proves the resulting finite-block and positive-excess arithmetic.
-/

namespace QuantitativeSpectralDeflation

/-- Exact finite-block denominator for the spectral fresh-prime inequality.
The compression loss may be bounded by all other removals, including future
ones. This weakens the hypothesis and permits arbitrary order in a block. -/
theorem spectral_block_loss {m : ℕ} (hm : 0 < m) (e Q : ℝ)
    (q r s d : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i) (hQ : 1 < Q)
    (hmax : ∀ i, q i ≤ Q) (hdetect : e ≤ ∑ i, r i)
    (hrestrict : ∀ i, r i ≤ s i + ((∑ j, d j) - d i))
    (hfresh : ∀ i, s i ≤ 2 * (q i - 1) * d i) :
    e / (2 * Q + (m : ℝ) - 3) ≤ ∑ i, d i := by
  have h := AsymptoticBlockLoss.block_loss hm e (2*Q-1)
    (fun i => 2*q i-1) r s d hd (by linarith)
    (fun i => by linarith [hmax i]) hdetect hrestrict
    (fun i => by nlinarith [hfresh i])
  convert h using 1
  ring

/-- Taking the positive excess is legitimate even after the remaining trace
falls below the target. The scalar loss assumptions need not assert that the
trace always stays above the target. -/
theorem positive_excess_step {p p' c a : ℝ} (ha : a ≤ 1)
    (hloss : a * (p-c) ≤ p-p') :
    max 0 (p'-c) ≤ (1-a) * max 0 (p-c) := by
  have hnonneg : 0 ≤ 1-a := sub_nonneg.mpr ha
  have hraw : p'-c ≤ (1-a)*(p-c) := by nlinarith
  apply max_le
  · exact mul_nonneg hnonneg (le_max_left _ _)
  · exact hraw.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hnonneg)

/-- Explicit finite-packet loss with a fixed target, valid across target
crossings. Prime-distribution estimates enter only after this theorem. -/
theorem trace_le_target_add_exp (p a : ℕ → ℝ) (c : ℝ)
    (ha : ∀ n, a n ≤ 1)
    (hloss : ∀ n, a n * (p n-c) ≤ p n-p (n+1)) (n : ℕ) :
    p n ≤ c + max 0 (p 0-c) * Real.exp (-(∑ i ∈ Finset.range n, a i)) := by
  have h := AsymptoticBlockLoss.excess_le_exp (fun n => max 0 (p n-c)) a
    (fun n => le_max_left _ _) (fun n => positive_excess_step (ha n) (hloss n)) n
  have := le_max_right (0 : ℝ) (p n-c)
  linarith

#print axioms spectral_block_loss
#print axioms positive_excess_step
#print axioms trace_le_target_add_exp

end QuantitativeSpectralDeflation
