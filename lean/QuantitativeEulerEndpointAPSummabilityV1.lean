module

public import QuantitativeEulerEndpointAPExceptionsV1
public import QuantitativeEulerEndpointCountSummabilityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointAP
open Finset
attribute [local instance] Classical.propDecidable

/-- Geometric counting cutoffs compatible with y^24=z and z^6=sqrt(x). -/
def blockCutoff (j : ℕ) : ℕ := 2^(288*(j+1))

theorem blockCutoff_pos (j : ℕ) : 0<blockCutoff j := by unfold blockCutoff; positivity

theorem blockCutoff_monotone : Monotone blockCutoff := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem blockCutoff_cofinal (n : ℕ) : ∃ j : ℕ, n≤blockCutoff j := by
  refine ⟨n,(show n<2^n from Nat.lt_two_pow_self).le.trans ?_⟩
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Summable majorant for the actual block-normalized exceptional counts. -/
theorem exception_block_counts_summable {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) (Q : ℕ) (hQ : 0<Q) :
    Summable (fun j : ℕ => (Nat.count (divisorException a Q) (blockCutoff (j+1)) : ℝ)/
      (blockCutoff j : ℝ)) := by
  obtain ⟨C,hC,hcount⟩ := divisorException_count_bound a ha Q hQ
  let r : ℝ := 1+apExponent M
  have hr : 1<r := by dsimp [r]; have := apExponent_pos M; linarith
  let K : ℝ := C*(2 : ℝ)^288/(Real.log 2)^r
  have hmajor (j : ℕ) :
      (Nat.count (divisorException a Q) (blockCutoff (j+1)) : ℝ)/(blockCutoff j : ℝ)≤
        K/((j+2 : ℕ) : ℝ)^r+(3+(Q : ℝ))/(2 : ℝ)^j := by
    let Y : ℕ := 2^(j+2)
    let z : ℕ := Y^24
    have hY : 4≤Y := by
      change 2^2≤2^(j+2)
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hbound := hcount (blockCutoff (j+1)) z Y hY le_rfl
    have hu : (blockCutoff j : ℝ)=(2 : ℝ)^(288*(j+1)) := by simp only [blockCutoff,Nat.cast_pow,Nat.cast_ofNat]
    have hYreal : (Y : ℝ)=(2 : ℝ)^(j+2) := by simp only [Y,Nat.cast_pow,Nat.cast_ofNat]
    have huz : (z : ℝ)^6=(2 : ℝ)^(144*(j+2)) := by
      simp only [z,Y,Nat.cast_pow,Nat.cast_ofNat,← pow_mul]
      congr 1
      omega
    have hnext : (blockCutoff (j+1) : ℝ)=(blockCutoff j : ℝ)*(2 : ℝ)^288 := by
      simp only [blockCutoff,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
      congr 1
    have hlog : Real.log (Y : ℝ)=((j+2 : ℕ) : ℝ)*Real.log 2 := by rw [hYreal,Real.log_pow]
    have hupos : (0 : ℝ)<blockCutoff j := by exact_mod_cast blockCutoff_pos j
    have hjpos : (0 : ℝ)<(2 : ℝ)^j := by positivity
    have hZratio : (z : ℝ)^6/(blockCutoff j : ℝ)≤1/(2 : ℝ)^j := by
      apply (div_le_div_iff₀ hupos hjpos).mpr
      rw [huz,hu,one_mul,← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hYratio : (Y : ℝ)/(blockCutoff j : ℝ)≤1/(2 : ℝ)^j := by
      apply (div_le_div_iff₀ hupos hjpos).mpr
      rw [hYreal,hu,one_mul,← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h1ratio : 1/(blockCutoff j : ℝ)≤1/(2 : ℝ)^j := by
      apply one_div_le_one_div_of_le hjpos
      rw [hu]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hQratio : (Q : ℝ)/(blockCutoff j : ℝ)≤(Q : ℝ)/(2 : ℝ)^j :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg Q) hjpos (by
        rw [hu]; exact pow_le_pow_right₀ (by norm_num) (by omega))
    have hmain : (C*(blockCutoff (j+1) : ℝ)/(Real.log (Y : ℝ))^r)/(blockCutoff j : ℝ)=
        K/((j+2 : ℕ) : ℝ)^r := by
      rw [hnext,hlog,Real.mul_rpow (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))]
      dsimp [K]
      field_simp
    have hnorm := div_le_div_of_nonneg_right hbound hupos.le
    have he : (C*(blockCutoff (j+1) : ℝ)/(Real.log (Y : ℝ))^r+(z : ℝ)^6+(Y+1 : ℕ)+(Q : ℝ))/
        (blockCutoff j : ℝ)=K/((j+2 : ℕ) : ℝ)^r+(z : ℝ)^6/(blockCutoff j : ℝ)+
          (Y : ℝ)/(blockCutoff j : ℝ)+1/(blockCutoff j : ℝ)+(Q : ℝ)/(blockCutoff j : ℝ) := by
      rw [Nat.cast_add,Nat.cast_one]
      rw [add_div,add_div,add_div,hmain]
      ring
    change _≤(C*(blockCutoff (j+1) : ℝ)/(Real.log (Y : ℝ))^r+(z : ℝ)^6+(Y+1 : ℕ)+(Q : ℝ))/
      (blockCutoff j : ℝ) at hnorm
    rw [he] at hnorm
    have herr := add_le_add (add_le_add hZratio hYratio) (add_le_add h1ratio hQratio)
    have herr' : (z : ℝ)^6/(blockCutoff j : ℝ)+(Y : ℝ)/(blockCutoff j : ℝ)+
        1/(blockCutoff j : ℝ)+(Q : ℝ)/(blockCutoff j : ℝ)≤(3+(Q : ℝ))/(2 : ℝ)^j := by
      convert herr using 1 <;> ring
    linarith
  have hp : Summable (fun j : ℕ => 1/((j+2 : ℕ) : ℝ)^r) := by
    exact (Real.summable_one_div_nat_rpow.mpr hr).comp_injective
      (show Function.Injective (fun j : ℕ => j+2) from fun _ _ h => Nat.add_right_cancel h)
  have hmain : Summable (fun j : ℕ => K/((j+2 : ℕ) : ℝ)^r) := by
    apply (hp.mul_left K).congr
    intro j
    ring
  have hg : Summable (fun j : ℕ => (3+(Q : ℝ))/(2 : ℝ)^j) := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1)
    apply (hs.mul_left (3+(Q : ℝ))).congr
    intro j
    rw [div_pow,one_pow]
    ring
  exact Summable.of_nonneg_of_le
    (fun j => div_nonneg (Nat.cast_nonneg (Nat.count (divisorException a Q) (blockCutoff (j+1))))
      (Nat.cast_nonneg (blockCutoff j))) hmajor (hmain.add hg)

/-- Unconditional reciprocal summability of the actual shifted-divisor
exceptional primes, for every positive shift and every unit residue class. -/
theorem divisorException_reciprocal_summable {M : ℕ} [NeZero M]
    (a : ZMod M) (ha : IsUnit a) (Q : ℕ) (hQ : 0<Q) :
    Summable (reciprocalIndicator (divisorException a Q)) :=
  summable_reciprocal_of_block_counts (divisorException a Q) blockCutoff
    blockCutoff_monotone blockCutoff_pos blockCutoff_cofinal
    (exception_block_counts_summable a ha Q hQ)

#print axioms exception_block_counts_summable
#print axioms divisorException_reciprocal_summable
end QuantitativeEulerEndpointAP
