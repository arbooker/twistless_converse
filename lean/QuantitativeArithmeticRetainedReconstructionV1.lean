module

public import QuantitativeArithmeticRetainedCertificateV1
public import FinitenessAnalyticReconstructionV1

set_option autoImplicit false

@[expose] public section

namespace QuantitativeArithmeticRetainedReconstruction

open QuantitativeArithmeticRetainedCertificate SpanningIntegerRows Matrix
  SpanningCyclicCoordinates SpanningTraceAlgebra FinitenessAnalyticReconstruction

variable {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
variable {K : Type*} [Field K] [CharZero K]

theorem coordinate_cast (A : Certificate N P Q hQ) (j t : Fin Q) :
    ∑ i ∈ (A.coeff j).support, (A.coeff j i : K) * (rows N P hQ i t : K) =
      if t = j then 1 else 0 := by
  classical
  have h := congrArg (fun a : ℚ => (a : K)) (coordinate_identity A j t)
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, apply_ite,
    Rat.cast_one, Rat.cast_zero] using h

/-- The mixed-row certificate reconstructs every finite coordinate vector
in characteristic zero. -/
theorem reconstruct_vector (A : Certificate N P Q hQ) (j : Fin Q) (v : Fin Q → K) :
    ∑ i ∈ (A.coeff j).support, (A.coeff j i : K) *
      dotProduct (fun t => (rows N P hQ i t : K)) v = v j := by
  classical
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ t, ∑ i ∈ (A.coeff j).support,
        (A.coeff j i : K) * ((rows N P hQ i t : K) * v t)) =
        ∑ t, (∑ i ∈ (A.coeff j).support,
          (A.coeff j i : K) * (rows N P hQ i t : K)) * v t := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ t, (if t = j then (1 : K) else 0) * v t := by
      simp only [coordinate_cast]
    _ = v j := by simp

/-- The literal mixed row sum on a periodic sequence. -/
def rowSum (v : ℤ → K) : AugIndex N (P : Set ℕ) Q → K
  | Sum.inl x => primitive x.val.1 (Q / x.val.1) v x.val.2
  | Sum.inr x => trace x.1.val (Q / x.1.val) v x.2

omit [CharZero K] in
theorem row_eval (v : Fin Q → K) (i : AugIndex N (P : Set ℕ) Q) :
    dotProduct (fun t => (rows N P hQ i t : K)) v = rowSum (extend hQ v) i := by
  cases i with
  | inl x => exact primitiveRow_eval hQ x.val.1 (Q / x.val.1) x.val.2 v
  | inr x => exact traceRow_eval hQ x.1.val (Q / x.1.val) x.2 v

/-- Reconstruction of any periodic sequence, before using analytic laws. -/
theorem reconstruct_periodic (A : Certificate N P Q hQ) (j : Fin Q) (v : ℤ → K)
    (hv : Cyclic Q v) :
    ∑ i ∈ (A.coeff j).support, (A.coeff j i : K) * rowSum v i = v j := by
  have h := reconstruct_vector A j (coordinates v)
  have he := extend_coordinates hQ hv
  simpa only [row_eval, he, coordinates] using h

noncomputable def completeTwist (F : ℂ → ℂ) (q : ℕ) (z : ℂ) : ℂ :=
  ∑ a ∈ Finset.range q, F (z + (a : ℂ) / q)

theorem sample_complete_row (F : ℂ → ℂ) {Q q : ℕ} (hQ : 0 < Q) (hq : q ∣ Q)
    (j u : ℤ) (z : ℂ) :
    trace q (Q / q) (sample F Q j z) u =
      completeTwist F q (z + ((u : ℂ) - j) / Q) := by
  have hqp : 0 < q := Nat.pos_of_dvd_of_pos hq hQ
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hqp.ne'
  have he : (q : ℂ) * ((Q / q : ℕ) : ℂ) = (Q : ℂ) := by
    exact_mod_cast Nat.mul_div_cancel' hq
  unfold SpanningTraceAlgebra.trace sample completeTwist
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  push_cast
  simp only [← Int.natCast_ediv, Int.cast_natCast]
  field_simp
  linear_combination (a : ℂ) * he

/-- The two analytic row types, with complete twists still literal. -/
noncomputable def twistRow (F : ℂ → ℂ) (j : Fin Q) (z : ℂ) :
    AugIndex N (P : Set ℕ) Q → ℂ
  | Sum.inl x => twist F x.val.1 (z + ((x.val.2 : ℂ) - (j : ℕ)) / Q)
  | Sum.inr x => completeTwist F x.1.val (z + ((x.2 : ℂ) - (j : ℕ)) / Q)

/-- Sampling the finite mixed-row certificate gives the exact analytic
identity. Divisibility is needed only to identify the complete samples. -/
theorem reconstruct_twists (A : Certificate N P Q hQ)
    (hdiv : ∀ p ∈ P, p ∣ Q)
    (F : ℂ → ℂ) (hp : ∀ z, F (z + 1) = F z) (j : Fin Q) (z : ℂ) :
    F z = ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) * twistRow F j z i := by
  have h := reconstruct_periodic A j (sample F Q j z) (sample_cyclic F hp hQ j z)
  have he (i : AugIndex N (P : Set ℕ) Q) :
      rowSum (sample F Q j z) i = twistRow F j z i := by
    cases i with
    | inl x =>
      simpa only [rowSum, twistRow, Int.cast_natCast] using
        sample_row F hQ x.property.1 (j : ℤ) x.val.2 z
    | inr x =>
      simpa only [rowSum, twistRow, Int.cast_natCast] using
        sample_complete_row F hQ (hdiv x.1.val x.1.property) (j : ℤ) x.2 z
  simpa only [he, sample, Int.cast_natCast, sub_self, zero_div, add_zero] using h.symm

/-- Fricke-transform the legal primitive rows and leave complete rows literal. -/
noncomputable def frickeRow (F : ℂ → ℂ) (k : ℕ) (χ : ℕ → ℂ)
    (j : Fin Q) (z : ℂ) : AugIndex N (P : Set ℕ) Q → ℂ
  | Sum.inl x =>
    χ x.val.1 /
      (((Real.sqrt (Nat.lcm N (x.val.1 ^ 2)) : ℝ) : ℂ) *
        (z + ((x.val.2 : ℂ) - (j : ℕ)) / Q)) ^ k *
      twist F x.val.1 (-1 / ((Nat.lcm N (x.val.1 ^ 2) : ℕ) *
        (z + ((x.val.2 : ℂ) - (j : ℕ)) / Q)))
  | Sum.inr x => completeTwist F x.1.val (z + ((x.2 : ℂ) - (j : ℕ)) / Q)

theorem reconstruct_FE (A : Certificate N P Q hQ) (hdiv : ∀ p ∈ P, p ∣ Q)
    (F : ℂ → ℂ) (hp : ∀ z, F (z + 1) = F z) (k : ℕ) (χ : ℕ → ℂ)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ w : ℂ, 0 < w.im →
      twist F q w = χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * w) ^ k *
        twist F q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * w)))
    (j : Fin Q) (z : ℂ) (hz : 0 < z.im) :
    F z = ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) * frickeRow F k χ j z i := by
  rw [reconstruct_twists A hdiv F hp j z]
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | inl x =>
    dsimp only [twistRow, frickeRow]
    rw [hFE x.val.1 x.property.1]
    simpa using hz
  | inr x => rfl

/-- Complete retained rows become scalar dilation branches. Setting `b p=0`
allows the highly ramified vanishing law without a separate construction. -/
noncomputable def dilationRow (F : ℂ → ℂ) (k : ℕ) (χ b : ℕ → ℂ)
    (j : Fin Q) (z : ℂ) : AugIndex N (P : Set ℕ) Q → ℂ
  | Sum.inl x => frickeRow (P := P) F k χ j z (Sum.inl x)
  | Sum.inr x => b x.1.val * F ((x.1.val : ℂ) * (z + ((x.2 : ℂ) - (j : ℕ)) / Q))

theorem reconstruct_FE_dilation (A : Certificate N P Q hQ) (hdiv : ∀ p ∈ P, p ∣ Q)
    (F : ℂ → ℂ) (hp : ∀ z, F (z + 1) = F z) (k : ℕ) (χ b : ℕ → ℂ)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ w : ℂ, 0 < w.im →
      twist F q w = χ q / (((Real.sqrt (Nat.lcm N (q ^ 2)) : ℝ) : ℂ) * w) ^ k *
        twist F q (-1 / ((Nat.lcm N (q ^ 2) : ℕ) * w)))
    (hcomplete : ∀ p ∈ P, ∀ w : ℂ, 0 < w.im →
      completeTwist F p w = b p * F ((p : ℂ) * w))
    (j : Fin Q) (z : ℂ) (hz : 0 < z.im) :
    F z = ∑ i ∈ (A.coeff j).support,
      (A.coeff j i : ℂ) * dilationRow F k χ b j z i := by
  rw [reconstruct_FE A hdiv F hp k χ hFE j z hz]
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | inl x => rfl
  | inr x =>
    dsimp only [frickeRow, dilationRow]
    rw [hcomplete x.1.val x.1.property]
    simpa using hz

#print axioms coordinate_cast
#print axioms reconstruct_vector
#print axioms reconstruct_periodic
#print axioms sample_complete_row
#print axioms reconstruct_twists
#print axioms reconstruct_FE
#print axioms reconstruct_FE_dilation

end QuantitativeArithmeticRetainedReconstruction
