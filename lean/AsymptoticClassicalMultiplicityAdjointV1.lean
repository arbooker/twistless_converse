module

public import AsymptoticClassicalMultiplicityPartialV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

/-- The Fricke target at a divisor prime is the corresponding dilation group. -/
theorem frickeOldLevel_div_eq_dilationLevel (N q : ℕ) (hN : 0 < N)
    (hq : 0 < q) (hqN : q ∣ N) :
    frickeOldLevel N (N / q) hN = dilationLevel (N / q) q hq := by
  have hm : q * (N / q) = N := Nat.mul_div_cancel' hqN
  have he := frickeOldLevel_eq_dilationLevel (N / q) q
    (Nat.div_pos (Nat.le_of_dvd hN hqN) hq) hq
  simpa only [hm] using he

/-- Ordinary trace carries the actual q-new kernel to the lower-level q-new
 kernel. Petersson adjunction reduces this to inclusions of old groups. -/
theorem trace_mem_primeTraceKernel (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : 0 < p) (k : ℤ)
    (q : {q : ℕ // q.Prime ∧ q ∣ M}) (f : CuspForm (level (p * M)) k)
    (hf : f ∈ primeTraceKernel (p * M) (Nat.mul_pos hp hM) k
      ⟨q.val, q.property.1, dvd_mul_of_dvd_right q.property.2 p⟩) :
    arithmeticTrace (level (p * M)) (level M) k f ∈ primeTraceKernel M hM k q := by
  let : NeZero (M / q.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hM q.property.2) q.property.1.pos).ne'⟩
  have hqN : q.val ∣ p * M := dvd_mul_of_dvd_right q.property.2 p
  let : NeZero (p * M / q.val) := ⟨(Nat.div_pos
    (Nat.le_of_dvd (Nat.mul_pos hp hM) hqN) q.property.1.pos).ne'⟩
  have hd : M / q.val ∣ p * M / q.val := by
    rw [Nat.mul_div_assoc p q.property.2]
    exact Nat.dvd_mul_left (M / q.val) p
  have hF : frickeOldLevel (p * M) (p * M / q.val) (Nat.mul_pos hp hM) ≤
      frickeOldLevel M (M / q.val) hM := by
    rw [frickeOldLevel_div_eq_dilationLevel (p * M) q.val (Nat.mul_pos hp hM) q.property.1.pos hqN,
      frickeOldLevel_div_eq_dilationLevel M q.val hM q.property.1.pos q.property.2]
    exact dilationLevel_mono q.property.1.pos hd
  change arithmeticTrace (level (p * M)) (level (p * M / q.val)) k f = 0 ∧
    arithmeticTrace (level (p * M))
      (frickeOldLevel (p * M) (p * M / q.val) (Nat.mul_pos hp hM)) k f = 0 at hf
  change arithmeticTrace (level M) (level (M / q.val)) k
      (arithmeticTrace (level (p * M)) (level M) k f) = 0 ∧
    arithmeticTrace (level M) (frickeOldLevel M (M / q.val) hM) k
      (arithmeticTrace (level (p * M)) (level M) k f) = 0
  constructor
  · apply (trace_zero_iff M (M / q.val) k (Nat.div_dvd_of_dvd q.property.2) _).mpr
    intro g
    rw [trace_adjoint (p * M) M k (Nat.dvd_mul_left M p)]
    have he := (trace_zero_iff (p * M) (p * M / q.val) k (Nat.div_dvd_of_dvd hqN) f).mp hf.1
      (restrict k (level_antitone hd) g)
    have hforms : restrict k (level_antitone (Nat.dvd_mul_left M p))
        (restrict k (level_antitone (Nat.div_dvd_of_dvd q.property.2)) g) =
      restrict k (level_antitone (Nat.div_dvd_of_dvd hqN))
        (restrict k (level_antitone hd) g) := by ext z; rfl
    rw [hforms]
    exact he
  · apply (fricke_trace_zero_iff M (M / q.val) hM k (Nat.div_dvd_of_dvd q.property.2) _).mpr
    intro g
    rw [trace_adjoint (p * M) M k (Nat.dvd_mul_left M p)]
    have he := (fricke_trace_zero_iff (p * M) (p * M / q.val) (Nat.mul_pos hp hM) k
      (Nat.div_dvd_of_dvd hqN) f).mp hf.2 (restrict k hF g)
    have hforms : restrict k (level_antitone (Nat.dvd_mul_left M p))
        (restrict k (level_le_frickeOldLevel hM (Nat.div_dvd_of_dvd q.property.2)) g) =
      restrict k (level_le_frickeOldLevel (Nat.mul_pos hp hM) (Nat.div_dvd_of_dvd hqN))
        (restrict k hF g) := by ext z; rfl
    rw [hforms]
    exact he

/-- The actual Petersson adjoint of ordinary p inclusion preserves every
 partial intersection of the other prime-new conditions. -/
theorem trace_mem_partialNewSpace (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : 0 < p) (k : ℤ) (S : Set ℕ)
    (f : CuspForm (level (p * M)) k)
    (hf : f ∈ partialNewSpace (p * M) (Nat.mul_pos hp hM) k S) :
    arithmeticTrace (level (p * M)) (level M) k f ∈ partialNewSpace M hM k S := by
  rw [mem_partialNewSpace] at hf ⊢
  intro q hqS
  exact trace_mem_primeTraceKernel M p hM hp k q f
    (hf ⟨q.val, q.property.1, dvd_mul_of_dvd_right q.property.2 p⟩ hqS)

#print axioms frickeOldLevel_div_eq_dilationLevel
#print axioms trace_mem_primeTraceKernel
#print axioms trace_mem_partialNewSpace

end AsymptoticClassicalCusp
