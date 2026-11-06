module

public import SpanningFiniteDimensionsV1

@[expose] public section

namespace SpanningTraceRemoval

open SpanningActualKernel SpanningTraceAlgebra SpanningLinearKernels SpanningFiniteDimensions

variable {K : Type*} [Field K]

theorem augmented_zero_at_multiples {N Q m : ℕ} {L : Set ℕ} (hm : 0<m)
    (hdiv : ∀ell∈L,ell∣Q) (hz : ∀f:ℤ → K,Augmented N L Q f → f=0) :
    ∀f:ℤ → K,Augmented N L (m*Q) f → f=0 := by
  intro f hf
  apply zero_of_all_restrictions hm
  intro t ht
  exact hz _ (augmented_restrict hdiv hf ht)

theorem insert_trace_zero {N Q p : ℕ} {L : Set ℕ} (hp : 0<p) {f : ℤ → K}
    (hf : Augmented N L (p*Q) f) (ht : trace p Q f=0) :
    Augmented N (insert p L) (p*Q) f := by
  refine ⟨hf.1,?_⟩
  intro ell hell
  rcases Set.mem_insert_iff.mp hell with he|he
  · subst ell
    simpa only [Nat.mul_div_cancel_left Q hp] using ht
  · exact hf.2 ell he

theorem trace_injective_after_insertion {N Q p : ℕ} {L : Set ℕ}
    (hp : 0<p) (hc : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣Q)
    (hz : ∀f:ℤ → K,Augmented N (insert p L) (p*Q) f → f=0) :
    Function.Injective (traceOnAugmented (K:=K) hp hc hdiv) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply Subtype.ext
  apply hz
  exact insert_trace_zero hp f.property (congrArg Subtype.val hf)

theorem bounded_axis_after_insertion {N B p : ℕ} {L : Set ℕ}
    (hB : 0<B) (hp : 0<p) (hc : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣B)
    (hz : ∀m:ℕ,0<m → ∀f:ℤ → K,Augmented N (insert p L) (m*B) f → f=0) :
    ∀a:ℕ,dimension (K:=K) N L (B*p^a)≤dimension (K:=K) N L B := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hQ : 0<B*p^a := Nat.mul_pos hB (pow_pos hp _)
    let : NeZero (B*p^a) := ⟨Nat.ne_of_gt hQ⟩
    have hi := trace_injective_after_insertion hp hc
      (fun ell hell => (hdiv ell hell).trans (dvd_mul_right B _)) (Q:=B*p^a) (by
        intro f hf
        have he : p*(B*p^a)=p^(a+1)*B := by rw [pow_succ]; ring
        apply hz (p^(a+1)) (pow_pos hp _) f
        simpa only [he] using hf)
    have hd := LinearMap.finrank_le_finrank_of_injective hi
    have he : p*(B*p^a)=B*p^(a+1) := by rw [pow_succ]; ring
    change dimension (K:=K) N L (p*(B*p^a))≤dimension (K:=K) N L (B*p^a) at hd
    rw [he] at hd
    exact hd.trans ih

#print axioms bounded_axis_after_insertion

end SpanningTraceRemoval
