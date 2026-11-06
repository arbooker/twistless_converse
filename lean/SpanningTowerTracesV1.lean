module

public import SpanningFiniteDimensionsV1

@[expose] public section

namespace SpanningTowerTraces

open SpanningTraceAlgebra SpanningActualKernel SpanningSlicedAddition
open SpanningLinearKernels SpanningFiniteDimensions
variable {K : Type*} [Field K]

def UniformTraceInjective (N : ℕ) (L : Set ℕ) (B p : ℕ) : Prop :=
  ∀m:ℕ,0<m → ∀v:ℤ → K,Augmented N L (p*(m*B)) v → trace p (m*B) v=0 → v=0

theorem uniform_one (N B : ℕ) (L : Set ℕ) : UniformTraceInjective (K:=K) N L B 1 := by
  intro m _ v _ hz
  funext j
  have hh := congrFun hz j
  simpa [SpanningTraceAlgebra.trace] using hh

theorem uniform_from_addition {N B p : ℕ} {L : Set ℕ}
    (hp : 0<p) (hdiv : ∀ell∈L,ell∣B)
    (hi : AdditionInjective p B {v:ℤ → K | Augmented N L B v}) :
    UniformTraceInjective (K:=K) N L B p := by
  intro m hm v hv hz
  exact augmented_zero_of_trace hp hm hdiv hi hv hz

theorem uniform_mul {N B p q : ℕ} {L : Set ℕ}
    (hp : 0<p) (hq : 0<q) (hNp : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣B)
    (hip : UniformTraceInjective (K:=K) N L B p)
    (hiq : UniformTraceInjective (K:=K) N L B q) :
    UniformTraceInjective (K:=K) N L B (p*q) := by
  intro m hm v hv hz
  have hv' : Augmented N L (p*(q*(m*B))) v := by simpa [Nat.mul_assoc] using hv
  have ht : Augmented N L (q*(m*B)) (trace p (q*(m*B)) v) :=
    augmented_trace hp hNp (fun ell hell =>
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hdiv ell hell) m) q) hv'
  have hz' : trace p (q*(m*B)) v=0 := hiq m hm _ ht (by rw [trace_comp]; exact hz)
  apply hip (q*m) (Nat.mul_pos hq hm) v
  · simpa [Nat.mul_assoc] using hv'
  · simpa [Nat.mul_assoc] using hz'

theorem uniform_pow {N B p : ℕ} {L : Set ℕ}
    (hp : 0<p) (hNp : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣B)
    (hi : UniformTraceInjective (K:=K) N L B p) (a : ℕ) :
    UniformTraceInjective (K:=K) N L B (p^a) := by
  induction a with
  | zero => exact uniform_one N B L
  | succ a ih =>
    rw [pow_succ']
    exact uniform_mul hp (pow_pos hp _) hNp hdiv hi ih

theorem uniform_two_powers {N B c d : ℕ} {L : Set ℕ}
    (hc : 0<c) (hd : 0<d) (hcN : Nat.Coprime N c) (hdN : Nat.Coprime N d)
    (hdiv : ∀ell∈L,ell∣B)
    (hci : AdditionInjective c B {v:ℤ → K | Augmented N L B v})
    (hdi : AdditionInjective d B {v:ℤ → K | Augmented N L B v}) (a b : ℕ) :
    UniformTraceInjective (K:=K) N L B (c^a*d^b) := by
  apply uniform_mul (pow_pos hc _) (pow_pos hd _) (hcN.pow_right a) hdiv
  · exact uniform_pow hc hcN hdiv (uniform_from_addition hc hdiv hci) a
  · exact uniform_pow hd hdN hdiv (uniform_from_addition hd hdiv hdi) b

theorem trace_injective {N B p m : ℕ} {L : Set ℕ}
    (hp : 0<p) (hm : 0<m) (hNp : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣B)
    (hi : UniformTraceInjective (K:=K) N L B p) :
    Function.Injective (traceOnAugmented (K:=K) hp hNp
      (fun ell hell => dvd_mul_of_dvd_right (hdiv ell hell) m)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply Subtype.ext
  exact hi m hm v.val v.property (congrArg Subtype.val hv)

noncomputable def cumulativeTraceIso {N B p m : ℕ} {L : Set ℕ}
    (hp : 0<p) (hm : 0<m) (hB : 0<B) (hNp : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣B)
    (hi : UniformTraceInjective (K:=K) N L B p)
    (heq : dimension (K:=K) N L (p*(m*B))=dimension (K:=K) N L (m*B)) :
    augmentedSubmodule (K:=K) N L (p*(m*B)) ≃ₗ[K] augmentedSubmodule (K:=K) N L (m*B) := by
  letI : NeZero (m*B) := ⟨Nat.ne_of_gt (Nat.mul_pos hm hB)⟩
  letI : NeZero (p*(m*B)) := ⟨Nat.ne_of_gt (Nat.mul_pos hp (Nat.mul_pos hm hB))⟩
  let T := traceOnAugmented (K:=K) hp hNp (fun ell hell => dvd_mul_of_dvd_right (hdiv ell hell) m)
  have hinj : Function.Injective T := trace_injective hp hm hNp hdiv hi
  exact LinearEquiv.ofBijective T ⟨hinj,surjective_of_injective_equal_dimension T hinj heq⟩

@[simp] theorem cumulativeTraceIso_apply {N B p m : ℕ} {L : Set ℕ}
    (hp : 0<p) (hm : 0<m) (hB : 0<B) (hNp : Nat.Coprime N p) (hdiv : ∀ell∈L,ell∣B)
    (hi : UniformTraceInjective (K:=K) N L B p)
    (heq : dimension (K:=K) N L (p*(m*B))=dimension (K:=K) N L (m*B))
    (v : augmentedSubmodule (K:=K) N L (p*(m*B))) :
    (cumulativeTraceIso hp hm hB hNp hdiv hi heq v).val=trace p (m*B) v.val := rfl

#print axioms uniform_two_powers
#print axioms cumulativeTraceIso

end SpanningTowerTraces
