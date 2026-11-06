module

/- Addition in quotient/remainder coordinates and trace injection at all scales.
This uses an explicit finite sum, not an unspecified abstract addition map.
-/
public import SpanningActualKernelV1
public import SpanningCyclicCoordinatesV1

@[expose] public section

namespace SpanningSlicedAddition

open Finset SpanningTraceAlgebra SpanningActualKernel
variable {F : Type*} [AddCommMonoid F]

/-- The q interleaved residue classes, summed over the B-periodic trace. -/
def addition (q B : ℕ) (w : ℕ → ℤ → F) : ℤ → F := fun n =>
  ∑ a∈range q, w ((n+a*B)%(q:ℤ)).toNat ((n+a*B)/(q:ℤ))

theorem addition_slices {q : ℕ} (hq : 0<q) (B : ℕ) (v : ℤ → F) :
    addition q B (fun r => restrict q r v)=trace q B v := by
  funext n
  apply sum_congr rfl
  intro a _
  dsimp [SpanningTraceAlgebra.restrict]
  congr 1
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt hq))]
  exact Int.mul_ediv_add_emod _ _

/-- Kernel-zero form of injectivity on q copies of a space V. -/
def AdditionInjective (q B : ℕ) (V : Set (ℤ → F)) : Prop :=
  ∀ w : ℕ → ℤ → F, (∀ r<q, w r∈V) → addition q B w=0 → ∀ r<q, w r=0

theorem sliced_identity {q : ℕ} (hq : 0<q) (B m : ℕ) (s : ℤ) (v : ℤ → F) :
    addition q B (fun r => restrict (m*q) (m*r+s) v)=
      restrict m s (trace q (m*B) v) := by
  rw [←trace_restrict,←addition_slices hq]
  congr 1
  funext r
  exact (restrict_comp m q s r v).symm

theorem zero_of_trace {q m B : ℕ} (hq : 0<q) (hm : 0<m)
    {V : Set (ℤ → F)} (hinj : AdditionInjective q B V) {v : ℤ → F}
    (hslices : ∀ s<m, ∀ r<q, restrict (m*q) (m*r+s) v∈V)
    (hz : trace q (m*B) v=0) : v=0 := by
  apply zero_of_all_restrictions hm
  intro s hs
  apply zero_of_all_restrictions hq
  intro r hr
  have hw := hinj (fun r => restrict (m*q) (m*r+s) v) (hslices s hs)
    (by rw [sliced_identity hq,hz]; rfl) r hr
  simpa only [restrict_comp] using hw

theorem kernel_zero_of_trace {N q m B : ℕ} (hq : 0<q) (hm : 0<m)
    (hinj : AdditionInjective q B {v : ℤ → F | Kernel N B v})
    {v : ℤ → F} (hv : Kernel N (q*(m*B)) v) (hz : trace q (m*B) v=0) : v=0 := by
  apply zero_of_trace hq hm hinj (v:=v) _ hz
  intro s hs r hr
  have ht : m*r+s<m*q := by
    calc
      m*r+s<m*r+m := Nat.add_lt_add_left hs _
      _ = m*(r+1) := (Nat.mul_succ m r).symm
      _ ≤ m*q := Nat.mul_le_mul_left m hr
  have hv' : Kernel N ((m*q)*B) v := by simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hv
  exact kernel_restrict hv' ht

theorem augmented_zero_of_trace {N q m B : ℕ} {L : Set ℕ}
    (hq : 0<q) (hm : 0<m) (hdiv : ∀ ell∈L, ell∣B)
    (hinj : AdditionInjective q B {v : ℤ → F | Augmented N L B v})
    {v : ℤ → F} (hv : Augmented N L (q*(m*B)) v)
    (hz : trace q (m*B) v=0) : v=0 := by
  apply zero_of_trace hq hm hinj (v:=v) _ hz
  intro s hs r hr
  have ht : m*r+s<m*q := by
    calc
      m*r+s<m*r+m := Nat.add_lt_add_left hs _
      _ = m*(r+1) := (Nat.mul_succ m r).symm
      _ ≤ m*q := Nat.mul_le_mul_left m hr
  have hv' : Augmented N L ((m*q)*B) v := by
    simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hv
  exact augmented_restrict hdiv hv' ht

#print axioms addition_slices
#print axioms kernel_zero_of_trace
#print axioms augmented_zero_of_trace

end SpanningSlicedAddition
