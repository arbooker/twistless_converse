module

public import GridBufferedDetectionV1

@[expose] public section

namespace SpanningKernelDifferences

open SpanningTraceAlgebra SpanningWindows SpanningActualKernel SpanningCyclicCoordinates
  GridBufferedDetection GridSupportedDetection GridCarrier GridAdmissibleGap

variable {K : Type} [AddCommGroup K]

def difference (P : ℕ) (f : ℤ → K) : ℤ → K := fun j => f (j+P)-f j

theorem difference_cyclic {P Q : ℕ} {f : ℤ → K} (hf : Cyclic Q f) :
    Cyclic Q (difference P f) := by
  intro j
  simp only [difference]
  rw [show j+(Q:ℤ)+P=j+P+Q by ring,hf,hf]

theorem trace_difference (P q D : ℕ) (f : ℤ → K) (u : ℤ) :
    trace q D (difference P f) u=trace q D f (u+P)-trace q D f u := by
  unfold trace difference
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  ring

theorem difference_buffered {N Q P : ℕ} {b : ℝ} {f : ℤ → K}
    (hf : CompleteKernel (radius N) Q f) (hP : (P:ℝ)<b) :
    BufferedZero N Q b (difference P f) := by
  intro q _ hq u hu hb
  have huP : Legal (radius N Q q) (u+P) := legal_shift hu (by linarith)
  rw [trace_difference,hf.2 q hq _ huP,hf.2 q hq _ hu,sub_self]

theorem difference_zero_iff (P : ℕ) (f : ℤ → K) : difference P f=0 ↔ Cyclic P f := by
  constructor
  · intro h j
    exact sub_eq_zero.mp (congrFun h j)
  · intro h
    funext j
    exact sub_eq_zero.mpr (h j)

theorem small_period_kernel_zero {N Q P : ℕ} (hP : 0<P) {f : ℤ → K}
    (hf : CompleteKernel (radius N) Q f) (hperiod : Cyclic P f)
    (hsize : (P:ℝ)<radius N Q 1) : f=0 := by
  have hz : ∀j:ℤ,0≤j → j<P → f j=0 := by
    intro j hj hjP
    have hleg := legal_interval hsize (by omega : -(P:ℤ)≤j) hjP
    have hh := hf.2 1 (one_dvd Q) j hleg
    simpa [trace] using hh
  funext j
  change f j=0
  rw [←cyclic_emod hperiod j]
  exact hz _ (Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt hP))
    (Int.emod_lt_of_pos _ (by exact_mod_cast hP))

#print axioms difference_buffered
#print axioms small_period_kernel_zero

end SpanningKernelDifferences
