module

/- The open, upper-buffered row window, abstracted only over its radius.
The intended radius is Q/sqrt(lcm(N,q^2)). No endpoint is closed here. -/
public import SpanningTraceAlgebraV1
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

namespace SpanningWindows

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

def Legal (radius : R) (u : ℤ) : Prop := -radius<(u:R) ∧ (u:R)+1<radius

theorem legal_mono {r s : R} {u : ℤ} (hrs : r≤s) (hu : Legal r u) : Legal s u := by
  rcases hu with ⟨h1,h2⟩
  constructor <;> linarith

theorem legal_scale {r : R} {u : ℤ} (hu : Legal r u)
    {m t : ℕ} (ht : t<m) : Legal ((m:R)*r) ((m:ℤ)*u+t) := by
  rcases hu with ⟨h1,h2⟩
  have hm : (0:R)<m := by exact_mod_cast (show 0<m by omega)
  have ht0 : (0:R)≤t := Nat.cast_nonneg t
  have htm : (t:R)+1≤m := by exact_mod_cast (show t+1≤m by omega)
  constructor <;> push_cast <;> nlinarith

theorem legal_shift {r : R} {u : ℤ} (hu : Legal r u) {s : ℕ}
    (hupper : (u:R)+s+1<r) : Legal r (u+s) := by
  rcases hu with ⟨h1,_⟩
  have hs : (0:R)≤s := Nat.cast_nonneg s
  constructor <;> push_cast <;> linarith

theorem legal_interval {r : R} {L : ℕ} (hL : (L:R)<r) {u : ℤ}
    (hlo : -(L:ℤ)≤u) (hhi : u<(L:ℤ)) : Legal r u := by
  have h1 : -(L:R)≤(u:R) := by exact_mod_cast hlo
  have h2 : (u:R)+1≤L := by exact_mod_cast (show u+1≤(L:ℤ) by omega)
  constructor <;> linarith

open SpanningTraceAlgebra
variable {F : Type*} [AddCommMonoid F]

def PrimitiveKernel (radius : ℕ → ℕ → R) (Q : ℕ) (v : ℤ → F) : Prop :=
  Cyclic Q v ∧ ∀ q, q∣Q → ∀ u, Legal (radius Q q) u → primitive q (Q/q) v u=0

def CompleteKernel (radius : ℕ → ℕ → R) (Q : ℕ) (v : ℤ → F) : Prop :=
  Cyclic Q v ∧ ∀ q, q∣Q → ∀ u, Legal (radius Q q) u → trace q (Q/q) v u=0

theorem primitive_kernel_restrict {radius : ℕ → ℕ → R} {m Q t : ℕ}
    (hscale : ∀ q, q∣Q → radius (m*Q) q=(m:R)*radius Q q)
    {v : ℤ → F} (hv : PrimitiveKernel radius (m*Q) v) (ht : t<m) :
    PrimitiveKernel radius Q (restrict m t v) := by
  refine ⟨restrict_cyclic hv.1 t,?_⟩
  intro q hq u hu
  have hleg := legal_scale hu ht
  rw [← hscale q hq] at hleg
  have hh := hv.2 q (dvd_mul_of_dvd_right hq m) ((m:ℤ)*u+t) hleg
  rw [primitive_restrict]
  rw [Nat.mul_div_assoc m hq] at hh
  exact hh

theorem complete_kernel_restrict {radius : ℕ → ℕ → R} {m Q t : ℕ}
    (hscale : ∀ q, q∣Q → radius (m*Q) q=(m:R)*radius Q q)
    {v : ℤ → F} (hv : CompleteKernel radius (m*Q) v) (ht : t<m) :
    CompleteKernel radius Q (restrict m t v) := by
  refine ⟨restrict_cyclic hv.1 t,?_⟩
  intro q hq u hu
  have hleg := legal_scale hu ht
  rw [← hscale q hq] at hleg
  have hh := hv.2 q (dvd_mul_of_dvd_right hq m) ((m:ℤ)*u+t) hleg
  rw [complete_restrict]
  rw [Nat.mul_div_assoc m hq] at hh
  exact hh

theorem primitive_kernel_zero_at_multiples {radius : ℕ → ℕ → R} {m Q : ℕ}
    (hm : 0<m) (hscale : ∀ q, q∣Q → radius (m*Q) q=(m:R)*radius Q q)
    (hzero : ∀ v : ℤ → F, PrimitiveKernel radius Q v → v=0) :
    ∀ v : ℤ → F, PrimitiveKernel radius (m*Q) v → v=0 := by
  intro v hv
  apply zero_of_all_restrictions hm
  intro t ht
  exact hzero _ (primitive_kernel_restrict hscale hv ht)

#print axioms legal_scale
#print axioms primitive_kernel_restrict
#print axioms primitive_kernel_zero_at_multiples

omit [IsStrictOrderedRing R] in
theorem complete_kernel_trace {radius : ℕ → ℕ → R} {p Q : ℕ}
    (hp : 0<p) (hradius : ∀ q, q∣Q → radius (p*Q) (p*q)=radius Q q)
    {v : ℤ → F} (hv : CompleteKernel radius (p*Q) v) :
    CompleteKernel radius Q (trace p Q v) := by
  refine ⟨trace_cyclic hv.1,?_⟩
  intro q hq u hu
  have hQ : q*(Q/q)=Q := Nat.mul_div_cancel' hq
  have he : trace q (Q/q) (trace p Q v)=trace (p*q) (Q/q) v := by
    simpa only [hQ] using trace_comp p q (Q/q) v
  have hleg : Legal (radius (p*Q) (p*q)) u := by rw [hradius q hq]; exact hu
  have hh := hv.2 (p*q) (Nat.mul_dvd_mul_left p hq) u hleg
  rw [Nat.mul_div_mul_left Q q hp] at hh
  rw [he]
  exact hh

def AugmentedKernel (radius : ℕ → ℕ → R) (L : Set ℕ) (Q : ℕ) (v : ℤ → F) : Prop :=
  CompleteKernel radius Q v ∧ ∀ ell∈L, trace ell (Q/ell) v=0

theorem augmented_kernel_restrict {radius : ℕ → ℕ → R} {L : Set ℕ} {m Q t : ℕ}
    (hscale : ∀ q, q∣Q → radius (m*Q) q=(m:R)*radius Q q)
    (hdiv : ∀ ell∈L, ell∣Q)
    {v : ℤ → F} (hv : AugmentedKernel radius L (m*Q) v) (ht : t<m) :
    AugmentedKernel radius L Q (restrict m t v) := by
  refine ⟨complete_kernel_restrict hscale hv.1 ht,?_⟩
  intro ell hell
  have he := hv.2 ell hell
  rw [Nat.mul_div_assoc m (hdiv ell hell)] at he
  rw [trace_restrict,he]
  rfl

omit [IsStrictOrderedRing R] in
theorem augmented_kernel_trace {radius : ℕ → ℕ → R} {L : Set ℕ} {p Q : ℕ}
    (hp : 0<p) (hradius : ∀ q, q∣Q → radius (p*Q) (p*q)=radius Q q)
    (hdiv : ∀ ell∈L, ell∣Q) {v : ℤ → F}
    (hv : AugmentedKernel radius L (p*Q) v) :
    AugmentedKernel radius L Q (trace p Q v) := by
  refine ⟨complete_kernel_trace hp hradius hv.1,?_⟩
  intro ell hell
  have hQ : ell*(Q/ell)=Q := Nat.mul_div_cancel' (hdiv ell hell)
  have hcomm : trace ell (Q/ell) (trace p Q v)=
      trace p (Q/ell) (trace ell (p*(Q/ell)) v) := by
    simpa only [hQ] using trace_comm p ell (Q/ell) v
  have he := hv.2 ell hell
  rw [Nat.mul_div_assoc p (hdiv ell hell)] at he
  rw [hcomm,he]
  funext j
  simp [trace]

#print axioms complete_kernel_trace
#print axioms augmented_kernel_restrict
#print axioms augmented_kernel_trace

end SpanningWindows
