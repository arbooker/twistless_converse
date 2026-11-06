module

public import QuantitativeMaassAutomorphicL2V1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace QuantitativeMaass.CosetTrace

variable {G α : Type*} [Group G] [MulAction G α]
    (H : Subgroup G) (f : α → ℂ)
    (hinv : ∀ h : H, ∀ x, f (h.val • x) = f x)

/-- The actual pullback attached to a left coset is independent of the
representative, using precisely H-automorphy of the function. -/
def value (q : G ⧸ H) (x : α) : ℂ :=
  Quotient.liftOn q (fun a : G => f (a⁻¹ • x)) (by
    intro a b hab
    have hh := hinv ⟨a⁻¹*b, QuotientGroup.leftRel_apply.mp hab⟩ (b⁻¹ • x)
    simpa only [mul_smul, smul_inv_smul] using hh)

theorem value_mk (a : G) (x : α) : value H f hinv (QuotientGroup.mk a) x = f (a⁻¹ • x) := rfl

theorem value_out (q : G ⧸ H) (x : α) : value H f hinv q x = f (q.out⁻¹ • x) := by
  conv_lhs => rw [← q.out_eq]
  rfl

theorem value_translate (g : G) (q : G ⧸ H) (x : α) :
    value H f hinv q (g • x) = value H f hinv (g⁻¹ • q) x := by
  induction q using Quotient.inductionOn with
  | h a =>
    change f (a⁻¹ • (g • x)) = f ((g⁻¹*a)⁻¹ • x)
    rw [mul_inv_rev, inv_inv, mul_smul]

variable [Fintype (G ⧸ H)]

/-- The unnormalized automorphic trace is a literal finite coset sum. -/
def trace (x : α) : ℂ := ∑ q : G ⧸ H, value H f hinv q x

theorem trace_invariant (g : G) (x : α) : trace H f hinv (g • x) = trace H f hinv x := by
  simp only [trace, value_translate]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun q : G ⧸ H => value H f hinv q x)

theorem trace_out (x : α) : trace H f hinv x = ∑ q : G ⧸ H, f (q.out⁻¹ • x) := by
  simp only [trace, value_out]

variable [MeasurableSpace α]

theorem trace_measurable (hact : ∀ g : G, Measurable (fun x : α => g • x))
    (hf : Measurable f) : Measurable (trace H f hinv) := by
  rw [show trace H f hinv = (fun x => ∑ q : G ⧸ H, f (q.out⁻¹ • x)) from
    funext (trace_out H f hinv)]
  exact Finset.measurable_sum _ (fun q _ => hf.comp (hact q.out⁻¹))

#print axioms value_out
#print axioms trace_invariant
#print axioms trace_measurable

end QuantitativeMaass.CosetTrace
