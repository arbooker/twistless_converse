module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticHeckeCuspIndicator

/-- Exactly one projective Hecke branch has first column divisible by p.
The extra term is the branch with first column (p*a,c). -/
theorem projective_indicator {p : ℕ} [Fact p.Prime] (a c : ZMod p)
    (h : a≠0 ∨ c≠0) :
    (if c=0 then 1 else 0)+(∑ j : ZMod p, if a+j*c=0 then 1 else 0 : ℕ)=1 := by
  classical
  by_cases hc : c=0
  · have ha : a≠0 := h.resolve_right (by simp only [hc,ne_eq,not_true_eq_false,not_false_eq_true])
    simp [hc,ha]
  · have he (j : ZMod p) : a+j*c=0 ↔ j= -a/c := by
      constructor
      · intro hj
        apply (eq_div_iff hc).mpr
        linear_combination hj
      · intro hj
        rw [hj,div_mul_cancel₀ _ hc]
        ring
    simp only [hc,ite_false,zero_add,he]
    simp

/-- The determinant-one hypothesis supplies the primitive first column. -/
theorem determinant_indicator {p : ℕ} [Fact p.Prime] (a b c d : ZMod p)
    (h : a*d-b*c=1) :
    (if c=0 then 1 else 0)+(∑ j : ZMod p, if a+j*c=0 then 1 else 0 : ℕ)=1 := by
  apply projective_indicator
  by_contra hn
  push Not at hn
  rcases hn with ⟨ha,hc⟩
  simp [ha,hc] at h

/-- The same count in the standard finite list of p translates. -/
theorem fin_indicator {p : ℕ} [Fact p.Prime] (a b c d : ZMod p)
    (h : a*d-b*c=1) :
    (if c=0 then 1 else 0)+
      (∑ j : Fin p, if a+(j.val:ZMod p)*c=0 then 1 else 0 : ℕ)=1 := by
  classical
  have hs := (ZMod.finEquiv p).toEquiv.sum_comp
    (fun j : ZMod p => if a+j*c=0 then (1:ℕ) else 0)
  have he : (∑ j : Fin p, if a+(j.val:ZMod p)*c=0 then 1 else 0 : ℕ)=
      ∑ j : ZMod p, if a+j*c=0 then 1 else 0 := by
    have hf (j : Fin p) : (ZMod.finEquiv p) j=(j.val:ZMod p) := by
      have hv : ((ZMod.finEquiv p) j).val=j.val := by
        cases p with
        | zero => exact Fin.elim0 j
        | succ n => rfl
      rw [← ZMod.natCast_zmod_val ((ZMod.finEquiv p) j),hv]
    change (∑ j : Fin p, if a+(ZMod.finEquiv p) j*c=0 then 1 else 0 : ℕ)=_ at hs
    simpa only [hf] using hs
  rw [he]
  exact determinant_indicator a b c d h

#print axioms projective_indicator
#print axioms determinant_indicator
#print axioms fin_indicator
end QuantitativeArithmeticHeckeCuspIndicator
