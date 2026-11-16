module

public import QuantitativeMaassCompositeTwistsV1
public import QuantitativeMaassRamifiedPowerAveragesV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

theorem analytic_twist_periodic (F : ℂ → ℂ) (hF : Function.Periodic F 1) (q : ℕ) :
    Function.Periodic (FinitenessAnalyticReconstruction.twist F q) 1 := by
  intro z
  unfold FinitenessAnalyticReconstruction.twist
  apply Finset.sum_congr rfl
  intro a _
  rw [add_right_comm z 1,hF]

theorem analytic_twist_commute (F : ℂ → ℂ) (m n : ℕ) (z : ℂ) :
    FinitenessAnalyticReconstruction.twist
      (FinitenessAnalyticReconstruction.twist F n) m z=
    FinitenessAnalyticReconstruction.twist
      (FinitenessAnalyticReconstruction.twist F m) n z := by
  classical
  unfold FinitenessAnalyticReconstruction.twist
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [add_right_comm]

theorem analytic_twist_dilation (F : ℂ → ℂ) (hF : Function.Periodic F 1)
    (p q : ℕ) (hq : 0<q) (hc : p.Coprime q) (z : ℂ) :
    FinitenessAnalyticReconstruction.twist (fun y => F ((p:ℂ)*y)) q z=
      FinitenessAnalyticReconstruction.twist F q ((p:ℂ)*z) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let e := Equiv.mulLeft (ZMod.unitOfCoprime p hc)
  have ht (a : (ZMod q)ˣ) :
      F ((p:ℂ)*(z+((a:ZMod q).val:ℂ)/q))=
        F ((p:ℂ)*z+((e a:ZMod q).val:ℂ)/q) := by
    have hh := periodic_fraction_congr F hF q hq
      ((p:ℤ)*(a:ZMod q).val) ((e a:ZMod q).val:ℤ)
      (by simp [e]) ((p:ℂ)*z)
    push_cast at hh
    convert hh using 1
    congr 1
    ring
  rw [analytic_twist_units,analytic_twist_units]
  simp_rw [ht]
  exact Equiv.sum_comp e (fun a : (ZMod q)ˣ => F ((p:ℂ)*z+((a:ZMod q).val:ℂ)/q))

theorem analytic_twist_ramified (F : ℂ → ℂ) (hF : Function.Periodic F 1)
    (p q : ℕ) (hp : 0<p) (hq : 0<q) (hc : p.Coprime q) (δ : ℂ)
    (hU : ∀ z,ramifiedAverage p F z=δ*F z) (z : ℂ) :
    ramifiedAverage p (FinitenessAnalyticReconstruction.twist F q) z=
      δ*FinitenessAnalyticReconstruction.twist F q z := by
  classical
  have hpC : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  have hs (y : ℂ) : (∑ a : Fin p,F (y+(a.val:ℂ)/p))=δ*F ((p:ℂ)*y) := by
    have hh := hU ((p:ℂ)*y)
    unfold ramifiedAverage at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    field_simp
  have he (y : ℂ) :
      (∑ a : Fin p,FinitenessAnalyticReconstruction.twist F q (y+(a.val:ℂ)/p))=
        δ*FinitenessAnalyticReconstruction.twist F q ((p:ℂ)*y) := by
    calc
      _ = FinitenessAnalyticReconstruction.twist
          (fun t => ∑ a : Fin p,F (t+(a.val:ℂ)/p)) q y := by
        unfold FinitenessAnalyticReconstruction.twist
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro a _
        rw [add_right_comm]
      _ = δ*FinitenessAnalyticReconstruction.twist
          (fun t => F ((p:ℂ)*t)) q y := by
        unfold FinitenessAnalyticReconstruction.twist
        simp_rw [hs]
        exact (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [analytic_twist_dilation F hF p q hq hc]
  have hh := he (z/(p:ℂ))
  rw [mul_div_cancel₀ z hpC] at hh
  simpa only [ramifiedAverage,add_div] using hh

#print axioms analytic_twist_periodic
#print axioms analytic_twist_commute
#print axioms analytic_twist_dilation
#print axioms analytic_twist_ramified

end QuantitativeMaass
