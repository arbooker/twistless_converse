module

public import QuantitativeMaassRamanujanPhaseV1
public import AsymptoticRamifiedFourierV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open FinitenessRamanujanSum FinitenessRamanujanDivisor
open scoped ComplexConjugate

/-- Full translation averaging of either Maass parity extracts precisely
frequencies divisible by the averaging modulus. -/
theorem eulerParityPhase_complete {p : ℕ} (hp : 0<p) (n σ : ℕ) (x : ℝ) :
    (∑ a∈Finset.range p,eulerParityPhase σ n ((x+(a:ℝ))/p))=
      (if p∣n then (p:ℂ) else 0)*eulerParityPhase σ n (x/p) := by
  simp_rw [show ∀ a : ℕ,(x+(a:ℝ))/p=x/p+(a:ℝ)/p by intro a;ring]
  simp_rw [eulerParityPhase,eulerPhase_translate_positive,eulerPhase_translate_negative]
  rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,←Finset.sum_mul,←map_sum]
  change complete p n*Complex.exp (((2*Real.pi*(n:ℝ)*(x/p):ℝ):ℂ)*Complex.I)+
      (-1:ℂ)^σ*(conj (complete p n)*Complex.exp (-(((2*Real.pi*(n:ℝ)*(x/p):ℝ):ℂ)*Complex.I)))=_
  rw [complete_eval hp]
  split_ifs <;> simp only [map_natCast,map_zero] <;> ring

/-- Natural indexing with its zero-frequency term explicitly removed. -/
def principalEulerTermNat (b : ℕ→ℂ) (r : ℝ) (σ n : ℕ) (z : ℝ×ℝ) : ℂ :=
  if n=0 then 0 else b n*(MaassKBessel.moment 0 r (2*Real.pi*(n:ℝ)*z.2):ℂ)*
    eulerParityPhase σ n z.1

theorem principalEulerTermNat_succ (b : ℕ→ℂ) (r : ℝ) (σ n : ℕ) (z : ℝ×ℝ) :
    principalEulerTermNat b r σ (n+1) z=principalEulerTerm b r σ n z := by
  simp [principalEulerTermNat,principalEulerTerm]

theorem principalEulerCore_nat (b : ℕ→ℂ) (r : ℝ) (σ : ℕ) (z : ℝ×ℝ) :
    principalEulerCore b r σ z=∑' n,principalEulerTermNat b r σ n z := by
  rw [←tsum_pnat_eq_tsum_of_eq_zero (show principalEulerTermNat b r σ 0 z=0 by simp [principalEulerTermNat]),
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => principalEulerTermNat b r σ n z)]
  simp only [principalEulerTermNat_succ,principalEulerCore]

theorem principalEulerTermNat_summable {b : ℕ→ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (z : ℝ×ℝ) (hz : 0<z.2) :
    Summable (fun n => principalEulerTermNat b r σ n z) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [principalEulerTermNat_succ] using principalEulerTerm_summable hb r σ z hz

#print axioms eulerParityPhase_complete
#print axioms principalEulerCore_nat
#print axioms principalEulerTermNat_summable
end QuantitativeMaass
