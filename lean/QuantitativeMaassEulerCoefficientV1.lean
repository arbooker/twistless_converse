module

public import QuantitativeMaassFourierCharactersV1
public import QuantitativeMaassEulerFourierV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

theorem principalEulerTerm_coefficient (b : ℕ → ℂ) (r : ℝ) (σ n m : ℕ)
    (hm : 0<m) (y : ℝ) :
    (∫ x in Ioc (0:ℝ) 1,eulerCharacter (-(m:ℤ)) x*principalEulerTerm b r σ n (x,y))=
      b (n+1)*(MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y):ℂ)*(if n+1=m then 1 else 0) := by
  have he : (fun x => eulerCharacter (-(m:ℤ)) x*principalEulerTerm b r σ n (x,y))=
      fun x => (b (n+1)*(MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y):ℂ))*
        (eulerCharacter (-(m:ℤ)) x*eulerParityPhase σ (n+1) x) := by
    funext x
    unfold principalEulerTerm
    dsimp only
    ring
  rw [he,integral_const_mul,eulerParityPhase_character_integral σ (n+1) m (by omega) hm]

/-- Coefficient integration commutes with the actual Fourier--Bessel series,
by the explicit summable uniform bounds on a fixed positive-height line. -/
theorem principalEulerCore_coefficient_hasSum {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ m : ℕ) (y : ℝ) (hy : 0<y) :
    HasSum (fun n => ∫ x in Ioc (0:ℝ) 1,eulerCharacter (-(m:ℤ)) x*principalEulerTerm b r σ n (x,y))
      (∫ x in Ioc (0:ℝ) 1,eulerCharacter (-(m:ℤ)) x*principalEulerCore b r σ (x,y)) := by
  apply hasSum_integral_of_dominated_convergence
    (bound:=fun n (_ : ℝ) => 2*principalMomentMajorant b 0 0 (2*Real.pi) y n)
  · intro n
    have hc : Continuous (fun x => eulerCharacter (-(m:ℤ)) x*principalEulerTerm b r σ n (x,y)) := by
      unfold principalEulerTerm
      dsimp only
      exact (eulerCharacter_continuous _).mul
        (continuous_const.mul (eulerParityPhase_continuous σ (n+1)))
    exact hc.aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall (fun x => by
      rw [norm_mul,eulerCharacter_norm,one_mul]
      exact principalEulerTerm_bound b r σ n y hy (x,y) le_rfl)
  · exact Filter.Eventually.of_forall (fun _ =>
      (principalMomentMajorant_summable hb 0 0 (2*Real.pi) y (by positivity) hy).mul_left 2)
  · exact continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact Filter.Eventually.of_forall (fun x =>
      (principalEulerTerm_summable hb r σ (x,y) hy).hasSum.mul_left (eulerCharacter (-(m:ℤ)) x))

/-- The positive Fourier coefficient is exactly the original coefficient times
the actual Bessel factor; no abstract reconstruction map is substituted. -/
theorem principalEulerCore_coefficient {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ n : ℕ) (y : ℝ) (hy : 0<y) :
    (∫ x in Ioc (0:ℝ) 1,eulerCharacter (-((n+1:ℕ):ℤ)) x*principalEulerCore b r σ (x,y))=
      b (n+1)*(MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y):ℂ) := by
  rw [←(principalEulerCore_coefficient_hasSum hb r σ (n+1) y hy).tsum_eq]
  simp_rw [principalEulerTerm_coefficient b r σ _ (n+1) (by omega) y]
  simp

theorem principalEulerWave_coefficient {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ n : ℕ) (y : ℝ) (hy : 0<y) :
    (∫ x in Ioc (0:ℝ) 1,eulerCharacter (-((n+1:ℕ):ℤ)) x*principalEulerWave b r σ (x,y))=
      (Real.sqrt y:ℂ)*(b (n+1)*(MaassKBessel.moment 0 r (2*Real.pi*((n+1:ℕ):ℝ)*y):ℂ)) := by
  have he : (fun x => eulerCharacter (-((n+1:ℕ):ℤ)) x*principalEulerWave b r σ (x,y))=
      fun x => (Real.sqrt y:ℂ)*(eulerCharacter (-((n+1:ℕ):ℤ)) x*principalEulerCore b r σ (x,y)) := by
    funext x
    unfold principalEulerWave
    dsimp only
    ring
  rw [he,integral_const_mul,principalEulerCore_coefficient hb r σ n y hy]

#print axioms principalEulerTerm_coefficient
#print axioms principalEulerCore_coefficient_hasSum
#print axioms principalEulerCore_coefficient
#print axioms principalEulerWave_coefficient

end QuantitativeMaass
