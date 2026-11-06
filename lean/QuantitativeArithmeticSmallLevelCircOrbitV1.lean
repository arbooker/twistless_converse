module

public import QuantitativeArithmeticSmallLevelCircV1
public import QuantitativeEulerOldProjectionHolomorphicPhaseV1
public import AsymptoticAtkinLehnerOldTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane Matrix AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticSlashGauge QuantitativeEulerOldProjectionHolomorphic
open AsymptoticClassicalPetersson AsymptoticFreshMatrices AsymptoticOrbitDecode
open scoped ModularForm MatrixGroups

/-- The phase-corrected weighted orbit of an actual holomorphic function.
This is an ordinary function on the rational group, with no L² premise. -/
def orbit (m : ℕ) (F : ℍ → ℂ) (z : ℍ) (g : AsymptoticRationalGroup.Group) : ℂ :=
  phase g m z * weighted ((2*m : ℕ) : ℤ) F (g • z)

theorem orbit_one (m : ℕ) (F : ℍ → ℂ) (z : ℍ) :
    orbit m F z 1 = weighted ((2*m : ℕ) : ℤ) F z := by
  simp only [orbit, phase_one, one_smul, one_mul]

theorem orbit_mul (m : ℕ) (F : ℍ → ℂ) (z : ℍ)
    (g h : AsymptoticRationalGroup.Group) :
    orbit m F z (g*h) = phase h m z * orbit m F (h • z) g := by
  simp only [orbit, phase_mul, mul_smul]
  ring

theorem orbit_integral (m : ℕ) (F : ℍ → ℂ) (z : ℍ) (A : SL(2,ℤ)) :
    orbit m F z (integralLabel A) =
      (z.im : ℂ)^m * (F ∣[((2*m : ℕ) : ℤ)] A) z := by
  rw [orbit, phase_integralLabel, integralLabel_action]
  have hh := weighted_slash_det_one (SpecialLinearGroup.mapGL ℝ A) (by simp) m F z
  simp only [weighted_even] at hh ⊢
  simpa [ModularForm.SL_slash, MulAction.compHom_smul_def, SpecialLinearGroup.mapGL] using hh

/-- Modularity gives the exact left congruence invariance required by
existing algebraic trace identities. -/
theorem orbit_gamma (N m : ℕ) (F : ModularForm (level N) ((2*m : ℕ) : ℤ))
    (z : ℍ) (a : gamma N) (g : AsymptoticRationalGroup.Group) :
    orbit m F z (a.val*g) = orbit m F z g := by
  obtain ⟨A, hA, he⟩ := a.property
  rw [orbit_mul, ← he, orbit_integral]
  have hs : (F : ℍ → ℂ) ∣[((2*m : ℕ) : ℤ)] A = F :=
    F.slash_action_eq' _ ⟨A, hA, rfl⟩
  rw [hs]
  rw [orbit, weighted_even]

/-- A concrete rational representative computes the weighted orbit
without any arbitrary projective representative remaining. -/
theorem orbit_ofMatrix (m : ℕ) (F : ℍ → ℂ) (z : ℍ)
    (R : GL (Fin 2) ℚ) (hR : 0 < (realMatrix R).det.val) :
    orbit m F z (ofMatrix R hR) =
      AsymptoticHyperbolicSlash.phase (realMatrix R) (2*m) z *
        weighted ((2*m : ℕ) : ℤ) F (realMatrix R • z) := by
  have hp : phase (ofMatrix R hR) m z =
      AsymptoticHyperbolicSlash.phase (realMatrix R) (2*m) z := by
    apply phase_projective_eq
    change rationalMap (representative (ofMatrix R hR)) = rationalMap R
    rw [representative_spec]
    rfl
  rw [orbit, hp, ofMatrix_action]

/-- The existing algebraic simple-prime trace identity applies to the
actual weighted orbit; cancellation of the nonzero y^m yields the honest
sum of classical slash transforms. The only pending inputs here are the
explicit Fricke and ramified orbit laws. -/
theorem simple_trace_slash_zero (M p m : ℕ) [Fact p.Prime]
    (hM : 0 < M) (hpM : ¬ p ∣ M) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1)
    (F : ModularForm (level (p*M)) ((2*m : ℕ) : ℤ))
    (w δ : ℂ) (hδ : δ^2=1)
    (hW : ∀ z g, w * orbit m F z
      (frickeLabel (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)*g) = orbit m F z g)
    (hU : ∀ z g, (∑ a : Fin p, orbit m F z
      (ramifiedLabel p (Fact.out : p.Prime).pos a*g)) = δ * orbit m F z g) :
    (F : ℍ → ℂ) + ∑ a : Fin p,
      (F : ℍ → ℂ) ∣[((2*m : ℕ) : ℤ)] AsymptoticAtkinLehner.traceSL M p A B hAB a.val = 0 := by
  funext z
  have hh := AsymptoticAtkinLehner.old_trace_zero M p hM hpM A B hAB
    (orbit m F z) (orbit_gamma (p*M) m F z) w δ hδ (hW z) (hU z) 1
  simp only [mul_one, orbit_one, orbit_integral, weighted_even, ← Finset.mul_sum] at hh
  have hz : (z.im : ℂ)^m ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr z.im_pos.ne')
  have ht : (z.im : ℂ)^m *
      (F z + ∑ a : Fin p, ((F : ℍ → ℂ) ∣[((2*m : ℕ) : ℤ)]
        AsymptoticAtkinLehner.traceSL M p A B hAB a.val) z) = 0 := by
    rw [mul_add]
    exact hh
  simpa only [Pi.add_apply, Finset.sum_apply, Pi.zero_apply] using
    (mul_eq_zero.mp ht).resolve_left hz

#print axioms orbit_gamma
#print axioms orbit_ofMatrix
#print axioms simple_trace_slash_zero
end QuantitativeArithmeticSmallLevelCirc
