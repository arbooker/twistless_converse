module

public import QuantitativeArithmeticSmallLevelCircRepeatedV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane Matrix FinitenessOriginalInput SmallLevelOriginal
open AsymptoticFreshMatrices AsymptoticOrbitDecode
open scoped ModularForm

theorem original_factor_trace (M p m : ℕ) (hM : 0<M) (hp : p.Prime) (hm : 0<m)
    {f : ℕ → ℂ} (hf : IsSolution (p*M) (2*m) f)
    (F : ModularForm (level (p*M)) ((2*m : ℕ) : ℤ))
    (hF : (F : ℍ → ℂ) = fourierFunction (2*m) f) :
    (by
      let : NeZero M := ⟨hM.ne'⟩
      let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
      let : (level (p*M)).IsFiniteRelIndex (level M) :=
        ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p*M))).trans
          (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
      exact (ModularForm.trace (level M) F : ℍ → ℂ) : ℍ → ℂ) = 0 := by
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  let : (level (p*M)).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p*M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  obtain ⟨χ, _, hW⟩ := original_fricke_orbit (Nat.mul_pos hp.pos hM) hf
  have hWF : ∀ z g, χ * orbit m F z (frickeLabel (p*M) (Nat.mul_pos hp.pos hM)*g) =
      orbit m F z g := by simpa only [hF] using hW
  have hU : ∀ z g, (∑ a : Fin p, orbit m F z (ramifiedLabel p hp.pos a*g)) =
      (f p * (Real.sqrt p : ℂ)) * orbit m F z g := by
    intro z g
    rw [hF]
    exact original_ramified_orbit hm hf hp (Nat.dvd_mul_right p M) z g
  by_cases hpM : p ∣ M
  · have hs : p^2 ∣ p*M := by rw [pow_two]; exact Nat.mul_dvd_mul_left p hpM
    have hz := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData hp hs
    have hU0 : ∀ z g, (∑ a : Fin p, orbit m F z (ramifiedLabel p hp.pos a*g)) = 0 := by
      simpa only [hz, zero_mul] using hU
    rw [modularTrace_repeated_sum M p hp.pos hM hpM]
    exact repeated_trace_slash_zero M p m hM hp.pos F χ hWF hU0
  · have hc : p.Coprime M := hp.coprime_iff_not_dvd.mpr hpM
    have hAB : (p : ℤ)*Nat.gcdA p M+(M : ℤ)*Nat.gcdB p M=1 := by
      have hh := Nat.gcd_eq_gcd_ab p M
      rw [hc.gcd_eq_one, Nat.cast_one] at hh
      exact hh.symm
    have hs : ¬ p^2 ∣ p*M := by
      rw [pow_two, mul_dvd_mul_iff_left hp.ne_zero]
      exact hpM
    have hδ : (f p * (Real.sqrt p : ℂ))^2 = 1 := by
      rcases AsymptoticRamifiedCoefficients.simple_sign hf.toEulerData hp
        (Nat.dvd_mul_right p M) hs with h|h <;> rw [h] <;> norm_num
    rw [modularTrace_prime_sum M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB]
    exact simple_trace_slash_zero M p m hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB
      F χ (f p * (Real.sqrt p : ℂ)) hδ hWF hU

theorem modularTrace_target_congr {G H J : Subgroup (GL (Fin 2) ℝ)}
    [G.IsFiniteRelIndex H] [G.IsFiniteRelIndex J] {k : ℤ}
    (F : ModularForm G k) (h : H=J) :
    (ModularForm.trace H F : ℍ → ℂ) = (ModularForm.trace J F : ℍ → ℂ) := by
  subst J
  rfl

theorem original_primeTrace {N m : ℕ} (hN : 0<N) (hm : 0<m) {f : ℕ → ℂ}
    (hf : IsSolution N (2*m) f) (F : ModularForm (level N) ((2*m : ℕ) : ℤ))
    (hF : (F : ℍ → ℂ) = fourierFunction (2*m) f)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) : primeTrace N hN _ p F = 0 := by
  rcases p with ⟨p, hp, hpN⟩
  obtain ⟨M, rfl⟩ := hpN
  have hM : 0<M := by nlinarith [hp.pos]
  apply DFunLike.coe_injective
  unfold primeTrace
  have ht := original_factor_trace M p m hM hp hm hf F hF
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero (p*M) := ⟨hN.ne'⟩
  let : NeZero ((p*M)/p) := ⟨by rw [Nat.mul_div_cancel_left M hp.pos]; omega⟩
  let : (level (p*M)).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p*M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let : (level (p*M)).IsFiniteRelIndex (level ((p*M)/p)) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p*M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level ((p*M)/p))).symm).1
  change (ModularForm.trace (level ((p*M)/p)) F : ℍ → ℂ) = 0
  rw [modularTrace_target_congr F (congrArg level (Nat.mul_div_cancel_left M hp.pos))]
  exact ht

/-- Once modularity is known, the original Euler product and Fricke law
force the full M_k^circ conclusion at every positive level. -/
theorem original_modular_isCirc {N m : ℕ} (hN : 0<N) (hm : 0<m) {f : ℕ → ℂ}
    (hf : IsSolution N (2*m) f) (hmod : IsModular N (2*m) f) :
    IsCirc N hN (2*m) f := by
  obtain ⟨F,hF⟩ := hmod
  exact of_modular_trace hN hf F hF (original_primeTrace hN hm hf F hF)

theorem original_modular_isCirc_even {N k : ℕ} (hN : 0<N) (hk : 0<k)
    (heven : Even k) {f : ℕ → ℂ} (hf : IsSolution N k f) (hmod : IsModular N k f) :
    IsCirc N hN k f := by
  obtain ⟨m, hm⟩ := heven
  have hk' : k=2*m := by omega
  rw [hk'] at hf hmod ⊢
  exact original_modular_isCirc (m:=m) hN (by omega) hf hmod

/-- A proof of the earlier modularity target automatically upgrades to
exactly the user's corrected M_k^circ theorem. -/
theorem smallLevelsCirc_of_modular (h : SmallLevelOriginal.SmallLevelsTheorem) :
    SmallLevelsCircTheorem := by
  intro N k hN h36 h29 h31 hk heven f hf
  exact original_modular_isCirc_even hN hk heven hf (h N k hN h36 h29 h31 hk heven f hf)

#print axioms original_factor_trace
#print axioms original_primeTrace
#print axioms original_modular_isCirc
#print axioms original_modular_isCirc_even
#print axioms smallLevelsCirc_of_modular
end QuantitativeArithmeticSmallLevelCirc
