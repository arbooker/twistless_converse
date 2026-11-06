module

public import AsymptoticClassicalFrickeDegeneracyV1
public import AsymptoticClassicalFrickeIsometryV1
public import AsymptoticClassicalHeckeSymmetryV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Complex AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct ComplexConjugate

/-- Fricke exchanges the two pairings of the level-raising maps. -/
theorem fricke_degeneracy_inner (N p : ℕ) [NeZero N] (hN : 0 < N)
    (hp : 0 < p) (k : ℕ) (hk : Even k) [NeZero (p*N)]
    (f g : CuspForm (level N) (k : ℤ)) :
    inner ℂ (degeneracy N p hp (k : ℤ) (frickeOperator N hN (k : ℤ) f))
      (restrict (k : ℤ) (level_antitone (dvd_mul_left N p)) (frickeOperator N hN (k : ℤ) g)) =
    inner ℂ (restrict (k : ℤ) (level_antitone (dvd_mul_left N p)) f)
      (degeneracy N p hp (k : ℤ) g) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have ha : conj ((p : ℂ)^(-((k : ℤ) : ℂ)/2)) = (p : ℂ)^(-((k : ℤ) : ℂ)/2) := by
    have he : (p : ℂ)^(-((k : ℤ) : ℂ)/2) = (((p : ℝ)^(-(k : ℝ)/2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity : 0 ≤ (p : ℝ))]
      push_cast
      rfl
    rw [he, Complex.conj_ofReal]
  have hc : conj ((p : ℂ)^(-((k : ℤ) : ℂ)/2)) * (p : ℂ)^(((k : ℤ) : ℂ)/2) = 1 := by
    rw [ha, ← Complex.cpow_add _ _ hpC]
    rw [show -((k : ℤ) : ℂ)/2 + ((k : ℤ) : ℂ)/2 = 0 by ring, Complex.cpow_zero]
  have hh := inner_frickeOperator (p*N) (Nat.mul_pos hp hN) (k : ℤ)
    (degeneracy N p hp (k : ℤ) (frickeOperator N hN (k : ℤ) f))
    (restrict (k : ℤ) (level_antitone (dvd_mul_left N p)) (frickeOperator N hN (k : ℤ) g))
  rw [fricke_degeneracy_restrict N p hN hp, fricke_restrict_degeneracy N p hN hp,
    frickeOperator_involutive N hN k hk f, frickeOperator_involutive N hN k hk g,
    inner_smul_left, inner_smul_right, ← mul_assoc, hc, one_mul] at hh
  exact hh.symm

/-- The actual good-level Hecke correspondence commutes with normalized global
Fricke. The proof uses the two level-raising maps and their Petersson adjunction. -/
theorem dilationTrace_fricke_commute (N p : ℕ) [NeZero N] (hN : 0 < N)
    (hp : 0 < p) (k : ℕ) (hk : Even k) (A B : ℤ)
    (hAB : (p : ℤ)*A + (N : ℤ)*B = 1) :
    Function.Commute (dilationTrace N p hp (k : ℤ)) (frickeOperator N hN (k : ℤ)) := by
  let : NeZero (p*N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  intro f
  apply ext_inner_right ℂ
  intro u
  obtain ⟨g, rfl⟩ := (frickeOperator_involutive N hN k hk).surjective u
  rw [inner_frickeOperator, dilationTrace_inner, fricke_degeneracy_inner N p hN hp k hk,
    dilationTrace_inner]
  have hh := slash_dilation_inner_swap N p hp (k : ℤ) A B hAB f g
  simpa only [inner_smul_left, inner_smul_right, map_zpow₀, Complex.conj_natCast] using hh.symm

theorem dilationTrace_prime_fricke_commute (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (k : ℕ) (hk : Even k) :
    Function.Commute (dilationTrace N p (Fact.out : p.Prime).pos (k : ℤ))
      (frickeOperator N hN (k : ℤ)) := by
  have hc : p.Coprime N := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN
  apply dilationTrace_fricke_commute N p hN (Fact.out : p.Prime).pos k hk
    (Nat.gcdA p N) (Nat.gcdB p N)
  have hh := Nat.gcd_eq_gcd_ab p N
  rw [hc.gcd_eq_one, Nat.cast_one] at hh
  exact hh.symm

#print axioms fricke_degeneracy_inner
#print axioms dilationTrace_fricke_commute
#print axioms dilationTrace_prime_fricke_commute

end AsymptoticClassicalCusp
