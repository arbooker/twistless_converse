module

public import QuantitativeNinaMaassHeckeOperatorsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeMaass
open scoped InnerProductSpace

/-!
The physical Hecke/Fricke symmetry and resolvent invariance needed to
choose a joint spectral eigenfamily. Global Fricke commutation follows
from the actual cover-adjoint factorization and self-adjointness. The
prime norm estimate is deliberately crude: it suffices for the polynomial
coefficient growth proved in EulerArithmetic, without a Ramanujan bound.
-/

namespace QuantitativeNinaMaass

/-- The actual Friedrichs resolvent preserves each pair of new trace
equations, because both cover adjoints and global Fricke intertwine it. -/
theorem newTraceKernel_resolvent {M N : ℕ} [NeZero M] [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N) (v : AutomorphicSpace N)
    (hv : v ∈ newTraceKernel hN hMN) :
    friedrichsResolvent N v ∈ newTraceKernel hN hMN := by
  change levelTrace hMN v = 0 ∧ levelTrace hMN (frickeIsometry N hN v) = 0 at hv
  change levelTrace hMN (friedrichsResolvent N v) = 0 ∧
    levelTrace hMN (frickeIsometry N hN (friedrichsResolvent N v)) = 0
  constructor
  · rw [← levelTrace_resolvent, hv.1, map_zero]
  · rw [← fricke_resolvent, ← levelTrace_resolvent, hv.2, map_zero]

theorem newSpace_resolvent (N : ℕ) [NeZero N] (hN : 0 < N)
    (v : AutomorphicSpace N) (hv : v ∈ newSpace N hN) :
    friedrichsResolvent N v ∈ newSpace N hN := by
  simp only [newSpace, Submodule.mem_iInf] at hv ⊢
  intro p
  let : NeZero (N / p.val) := ⟨(Nat.div_pos
    (Nat.le_of_dvd hN p.property.2) p.property.1.pos).ne'⟩
  exact newTraceKernel_resolvent hN (Nat.div_dvd_of_dvd p.property.2) v (hv p)

/-- Multiplication by global Fricke removes the last Fricke factor in
the actual Hecke factorization, leaving a self-adjoint compressed operator. -/
theorem hecke_mul_fricke_selfAdjoint (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) :
    IsSelfAdjoint (HeckeL2.operator N p hN hpN A B hAB *
      (frickeIsometry N hN).toContinuousLinearMap) := by
  let hp := (Fact.out : p.Prime).pos
  let C := levelCover (Nat.dvd_mul_left N p)
  let V := (frickeIsometry (p * N) (Nat.mul_pos hp hN)).toContinuousLinearMap
  have he : HeckeL2.operator N p hN hpN A B hAB *
      (frickeIsometry N hN).toContinuousLinearMap =
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) • C.adjoint.comp (V.comp C) := by
    apply ContinuousLinearMap.ext
    intro v
    change HeckeL2.operator N p hN hpN A B hAB (frickeIsometry N hN v) = _
    rw [hecke_eq_dilationTraceOperator, dilationTraceOperator_apply,
      frickeIsometry_involutive]
    rfl
  rw [he]
  apply IsSelfAdjoint.smul
  · simp [IsSelfAdjoint]
  · exact (frickeIsometry_selfAdjoint (p * N) (Nat.mul_pos hp hN)).adjoint_conj C

/-- Every actual unramified Hecke operator commutes with global Fricke.
No sign-sector asymptotic or simultaneous-diagonalization premise is used. -/
theorem hecke_fricke_commute (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) :
    Commute (HeckeL2.operator N p hN hpN A B hAB)
      (frickeIsometry N hN).toContinuousLinearMap :=
  ((HeckeL2.operator_selfAdjoint N p hN hpN A B hAB).commute_iff
    (frickeIsometry_selfAdjoint N hN)).mpr
      (hecke_mul_fricke_selfAdjoint N p hN hpN A B hAB)

/-- The norm bound on an actual nonzero Hilbert eigenvector gives the
coarse prime estimate needed by the canonical Euler coefficient construction. -/
theorem hecke_eigenvalue_bound (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (v : AutomorphicSpace N) (hv : v ≠ 0) (ell : ℂ)
    (he : HeckeL2.operator N p hN hpN A B hAB v = ell • v) :
    ‖ell‖ ≤ (p : ℝ) + 1 := by
  have hb := (HeckeL2.operator N p hN hpN A B hAB).le_opNorm v
  rw [he, norm_smul] at hb
  have hell : ‖ell‖ ≤ ‖HeckeL2.operator N p hN hpN A B hAB‖ := by
    nlinarith [norm_pos_iff.mpr hv]
  apply hell.trans ((HeckeL2.operator_norm_le N p hN hpN A B hAB).trans ?_)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hs : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr hp1
  rw [Nat.cast_add, Nat.cast_one]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hs)).mpr
  nlinarith

/-- The ramified quadratic equation itself supplies the remaining prime
norm bound. The equation is separately derived from the physical traces. -/
theorem ramified_quadratic_norm_bound (N p : ℕ) (hp : p.Prime) (ell : ℂ)
    (he : ell ^ 2 = if p ^ 2 ∣ N then 0 else (p : ℂ)⁻¹) :
    ‖ell‖ ≤ 1 := by
  have hnorm := congrArg norm he
  rw [norm_pow] at hnorm
  have hb : ‖(if p ^ 2 ∣ N then 0 else (p : ℂ)⁻¹)‖ ≤ 1 := by
    split_ifs
    · simp only [norm_zero, zero_le_one]
    · rw [norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_lt.le)
  rw [← hnorm] at hb
  nlinarith [norm_nonneg ell]

theorem ramified_eigenvalue_coarse_bound (N p : ℕ) (hp : p.Prime) (ell : ℂ)
    (he : ell ^ 2 = if p ^ 2 ∣ N then 0 else (p : ℂ)⁻¹) :
    ‖ell‖ ≤ (p : ℝ) + 1 := by
  have h := ramified_quadratic_norm_bound N p hp ell he
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  linarith

#print axioms newTraceKernel_resolvent
#print axioms newSpace_resolvent
#print axioms hecke_mul_fricke_selfAdjoint
#print axioms hecke_fricke_commute
#print axioms hecke_eigenvalue_bound
#print axioms ramified_quadratic_norm_bound
#print axioms ramified_eigenvalue_coarse_bound

end QuantitativeNinaMaass
