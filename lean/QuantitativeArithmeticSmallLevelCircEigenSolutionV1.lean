module

public import QuantitativeArithmeticSmallLevelCircPrimeFrickeV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane
open scoped ModularForm

/-- Coefficient multiplicity one forces every normalized simultaneous
eigenform in full Mcirc to have a genuine Fricke sign. -/
theorem prime_eigen_fricke_sign {N k : ℕ} [NeZero N] {hN : 0 < N} (hk : Even k)
    (F : space N hN k) (hone : coefficient N hN k 1 F = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes,
      ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val) :
    ∃ eta : ℂ, (eta = 1 ∨ eta = -1) ∧ frickeLinear hk F = eta • F := by
  let J := frickeLinear (hN := hN) hk
  let c := coefficient N hN k 1 (J F)
  have hj (p : Nat.Primes) :
      ModularHecke.primeHecke N p.val p.property (k : ℤ) (J F).val = e p • (J F).val := by
    change ModularHecke.primeHecke N p.val p.property (k : ℤ) (frickeLinear hk F).val = _
    rw [frickeLinear_val, primeHecke_fricke_circ N k hN hk F.val F.property p.val p.property,
      heigen, map_smul, ← frickeLinear_val hk F]
  have hc (p : Nat.Primes) :
      ModularHecke.primeHecke N p.val p.property (k : ℤ) (c • F).val = e p • (c • F).val := by
    simp only [Submodule.coe_smul, map_smul, heigen]
    exact smul_comm _ _ _
  have he : J F = c • F := (recurrence_of_prime_eigen (J F) e hj).unique
    (recurrence_of_prime_eigen (c • F) e hc) (by simp [c, hone])
  refine ⟨c, ?_, he⟩
  apply sq_eq_one_iff.mp
  have hh := congrArg (fun V => coefficient N hN k 1 (J V)) he
  rw [show J (J F) = F from frickeLinear_involutive hk F,
    map_smul, map_smul, hone] at hh
  simpa only [smul_eq_mul, pow_two] using hh.symm

/-- Every normalized simultaneous prime Hecke eigenform in the genuine
full Mcirc is an original Euler solution, in every positive even weight
and at every level. Ramified factors and Fricke sign are derived. -/
theorem eigenform_isSolution {N k : ℕ} [NeZero N] {hN : 0 < N}
    (hk : 0 < k) (heven : Even k) (F : space N hN k)
    (hone : coefficient N hN k 1 F = 1) (e : Nat.Primes → ℂ)
    (heigen : ∀ p : Nat.Primes,
      ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val = e p • F.val) :
    FinitenessOriginalInput.IsSolution N k (ModularLSeries.coefficients F.val) := by
  obtain ⟨eta, heta, hfr⟩ := prime_eigen_fricke_sign heven F hone e heigen
  apply prime_eigen_original_of_fricke hk heven F hone e heigen eta heta
  have he := congrArg (fun G : space N hN k => (G.val : ℍ → ℂ)) hfr
  change ((frickeValue heven F).val : ℍ → ℂ) = eta • (F.val : ℍ → ℂ) at he
  simpa only [frickeValue_coe, Submodule.coe_smul, FunLike.coe_smul] using he

#print axioms prime_eigen_fricke_sign
#print axioms eigenform_isSolution
end QuantitativeArithmeticSmallLevelCirc
