module

public import AsymptoticClassicalEigenFrickeSlashV1
public import AsymptoticClassicalEulerBadPrimesV1
public import AsymptoticClassicalEulerNormalizationV1
public import QuantitativeArithmeticSmallLevelCircMellinV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelCirc.ModularLSeries. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelCircFourierNormalizationV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularLSeries
open UpperHalfPlane Filter Asymptotics AsymptoticClassicalCusp
variable {N : ℕ} {k : ℤ}

/-- The unitary normalization of the actual Fourier coefficients. -/
def coefficients (f : ModularForm (level N) k) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n * ((n : ℝ) ^ (-((k : ℝ) - 1) / 2) : ℝ)

@[simp] theorem coefficients_zero (f : ModularForm (level N) k)
    (hzero : (qExpansion 1 f).coeff 0 = 0) : coefficients f 0 = 0 := by
  rw [coefficients, hzero, zero_mul]

@[simp] theorem coefficients_one (f : ModularForm (level N) k) :
    coefficients f 1 = (qExpansion 1 f).coeff 1 := by simp [coefficients]

theorem coefficients_recover (f : ModularForm (level N) k) (n : ℕ) (hn : 0 < n) :
    coefficients f n * ((n : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) = (qExpansion 1 f).coeff n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [coefficients, mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hnR]
  rw [show -((k : ℝ) - 1) / 2 + ((k : ℝ) - 1) / 2 = 0 by ring]
  simp

/-- The elementary Hecke coefficient bound suffices for the growth
 hypothesis of the complex Euler-product predicate. -/
theorem coefficients_isBigO [NeZero N] (hk : 0≤k) (f : ModularForm (level N) k) :
    coefficients f =O[atTop] (fun n : ℕ => (n : ℝ) ^ (((k : ℝ)+1) / 2)) := by
  have ha : (fun n => (qExpansion 1 f).coeff n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (k : ℝ)) := by
    simpa only [level, CongruenceSubgroup.strictWidthInfty_Gamma0, Real.rpow_intCast] using
      ModularFormClass.qExpansion_isBigO hk f
  obtain ⟨C, _, hb⟩ := bound_of_isBigO_nat_atTop ha
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb' : ‖(qExpansion 1 f).coeff n‖ ≤ C * (n : ℝ) ^ (k : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hnR _)] using
      hb (Real.rpow_pos_of_pos hnR (k : ℝ)).ne'
  calc
    ‖coefficients f n‖ = ‖(qExpansion 1 f).coeff n‖ * (n : ℝ) ^ (-((k : ℝ) - 1) / 2) := by
      simp only [coefficients, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hnR _)]
    _ ≤ (C * (n : ℝ) ^ (k : ℝ)) * (n : ℝ) ^ (-((k : ℝ) - 1) / 2) :=
      mul_le_mul_of_nonneg_right hb' (Real.rpow_pos_of_pos hnR _).le
    _ = C * ‖(n : ℝ) ^ (((k : ℝ)+1) / 2)‖ := by
      rw [mul_assoc, ← Real.rpow_add hnR,
        show (k : ℝ) + -((k : ℝ) - 1) / 2 = ((k : ℝ)+1) / 2 by ring,
        Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hnR _)]

theorem coefficients_growth [NeZero N] (hk : 0≤k) (f : ModularForm (level N) k) :
    ∃ σ : ℝ, 0 < σ ∧ coefficients f =O[atTop] (fun n : ℕ => (n : ℝ) ^ σ) :=
  ⟨((k : ℝ)+1) / 2, by
    have h : (0 : ℝ)≤k := by exact_mod_cast hk
    linarith, coefficients_isBigO hk f⟩

#print axioms coefficients_zero
#print axioms coefficients_recover
#print axioms coefficients_isBigO
#print axioms coefficients_growth
end QuantitativeArithmeticSmallLevelCirc.ModularLSeries
end
end

/-! ## QuantitativeArithmeticSmallLevelCircEulerDataV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularLSeries
open UpperHalfPlane Complex AsymptoticClassicalCusp
variable {N : ℕ} {k : ℤ}

/-- Unitary normalization preserves coprime multiplicativity. -/
theorem coefficients_multiplicative (f : ModularForm (level N) k)
    (hmul : ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n)
    (m n : ℕ) (hc : m.Coprime n) :
    coefficients f (m*n) = coefficients f m * coefficients f n := by
  simp only [coefficients, hmul m n hc, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), Complex.ofReal_mul]
  ring

/-- At prime powers the unitary normalization is a geometric rescaling. -/
theorem coefficients_prime_pow (f : ModularForm (level N) k) (p j : ℕ) :
    coefficients f (p^j) = (qExpansion 1 f).coeff (p^j) *
      (((p : ℝ)^(-((k : ℝ)-1)/2) : ℝ) : ℂ)^j := by
  rw [coefficients, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg p),
    Complex.ofReal_pow]

/-- The factor `p^(k-1)` in the classical Hecke recurrence disappears
under the unitary normalization used in the paper. -/
theorem coefficients_prime_recurrence (f : ModularForm (level N) k)
    (p : ℕ) (hp : 0 < p) (j : ℕ) (ξ : ℂ)
    (hrec : (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        ξ * (p : ℂ)^(k-1) * (qExpansion 1 f).coeff (p^j)) :
    coefficients f (p^(j+2)) = coefficients f p * coefficients f (p^(j+1)) -
      ξ * coefficients f (p^j) := by
  let r : ℂ := (((p : ℝ)^(-((k : ℝ)-1)/2) : ℝ) : ℂ)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hscale : (p : ℂ)^(k-1) * r^2 = 1 := by
    dsimp [r]
    rw [← Complex.ofReal_natCast p, ← Complex.ofReal_zpow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hpR.le,
      ← Real.rpow_add hpR]
    norm_num only [Int.cast_sub, Int.cast_one, Nat.cast_ofNat]
    rw [show (k : ℝ)-1 + (-((k : ℝ)-1)/2)*2 = 0 by ring, Real.rpow_zero]
  rw [coefficients_prime_pow, coefficients_prime_pow, coefficients_prime_pow, hrec]
  change (_ - ξ * (p : ℂ)^(k-1) * _) * r^(j+2) =
    ((qExpansion 1 f).coeff p * r) * (_ * r^(j+1)) - ξ * (_ * r^j)
  simp only [pow_add, pow_one]
  linear_combination -ξ * (qExpansion 1 f).coeff (p^j) * r^j * hscale

/-- The classical raw Fourier recurrences give the exact complex Euler
product of the normalized coefficients. -/
theorem coefficients_eulerProduct [NeZero N] (hk : 0≤k) (f : ModularForm (level N) k)
    (hzero : (qExpansion 1 f).coeff 0 = 0)
    (hone : (qExpansion 1 f).coeff 1 = 1)
    (hmul : ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n)
    (hrec : ∀ p, p.Prime → ∀ j, (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        FinitenessEulerIdentification.xi N p * (p : ℂ)^(k-1) *
          (qExpansion 1 f).coeff (p^j)) :
    FinitenessOriginalInput.EulerProduct N (coefficients f) := by
  apply AsymptoticClassicalEulerProduct.eulerProduct_of_arithmetic
    (coefficients_zero f hzero) (by simpa using hone) (coefficients_isBigO hk f)
    (coefficients_multiplicative f hmul)
  intro p hp j
  exact coefficients_prime_recurrence f p hp.pos j _ (hrec p hp j)

/-- The raw newform bad-prime squares have precisely the normalized
values required by E(N,k). -/
theorem coefficients_badPrimeConditions (f : ModularForm (level N) k)
    (hbad : ∀ p, p.Prime → p ∣ N →
      (qExpansion 1 f).coeff p ^ 2 = if p^2 ∣ N then 0 else (p : ℂ)^(k-2)) :
    FinitenessOriginalInput.BadPrimeConditions N (coefficients f) := by
  intro p hp hpN
  rw [coefficients, mul_pow, hbad p hp hpN]
  by_cases hpp : p^2 ∣ N
  · simp [hpp]
  rw [ite_eq_right hpp, ite_eq_right hpp]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  rw [← Complex.ofReal_natCast p, ← Complex.ofReal_zpow, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_inv]
  apply congrArg Complex.ofReal
  rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hpR.le,
    ← Real.rpow_add hpR]
  norm_num only [Int.cast_sub, Int.cast_ofNat, Nat.cast_ofNat]
  rw [show (k : ℝ)-2 + (-((k : ℝ)-1)/2)*2 = -1 by ring, Real.rpow_neg_one]

/-- Every part of EulerData follows from the classical raw Fourier
relations; the polynomial growth is already proved for actual cusp forms. -/
theorem coefficients_eulerData [NeZero N] (hk : 0≤k) (f : ModularForm (level N) k)
    (hzero : (qExpansion 1 f).coeff 0 = 0)
    (hone : (qExpansion 1 f).coeff 1 = 1)
    (hmul : ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n)
    (hrec : ∀ p, p.Prime → ∀ j, (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        FinitenessEulerIdentification.xi N p * (p : ℂ)^(k-1) *
          (qExpansion 1 f).coeff (p^j))
    (hbad : ∀ p, p.Prime → p ∣ N →
      (qExpansion 1 f).coeff p ^ 2 = if p^2 ∣ N then 0 else (p : ℂ)^(k-2)) :
    FinitenessOriginalInput.EulerData N (coefficients f) where
  zero := coefficients_zero f hzero
  growth := coefficients_growth hk f
  euler := coefficients_eulerProduct hk f hzero hone hmul hrec
  bad := coefficients_badPrimeConditions f hbad

#print axioms coefficients_prime_recurrence
#print axioms coefficients_eulerProduct
#print axioms coefficients_badPrimeConditions
#print axioms coefficients_eulerData
end QuantitativeArithmeticSmallLevelCirc.ModularLSeries
end
end

/-! ## QuantitativeArithmeticSmallLevelCircCompletionV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularLSeries
open UpperHalfPlane Complex Filter AsymptoticClassicalCusp

variable {N : ℕ} {k : ℤ}

/-- The conversion uses the unitary normalization of the Dirichlet
coefficients throughout. -/
theorem coefficient_dirichlet_term (f : ModularForm (level N) k)
    (n : ℕ) (hn : 0<n) (s : ℂ) :
    coefficients f n * (n : ℂ)^(-s) =
      (qExpansion 1 f).coeff n * (n : ℂ)^(-(s+((k : ℂ)-1)/2)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [coefficients, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast,
    mul_assoc, ← Complex.cpow_add _ _ hnC]
  congr 2
  push_cast
  ring

theorem mellin_dirichlet_term (f : ModularForm (level N) k)
    (n : ℕ) (hn : 0<n) (s : ℂ) :
    (Real.pi : ℂ)^(-(s+((k : ℂ)-1)/2)) * Gamma (s+((k : ℂ)-1)/2) *
      (qExpansion 1 f).coeff n / (2*(n : ℝ) : ℝ)^(s+((k : ℂ)-1)/2) =
    ((2*Real.pi : ℝ) : ℂ)^(-(s+((k : ℂ)-1)/2)) * Gamma (s+((k : ℂ)-1)/2) *
      (coefficients f n * (n : ℂ)^(-s)) := by
  rw [coefficient_dirichlet_term f n hn s]
  simp only [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg zero_le_two (Nat.cast_nonneg n),
    Complex.mul_cpow_ofReal_nonneg zero_le_two Real.pi_pos.le]
  simp only [Complex.ofReal_ofNat, Complex.ofReal_natCast, div_eq_mul_inv,
    mul_inv_rev, ← Complex.cpow_neg]
  ring

/-- The paper's conductor and central-line normalization, applied to the
general modular Mellin transform. Entireness requires the two cusp zeros. -/
def entireCompletion (N k : ℕ) [NeZero N] (hk : 0<k)
    (f : ModularForm (level N) (k : ℤ)) (s : ℂ) : ℂ :=
  2 * (N : ℂ)^((s-1/2)/2) *
    ModularForm.Λ (by exact_mod_cast hk) f (s+((k : ℂ)-1)/2)

theorem entireCompletion_differentiable (N k : ℕ) [NeZero N]
    (hN : 0<N) (hk : 0<k) (f : ModularForm (level N) (k : ℤ))
    (hf : f ∈ space N hN k) : Differentiable ℂ (entireCompletion N k hk f) := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hp : Differentiable ℂ (fun s : ℂ => (N : ℂ)^((s-1/2)/2)) := by
    simp only [Complex.cpow_def_of_ne_zero hNC]
    fun_prop
  have hΛ := space_lambda_differentiable hk (⟨f,hf⟩ : space N hN k)
  exact ((differentiable_const _).mul hp).mul
    (hΛ.comp (differentiable_id.add (differentiable_const _)))

/-- A possibly wider right half-plane accommodates Eisenstein coefficient
growth. Its exact boundary is immaterial to the original continuation predicate. -/
theorem entireCompletion_eq_completed (N k : ℕ) [NeZero N]
    (hN : 0<N) (hk : 0<k) (f : ModularForm (level N) (k : ℤ))
    (hf : f ∈ space N hN k) (s : ℂ) (hs : (k : ℝ)+2 < s.re) :
    entireCompletion N k hk f s = FinitenessOriginalInput.completed N k (coefficients f) s := by
  let z : ℂ := s+((k : ℂ)-1)/2
  have hsz : (k : ℝ)+1 < z.re := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re, Complex.one_re]
    have hkn : (0 : ℝ)≤k := Nat.cast_nonneg k
    linarith
  have hh := ModularForm.hasSum_Λ (f := f)
    (by exact_mod_cast hk : (0 : ℤ)<k) (s := z) (by exact_mod_cast hsz)
  simp only [level, CongruenceSubgroup.strictWidthInfty_Gamma0, div_one] at hh
  have hzero : (qExpansion 1 f).coeff 0 = 0 :=
    coefficient_zero N hN k (⟨f,hf⟩ : space N hN k)
  have hh' : HasSum (fun n : ℕ => (Real.pi : ℂ)^(-z) * Gamma z *
      (qExpansion 1 f).coeff (n+1) / (2*(n+1 : ℕ) : ℝ)^z)
      (ModularForm.Λ (by exact_mod_cast hk) f z) := by
    apply (hasSum_nat_add_iff 1 (f := fun n : ℕ => (Real.pi : ℂ)^(-z) * Gamma z *
      (qExpansion 1 f).coeff n / (2*(n : ℝ) : ℝ)^z)).mpr
    simpa only [Finset.sum_range_one, hzero, mul_zero, zero_div, add_zero] using hh
  have hterms : (fun n : ℕ => (Real.pi : ℂ)^(-z) * Gamma z *
      (qExpansion 1 f).coeff (n+1) / (2*(n+1 : ℕ) : ℝ)^z) =
      (fun n : ℕ => ((2*Real.pi : ℝ) : ℂ)^(-z) * Gamma z *
        (coefficients f (n+1) * ((n+1 : ℕ) : ℂ)^(-s))) := by
    funext n
    exact mellin_dirichlet_term f (n+1) (Nat.succ_pos n) s
  rw [hterms] at hh'
  have he := hh'.tsum_eq.symm
  rw [tsum_mul_left] at he
  change ModularForm.Λ _ f z = ((2*Real.pi : ℝ) : ℂ)^(-z) * Gamma z *
    FinitenessOriginalInput.L (coefficients f) s at he
  unfold entireCompletion FinitenessOriginalInput.completed FinitenessOriginalInput.gammaC
  change 2 * (N : ℂ)^((s-1/2)/2) * ModularForm.Λ _ f z = _
  rw [he]
  dsimp [z]
  ring

theorem entireCompletion_finiteOrder (N k : ℕ) [NeZero N]
    (hN : 0<N) (hk : 0<k) (f : ModularForm (level N) (k : ℤ))
    (hf : f ∈ space N hN k) :
    FinitenessOriginalInput.FiniteOrder (entireCompletion N k hk f) := by
  apply FinitenessInputBounds.bound_finiteOrder
  have hΛ := FinitenessInputBounds.bound_shift
    (space_lambda_finiteOrder hk (⟨f,hf⟩ : space N hN k)) (((k : ℂ)-1)/2)
  exact FinitenessFiniteOrder.mul
    (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const 2)
      (AsymptoticClassicalLSeries.conductor_finiteOrder N hN)) hΛ

#print axioms coefficient_dirichlet_term
#print axioms entireCompletion_differentiable
#print axioms entireCompletion_eq_completed
#print axioms entireCompletion_finiteOrder
end QuantitativeArithmeticSmallLevelCirc.ModularLSeries
end
end

/-! ## QuantitativeArithmeticSmallLevelCircEulerSolutionV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularLSeries
open UpperHalfPlane Complex AsymptoticClassicalCusp
open scoped ModularForm

/-- Identify the two existing normalizations of the actual Fricke action. -/
theorem normalizedFricke_eq_detOne_slash (N : ℕ) (hN : 0<N)
    (k : ℤ) (f : ℍ → ℂ) :
    AsymptoticClassicalLSeries.normalizedFricke N hN k f =
      f ∣[k] SmallLevelNormalized.fricke N hN := by
  have hscale : (Real.sqrt N : ℂ)^(-k) = (N : ℂ)^(-(k : ℂ)/2) := by
    rw [← Complex.ofReal_zpow, ← Real.rpow_intCast, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (Nat.cast_nonneg N), Complex.ofReal_cpow (Nat.cast_nonneg N)]
    congr 2
    push_cast
    ring
  funext z
  have ha : AsymptoticClassicalCusp.frickeReal N hN • z =
      SmallLevelNormalized.fricke N hN • z := by
    apply UpperHalfPlane.ext
    exact (AsymptoticClassicalLSeries.frickeReal_action N hN z).trans
      (SmallLevelNormalized.fricke_point N hN z).symm
  rw [AsymptoticClassicalLSeries.normalizedFricke,
    SmallLevelNormalized.det_one_slash _ (SmallLevelNormalized.fricke_det N hN),
    SmallLevelNormalized.fricke_denom, mul_zpow, hscale, ha]
  ring

/-- Conductor-normalized reflection from the actual Fricke eigenrelation,
using the Mellin integral whose convergence was proved from the two cusp zeros. -/
theorem entireCompletion_fricke_eigen (N k : ℕ) [NeZero N]
    (hN : 0<N) (hk : 0<k) (f : ModularForm (level N) (k : ℤ))
    (hf : f ∈ space N hN k) (eta : ℂ)
    (hfr : (f : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN = eta • (f : ℍ → ℂ))
    (s : ℂ) :
    entireCompletion N k hk f s = (Complex.I^(k : ℤ)*eta) *
      entireCompletion N k hk f (1-s) := by
  have hNreal : 0<(N : ℝ) := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have heigen : AsymptoticClassicalLSeries.normalizedFricke N hN (k : ℤ) f =
      eta • (f : ℍ → ℂ) := by
    rw [normalizedFricke_eq_detOne_slash]
    exact hfr
  have haxis (t : ℝ) (ht : 0<t) :
      f (ofComplex (Complex.I*((N : ℝ)*t)⁻¹)) =
        (Complex.I^(k : ℤ)*eta) * (N : ℂ)^((k : ℂ)/2) * (t : ℂ)^(k : ℂ) *
          f (ofComplex (Complex.I*t)) := by
    simpa only [Int.cast_natCast] using
      AsymptoticClassicalLSeries.axial_fricke_of_eigen N hN (k : ℤ) f eta heigen t ht
  have hm := AsymptoticClassicalLSeries.mellin_fricke (N : ℝ) hNreal
    (fun t => f (ofComplex (Complex.I*t))) (k : ℂ) (Complex.I^(k : ℤ)*eta)
    haxis (s+((k : ℂ)-1)/2)
  simp only [Complex.ofReal_natCast] at hm
  have he (z : ℂ) : ModularForm.Λ (by exact_mod_cast hk) f z =
      mellin (fun t => f (ofComplex (Complex.I*t))) z :=
    congrFun (space_strongPair hk (⟨f,hf⟩ : space N hN k)).Λ_eq z
  unfold entireCompletion
  rw [he, hm, he]
  rw [show (k : ℂ)-(s+((k : ℂ)-1)/2) = 1-s+((k : ℂ)-1)/2 by ring]
  calc
    _ = (Complex.I^(k : ℤ)*eta) *
        (2 * ((N : ℂ)^((s-1/2)/2) * (N : ℂ)^((k : ℂ)/2-(s+((k : ℂ)-1)/2))) *
          mellin (fun t => f (ofComplex (Complex.I*t))) (1-s+((k : ℂ)-1)/2)) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hNC]
      congr 3
      ring

/-- Every analytic clause in the original input, for full modular forms
vanishing at the two distinguished cusps. -/
theorem coefficients_continuation (N k : ℕ) [NeZero N]
    (hN : 0<N) (hk : 0<k) (heven : Even k)
    (f : ModularForm (level N) (k : ℤ)) (hf : f ∈ space N hN k)
    (eta : ℂ) (heta : eta=1 ∨ eta= -1)
    (hfr : (f : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN = eta • (f : ℍ → ℂ)) :
    FinitenessOriginalInput.Continuation N k (coefficients f) := by
  refine ⟨entireCompletion N k hk f, entireCompletion_differentiable N k hN hk f hf,
    entireCompletion_finiteOrder N k hN hk f hf, ⟨(k : ℝ)+2, ?_⟩,
    Complex.I^(k : ℤ)*eta, AsymptoticClassicalLSeries.fricke_root_sign k heven heta, ?_⟩
  · intro s hs
    exact entireCompletion_eq_completed N k hN hk f hf s hs
  · intro s
    exact entireCompletion_fricke_eigen N k hN hk f hf eta hfr s

/-- Full modular eigenpacket interface. The hypotheses are actual Fourier
arithmetic and Fricke equations; continuation and finite order are conclusions.
No cuspidality at the other cusps and no eigenbasis premise are imposed. -/
theorem coefficients_isSolution (N k : ℕ) [NeZero N]
    (hN : 0<N) (hk : 0<k) (heven : Even k)
    (f : ModularForm (level N) (k : ℤ)) (hf : f ∈ space N hN k)
    (hone : (qExpansion 1 f).coeff 1 = 1)
    (hmul : ∀ m n, m.Coprime n → (qExpansion 1 f).coeff (m*n) =
      (qExpansion 1 f).coeff m * (qExpansion 1 f).coeff n)
    (hrec : ∀ p, p.Prime → ∀ j, (qExpansion 1 f).coeff (p^(j+2)) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff (p^(j+1)) -
        FinitenessEulerIdentification.xi N p * (p : ℂ)^((k : ℤ)-1) *
          (qExpansion 1 f).coeff (p^j))
    (hbad : ∀ p, p.Prime → p∣N →
      (qExpansion 1 f).coeff p ^ 2 = if p^2∣N then 0 else (p : ℂ)^((k : ℤ)-2))
    (eta : ℂ) (heta : eta=1 ∨ eta= -1)
    (hfr : (f : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN = eta • (f : ℍ → ℂ)) :
    FinitenessOriginalInput.IsSolution N k (coefficients f) where
  toEulerData := coefficients_eulerData (by omega) f
    (coefficient_zero N hN k (⟨f,hf⟩ : space N hN k)) hone hmul hrec hbad
  continuation := coefficients_continuation N k hN hk heven f hf eta heta hfr

#print axioms normalizedFricke_eq_detOne_slash
#print axioms entireCompletion_fricke_eigen
#print axioms coefficients_continuation
#print axioms coefficients_isSolution
end QuantitativeArithmeticSmallLevelCirc.ModularLSeries
end
end
