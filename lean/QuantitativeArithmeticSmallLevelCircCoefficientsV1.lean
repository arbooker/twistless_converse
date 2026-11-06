module

public import QuantitativeArithmeticSmallLevelCircSpaceV1
public import AsymptoticClassicalEigenPrimeArithmeticV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalEigenbasis

instance space_finite (N : ℕ) (hN : 0<N) (k : ℕ) :
    Module.Finite ℂ (space N hN k) := by
  let : NeZero N := ⟨hN.ne'⟩
  have : Module.Finite ℂ (ModularForm (level N) (k : ℤ)) :=
    AsymptoticClassicalCusp.modular_finite N (k : ℤ)
  infer_instance

/-- Raw holomorphic Fourier coefficients on the actual modular space;
these are not the unitary-normalized Dirichlet coefficients. -/
def modularCoefficient (N : ℕ) (k : ℤ) (n : ℕ) :
    ModularForm (level N) k →ₗ[ℂ] ℂ where
  toFun F := (qExpansion 1 F).coeff n
  map_add' F G := by
    simp only [FunLike.coe_add]
    rw [ModularForm.qExpansion_add zero_lt_one
      (AsymptoticClassicalCusp.level_one_period N), map_add]
  map_smul' c F := by
    simp only [FunLike.coe_smul]
    rw [ModularForm.qExpansion_smul zero_lt_one
      (AsymptoticClassicalCusp.level_one_period N), PowerSeries.coeff_smul]
    rfl

theorem modularCoefficient_separates (N : ℕ) (k : ℤ)
    (F : ModularForm (level N) k) (hF : ∀ n, modularCoefficient N k n F = 0) :
    F = 0 := by
  apply ModularForm.qExpansion_injective zero_lt_one
    (AsymptoticClassicalCusp.level_one_period N)
  ext n
  change (qExpansion 1 F).coeff n = (qExpansion 1 (0 : ℍ → ℂ)).coeff n
  rw [qExpansion_zero, map_zero]
  exact hF n

/-- Coefficient functionals on M_k^circ, including its Eisenstein part. -/
def coefficient (N : ℕ) (hN : 0<N) (k n : ℕ) : space N hN k →ₗ[ℂ] ℂ :=
  (modularCoefficient N (k : ℤ) n).comp (space N hN k).subtype

theorem coefficient_separates (N : ℕ) (hN : 0<N) (k : ℕ)
    (F : space N hN k) (hF : ∀ n, coefficient N hN k n F = 0) : F = 0 := by
  apply Subtype.val_injective
  exact modularCoefficient_separates N _ F.val hF

@[simp] theorem coefficient_zero (N : ℕ) (hN : 0<N) (k : ℕ)
    (F : space N hN k) : coefficient N hN k 0 F = 0 := by
  obtain ⟨G,hG,hF0,hG0,ht⟩ := F.property
  change (qExpansion 1 F.val).coeff 0 = 0
  simp [qExpansion_coeff, hF0.cuspFunction_apply_zero zero_lt_one]

/-- The usual prime recurrence, expressed only in actual q-coefficients.
Its derivation from actual Hecke operators is a separate theorem. -/
def HasPrimeRecurrence {N k : ℕ} {hN : 0<N}
    (F : space N hN k) (e b : Nat.Primes → ℂ) : Prop :=
  ∀ p : Nat.Primes, ∀ n : ℕ,
    coefficient N hN k (p.val*n) F = e p * coefficient N hN k n F -
      b p * (if p.val∣n then coefficient N hN k (n/p.val) F else 0)

theorem HasPrimeRecurrence.smul {N k : ℕ} {hN : 0<N}
    {F : space N hN k} {e b : Nat.Primes → ℂ}
    (hF : HasPrimeRecurrence F e b) (c : ℂ) : HasPrimeRecurrence (c • F) e b := by
  intro p n
  simp only [map_smul, smul_eq_mul]
  rw [hF p n]
  split_ifs <;> ring

theorem HasPrimeRecurrence.sub {N k : ℕ} {hN : 0<N}
    {F G : space N hN k} {e b : Nat.Primes → ℂ}
    (hF : HasPrimeRecurrence F e b) (hG : HasPrimeRecurrence G e b) :
    HasPrimeRecurrence (F-G) e b := by
  intro p n
  simp only [map_sub]
  rw [hF p n, hG p n]
  split_ifs <;> ring

theorem HasPrimeRecurrence.first_kernel {N k : ℕ} {hN : 0<N}
    {F : space N hN k} {e b : Nat.Primes → ℂ}
    (hF : HasPrimeRecurrence F e b) (hone : coefficient N hN k 1 F = 0) : F = 0 := by
  have h := zero_of_prime_recurrence (fun n => coefficient N hN k n F) e b
    (coefficient_zero N hN k F) hone hF
  apply coefficient_separates N hN k F
  intro n
  exact congrFun h n

theorem HasPrimeRecurrence.unique {N k : ℕ} {hN : 0<N}
    {F G : space N hN k} {e b : Nat.Primes → ℂ}
    (hF : HasPrimeRecurrence F e b) (hG : HasPrimeRecurrence G e b)
    (hone : coefficient N hN k 1 F = coefficient N hN k 1 G) : F = G := by
  apply sub_eq_zero.mp
  apply (hF.sub hG).first_kernel
  simp only [map_sub, hone, sub_self]

/-- A nonzero prime-recurrence form has a canonical normalization in the
actual full trace-new space, without any Petersson or cusp hypothesis. -/
theorem HasPrimeRecurrence.normalize {N k : ℕ} {hN : 0<N}
    {F : space N hN k} {e b : Nat.Primes → ℂ}
    (hF : HasPrimeRecurrence F e b) (hne : F ≠ 0) :
    ∃! G : space N hN k, coefficient N hN k 1 G = 1 ∧ HasPrimeRecurrence G e b := by
  have hfirst : coefficient N hN k 1 F ≠ 0 := fun h => hne (hF.first_kernel h)
  refine ⟨(coefficient N hN k 1 F)⁻¹ • F, ?_, ?_⟩
  · constructor
    · simp [hfirst]
    · exact hF.smul _
  · intro G hG
    apply hG.2.unique (hF.smul _)
    simp [hG.1, hfirst]

theorem HasPrimeRecurrence.prime_eigenvalue {N k : ℕ} {hN : 0<N}
    {F : space N hN k} {e b : Nat.Primes → ℂ}
    (hF : HasPrimeRecurrence F e b) (hone : coefficient N hN k 1 F = 1)
    (p : Nat.Primes) : e p = coefficient N hN k p.val F :=
  prime_eigenvalue_eq_coefficient (fun n => coefficient N hN k n F) e b hone hF p

theorem HasPrimeRecurrence.multiplicative {N k : ℕ} {hN : 0<N}
    {F : space N hN k} {e b : Nat.Primes → ℂ}
    (hF : HasPrimeRecurrence F e b) (hone : coefficient N hN k 1 F = 1) :
    ∀ m n : ℕ, m.Coprime n → coefficient N hN k (m*n) F =
      coefficient N hN k m F * coefficient N hN k n F := by
  apply multiplicative_of_prime_recurrence (fun n => coefficient N hN k n F) b
    (coefficient_zero N hN k F) hone
  intro p n
  rw [← hF.prime_eigenvalue hone p]
  exact hF p n

#print axioms modularCoefficient_separates
#print axioms coefficient_zero
#print axioms HasPrimeRecurrence.first_kernel
#print axioms HasPrimeRecurrence.unique
#print axioms HasPrimeRecurrence.normalize
#print axioms HasPrimeRecurrence.multiplicative
end QuantitativeArithmeticSmallLevelCirc
