module
public import AsymptoticClassicalOldIntersectionV1
public import AsymptoticFrickeNormalizerV1
public import FinitenessAllLevelGoodCoefficientsV1
public import FinitenessNormalizedTwistProductV1
public import FinitenessRamanujanDivisorV1
public import QuantitativeArithmeticPrimeSmallTwistCharactersV1
public import QuantitativeArithmeticWeightedFourierTwistV1
public import SmallLevelNormalizedMatricesV1
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Topology.Instances.Int
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.NumberTheory.ModularForms.Basic


/-! The small-conductor converse theorem: geometric generation,
additive-twist reconstruction, and reduction to primitive characters. -/

/-! ## CharacterPair -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

/-- For t=-p this is the partner residue b determined by pab=-1. -/
def partnerEquiv {q : ℕ} (t : (ZMod q)ˣ) : (ZMod q)ˣ ≃ (ZMod q)ˣ :=
  (Equiv.mulLeft t).trans (Equiv.inv _)

theorem character_partner_weight {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t a : (ZMod q)ˣ) :
    χ (a : ZMod q)=star (χ (t : ZMod q))*
      star (χ ((partnerEquiv t a : (ZMod q)ˣ) : ZMod q)) := by
  have hinv (u : (ZMod q)ˣ) : χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q)=(χ (u : ZMod q))⁻¹ := by
    have h := congrArg (fun v : ℂˣ => (v : ℂ)) ((MulChar.equivToUnitHom χ).map_inv u)
    simpa only [MulChar.coe_equivToUnitHom,Units.val_inv_eq_inv_val] using h
  change χ (a : ZMod q)=star (χ (t : ZMod q))*star (χ (((t*a)⁻¹ : (ZMod q)ˣ) : ZMod q))
  rw [hinv,Units.val_mul,map_mul]
  have ht : star (χ (t : ZMod q))=(χ (t : ZMod q))⁻¹ :=
    (Complex.inv_eq_conj (χ.unit_norm_eq_one t)).symm
  have ha : star (χ (a : ZMod q))=(χ (a : ZMod q))⁻¹ :=
    (Complex.inv_eq_conj (χ.unit_norm_eq_one a)).symm
  have ht0 : χ (t : ZMod q) ≠ 0 := by
    intro h; simpa [h] using χ.unit_norm_eq_one t
  rw [star_inv₀,star_mul,ht,ha]
  simp [mul_inv_rev,ht0]

theorem character_partner_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : (ZMod q)ˣ) (R : (ZMod q)ˣ → ℂ) :
    star (χ (t : ZMod q))*∑ b : (ZMod q)ˣ, star (χ (b : ZMod q))*R b =
      ∑ a : (ZMod q)ˣ, χ (a : ZMod q)*R (partnerEquiv t a) := by
  classical
  rw [← (partnerEquiv t).sum_comp (fun b => star (χ (b : ZMod q))*R b)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc,← character_partner_weight]

/-- The paired character relation recovers each individual additive
branch, including the partner permutation and its root-number factor. -/
theorem individual_of_paired_character_sums {X : Type*}
    (q : ℕ) [NeZero q] (t : (ZMod q)ˣ) (ε : ℂ)
    (L R : (ZMod q)ˣ → X → ℂ)
    (h : ∀ χ : DirichletCharacter ℂ q, ∀ z : X,
      (∑ a : (ZMod q)ˣ, χ (a : ZMod q)*L a z)=
        ε*star (χ (t : ZMod q))*∑ b : (ZMod q)ˣ, star (χ (b : ZMod q))*R b z) :
    ∀ a z, L a z=ε*R (partnerEquiv t a) z := by
  have he : L=(fun a z => ε*R (partnerEquiv t a) z) := by
    apply individual_function_eq_of_all_character_sums
    intro χ z
    rw [h χ z,mul_assoc,character_partner_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  intro a z
  exact congrFun (congrFun he a) z

#print axioms character_partner_weight
#print axioms individual_of_paired_character_sums

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## AnalyticLaws -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex UpperHalfPlane SmallLevelNormalized Filter Asymptotics
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  QuantitativeArithmeticWeightedFourierTwist
open scoped MatrixGroups ModularForm

theorem inverse_fricke_pair (N k : ℕ) (hN : 0<N) (F G : ℂ → ℂ) (c : ℂ)
    (h : ∀ z : ℂ, 0<z.im → F z=c/(((Real.sqrt N : ℂ)*z)^k)*G (-1/((N : ℂ)*z))) :
    (fun z : ℍ => F z) ∣[(k : ℤ)] (fricke N hN)⁻¹=c • (fun z : ℍ => G z) := by
  have he : (fun z : ℍ => F z)=c • ((fun z : ℍ => G z) ∣[(k : ℤ)] fricke N hN) := by
    funext z
    rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (fricke_det N hN),fricke_denom,fricke_point]
    simpa only [zpow_neg,zpow_natCast,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]
      using h z z.im_pos
  have hh := congrArg (fun f : ℍ → ℂ => f ∣[(k : ℤ)] (fricke N hN)⁻¹) he
  rw [det_one_smul _ (det_one_inv _ (fricke_det N hN)),
    ← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hh
  exact hh

theorem translates_eq_slash_sum {ι : Type*} [Fintype ι]
    (F : ℂ → ℂ) (w : ι → ℂ) (r : ι → ℝ) (k : ℤ) :
    (fun z : ℍ => translates F w r z)=
      ∑ i, w i • ((fun z : ℍ => F z) ∣[k] translation (r i)) := by
  funext z
  simp only [translates,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    translation_slash,translation_point]

/-- Entire finite-order completions of all character twists, with the
specified paired equations, yield every individual additive transformation.
The coefficient twists are literal finite exponential sums. -/
theorem additive_laws_of_character_FE (N q k : ℕ) (hN : 0<N) [NeZero q]
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (r : (ZMod q)ˣ → ℝ) (t : (ZMod q)ˣ) (ε : ℂ) (hε : ‖ε‖=1)
    (Λ : DirichletCharacter ℂ q → ℂ → ℂ)
    (hhol : ∀ χ, Differentiable ℂ (Λ χ)) (hfinite : ∀ χ, FiniteOrder (Λ χ))
    (hagree : ∀ χ, ∃ c : ℝ, ∀ s : ℂ, c<s.re →
      Λ χ s=completed N k (twisted f (fun a : (ZMod q)ˣ => χ (a : ZMod q)) r) s)
    (hFE : ∀ χ s, Λ χ s=ε*star (χ (t : ZMod q))*Λ (star χ) (1-s)) :
    ∀ a : (ZMod q)ˣ,
      (fun z : ℍ => fourier (fullCoefficients f k) z) ∣[(k : ℤ)]
          (translation (r a)*(fricke N hN)⁻¹)=
        (ε*Complex.I^k) • ((fun z : ℍ => fourier (fullCoefficients f k) z) ∣[(k : ℤ)]
          translation (r (partnerEquiv t a))) := by
  let F : ℍ → ℂ := fun z => fourier (fullCoefficients f k) z
  have hall (χ : DirichletCharacter ℂ q) :
      (∑ a : (ZMod q)ˣ, χ (a : ZMod q) • (F ∣[(k : ℤ)] translation (r a))) ∣[(k : ℤ)]
          (fricke N hN)⁻¹=
        ((ε*star (χ (t : ZMod q)))*Complex.I^k) •
          ∑ b : (ZMod q)ˣ, star (χ (b : ZMod q)) • (F ∣[(k : ℤ)] translation (r b)) := by
    obtain ⟨c,hc⟩ := hagree χ
    obtain ⟨d,hd⟩ := hagree (star χ)
    have hunit : ‖ε*star (χ (t : ZMod q))‖=1 := by
      rw [norm_mul,norm_star,hε,χ.unit_norm_eq_one,mul_one]
    have hlaw := paired_translation_law hN hf0 hf
      (fun a : (ZMod q)ˣ => χ (a : ZMod q))
      (fun a : (ZMod q)ˣ => (star χ) (a : ZMod q)) r
      (Λ χ) (Λ (star χ)) (hhol χ) (hfinite χ) hc hd hunit (hFE χ)
    have h := inverse_fricke_pair N k hN _ _ _ hlaw
    rw [translates_eq_slash_sum _ _ _ (k : ℤ),
      translates_eq_slash_sum _ _ _ (k : ℤ)] at h
    simpa only [MulChar.star_apply] using h
  have hind := individual_of_paired_character_sums q t (ε*Complex.I^k)
    (fun a z => (F ∣[(k : ℤ)] (translation (r a)*(fricke N hN)⁻¹)) z)
    (fun b z => (F ∣[(k : ℤ)] translation (r b)) z) (by
      intro χ z
      have h := congrFun (hall χ) z
      simp only [SlashAction.sum_slash,det_one_smul _ (det_one_inv _ (fricke_det N hN)),
        ← SlashAction.slash_mul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at h
      convert h using 1; ring)
  intro a
  funext z
  exact hind a z

#print axioms additive_laws_of_character_FE

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## TwoCosets -/
section

set_option autoImplicit false
@[expose] public section

namespace QuantitativeArithmeticPrimeSmallTwist

variable {G : Type*} [Group G]

/-- Adjoining a normalizing element whose square is in the subgroup gives
exactly two possible cosets. This supplies the group structure behind the
Fricke sign, without assuming generation or an index statement. -/
def twoCosetSubgroup (K : Subgroup G) (w : G)
    (hw : w ∈ Subgroup.normalizer (K : Set G)) (hsq : w * w ∈ K) : Subgroup G where
  carrier := {g | g ∈ K ∨ ∃ a ∈ K, g = a * w}
  one_mem' := Or.inl K.one_mem
  mul_mem' := by
    intro x y hx hy
    rcases hx with hx | ⟨a, ha, rfl⟩
    · rcases hy with hy | ⟨b, hb, rfl⟩
      · exact Or.inl (K.mul_mem hx hy)
      · exact Or.inr ⟨x * b, K.mul_mem hx hb, by group⟩
    · rcases hy with hy | ⟨b, hb, rfl⟩
      · have hc : w * y * w⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hw y).mp hy
        exact Or.inr ⟨a * (w * y * w⁻¹), K.mul_mem ha hc, by group⟩
      · have hc : w * b * w⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hw b).mp hb
        apply Or.inl
        have h := K.mul_mem (K.mul_mem ha hc) hsq
        convert h using 1; group
  inv_mem' := by
    intro x hx
    rcases hx with hx | ⟨a, ha, rfl⟩
    · exact Or.inl (K.inv_mem hx)
    · have hc : w⁻¹ * a⁻¹ * w ∈ K :=
        (Subgroup.mem_normalizer_iff''.mp hw a⁻¹).mp (K.inv_mem ha)
      refine Or.inr ⟨(w⁻¹ * a⁻¹ * w) * (w * w)⁻¹,
        K.mul_mem hc (K.inv_mem hsq), ?_⟩
      group

theorem closure_eq_twoCosetSubgroup (K : Subgroup G) (w : G)
    (hw : w ∈ Subgroup.normalizer (K : Set G)) (hsq : w * w ∈ K) :
    Subgroup.closure ((K : Set G) ∪ {w}) = twoCosetSubgroup K w hw hsq := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · have hxw : x = w := Set.mem_singleton_iff.mp hx
      subst x
      exact Or.inr ⟨1, K.one_mem, (one_mul w).symm⟩
  · intro x hx
    have hK : K ≤ Subgroup.closure ((K : Set G) ∪ {w}) :=
      fun _ ha => Subgroup.subset_closure (Or.inl ha)
    have hw' : w ∈ Subgroup.closure ((K : Set G) ∪ {w}) :=
      Subgroup.subset_closure (Or.inr (Set.mem_singleton w))
    rcases hx with hx | ⟨a, ha, rfl⟩
    · exact hK hx
    · exact Subgroup.mul_mem _ (hK ha) hw'

theorem mem_closure_iff_two_cosets (K : Subgroup G) (w : G)
    (hw : w ∈ Subgroup.normalizer (K : Set G)) (hsq : w * w ∈ K) (g : G) :
    g ∈ Subgroup.closure ((K : Set G) ∪ {w}) ↔
      g ∈ K ∨ ∃ a ∈ K, g = a * w := by
  rw [closure_eq_twoCosetSubgroup K w hw hsq]
  rfl

#print axioms closure_eq_twoCosetSubgroup
#print axioms mem_closure_iff_two_cosets

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## FrickeGroup -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix AsymptoticCongruenceLabels
open scoped MatrixGroups

def realGamma0 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (SpecialLinearGroup.mapGL ℝ)

/-- The determinant-one Fricke extension, as an actual matrix subgroup. -/
def frickeExtension (N : ℕ) (hN : 0 < N) : Subgroup (GL (Fin 2) ℝ) :=
  Subgroup.closure ((realGamma0 N : Set (GL (Fin 2) ℝ)) ∪
    {SmallLevelNormalized.fricke N hN})

theorem normalized_fricke_intertwine (N : ℕ) (hN : 0 < N)
    (A : SL(2, ℤ)) (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    SmallLevelNormalized.fricke N hN * SpecialLinearGroup.mapGL ℝ A =
      SpecialLinearGroup.mapGL ℝ (frickeConjugate N A c hc) *
        SmallLevelNormalized.fricke N hN := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  apply Units.ext
  change (SmallLevelNormalized.fricke N hN).val * A.val.map (fun z : ℤ => (z : ℝ)) =
    (frickeConjugate N A c hc).val.map (fun z : ℤ => (z : ℝ)) *
      (SmallLevelNormalized.fricke N hN).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SmallLevelNormalized.fricke, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, frickeConjugate, Matrix.mul_apply,
      Fin.sum_univ_two, hc]
  all_goals field_simp [hs]
  all_goals ring_nf
  all_goals simp [hsq, mul_comm]

/-- A one-sided conjugation inclusion becomes equality when the square
of the conjugating element already lies in the subgroup. -/
theorem normalizer_of_square_mem {G : Type*} [Group G] (K : Subgroup G) (w : G)
    (hsq : w * w ∈ K) (hconj : ∀ a ∈ K, w * a * w⁻¹ ∈ K) :
    w ∈ Subgroup.normalizer (K : Set G) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro a
  refine ⟨hconj a, ?_⟩
  intro ha
  have h := hconj (w * a * w⁻¹) ha
  have h' := K.mul_mem (K.mul_mem (K.inv_mem hsq) h) hsq
  convert h' using 1; group

def integralMinusIdentity : SL(2, ℤ) :=
  ⟨!![-1, 0; 0, -1], by norm_num [det_fin_two]⟩

theorem integralMinusIdentity_mem (N : ℕ) :
    integralMinusIdentity ∈ CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_dvd]
  exact dvd_zero _

theorem normalized_fricke_square (N : ℕ) (hN : 0 < N) :
    SmallLevelNormalized.fricke N hN * SmallLevelNormalized.fricke N hN =
      SpecialLinearGroup.mapGL ℝ integralMinusIdentity := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SmallLevelNormalized.fricke, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, integralMinusIdentity,
      SpecialLinearGroup.mapGL, Matrix.mul_apply, Fin.sum_univ_two, hs]
  all_goals field_simp [hs]

theorem normalized_fricke_square_mem (N : ℕ) (hN : 0 < N) :
    SmallLevelNormalized.fricke N hN * SmallLevelNormalized.fricke N hN ∈
      realGamma0 N := by
  rw [normalized_fricke_square]
  exact ⟨integralMinusIdentity, integralMinusIdentity_mem N, rfl⟩

theorem normalized_fricke_normalizes (N : ℕ) (hN : 0 < N) :
    SmallLevelNormalized.fricke N hN ∈
      Subgroup.normalizer (realGamma0 N : Set (GL (Fin 2) ℝ)) := by
  apply normalizer_of_square_mem _ _ (normalized_fricke_square_mem N hN)
  rintro g ⟨A, hA, rfl⟩
  obtain ⟨c, hc⟩ := (gamma0_mem_dvd N A).mp hA
  rw [normalized_fricke_intertwine N hN A c hc, mul_inv_cancel_right]
  exact ⟨frickeConjugate N A c hc, frickeConjugate_mem N A c hc, rfl⟩

theorem mem_frickeExtension_iff (N : ℕ) (hN : 0 < N) (g : GL (Fin 2) ℝ) :
    g ∈ frickeExtension N hN ↔
      g ∈ realGamma0 N ∨ ∃ a ∈ realGamma0 N,
        g = a * SmallLevelNormalized.fricke N hN :=
  mem_closure_iff_two_cosets _ _ (normalized_fricke_normalizes N hN)
    (normalized_fricke_square_mem N hN) g

#print axioms normalized_fricke_intertwine
#print axioms normalized_fricke_normalizes
#print axioms mem_frickeExtension_iff

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Approximation -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

/-- The sharp Dirichlet bound gives an open isometric-interval cover whenever
the radius parameter is strictly below the next integer. -/
theorem exists_small_denominator_circle (x R : ℝ) (Q : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hRQ : R < (Q : ℝ) + 1) :
    ∃ a : ℚ, a.den ≤ Q ∧ |x - (a : ℝ)| < 1 / (R * (a.den : ℝ)) := by
  obtain ⟨a, ha, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hQ
  refine ⟨a, hden, ha.trans_lt ?_⟩
  have hd : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  exact one_div_lt_one_div_of_lt (mul_pos hR hd) (mul_lt_mul_of_pos_right hRQ hd)

theorem nat_sqrt_sq_lt_prime {p : ℕ} (hp : p.Prime) :
    p.sqrt * p.sqrt < p := by
  have hle := Nat.sqrt_le p
  have hlt := Nat.sqrt_lt_self hp.one_lt
  by_contra hn
  have heq : p.sqrt * p.sqrt = p := by omega
  have hd : p.sqrt ∣ p := ⟨p.sqrt, heq.symm⟩
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · rw [h] at heq
    norm_num at heq
    exact hp.ne_one heq.symm
  · omega

theorem nat_sqrt_lt_real_sqrt_prime {p : ℕ} (hp : p.Prime) :
    (p.sqrt : ℝ) < Real.sqrt p := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have hn := Real.sqrt_nonneg (p : ℝ)
  have hlt : (p.sqrt : ℝ) * p.sqrt < p := by
    exact_mod_cast nat_sqrt_sq_lt_prime hp
  nlinarith

theorem real_sqrt_lt_nat_sqrt_add_one (p : ℕ) :
    Real.sqrt p < (p.sqrt : ℝ) + 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have hn := Real.sqrt_nonneg (p : ℝ)
  have hlt : (p : ℝ) < ((p.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' p
  have hq : (0 : ℝ) ≤ p.sqrt := by positivity
  nlinarith

/-- Every real point lies strictly inside an available prime-level circle.
The denominator is genuinely below sqrt(p) and coprime to p. -/
theorem prime_circle_cover {p : ℕ} (hp : p.Prime) (x : ℝ) :
    ∃ a : ℚ, a.den ≤ p.sqrt ∧ (a.den : ℝ) < Real.sqrt p ∧
      p.Coprime a.den ∧
      |x - (a : ℝ)| < 1 / (Real.sqrt p * (a.den : ℝ)) := by
  obtain ⟨a, hden, ha⟩ := exists_small_denominator_circle x (Real.sqrt p) p.sqrt
    (Nat.sqrt_pos.mpr hp.pos) (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos))
    (real_sqrt_lt_nat_sqrt_add_one p)
  have hdp : a.den < p := hden.trans_lt (Nat.sqrt_lt_self hp.one_lt)
  refine ⟨a, hden, ?_, Nat.coprime_of_lt_prime a.pos.ne' hdp hp, ha⟩
  exact (show (a.den : ℝ) ≤ p.sqrt by exact_mod_cast hden).trans_lt
    (nat_sqrt_lt_real_sqrt_prime hp)

#print axioms exists_small_denominator_circle
#print axioms prime_circle_cover

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Height -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

/-- The sharp approximation theorem in the lower-row coordinates of an
isometric circle. The rational is reduced by its actual numerator/denominator. -/
theorem exists_small_denominator_residual (x : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ a : ℚ, a.den ≤ Q ∧
      |(a.den : ℝ) * x - a.num| ≤ 1 / ((Q : ℝ) + 1) := by
  obtain ⟨a, ha, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hQ
  refine ⟨a, hden, ?_⟩
  have hd : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have hQ' : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have heq : (a.den : ℝ) * x - a.num = (a.den : ℝ) * (x - (a : ℝ)) := by
    rw [Rat.cast_def]
    field_simp
  rw [heq, abs_mul, abs_of_pos hd]
  calc
    (a.den : ℝ) * |x - (a : ℝ)| ≤
        (a.den : ℝ) * (1 / (((Q : ℝ) + 1) * a.den)) :=
      mul_le_mul_of_nonneg_left ha hd.le
    _ = 1 / ((Q : ℝ) + 1) := by field_simp

/-- Explicit positive squared-height threshold. -/
def heightThresholdSq (P Q : ℝ) : ℝ :=
  (1 / P - 1 / (Q + 1) ^ 2) / Q ^ 2

theorem heightThresholdSq_pos {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (hPQ : P < (Q + 1) ^ 2) : 0 < heightThresholdSq P Q := by
  unfold heightThresholdSq
  apply div_pos
  · exact sub_pos.mpr (one_div_lt_one_div_of_lt hP hPQ)
  · positivity

/-- Arithmetic core of the maximum-height barrier. -/
theorem height_sq_lower_of_residual {P Q q r y : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hq : 0 < q) (hqQ : q ≤ Q)
    (hr : |r| ≤ 1 / (Q + 1))
    (hexterior : 1 ≤ P * (r ^ 2 + q ^ 2 * y ^ 2)) :
    heightThresholdSq P Q ≤ y ^ 2 := by
  have hb : 0 ≤ 1 / (Q + 1) := by positivity
  have hrsq : r ^ 2 ≤ 1 / (Q + 1) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg r) hb).mpr hr
    simpa only [sq_abs, div_pow, one_pow] using h
  have hqsq : q ^ 2 ≤ Q ^ 2 := by nlinarith
  have hy := mul_le_mul_of_nonneg_right hqsq (sq_nonneg y)
  have hres := mul_le_mul_of_nonneg_left hrsq hP.le
  have hheight := mul_le_mul_of_nonneg_left hy hP.le
  have hcombined : 1 ≤ P * (1 / (Q + 1) ^ 2 + Q ^ 2 * y ^ 2) := by
    nlinarith
  unfold heightThresholdSq
  apply (div_le_iff₀ (sq_pos_of_pos hQ)).mpr
  have hone : 1 / P ≤ 1 / (Q + 1) ^ 2 + Q ^ 2 * y ^ 2 := by
    apply (div_le_iff₀ hP).mpr
    nlinarith [hcombined]
  nlinarith [hone]

/-- Every point exterior to all small-denominator prime-level circles has
an explicit positive lower bound on its squared height. -/
theorem prime_exterior_height {p : ℕ} (hp : p.Prime) (x y : ℝ)
    (hexterior : ∀ a : ℚ, a.den ≤ p.sqrt →
      1 ≤ (p : ℝ) * (((a.den : ℝ) * x - a.num) ^ 2 +
        (a.den : ℝ) ^ 2 * y ^ 2)) :
    0 < heightThresholdSq p p.sqrt ∧ heightThresholdSq p p.sqrt ≤ y ^ 2 := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hQ : (0 : ℝ) < p.sqrt := by exact_mod_cast Nat.sqrt_pos.mpr hp.pos
  have hPQ : (p : ℝ) < ((p.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' p
  refine ⟨heightThresholdSq_pos hP hQ hPQ, ?_⟩
  obtain ⟨a, ha, hr⟩ := exists_small_denominator_residual x p.sqrt
    (Nat.sqrt_pos.mpr hp.pos)
  exact height_sq_lower_of_residual hP hQ
    (by exact_mod_cast a.pos) (by exact_mod_cast ha) hr (hexterior a ha)

#print axioms exists_small_denominator_residual
#print axioms prime_exterior_height

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Orbit -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix UpperHalfPlane
open scoped MatrixGroups

/-- Finite many attained values above one reference value suffice for
attainment of a global maximum; the domain itself need not be finite. -/
theorem exists_max_of_finite_superlevel {α : Type*} (f : α → ℝ) (a₀ : α)
    (hfin : {r : ℝ | (∃ a, f a = r) ∧ f a₀ ≤ r}.Finite) :
    ∃ a : α, ∀ b : α, f b ≤ f a := by
  classical
  let s := hfin.toFinset
  have hmem : f a₀ ∈ s := by
    exact hfin.mem_toFinset.mpr ⟨⟨a₀, rfl⟩, le_rfl⟩
  obtain ⟨r, hr, hmax⟩ := s.exists_max_image (fun r : ℝ => r) ⟨_, hmem⟩
  obtain ⟨⟨a, ha⟩, hra⟩ := hfin.mem_toFinset.mp hr
  refine ⟨a, fun b => ?_⟩
  by_cases hb : f a₀ ≤ f b
  · have hbmem : f b ∈ s := hfin.mem_toFinset.mpr ⟨⟨b, rfl⟩, hb⟩
    simpa only [ha] using hmax (f b) hbmem
  · exact (not_le.mp hb).le.trans (ha ▸ hra)

/-- The precise real lower-row formula used in the geometric proof. -/
theorem det_one_height (g : GL (Fin 2) ℝ)
    (hg : (g.det : ℝ) = 1) (z : ℍ) :
    (g • z).im = z.im /
      ((g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2) := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq, hg, abs_one, one_mul]
  congr 1
  simp [UpperHalfPlane.denom, Complex.normSq_apply, pow_two]

/-- An element cannot increase a maximum-height point precisely when the
squared norm of its lower-row denominator is at least one. -/
theorem denominator_sq_ge_one_of_height_max (g : GL (Fin 2) ℝ)
    (hg : (g.det : ℝ) = 1) (z : ℍ) (hmax : (g • z).im ≤ z.im) :
    1 ≤ (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 := by
  have hden : 0 < (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 := by
    have h := UpperHalfPlane.normSq_denom_pos g z.im_ne_zero
    simpa [UpperHalfPlane.denom, Complex.normSq_apply, pow_two] using h
  rw [det_one_height g hg z] at hmax
  have h := (div_le_iff₀ hden).mp hmax
  nlinarith [z.im_pos]

/-- The actual small prime-level circles force the explicit height barrier
at a maximum-height orbit representative. -/
theorem prime_orbit_max_height {p : ℕ} (hp : p.Prime)
    (H : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ g ∈ H, (g.det : ℝ) = 1)
    (hcircles : ∀ a : ℚ, a.den ≤ p.sqrt →
      ∃ g ∈ H, g 1 0 = Real.sqrt p * a.den ∧
        g 1 1 = -(Real.sqrt p * a.num))
    (z : ℍ) (hmax : ∀ g ∈ H, (g • z).im ≤ z.im) :
    0 < heightThresholdSq p p.sqrt ∧
      heightThresholdSq p p.sqrt ≤ z.im ^ 2 := by
  apply prime_exterior_height hp z.re z.im
  intro a ha
  obtain ⟨g, hg, hc, hd⟩ := hcircles a ha
  have h := denominator_sq_ge_one_of_height_max g (hdet g hg) z (hmax g hg)
  rw [hc, hd] at h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have hid : (Real.sqrt p * a.den * z.re + -(Real.sqrt p * a.num)) ^ 2 +
      (Real.sqrt p * a.den * z.im) ^ 2 = (Real.sqrt p) ^ 2 *
        (((a.den : ℝ) * z.re - a.num) ^ 2 + (a.den : ℝ) ^ 2 * z.im ^ 2) := by ring
  rw [hid, hs] at h
  exact h

#print axioms exists_max_of_finite_superlevel
#print axioms prime_orbit_max_height

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Rows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix AsymptoticCongruenceLabels
open scoped MatrixGroups

theorem realGamma0_det (N : ℕ) (g : GL (Fin 2) ℝ) (hg : g ∈ realGamma0 N) :
    (g.det : ℝ) = 1 := by
  obtain ⟨A, _, rfl⟩ := hg
  exact congrArg (fun u : ℝˣ => (u : ℝ))
    (SpecialLinearGroup.det_mapGL (S := ℝ) A)

theorem frickeExtension_det (N : ℕ) (hN : 0 < N) (g : GL (Fin 2) ℝ)
    (hg : g ∈ frickeExtension N hN) : (g.det : ℝ) = 1 := by
  rcases (mem_frickeExtension_iff N hN g).mp hg with hg | ⟨a, ha, rfl⟩
  · exact realGamma0_det N g hg
  · simp only [map_mul, Units.val_mul, realGamma0_det N a ha,
      SmallLevelNormalized.fricke_det, one_mul]

theorem integral_fricke_lower_row (N : ℕ) (hN : 0 < N)
    (A : SL(2, ℤ)) (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    (SpecialLinearGroup.mapGL ℝ A * SmallLevelNormalized.fricke N hN) 1 0 =
        Real.sqrt N * (A 1 1 : ℝ) ∧
      (SpecialLinearGroup.mapGL ℝ A * SmallLevelNormalized.fricke N hN) 1 1 =
        -(Real.sqrt N * (c : ℝ)) := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  constructor
  · change ((A.val.map (fun z : ℤ => (z : ℝ))) *
        (SmallLevelNormalized.fricke N hN).val) 1 0 = _
    simp [SmallLevelNormalized.fricke, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  · change ((A.val.map (fun z : ℤ => (z : ℝ))) *
        (SmallLevelNormalized.fricke N hN).val) 1 1 = _
    simp [SmallLevelNormalized.fricke, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two, hc]
    field_simp [hs]
    ring_nf
    simp [hsq, mul_comm]

/-- The lower rows lie in precisely the two lattices used by the height
argument. No discreteness hypothesis is imposed on the Fricke extension. -/
theorem frickeExtension_lower_rows (N : ℕ) (hN : 0 < N) (g : GL (Fin 2) ℝ)
    (hg : g ∈ frickeExtension N hN) :
    (∃ c d : ℤ, g 1 0 = (N : ℝ) * c ∧ g 1 1 = (d : ℝ)) ∨
      (∃ c d : ℤ, g 1 0 = Real.sqrt N * d ∧
        g 1 1 = -(Real.sqrt N * c)) := by
  rcases (mem_frickeExtension_iff N hN g).mp hg with hg | ⟨a, ha, rfl⟩
  · obtain ⟨A, hA, rfl⟩ := hg
    obtain ⟨c, hc⟩ := (gamma0_mem_dvd N A).mp hA
    refine Or.inl ⟨c, A 1 1, ?_, rfl⟩
    change (A 1 0 : ℝ) = (N : ℝ) * (c : ℝ)
    exact_mod_cast hc
  · obtain ⟨A, hA, rfl⟩ := ha
    obtain ⟨c, hc⟩ := (gamma0_mem_dvd N A).mp hA
    exact Or.inr ⟨c, A 1 1, integral_fricke_lower_row N hN A c hc⟩

theorem int_sq_ge_one {a : ℤ} (ha : a ≠ 0) : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
  have h : (1 : ℤ) ≤ a ^ 2 := by
    have hpos := sq_pos_of_ne_zero ha
    omega
  exact_mod_cast h

/-- The concrete nonzero lower-left gap, uniform over the actual group. -/
theorem frickeExtension_lower_left_gap (N : ℕ) (hN : 0 < N)
    (g : GL (Fin 2) ℝ) (hg : g ∈ frickeExtension N hN) (hc : g 1 0 ≠ 0) :
    (N : ℝ) ≤ (g 1 0) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases frickeExtension_lower_rows N hN g hg with
    ⟨c, d, hgc, _⟩ | ⟨c, d, hgd, _⟩
  · have hc0 : c ≠ 0 := by intro h; apply hc; simp [hgc, h]
    have h := mul_le_mul_of_nonneg_left (int_sq_ge_one hc0) (sq_nonneg (N : ℝ))
    rw [hgc]
    nlinarith
  · have hd0 : d ≠ 0 := by intro h; apply hc; simp [hgd, h]
    have h := mul_le_mul_of_nonneg_left (int_sq_ge_one hd0)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    rw [hgd, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    simpa only [mul_one] using h

#print axioms frickeExtension_det
#print axioms frickeExtension_lower_rows
#print axioms frickeExtension_lower_left_gap

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## RowFiniteness -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

theorem finite_int_abs_le (B : ℝ) : {n : ℤ | |(n : ℝ)| ≤ B}.Finite := by
  apply (Set.finite_Icc (-⌈B⌉) ⌈B⌉).subset
  intro n hn
  have hB := Int.le_ceil B
  constructor
  · have h := (neg_le_neg hB).trans (abs_le.mp hn).1
    exact_mod_cast h
  · have h := (abs_le.mp hn).2.trans hB
    exact_mod_cast h

/-- A lower row with denominator norm at most one lies in an explicit
bounded rectangle. This estimate only uses positive height. -/
theorem lower_row_bounds {x y c d : ℝ} (hy : 0 < y)
    (h : (c*x+d)^2+(c*y)^2 ≤ 1) :
    |c| ≤ 1/y ∧ |d| ≤ 1+|x|/y := by
  have hcy : |c*y| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (c*x+d)]
  have hc : |c| ≤ 1/y := by
    apply (le_div_iff₀ hy).mpr
    simpa only [abs_mul, abs_of_pos hy] using hcy
  have hs : |c*x+d| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (c*y)]
  refine ⟨hc, ?_⟩
  calc
    |d| = |(c*x+d)-c*x| := by congr 1; ring
    _ ≤ |c*x+d|+|c*x| := abs_sub _ _
    _ ≤ 1+(1/y)*|x| := add_le_add hs (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg x))
    _ = 1+|x|/y := by ring

/-- Every diagonal real rescaling of the integer lattice has only finitely
many lower rows with bounded denominator at a fixed upper-half-plane point. -/
theorem finite_lattice_rows (α β x y : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hy : 0 < y) :
    {r : ℝ × ℝ | (∃ a b : ℤ, r = (α*a, β*b)) ∧
      (r.1*x+r.2)^2+(r.1*y)^2 ≤ 1}.Finite := by
  let A : Set ℤ := {a | |(a : ℝ)| ≤ (1/y)/α}
  let B : Set ℤ := {b | |(b : ℝ)| ≤ (1+|x|/y)/β}
  have hA : A.Finite := finite_int_abs_le _
  have hB : B.Finite := finite_int_abs_le _
  have hprod := (hA.prod hB).image (fun u : ℤ × ℤ => (α*u.1, β*u.2))
  apply hprod.subset
  rintro r ⟨⟨a,b,rfl⟩,hr⟩
  obtain ⟨ha,hb⟩ := lower_row_bounds hy hr
  refine ⟨(a,b), ⟨?_, ?_⟩, rfl⟩
  · change |(a : ℝ)| ≤ (1/y)/α
    apply (le_div_iff₀ hα).mpr
    simpa only [abs_mul, abs_of_pos hα, mul_comm] using ha
  · change |(b : ℝ)| ≤ (1+|x|/y)/β
    apply (le_div_iff₀ hβ).mpr
    simpa only [abs_mul, abs_of_pos hβ, mul_comm] using hb

#print axioms finite_lattice_rows
#print axioms lower_row_bounds

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## HeightFiniteness -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix UpperHalfPlane
open scoped MatrixGroups

theorem frickeExtension_finite_lower_rows (N : ℕ) (hN : 0 < N) (z : ℍ) :
    {r : ℝ × ℝ | (∃ g ∈ frickeExtension N hN, r = (g 1 0, g 1 1)) ∧
      (r.1*z.re+r.2)^2+(r.1*z.im)^2 ≤ 1}.Finite := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := Real.sqrt_pos.mpr hNr
  have h₁ := finite_lattice_rows (N : ℝ) 1 z.re z.im hNr zero_lt_one z.im_pos
  have h₂ := finite_lattice_rows (Real.sqrt N) (Real.sqrt N) z.re z.im hs hs z.im_pos
  apply (h₁.union h₂).subset
  rintro r ⟨⟨g,hg,rfl⟩,hr⟩
  rcases frickeExtension_lower_rows N hN g hg with
    ⟨c,d,hc,hd⟩ | ⟨c,d,hc,hd⟩
  · left
    refine ⟨⟨c,d,?_⟩,hr⟩
    simp only [hc,hd,one_mul]
  · right
    refine ⟨⟨d,-c,?_⟩,hr⟩
    simp only [hc,hd,Int.cast_neg,mul_neg]

theorem denominator_sq_le_one_of_height_increase (g : GL (Fin 2) ℝ)
    (hg : (g.det : ℝ) = 1) (z : ℍ) (h : z.im ≤ (g • z).im) :
    (g 1 0*z.re+g 1 1)^2+(g 1 0*z.im)^2 ≤ 1 := by
  have hden : 0 < (g 1 0*z.re+g 1 1)^2+(g 1 0*z.im)^2 := by
    have hpos := UpperHalfPlane.normSq_denom_pos g z.im_ne_zero
    simpa [UpperHalfPlane.denom, Complex.normSq_apply, pow_two] using hpos
  rw [det_one_height g hg z] at h
  have hh := (le_div_iff₀ hden).mp h
  nlinarith [z.im_pos]

/-- The finite-superlevel input of the height argument follows from the
two explicit row lattices of the actual Fricke extension. -/
theorem frickeExtension_finite_height_superlevel (N : ℕ) (hN : 0 < N)
    (H : Subgroup (GL (Fin 2) ℝ)) (hH : H ≤ frickeExtension N hN) (z : ℍ) :
    {r : ℝ | (∃ g : H, ((g : GL (Fin 2) ℝ) • z).im = r) ∧ z.im ≤ r}.Finite := by
  let φ : ℝ × ℝ → ℝ := fun r =>
    z.im / ((r.1*z.re+r.2)^2+(r.1*z.im)^2)
  apply ((frickeExtension_finite_lower_rows N hN z).image φ).subset
  rintro r ⟨⟨g,hg⟩,hr⟩
  have hmem := hH g.property
  have hdet := frickeExtension_det N hN g hmem
  refine ⟨((g : GL (Fin 2) ℝ) 1 0, (g : GL (Fin 2) ℝ) 1 1), ?_, ?_⟩
  · refine ⟨⟨g,hmem,rfl⟩,?_⟩
    exact denominator_sq_le_one_of_height_increase g hdet z (hg ▸ hr)
  · exact (det_one_height g hdet z).symm.trans hg

#print axioms frickeExtension_finite_height_superlevel

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Stabilizer -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix AsymptoticCongruenceLabels
open scoped MatrixGroups

/-- Denominator-one branches and Fricke already contain the entire
stabilizer of infinity. The assertion holds at every level greater than one. -/
theorem frickeExtension_stabilizer_mem (N : ℕ) (hN : 1 < N)
    (H : Subgroup (GL (Fin 2) ℝ))
    (hw : SmallLevelNormalized.fricke N (by omega) ∈ H)
    (hsmall : ∀ A : SL(2, ℤ), A ∈ CongruenceSubgroup.Gamma0 N →
      A 1 1 = 1 → SpecialLinearGroup.mapGL ℝ A ∈ H)
    (g : GL (Fin 2) ℝ) (hg : g ∈ frickeExtension N (by omega))
    (hc : g 1 0 = 0) : g ∈ H := by
  have hminus : SpecialLinearGroup.mapGL ℝ integralMinusIdentity ∈ H := by
    rw [← normalized_fricke_square N (by omega)]
    exact H.mul_mem hw hw
  rcases (mem_frickeExtension_iff N (by omega) g).mp hg with hg | ⟨a,ha,rfl⟩
  · obtain ⟨A,hA,rfl⟩ := hg
    have hcA : A 1 0 = 0 := by
      change (A 1 0 : ℝ) = 0 at hc
      exact_mod_cast hc
    have hd := A.property
    rw [det_fin_two] at hd
    change A 0 0*A 1 1-A 0 1*A 1 0=1 at hd
    rw [hcA, mul_zero, sub_zero] at hd
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨_,hd⟩ | ⟨_,hd⟩
    · exact hsmall A hA hd
    · let B := integralMinusIdentity * A
      have hB : B ∈ CongruenceSubgroup.Gamma0 N :=
        (CongruenceSubgroup.Gamma0 N).mul_mem (integralMinusIdentity_mem N) hA
      have hdB : B 1 1 = 1 := by
        simp [B, integralMinusIdentity, Matrix.mul_apply, Fin.sum_univ_two, hd]
      have hh := hsmall B hB hdB
      change SpecialLinearGroup.mapGL ℝ (integralMinusIdentity*A) ∈ H at hh
      rw [map_mul] at hh
      simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem hminus) hh
  · obtain ⟨A,hA,rfl⟩ := ha
    obtain ⟨c,hcA⟩ := (gamma0_mem_dvd N A).mp hA
    have hrow := (integral_fricke_lower_row N (by omega) A c hcA).1
    have hs : Real.sqrt (N : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
    have hdA : A 1 1 = 0 := by
      rw [hrow] at hc
      have hh := (mul_eq_zero.mp hc).resolve_left hs
      exact_mod_cast hh
    have hd := A.property
    rw [det_fin_two] at hd
    change A 0 0*A 1 1-A 0 1*A 1 0=1 at hd
    rw [hdA,hcA] at hd
    have hunit : (N : ℤ) * (-A 0 1*c) = 1 := by nlinarith [hd]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h <;> omega

#print axioms frickeExtension_stabilizer_mem

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Generation -/
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix UpperHalfPlane
open scoped MatrixGroups

/-- An explicit height bound on the imaginary axis when the lower-left
entry is separated from zero. -/
theorem height_imaginary_axis_le (g : GL (Fin 2) ℝ)
    (hg : (g.det : ℝ) = 1) {P Y : ℝ} (hP : 0 < P) (hY : 0 < Y)
    (hc : P ≤ (g 1 0) ^ 2) :
    (g • (⟨⟨0, Y⟩, hY⟩ : ℍ)).im ≤ 1 / (P * Y) := by
  rw [det_one_height g hg]
  change Y / ((g 1 0 * 0 + g 1 1) ^ 2 + (g 1 0 * Y) ^ 2) ≤ _
  have hden : P * Y ^ 2 ≤ (g 1 0 * 0 + g 1 1) ^ 2 + (g 1 0 * Y) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hc (sq_nonneg Y)
    nlinarith [sq_nonneg (g 1 1)]
  calc
    _ ≤ Y / (P * Y ^ 2) :=
      div_le_div_of_nonneg_left hY.le (mul_pos hP (sq_pos_of_pos hY)) hden
    _ = 1 / (P * Y) := by field_simp

/-- The geometric generation step, proved from explicit matrix and
finiteness hypotheses. This is not yet the arithmetic specialization to
Gamma_0(p) and its Fricke extension. -/
theorem eq_of_prime_circles {p : ℕ} (hp : p.Prime)
    (H G : Subgroup (GL (Fin 2) ℝ)) (hHG : H ≤ G)
    (hdet : ∀ g ∈ G, (g.det : ℝ) = 1)
    (hfinite : ∀ z : ℍ,
      {r : ℝ | (∃ g : H, ((g : GL (Fin 2) ℝ) • z).im = r) ∧ z.im ≤ r}.Finite)
    (hstabilizer : ∀ g ∈ G, g 1 0 = 0 → g ∈ H)
    (hgap : ∀ g ∈ G, g 1 0 ≠ 0 → (p : ℝ) ≤ (g 1 0) ^ 2)
    (hcircles : ∀ a : ℚ, a.den ≤ p.sqrt →
      ∃ g ∈ H, g 1 0 = Real.sqrt p * a.den ∧
        g 1 1 = -(Real.sqrt p * a.num)) : H = G := by
  apply le_antisymm hHG
  intro g hg
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hQ : (0 : ℝ) < p.sqrt := by exact_mod_cast Nat.sqrt_pos.mpr hp.pos
  have hPQ : (p : ℝ) < ((p.sqrt : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' p
  let D := heightThresholdSq p p.sqrt
  have hD : 0 < D := heightThresholdSq_pos hP hQ hPQ
  let δ := Real.sqrt D
  have hδ : 0 < δ := Real.sqrt_pos.mpr hD
  have hδsq : δ ^ 2 = D := Real.sq_sqrt hD.le
  let Y := 1 / ((p : ℝ) * δ) + 1
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hsmall : 1 / ((p : ℝ) * Y) < δ := by
    apply (div_lt_iff₀ (mul_pos hP hY)).mpr
    have heq : δ * ((p : ℝ) * Y) = 1 + (p : ℝ) * δ := by
      dsimp [Y]
      field_simp
    rw [heq]
    linarith [mul_pos hP hδ]
  let z : ℍ := ⟨⟨0, Y⟩, hY⟩
  let F : H → ℝ := fun h => ((h : GL (Fin 2) ℝ) • (g • z)).im
  have hfin : {r : ℝ | (∃ h, F h = r) ∧ F 1 ≤ r}.Finite := by
    simpa only [F, OneMemClass.coe_one, one_smul] using hfinite (g • z)
  obtain ⟨h, hh⟩ := exists_max_of_finite_superlevel F 1 hfin
  let z' := (h : GL (Fin 2) ℝ) • (g • z)
  have hmax : ∀ k ∈ H, (k • z').im ≤ z'.im := by
    intro k hk
    simpa only [F, z', Subgroup.coe_mul, mul_smul] using hh (⟨k, hk⟩ * h)
  have hbarrier := (prime_orbit_max_height hp H
    (fun k hk => hdet k (hHG hk)) hcircles z' hmax).2
  have hprodG : (h : GL (Fin 2) ℝ) * g ∈ G := G.mul_mem (hHG h.property) hg
  have hc : ((h : GL (Fin 2) ℝ) * g) 1 0 = 0 := by
    by_contra hc
    have hbound := height_imaginary_axis_le ((h : GL (Fin 2) ℝ) * g)
      (hdet _ hprodG) hP hY (hgap _ hprodG hc)
    have hzlt : z'.im < δ := by
      apply lt_of_le_of_lt ?_ hsmall
      simpa only [z', z, mul_smul] using hbound
    have hzpos := z'.im_pos
    change D ≤ z'.im ^ 2 at hbarrier
    nlinarith [hδsq]
  have hprodH := hstabilizer _ hprodG hc
  have hmem := H.mul_mem (H.inv_mem h.property) hprodH
  simpa only [inv_mul_cancel_left] using hmem

#print axioms height_imaginary_axis_le
#print axioms eq_of_prime_circles

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Matrices -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix

def translationMatrix (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, x; 0, 1]

def frickeMatrix (N : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; N, 0]

def branchMatrix (N q a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + N * a * b) / q, a; N * b, q]

theorem branchMatrix_det (N q a b : ℝ) (hq : q ≠ 0) :
    (branchMatrix N q a b).det = 1 := by
  rw [Matrix.det_fin_two]
  change (1 + N * a * b) / q * q - a * (N * b) = 1
  field_simp [hq]
  ring

set_option linter.unnecessarySeqFocus false in
/-- Exact additive-twist matrix identity, before dropping the positive
scalar in the determinant-normalized slash action. -/
theorem additive_fricke_matrix_identity (N q a b : ℝ) (hq : q ≠ 0) :
    translationMatrix (a / q) * frickeMatrix (N * q ^ 2) =
      q • (branchMatrix N q a b * frickeMatrix N * translationMatrix (b / q)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translationMatrix, frickeMatrix, branchMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply] <;> field_simp [hq] <;> ring <;> simp

/-- Bezout supplies an integral small-denominator branch for every reduced
rational center; primality is used only to make its denominator coprime to p. -/
theorem prime_circle_integer_witness {p : ℕ} (hp : p.Prime)
    (a : ℚ) (ha : a.den ≤ p.sqrt) :
    ∃ A u : ℤ, A * a.den - (p : ℤ) * u * a.num = 1 := by
  have hdp : a.den < p := ha.trans_lt (Nat.sqrt_lt_self hp.one_lt)
  have hcop : IsCoprime (a.den : ℤ) (p : ℤ) :=
    (Nat.coprime_of_lt_prime a.pos.ne' hdp hp).symm.isCoprime
  have hred : IsCoprime (a.den : ℤ) a.num := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa only [Int.gcd_def, Int.natAbs_natCast] using a.reduced.symm.gcd_eq_one
  obtain ⟨A, v, hv⟩ := hcop.mul_right hred
  refine ⟨A, -v, ?_⟩
  nlinarith [hv]

/-- The integral witness has determinant one, with lower-left entry a
multiple of p and prescribed lower-right denominator. -/
theorem integer_branch_det {p q A u b : ℤ} (h : A * q - p * u * b = 1) :
    (Matrix.det !![A, u; p * b, q]) = 1 := by
  rw [Matrix.det_fin_two]
  change A * q - u * (p * b) = 1
  nlinarith [h]

#print axioms additive_fricke_matrix_identity
#print axioms prime_circle_integer_witness

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## ConcreteGeneration -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix AsymptoticCongruenceLabels
open scoped MatrixGroups

/-- All integral branches of positive bottom-right denominator at most Q. -/
def smallDenominatorBranches (N Q : ℕ) : Set (GL (Fin 2) ℝ) :=
  {g | ∃ A : SL(2, ℤ), A ∈ CongruenceSubgroup.Gamma0 N ∧
    1 ≤ A 1 1 ∧ A 1 1 ≤ (Q : ℤ) ∧ g = SpecialLinearGroup.mapGL ℝ A}

def smallFrickeGroup (p : ℕ) (hp : 0 < p) : Subgroup (GL (Fin 2) ℝ) :=
  Subgroup.closure (smallDenominatorBranches p p.sqrt ∪
    {SmallLevelNormalized.fricke p hp})

theorem smallFrickeGroup_le (p : ℕ) (hp : 0 < p) :
    smallFrickeGroup p hp ≤ frickeExtension p hp := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨A,hA,_,_,rfl⟩ | hg
  · exact Subgroup.subset_closure (Or.inl ⟨A,hA,rfl⟩)
  · exact Subgroup.subset_closure (Or.inr hg)

theorem smallFrickeGroup_fricke (p : ℕ) (hp : 0 < p) :
    SmallLevelNormalized.fricke p hp ∈ smallFrickeGroup p hp :=
  Subgroup.subset_closure (Or.inr rfl)

theorem smallFrickeGroup_branch (p : ℕ) (hp : 0 < p) (A : SL(2, ℤ))
    (hA : A ∈ CongruenceSubgroup.Gamma0 p) (hpos : 1 ≤ A 1 1)
    (hbound : A 1 1 ≤ (p.sqrt : ℤ)) :
    SpecialLinearGroup.mapGL ℝ A ∈ smallFrickeGroup p hp :=
  Subgroup.subset_closure (Or.inl ⟨A,hA,hpos,hbound,rfl⟩)

theorem smallFrickeGroup_circles {p : ℕ} (hp : p.Prime)
    (a : ℚ) (ha : a.den ≤ p.sqrt) :
    ∃ g ∈ smallFrickeGroup p hp.pos,
      g 1 0 = Real.sqrt p*a.den ∧ g 1 1 = -(Real.sqrt p*a.num) := by
  obtain ⟨A,u,hu⟩ := prime_circle_integer_witness hp a ha
  let B : SL(2, ℤ) :=
    ⟨!![A,u;(p : ℤ)*a.num,a.den], integer_branch_det hu⟩
  have hB : B ∈ CongruenceSubgroup.Gamma0 p := by
    rw [gamma0_mem_dvd]
    exact ⟨a.num,rfl⟩
  have hpos : 1 ≤ B 1 1 := by
    change (1 : ℤ) ≤ (a.den : ℤ)
    exact_mod_cast a.pos
  have hbound : B 1 1 ≤ (p.sqrt : ℤ) := by
    change (a.den : ℤ) ≤ (p.sqrt : ℤ)
    exact_mod_cast ha
  have hmem := smallFrickeGroup_branch p hp.pos B hB hpos hbound
  refine ⟨SpecialLinearGroup.mapGL ℝ B * SmallLevelNormalized.fricke p hp.pos,
    (smallFrickeGroup p hp.pos).mul_mem hmem (smallFrickeGroup_fricke p hp.pos), ?_⟩
  exact integral_fricke_lower_row p hp.pos B a.num rfl

/-- Concrete small-denominator generation at every prime level. All orbit
finiteness, stabilizer, lower-row gap and circle-cover inputs are proved. -/
theorem prime_small_denominator_generation {p : ℕ} (hp : p.Prime) :
    smallFrickeGroup p hp.pos = frickeExtension p hp.pos := by
  apply eq_of_prime_circles hp _ _ (smallFrickeGroup_le p hp.pos)
  · exact frickeExtension_det p hp.pos
  · exact frickeExtension_finite_height_superlevel p hp.pos _
      (smallFrickeGroup_le p hp.pos)
  · apply frickeExtension_stabilizer_mem p hp.one_lt _
      (smallFrickeGroup_fricke p hp.pos)
    intro A hA hd
    apply smallFrickeGroup_branch p hp.pos A hA (by omega)
    rw [hd]
    exact_mod_cast Nat.sqrt_pos.mpr hp.pos
  · exact frickeExtension_lower_left_gap p hp.pos
  · exact smallFrickeGroup_circles hp

#print axioms prime_small_denominator_generation

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Invariance -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix UpperHalfPlane SmallLevelNormalized AsymptoticCongruenceLabels
open scoped MatrixGroups ModularForm

theorem fricke_not_mem_realGamma0 (N : ℕ) (hN : 1 < N) :
    fricke N (by omega) ∉ realGamma0 N := by
  rintro ⟨A,hA,he⟩
  obtain ⟨c,hc⟩ := (gamma0_mem_dvd N A).mp hA
  have hrow := congrArg (fun g : GL (Fin 2) ℝ => g 1 0) he
  change (A 1 0 : ℝ) = Real.sqrt N at hrow
  rw [hc,Int.cast_mul,Int.cast_natCast] at hrow
  have hpos : (1 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hc0 : c ≠ 0 := by intro h; simp [h] at hrow; linarith
  have hsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hbound := mul_le_mul_of_nonneg_left (int_sq_ge_one hc0) (sq_nonneg (N : ℝ))
  have heq := congrArg (fun x : ℝ => x^2) hrow
  rw [mul_pow,hsq] at heq
  nlinarith

/-- Small-branch invariance and the specified Fricke eigenvalue imply
invariance under the full congruence group. The Fricke sign is retained;
it is not silently replaced by invariance under Fricke. -/
theorem invariant_of_small_branches {p : ℕ} (hp : p.Prime)
    (k : ℤ) (F : ℍ → ℂ) (ε : ℂ) (hε : ε*ε=1)
    (hw : F ∣[k] fricke p hp.pos=ε • F)
    (hsmall : ∀ g ∈ smallDenominatorBranches p p.sqrt, F ∣[k] g=F) :
    ∀ g ∈ realGamma0 p, F ∣[k] g=F := by
  let K := realGamma0 p ⊓ AsymptoticClassicalCusp.slashStabilizer k F
  let w := fricke p hp.pos
  have hwinv : ε • (F ∣[k] w⁻¹)=F := by
    have h := congrArg (fun f : ℍ → ℂ => f ∣[k] w⁻¹) hw
    rw [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,
      det_one_smul _ (det_one_inv _ (fricke_det p hp.pos))] at h
    exact h.symm
  have hsq : w*w ∈ K := by
    refine ⟨normalized_fricke_square_mem p hp.pos,?_⟩
    change F ∣[k] (w*w)=F
    rw [SlashAction.slash_mul,hw,det_one_smul _ (fricke_det p hp.pos),hw,
      smul_smul,hε,one_smul]
  have hconj : ∀ a ∈ K, w*a*w⁻¹ ∈ K := by
    intro a ha
    refine ⟨(Subgroup.mem_normalizer_iff.mp
      (normalized_fricke_normalizes p hp.pos) a).mp ha.1,?_⟩
    change F ∣[k] (w*a*w⁻¹)=F
    have hdet := realGamma0_det p a ha.1
    have hfix : F ∣[k] a=F := ha.2
    rw [SlashAction.slash_mul,SlashAction.slash_mul,hw,
      det_one_smul a hdet,hfix,
      det_one_smul _ (det_one_inv _ (fricke_det p hp.pos)),hwinv]
  have hnorm := normalizer_of_square_mem K w hsq hconj
  let H := twoCosetSubgroup K w hnorm hsq
  have hsmallH : smallFrickeGroup p hp.pos ≤ H := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with hg | hg
    · left
      obtain ⟨A,hA,hpos,hbound,he⟩ := hg
      refine ⟨?_,?_⟩
      · exact he ▸ ⟨A,hA,rfl⟩
      · exact hsmall g ⟨A,hA,hpos,hbound,he⟩
    · have hg' : g=w := hg
      right
      exact ⟨1,K.one_mem,by simpa using hg'⟩
  intro g hg
  have hgG : g ∈ frickeExtension p hp.pos := Subgroup.subset_closure (Or.inl hg)
  rw [← prime_small_denominator_generation hp] at hgG
  rcases hsmallH hgG with hK | ⟨a,ha,he⟩
  · exact hK.2
  · have hbad := (realGamma0 p).mul_mem ((realGamma0 p).inv_mem ha.1) hg
    rw [he,inv_mul_cancel_left] at hbad
    exact False.elim (fricke_not_mem_realGamma0 p hp.one_lt hbad)

#print axioms fricke_not_mem_realGamma0
#print axioms invariant_of_small_branches

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## BranchAction -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem fricke_inverse_eq_negative (N : ℕ) (hN : 0<N) :
    (fricke N hN)⁻¹=GeneralLinearGroup.scalar (Fin 2) (-1)*fricke N hN := by
  apply inv_eq_of_mul_eq_one_left
  rw [mul_assoc,normalized_fricke_square]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [GeneralLinearGroup.scalar,Matrix.scalar,integralMinusIdentity,
      SpecialLinearGroup.mapGL,Matrix.mul_apply,Fin.sum_univ_two]

/-- The normalized matrix identity removes the positive scalar from the
additive-twist functional equation. -/
theorem normalized_branch_identity (p q : ℕ) (hp : 0<p) (hq : 0<q)
    (A : SL(2, ℤ)) (b : ℤ) (hc : A 1 0=(p : ℤ)*b) (hd : A 1 1=(q : ℤ)) :
    translation ((A 0 1 : ℝ)/q)*fricke (p*q^2) (by positivity)=
      SpecialLinearGroup.mapGL ℝ A*fricke p hp*translation ((b : ℝ)/q) := by
  have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hp)).ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsq := Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ)≤p)
  have hdet := A.property
  rw [det_fin_two] at hdet
  change A 0 0*A 1 1-A 0 1*A 1 0=1 at hdet
  rw [hc,hd] at hdet
  have hdetR : (A 0 0 : ℝ)*(q : ℝ)-(A 0 1 : ℝ)*((p : ℝ)*(b : ℝ))=1 := by
    exact_mod_cast hdet
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translation,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.mapGL,Matrix.mul_apply,Fin.sum_univ_two,hc,hd]
  all_goals field_simp [hs,hq0]
  all_goals ring_nf
  all_goals simp [hsq]
  all_goals nlinarith [hdetR]

theorem inverse_normalized_branch_identity (p q : ℕ) (hp : 0<p) (hq : 0<q)
    (A : SL(2, ℤ)) (b : ℤ) (hc : A 1 0=(p : ℤ)*b) (hd : A 1 1=(q : ℤ)) :
    translation ((A 0 1 : ℝ)/q)*(fricke (p*q^2) (by positivity))⁻¹=
      SpecialLinearGroup.mapGL ℝ A*(fricke p hp)⁻¹*translation ((b : ℝ)/q) := by
  rw [fricke_inverse_eq_negative,fricke_inverse_eq_negative]
  have h := congrArg (fun g : GL (Fin 2) ℝ => GeneralLinearGroup.scalar (Fin 2) (-1)*g)
    (normalized_branch_identity p q hp hq A b hc hd)
  simpa only [mul_assoc,GeneralLinearGroup.scalar_commute] using h

/-- Matching the two individual inverse-Fricke laws forces the branch
matrix to fix F. No nonvanishing or eigenvalue cancellation is required. -/
theorem branch_invariance (p q : ℕ) (hp : 0<p) (hq : 0<q)
    (A : SL(2, ℤ)) (b : ℤ) (hc : A 1 0=(p : ℤ)*b) (hd : A 1 1=(q : ℤ))
    (k : ℤ) (F : ℍ → ℂ) (ε : ℂ)
    (hw : F ∣[k] (fricke p hp)⁻¹=ε • F)
    (hpair : F ∣[k] (translation ((A 0 1 : ℝ)/q)*(fricke (p*q^2) (by positivity))⁻¹)=
      ε • (F ∣[k] translation ((b : ℝ)/q))) :
    F ∣[k] SpecialLinearGroup.mapGL ℝ A=F := by
  rw [inverse_normalized_branch_identity p q hp hq A b hc hd,
    SlashAction.slash_mul,← det_one_smul _ (translation_det _),← hw] at hpair
  have h := congrArg (fun f : ℍ → ℂ =>
    (f ∣[k] (translation ((b : ℝ)/q))⁻¹) ∣[k] fricke p hp) hpair
  simp only [← SlashAction.slash_mul,mul_inv_cancel_right,
    inv_mul_cancel,SlashAction.slash_one] at h
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

#print axioms normalized_branch_identity
#print axioms branch_invariance

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Residues -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def residueTranslation {q : ℕ} (a : (ZMod q)ˣ) : ℝ :=
  ((a : ZMod q).val : ℝ)/q

/-- Integer shifts in the numerator have no effect on an additive branch
of a one-periodic function. -/
theorem slash_translation_intCast_eq (q : ℕ) (hq : 0<q) (a b : ℤ)
    (hab : (a : ZMod q)=(b : ZMod q)) (k : ℤ) (F : ℂ → ℂ)
    (hp : Function.Periodic F 1) :
    (fun z : ℍ => F z) ∣[k] translation ((a : ℝ)/q)=
      (fun z : ℍ => F z) ∣[k] translation ((b : ℝ)/q) := by
  obtain ⟨m,hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).mp hab
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hR : (b : ℝ)-(a : ℝ)=(q : ℝ)*(m : ℝ) := by exact_mod_cast hm
  have hr : (b : ℝ)/q=(a : ℝ)/q+(m : ℝ) := by
    apply (div_eq_iff hq0).mpr
    field_simp
    nlinarith [hR]
  funext z
  simp only [translation_slash,translation_point,hr,Complex.ofReal_add]
  have he := hp.int_mul m ((z : ℂ)+(((a : ℝ)/q : ℝ):ℂ))
  simpa only [mul_one,add_assoc,Complex.ofReal_intCast] using he.symm

theorem slash_residueTranslation {q : ℕ} [NeZero q] (a : (ZMod q)ˣ)
    (u : ℤ) (hu : (u : ZMod q)=(a : ZMod q)) (k : ℤ) (F : ℂ → ℂ)
    (hp : Function.Periodic F 1) :
    (fun z : ℍ => F z) ∣[k] translation (residueTranslation a)=
      (fun z : ℍ => F z) ∣[k] translation ((u : ℝ)/q) := by
  have ha : (((a : ZMod q).val : ℤ) : ZMod q)=(u : ZMod q) := by
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using hu.symm
  simpa only [residueTranslation,Int.cast_natCast] using
    slash_translation_intCast_eq q (Nat.pos_of_ne_zero (NeZero.ne q))
      ((a : ZMod q).val : ℤ) u ha k F hp

#print axioms slash_translation_intCast_eq
#print axioms slash_residueTranslation

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## ResidueBranches -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix Complex UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- The determinant identity identifies the partner unit with the
integer numerator in the matrix branch. -/
theorem unit_partner_of_branch (p q : ℕ) [NeZero q] (A : SL(2, ℤ)) (b : ℤ)
    (hc : A 1 0=(p : ℤ)*b) (hd : A 1 1=(q : ℤ))
    (t : (ZMod q)ˣ) (ht : (t : ZMod q)=-(p : ZMod q)) :
    ∃ a : (ZMod q)ˣ, (a : ZMod q)=(A 0 1 : ZMod q) ∧
      ((partnerEquiv t a : (ZMod q)ˣ) : ZMod q)=(b : ZMod q) := by
  have hdet := A.property
  rw [det_fin_two] at hdet
  change A 0 0*A 1 1-A 0 1*A 1 0=1 at hdet
  rw [hc,hd] at hdet
  have hh := congrArg (fun n : ℤ => (n : ZMod q)) hdet
  push_cast at hh
  simp only [ZMod.natCast_self,mul_zero,zero_sub] at hh
  have ha : (A 0 1 : ZMod q)*(-(p : ZMod q)*(b : ZMod q))=1 := by
    linear_combination hh
  let a : (ZMod q)ˣ := ⟨(A 0 1 : ZMod q),-(p : ZMod q)*(b : ZMod q),ha,by
    rw [mul_comm]; exact ha⟩
  refine ⟨a,rfl,?_⟩
  have hm : ((t*a : (ZMod q)ˣ) : ZMod q)*(b : ZMod q)=1 := by
    change (t : ZMod q)*(A 0 1 : ZMod q)*(b : ZMod q)=1
    rw [ht]
    linear_combination ha
  change (((t*a)⁻¹ : (ZMod q)ˣ) : ZMod q)=(b : ZMod q)
  calc
    _ = (((t*a)⁻¹ : (ZMod q)ˣ) : ZMod q)*
        (((t*a : (ZMod q)ˣ) : ZMod q)*(b : ZMod q)) := by rw [hm,mul_one]
    _ = _ := by rw [← mul_assoc,← Units.val_mul,inv_mul_cancel,Units.val_one,one_mul]

/-- Canonical unit-residue additive laws imply invariance under every
integral branch of the same denominator. -/
theorem branch_invariance_of_residue_laws (p q : ℕ) (hp : 0<p) (hq : 0<q)
    [NeZero q] (A : SL(2, ℤ)) (b : ℤ) (hc : A 1 0=(p : ℤ)*b) (hd : A 1 1=(q : ℤ))
    (t : (ZMod q)ˣ) (ht : (t : ZMod q)=-(p : ZMod q))
    (k : ℤ) (F : ℂ → ℂ) (ε : ℂ) (hperiod : Function.Periodic F 1)
    (hw : (fun z : ℍ => F z) ∣[k] (fricke p hp)⁻¹=ε • (fun z : ℍ => F z))
    (hlaw : ∀ a : (ZMod q)ˣ, (fun z : ℍ => F z) ∣[k]
      (translation (residueTranslation a)*(fricke (p*q^2) (by positivity))⁻¹)=
        ε • ((fun z : ℍ => F z) ∣[k] translation (residueTranslation (partnerEquiv t a)))) :
    (fun z : ℍ => F z) ∣[k] SpecialLinearGroup.mapGL ℝ A=(fun z : ℍ => F z) := by
  obtain ⟨a,ha,hb⟩ := unit_partner_of_branch p q A b hc hd t ht
  have h := hlaw a
  rw [SlashAction.slash_mul,slash_residueTranslation a (A 0 1) ha.symm k F hperiod,
    slash_residueTranslation (partnerEquiv t a) b hb.symm k F hperiod] at h
  apply branch_invariance p q hp hq A b hc hd k (fun z : ℍ => F z) ε hw
  simpa only [SlashAction.slash_mul] using h

#print axioms unit_partner_of_branch
#print axioms branch_invariance_of_residue_laws

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Input -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex UpperHalfPlane SmallLevelNormalized Filter Asymptotics Matrix
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  QuantitativeArithmeticWeightedFourierTwist AsymptoticCongruenceLabels
open scoped MatrixGroups ModularForm

/-- The literal c_chi coefficient: a finite weighted sum of e(an/q).
Multiplication by the original normalized f_n is performed by `twisted`. -/
def characterTwisted (q : ℕ) [NeZero q] (f : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  twisted f (fun a : (ZMod q)ˣ => χ (a : ZMod q)) residueTranslation

/-- The analytic hypotheses for all character twists in the small window.
No Euler product, modularity or transformation equation is included. -/
def SmallTwistContinuations (p k : ℕ) (f : ℕ → ℂ) (ε : ℂ) : Prop :=
  ∀ q : ℕ, ∀ hq : 0<q, q≤p.sqrt →
    letI : NeZero q := ⟨hq.ne'⟩
    ∃ Λ : DirichletCharacter ℂ q → ℂ → ℂ,
      (∀ χ, Differentiable ℂ (Λ χ)) ∧ (∀ χ, FiniteOrder (Λ χ)) ∧
      (∀ χ, ∃ c : ℝ, ∀ s : ℂ, c<s.re →
        Λ χ s=completed (p*q^2) k (characterTwisted q f χ) s) ∧
      (∀ χ s, Λ χ s=ε*star (χ (-(p : ZMod q)))*Λ (star χ) (1-s))

theorem characterTwisted_one (f : ℕ → ℂ) :
    characterTwisted 1 f (1 : DirichletCharacter ℂ 1)=f := by
  funext n
  have hd : (default : (ZMod 1)ˣ)=1 := Subsingleton.elim _ _
  have hr (a : (ZMod 1)ˣ) : residueTranslation a=0 := by
    have hz : (a : ZMod 1)=0 := Subsingleton.elim _ _
    simp [residueTranslation,hz]
  simp [characterTwisted,twisted,coefficient,hr,phase,hd]

theorem untwisted_of_small_twists {p k : ℕ} (hp : 0<p) (f : ℕ → ℂ) (ε : ℂ)
    (h : SmallTwistContinuations p k f ε) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ FiniteOrder Λ ∧
      (∃ c : ℝ, ∀ s : ℂ, c<s.re → Λ s=completed p k f s) ∧
      (∀ s, Λ s=ε*Λ (1-s)) := by
  obtain ⟨Λ,hhol,hfinite,hagree,hFE⟩ := h 1 (by decide) (Nat.sqrt_pos.mpr hp)
  refine ⟨Λ 1,hhol 1,hfinite 1,?_,?_⟩
  · obtain ⟨c,hc⟩ := hagree 1
    exact ⟨c,fun s hs => by simpa [characterTwisted_one] using hc s hs⟩
  · intro s
    have he : -(p : ZMod 1)=1 := Subsingleton.elim _ _
    simpa only [he,map_one,star_one,mul_one] using hFE 1 s

theorem inverse_fricke_of_small_twists {p k : ℕ} (hp : 0<p)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (ε : ℂ) (hε : ‖ε‖=1) (h : SmallTwistContinuations p k f ε) :
    (fun z : ℍ => fourier (fullCoefficients f k) z) ∣[(k : ℤ)] (fricke p hp)⁻¹=
      (ε*Complex.I^k) • (fun z : ℍ => fourier (fullCoefficients f k) z) := by
  obtain ⟨Λ,hhol,hfinite,⟨c,hc⟩,hFE⟩ := untwisted_of_small_twists hp f ε h
  exact inverse_fricke_pair p k hp _ _ _
    (FinitenessOriginalFricke.fricke_with_sign hp hf0 hf Λ hhol hfinite hc hε hFE)

/-- From the literal small-twist analytic hypotheses to every integral
small-denominator matrix transformation. -/
theorem small_branch_of_continuations {p k : ℕ} (hp : p.Prime)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (ε : ℂ) (hε : ‖ε‖=1) (h : SmallTwistContinuations p k f ε) :
    ∀ g ∈ smallDenominatorBranches p p.sqrt,
      (fun z : ℍ => fourier (fullCoefficients f k) z) ∣[(k : ℤ)] g=
        (fun z : ℍ => fourier (fullCoefficients f k) z) := by
  rintro g ⟨A,hA,hpos,hbound,rfl⟩
  let q := (A 1 1).toNat
  have hd : A 1 1=(q : ℤ) := (Int.toNat_of_nonneg (by omega : 0≤A 1 1)).symm
  have hq : 0<q := by omega
  let : NeZero q := ⟨hq.ne'⟩
  have hQ : q≤p.sqrt := by omega
  have hqp : q<p := hQ.trans_lt (Nat.sqrt_lt_self hp.one_lt)
  have hunit : IsUnit (-(p : ZMod q)) :=
    ((ZMod.isUnit_iff_coprime p q).mpr (Nat.coprime_of_lt_prime hq.ne' hqp hp)).neg
  let t : (ZMod q)ˣ := hunit.unit
  have ht : (t : ZMod q)=-(p : ZMod q) := hunit.unit_spec
  obtain ⟨b,hc⟩ := (gamma0_mem_dvd p A).mp hA
  apply branch_invariance_of_residue_laws p q hp.pos hq A b hc hd t ht
    (k : ℤ) (fourier (fullCoefficients f k)) (ε*Complex.I^k) (periodic _)
    (inverse_fricke_of_small_twists hp.pos hf0 hf ε hε h)
  obtain ⟨Λ,hhol,hfinite,hagree,hFE⟩ := h q hq hQ
  apply additive_laws_of_character_FE (p*q^2) q k (Nat.mul_pos hp.pos (pow_pos hq _)) hf0 hf
    residueTranslation t ε hε Λ hhol hfinite hagree
  intro χ s
  simpa only [ht] using hFE χ s

/-- Even weight and a sign root number give the square-one Fricke scalar. -/
theorem fricke_scalar_square (m : ℕ) (ε : ℂ) (hε : ε=1 ∨ ε= -1) :
    (ε*Complex.I^(2*m))*(ε*Complex.I^(2*m))=1 := by
  have he : ε*ε=1 := by rcases hε with rfl | rfl <;> norm_num
  have hi : (Complex.I^(2*m))^2=1 := by
    rw [← pow_mul,show 2*m*2=4*m by omega,pow_mul,Complex.I_pow_four,one_pow]
  calc
    _ = (ε*ε)*(Complex.I^(2*m))^2 := by ring
    _ = _ := by rw [he,hi,mul_one]

/-- Full Gamma0(p) invariance from the original small-conductor twist
functional equations. The hypotheses contain no Euler product. -/
theorem gamma0_invariance_of_small_twists {p m : ℕ} (hp : p.Prime)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) (h : SmallTwistContinuations p (2*m) f ε) :
    ∀ g ∈ realGamma0 p,
      (fun z : ℍ => fourier (fullCoefficients f (2*m)) z) ∣[((2*m : ℕ) : ℤ)] g=
        (fun z : ℍ => fourier (fullCoefficients f (2*m)) z) := by
  have hnorm : ‖ε‖=1 := by rcases hε with rfl | rfl <;> norm_num
  have hsq := fricke_scalar_square m ε hε
  have hw := inverse_fricke_of_small_twists hp.pos hf0 hf ε hnorm h
  apply invariant_of_small_branches hp _ _ (ε*Complex.I^(2*m)) hsq
  · have hh := congrArg (fun F : ℍ → ℂ => F ∣[((2*m : ℕ) : ℤ)] fricke p hp.pos) hw
    rw [← SlashAction.slash_mul,inv_mul_cancel,SlashAction.slash_one,
      det_one_smul _ (fricke_det p hp.pos)] at hh
    have he := congrArg (fun F : ℍ → ℂ => (ε*Complex.I^(2*m)) • F) hh
    simpa only [smul_smul,hsq,one_smul] using he.symm
  · exact small_branch_of_continuations hp hf0 hf ε hnorm h

#print axioms untwisted_of_small_twists
#print axioms gamma0_invariance_of_small_twists

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Gauss -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex QuantitativeArithmeticWeightedFourierTwist

/-- The standard Gauss sum, also for composite conductors. -/
def gauss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  gaussSum χ ZMod.stdAddChar

theorem primitive_star {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : (star χ).IsPrimitive := by
  simpa only [DirichletCharacter.IsPrimitive, MulChar.star_eq_inv,
    DirichletCharacter.conductor_inv] using hχ

/-- Fourier inversion gives the Gauss product over Z/qZ without any
primality restriction on q. -/
theorem primitive_gauss_product {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gauss χ * gauss (star χ) = χ (-1) * (q : ℂ) := by
  classical
  have hshift (a : ZMod q) :=
    gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ a
  calc
    gauss χ * gauss (star χ) =
        ∑ a : ZMod q, gaussSum χ (ZMod.stdAddChar.mulShift a) *
          ZMod.stdAddChar a := by
      change gauss χ * (∑ a : ZMod q, (star χ) a * ZMod.stdAddChar a) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [hshift, MulChar.star_eq_inv]
      change gaussSum χ ZMod.stdAddChar * _ = _
      ring
    _ = ∑ b : ZMod q, χ b * ∑ a : ZMod q,
        ZMod.stdAddChar (a * (b+1)) := by
      simp only [gaussSum, AddChar.mulShift_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = χ (-1) * (q : ℂ) := by
      simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
      simp [add_eq_zero_iff_eq_neg]

theorem primitive_gauss_ne_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) : gauss χ ≠ 0 := by
  have hc : χ (-1) ≠ 0 := (isUnit_neg_one.map χ).ne_zero
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  intro h
  have := primitive_gauss_product hχ
  rw [h, zero_mul] at this
  exact mul_ne_zero hc hq this.symm

theorem residue_phase {q : ℕ} [NeZero q] (n : ℕ) (a : (ZMod q)ˣ) :
    phase n (residueTranslation a) = ZMod.stdAddChar ((n : ZMod q) * (a : ZMod q)) := by
  have hcast : (n : ZMod q) * (a : ZMod q) =
      (((n : ℤ) * ((a : ZMod q).val : ℤ) : ℤ) : ZMod q) := by
    simp
  rw [hcast, ZMod.stdAddChar_coe]
  simp only [phase, residueTranslation, Complex.ofReal_div, Complex.ofReal_natCast,
    Int.cast_mul, Int.cast_natCast]
  congr 1
  ring

theorem gauss_sum_units {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (e : AddChar (ZMod q) ℂ) :
    gaussSum χ e = ∑ a : (ZMod q)ˣ, χ (a : ZMod q) * e a := by
  classical
  let u : (ZMod q)ˣ ↪ ZMod q := ⟨Units.val, Units.val_injective⟩
  have hs : (Finset.univ.map u).sum (fun a => χ a * e a) =
      Finset.univ.sum (fun a => χ a * e a) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    have hn : ¬ IsUnit a := by
      intro h
      apply ha
      exact Finset.mem_map.mpr ⟨h.unit, Finset.mem_univ _, h.unit_spec⟩
    rw [MulChar.map_nonunit χ hn, zero_mul]
  simpa only [gaussSum, Finset.sum_map, u, Function.Embedding.coeFn_mk] using hs.symm

/-- The literal weighted additive twist is the Gauss sum times the
conjugate multiplicative twist, including at nonunits. -/
theorem characterTwisted_primitive {q : ℕ} [NeZero q]
    (f : ℕ → ℂ) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (n : ℕ) :
    characterTwisted q f χ n = gauss χ * (f n * (star χ) (n : ZMod q)) := by
  have hs := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (n : ZMod q)
  rw [gauss_sum_units] at hs
  simp only [AddChar.mulShift_apply] at hs
  simp only [characterTwisted, twisted, coefficient, residue_phase]
  rw [hs, MulChar.star_eq_inv]
  simp only [gauss]
  ring

#print axioms primitive_gauss_product
#print axioms primitive_gauss_ne_zero
#print axioms characterTwisted_primitive

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## InducedFourier -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex Finset
open FinitenessRamanujanSum FinitenessRamanujanDivisor

/-- Full residue sum with a character pulled back from its conductor.
Unlike a Dirichlet character changed to level q, no unit filter at q is
imposed here. -/
def completeWeighted {d : ℕ} (χ : DirichletCharacter ℂ d) (q n : ℕ) : ℂ :=
  ∑ a ∈ range q, χ (a : ZMod d) * phase q n a

/-- The corresponding sum restricted to units at the larger modulus. -/
def primitiveWeighted {d : ℕ} (χ : DirichletCharacter ℂ d) (q n : ℕ) : ℂ :=
  ∑ a ∈ residues q, χ (a : ZMod d) * phase q n a

theorem sum_range_blocks (d r : ℕ) (F : ℕ → ℂ) :
    (∑ a ∈ range (d*r), F a) = ∑ b ∈ range r, ∑ a ∈ range d, F (d*b+a) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.mul_succ,sum_range_add,sum_range_succ,ih]

theorem phase_block (d r n b a : ℕ) (hd : 0<d) (hr : 0<r) :
    phase (d*r) n (d*b+a) = phase r n b * phase (d*r) n a := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [hd0,hr0]

theorem phase_frequency_scaled (d r n a : ℕ) (hr : 0<r) :
    phase (d*r) (r*n) a = phase d n a := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold phase
  congr 1
  push_cast
  field_simp [hr0]

theorem completeWeighted_blocks {d r : ℕ} (hd : 0<d) (hr : 0<r)
    (χ : DirichletCharacter ℂ d) (n : ℕ) :
    completeWeighted χ (d*r) n = complete r n *
      ∑ a ∈ range d, χ (a : ZMod d) * phase (d*r) n a := by
  rw [completeWeighted,sum_range_blocks,complete,Finset.sum_mul]
  apply sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro a _
  rw [phase_block d r n b a hd hr]
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add]
  ring

theorem completeWeighted_scaled {d r : ℕ} (hd : 0<d) (hr : 0<r)
    (χ : DirichletCharacter ℂ d) (n : ℕ) :
    completeWeighted χ (d*r) (r*n) = (r : ℂ)*completeWeighted χ d n := by
  rw [completeWeighted_blocks hd hr,complete_eval hr,ite_eq_left (dvd_mul_right r n)]
  simp only [phase_frequency_scaled d r n _ hr,completeWeighted]

theorem completeWeighted_zero {d r : ℕ} (hd : 0<d) (hr : 0<r)
    (χ : DirichletCharacter ℂ d) (n : ℕ) (hn : ¬r ∣ n) :
    completeWeighted χ (d*r) n = 0 := by
  rw [completeWeighted_blocks hd hr,complete_eval hr,ite_eq_right hn,zero_mul]

theorem natural_phase {q : ℕ} [NeZero q] (n a : ℕ) :
    phase q n a = ZMod.stdAddChar ((n : ZMod q)*(a : ZMod q)) := by
  have he : (n : ZMod q)*(a : ZMod q) = (((n*a : ℕ) : ℤ) : ZMod q) := by
    simp
  rw [he,ZMod.stdAddChar_coe]
  unfold phase
  push_cast
  congr 1
  ring

theorem completeWeighted_gauss {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) (n : ℕ) :
    completeWeighted χ d n = gaussSum χ (ZMod.stdAddChar.mulShift (n : ZMod d)) := by
  classical
  unfold completeWeighted gaussSum
  apply sum_bij (fun (a : ℕ) _ => (a : ZMod d))
  · intro a _
    exact mem_univ _
  · intro a ha b hb hab
    have hv := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp ha),
      Nat.mod_eq_of_lt (mem_range.mp hb)] using hv
  · intro b _
    exact ⟨b.val,mem_range.mpr b.val_lt,ZMod.natCast_zmod_val b⟩
  · intro a _
    rw [natural_phase]
    rfl

/-- Complete Fourier transform of a primitive character inflated to any
multiple of its conductor. This supplies the nonunit terms in the
imprimitive-character reduction. -/
theorem completeWeighted_primitive {d r : ℕ} [NeZero d] (hr : 0<r)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (n : ℕ) :
    completeWeighted χ (d*r) n =
      if r ∣ n then (r : ℂ)*gauss χ*(star χ) ((n/r : ℕ) : ZMod d) else 0 := by
  classical
  have hd : 0<d := NeZero.pos d
  by_cases hn : r ∣ n
  · rw [ite_eq_left hn,← Nat.mul_div_cancel' hn,completeWeighted_scaled hd hr]
    rw [completeWeighted_gauss,gaussSum_mulShift_of_isPrimitive _ hχ,
      MulChar.star_eq_inv]
    simp only [gauss,Nat.mul_div_cancel_left _ hr]
    ring
  · rw [ite_eq_right hn,completeWeighted_zero hd hr χ n hn]

/-- Gcd partition, before imposing any relation between the two moduli. -/
theorem weighted_fiber {d : ℕ} (χ : DirichletCharacter ℂ d)
    (h e n : ℕ) (hh : 0<h) :
    (∑ a ∈ (range (h*e)).filter (fun a => Nat.gcd (h*e) a=h),
      χ (a : ZMod d)*phase (h*e) n a) = χ (h : ZMod d)*primitiveWeighted χ e n := by
  symm
  unfold primitiveWeighted residues
  rw [Finset.mul_sum]
  apply sum_bij (fun a _ => h*a)
  · intro a ha
    obtain ⟨ha,hcop⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp ha) hh),?_⟩
    rw [Nat.gcd_mul_left,hcop.symm.gcd_eq_one,Nat.mul_one]
  · intro a _ b _ heq
    exact Nat.eq_of_mul_eq_mul_left hh heq
  · intro a ha
    obtain ⟨ha,hg⟩ := mem_filter.mp ha
    have hda : h ∣ a := by rw [← hg]; exact Nat.gcd_dvd_right _ _
    obtain ⟨b,rfl⟩ := hda
    refine ⟨b,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_of_mul_lt_mul_left (mem_range.mp ha)),?_⟩,rfl⟩
    rw [Nat.gcd_mul_left] at hg
    have h1 : Nat.gcd e b=1 := by
      apply Nat.eq_of_mul_eq_mul_left hh
      simpa using hg
    exact (show Nat.Coprime e b from h1).symm
  · intro a _
    rw [phase_scaled h e n a hh,Nat.cast_mul,map_mul]
    ring

theorem completeWeighted_divisors {d q : ℕ} (χ : DirichletCharacter ℂ d)
    (hq : 0<q) (n : ℕ) :
    completeWeighted χ q n =
      ∑ h ∈ q.divisors, χ (h : ZMod d)*primitiveWeighted χ (q/h) n := by
  have H : (∑ h ∈ q.divisors, ∑ a ∈ (range q).filter (fun a => Nat.gcd q a=h),
      χ (a : ZMod d)*phase q n a) = completeWeighted χ q n := by
    apply sum_fiberwise_of_maps_to
    intro a _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q a,hq.ne'⟩
  rw [← H]
  apply sum_congr rfl
  intro h hh
  have he : h*(q/h)=q := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hh)
  have hf := weighted_fiber χ h (q/h) n (Nat.pos_of_mem_divisors hh)
  rw [he] at hf
  exact hf

#print axioms completeWeighted_primitive
#print axioms completeWeighted_divisors

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Moebius -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex Finset ArithmeticFunction
open FinitenessRamanujanSum

def characterScale {d : ℕ} (χ : DirichletCharacter ℂ d)
    (F : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => χ (n : ZMod d)*F n,by simp⟩

theorem characterScale_mul {d : ℕ} (χ : DirichletCharacter ℂ d)
    (F G : ArithmeticFunction ℂ) :
    characterScale χ (F*G)=characterScale χ F*characterScale χ G := by
  ext n
  change χ (n : ZMod d)*(F*G) n=(characterScale χ F*characterScale χ G) n
  rw [mul_apply,mul_apply,Finset.mul_sum]
  apply sum_congr rfl
  intro a ha
  have he : a.1*a.2=n := (Nat.mem_divisorsAntidiagonal.mp ha).1
  change χ (n : ZMod d)*(F a.1*G a.2)=
    (χ (a.1 : ZMod d)*F a.1)*(χ (a.2 : ZMod d)*G a.2)
  rw [← he,Nat.cast_mul,map_mul]
  ring

theorem characterScale_one {d : ℕ} (χ : DirichletCharacter ℂ d) :
    characterScale χ 1=1 := by
  ext n
  by_cases hn : n=1
  · simp [characterScale,hn]
  · simp [characterScale,ArithmeticFunction.one_apply,hn]

def completeWeightedFunction {d : ℕ} (χ : DirichletCharacter ℂ d)
    (n : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => completeWeighted χ q n,by simp [completeWeighted]⟩

def primitiveWeightedFunction {d : ℕ} (χ : DirichletCharacter ℂ d)
    (n : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => primitiveWeighted χ q n,by simp [primitiveWeighted,residues]⟩

theorem weighted_convolution {d : ℕ} (χ : DirichletCharacter ℂ d) (n : ℕ) :
    characterScale χ (ArithmeticFunction.zeta : ArithmeticFunction ℂ)*
      primitiveWeightedFunction χ n=completeWeightedFunction χ n := by
  ext q
  by_cases hq : q=0
  · simp [hq]
  rw [mul_apply,Nat.sum_divisorsAntidiagonal
    (fun a b => (characterScale χ (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) a*
      primitiveWeightedFunction χ n b)]
  change (∑ h ∈ q.divisors, (characterScale χ _) h*primitiveWeighted χ (q/h) n)=
    completeWeighted χ q n
  rw [completeWeighted_divisors χ (Nat.pos_of_ne_zero hq)]
  apply sum_congr rfl
  intro h hh
  simp only [characterScale,ArithmeticFunction.coe_mk,ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hh).ne',Nat.cast_one,mul_one]

/-- Exact finite divisor reduction for the character-weighted unit sum.
This identity is unconditional; its use in the L-series reduction only
requires the original unramified Hecke relations afterward. -/
theorem primitiveWeighted_moebius {d : ℕ} (χ : DirichletCharacter ℂ d) (q n : ℕ) :
    primitiveWeighted χ q n = ∑ h ∈ q.divisors,
      ((ArithmeticFunction.moebius h : ℤ) : ℂ)*χ (h : ZMod d)*
        completeWeighted χ (q/h) n := by
  have hi : characterScale χ (ArithmeticFunction.moebius : ArithmeticFunction ℂ)*
      characterScale χ (ArithmeticFunction.zeta : ArithmeticFunction ℂ)=1 := by
    rw [← characterScale_mul,ArithmeticFunction.coe_moebius_mul_coe_zeta,characterScale_one]
  have he : characterScale χ (ArithmeticFunction.moebius : ArithmeticFunction ℂ)*
      completeWeightedFunction χ n=primitiveWeightedFunction χ n := by
    rw [← weighted_convolution χ n,← mul_assoc,hi,one_mul]
  have hv := congrArg (fun F : ArithmeticFunction ℂ => F q) he
  rw [mul_apply,Nat.sum_divisorsAntidiagonal
    (fun a b => (characterScale χ (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) a*
      completeWeightedFunction χ n b)] at hv
  change (∑ h ∈ q.divisors, (characterScale χ _) h*completeWeighted χ (q/h) n)=
    primitiveWeighted χ q n at hv
  rw [← hv]
  apply sum_congr rfl
  intro h _
  simp only [characterScale,ArithmeticFunction.coe_mk,ArithmeticFunction.intCoe_apply]
  ring

theorem primitiveWeighted_changeLevel {d q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ d) (hd : d ∣ q) (n : ℕ) :
    primitiveWeighted χ q n=completeWeighted (DirichletCharacter.changeLevel hd χ) q n := by
  classical
  simp only [primitiveWeighted,residues,completeWeighted,sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : a.Coprime q
  · rw [ite_eq_left ha]
    have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
    have he := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd hu.unit
    rw [hu.unit_spec,ZMod.cast_natCast hd] at he
    rw [he]
  · rw [ite_eq_right ha]
    have hu : ¬IsUnit (a : ZMod q) := fun h => ha ((ZMod.isUnit_iff_coprime a q).mp h)
    rw [MulChar.map_nonunit _ hu,zero_mul]

/-- Identification with the exact characterTwisted input used by the
checked converse theorem. -/
theorem characterTwisted_changeLevel {d q : ℕ} [NeZero q]
    (f : ℕ → ℂ) (χ : DirichletCharacter ℂ d) (hd : d ∣ q) (n : ℕ) :
    characterTwisted q f (DirichletCharacter.changeLevel hd χ) n=
      f n*primitiveWeighted χ q n := by
  rw [primitiveWeighted_changeLevel χ hd,completeWeighted_gauss,gauss_sum_units]
  simp only [characterTwisted,QuantitativeArithmeticWeightedFourierTwist.twisted,
    QuantitativeArithmeticWeightedFourierTwist.coefficient,residue_phase,
    AddChar.mulShift_apply]

#print axioms primitiveWeighted_moebius
#print axioms characterTwisted_changeLevel

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## InducedCoefficients -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex Finset

theorem primitiveWeighted_restricted_moebius {d r : ℕ} [NeZero d] (hr : 0<r)
    (χ : DirichletCharacter ℂ d) (n : ℕ) :
    primitiveWeighted χ (d*r) n = ∑ h ∈ r.divisors,
      ((ArithmeticFunction.moebius h : ℤ) : ℂ)*χ (h : ZMod d)*
        completeWeighted χ (d*(r/h)) n := by
  rw [primitiveWeighted_moebius]
  have hz : d*r ≠ 0 := Nat.mul_ne_zero (NeZero.ne d) hr.ne'
  calc
    _ = ∑ h ∈ r.divisors,
        ((ArithmeticFunction.moebius h : ℤ) : ℂ)*χ (h : ZMod d)*
          completeWeighted χ (d*r/h) n := by
      symm
      apply sum_subset (Nat.divisors_subset_of_dvd hz (dvd_mul_left r d))
      intro h hq hh
      have hc : ¬h.Coprime d := by
        intro hc
        exact hh (Nat.mem_divisors.mpr
          ⟨hc.dvd_of_dvd_mul_left (Nat.dvd_of_mem_divisors hq),hr.ne'⟩)
      have hu : ¬IsUnit (h : ZMod d) := fun H => hc ((ZMod.isUnit_iff_coprime h d).mp H)
      rw [MulChar.map_nonunit χ hu,mul_zero,zero_mul]
    _ = _ := by
      apply sum_congr rfl
      intro h hh
      rw [Nat.mul_div_assoc d (Nat.dvd_of_mem_divisors hh)]

/-- Explicit coefficient formula for every induced character. The sum
is over divisors of the ratio of moduli, not over unknown continuations. -/
theorem primitiveWeighted_induced_formula {d r : ℕ} [NeZero d] (hr : 0<r)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (n : ℕ) :
    primitiveWeighted χ (d*r) n = gauss χ * ∑ h ∈ r.divisors,
      ((ArithmeticFunction.moebius h : ℤ) : ℂ)*χ (h : ZMod d)*
        (if r/h ∣ n then ((r/h : ℕ) : ℂ)*(star χ) ((n/(r/h) : ℕ) : ZMod d) else 0) := by
  rw [primitiveWeighted_restricted_moebius hr χ,Finset.mul_sum]
  apply sum_congr rfl
  intro h hh
  have hpos : 0<r/h := Nat.div_pos (Nat.le_of_dvd hr (Nat.dvd_of_mem_divisors hh))
    (Nat.pos_of_mem_divisors hh)
  rw [completeWeighted_primitive hpos hχ]
  split_ifs <;> ring

/-- The induced-character formula for the actual normalized coefficients
used in the analytic hypotheses. -/
theorem characterTwisted_induced_formula {d r : ℕ} [NeZero d] [NeZero (d*r)]
    (hr : 0<r) (f : ℕ → ℂ) {χ : DirichletCharacter ℂ d}
    (hχ : χ.IsPrimitive) (n : ℕ) :
    characterTwisted (d*r) f (DirichletCharacter.changeLevel (dvd_mul_right d r) χ) n =
      gauss χ * ∑ h ∈ r.divisors,
        ((ArithmeticFunction.moebius h : ℤ) : ℂ)*χ (h : ZMod d)*
          (if r/h ∣ n then ((r/h : ℕ) : ℂ)*f n*
            (star χ) ((n/(r/h) : ℕ) : ZMod d) else 0) := by
  rw [characterTwisted_changeLevel,primitiveWeighted_induced_formula hr hχ]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro h _
  split_ifs <;> ring

#print axioms primitiveWeighted_induced_formula
#print axioms characterTwisted_induced_formula

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Primitive -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex FinitenessOriginalInput FinitenessInputBounds

/-- Multiplicative twisting of the normalized coefficients. -/
def multiplicativeTwisted (q : ℕ) (f : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (n : ℕ) : ℂ := f n * χ (n : ZMod q)

theorem completed_const_mul (N k : ℕ) (f : ℕ → ℂ) (a s : ℂ) :
    completed N k (fun n => a*f n) s = a*completed N k f s := by
  simp only [completed,L,mul_assoc,tsum_mul_left]
  ring

theorem completed_primitive {q : ℕ} [NeZero q] (N k : ℕ) (f : ℕ → ℂ)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (s : ℂ) :
    completed N k (characterTwisted q f χ) s =
      gauss χ * completed N k (multiplicativeTwisted q f (star χ)) s := by
  have he : characterTwisted q f χ =
      fun n => gauss χ * multiplicativeTwisted q f (star χ) n :=
    funext (characterTwisted_primitive f hχ)
  rw [he,completed_const_mul]

theorem finiteOrder_const_mul {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (ho : FiniteOrder F) (a : ℂ) : FiniteOrder (fun s => a*F s) :=
  bound_finiteOrder (FinitenessFiniteOrder.mul (bound_const a)
    (finiteOrder_bound hF.continuous ho))

/-- Exact conversion of the primitive multiplicative-twist root number. -/
theorem primitive_root_conversion {q : ℕ} [NeZero q] (p : ℕ) (ε : ℂ)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gauss χ * (ε*(star χ) (p : ZMod q)*gauss (star χ)^2/(q : ℂ)) =
      ε*star (χ (-(p : ZMod q)))*gauss (star χ) := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hg := primitive_gauss_product (primitive_star hχ)
  rw [star_star] at hg
  have hv : star (χ (-(p : ZMod q))) =
      (star χ) (-1) * (star χ) (p : ZMod q) := by
    rw [← MulChar.star_apply, ← map_mul, neg_one_mul]
  rw [hv,← mul_div_assoc]
  apply (div_eq_iff hq).mpr
  linear_combination (ε*(star χ) (p : ZMod q)*gauss (star χ))*hg

/-- Primitive multiplicative continuations give the required literal
c_chi continuations, with the prescribed paired functional equation.
No Euler relations or primality of the conductor are used in this step. -/
theorem primitive_continuations {p q k : ℕ} [NeZero q] (f : ℕ → ℂ) (ε : ℂ)
    (Λ : DirichletCharacter ℂ q → ℂ → ℂ)
    (hhol : ∀ χ, χ.IsPrimitive → Differentiable ℂ (Λ χ))
    (hord : ∀ χ, χ.IsPrimitive → FiniteOrder (Λ χ))
    (hagree : ∀ χ, χ.IsPrimitive → ∃ c : ℝ, ∀ s : ℂ, c<s.re →
      Λ χ s=completed (p*q^2) k (multiplicativeTwisted q f χ) s)
    (hFE : ∀ χ, χ.IsPrimitive → ∀ s : ℂ,
      Λ χ s=(ε*χ (p : ZMod q)*gauss χ^2/(q : ℂ))*Λ (star χ) (1-s)) :
    ∃ A : DirichletCharacter ℂ q → ℂ → ℂ,
      (∀ χ, χ.IsPrimitive → Differentiable ℂ (A χ)) ∧
      (∀ χ, χ.IsPrimitive → FiniteOrder (A χ)) ∧
      (∀ χ, χ.IsPrimitive → ∃ c : ℝ, ∀ s : ℂ, c<s.re →
        A χ s=completed (p*q^2) k (characterTwisted q f χ) s) ∧
      (∀ χ, χ.IsPrimitive → ∀ s : ℂ,
        A χ s=ε*star (χ (-(p : ZMod q)))*A (star χ) (1-s)) := by
  refine ⟨fun χ s => gauss χ*Λ (star χ) s,?_,?_,?_,?_⟩
  · intro χ hχ
    exact (hhol _ (primitive_star hχ)).const_mul _
  · intro χ hχ
    exact finiteOrder_const_mul (hhol _ (primitive_star hχ))
      (hord _ (primitive_star hχ)) _
  · intro χ hχ
    obtain ⟨c,hc⟩ := hagree _ (primitive_star hχ)
    refine ⟨c,fun s hs => ?_⟩
    dsimp only
    rw [hc s hs,completed_primitive _ _ _ hχ]
  · intro χ hχ s
    dsimp only
    rw [hFE _ (primitive_star hχ),star_star,← mul_assoc,
      primitive_root_conversion p ε hχ,mul_assoc]

#print axioms completed_primitive
#print axioms primitive_root_conversion
#print axioms primitive_continuations

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## HeckeShift -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex FinitenessOriginalInput FinitenessEulerLocal

/-- A second-order Euler recurrence has a uniform two-term expression
for every shifted subsequence. -/
theorem recurrence_shift (a D : ℂ) (g : ℕ → ℂ)
    (h1 : g 1=a*g 0-D)
    (hr : ∀ j, g (j+2)=a*g (j+1)-g j) (j : ℕ) :
    g (j+1)=coeff a 1 (j+1)*g 0-coeff a 1 j*D := by
  induction j using Nat.twoStepInduction with
  | zero => simpa only [Nat.zero_add,coeff,one_mul] using h1
  | one =>
      rw [hr 0,h1]
      simp only [coeff,one_mul]
      ring
  | more j ih0 ih1 =>
      rw [hr (j+1),ih1,ih0]
      simp only [coeff,one_mul]
      ring

theorem good_power_recurrence {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬p ∣ N) (j m : ℕ) :
    f (p^(j+2)*m)=f p*f (p^(j+1)*m)-f (p^j*m) := by
  have he : p*(p^(j+1)*m)=p^(j+2)*m := by ring
  have hd : p ∣ p^(j+1)*m := ⟨p^j*m,by ring⟩
  have hdiv : (p^(j+1)*m)/p=p^j*m := by
    rw [pow_succ',mul_assoc,Nat.mul_div_right _ hp.pos]
  have H := FinitenessAllLevelGoodCoefficients.good_mul hf hp hgood (p^(j+1)*m)
  rw [he,ite_eq_left hd,hdiv] at H
  exact H

/-- A prime-power coefficient shift expressed through two coefficients,
including indices divisible by that prime. -/
theorem good_power_shift {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬p ∣ N) (j m : ℕ) :
    f (p^(j+1)*m)=coeff (f p) 1 (j+1)*f m-
      coeff (f p) 1 j*(if p ∣ m then f (m/p) else 0) := by
  simpa only [pow_zero,one_mul] using recurrence_shift (f p)
    (if p ∣ m then f (m/p) else 0) (fun t => f (p^t*m))
    (by simpa using FinitenessAllLevelGoodCoefficients.good_mul hf hp hgood m)
    (fun t => good_power_recurrence hf hp hgood t m) j

def coefficientInsert (p : ℕ) (g : ℕ → ℂ) (n : ℕ) : ℂ :=
  if p ∣ n then g (n/p) else 0

def twistedShift {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (r n : ℕ) : ℂ := f (r*n)*χ (n : ZMod d)

/-- The coefficient form of the local Dirichlet-polynomial reduction.
All coefficients remain in the normalization with critical line 1/2. -/
theorem twisted_good_power_shift {N d : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (χ : DirichletCharacter ℂ d) {p r : ℕ} (hp : p.Prime) (hgood : ¬p ∣ N)
    (hpr : p.Coprime r) (j n : ℕ) :
    twistedShift χ f (p^(j+1)*r) n =
      coeff (f p) 1 (j+1)*twistedShift χ f r n-
        (coeff (f p) 1 j*χ (p : ZMod d))*coefficientInsert p (twistedShift χ f r) n := by
  unfold twistedShift coefficientInsert
  rw [mul_assoc,good_power_shift hf hp hgood]
  by_cases hn : p ∣ n
  · rw [ite_eq_left hn,ite_eq_left (dvd_mul_of_dvd_right hn r),Nat.mul_div_assoc r hn]
    have hc : χ (n : ZMod d)=χ (p : ZMod d)*χ ((n/p : ℕ) : ZMod d) := by
      rw [← map_mul,← Nat.cast_mul,Nat.mul_div_cancel' hn]
    rw [hc]
    ring
  · rw [ite_eq_right hn,ite_eq_right (fun h => hn (hpr.dvd_of_dvd_mul_left h))]
    ring

#print axioms good_power_shift
#print axioms twisted_good_power_shift

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## ShiftSeries -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex FinitenessOriginalInput FinitenessEulerLocal

theorem coefficientInsert_zero (p : ℕ) {g : ℕ → ℂ} (hg : g 0=0) :
    coefficientInsert p g 0=0 := by simp [coefficientInsert,hg]

theorem insert_term_mul {p : ℕ} (hp : 0<p) {g : ℕ → ℂ} (hg : g 0=0)
    (s : ℂ) (n : ℕ) :
    LSeries.term (coefficientInsert p g) s (p*n)=
      (p : ℂ)^(-s)*LSeries.term g s n := by
  rw [LSeries.term_def₀ (coefficientInsert_zero p hg),LSeries.term_def₀ hg]
  rw [coefficientInsert,ite_eq_left (dvd_mul_right p n),Nat.mul_div_right _ hp,Nat.cast_mul]
  have he := mul_cpow_ofReal_nonneg (Nat.cast_nonneg p : (0 : ℝ)≤p)
    (Nat.cast_nonneg n : (0 : ℝ)≤n) (-s)
  simp only [ofReal_natCast] at he
  rw [he]
  ring

theorem insert_term_support {p : ℕ} {g : ℕ → ℂ} (hg : g 0=0) (s : ℂ) :
    Function.support (LSeries.term (coefficientInsert p g) s) ⊆
      Set.range (fun n : ℕ => p*n) := by
  intro n hn
  have hd : p ∣ n := by
    by_contra h
    apply hn
    rw [LSeries.term_def₀ (coefficientInsert_zero p hg),coefficientInsert,ite_eq_right h,zero_mul]
  obtain ⟨m,hm⟩ := hd
  exact ⟨m,hm.symm⟩

theorem LSeries_insert {p : ℕ} (hp : 0<p) {g : ℕ → ℂ} (hg : g 0=0) (s : ℂ) :
    LSeries (coefficientInsert p g) s=(p : ℂ)^(-s)*LSeries g s := by
  have hinj : Function.Injective (fun n : ℕ => p*n) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h
  rw [LSeries,← hinj.tsum_eq (insert_term_support hg s)]
  simp only [insert_term_mul hp hg,tsum_mul_left,LSeries]

theorem summable_insert {p : ℕ} (hp : 0<p) {g : ℕ → ℂ} (hg : g 0=0)
    {s : ℂ} (hs : LSeriesSummable g s) : LSeriesSummable (coefficientInsert p g) s := by
  have hinj : Function.Injective (fun n : ℕ => p*n) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h
  apply (hinj.summable_iff ?_).mp
  · simpa only [Function.comp_def,insert_term_mul hp hg] using hs.mul_left ((p : ℂ)^(-s))
  · intro n hn
    by_contra he
    exact hn (insert_term_support hg s he)

theorem twistedShift_zero {N d : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (χ : DirichletCharacter ℂ d) (r : ℕ) : twistedShift χ f r 0=0 := by
  simp [twistedShift,hf.zero]

/-- The actual local Dirichlet-polynomial ratio, derived from the Hecke
relations by an absolutely convergent reindexing. -/
theorem shifted_prime_power_series {N d : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (χ : DirichletCharacter ℂ d) {p r : ℕ} (hp : p.Prime) (hgood : ¬p ∣ N)
    (hpr : p.Coprime r) (j : ℕ) {s : ℂ} (hs : LSeriesSummable (twistedShift χ f r) s) :
    LSeriesSummable (twistedShift χ f (p^(j+1)*r)) s ∧
      LSeries (twistedShift χ f (p^(j+1)*r)) s=
        (coeff (f p) 1 (j+1)-coeff (f p) 1 j*χ (p : ZMod d)*(p : ℂ)^(-s))*
          LSeries (twistedShift χ f r) s := by
  have hi := summable_insert hp.pos (twistedShift_zero hf χ r) hs
  have he : twistedShift χ f (p^(j+1)*r)=
      coeff (f p) 1 (j+1) • twistedShift χ f r-
        (coeff (f p) 1 j*χ (p : ZMod d)) • coefficientInsert p (twistedShift χ f r) := by
    funext n
    exact twisted_good_power_shift hf χ hp hgood hpr j n
  rw [he]
  refine ⟨(hs.smul _).sub (hi.smul _),?_⟩
  rw [LSeries_sub (hs.smul _) (hi.smul _),LSeries_smul,LSeries_smul,
    LSeries_insert hp.pos (twistedShift_zero hf χ r)]
  ring

#print axioms LSeries_insert
#print axioms shifted_prime_power_series

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## ShiftProduct -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex FinitenessOriginalInput FinitenessEulerLocal

def shiftLocal {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (s : ℂ) (p a : ℕ) : ℂ :=
  if a=0 then 1 else coeff (f p) 1 a-coeff (f p) 1 (a-1)*χ (p : ZMod d)*(p : ℂ)^(-s)

def shiftProduct {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (r : ℕ) (s : ℂ) : ℂ := r.factorization.prod (shiftLocal χ f s)

theorem shiftProduct_mul {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    {r t : ℕ} (h : r.Coprime t) (s : ℂ) :
    shiftProduct χ f (r*t) s=shiftProduct χ f r s*shiftProduct χ f t s := by
  unfold shiftProduct
  rw [Nat.factorization_mul_of_coprime h]
  exact Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors _

theorem shiftProduct_prime_pow {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    {p : ℕ} (hp : p.Prime) (j : ℕ) (s : ℂ) :
    shiftProduct χ f (p^(j+1)) s=
      coeff (f p) 1 (j+1)-coeff (f p) 1 j*χ (p : ZMod d)*(p : ℂ)^(-s) := by
  unfold shiftProduct
  rw [hp.factorization_pow,Finsupp.prod_single_index (by simp [shiftLocal])]
  simp [shiftLocal]

/-- Every coefficient shift by an integer coprime to the level has an
explicit finite local product. Summability is propagated from the
unshifted multiplicative twist, not assumed for each new subsequence. -/
theorem shifted_series_product {N d : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (χ : DirichletCharacter ℂ d) {s : ℂ}
    (hs : LSeriesSummable (multiplicativeTwisted d f χ) s) :
    ∀ r : ℕ, r≠0 → r.Coprime N →
      LSeriesSummable (twistedShift χ f r) s ∧
        LSeries (twistedShift χ f r) s=
          shiftProduct χ f r s*LSeries (multiplicativeTwisted d f χ) s := by
  apply Nat.recOnPrimePow
  · intro h _
    exact (h rfl).elim
  · intro _ _
    have he : twistedShift χ f 1=multiplicativeTwisted d f χ := by
      funext n
      simp [twistedShift,multiplicativeTwisted]
    rw [he]
    exact ⟨hs,by simp [shiftProduct]⟩
  · intro r p a hp hpr ha ih hzero hcop
    have hr : r≠0 := right_ne_zero_of_mul hzero
    have hrN : r.Coprime N := hcop.of_dvd_left (dvd_mul_left r (p^a))
    have hpN : p.Coprime N := hcop.of_dvd_left
      (dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') r)
    have hgood : ¬p ∣ N := hp.coprime_iff_not_dvd.mp hpN
    have hpr' : p.Coprime r := hp.coprime_iff_not_dvd.mpr hpr
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    obtain ⟨hsr,he⟩ := ih hr hrN
    obtain ⟨hss,hse⟩ := shifted_prime_power_series hf χ hp hgood hpr' j hsr
    refine ⟨hss,?_⟩
    rw [hse,he,shiftProduct_mul χ f (hpr'.pow_left (j+1)),
      shiftProduct_prime_pow χ f hp]
    ring

#print axioms shifted_series_product

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## InducedSeries -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex Finset FinitenessOriginalInput FinitenessEulerLocal

def inducedCoefficientTerm {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (r h : ℕ) : ℕ → ℂ :=
  (((ArithmeticFunction.moebius h : ℤ) : ℂ)*χ (h : ZMod d)*((r/h : ℕ) : ℂ)) •
    coefficientInsert (r/h) (twistedShift (star χ) f (r/h))

theorem characterTwisted_induced_insert {d r : ℕ} [NeZero d] [NeZero (d*r)]
    (hr : 0<r) (f : ℕ → ℂ) {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) :
    characterTwisted (d*r) f (DirichletCharacter.changeLevel (dvd_mul_right d r) χ)=
      gauss χ • ∑ h ∈ r.divisors, inducedCoefficientTerm χ f r h := by
  funext n
  rw [characterTwisted_induced_formula hr f hχ]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  congr 1
  apply sum_congr rfl
  intro h _
  simp only [inducedCoefficientTerm,Pi.smul_apply,smul_eq_mul,coefficientInsert,twistedShift]
  split_ifs with hn
  · rw [Nat.mul_div_cancel' hn]
    ring
  · ring

/-- A finite sum of products of elementary Dirichlet polynomials. This
is the unnormalized ratio; the completed ratio additionally has r^(s-1/2). -/
def inducedMultiplier {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (r : ℕ) (s : ℂ) : ℂ :=
  ∑ h ∈ r.divisors, ((ArithmeticFunction.moebius h : ℤ) : ℂ)*χ (h : ZMod d)*
    ((r/h : ℕ) : ℂ)*((r/h : ℕ) : ℂ)^(-s)*shiftProduct (star χ) f (r/h) s

theorem inducedTerm_summable {N d r : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (χ : DirichletCharacter ℂ d) (hr : 0<r) (hrN : r.Coprime N) {s : ℂ}
    (hs : LSeriesSummable (multiplicativeTwisted d f (star χ)) s)
    {h : ℕ} (hh : h ∈ r.divisors) : LSeriesSummable (inducedCoefficientTerm χ f r h) s := by
  have ht : 0<r/h := Nat.div_pos (Nat.le_of_dvd hr (Nat.dvd_of_mem_divisors hh))
    (Nat.pos_of_mem_divisors hh)
  have hc : (r/h).Coprime N := hrN.of_dvd_left (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hh))
  have hss := (shifted_series_product hf (star χ) hs (r/h) ht.ne' hc).1
  exact (summable_insert ht (twistedShift_zero hf (star χ) (r/h)) hss).smul _

theorem inducedTerm_series {N d r : ℕ} {f : ℕ → ℂ} (hf : EulerData N f)
    (χ : DirichletCharacter ℂ d) (hr : 0<r) (hrN : r.Coprime N) {s : ℂ}
    (hs : LSeriesSummable (multiplicativeTwisted d f (star χ)) s)
    {h : ℕ} (hh : h ∈ r.divisors) :
    LSeries (inducedCoefficientTerm χ f r h) s=
      (((ArithmeticFunction.moebius h : ℤ) : ℂ)*χ (h : ZMod d)*
        ((r/h : ℕ) : ℂ)*((r/h : ℕ) : ℂ)^(-s)*shiftProduct (star χ) f (r/h) s)*
        LSeries (multiplicativeTwisted d f (star χ)) s := by
  have ht : 0<r/h := Nat.div_pos (Nat.le_of_dvd hr (Nat.dvd_of_mem_divisors hh))
    (Nat.pos_of_mem_divisors hh)
  have hc : (r/h).Coprime N := hrN.of_dvd_left (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hh))
  rw [inducedCoefficientTerm,LSeries_smul,
    LSeries_insert ht (twistedShift_zero hf (star χ) (r/h)),
    (shifted_series_product hf (star χ) hs (r/h) ht.ne' hc).2]
  ring

/-- The actual imprimitive c_chi Dirichlet series is its inducing
primitive c_chi series multiplied by an explicit finite Dirichlet
polynomial. No analytic continuation is assumed in this theorem. -/
theorem induced_series_identity {N d r : ℕ} [NeZero d] [NeZero (d*r)]
    {f : ℕ → ℂ} (hf : EulerData N f) (hr : 0<r) (hrN : r.Coprime N)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : LSeriesSummable (multiplicativeTwisted d f (star χ)) s) :
    LSeriesSummable
        (characterTwisted (d*r) f (DirichletCharacter.changeLevel (dvd_mul_right d r) χ)) s ∧
      LSeries (characterTwisted (d*r) f
        (DirichletCharacter.changeLevel (dvd_mul_right d r) χ)) s=
        inducedMultiplier χ f r s*LSeries (characterTwisted d f χ) s := by
  have hsum := LSeriesSummable.sum (fun h hh => inducedTerm_summable hf χ hr hrN hs hh)
  rw [characterTwisted_induced_insert hr f hχ]
  refine ⟨hsum.smul _,?_⟩
  rw [LSeries_smul,LSeries_sum (fun h hh => inducedTerm_summable hf χ hr hrN hs hh)]
  have he : characterTwisted d f χ=gauss χ • multiplicativeTwisted d f (star χ) := by
    funext n
    exact characterTwisted_primitive f hχ n
  rw [he,LSeries_smul,inducedMultiplier,Finset.sum_mul,Finset.mul_sum]
  apply sum_congr rfl
  intro h hh
  rw [inducedTerm_series hf χ hr hrN hs hh]
  ring

#print axioms induced_series_identity

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## InducedAnalytic -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex FinitenessOriginalInput FinitenessInputBounds FinitenessTwistExponential

theorem negative_power_exp {p : ℕ} (hp : 0<p) :
    (fun s : ℂ => (p : ℂ)^(-s)) = fun s : ℂ => exp (((-Real.log p : ℝ) : ℂ)*s) := by
  funext s
  rw [← power_eq hp]
  simp only [power,ofReal_neg,mul_neg,neg_mul]

theorem negative_power_entire {p : ℕ} (hp : 0<p) :
    Differentiable ℂ (fun s : ℂ => (p : ℂ)^(-s)) := by
  rw [negative_power_exp hp]
  exact differentiable_exp.comp ((differentiable_const _).mul differentiable_id)

theorem negative_power_bound {p : ℕ} (hp : 0<p) :
    FinitenessFiniteOrder.Bound (fun s : ℂ => (p : ℂ)^(-s)) := by
  rw [negative_power_exp hp]
  exact FinitenessFiniteOrder.exp_linear _

theorem shiftLocal_entire {d p : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (hp : 0<p) (a : ℕ) : Differentiable ℂ (fun s => shiftLocal χ f s p a) := by
  by_cases ha : a=0
  · simp only [shiftLocal,ha]
    exact differentiable_const _
  · simp only [shiftLocal,ite_eq_right ha]
    exact (differentiable_const _).sub ((negative_power_entire hp).const_mul _)

theorem shiftLocal_bound {d p : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (hp : 0<p) (a : ℕ) : FinitenessFiniteOrder.Bound (fun s => shiftLocal χ f s p a) := by
  by_cases ha : a=0
  · simp only [shiftLocal,ha]
    exact bound_const _
  · simp only [shiftLocal,ite_eq_right ha]
    exact FinitenessFiniteOrderClosure.sub (bound_const _)
      (FinitenessFiniteOrder.mul (bound_const _) (negative_power_bound hp))

theorem shiftProduct_entire {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (r : ℕ) : Differentiable ℂ (shiftProduct χ f r) := by
  unfold shiftProduct Finsupp.prod
  apply Differentiable.fun_finsetProd
  intro p hp
  exact shiftLocal_entire χ f (Nat.prime_of_mem_primeFactors (by simpa using hp)).pos _

theorem shiftProduct_bound {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (r : ℕ) : FinitenessFiniteOrder.Bound (shiftProduct χ f r) := by
  unfold shiftProduct Finsupp.prod
  apply FinitenessFiniteOrderClosure.prod
  intro p hp
  exact shiftLocal_bound χ f (Nat.prime_of_mem_primeFactors (by simpa using hp)).pos _

theorem finiteOrderBound_sum {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i∈t, FinitenessFiniteOrder.Bound (F i)) :
    FinitenessFiniteOrder.Bound (fun s => ∑ i∈t, F i s) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using bound_const (0 : ℂ)
  | @insert i t hi ih =>
      simpa only [Finset.sum_insert hi] using FinitenessFiniteOrderClosure.add
        (hF i (Finset.mem_insert_self _ _)) (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem inducedMultiplier_entire {d r : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (hr : 0<r) : Differentiable ℂ (inducedMultiplier χ f r) := by
  unfold inducedMultiplier
  apply Differentiable.fun_sum
  intro h hh
  have ht : 0<r/h := Nat.div_pos (Nat.le_of_dvd hr (Nat.dvd_of_mem_divisors hh))
    (Nat.pos_of_mem_divisors hh)
  exact ((negative_power_entire ht).const_mul _).mul (shiftProduct_entire (star χ) f _)

theorem inducedMultiplier_bound {d r : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (hr : 0<r) : FinitenessFiniteOrder.Bound (inducedMultiplier χ f r) := by
  unfold inducedMultiplier
  apply finiteOrderBound_sum
  intro h hh
  have ht : 0<r/h := Nat.div_pos (Nat.le_of_dvd hr (Nat.dvd_of_mem_divisors hh))
    (Nat.pos_of_mem_divisors hh)
  exact FinitenessFiniteOrder.mul
    (FinitenessFiniteOrder.mul (bound_const _) (negative_power_bound ht))
    (shiftProduct_bound (star χ) f _)

def completedInducedMultiplier {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (r : ℕ) (s : ℂ) : ℂ := scale r 2 s*inducedMultiplier χ f r s

theorem completedInducedMultiplier_entire {d r : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) (hr : 0<r) :
    Differentiable ℂ (completedInducedMultiplier χ f r) :=
  (scale_entire r 2).mul (inducedMultiplier_entire χ f hr)

theorem completedInducedMultiplier_bound {d r : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) (hr : 0<r) :
    FinitenessFiniteOrder.Bound (completedInducedMultiplier χ f r) :=
  FinitenessFiniteOrder.mul (scale_bound r 2) (inducedMultiplier_bound χ f hr)

theorem induced_completed_identity {N d r k : ℕ} [NeZero d] [NeZero (d*r)]
    {f : ℕ → ℂ} (hf : EulerData N f) (hr : 0<r) (hrN : r.Coprime N)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : LSeriesSummable (multiplicativeTwisted d f (star χ)) s) :
    completed (N*(d*r)^2) k
      (characterTwisted (d*r) f (DirichletCharacter.changeLevel (dvd_mul_right d r) χ)) s=
      completedInducedMultiplier χ f r s*completed (N*d^2) k (characterTwisted d f χ) s := by
  obtain ⟨hss,he⟩ := induced_series_identity hf hr hrN hχ hs
  have hprim : characterTwisted d f χ=gauss χ • multiplicativeTwisted d f (star χ) := by
    funext n
    exact characterTwisted_primitive f hχ n
  have hsp : LSeriesSummable (characterTwisted d f χ) s := by
    rw [hprim]
    exact hs.smul _
  have hz (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) : characterTwisted q f ψ 0=0 := by
    simp [characterTwisted,QuantitativeArithmeticWeightedFourierTwist.twisted,hf.zero]
  have hL : L (characterTwisted (d*r) f
      (DirichletCharacter.changeLevel (dvd_mul_right d r) χ)) s=
      inducedMultiplier χ f r s*L (characterTwisted d f χ) s := by
    rw [FinitenessEulerIdentification.L_eq_mathlib (hz _ _) hss,
      FinitenessEulerIdentification.L_eq_mathlib (hz _ _) hsp]
    exact he
  unfold completed completedInducedMultiplier
  rw [hL,show N*(d*r)^2=r^2*(N*d^2) by ring,Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow,
    ← FinitenessNormalizedTwistProduct.scale_as_cpow hr 2 s]
  ring

#print axioms completedInducedMultiplier_entire
#print axioms completedInducedMultiplier_bound
#print axioms induced_completed_identity

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## MultiplierProduct -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex ArithmeticFunction FinitenessTwistExponential

theorem characterScale_multiplicative {d : ℕ} (χ : DirichletCharacter ℂ d)
    {F : ArithmeticFunction ℂ} (hF : F.IsMultiplicative) :
    (characterScale χ F).IsMultiplicative := by
  constructor
  · simp [characterScale,hF.1]
  · intro r t h
    change χ ((r*t : ℕ) : ZMod d)*F (r*t)=(χ (r : ZMod d)*F r)*(χ (t : ZMod d)*F t)
    rw [Nat.cast_mul,map_mul,hF.2 h]
    ring

def weightedShiftFunction {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun r => (r : ℂ)*(r : ℂ)^(-s)*shiftProduct χ f r s,by simp⟩

theorem weightedShiftFunction_multiplicative {d : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) (s : ℂ) :
    (weightedShiftFunction χ f s).IsMultiplicative := by
  constructor
  · simp [weightedShiftFunction,shiftProduct]
  · intro r t h
    change ((r*t : ℕ) : ℂ)*((r*t : ℕ) : ℂ)^(-s)*shiftProduct χ f (r*t) s=_
    rw [shiftProduct_mul χ f h,Nat.cast_mul,natCast_mul_natCast_cpow]
    change _=((r : ℂ)*(r : ℂ)^(-s)*shiftProduct χ f r s)*
      ((t : ℂ)*(t : ℂ)^(-s)*shiftProduct χ f t s)
    ring

def inducedMultiplierFunction {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    (s : ℂ) : ArithmeticFunction ℂ :=
  characterScale χ (ArithmeticFunction.moebius : ArithmeticFunction ℂ)*
    weightedShiftFunction (star χ) f s

theorem inducedMultiplierFunction_apply {d : ℕ} (χ : DirichletCharacter ℂ d)
    (f : ℕ → ℂ) (r : ℕ) (s : ℂ) :
    inducedMultiplierFunction χ f s r=inducedMultiplier χ f r s := by
  rw [inducedMultiplierFunction,mul_apply,Nat.sum_divisorsAntidiagonal
    (fun h t => characterScale χ (ArithmeticFunction.moebius : ArithmeticFunction ℂ) h*
      weightedShiftFunction (star χ) f s t)]
  unfold inducedMultiplier
  apply Finset.sum_congr rfl
  intro h _
  simp only [characterScale,weightedShiftFunction,ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply]
  ring

theorem inducedMultiplierFunction_multiplicative {d : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) (s : ℂ) :
    (inducedMultiplierFunction χ f s).IsMultiplicative :=
  (characterScale_multiplicative χ ArithmeticFunction.isMultiplicative_moebius.intCast).mul
    (weightedShiftFunction_multiplicative (star χ) f s)

theorem inducedMultiplier_mul {d : ℕ} (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ)
    {r t : ℕ} (h : r.Coprime t) (s : ℂ) :
    inducedMultiplier χ f (r*t) s=inducedMultiplier χ f r s*inducedMultiplier χ f t s := by
  simpa only [inducedMultiplierFunction_apply] using
    (inducedMultiplierFunction_multiplicative χ f s).2 h

theorem scale_two_mul {r t : ℕ} (hr : 0<r) (ht : 0<t) (s : ℂ) :
    scale (r*t) 2 s=scale r 2 s*scale t 2 s := by
  rw [FinitenessNormalizedTwistProduct.scale_as_cpow (Nat.mul_pos hr ht),
    FinitenessNormalizedTwistProduct.scale_as_cpow hr,
    FinitenessNormalizedTwistProduct.scale_as_cpow ht,mul_pow,Nat.cast_mul,
    natCast_mul_natCast_cpow]

theorem completedInducedMultiplier_mul {d r t : ℕ} (χ : DirichletCharacter ℂ d)
    (f : ℕ → ℂ) (hr : 0<r) (ht : 0<t) (h : r.Coprime t) (s : ℂ) :
    completedInducedMultiplier χ f (r*t) s=
      completedInducedMultiplier χ f r s*completedInducedMultiplier χ f t s := by
  unfold completedInducedMultiplier
  rw [scale_two_mul hr ht,inducedMultiplier_mul χ f h]
  ring

def completedInducedMultiplierFunction {d : ℕ} (χ : DirichletCharacter ℂ d)
    (f : ℕ → ℂ) (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun r => completedInducedMultiplier χ f r s,by simp [completedInducedMultiplier,inducedMultiplier]⟩

theorem completedInducedMultiplierFunction_multiplicative {d : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) (s : ℂ) :
    (completedInducedMultiplierFunction χ f s).IsMultiplicative := by
  constructor
  · simp [completedInducedMultiplierFunction,completedInducedMultiplier,
      inducedMultiplier,shiftProduct,scale,power]
  · intro r t h
    change completedInducedMultiplier χ f (r*t) s=
      completedInducedMultiplier χ f r s*completedInducedMultiplier χ f t s
    by_cases hr : r=0
    · simp [hr,completedInducedMultiplier,inducedMultiplier]
    by_cases ht : t=0
    · simp [ht,completedInducedMultiplier,inducedMultiplier]
    exact completedInducedMultiplier_mul χ f (Nat.pos_of_ne_zero hr) (Nat.pos_of_ne_zero ht) h s

/-- The completed correction factors into local prime-power corrections.
Reciprocity can therefore be checked by a fixed quadratic calculation. -/
theorem completedInducedMultiplier_factorization {d : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) {r : ℕ} (hr : r≠0) (s : ℂ) :
    completedInducedMultiplier χ f r s=
      r.factorization.prod (fun p a => completedInducedMultiplier χ f (p^a) s) :=
  (completedInducedMultiplierFunction_multiplicative χ f s).multiplicative_factorization
    (completedInducedMultiplierFunction χ f s) hr

#print axioms completedInducedMultiplier_factorization

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## LocalMultiplier -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex ArithmeticFunction FinitenessEulerLocal

theorem moebius_character_prime_power {d : ℕ} (χ : DirichletCharacter ℂ d)
    (F : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (characterScale χ (ArithmeticFunction.moebius : ArithmeticFunction ℂ)*F) (p^(j+1))=
      F (p^(j+1))-χ (p : ZMod d)*F (p^j) := by
  rw [mul_apply,Nat.sum_divisorsAntidiagonal
    (fun h t => characterScale χ (ArithmeticFunction.moebius : ArithmeticFunction ℂ) h*F t),
    Nat.sum_divisors_prime_pow hp,Finset.sum_range_succ',Finset.sum_range_succ']
  have hz : (∑ i ∈ Finset.range j,
      characterScale χ (ArithmeticFunction.moebius : ArithmeticFunction ℂ) (p^((i+1)+1))*
        F (p^(j+1)/p^((i+1)+1)))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [characterScale,ArithmeticFunction.moebius_apply_prime_pow hp (by omega : (i+1)+1≠0)]
  rw [hz]
  have hd : p^(j+1)/p=p^j := by
    rw [pow_succ',Nat.mul_div_right _ hp.pos]
  simp [characterScale,ArithmeticFunction.moebius_apply_prime hp,hd,sub_eq_add_neg]
  ring

theorem inducedMultiplier_prime_power_difference {d : ℕ} (χ : DirichletCharacter ℂ d)
    (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) (s : ℂ) :
    inducedMultiplier χ f (p^(j+1)) s=
      weightedShiftFunction (star χ) f s (p^(j+1))-
        χ (p : ZMod d)*weightedShiftFunction (star χ) f s (p^j) := by
  rw [← inducedMultiplierFunction_apply,inducedMultiplierFunction]
  exact moebius_character_prime_power χ _ hp j

def localInducedPolynomial (p a u v : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  match j with
  | 0 => p*a*z-u-p*v*z^2
  | j+1 => p^(j+1)*z^(j+1)*
      ((p*coeff a 1 (j+2)+u*v*coeff a 1 j)*z-
        coeff a 1 (j+1)*(u+p*v*z^2))

theorem weightedShift_prime_power {d : ℕ} (χ : DirichletCharacter ℂ d)
    (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) (s : ℂ) :
    weightedShiftFunction χ f s (p^(j+1))=
      (p : ℂ)^(j+1)*((p : ℂ)^(-s))^(j+1)*
        (coeff (f p) 1 (j+1)-coeff (f p) 1 j*χ (p : ZMod d)*(p : ℂ)^(-s)) := by
  change ((p^(j+1) : ℕ) : ℂ)*((p^(j+1) : ℕ) : ℂ)^(-s)*
    shiftProduct χ f (p^(j+1)) s=_
  rw [shiftProduct_prime_pow χ f hp,Nat.cast_pow,← natCast_cpow_natCast_mul,cpow_nat_mul]

theorem inducedMultiplier_local {d : ℕ} (χ : DirichletCharacter ℂ d)
    (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (j : ℕ) (s : ℂ) :
    inducedMultiplier χ f (p^(j+1)) s=
      localInducedPolynomial (p : ℂ) (f p) (χ (p : ZMod d))
        ((star χ) (p : ZMod d)) j ((p : ℂ)^(-s)) := by
  rw [inducedMultiplier_prime_power_difference χ f hp,weightedShift_prime_power (star χ) f hp]
  cases j with
  | zero =>
      simp [localInducedPolynomial,weightedShiftFunction,shiftProduct,coeff]
      ring
  | succ j =>
      rw [weightedShift_prime_power (star χ) f hp]
      simp only [localInducedPolynomial,pow_succ]
      ring

/-- The local quadratic symmetry is valid even when both character
values vanish. No assumption on a local unitary parameter is required. -/
theorem paired_quadratic_reciprocity (A B u v : ℂ) {p z : ℂ}
    (hp : p≠0) (hz : z≠0) :
    p*z^2*(A*(p*z)⁻¹-B*(v+p*u*((p*z)⁻¹)^2))=A*z-B*(u+p*v*z^2) := by
  field_simp
  ring

theorem paired_monomial_reciprocity (A B u v : ℂ) (j : ℕ) {p z : ℂ}
    (hp : p≠0) (hz : z≠0) :
    p^j*z^j*(A*z-B*(u+p*v*z^2))=
      p^(j+1)*z^(2*(j+1))*
        (p^j*((p*z)⁻¹)^j*(A*(p*z)⁻¹-B*(v+p*u*((p*z)⁻¹)^2))) := by
  have H := FinitenessEulerTwistReciprocity.monomial_transport (p^j) j
    (fun w => A*w-B*(v+p*u*w^2)) hp hz (p*z^2)
  rw [paired_quadratic_reciprocity A B u v hp hz] at H
  have he : (p*z^2)^j*(p*z^2)=p^(j+1)*z^(2*(j+1)) := by
    rw [← pow_succ,mul_pow,pow_mul]
  rw [he] at H
  exact H.symm

theorem localInducedPolynomial_reciprocal (a u v : ℂ) (j : ℕ) {p z : ℂ}
    (hp : p≠0) (hz : z≠0) :
    localInducedPolynomial p a u v j z=
      p^(j+1)*z^(2*(j+1))*localInducedPolynomial p a v u j ((p*z)⁻¹) := by
  cases j with
  | zero =>
      have H := paired_quadratic_reciprocity (p*a) 1 u v hp hz
      simp only [localInducedPolynomial,one_mul] at H ⊢
      linear_combination -H
  | succ j =>
      have H := paired_monomial_reciprocity
        (p*coeff a 1 (j+2)+u*v*coeff a 1 j) (coeff a 1 (j+1)) u v (j+1) hp hz
      simpa only [localInducedPolynomial,mul_comm v u] using H

#print axioms inducedMultiplier_local
#print axioms localInducedPolynomial_reciprocal

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## InducedContinuation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessInputBounds

theorem multiplicativeTwisted_growth {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {f : ℕ → ℂ} {τ : ℝ} (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) :
    multiplicativeTwisted d f χ =O[atTop] (fun n : ℕ => (n : ℝ)^τ) := by
  have hb : (fun n : ℕ => χ (n : ZMod d)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro n
    simpa using χ.norm_le_one (n : ZMod d)
  unfold multiplicativeTwisted
  simpa only [mul_one] using hf.mul hb

/-- Entire continuation and finite order for an imprimitive character
are consequences of the inducing primitive continuation and the original
Euler relations. No imprimitive analytic hypothesis is used. The paired
functional equation is a separate reciprocal-polynomial step. -/
theorem induced_entire_continuation {N d r k : ℕ} [NeZero d] [NeZero (d*r)]
    {f : ℕ → ℂ} (hf : EulerData N f) (hr : 0<r) (hrN : r.Coprime N)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (A : ℂ → ℂ) (hhol : Differentiable ℂ A) (hord : FiniteOrder A)
    (hagree : ∃ c : ℝ, ∀ s : ℂ, c<s.re →
      A s=completed (N*d^2) k (characterTwisted d f χ) s) :
    ∃ B : ℂ → ℂ, Differentiable ℂ B ∧ FiniteOrder B ∧
      (∃ c : ℝ, ∀ s : ℂ, c<s.re →
        B s=completed (N*(d*r)^2) k
          (characterTwisted (d*r) f (DirichletCharacter.changeLevel (dvd_mul_right d r) χ)) s) ∧
      (∀ s, B s=completedInducedMultiplier χ f r s*A s) := by
  refine ⟨fun s => completedInducedMultiplier χ f r s*A s,
    (completedInducedMultiplier_entire χ f hr).mul hhol,?_,?_,fun _ => rfl⟩
  · exact bound_finiteOrder (FinitenessFiniteOrder.mul
      (completedInducedMultiplier_bound χ f hr) (finiteOrder_bound hhol.continuous hord))
  · obtain ⟨a,ha⟩ := hagree
    obtain ⟨τ,_,hg⟩ := hf.growth
    refine ⟨max a (τ+1),fun s hs => ?_⟩
    have hsum : LSeriesSummable (multiplicativeTwisted d f (star χ)) s := by
      apply LSeriesSummable_of_isBigO_rpow (lt_of_le_of_lt (le_max_right _ _) hs)
      simpa only [add_sub_cancel_right] using multiplicativeTwisted_growth (star χ) hg
    dsimp only
    rw [ha s (lt_of_le_of_lt (le_max_left _ _) hs)]
    exact (induced_completed_identity hf hr hrN hχ hsum).symm

#print axioms induced_entire_continuation

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## MultiplierReciprocity -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex FinitenessTwistExponential

theorem scale_prime_power (p a : ℕ) (s : ℂ) :
    scale (p^a) 2 s=scale p (2*a) s := by
  unfold scale power
  rw [Nat.cast_pow,Real.log_pow]
  congr 1
  push_cast
  ring

theorem completedInducedMultiplier_prime_reciprocal {d : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime)
    (j : ℕ) (s : ℂ) :
    completedInducedMultiplier χ f (p^(j+1)) s=
      completedInducedMultiplier (star χ) f (p^(j+1)) (1-s) := by
  have hp0 : (p : ℂ)≠0 := by exact_mod_cast hp.ne_zero
  unfold completedInducedMultiplier
  rw [scale_prime_power,scale_prime_power,inducedMultiplier_local χ f hp,
    inducedMultiplier_local (star χ) f hp,star_star,
    ← power_eq hp.pos (-s),← power_eq hp.pos (-(1-s)),
    localInducedPolynomial_reciprocal (f p) (χ (p : ZMod d))
      ((star χ) (p : ZMod d)) j hp0 (power_ne_zero p (-s)),
    ← reflected hp.pos s,good_scalar hp.pos j,← mul_assoc]
  have ht := scale_transport p (2*(j+1)) s
  push_cast at ht
  rw [ht]

theorem completedInducedMultiplier_prime_reciprocal_all {d : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime)
    (a : ℕ) (s : ℂ) :
    completedInducedMultiplier χ f (p^a) s=
      completedInducedMultiplier (star χ) f (p^a) (1-s) := by
  cases a with
  | zero => simp [completedInducedMultiplier,inducedMultiplier,shiftProduct,scale,power]
  | succ j => exact completedInducedMultiplier_prime_reciprocal χ f hp j s

/-- The completed imprimitive correction has the paired reciprocal
symmetry for arbitrary positive modulus ratio. This is a proved finite
algebraic identity; no functional equation is assumed for the correction. -/
theorem completedInducedMultiplier_reciprocal {d : ℕ}
    (χ : DirichletCharacter ℂ d) (f : ℕ → ℂ) {r : ℕ} (hr : r≠0) (s : ℂ) :
    completedInducedMultiplier χ f r s=
      completedInducedMultiplier (star χ) f r (1-s) := by
  rw [completedInducedMultiplier_factorization χ f hr,
    completedInducedMultiplier_factorization (star χ) f hr]
  unfold Finsupp.prod
  apply Finset.prod_congr rfl
  intro p hp
  exact completedInducedMultiplier_prime_reciprocal_all χ f
    (Nat.prime_of_mem_primeFactors (by simpa using hp)) _ s

theorem induced_pair_functional_equation {d r : ℕ} (χ : DirichletCharacter ℂ d)
    (f : ℕ → ℂ) (hr : r≠0) (A B : ℂ → ℂ) (ε : ℂ)
    (hFE : ∀ s, A s=ε*B (1-s)) (s : ℂ) :
    completedInducedMultiplier χ f r s*A s=
      ε*(completedInducedMultiplier (star χ) f r (1-s)*B (1-s)) := by
  rw [completedInducedMultiplier_reciprocal χ f hr,hFE]
  ring

#print axioms completedInducedMultiplier_reciprocal
#print axioms induced_pair_functional_equation

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## LiftedPair -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex Filter Set FinitenessOriginalInput
open scoped Topology

structure CharacterContinuation (N k : ℕ) (f : ℕ → ℂ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (A : ℂ → ℂ) : Prop where
  holomorphic : Differentiable ℂ A
  finiteOrder : FiniteOrder A
  agrees : ∃ c : ℝ, ∀ s : ℂ, c<s.re → A s=completed (N*q^2) k (characterTwisted q f χ) s

theorem entire_eq_of_halfplane {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (c : ℝ) (he : ∀ s : ℂ, c<s.re → A s=B s) : A=B := by
  have hnear : A =ᶠ[𝓝 ((c+1 : ℝ) : ℂ)] B := by
    have ho : IsOpen {s : ℂ | c<s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hm : ((c+1 : ℝ) : ℂ) ∈ {s : ℂ | c<s.re} := by simp
    filter_upwards [ho.mem_nhds hm] with s hs
    exact he s hs
  exact (show AnalyticOnNhd ℂ A univ from fun z _ => hA.analyticAt z).eq_of_eventuallyEq
    (show AnalyticOnNhd ℂ B univ from fun z _ => hB.analyticAt z) hnear

theorem CharacterContinuation.unique {N k q : ℕ} [NeZero q] {f : ℕ → ℂ}
    {χ : DirichletCharacter ℂ q} {A B : ℂ → ℂ}
    (hA : CharacterContinuation N k f χ A) (hB : CharacterContinuation N k f χ B) : A=B := by
  obtain ⟨a,ha⟩ := hA.agrees
  obtain ⟨b,hb⟩ := hB.agrees
  apply entire_eq_of_halfplane hA.holomorphic hB.holomorphic (max a b)
  intro s hs
  rw [ha s (lt_of_le_of_lt (le_max_left _ _) hs),hb s (lt_of_le_of_lt (le_max_right _ _) hs)]

theorem changeLevel_star {d q : ℕ} (χ : DirichletCharacter ℂ d) (hd : d ∣ q) :
    DirichletCharacter.changeLevel hd (star χ)=star (DirichletCharacter.changeLevel hd χ) := by
  simp only [MulChar.star_eq_inv,map_inv]

theorem changeLevel_neg_nat {d q N : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ d) (hd : d ∣ q) (hc : q.Coprime N) :
    (DirichletCharacter.changeLevel hd χ) (-(N : ZMod q))=χ (-(N : ZMod d)) := by
  have hu : IsUnit (-(N : ZMod q)) :=
    ((ZMod.isUnit_iff_coprime N q).mpr hc.symm).neg
  have he := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd hu.unit
  rw [hu.unit_spec,ZMod.cast_neg hd,ZMod.cast_natCast hd] at he
  exact he

/-- A primitive pair lifts to every multiple of its conductor coprime
to the level, including both actual continuations and their paired FE. -/
theorem induced_pair_continuations {N k d q : ℕ} [NeZero d] [NeZero q]
    {f : ℕ → ℂ} (hf : EulerData N f) (hd : d ∣ q) (hc : q.Coprime N)
    {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (ε : ℂ)
    (A B : ℂ → ℂ) (hA : CharacterContinuation N k f χ A)
    (hB : CharacterContinuation N k f (star χ) B)
    (hFE : ∀ s, A s=ε*star (χ (-(N : ZMod d)))*B (1-s)) :
    ∃ C D : ℂ → ℂ,
      CharacterContinuation N k f (DirichletCharacter.changeLevel hd χ) C ∧
      CharacterContinuation N k f (star (DirichletCharacter.changeLevel hd χ)) D ∧
      (∀ s, C s=ε*star ((DirichletCharacter.changeLevel hd χ) (-(N : ZMod q)))*D (1-s)) := by
  obtain ⟨r,rfl⟩ := hd
  have hr : 0<r := Nat.pos_of_ne_zero (right_ne_zero_of_mul (NeZero.ne (d*r)))
  have hrN : r.Coprime N := hc.of_dvd_left (dvd_mul_left r d)
  obtain ⟨C,hCh,hCo,hCa,hCe⟩ := induced_entire_continuation hf hr hrN hχ
    A hA.holomorphic hA.finiteOrder hA.agrees
  obtain ⟨D,hDh,hDo,hDa,hDe⟩ := induced_entire_continuation hf hr hrN (primitive_star hχ)
    B hB.holomorphic hB.finiteOrder hB.agrees
  refine ⟨C,D,⟨hCh,hCo,hCa⟩,?_,?_⟩
  · rw [changeLevel_star] at hDa
    exact ⟨hDh,hDo,hDa⟩
  · intro s
    rw [hCe,hDe,changeLevel_neg_nat χ _ hc]
    exact induced_pair_functional_equation χ f hr.ne' A B _ hFE s

#print axioms CharacterContinuation.unique
#print axioms induced_pair_continuations

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## AllCharacters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex FinitenessOriginalInput

/-- Primitive data at the divisors of q suffice for every character modulo q.
Uniqueness of entire continuation makes the separately lifted dual pairs
coherent, without making arbitrary primitive-character choices compatible. -/
theorem all_character_continuations {N k q : ℕ} [NeZero q]
    {f : ℕ → ℂ} (hf : EulerData N f) (hc : q.Coprime N) (ε : ℂ)
    (h : ∀ d : ℕ, d ∣ q → ∀ hd : 0<d,
      letI : NeZero d := ⟨hd.ne'⟩
      ∃ A : DirichletCharacter ℂ d → ℂ → ℂ,
        (∀ χ, χ.IsPrimitive → CharacterContinuation N k f χ (A χ)) ∧
        (∀ χ, χ.IsPrimitive → ∀ s,
          A χ s=ε*star (χ (-(N : ZMod d)))*A (star χ) (1-s))) :
    ∃ A : DirichletCharacter ℂ q → ℂ → ℂ,
      (∀ χ, CharacterContinuation N k f χ (A χ)) ∧
      (∀ χ s, A χ s=ε*star (χ (-(N : ZMod q)))*A (star χ) (1-s)) := by
  classical
  have pairs : ∀ χ : DirichletCharacter ℂ q, ∃ A B : ℂ → ℂ,
      CharacterContinuation N k f χ A ∧
      CharacterContinuation N k f (star χ) B ∧
      (∀ s, A s=ε*star (χ (-(N : ZMod q)))*B (1-s)) := by
    intro χ
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    obtain ⟨A,hA,hFE⟩ := h χ.conductor χ.conductor_dvd_level
      (Nat.pos_of_ne_zero χ.conductor_ne_zero)
    have hp := χ.primitiveCharacter_isPrimitive
    have pair := induced_pair_continuations hf χ.conductor_dvd_level hc hp ε
      (A χ.primitiveCharacter) (A (star χ.primitiveCharacter))
      (hA _ hp) (hA _ (primitive_star hp)) (hFE _ hp)
    simpa only [DirichletCharacter.changeLevel_primitiveCharacter] using pair
  choose A B hA hB hFE using pairs
  refine ⟨A,hA,fun χ s => ?_⟩
  rw [hFE χ s,CharacterContinuation.unique (hB χ) (hA (star χ))]

#print axioms all_character_continuations

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Cusps -/
section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Matrix UpperHalfPlane SmallLevelNormalized AsymptoticCongruenceLabels
open scoped MatrixGroups ModularForm

/-- Every integral cusp representative at prime level is either in
Gamma0 or Gamma0 times Fricke times an upper triangular real matrix. -/
theorem prime_cusp_factorization {p : ℕ} (hp : p.Prime) (A : SL(2, ℤ)) :
    A ∈ CongruenceSubgroup.Gamma0 p ∨
      ∃ B : SL(2, ℤ), B ∈ CongruenceSubgroup.Gamma0 p ∧
        ∃ U : GL (Fin 2) ℝ, U 1 0=0 ∧
          SpecialLinearGroup.mapGL ℝ A=
            SpecialLinearGroup.mapGL ℝ B*fricke p hp.pos*U := by
  by_cases hA : A ∈ CongruenceSubgroup.Gamma0 p
  · exact Or.inl hA
  right
  have hn : ¬ (p : ℤ) ∣ A 1 0 := by simpa only [gamma0_mem_dvd] using hA
  have hcp : IsCoprime (A 1 0) (p : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    have h := (hp.coprime_iff_not_dvd.mpr (fun h => hn (Int.natCast_dvd.mpr h))).symm.gcd_eq_one
    simpa only [Int.gcd_def,Int.natAbs_natCast] using h
  have hdet := A.property
  rw [det_fin_two] at hdet
  change A 0 0*A 1 1-A 0 1*A 1 0=1 at hdet
  have hca : IsCoprime (A 1 0) (A 0 0) :=
    ⟨-A 0 1,A 1 1,by nlinarith [hdet]⟩
  obtain ⟨x,y,hxy⟩ := hcp.mul_right hca
  let B : SL(2, ℤ) := ⟨!![x,A 0 0;-(p : ℤ)*y,A 1 0],by
    rw [det_fin_two]
    change x*A 1 0-A 0 0*(-(p : ℤ)*y)=1
    nlinarith [hxy]⟩
  have hB : B ∈ CongruenceSubgroup.Gamma0 p := by
    rw [gamma0_mem_dvd]
    exact ⟨-y,by change -(p : ℤ)*y=(p : ℤ)*(-y); ring⟩
  let U := (fricke p hp.pos)⁻¹*SpecialLinearGroup.mapGL ℝ (B⁻¹*A)
  have hU : U 1 0=0 := by
    dsimp only [U]
    rw [fricke_inverse_eq_negative]
    change (((GeneralLinearGroup.scalar (Fin 2) (-1)*fricke p hp.pos).val)*
      (B⁻¹*A).val.map (fun n : ℤ => (n : ℝ))) 1 0=0
    simp [GeneralLinearGroup.scalar,Matrix.scalar,fricke,matrix,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.adjugate_fin_two,B,mul_comm,Matrix.vecMul,dotProduct]
  refine ⟨B,hB,U,hU,?_⟩
  simp only [U,← mul_assoc,mul_inv_cancel_right,← map_mul,mul_inv_cancel,one_mul]

/-- Vanishing at infinity and the Fricke cusp propagates to every cusp
at prime level, without using Euler relations. -/
theorem prime_all_cusp_vanishing {p : ℕ} (hp : p.Prime) (k : ℤ) (F : ℍ → ℂ)
    (hinv : ∀ g ∈ realGamma0 p, F ∣[k] g=F)
    (hzero : IsZeroAtImInfty F)
    (hwzero : IsZeroAtImInfty (F ∣[k] fricke p hp.pos)) (A : SL(2, ℤ)) :
    IsZeroAtImInfty (F ∣[k] SpecialLinearGroup.mapGL ℝ A) := by
  rcases prime_cusp_factorization hp A with hA | ⟨B,hB,U,hU,he⟩
  · simpa only [hinv _ ⟨A,hA,rfl⟩] using hzero
  · rw [he,SlashAction.slash_mul,SlashAction.slash_mul,hinv _ ⟨B,hB,rfl⟩]
    exact hwzero.slash k hU

#print axioms prime_cusp_factorization
#print axioms prime_all_cusp_vanishing

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## CuspForm -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex UpperHalfPlane SmallLevelNormalized Filter Asymptotics Matrix
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm Manifold Topology

theorem fourier_zeroAtInfty_of_growth {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (k : ℕ) :
    IsZeroAtImInfty (fun z : ℍ => fourier (fullCoefficients f k) z) := by
  have hs := (FinitenessPolynomialSeries.has_series
    (polynomial_bound hf0 hf k)).differentiableAt.continuousAt
  have hq := ((Function.Periodic.qParam_tendsto (by norm_num : (0 : ℝ)<1)).mono_right
    nhdsWithin_le_nhds).comp tendsto_coe_atImInfty
  have hh := hs.tendsto.comp hq
  rw [FinitenessPolynomialSeries.zero (fullCoefficients_zero hf0 k)] at hh
  exact hh

theorem forward_fricke_of_small_twists {p m : ℕ} (hp : 0<p)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) (h : SmallTwistContinuations p (2*m) f ε) :
    (fun z : ℍ => fourier (fullCoefficients f (2*m)) z) ∣[((2*m : ℕ) : ℤ)] fricke p hp=
      (ε*Complex.I^(2*m)) • (fun z : ℍ => fourier (fullCoefficients f (2*m)) z) := by
  have hnorm : ‖ε‖=1 := by rcases hε with rfl | rfl <;> norm_num
  have hsq := fricke_scalar_square m ε hε
  have hw := inverse_fricke_of_small_twists hp hf0 hf ε hnorm h
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[((2*m : ℕ) : ℤ)] fricke p hp) hw
  rw [← SlashAction.slash_mul,inv_mul_cancel,SlashAction.slash_one,
    det_one_smul _ (fricke_det p hp)] at hh
  have he := congrArg (fun F : ℍ → ℂ => (ε*Complex.I^(2*m)) • F) hh
  simpa only [smul_smul,hsq,one_smul] using he.symm

/-- Actual Mathlib cusp-form construction from the small-twist hypotheses.
This is the linear converse theorem, without any Euler-product assumption. -/
def smallTwistCuspForm {p m : ℕ} (hp : p.Prime)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) (h : SmallTwistContinuations p (2*m) f ε) :
    CuspForm (realGamma0 p) ((2*m : ℕ) : ℤ) := by
  let F : ℍ → ℂ := fun z => fourier (fullCoefficients f (2*m)) z
  have hinv := gamma0_invariance_of_small_twists hp hf0 hf ε hε h
  have hzero : IsZeroAtImInfty F := fourier_zeroAtInfty_of_growth hf0 hf (2*m)
  have hwzero : IsZeroAtImInfty (F ∣[((2*m : ℕ) : ℤ)] fricke p hp.pos) := by
    rw [forward_fricke_of_small_twists hp.pos hf0 hf ε hε h]
    change Tendsto (fun z : ℍ => (ε*Complex.I^(2*m))*F z) atImInfty (𝓝 0)
    simpa only [mul_zero] using hzero.const_mul (ε*Complex.I^(2*m))
  exact {
    toFun := F
    slash_action_eq' := hinv
    holo' := by
      intro z
      exact (holomorphic (polynomial_bound hf0 hf (2*m)) z.im_pos).mdifferentiableAt.comp z
        (mdifferentiable_coe z)
    zero_at_cusps' := by
      intro c hc
      have hle : realGamma0 p ≤ 𝒮ℒ := by
        rintro g ⟨A,_,rfl⟩
        exact ⟨A,rfl⟩
      apply (OnePoint.isZeroAt_iff_forall_SL2Z (hc.mono hle)).mpr
      intro A _
      exact prime_all_cusp_vanishing hp _ F hinv hzero hwzero A }

theorem smallTwistCuspForm_coe {p m : ℕ} (hp : p.Prime)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) (h : SmallTwistContinuations p (2*m) f ε) :
    (smallTwistCuspForm hp hf0 hf ε hε h : ℍ → ℂ)=
      (fun z : ℍ => fourier (fullCoefficients f (2*m)) z) := rfl

#print axioms smallTwistCuspForm
#print axioms smallTwistCuspForm_coe

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## Theorem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex UpperHalfPlane SmallLevelNormalized Filter Asymptotics Matrix
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

theorem small_prime_window {p : ℕ} (hp : p.Prime) (q : ℕ) :
    q≤p.sqrt ↔ (q : ℝ)<Real.sqrt p := by
  have hp0 : (0 : ℝ)≤p := Nat.cast_nonneg p
  have hs := Real.sq_sqrt hp0
  have hs0 := Real.sqrt_nonneg (p : ℝ)
  have hq0 : (0 : ℝ)≤q := Nat.cast_nonneg q
  have hne : q^2 ≠ p := by
    intro he
    have hd : q ∣ p := ⟨q,by simpa only [pow_two] using he.symm⟩
    rcases (Nat.dvd_prime hp).mp hd with hq | hq
    · rw [hq] at he
      norm_num at he
      exact hp.ne_one he.symm
    · rw [hq] at he
      nlinarith [hp.two_le]
  rw [Nat.le_sqrt']
  constructor
  · intro h
    have hlt : (q : ℝ)^2<(p : ℝ) := by exact_mod_cast lt_of_le_of_ne h hne
    nlinarith
  · intro h
    have hlt : (q : ℝ)^2<(p : ℝ) := by nlinarith
    exact_mod_cast hlt.le

/-- Literal analytic hypotheses in the strict real window q<sqrt(p). -/
def SmallTwistContinuationsBelowSqrt (p k : ℕ) (f : ℕ → ℂ) (ε : ℂ) : Prop :=
  ∀ q : ℕ, ∀ hq : 0<q, (q : ℝ)<Real.sqrt p →
    letI : NeZero q := ⟨hq.ne'⟩
    ∃ Λ : DirichletCharacter ℂ q → ℂ → ℂ,
      (∀ χ, Differentiable ℂ (Λ χ)) ∧ (∀ χ, FiniteOrder (Λ χ)) ∧
      (∀ χ, ∃ c : ℝ, ∀ s : ℂ, c<s.re →
        Λ χ s=completed (p*q^2) k (characterTwisted q f χ) s) ∧
      (∀ χ s, Λ χ s=ε*star (χ (-(p : ZMod q)))*Λ (star χ) (1-s))

theorem continuations_window_iff {p k : ℕ} (hp : p.Prime) (f : ℕ → ℂ) (ε : ℂ) :
    SmallTwistContinuationsBelowSqrt p k f ε ↔ SmallTwistContinuations p k f ε := by
  constructor
  · intro h q hq hQ
    exact h q hq ((small_prime_window hp q).mp hQ)
  · intro h q hq hQ
    exact h q hq ((small_prime_window hp q).mpr hQ)

/-- The prime-level small-conductor linear converse, with the actual cusp
form and original normalized Fourier series. No Euler product is assumed.
The positive-weight restriction is unnecessary for this construction. -/
theorem small_conductor_converse {p k : ℕ} (hp : p.Prime) (hk : Even k)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (h : SmallTwistContinuationsBelowSqrt p k f ε) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) (k : ℤ),
      (F : ℍ → ℂ)=(fun z : ℍ => fourier (fullCoefficients f k) z) ∧
      (F : ℍ → ℂ) ∣[(k : ℤ)] fricke p hp.pos=
        (ε*Complex.I^(-(k : ℤ))) • (F : ℍ → ℂ) := by
  obtain ⟨m,hm⟩ := hk
  have he : k=2*m := by omega
  rw [he] at h ⊢
  have hc := (continuations_window_iff hp f ε).mp h
  refine ⟨smallTwistCuspForm hp hf0 hf ε hε hc,rfl,?_⟩
  have hi : (Complex.I^(2*m))⁻¹=Complex.I^(2*m) := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [one_mul] using fricke_scalar_square m 1 (Or.inl rfl)
  change (fun z : ℍ => fourier (fullCoefficients f (2*m)) z) ∣[((2*m : ℕ) : ℤ)]
      fricke p hp.pos=(ε*Complex.I^(-((2*m : ℕ) : ℤ))) •
        (fun z : ℍ => fourier (fullCoefficients f (2*m)) z)
  rw [_root_.zpow_neg,zpow_natCast,hi]
  exact forward_fricke_of_small_twists hp.pos hf0 hf ε hε hc

#print axioms small_prime_window
#print axioms small_conductor_converse

end QuantitativeArithmeticPrimeSmallTwist
end
end

/-! ## PrimitiveConverse -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex UpperHalfPlane FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction
open scoped ModularForm

/-- Literal multiplicative-twist hypotheses of Corollary 5. Only primitive
characters are assumed; the normalization keeps the critical line at 1/2. -/
def PrimitiveTwistContinuationsBelowSqrt (p k : ℕ) (f : ℕ → ℂ) (ε : ℂ) : Prop :=
  ∀ q : ℕ, ∀ hq : 0<q, (q : ℝ)<Real.sqrt p →
    letI : NeZero q := ⟨hq.ne'⟩
    ∃ Λ : DirichletCharacter ℂ q → ℂ → ℂ,
      (∀ χ, χ.IsPrimitive → Differentiable ℂ (Λ χ)) ∧
      (∀ χ, χ.IsPrimitive → FiniteOrder (Λ χ)) ∧
      (∀ χ, χ.IsPrimitive → ∃ c : ℝ, ∀ s : ℂ, c<s.re →
        Λ χ s=completed (p*q^2) k (multiplicativeTwisted q f χ) s) ∧
      (∀ χ, χ.IsPrimitive → ∀ s : ℂ,
        Λ χ s=(ε*χ (p : ZMod q)*gauss χ^2/(q : ℂ))*Λ (star χ) (1-s))

theorem primitive_to_all_small_twists {p k : ℕ} (hp : p.Prime)
    {f : ℕ → ℂ} (hf : EulerData p f) (ε : ℂ)
    (h : PrimitiveTwistContinuationsBelowSqrt p k f ε) :
    SmallTwistContinuationsBelowSqrt p k f ε := by
  intro q hq hQ
  let : NeZero q := ⟨hq.ne'⟩
  have hqp : q<p := ((small_prime_window hp q).mpr hQ).trans_lt
    (Nat.sqrt_lt_self hp.one_lt)
  have hc : q.Coprime p := (Nat.coprime_of_lt_prime hq.ne' hqp hp).symm
  obtain ⟨A,hA,hFE⟩ := all_character_continuations hf hc ε (by
    intro d hd hd0
    let : NeZero d := ⟨hd0.ne'⟩
    have hdp : (d : ℝ)<Real.sqrt p := lt_of_le_of_lt
      (by exact_mod_cast Nat.le_of_dvd hq hd) hQ
    obtain ⟨Λ,hhol,hord,hagree,hFE⟩ := h d hd0 hdp
    obtain ⟨B,hBh,hBo,hBa,hBFE⟩ := primitive_continuations f ε Λ hhol hord hagree hFE
    exact ⟨B,fun χ hχ => ⟨hBh χ hχ,hBo χ hχ,hBa χ hχ⟩,hBFE⟩)
  exact ⟨A,fun χ => (hA χ).holomorphic,fun χ => (hA χ).finiteOrder,
    fun χ => (hA χ).agrees,hFE⟩

/-- Primitive multiplicative twists below sqrt(p), together with the
original Euler data, give an actual prime-level cusp form. -/
theorem primitive_small_conductor_converse {p k : ℕ} (hp : p.Prime) (hk : Even k)
    {f : ℕ → ℂ} (hf : EulerData p f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (h : PrimitiveTwistContinuationsBelowSqrt p k f ε) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)) (k : ℤ),
      (F : ℍ → ℂ)=(fun z : ℍ => fourier (fullCoefficients f k) z) ∧
      (F : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke p hp.pos=
        (ε*Complex.I^(-(k : ℤ))) • (F : ℍ → ℂ) := by
  obtain ⟨σ,_,hg⟩ := hf.growth
  exact small_conductor_converse hp hk hf.zero hg ε hε
    (primitive_to_all_small_twists hp hf ε h)

#print axioms primitive_to_all_small_twists
#print axioms primitive_small_conductor_converse

end QuantitativeArithmeticPrimeSmallTwist
end
end
