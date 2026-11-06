module

public import AsymptoticClassicalFrickeTraceSwapV1
public import AsymptoticClassicalHeckeCoefficientAlgebraV1
public import AsymptoticClassicalHeckePrimeV1
public import AsymptoticClassicalLocalAtkinTraceV1
public import QuantitativeArithmeticSmallLevelCircFrickeV1
public import QuantitativeArithmeticSmallLevelCircModularTraceV1
public import QuantitativeArithmeticSmallLevelCircTraceDiamondV1
public import QuantitativeArithmeticSmallLevelCircTraceSumV1
public import QuantitativeArithmeticSmallLevelCircTraceTowerCosetsV1
public import QuantitativeArithmeticSmallLevelCircTraceTranslateV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelCirc.ModularHecke. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelCircBadHeckeV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane Matrix AsymptoticClassicalCusp
open AsymptoticCongruenceLabels AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups

/-- The standard trace correspondence in the diag(1,p) direction. -/
def upperTrace (N p : ℕ) [NeZero N] (hp : 0 < p) (k : ℤ) :
    ModularForm (level N) k →ₗ[ℂ] ModularForm (level N) k :=
  (arithmeticTrace (upperDilationLevel N p hp) (level N) k).comp
    (translateLinear (level N) k (upperDilationReal p hp)
      (by rw [upperDilationReal_det]; exact_mod_cast hp))

/-- At a bad prime the genuine trace consists of exactly the p upper branches. -/
theorem upperTrace_bad_slash (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    (k : ℤ) (f : ModularForm (level N) k) :
    (upperTrace N p hp.pos k f : ℍ → ℂ) =
      ∑ a : Fin p, (f : ℍ → ℂ) ∣[k]
        triangularGL 1 a.val p (by norm_num) (by exact_mod_cast hp.pos) := by
  classical
  let : (upperDilationLevel N p hp.pos).IsFiniteRelIndex (level N) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := upperDilationLevel N p hp.pos)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).symm).1
  let := Fintype.ofFinite (level N ⧸ (upperDilationLevel N p hp.pos).subgroupOf (level N))
  let e := upperCosetEquiv N p hp hpN
  change (∑ q : level N ⧸ (upperDilationLevel N p hp.pos).subgroupOf (level N),
    SlashInvariantForm.quotientFunc (ModularForm.translate f (upperDilationReal p hp.pos)) q) = _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  change SlashInvariantForm.quotientFunc (ModularForm.translate f (upperDilationReal p hp.pos))
    (QuotientGroup.mk (upperRepresentative N a.val)) = _
  rw [SlashInvariantForm.quotientFunc_mk]
  change ((f : ℍ → ℂ) ∣[k] upperDilationReal p hp.pos) ∣[k]
    (SpecialLinearGroup.mapGL ℝ (upperSL (-(a.val : ℤ))))⁻¹ = _
  rw [← SlashAction.slash_mul]
  have he : (SpecialLinearGroup.mapGL ℝ (upperSL (-(a.val : ℤ))))⁻¹ =
      SpecialLinearGroup.mapGL ℝ (upperSL a.val) := by
    rw [← map_inv]
    congr 1
    apply Subtype.ext
    change Matrix.adjugate !![1, -(a.val : ℤ); 0, 1] = !![1, (a.val : ℤ); 0, 1]
    simp [Matrix.adjugate_fin_two]
  rw [he, upperDilation_translation]
  rfl

theorem upperTrace_bad_apply (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    (k : ℤ) (f : ModularForm (level N) k) (z : ℍ) :
    upperTrace N p hp.pos k f z = heckeAverage p hp.pos f z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ht : triangularFactor 1 p k = (p : ℂ)⁻¹ := by
    simp only [triangularFactor, one_mul, Complex.ofReal_natCast]
    rw [← zpow_add₀ hpC, show k - 1 + -k = -1 by omega, _root_.zpow_neg_one]
  have hf := congrFun (upperTrace_bad_slash N p hp hpN k f) z
  simp only [Finset.sum_apply, slash_triangular, ht] at hf
  rw [← Finset.mul_sum] at hf
  exact hf

/-- The Fourier law of the actual bad-prime U_p operator. -/
theorem coeff_upperTrace_bad (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    (k : ℤ) (f : ModularForm (level N) k) (n : ℕ) :
    modularCoefficient N k n (upperTrace N p hp.pos k f) = modularCoefficient N k (p * n) f := by
  change (qExpansion 1 (upperTrace N p hp.pos k f)).coeff n = _
  symm
  apply ModularFormClass.qExpansion_coeff_unique
    (f := upperTrace N p hp.pos k f)
    (c := fun n => modularCoefficient N k (p * n) f)
    zero_lt_one (level_one_period N) (m := n)
  intro z
  rw [upperTrace_bad_apply N p hp hpN]
  exact hasSum_heckeAverage p hp.pos f (fun m => modularCoefficient N k m f)
    (fun z => ModularForm.hasSum_qExpansion (f := f) zero_lt_one (level_one_period N) z) z

#print axioms upperTrace
#print axioms upperTrace_bad_slash
#print axioms upperTrace_bad_apply
#print axioms coeff_upperTrace_bad
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircDoubleCosetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane ConjAct AsymptoticClassicalCusp
open scoped ModularForm Pointwise

theorem trace_coe_congr {G J H : Subgroup (GL (Fin 2) ℝ)}
    [G.IsFiniteRelIndex H] [J.IsFiniteRelIndex H] (k : ℤ) (hG : G=J)
    (f : ModularForm G k) (g : ModularForm J k) (he : (f : ℍ → ℂ) = g) :
    (ModularForm.trace H f : ℍ → ℂ) = ModularForm.trace H g := by
  subst J
  have hfg : f=g := DFunLike.coe_injective he
  subst g
  rfl

/-- The actual double-coset correspondence, expressed by the full modular trace. -/
def translateTrace (G : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) (d : GL (Fin 2) ℝ)
    [(toConjAct d⁻¹ • G).IsFiniteRelIndex G] (f : ModularForm G k) : ModularForm G k :=
  ModularForm.trace G (ModularForm.translate f d)

theorem conj_level_of_mem {G : Subgroup (GL (Fin 2) ℝ)} {g : GL (Fin 2) ℝ}
    (hg : g ∈ G) : toConjAct g⁻¹ • G = G :=
  Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer (G.inv_mem hg))

/-- Left multiplication by a level matrix leaves the actual correspondence unchanged. -/
theorem translateTrace_left {G : Subgroup (GL (Fin 2) ℝ)}
    (k : ℤ) (d a : GL (Fin 2) ℝ) (ha : a ∈ G)
    [(toConjAct d⁻¹ • G).IsFiniteRelIndex G]
    [(toConjAct (a*d)⁻¹ • G).IsFiniteRelIndex G] (f : ModularForm G k) :
    translateTrace G k (a*d) f = translateTrace G k d f := by
  have hG : toConjAct (a*d)⁻¹ • G = toConjAct d⁻¹ • G := by
    rw [mul_inv_rev, map_mul, mul_smul, conj_level_of_mem ha]
  apply DFunLike.coe_injective
  apply trace_coe_congr k hG
  change (f : ℍ → ℂ) ∣[k] (a*d) = (f : ℍ → ℂ) ∣[k] d
  have hi : (f : ℍ → ℂ) ∣[k] a = f := f.slash_action_eq' a ha
  rw [SlashAction.slash_mul, hi]

/-- Right multiplication by a level matrix merely permutes the cosets.
This statement concerns full modular forms, not only cusp forms. -/
theorem translateTrace_right {G : Subgroup (GL (Fin 2) ℝ)}
    (k : ℤ) (d a : GL (Fin 2) ℝ) (ha : a ∈ G)
    [(toConjAct d⁻¹ • G).IsFiniteRelIndex G]
    [(toConjAct (d*a)⁻¹ • G).IsFiniteRelIndex G] (f : ModularForm G k) :
    translateTrace G k (d*a) f = translateTrace G k d f := by
  let J := toConjAct d⁻¹ • G
  have hJ : toConjAct a⁻¹ • J = toConjAct (d*a)⁻¹ • G := by
    dsimp [J]
    simp only [mul_inv_rev, mul_smul]
  let : (toConjAct a⁻¹ • J).IsFiniteRelIndex G :=
    hJ.symm ▸ inferInstanceAs ((toConjAct (d*a)⁻¹ • G).IsFiniteRelIndex G)
  let := conjugate_finiteRelIndex J G a
  have hG := conj_level_of_mem ha
  have htr := trace_translate J G a k (ModularForm.translate f d)
  dsimp only at htr
  have htr' := (modularTrace_target_congr
    (ModularForm.translate (ModularForm.translate f d) a) hG).symm.trans htr
  have he := trace_coe_congr (H := G) k hJ (ModularForm.translate (ModularForm.translate f d) a)
    (ModularForm.translate f (d*a)) (by
      change ((f : ℍ → ℂ) ∣[k] d) ∣[k] a = (f : ℍ → ℂ) ∣[k] (d*a)
      rw [SlashAction.slash_mul])
  apply DFunLike.coe_injective
  change (ModularForm.trace G (ModularForm.translate f (d*a)) : ℍ → ℂ) = _
  rw [← he, htr']
  exact (translateTrace G k d f).slash_action_eq' a ha

#print axioms translateTrace_left
#print axioms translateTrace_right
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircLocalAtkinV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane Matrix ConjAct AsymptoticClassicalCusp AsymptoticAtkinLehner
open AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups Pointwise

theorem trace_coe_congr_full {G G' H H' : Subgroup (GL (Fin 2) ℝ)}
    [G.IsFiniteRelIndex H] [G'.IsFiniteRelIndex H'] (k : ℤ) (hG : G = G') (hH : H = H')
    (f : ModularForm G k) (g : ModularForm G' k) (hfg : (f : ℍ → ℂ) = g) :
    (ModularForm.trace H f : ℍ → ℂ) = (ModularForm.trace H' g : ℍ → ℂ) := by
  subst G'
  subst H'
  have he : f = g := DFunLike.coe_injective hfg
  subst g
  rfl

variable (M p : ℕ) (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)

/-- Local Atkin slash on the full modular space. -/
def localAtkinOperator (k : ℤ) :
    ModularForm (level (p * M)) k →ₗ[ℂ] ModularForm (level (p * M)) k := by
  let C : ModularForm (toConjAct (localAtkinReal M p hp A B hAB)⁻¹ • level (p * M)) k →ₗ[ℂ]
      ModularForm (level (p * M)) k := {
    toFun := fun f => ModularForm.mcast rfl f (localAtkinReal_normalizes M p hp A B hAB).symm
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact C.comp (translateLinear (level (p * M)) k (localAtkinReal M p hp A B hAB)
    (by rw [localAtkinReal_det]; exact_mod_cast hp))

@[simp] theorem localAtkinOperator_coe (k : ℤ) (f : ModularForm (level (p * M)) k) :
    (localAtkinOperator M p hp A B hAB k f : ℍ → ℂ) =
      (f : ℍ → ℂ) ∣[k] localAtkinReal M p hp A B hAB := rfl

theorem localAtkinOperator_square (k : ℤ) (f : ModularForm (level (p * M)) k) :
    localAtkinOperator M p hp A B hAB k (localAtkinOperator M p hp A B hAB k f) =
      (p : ℂ) ^ (k - 2) • f := by
  apply DFunLike.coe_injective
  simp only [localAtkinOperator_coe]
  rw [← SlashAction.slash_mul, localAtkinReal_square, scalar_eq_positiveScalarReal p hp,
    SlashAction.slash_mul]
  have hi : (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (localSquare M p A B hAB) = f :=
    f.slash_action_eq' _ ⟨_, localSquare_mem M p A B hAB, rfl⟩
  rw [hi, slash_positiveScalarReal]
  rfl

/-- The conjugate old trace becomes the ordinary trace after local Atkin. -/
theorem localAtkin_trace_zero [NeZero M] (k : ℤ) (f : ModularForm (level (p * M)) k)
    (hf : let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (dilationLevel M p hp) k f = 0) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
    arithmeticTrace (level (p * M)) (level M) k (localAtkinOperator M p hp A B hAB k f) = 0 := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
  dsimp only
  let G := level (p * M)
  let H := dilationLevel M p hp
  let V := localAtkinReal M p hp A B hAB
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  let := conjugate_finiteRelIndex G H V
  let : G.IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  have hzero : (ModularForm.trace H f : ℍ → ℂ) = 0 :=
    congrArg (fun h : ModularForm H k => (h : ℍ → ℂ)) hf
  have ht := trace_translate G H V k f
  rw [hzero, SlashAction.zero_slash] at ht
  dsimp only at ht
  apply DFunLike.coe_injective
  change (ModularForm.trace (level M) (localAtkinOperator M p hp A B hAB k f) : ℍ → ℂ) = 0
  have he := trace_coe_congr_full k (localAtkinReal_normalizes M p hp A B hAB)
    (localAtkinReal_oldGroup_back M p hp A B hAB)
    (ModularForm.translate f V) (localAtkinOperator M p hp A B hAB k f) rfl
  exact he.symm.trans ht

/-- The genuine trace identity relating U_p and local Atkin, including
noncuspidal modular forms. -/
theorem upperTrace_localAtkin [NeZero M] [Fact p.Prime] (hM : 0 < M) (hpM : ¬ p ∣ M)
    (k : ℤ) (f : ModularForm (level (p * M)) k) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
    (upperTrace (p * M) p hp k (localAtkinOperator M p hp A B hAB k f) : ℍ → ℂ) =
      (p : ℂ) ^ (k - 2) • ((arithmeticTrace (level (p * M)) (level M) k f : ℍ → ℂ) - f) := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
  dsimp only
  have ht := modularTrace_prime_sum M p hM hpM A B hAB k f
  change (arithmeticTrace (level (p * M)) (level M) k f : ℍ → ℂ) = _ at ht
  rw [upperTrace_bad_slash (p * M) p (Fact.out : p.Prime) (Nat.dvd_mul_right p M), ht]
  simp only [add_sub_cancel_left]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hb := AsymptoticClassicalCusp.localAtkin_upper_branch M p hp A B hAB (a.val : ℤ)
  simp only [Int.cast_natCast] at hb
  rw [localAtkinOperator_coe, ← SlashAction.slash_mul, hb,
    SlashAction.slash_mul, slash_positiveScalarReal]
  rfl

#print axioms localAtkinOperator_square
#print axioms localAtkin_trace_zero
#print axioms upperTrace_localAtkin
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircBadRepeatedV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane Matrix ConjAct AsymptoticClassicalCusp
open AsymptoticClassicalDiscriminant AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups Pointwise

theorem upperTrace_coset_sum (N M p : ℕ) [NeZero N] [NeZero M] (hp : 0 < p)
    (e : Fin p ≃ level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M))
    (he : ∀ a, e a = QuotientGroup.mk (upperRepresentative M a.val))
    (k : ℤ) (f : ModularForm (level N) k) :
    (arithmeticTrace (upperDilationLevel N p hp) (level M) k
      (ModularForm.translate f (upperDilationReal p hp)) : ℍ → ℂ) =
      ∑ a : Fin p, (f : ℍ → ℂ) ∣[k]
        triangularGL 1 a.val p (by norm_num) (by exact_mod_cast hp) := by
  classical
  let : (upperDilationLevel N p hp).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := upperDilationLevel N p hp)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let := Fintype.ofFinite (level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M))
  change (∑ q : level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M),
    SlashInvariantForm.quotientFunc (ModularForm.translate f (upperDilationReal p hp)) q) = _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [he a]
  change SlashInvariantForm.quotientFunc (ModularForm.translate f (upperDilationReal p hp))
    (QuotientGroup.mk (upperRepresentative M a.val)) = _
  rw [SlashInvariantForm.quotientFunc_mk]
  change ((f : ℍ → ℂ) ∣[k] upperDilationReal p hp) ∣[k]
    (SpecialLinearGroup.mapGL ℝ (upperSL (-(a.val : ℤ))))⁻¹ = _
  rw [← SlashAction.slash_mul]
  have hmat : (SpecialLinearGroup.mapGL ℝ (upperSL (-(a.val : ℤ))))⁻¹ =
      SpecialLinearGroup.mapGL ℝ (upperSL a.val) := by
    rw [← map_inv]
    congr 1
    apply Subtype.ext
    change Matrix.adjugate !![1, -(a.val : ℤ); 0, 1] = !![1, (a.val : ℤ); 0, 1]
    simp [Matrix.adjugate_fin_two]
  rw [hmat, upperDilation_translation]
  rfl

theorem upperTrace_repeated_lower (M p : ℕ) [NeZero M] (hp : p.Prime) (hpM : p ∣ M)
    (k : ℤ) (f : ModularForm (level (p * M)) k) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
    (upperTrace (p * M) p hp.pos k f : ℍ → ℂ) =
      (arithmeticTrace (upperDilationLevel (p * M) p hp.pos) (level M) k
        (ModularForm.translate f (upperDilationReal p hp.pos)) : ℍ → ℂ) := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
  dsimp only
  rw [upperTrace_bad_slash (p * M) p hp (Nat.dvd_mul_right p M),
    upperTrace_coset_sum (p * M) M p hp.pos (upperLowerCosetEquiv M p hp hpM)
      (upperLowerCosetEquiv_mk M p hp hpM)]

/-- At every square divisor the conjugate trace kernel forces U_p=0,
without any assumption of cuspidality. -/
theorem upperTrace_repeated_zero_of_trace (M p : ℕ) [NeZero M] (hp : p.Prime)
    (hpM : p ∣ M) (k : ℤ) (f : ModularForm (level (p * M)) k)
    (hf : let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (dilationLevel M p hp.pos) k f = 0) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p hp.pos k f = 0 := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
  dsimp only
  let G := level (p * M)
  let H := dilationLevel M p hp.pos
  let g := upperDilationReal p hp.pos
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  let := conjugate_finiteRelIndex G H g
  let : (upperDilationLevel (p * M) p hp.pos).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := upperDilationLevel (p * M) p hp.pos)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let : (toConjAct g⁻¹ • G).IsFiniteRelIndex (level M) :=
    inferInstanceAs ((upperDilationLevel (p * M) p hp.pos).IsFiniteRelIndex (level M))
  have hzero : (ModularForm.trace H f : ℍ → ℂ) = 0 :=
    congrArg (fun h : ModularForm H k => (h : ℍ → ℂ)) hf
  have ht := trace_translate G H g k f
  rw [hzero, SlashAction.zero_slash] at ht
  dsimp only at ht
  apply DFunLike.coe_injective
  rw [upperTrace_repeated_lower M p hp hpM k f]
  change (ModularForm.trace (level M) (ModularForm.translate f g) : ℍ → ℂ) = 0
  have he := trace_coe_congr_full k rfl (upper_translate_dilationLevel M p hp.pos)
    (ModularForm.translate f g) (ModularForm.translate f g) rfl
  exact he.symm.trans ht

#print axioms upperTrace_repeated_lower
#print axioms upperTrace_repeated_zero_of_trace
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircBadSimpleV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane AsymptoticClassicalCusp
open scoped ModularForm

variable (M p : ℕ) [NeZero M] [Fact p.Prime] (hM : 0 < M) (hpM : ¬ p ∣ M)
variable (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)

include hM hpM in
theorem upperTrace_simple_eq_neg_local (k : ℤ) (f : ModularForm (level (p * M)) k)
    (hf : let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (dilationLevel M p (Fact.out : p.Prime).pos) k f = 0) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p (Fact.out : p.Prime).pos k f =
      -localAtkinOperator M p (Fact.out : p.Prime).pos A B hAB k f := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
  dsimp only
  let hp := (Fact.out : p.Prime).pos
  have hc : (p : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.ne')
  have ht := localAtkin_trace_zero M p hp A B hAB k f hf
  have hh := upperTrace_localAtkin M p hp A B hAB hM hpM k
    (localAtkinOperator M p hp A B hAB k f)
  dsimp only at ht hh
  rw [localAtkinOperator_square, map_smul, ht] at hh
  ext z
  apply mul_left_cancel₀ hc
  have hz := congrFun hh z
  simpa only [FunLike.coe_smul, FunLike.coe_zero, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Pi.zero_apply, zero_sub, Pi.neg_apply, neg_apply] using hz

include hM hpM hAB in
/-- Exact ramified quadratic relation on the full two-trace kernel. -/
theorem upperTrace_simple_square_of_traces (k : ℤ) (f : ModularForm (level (p * M)) k)
    (hfirst : let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (level M) k f = 0)
    (hsecond : let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (dilationLevel M p (Fact.out : p.Prime).pos) k f = 0) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p (Fact.out : p.Prime).pos k
      (upperTrace (p * M) p (Fact.out : p.Prime).pos k f) = (p : ℂ) ^ (k - 2) • f := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
  dsimp only
  rw [upperTrace_simple_eq_neg_local M p hM hpM A B hAB k f hsecond, map_neg]
  have hh := upperTrace_localAtkin M p (Fact.out : p.Prime).pos A B hAB hM hpM k f
  dsimp only at hh
  rw [hfirst] at hh
  ext z
  have hz := congrFun hh z
  simp only [FunLike.coe_zero, Pi.smul_apply, smul_eq_mul, zero_sub, Pi.neg_apply] at hz
  change -(upperTrace (p * M) p (Fact.out : p.Prime).pos k
    (localAtkinOperator M p (Fact.out : p.Prime).pos A B hAB k f) z) =
      (p : ℂ) ^ (k - 2) * f z
  rw [hz]
  ring

#print axioms upperTrace_simple_eq_neg_local
#print axioms upperTrace_simple_square_of_traces
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircTraceTowerV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane
open scoped ModularForm

theorem quotientFunc_out {G H : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : ModularForm G k) (q : H ⧸ G.subgroupOf H) :
    SlashInvariantForm.quotientFunc f q = (f : ℍ → ℂ) ∣[k] q.out.val⁻¹ := by
  calc
    _ = SlashInvariantForm.quotientFunc f (QuotientGroup.mk q.out) :=
      congrArg (SlashInvariantForm.quotientFunc f) (Quotient.out_eq q).symm
    _ = _ := SlashInvariantForm.quotientFunc_mk _ _

/-- Transitivity of the literal modular trace along a subgroup tower. -/
theorem trace_tower {G H K : Subgroup (GL (Fin 2) ℝ)}
    [G.IsFiniteRelIndex H] [H.IsFiniteRelIndex K] [G.IsFiniteRelIndex K]
    (hGH : G ≤ H) (hHK : H ≤ K) (k : ℤ) (f : ModularForm G k) :
    ModularForm.trace K (ModularForm.trace H f) = ModularForm.trace K f := by
  classical
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  let := Fintype.ofFinite (K ⧸ H.subgroupOf K)
  let := Fintype.ofFinite (K ⧸ G.subgroupOf K)
  let e := TraceTower.equiv G H K hGH hHK
  have he (a : K ⧸ H.subgroupOf K) :
      SlashInvariantForm.quotientFunc (ModularForm.trace H f) a =
        ∑ b : H ⧸ G.subgroupOf H, SlashInvariantForm.quotientFunc f (e (a,b)) := by
    rw [quotientFunc_out, ModularForm.coe_trace, SlashAction.sum_slash]
    apply Finset.sum_congr rfl
    intro b _
    rw [quotientFunc_out]
    change _ = SlashInvariantForm.quotientFunc f
      (QuotientGroup.mk (TraceTower.representative G H K hHK (a,b)))
    rw [SlashInvariantForm.quotientFunc_mk, ← SlashAction.slash_mul]
    rfl
  apply DFunLike.coe_injective
  rw [ModularForm.coe_trace, ModularForm.coe_trace]
  simp_rw [he]
  rw [← Fintype.sum_prod_type (fun x => SlashInvariantForm.quotientFunc f (e x))]
  exact e.sum_comp (SlashInvariantForm.quotientFunc f)

theorem arithmeticTrace_tower {G H K : Subgroup (GL (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] [K.HasDetOne]
    [G.IsArithmetic] [H.IsArithmetic] [K.IsArithmetic]
    (hGH : G ≤ H) (hHK : H ≤ K) (k : ℤ) (f : ModularForm G k) :
    arithmeticTrace H K k (arithmeticTrace G H k f) = arithmeticTrace G K k f := by
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  let : H.IsFiniteRelIndex K :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := K)).symm).1
  let : G.IsFiniteRelIndex K :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := K)).symm).1
  exact trace_tower hGH hHK k f

#print axioms trace_tower
#print axioms arithmeticTrace_tower
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircDegeneracyTraceV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane AsymptoticClassicalCusp ConjAct
open scoped ModularForm Pointwise

/-- A degeneracy map at p commutes with removing a coprime prime q.
This is an identity of genuine modular forms, with no cusp condition. -/
theorem degeneracy_cross_trace (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0<M) (hp : 0<p) (hq : q.Prime) (hc : p.Coprime q) (k : ℤ)
    (f : ModularForm (level (q*M)) k) :
    arithmeticTrace (level (p*(q*M))) (level (p*M)) k
      (degeneracy (q*M) p hp k f) =
    degeneracy M p hp k (arithmeticTrace (level (q*M)) (level M) k f) := by
  let : NeZero (q*M) := ⟨(Nat.mul_pos hq.pos hM).ne'⟩
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp hM).ne'⟩
  let : NeZero (p*(q*M)) := ⟨(Nat.mul_pos hp (Nat.mul_pos hq.pos hM)).ne'⟩
  let : (toConjAct (dilationReal p hp)⁻¹ • level (q*M)).IsArithmetic :=
    inferInstanceAs (dilationLevel (q*M) p hp).IsArithmetic
  let : (toConjAct (dilationReal p hp)⁻¹ • level M).IsArithmetic :=
    inferInstanceAs (dilationLevel M p hp).IsArithmetic
  let : (level (q*M)).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (q*M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let : (toConjAct (dilationReal p hp)⁻¹ • level (q*M)).IsFiniteRelIndex
      (dilationLevel M p hp) :=
    ((Subgroup.IsArithmetic.is_commensurable
      (𝒢 := toConjAct (dilationReal p hp)⁻¹ • level (q*M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := dilationLevel M p hp)).symm).1
  have hmeet : dilationLevel (q*M) p hp ⊓ level (p*M) = level (p*(q*M)) := by
    rw [inf_comm, mixed_level_inf]
    congr 1
    ring
  have hindex : (level (p*(q*M))).relIndex (level (p*M)) =
      (dilationLevel (q*M) p hp).relIndex (dilationLevel M p hp) := by
    rw [dilationLevel_relIndex]
    exact coprime_level_index M p q hM hp hq hc
  change arithmeticTrace _ _ k
      ((p : ℂ)^(1-k) • restrictModular k (level_le_dilation_conjugate (q*M) p hp)
        (ModularForm.translate f (dilationReal p hp))) =
    (p : ℂ)^(1-k) • restrictModular k (level_le_dilation_conjugate M p hp)
      (ModularForm.translate (arithmeticTrace (level (q*M)) (level M) k f) (dilationReal p hp))
  rw [map_smul, arithmeticTrace_restrict_diamond k
    (level_le_dilation_conjugate (q*M) p hp)
    (level_le_dilation_conjugate M p hp) hmeet hindex
    (ModularForm.translate f (dilationReal p hp))]
  congr 1
  apply DFunLike.coe_injective
  change (ModularForm.trace (dilationLevel M p hp)
      (ModularForm.translate f (dilationReal p hp)) : ℍ → ℂ) =
    ((ModularForm.trace (level M) f : ℍ → ℂ) ∣[k] dilationReal p hp)
  exact trace_translate (level (q*M)) (level M) (dilationReal p hp) k f

/-- Good-prime Hecke commutes with the ordinary level-lowering trace.
The two compositions are the same trace through the common level p*q*M. -/
theorem dilationTrace_cross_trace (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0<M) (hp : 0<p) (hq : q.Prime) (hc : p.Coprime q) (k : ℤ)
    (f : ModularForm (level (q*M)) k) :
    arithmeticTrace (level (q*M)) (level M) k (dilationTrace (q*M) p hp k f) =
      dilationTrace M p hp k (arithmeticTrace (level (q*M)) (level M) k f) := by
  let : NeZero (q*M) := ⟨(Nat.mul_pos hq.pos hM).ne'⟩
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp hM).ne'⟩
  let : NeZero (p*(q*M)) := ⟨(Nat.mul_pos hp (Nat.mul_pos hq.pos hM)).ne'⟩
  change arithmeticTrace _ _ k ((p : ℂ)^(k-1) •
      arithmeticTrace (level (p*(q*M))) (level (q*M)) k (degeneracy (q*M) p hp k f)) =
    (p : ℂ)^(k-1) • arithmeticTrace (level (p*M)) (level M) k
      (degeneracy M p hp k (arithmeticTrace (level (q*M)) (level M) k f))
  rw [map_smul, ← degeneracy_cross_trace M p q hM hp hq hc k f]
  congr 1
  rw [arithmeticTrace_tower
      (level_antitone (Nat.dvd_mul_left (q*M) p))
      (level_antitone (Nat.dvd_mul_left M q)),
    arithmeticTrace_tower
      (level_antitone (Nat.mul_dvd_mul_left p (Nat.dvd_mul_left M q)))
      (level_antitone (Nat.dvd_mul_left M p))]

#print axioms degeneracy_cross_trace
#print axioms dilationTrace_cross_trace
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircHeckeCovarianceV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane ConjAct AsymptoticClassicalCusp
open scoped ModularForm Pointwise

/-- A normalizer conjugates the actual double-coset correspondence.
This is a full modular trace identity, independent of any inner product. -/
theorem translateTrace_intertwine {G : Subgroup (GL (Fin 2) ℝ)}
    (k : ℤ) (w d e : GL (Fin 2) ℝ)
    (hw : toConjAct w⁻¹ • G = G) (hde : w*d=e*w)
    [(toConjAct d⁻¹ • G).IsFiniteRelIndex G]
    [(toConjAct e⁻¹ • G).IsFiniteRelIndex G]
    (f g : ModularForm G k) (hg : (g : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] w) :
    (translateTrace G k d g : ℍ → ℂ) =
      (translateTrace G k e f : ℍ → ℂ) ∣[k] w := by
  let J := toConjAct e⁻¹ • G
  have hJ : toConjAct w⁻¹ • J = toConjAct d⁻¹ • G := by
    dsimp [J]
    rw [← mul_smul]
    change toConjAct (w⁻¹*e⁻¹) • G = _
    have hi : w⁻¹*e⁻¹=d⁻¹*w⁻¹ := by
      simpa only [mul_inv_rev] using (congrArg Inv.inv hde).symm
    rw [hi]
    change (toConjAct d⁻¹ * toConjAct w⁻¹) • G = _
    rw [mul_smul, hw]
    rfl
  let : (toConjAct w⁻¹ • J).IsFiniteRelIndex G :=
    hJ.symm ▸ inferInstanceAs ((toConjAct d⁻¹ • G).IsFiniteRelIndex G)
  let := conjugate_finiteRelIndex J G w
  have htr := trace_translate J G w k (ModularForm.translate f e)
  dsimp only at htr
  have htr' := (modularTrace_target_congr
    (ModularForm.translate (ModularForm.translate f e) w) hw).symm.trans htr
  have he := trace_coe_congr (H := G) k hJ (ModularForm.translate (ModularForm.translate f e) w)
    (ModularForm.translate g d) (by
      change ((f : ℍ → ℂ) ∣[k] e) ∣[k] w = (g : ℍ → ℂ) ∣[k] d
      rw [hg, ← SlashAction.slash_mul, ← SlashAction.slash_mul, hde])
  exact he.symm.trans htr'

#print axioms translateTrace_intertwine
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircGoodHeckeV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane Matrix AsymptoticClassicalCusp AsymptoticAtkinLehner
open AsymptoticClassicalDiscriminant
open scoped ModularForm MatrixGroups

@[simp] theorem modularCoefficient_apply (N : ℕ) (k : ℤ) (n : ℕ)
    (f : ModularForm (level N) k) :
    modularCoefficient N k n f = (qExpansion 1 f).coeff n := rfl

/-- Explicit good-prime trace on the full modular space. -/
theorem arithmeticTrace_prime_sum (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬ p∣N) (A B : ℤ)
    (hAB : (p : ℤ)*A+(N : ℤ)*B=1) (k : ℤ)
    (f : ModularForm (level (p*N)) k) :
    (by
      let : NeZero (p*N) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne N)⟩
      exact (arithmeticTrace (level (p*N)) (level N) k f : ℍ → ℂ)) =
      f + ∑ a : Fin p, (f : ℍ → ℂ) ∣[k] traceSL N p A B hAB a.val :=
  modularTrace_prime_sum N p hN hpN A B hAB k f

/-- The Fourier series of an actual degeneracy form is obtained by replacing
 the formal parameter by its p-th power. -/
theorem qExpansion_degeneracy (N p : ℕ) [NeZero N] (hp : 0 < p) (k : ℤ)
    (f : ModularForm (level N) k) :
    qExpansion 1 (degeneracy N p hp k f) =
      PowerSeries.expand p hp.ne' (qExpansion 1 f) := by
  classical
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  ext n
  symm
  apply ModularFormClass.qExpansion_coeff_unique (f := degeneracy N p hp k f)
    (c := fun m => (PowerSeries.expand p hp.ne' (qExpansion 1 f)).coeff m)
    zero_lt_one (level_one_period (p * N)) (m := n)
  intro z
  have hi : Function.Injective (fun n : ℕ => p * n) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h
  apply (hi.hasSum_iff (fun n hn => ?_)).mp
  · change HasSum (fun n : ℕ =>
      (PowerSeries.expand p hp.ne' (qExpansion 1 f)).coeff (p * n) •
        Function.Periodic.qParam 1 z ^ (p * n)) _
    simp only [PowerSeries.coeff_expand_mul, pow_mul, ← qParam_dilation p hp z,
      degeneracy_apply]
    simpa only [smul_eq_mul] using ModularForm.hasSum_qExpansion
      (f := f) zero_lt_one (level_one_period N) (dilationReal p hp • z)
  · have hnd : ¬ p ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [PowerSeries.coeff_expand_of_not_dvd p hp.ne' _ hnd]

/-- Exact coefficient transport along the classical degeneracy map. -/
theorem coeff_degeneracy (N p : ℕ) [NeZero N] (hp : 0 < p) (k : ℤ)
    (f : ModularForm (level N) k) (n : ℕ) :
    (qExpansion 1 (degeneracy N p hp k f)).coeff n =
      if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0 := by
  rw [qExpansion_degeneracy, PowerSeries.coeff_expand]

/-- Scalar normalization converts literal dilation to Mathlib's slash translate. -/
theorem scaled_degeneracy_coe (N p : ℕ) (hp : 0 < p) (k : ℤ)
    (f : ModularForm (level N) k) :
    (p : ℂ) ^ (k - 1) • (degeneracy N p hp k f : ℍ → ℂ) =
      (f : ℍ → ℂ) ∣[k] dilationReal p hp := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  change (p : ℂ) ^ (k - 1) • ((p : ℂ) ^ (1 - k) •
    ((f : ℍ → ℂ) ∣[k] dilationReal p hp)) = _
  rw [smul_smul, ← zpow_add₀ hpC]
  simp

/-- The classical good-prime operator expressed by its p+1 upper-triangular
 representatives. This follows from the concrete trace, not a prescribed action. -/
theorem dilationTrace_prime_slash (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (k : ℤ)
    (f : ModularForm (level N) k) :
    (dilationTrace N p (Fact.out : p.Prime).pos k f : ℍ → ℂ) =
      (f : ℍ → ℂ) ∣[k] dilationReal p (Fact.out : p.Prime).pos +
        ∑ a : Fin p, (f : ℍ → ℂ) ∣[k]
          triangularGL 1 a.val p (by norm_num) (by exact_mod_cast (Fact.out : p.Prime).pos) := by
  let hp := (Fact.out : p.Prime).pos
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  change (p : ℂ) ^ (k - 1) •
    (arithmeticTrace (level (p * N)) (level N) k (degeneracy N p hp k f) : ℍ → ℂ) = _
  rw [arithmeticTrace_prime_sum N p hN hpN A B hAB k, smul_add, Finset.smul_sum,
    scaled_degeneracy_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← ModularForm.SL_smul_slash, scaled_degeneracy_coe, ModularForm.SL_slash,
    ← SlashAction.slash_mul]
  change (f : ℍ → ℂ) ∣[k] (dilationReal p hp *
    SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB a.val)) = _
  rw [dilation_traceSL, SlashAction.slash_mul]
  have hinv : (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB) =
      (f : ℍ → ℂ) := f.slash_action_eq' _ ⟨_, heckeSL_mem N p A B hAB, rfl⟩
  rw [hinv]
  simp only [Int.cast_natCast]

/-- The pointwise classical T_p formula, derived from the trace correspondence. -/
theorem dilationTrace_prime_apply (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (k : ℤ)
    (f : ModularForm (level N) k) (z : ℍ) :
    dilationTrace N p (Fact.out : p.Prime).pos k f z =
      (p : ℂ) ^ (k - 1) * f (dilationReal p (Fact.out : p.Prime).pos • z) +
        heckeAverage p (Fact.out : p.Prime).pos f z := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ht : triangularFactor 1 p k = (p : ℂ)⁻¹ := by
    simp only [triangularFactor, one_mul, Complex.ofReal_natCast]
    rw [← zpow_add₀ hpC, show k - 1 + -k = -1 by omega, _root_.zpow_neg_one]
  have hf := congrFun (dilationTrace_prime_slash N p hN hpN A B hAB k f) z
  rw [← scaled_degeneracy_coe N p (Fact.out : p.Prime).pos k f] at hf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, degeneracy_apply,
    Finset.sum_apply, slash_triangular, ht] at hf
  rw [← Finset.mul_sum] at hf
  exact hf

/-- The exact good-prime Fourier-coefficient law for the concrete operator. -/
theorem coeff_dilationTrace (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (k : ℤ)
    (f : ModularForm (level N) k) (n : ℕ) :
    modularCoefficient N k n (dilationTrace N p (Fact.out : p.Prime).pos k f) =
      modularCoefficient N k (p * n) f + (p : ℂ) ^ (k - 1) *
        if p ∣ n then modularCoefficient N k (n / p) f else 0 := by
  let hp := (Fact.out : p.Prime).pos
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  change (qExpansion 1 (dilationTrace N p hp k f)).coeff n = _
  symm
  apply ModularFormClass.qExpansion_coeff_unique
    (f := dilationTrace N p hp k f)
    (c := fun n => modularCoefficient N k (p * n) f + (p : ℂ) ^ (k - 1) *
      if p ∣ n then modularCoefficient N k (n / p) f else 0)
    zero_lt_one (level_one_period N) (m := n)
  intro z
  rw [dilationTrace_prime_apply N p hN hpN A B hAB k f z, add_comm]
  have ha := hasSum_heckeAverage p hp f (fun m => modularCoefficient N k m f)
    (fun z => ModularForm.hasSum_qExpansion (f := f) zero_lt_one (level_one_period N) z) z
  have hd := ModularForm.hasSum_qExpansion (f := degeneracy N p hp k f)
    zero_lt_one (level_one_period (p * N)) z
  simp_rw [coeff_degeneracy, degeneracy_apply] at hd
  apply (ha.add (hd.mul_left ((p : ℂ) ^ (k - 1)))).congr_fun
  intro m
  simp only [modularCoefficient_apply, smul_eq_mul]
  ring

/-- The coefficient law is independent of auxiliary Bezout choices. -/
theorem coeff_dilationTrace_prime (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hpN : ¬ p ∣ N) (k : ℤ) (f : ModularForm (level N) k) (n : ℕ) :
    modularCoefficient N k n (dilationTrace N p (Fact.out : p.Prime).pos k f) =
      modularCoefficient N k (p * n) f + (p : ℂ) ^ (k - 1) *
        if p ∣ n then modularCoefficient N k (n / p) f else 0 := by
  have hc : p.Coprime N := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN
  have hAB : (p : ℤ) * Nat.gcdA p N + (N : ℤ) * Nat.gcdB p N = 1 := by
    have hh := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one, Nat.cast_one] at hh
    exact hh.symm
  exact coeff_dilationTrace N p (Nat.pos_of_ne_zero (NeZero.ne N)) hpN
    (Nat.gcdA p N) (Nat.gcdB p N) hAB k f n

/-- The first coefficient of T_p f is the p-th coefficient of f. -/
theorem first_dilationTrace_prime (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hpN : ¬ p ∣ N) (k : ℤ) (f : ModularForm (level N) k) :
    modularCoefficient N k 1 (dilationTrace N p (Fact.out : p.Prime).pos k f) =
      modularCoefficient N k p f := by
  rw [coeff_dilationTrace_prime N p hpN]
  simp [(Fact.out : p.Prime).not_dvd_one]

#print axioms qExpansion_degeneracy
#print axioms dilationTrace_prime_slash
#print axioms coeff_dilationTrace_prime
#print axioms first_dilationTrace_prime
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircHeckeDoubleCosetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane AsymptoticClassicalCusp ConjAct Matrix
open AsymptoticClassicalDiscriminant AsymptoticCongruenceLabels AsymptoticAtkinLehner
open scoped ModularForm Pointwise MatrixGroups

instance dilation_relative (N p : ℕ) [NeZero N] (hp : 0<p) :
    (toConjAct (dilationReal p hp)⁻¹ • level N).IsFiniteRelIndex (level N) := by
  let : (toConjAct (dilationReal p hp)⁻¹ • level N).IsArithmetic :=
    inferInstanceAs (dilationLevel N p hp).IsArithmetic
  exact ((Subgroup.IsArithmetic.is_commensurable
    (𝒢 := toConjAct (dilationReal p hp)⁻¹ • level N)).trans
    (Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).symm).1

instance upperDilation_relative (N p : ℕ) [NeZero N] (hp : 0<p) :
    (toConjAct (upperDilationReal p hp)⁻¹ • level N).IsFiniteRelIndex (level N) := by
  let : (toConjAct (upperDilationReal p hp)⁻¹ • level N).IsArithmetic :=
    inferInstanceAs (upperDilationLevel N p hp).IsArithmetic
  exact ((Subgroup.IsArithmetic.is_commensurable
    (𝒢 := toConjAct (upperDilationReal p hp)⁻¹ • level N)).trans
    (Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).symm).1

/-- The concrete trace/degeneracy definition is the actual double-coset correspondence. -/
theorem dilationTrace_eq_translateTrace (N p : ℕ) [NeZero N] (hp : 0<p) (k : ℤ)
    (f : ModularForm (level N) k) :
    dilationTrace N p hp k f = translateTrace (level N) k (dilationReal p hp) f := by
  let : NeZero (p*N) := ⟨(Nat.mul_ne_zero hp.ne' (NeZero.ne N))⟩
  let : (toConjAct (dilationReal p hp)⁻¹ • level N).IsArithmetic :=
    inferInstanceAs (dilationLevel N p hp).IsArithmetic
  have hmeet : dilationLevel N p hp ⊓ level N = level (p*N) := by
    rw [inf_comm, level_inf_dilationLevel, Nat.lcm_eq_right (Nat.dvd_mul_left N p)]
  have hindex : (level (p*N)).relIndex (level N) =
      (dilationLevel N p hp).relIndex (level N) := by
    rw [← hmeet, Subgroup.inf_relIndex_right]
  have hscaled : (p : ℂ)^(k-1) • degeneracy N p hp k f =
      restrictModular k (level_le_dilation_conjugate N p hp)
        (ModularForm.translate f (dilationReal p hp)) := by
    apply DFunLike.coe_injective
    exact scaled_degeneracy_coe N p hp k f
  change (p : ℂ)^(k-1) • arithmeticTrace (level (p*N)) (level N) k
    (degeneracy N p hp k f) = _
  rw [← map_smul, hscaled, arithmeticTrace_restrict_diamond k
    (level_le_dilation_conjugate N p hp) (le_refl (level N)) hmeet hindex
    (ModularForm.translate f (dilationReal p hp))]
  rfl

/-- The upper and lower good-prime matrices belong to the same actual level double coset. -/
theorem upper_eq_dilationTrace (N p : ℕ) [NeZero N] (hp : 0<p)
    (A B : ℤ) (hAB : (p : ℤ)*A+(N : ℤ)*B=1) (k : ℤ)
    (f : ModularForm (level N) k) :
    translateTrace (level N) k (upperDilationReal p hp) f = dilationTrace N p hp k f := by
  let D := dilationReal p hp
  let J := upperDilationReal p hp
  let U := SpecialLinearGroup.mapGL ℝ (heckeSL N p A B hAB)
  let V := SpecialLinearGroup.mapGL ℝ (traceSL N p A B hAB 0)
  have hU : U ∈ level N := ⟨_,heckeSL_mem N p A B hAB,rfl⟩
  have hV : V ∈ level N := ⟨_,traceSL_mem N p A B hAB 0,rfl⟩
  have hmat : D*V=U*J := by
    simpa only [D,U,J,V,upperDilationReal_eq,Int.cast_zero] using
      dilation_traceSL N p hp A B hAB 0
  have hg : toConjAct (D*V)⁻¹ • level N = toConjAct V⁻¹ • (toConjAct D⁻¹ • level N) := by
    rw [_root_.mul_inv_rev]
    change (toConjAct V⁻¹ * toConjAct D⁻¹) • level N = _
    exact mul_smul _ _ _
  let : (toConjAct V⁻¹ • (toConjAct D⁻¹ • level N)).IsFiniteRelIndex (level N) := by
    have h := conjugate_finiteRelIndex (toConjAct D⁻¹ • level N) (level N) V
    rwa [conj_level_of_mem hV] at h
  let : (toConjAct (D*V)⁻¹ • level N).IsFiniteRelIndex (level N) := hg.symm ▸ inferInstance
  let : (toConjAct (U*J)⁻¹ • level N).IsFiniteRelIndex (level N) := hmat ▸ inferInstance
  have hr := translateTrace_right k D V hV f
  have hl := translateTrace_left k J U hU f
  have hm : translateTrace (level N) k (D*V) f = translateTrace (level N) k (U*J) f := by
    apply DFunLike.coe_injective
    apply trace_coe_congr k (congrArg (fun d : GL (Fin 2) ℝ => toConjAct d⁻¹ • level N) hmat)
    change (f : ℍ → ℂ) ∣[k] (D*V) = (f : ℍ → ℂ) ∣[k] (U*J)
    rw [hmat]
  rw [dilationTrace_eq_translateTrace]
  exact hl.symm.trans (hm.symm.trans hr)

#print axioms dilationTrace_eq_translateTrace
#print axioms upper_eq_dilationTrace
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircModularFrickeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane Matrix ConjAct AsymptoticClassicalCusp AsymptoticClassicalLSeries
open AsymptoticCongruenceLabels
open scoped ModularForm Pointwise

/-- Normalized Fricke on the entire modular space, including Eisenstein forms. -/
def frickeOperator (N : ℕ) (hN : 0<N) (k : ℤ) :
    ModularForm (level N) k →ₗ[ℂ] ModularForm (level N) k := by
  let C : ModularForm (toConjAct (frickeReal N hN)⁻¹ • level N) k →ₗ[ℂ]
      ModularForm (level N) k := {
    toFun := fun f => ModularForm.mcast rfl f (fricke_inverse_normalizes N hN).symm
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact (N : ℂ)^(1-(k : ℂ)/2) • C.comp
    (translateLinear (level N) k (frickeReal N hN)
      (by rw [frickeReal_det]; exact_mod_cast hN))

theorem frickeOperator_coe (N : ℕ) (hN : 0<N) (k : ℤ)
    (f : ModularForm (level N) k) :
    (frickeOperator N hN k f : ℍ → ℂ) =
      (f : ℍ → ℂ) ∣[k] SmallLevelNormalized.fricke N hN := by
  rw [← ModularLSeries.normalizedFricke_eq_detOne_slash, normalizedFricke_eq_slash]
  rfl

theorem fricke_dilation_upper (N p : ℕ) (hN : 0<N) (hp : 0<p) :
    frickeReal N hN * dilationReal p hp = upperDilationReal p hp * frickeReal N hN := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeReal, fricke, AsymptoticReconstructionBranch.branch,
      dilationReal, dilationGL, upperDilationReal, upperDilationGL,
      GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Good-prime Hecke commutes with normalized Fricke on all modular forms.
The proof uses literal coset trace covariance and equality of double cosets;
there is no Petersson or cuspidality hypothesis. -/
theorem dilationTrace_fricke_commute (N p : ℕ) [NeZero N]
    (hN : 0<N) (hp : 0<p) (A B : ℤ) (hAB : (p : ℤ)*A+(N : ℤ)*B=1) (k : ℤ) :
    Function.Commute (dilationTrace N p hp k) (frickeOperator N hN k) := by
  intro f
  let g : ModularForm (level N) k := ModularForm.mcast rfl
    (ModularForm.translate f (frickeReal N hN)) (fricke_inverse_normalizes N hN).symm
  have hg : (g : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] frickeReal N hN := rfl
  have he := translateTrace_intertwine k (frickeReal N hN) (dilationReal p hp)
    (upperDilationReal p hp) (fricke_inverse_normalizes N hN)
    (fricke_dilation_upper N p hN hp) f g hg
  rw [upper_eq_dilationTrace N p hp A B hAB k,
    ← dilationTrace_eq_translateTrace N p hp k] at he
  have hf : frickeOperator N hN k f = (N : ℂ)^(1-(k : ℂ)/2) • g := rfl
  rw [hf, map_smul]
  apply DFunLike.coe_injective
  change (N : ℂ)^(1-(k : ℂ)/2) • (dilationTrace N p hp k g : ℍ → ℂ) =
    (N : ℂ)^(1-(k : ℂ)/2) •
      ((dilationTrace N p hp k f : ℍ → ℂ) ∣[k] frickeReal N hN)
  rw [he]

#print axioms frickeOperator_coe
#print axioms fricke_dilation_upper
#print axioms dilationTrace_fricke_commute
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircFrickeTraceV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane Matrix AsymptoticClassicalCusp AsymptoticClassicalCosets
open scoped ModularForm MatrixGroups

theorem fricke_quotient_swap (N M : ℕ) (hN : 0 < N) (k : ℤ)
    (f : ModularForm (level N) k)
    (q : CongruenceSubgroup.Gamma0 M ⧸
      (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M)) :
    SlashInvariantForm.quotientFunc (frickeOperator N hN k f) (matrixEquiv N M q) =
      (N : ℂ)^(1-(k : ℂ)/2) •
        ((SlashInvariantForm.quotientFunc f (frickeMatrixEquiv N M hN q)) ∣[k] frickeReal N hN) := by
  induction q using Quotient.inductionOn with
  | h a =>
    have hm : matrixEquiv N M (QuotientGroup.mk a) =
        QuotientGroup.mk ((SpecialLinearGroup.mapGL ℝ).subgroupMap _ a) := rfl
    have hf : frickeMatrixEquiv N M hN (QuotientGroup.mk a) =
        QuotientGroup.mk (frickeMatrixRepresentative N M hN a) := imageEquivOfEq_mk ..
    rw [hm, hf, SlashInvariantForm.quotientFunc_mk, SlashInvariantForm.quotientFunc_mk]
    have hcoe : (frickeOperator N hN k f : ℍ → ℂ) =
        (N : ℂ)^(1-(k : ℂ)/2) • ((f : ℍ → ℂ) ∣[k] frickeReal N hN) := rfl
    rw [hcoe, ModularForm.smul_slash]
    have hd : (((SpecialLinearGroup.mapGL ℝ).subgroupMap
        (CongruenceSubgroup.Gamma0 M) a).val⁻¹).det.val = 1 := by simp
    simp only [σ, hd, zero_lt_one, ite_true, ContinuousAlgEquiv.refl_apply]
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
    congr 2
    change frickeReal N hN * (SpecialLinearGroup.mapGL ℝ a.val)⁻¹ =
      (frickeReal N hN * SpecialLinearGroup.mapGL ℝ a.val * (frickeReal N hN)⁻¹)⁻¹ *
        frickeReal N hN
    simp only [_root_.mul_inv_rev, inv_inv]
    group

theorem fricke_trace_swap (N M : ℕ) [NeZero N] [NeZero M] (hN : 0 < N) (k : ℤ)
    (f : ModularForm (level N) k) :
    (arithmeticTrace (level N) (level M) k (frickeOperator N hN k f) : ℍ → ℂ) =
      (N : ℂ)^(1-(k : ℂ)/2) •
        ((arithmeticTrace (level N) (frickeOldLevel N M hN) k f : ℍ → ℂ)
          ∣[k] frickeReal N hN) := by
  classical
  let : (level N).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let : (level N).IsFiniteRelIndex (frickeOldLevel N M hN) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := frickeOldLevel N M hN)).symm).1
  let Q := CongruenceSubgroup.Gamma0 M ⧸
    (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M)
  let := Fintype.ofFinite Q
  let := Fintype.ofFinite (level M ⧸ (level N).subgroupOf (level M))
  let := Fintype.ofFinite (frickeOldLevel N M hN ⧸
    (level N).subgroupOf (frickeOldLevel N M hN))
  change (∑ q : level M ⧸ (level N).subgroupOf (level M),
      SlashInvariantForm.quotientFunc (frickeOperator N hN k f) q) =
    (N : ℂ)^(1-(k : ℂ)/2) •
      ((∑ q : frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN),
        SlashInvariantForm.quotientFunc f q) ∣[k] frickeReal N hN)
  rw [← (matrixEquiv N M).sum_comp, ← (frickeMatrixEquiv N M hN).sum_comp,
    SlashAction.sum_slash, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun q _ => fricke_quotient_swap N M hN k f q)

theorem fricke_trace_swap_zero_iff (N M : ℕ) [NeZero N] [NeZero M]
    (hN : 0 < N) (k : ℤ) (f : ModularForm (level N) k) :
    arithmeticTrace (level N) (level M) k (frickeOperator N hN k f) = 0 ↔
      arithmeticTrace (level N) (frickeOldLevel N M hN) k f = 0 := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (N : ℂ)^(1-(k : ℂ)/2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hNC)
  have he := fricke_trace_swap N M hN k f
  constructor
  · intro hz
    rw [hz] at he
    have hslash : ((arithmeticTrace (level N) (frickeOldLevel N M hN) k f : ℍ → ℂ)
        ∣[k] frickeReal N hN) = 0 := (smul_eq_zero.mp he.symm).resolve_left hc
    exact DFunLike.coe_injective ((SlashAction.slash_eq_zero_iff k (frickeReal N hN) _).mp hslash)
  · intro hz
    rw [hz] at he
    apply DFunLike.coe_injective
    simpa only [FunLike.coe_zero, SlashAction.zero_slash, smul_zero] using he

#print axioms fricke_trace_swap
#print axioms fricke_trace_swap_zero_iff
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end

/-! ## QuantitativeArithmeticSmallLevelCircPrimeHeckeV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane AsymptoticClassicalCusp
open scoped ModularForm

/-- The usual prime Hecke operator, with the U_p correspondence at bad primes. -/
def primeHecke (N p : ℕ) [NeZero N] (hp : p.Prime) (k : ℤ) :
    ModularForm (level N) k →ₗ[ℂ] ModularForm (level N) k :=
  if p ∣ N then upperTrace N p hp.pos k else dilationTrace N p hp.pos k

/-- The local quadratic coefficient is zero at bad primes. -/
def primeHeckeFactor (N p : ℕ) (k : ℤ) : ℂ := if p ∣ N then 0 else (p : ℂ) ^ (k - 1)

theorem coeff_primeHecke (N p : ℕ) [NeZero N] (hp : p.Prime) (k : ℤ)
    (f : ModularForm (level N) k) (n : ℕ) :
    modularCoefficient N k n (primeHecke N p hp k f) =
      modularCoefficient N k (p * n) f + primeHeckeFactor N p k *
        (if p ∣ n then modularCoefficient N k (n / p) f else 0) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpN : p ∣ N
  · simp only [primeHecke, primeHeckeFactor, hpN, ite_true, zero_mul, add_zero]
    exact coeff_upperTrace_bad N p hp hpN k f n
  · simp only [primeHecke, primeHeckeFactor, hpN, ite_false]
    exact coeff_dilationTrace_prime N p hpN k f n

theorem first_primeHecke (N p : ℕ) [NeZero N] (hp : p.Prime) (k : ℤ)
    (f : ModularForm (level N) k) :
    modularCoefficient N k 1 (primeHecke N p hp k f) = modularCoefficient N k p f := by
  rw [coeff_primeHecke]
  simp [hp.not_dvd_one]

/-- The actual good and bad prime operators all commute at distinct primes. -/
theorem primeHecke_commute (N p q : ℕ) [NeZero N] (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (k : ℤ) :
    Function.Commute (primeHecke N p hp k) (primeHecke N q hq k) := by
  intro f
  apply sub_eq_zero.mp
  apply modularCoefficient_separates N k
  intro n
  rw [map_sub]
  apply sub_eq_zero.mpr
  simp_rw [coeff_primeHecke N p hp, coeff_primeHecke N q hq, coeff_primeHecke N p hp]
  have hh := congrFun (AsymptoticClassicalHeckeCoefficients.hecke_commute p q hp.pos hq.pos hpq
    (primeHeckeFactor N p k) (primeHeckeFactor N q k)
    (fun m => modularCoefficient N k m f)) n
  simpa only [AsymptoticClassicalHeckeCoefficients.hecke,
    AsymptoticClassicalHeckeCoefficients.down] using hh

#print axioms coeff_primeHecke
#print axioms first_primeHecke
#print axioms primeHecke_commute
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
end
end
