module

public import QuantitativeArithmeticSmallLevelCircModularLSeriesTheoryV4
public import AsymptoticClassicalFrickeSquareV1

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane Complex AsymptoticClassicalCusp AsymptoticClassicalLSeries
open scoped ModularForm

/-- The Fricke square identity is an identity on functions, with no cusp hypothesis. -/
theorem fricke_slash_square (N : ℕ) (hN : 0<N) (k : ℤ) (f : ℍ → ℂ) :
    (f ∣[k] SmallLevelNormalized.fricke N hN) ∣[k] SmallLevelNormalized.fricke N hN =
      (-1 : ℂ)^k • f := by
  rw [← ModularLSeries.normalizedFricke_eq_detOne_slash,
    ← ModularLSeries.normalizedFricke_eq_detOne_slash]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : ((N : ℂ)^(-(k : ℂ)/2))^2 * (N : ℂ)^k = 1 := by
    rw [← Complex.cpow_intCast, pow_two, ← Complex.cpow_add _ _ hNC,
      ← Complex.cpow_add _ _ hNC]
    rw [show -(k : ℂ)/2 + -(k : ℂ)/2 + (k : ℂ) = 0 by ring, Complex.cpow_zero]
  funext z
  simp only [normalizedFricke, Pi.smul_apply, smul_eq_mul]
  rw [fricke_action_twice, frickeReal_action]
  have hpow : (z : ℂ)^(-k) * (z : ℂ)^k = 1 := by
    rw [← zpow_add₀ (ne_zero z), neg_add_cancel, zpow_zero]
  have hn : ((-1 : ℂ)^k)⁻¹ = (-1 : ℂ)^k := by
    rw [← inv_zpow, inv_neg, inv_one]
  have hWpow : (-1 / ((N : ℂ) * (z : ℂ)))^(-k) =
      (-1 : ℂ)^k * (N : ℂ)^k * (z : ℂ)^k := by
    rw [zpow_neg, div_zpow, mul_zpow, inv_div, div_eq_mul_inv, hn]
    ring
  rw [hWpow]
  calc
    _ = (((N : ℂ)^(-(k : ℂ)/2))^2 * (N : ℂ)^k) *
        ((z : ℂ)^(-k) * (z : ℂ)^k) * (-1 : ℂ)^k * f z := by ring
    _ = _ := by rw [hc, hpow, one_mul, one_mul]

theorem fricke_slash_involutive (N : ℕ) (hN : 0<N) (k : ℕ) (hk : Even k)
    (f : ℍ → ℂ) :
    (f ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN) ∣[(k : ℤ)]
      SmallLevelNormalized.fricke N hN = f := by
  rw [fricke_slash_square, zpow_natCast, hk.neg_one_pow, one_smul]

/-- Genuine preservation of the two trace kernels and the two cusp zeros:
Fricke interchanges the two entries in their defining pair. -/
theorem fricke_mem_space {N k : ℕ} {hN : 0<N} (hk : Even k)
    (F G : ModularForm (level N) (k : ℤ)) (hF : F ∈ space N hN k)
    (hG : (G : ℍ → ℂ) = (F : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN) :
    G ∈ space N hN k := by
  obtain ⟨H,hH,hF0,hH0,ht⟩ := hF
  have hHG : H=G := DFunLike.coe_injective (hH.trans hG.symm)
  subst H
  refine ⟨F, ?_, hH0, hF0, fun p => ⟨(ht p).2,(ht p).1⟩⟩
  rw [hG, fricke_slash_involutive N hN k hk]

/-- The actual Fricke translate, as an element of the full space M_k^circ. -/
def frickeValue {N k : ℕ} {hN : 0<N} (hk : Even k) (F : space N hN k) :
    space N hN k :=
  ⟨Classical.choose F.property,
    fricke_mem_space hk F.val (Classical.choose F.property) F.property
      (Classical.choose_spec F.property).1⟩

theorem frickeValue_coe {N k : ℕ} {hN : 0<N} (hk : Even k) (F : space N hN k) :
    ((frickeValue hk F).val : ℍ → ℂ) =
      (F.val : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN :=
  (Classical.choose_spec F.property).1

/-- Fricke is complex linear on the entire trace-new space, including its Eisenstein part. -/
def frickeLinear {N k : ℕ} {hN : 0<N} (hk : Even k) :
    space N hN k →ₗ[ℂ] space N hN k where
  toFun := frickeValue hk
  map_add' F G := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    simp only [frickeValue_coe, Submodule.coe_add, FunLike.coe_add, SlashAction.add_slash]
  map_smul' c F := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    simp only [frickeValue_coe, Submodule.coe_smul, FunLike.coe_smul,
      SmallLevelNormalized.det_one_smul _ (SmallLevelNormalized.fricke_det N hN),
      RingHom.id_apply]

theorem frickeLinear_involutive {N k : ℕ} {hN : 0<N} (hk : Even k) :
    Function.Involutive (frickeLinear (hN := hN) hk) := by
  intro F
  apply Subtype.ext
  apply DFunLike.coe_injective
  change ((frickeValue hk (frickeValue hk F)).val : ℍ → ℂ) = _
  rw [frickeValue_coe, frickeValue_coe, fricke_slash_involutive N hN k hk]

/-- In particular Fricke gives an automorphism of the genuine full modular subspace. -/
def frickeEquiv {N k : ℕ} {hN : 0<N} (hk : Even k) :
    space N hN k ≃ₗ[ℂ] space N hN k :=
  LinearEquiv.ofInvolutive (frickeLinear hk) (frickeLinear_involutive hk)

#print axioms fricke_slash_square
#print axioms fricke_mem_space
#print axioms frickeLinear
#print axioms frickeLinear_involutive
#print axioms frickeEquiv
end QuantitativeArithmeticSmallLevelCirc
