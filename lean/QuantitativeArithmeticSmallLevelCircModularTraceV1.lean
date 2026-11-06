module

public import QuantitativeArithmeticSmallLevelCircCoefficientsV1
public import AsymptoticClassicalDiscriminantFamilyV1
public import AsymptoticClassicalBadHeckeV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane Matrix ConjAct AsymptoticClassicalCusp
open scoped ModularForm MatrixGroups Pointwise

variable {G H : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [H.HasDetOne] (k : ℤ)
variable [G.IsFiniteRelIndex H]

/-- The classical coset trace, as a complex linear map. All matrices of the
 target have determinant one, so the GL slash action is complex linear. -/
def trace : ModularForm G k →ₗ[ℂ] ModularForm H k where
  toFun := fun f : ModularForm G k => ModularForm.trace H f
  map_add' f g := by
    classical
    apply ModularForm.ext
    intro z
    simp only [ModularForm.coe_trace, Finset.sum_apply, _root_.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with
    | h r => simp [SlashInvariantForm.quotientFunc_mk]
  map_smul' c f := by
    change ModularForm.trace H (c • f) = c • ModularForm.trace H f
    classical
    apply ModularForm.ext
    intro z
    simp only [ModularForm.coe_trace, Finset.sum_apply, _root_.smul_apply,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with
    | h r =>
      simp [SlashInvariantForm.quotientFunc_mk,
        ModularForm.smul_slash, σ, Subgroup.HasDetOne.det_eq (H.inv_mem r.property)]

@[simp] theorem trace_apply (f : ModularForm G k) :
    trace k f = ModularForm.trace H f := rfl

section Translate
variable (G : Subgroup (GL (Fin 2) ℝ)) [G.HasDetOne] (k : ℤ)
variable (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
/-- Positive-determinant translation is complex linear between the
 actual classical cusp spaces on conjugate groups. -/
def translateLinear : ModularForm G k →ₗ[ℂ] ModularForm (toConjAct g⁻¹ • G) k where
  toFun f := ModularForm.translate f g
  map_add' f h := by
    apply DFunLike.coe_injective
    change ((f + h : ModularForm G k) : ℍ → ℂ) ∣[k] g = _
    rw [FunLike.coe_add, SlashAction.add_slash]
    rfl
  map_smul' c f := by
    apply DFunLike.coe_injective
    change ((c • f : ModularForm G k) : ℍ → ℂ) ∣[k] g = _
    rw [FunLike.coe_smul, ModularForm.smul_slash]
    simp only [σ, hg, ite_true, ContinuousAlgEquiv.refl_apply]
    rfl

@[simp] theorem translateLinear_coe (f : ModularForm G k) :
    (translateLinear G k g hg f : ℍ → ℂ) = (f : ℍ → ℂ) ∣[k] g := rfl

end Translate

/-- The translated cusp form with the determinant normalization chosen
 so that its value is literally f(p*z). -/
def degeneracyForm (M p : ℕ) (hp : 0 < p) (k : ℤ) (f : ModularForm (level M) k) :
    ModularForm (level (p * M)) k :=
  (p : ℂ) ^ (1 - k) • restrictModular k (level_le_dilation_conjugate M p hp)
    (ModularForm.translate f (dilationReal p hp))

theorem degeneracyForm_apply (M p : ℕ) (hp : 0 < p) (k : ℤ)
    (f : ModularForm (level M) k) (z : ℍ) :
    degeneracyForm M p hp k f z = f (dilationReal p hp • z) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  change (p : ℂ) ^ (1 - k) * ((f : ℍ → ℂ) ∣[k] dilationReal p hp) z = _
  simp only [ModularForm.slash_def]
  rw [dilationReal_denom, dilationReal_det]
  simp only [σ, dilationReal_det, hpR, ite_true, ContinuousAlgEquiv.refl_apply,
    abs_of_pos hpR, Complex.ofReal_natCast, _root_.one_zpow, mul_one]
  calc
    _ = ((p : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 1)) * f (dilationReal p hp • z) := by ring
    _ = _ := by rw [← zpow_add₀ hpC]; simp

/-- The normalized degeneracy map between the actual classical cusp spaces. -/
def degeneracy (M p : ℕ) (hp : 0 < p) (k : ℤ) :
    ModularForm (level M) k →ₗ[ℂ] ModularForm (level (p * M)) k where
  toFun := degeneracyForm M p hp k
  map_add' f g := by
    ext z
    simp only [degeneracyForm_apply, _root_.add_apply]
  map_smul' c f := by
    ext z
    simp only [degeneracyForm_apply, _root_.smul_apply, RingHom.id_apply]

@[simp] theorem degeneracy_apply (M p : ℕ) (hp : 0 < p) (k : ℤ)
    (f : ModularForm (level M) k) (z : ℍ) :
    degeneracy M p hp k f z = f (dilationReal p hp • z) := degeneracyForm_apply M p hp k f z

theorem degeneracy_injective (M p : ℕ) (hp : 0 < p) (k : ℤ) :
    Function.Injective (degeneracy M p hp k) := by
  intro f g he
  ext z
  have hz := congrArg (fun h : ModularForm (level (p * M)) k => h ((dilationReal p hp)⁻¹ • z)) he
  simpa only [degeneracy_apply, smul_inv_smul] using hz

/-- Literal arithmetic trace on all modular forms, including Eisenstein forms. -/
def arithmeticTrace (G H : Subgroup (GL (Fin 2) ℝ))
    [G.HasDetOne] [H.HasDetOne] [G.IsArithmetic] [H.IsArithmetic] (k : ℤ) :
    ModularForm G k →ₗ[ℂ] ModularForm H k := by
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  exact trace k

/-- The genuine full-space good-prime correspondence. -/
def dilationTrace (N p : ℕ) [NeZero N] (hp : 0<p) (k : ℤ) :
    ModularForm (level N) k →ₗ[ℂ] ModularForm (level N) k := by
  let : NeZero (p*N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  exact (p : ℂ)^(k-1) •
    (arithmeticTrace (level (p*N)) (level N) k).comp (degeneracy N p hp k)

#print axioms trace
#print axioms translateLinear
#print axioms degeneracy_injective
#print axioms dilationTrace
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
