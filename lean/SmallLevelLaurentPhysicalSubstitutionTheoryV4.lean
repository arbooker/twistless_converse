module

public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import SmallLevelLaurentGermOperationsV1

/-! Consolidated chapter: SmallLevelLaurentPhysicalSubstitution. Original declarations and local scopes are retained. -/

/-! ## SmallLevelLaurentPhysicalSubstitutionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelLaurentPhysicalSubstitution
open QuantitativeArithmeticSevenLaurentRows

/-- Substitute the squared prime parameters and the normalized Hecke parameters. -/
def physicalExponent (e : Exponent) : Exponent :=
  (e.1,2*e.2.1+(e.2.2.2.2.1:ℤ),e.2.2.1,
    2*e.2.2.2.1+(e.2.2.2.2.2.1:ℤ),e.2.2.2.2.1,e.2.2.2.2.2.1,e.2.2.2.2.2.2)

def physicalRows (p : Poly) : Poly :=
  p.map fun t => (t.1,t.2.1,physicalExponent t.2.2)

theorem monomial_physical (x y z w a b c : ℂ) (hy : y≠0) (hw : w≠0)
    (e : Exponent) :
    monomial x y z w a b c (physicalExponent e)=
      monomial x (y^2) z (w^2) (a*y) (b*w) c e := by
  simp only [monomial,physicalExponent,zpow_add₀ hy,zpow_add₀ hw,
    zpow_mul,zpow_natCast,zpow_ofNat,mul_pow]
  ring

theorem eval_physical (x y z w a b c : ℂ) (hy : y≠0) (hw : w≠0)
    (u : ℕ→ℂ) (p : Poly) :
    eval x y z w a b c u (physicalRows p)=
      eval x (y^2) z (w^2) (a*y) (b*w) c u p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [physicalRows] at ih
    simp only [physicalRows,List.map_cons,eval_cons,
      monomial_physical x y z w a b c hy hw,ih]

#print axioms monomial_physical
#print axioms eval_physical
end SmallLevelLaurentPhysicalSubstitution
end
end

/-! ## SmallLevelLaurentNormalizationGermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelLaurentPhysicalSubstitution
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm

/-- Remove the explicit nonvanishing exponential monomial used to
normalize a raw Laurent row. The Hecke parameters may be zero. -/
theorem unit_normalization_germ (X Y Z W : ℂ→ℂ) (a b s : ℂ)
    (r : ℚ) (e : ℤ×ℤ×ℤ×ℤ) (u : ℂ→ℕ→ℂ) (raw primitive : Poly)
    (hr : r≠0)
    (hcertificate : raw=shift r (e.1,e.2.1,e.2.2.1,e.2.2.2,0,0,0) (physicalRows primitive))
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hx : ∀ t,X t≠0) (hy : ∀ t,Y t≠0) (hz : ∀ t,Z t≠0) (hw : ∀ t,W t≠0)
    (hraw : HasAnalyticGerm (fun t => eval (X t) (Y t) (Z t) (W t) a b 1 (u t) raw) s) :
    HasAnalyticGerm (fun t => eval (X t) ((Y t)^2) (Z t) ((W t)^2)
      (a*Y t) (b*W t) 1 (u t) primitive) s := by
  let U : ℂ→ℂ := fun t => (r:ℂ)*monomial (X t) (Y t) (Z t) (W t) a b 1
    (e.1,e.2.1,e.2.2.1,e.2.2.2,0,0,0)
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hr
  have hU (t : ℂ) : U t≠0 := by
    simp only [U,monomial,pow_zero,mul_one]
    exact mul_ne_zero hrC (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (zpow_ne_zero _ (hx t)) (zpow_ne_zero _ (hy t)))
      (zpow_ne_zero _ (hz t))) (zpow_ne_zero _ (hw t)))
  have hUa : AnalyticAt ℂ U s := analyticAt_const.mul
    (monomial_analytic X Y Z W a b 1 s _ hX hY hZ hW (hx s) (hy s) (hz s) (hw s))
  have hUi : AnalyticAt ℂ (fun t => (1:ℂ)/U t) s := analyticAt_const.div hUa (hU s)
  have hh := hraw.mul_analytic hUi
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro t
  have he : eval (X t) (Y t) (Z t) (W t) a b 1 (u t) raw =
      U t*eval (X t) ((Y t)^2) (Z t) ((W t)^2) (a*Y t) (b*W t) 1 (u t) primitive := by
    rw [hcertificate,eval_shift (X t) (Y t) (Z t) (W t) a b 1 (u t)
      (hx t) (hy t) (hz t) (hw t),eval_physical (X t) (Y t) (Z t) (W t) a b 1 (hy t) (hw t)]
  dsimp only
  rw [he]
  field_simp [hU t]

#print axioms unit_normalization_germ
end SmallLevelLaurentPhysicalSubstitution
end
end
