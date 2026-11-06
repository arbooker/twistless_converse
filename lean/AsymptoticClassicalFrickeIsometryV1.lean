module

public import AsymptoticClassicalFrickeNewV1
public import AsymptoticClassicalPeterssonNormalizerV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane Complex AsymptoticClassicalCusp AsymptoticClassicalLSeries
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticFreshMatrices
open scoped ModularForm ComplexConjugate InnerProduct

/-- The determinant-half-weight normalized global Fricke operator
preserves the actual Petersson inner product. -/
theorem inner_frickeOperator (N : ℕ) [NeZero N] (hN : 0 < N) (k : ℤ)
    (f g : CuspForm (level N) k) :
    inner ℂ (frickeOperator N hN k f) (frickeOperator N hN k g) = inner ℂ f g := by
  let c : ℂ := (N : ℂ)^(1-(k : ℂ)/2)
  let raw (u : CuspForm (level N) k) : CuspForm (level N) k :=
    CuspForm.mcast rfl (CuspForm.translate u (frickeReal N hN))
      (fricke_inverse_normalizes N hN).symm
  have hraw (u : CuspForm (level N) k) :
      (raw u : ℍ → ℂ) = (u : ℍ → ℂ) ∣[k] frickeReal N hN := rfl
  have hJ (u : CuspForm (level N) k) : frickeOperator N hN k u = c • raw u := by
    apply DFunLike.coe_injective
    rw [frickeOperator_coe, normalizedFricke_eq_slash]
    rfl
  have ha (z : ℍ) : frickeReal N hN • z = frickeLabel N hN • z := by
    symm
    exact AsymptoticRationalBranches.ofMatrix_action _ _ z
  have hh := inner_slash_normalizer N k (frickeLabel N hN) (frickeReal N hN)
    (by rw [frickeReal_det]; exact_mod_cast hN) ha
    (fun _ hx => fricke_conj_mem N hN hx)
    (fun _ hx => by simpa only [frickeLabel_inv] using fricke_conj_mem N hN hx)
    f g (raw f) (raw g) (hraw f) (hraw g)
  rw [frickeReal_det] at hh
  simp only [Complex.ofReal_natCast] at hh
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc : c = (((N : ℝ)^(1-(k : ℝ)/2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hNR.le]
    dsimp [c]
    push_cast
    rfl
  have hs : conj c * c * (N : ℂ)^(k-2) = 1 := by
    rw [hc, Complex.conj_ofReal, ← Complex.ofReal_natCast N,
      ← Complex.ofReal_zpow, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    rw [← Real.rpow_intCast, ← Real.rpow_add hNR, ← Real.rpow_add hNR]
    push_cast
    rw [show 1-(k : ℝ)/2 + (1-(k : ℝ)/2) + ((k : ℝ)-2) = 0 by ring,
      Real.rpow_zero]
  rw [hJ f, hJ g, inner_smul_left, inner_smul_right, hh]
  calc
    _ = (conj c * c * (N : ℂ)^(k-2)) * inner ℂ f g := by ring
    _ = _ := by rw [hs, one_mul]

/-- Fricke is also an isometry on the genuine newspace. -/
theorem inner_newFrickeOperator (N : ℕ) [NeZero N] (hN : 0 < N) (k : ℤ)
    (f g : newSpace N hN k) :
    inner ℂ (newFrickeOperator N hN k f) (newFrickeOperator N hN k g) = inner ℂ f g :=
  inner_frickeOperator N hN k f.val g.val

#print axioms inner_frickeOperator
#print axioms inner_newFrickeOperator

end AsymptoticClassicalPetersson
