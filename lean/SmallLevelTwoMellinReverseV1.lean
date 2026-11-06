module

public import QuantitativeArithmeticSmallLevelNineteenTwoMellinTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwoMellin
open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries
  FinitenessFourierConstruction FinitenessAllLevelAxisDecay FinitenessAllLevelMellinPair
open QuantitativeArithmeticSmallLevelNineteenTwoMellin

/-- The reverse member of a genuine two-series Mellin pair has the same
entireness and finite-order control, with the inverse root number. -/
theorem two_mellin_reverse {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (a b : ℕ → ℂ)
    (ha : PolynomialBound a) (ha0 : a 0 = 0)
    (hb : PolynomialBound b) (hb0 : b 0 = 0) (ε : ℂ) (hε : ε ≠ 0)
    (hfr : ∀ z : ℂ, 0 < z.im → fourier a z =
      (ε * I ^ k) / (((Real.sqrt N : ℝ) : ℂ) * z) ^ k *
        fourier b (-1 / ((N : ℂ) * z))) :
    Differentiable ℂ (mellin (axis N b)) ∧
      FinitenessFiniteOrder.Bound (mellin (axis N b)) ∧
      ∀ w : ℂ, mellin (axis N b) w = ε⁻¹ * mellin (axis N a) ((k : ℂ) - w) := by
  let P := two_pair hN hk a b ha ha0 hb hb0 ε hε hfr
  have hP : IsStrongFEPair P := two_pair_strong hN hk a b ha ha0 hb hb0 ε hε hfr
  have he : P.Λ = mellin (axis N a) := funext (fun w => (hP.hasMellin w).2.symm)
  have he' : P.symm.Λ = mellin (axis N b) := funext (fun w => (hP.symm.hasMellin w).2.symm)
  obtain ⟨Ca, ca, hCa, hca, hba⟩ := axis_exponential hN ha ha0
  obtain ⟨Cb, cb, hCb, hcb, hbb⟩ := axis_exponential hN hb hb0
  refine ⟨he' ▸ hP.symm.differentiable_Λ,
    he' ▸ AsymptoticClassicalLSeries.strongPair_finiteOrder P.symm hP.symm hCb hCa hcb hca hbb hba, ?_⟩
  intro w
  have h := P.functional_equation w
  rw [he, he'] at h
  have hh : mellin (axis N a) ((k:ℂ)-w)=ε*mellin (axis N b) w := by
    simpa only [P,two_pair,ofReal_natCast,smul_eq_mul] using h
  rw [hh,← mul_assoc,inv_mul_cancel₀ hε,one_mul]

#print axioms two_mellin_reverse
end SmallLevelTwoMellin
