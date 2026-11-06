module

public import AsymptoticOrbitDiagonalV1
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
@[expose] public section

namespace AsymptoticHyperbolicArea

open MeasureTheory UpperHalfPlane Set
open scoped ENNReal NNReal lp

/-- The terminal part of the translation strip. Using a strict height
cutoff avoids a boundary whose hyperbolic measure is zero. -/
def terminal (ε : ℝ) : Set ℍ :=
  AsymptoticMassTransport.strip∩(fun z : ℍ => z.im) ⁻¹' Ioi ε

theorem terminal_measurable (ε : ℝ) : MeasurableSet (terminal ε) :=
  AsymptoticMassTransport.strip_measurable.inter
    (measurableSet_Ioi.preimage continuous_im.measurable)

theorem vertical_area {ε : ℝ} (hε : 0<ε) :
    (∫⁻ y : ℝ in Ioi ε, (↑((1/‖y‖₊)^2 : ℝ≥0) : ℝ≥0∞))=ENNReal.ofReal ε⁻¹ := by
  have hi := integrableOn_Ioi_rpow_of_lt (a:=(-2 : ℝ)) (by norm_num) hε
  have he := integral_Ioi_rpow_of_lt (a:=(-2 : ℝ)) (by norm_num) hε
  have hfun : ∀ y∈Ioi ε, (↑((1/‖y‖₊)^2 : ℝ≥0) : ℝ≥0∞)=
      ENNReal.ofReal (y^(-2 : ℝ)) := by
    intro y hy
    have hy0 : 0<y := hε.trans hy
    rw [Real.rpow_neg hy0.le,Real.rpow_two]
    rw [ENNReal.coe_nnreal_eq]
    congr 1
    simp [Real.nnnorm_of_nonneg hy0.le]
  rw [setLIntegral_congr_fun measurableSet_Ioi hfun,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun y => by
        change 0≤y^(-2 : ℝ)
        rw [Real.rpow_neg_eq_inv_rpow,Real.rpow_two]
        positivity)),he]
  norm_num [Real.rpow_neg_one]

theorem terminal_image {ε : ℝ} (hε : 0<ε) :
    UpperHalfPlane.coe '' terminal ε=
      Complex.measurableEquivRealProd.symm '' (Ico (0 : ℝ) 1 ×ˢ Ioi ε) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨(w.re,w.im),hw,rfl⟩
  · rintro ⟨⟨x,y⟩,hxy,rfl⟩
    exact ⟨⟨⟨x,y⟩,hε.trans hxy.2⟩,hxy,rfl⟩

/-- The finite terminal corner has trace ε⁻¹, computed from the actual
hyperbolic measure used by the rational action. -/
theorem terminal_area {ε : ℝ} (hε : 0<ε) :
    (volume : Measure ℍ) (terminal ε)=ENNReal.ofReal ε⁻¹ := by
  rw [UpperHalfPlane.volume_eq_lintegral,terminal_image hε]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  change (∫⁻ p : ℝ×ℝ in Ico (0 : ℝ) 1 ×ˢ Ioi ε,
    (↑((1/‖p.2‖₊)^2 : ℝ≥0) : ℝ≥0∞))=ENNReal.ofReal ε⁻¹
  rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
  simp only [vertical_area hε]
  simp

theorem terminal_trace {ε : ℝ} (hε : 0<ε) :
    AsymptoticRegularTrace.trace volume
      (AsymptoticOrbitDiagonal.corner (G:=AsymptoticRationalGroup.Group) (terminal ε))=
        ENNReal.ofReal ε⁻¹ := by
  rw [AsymptoticOrbitDiagonal.trace_corner volume (terminal_measurable ε),terminal_area hε]

theorem terminal_trace_finite {ε C : ℝ} (hε : 0<ε)
    (B : ℍ → ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ]
      ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hB : ∀ x, ‖B x‖≤C)
    (hsupport : ∀ x, (B x).comp (AsymptoticOrbitDiagonal.corner (terminal ε) x)=B x) :
    AsymptoticRegularTrace.trace volume B<∞ := by
  have hb := AsymptoticOrbitDiagonal.trace_le_corner volume (terminal_measurable ε) B hB hsupport
  rw [terminal_area hε] at hb
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- The closed-height terminal strip used by the reconstruction. -/
def closedTerminal (ε : ℝ) : Set ℍ :=
  AsymptoticMassTransport.strip∩(fun z : ℍ => z.im) ⁻¹' Ici ε

theorem closedTerminal_measurable (ε : ℝ) : MeasurableSet (closedTerminal ε) :=
  AsymptoticMassTransport.strip_measurable.inter
    (measurableSet_Ici.preimage continuous_im.measurable)

theorem closedTerminal_image {ε : ℝ} (hε : 0<ε) :
    UpperHalfPlane.coe '' closedTerminal ε=
      Complex.measurableEquivRealProd.symm '' (Ico (0:ℝ) 1 ×ˢ Ici ε) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨(w.re,w.im),hw,rfl⟩
  · rintro ⟨⟨x,y⟩,hxy,rfl⟩
    exact ⟨⟨⟨x,y⟩,hε.trans_le hxy.2⟩,hxy,rfl⟩

theorem closed_terminal_area {ε : ℝ} (hε : 0<ε) :
    (volume : Measure ℍ) (closedTerminal ε)=ENNReal.ofReal ε⁻¹ := by
  rw [UpperHalfPlane.volume_eq_lintegral,closedTerminal_image hε]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  change (∫⁻ p : ℝ×ℝ in Ico (0:ℝ) 1 ×ˢ Ici ε,
    (↑((1/‖p.2‖₊)^2 : ℝ≥0) : ℝ≥0∞))=ENNReal.ofReal ε⁻¹
  rw [Measure.volume_eq_prod,setLIntegral_prod _ (by fun_prop)]
  have hi : (∫⁻ y : ℝ in Ici ε,(↑((1/‖y‖₊)^2 : ℝ≥0) : ℝ≥0∞))=ENNReal.ofReal ε⁻¹ := by
    rw [← restrict_Ioi_eq_restrict_Ici]
    exact vertical_area hε
  simp only [hi]
  simp

theorem closed_terminal_trace_finite {ε C : ℝ} (hε : 0<ε)
    (B : ℍ → ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ]
      ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hB : ∀ x,‖B x‖≤C)
    (hsupport : ∀ x,(B x).comp (AsymptoticOrbitDiagonal.corner (closedTerminal ε) x)=B x) :
    AsymptoticRegularTrace.trace volume B<∞ := by
  have hb := AsymptoticOrbitDiagonal.trace_le_corner volume (closedTerminal_measurable ε) B hB hsupport
  rw [closed_terminal_area hε] at hb
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

#print axioms closed_terminal_area
#print axioms closed_terminal_trace_finite
#print axioms terminal_area
#print axioms terminal_trace
#print axioms terminal_trace_finite

end AsymptoticHyperbolicArea
