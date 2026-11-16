module

public import QuantitativeMaassIntegralSchurOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology ComplexConjugate

namespace QuantitativeMaass.IntegralSchur
variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SFinite μ]

def Data.transpose (D : Data μ) : Data μ where
  kernel := fun x y => D.kernel y x
  measurable := D.measurable.comp measurable_swap
  bound := D.bound
  bound_nonneg := D.bound_nonneg
  row_integrable := D.column_integrable
  column_integrable := D.row_integrable
  row_bound := D.column_bound
  column_bound := D.row_bound

/-- Absolute integrability of the full kernel pairing is derived from both
Schur energy bounds; it is not assumed in the Fubini identity. -/
theorem Data.pairing_integrable (D : Data μ) (f g : Lp ℂ 2 μ) :
    Integrable (fun p : A×A => star (g p.1)*D.kernel p.1 p.2*f p.2) (μ.prod μ) := by
  have hf := (energy_integrable D.kernel D.measurable D.bound_nonneg
    D.column_integrable D.column_bound f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1
  have hg := (energy_integrable D.transpose.kernel D.transpose.measurable D.bound_nonneg
    D.row_integrable D.row_bound g (Lp.stronglyMeasurable g).measurable (Lp.memLp g)).1.swap
  have hG : Integrable (fun p : A×A => ‖D.kernel p.1 p.2‖*‖g p.1‖^2) (μ.prod μ) := hg
  apply (hf.add hG).mono'
    (((continuous_star.measurable.comp ((Lp.stronglyMeasurable g).measurable.comp measurable_fst)).mul
      D.measurable).mul ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).aestronglyMeasurable
  filter_upwards with p
  change ‖star (g p.1)*D.kernel p.1 p.2*f p.2‖≤
    ‖D.kernel p.1 p.2‖*‖f p.2‖^2+‖D.kernel p.1 p.2‖*‖g p.1‖^2
  simp only [norm_mul,norm_star]
  have hab : ‖f p.2‖*‖g p.1‖≤‖f p.2‖^2+‖g p.1‖^2 := by
    nlinarith [sq_nonneg (‖f p.2‖-‖g p.1‖),mul_nonneg (norm_nonneg (f p.2)) (norm_nonneg (g p.1))]
  calc
    _ = ‖D.kernel p.1 p.2‖*(‖f p.2‖*‖g p.1‖) := by ring
    _ ≤ ‖D.kernel p.1 p.2‖*(‖f p.2‖^2+‖g p.1‖^2) :=
      mul_le_mul_of_nonneg_left hab (norm_nonneg _)
    _ = _ := by ring

/-- Exact Hilbert pairing with the integral kernel, for arbitrary L2 inputs. -/
theorem Data.operator_pairing (D : Data μ) (f g : Lp ℂ 2 μ) :
    inner ℂ g (D.operator f)=
      ∫ p : A×A,star (g p.1)*D.kernel p.1 p.2*f p.2 ∂μ.prod μ := by
  rw [L2.inner_def,integral_prod _ (D.pairing_integrable f g)]
  apply integral_congr_ae
  filter_upwards [D.operator_coeFn f] with x hx
  rw [hx,RCLike.inner_apply,mul_comm,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  change star (g x)*(D.kernel x y*f y)=star (g x)*D.kernel x y*f y
  ring

/-- Hermitian symmetry of a measurable Schur kernel gives the actual
operator adjoint identity by the proved absolutely integrable pairing. -/
theorem Data.operator_selfAdjoint (D : Data μ)
    (hK : ∀ x y,star (D.kernel y x)=D.kernel x y) : D.operator.adjoint=D.operator := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [← inner_conj_symm, D.operator_pairing, D.operator_pairing,← integral_conj]
  rw [← integral_prod_swap (fun p : A×A => star (f p.1)*D.kernel p.1 p.2*g p.2)]
  apply integral_congr_ae
  filter_upwards with p
  change star (star (g p.1)*D.kernel p.1 p.2*f p.2)=
    star (f p.2)*D.kernel p.2 p.1*g p.1
  simp only [star_mul,star_star,hK]
  ring

#print axioms Data.pairing_integrable
#print axioms Data.operator_pairing
#print axioms Data.operator_selfAdjoint

end QuantitativeMaass.IntegralSchur
