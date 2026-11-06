module

public import AsymptoticMassTransportV1
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory UpperHalfPlane ContinuousLinearMap InnerProductSpace
open scoped lp InnerProduct ComplexConjugate ENNReal

variable {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]

noncomputable def delta (g : G) : ℓ²(G,ℂ) := by
  classical
  exact lp.single 2 g 1

noncomputable def matrix (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (g h : G) : ℂ :=
  B (delta h) g

omit [Group G] in
theorem delta_inner (g : G) (v : ℓ²(G,ℂ)) : ⟪delta g,v⟫_ℂ=v g := by
  classical
  simp [delta,lp.inner_single_left,RCLike.inner_apply]

omit [Group G] in
theorem matrix_adjoint (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (g h : G) :
    matrix B.adjoint g h=conj (matrix B h g) := by
  rw [matrix,← delta_inner,adjoint_inner_right,← inner_conj_symm,delta_inner]
  rfl

/-- Re-rooting an orbit at `a • x` relabels its counting coordinates by
right multiplication by `a`. This is the covariance of actual orbit
operators, including operators supported on the translation strip. -/
def Covariant (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) : Prop :=
  ∀ x a g h, matrix (B (a • x)) g h=matrix (B x) (g*a) (h*a)

noncomputable def trace (μ : Measure α) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) : ℝ≥0∞ :=
  ∫⁻ x,ENNReal.ofReal (matrix (B x) 1 1).re ∂μ

omit [Group G] in
/-- Parseval with a nonnegative extended-real sum, so no integrability
or finite-row hypothesis is needed in the subsequent trace identity. -/
theorem energy_sum (v : ℓ²(G,ℂ)) :
    (∑' g,ENNReal.ofReal (‖v g‖^2))=ENNReal.ofReal (‖v‖^2) := by
  have hv : HasSum (fun g => ‖v g‖^2) (‖v‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) v
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hv.summable,hv.tsum_eq]

omit [Group G] in
theorem matrix_gram (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (g : G) :
    (matrix (B.adjoint.comp B) g g).re=‖B (delta g)‖^2 := by
  rw [matrix,← delta_inner,comp_apply,adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) _).symm

omit [MulAction G α] in
theorem trace_gram (μ : Measure α) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    trace μ (fun x => (B x).adjoint.comp (B x))=
      ∫⁻ x,ENNReal.ofReal (‖B x (delta 1)‖^2) ∂μ := by
  simp only [trace,matrix_gram]

/-- The rooted trace is tracial for covariant measurable orbit
operators. Tonelli and mass transport handle arbitrary infinite rows
and columns; the common value is allowed to be infinite. -/
theorem trace_adjoint_mul [Countable G] {μ : Measure α}
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hc : Covariant B) :
    trace μ (fun x => (B x).adjoint.comp (B x))=
      trace μ (fun x => (B x).comp (B x).adjoint) := by
  have hm (g : G) : Measurable (fun x => ENNReal.ofReal (‖matrix (B x) g 1‖^2)) :=
    ((hB g 1).norm.pow_const 2).ennreal_ofReal
  have he := AsymptoticMassTransport.indexed_transport hmp _ hm
  have hcov (g : G) (x : α) : matrix (B (g • x)) g⁻¹ 1=matrix (B x) 1 g := by
    simpa using hc x g g⁻¹ 1
  simp_rw [hcov] at he
  have hnorm (x : α) (g : G) : ‖matrix (B x) 1 g‖=‖(B x).adjoint (delta 1) g‖ := by
    rw [← matrix,matrix_adjoint,RCLike.norm_conj]
  simp_rw [hnorm] at he
  change (∫⁻ x,∑' g,ENNReal.ofReal (‖B x (delta 1) g‖^2) ∂μ)=_ at he
  simp_rw [energy_sum] at he
  rw [trace_gram]
  have ht := trace_gram μ (fun x => (B x).adjoint)
  simp only [adjoint_adjoint] at ht
  rw [ht]
  exact he

/-- Specialization to the positive rational projective group with its
proved measure-preserving action on hyperbolic area. -/
theorem rational_trace_adjoint_mul
    (B : ℍ → ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ]
      ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hB : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hc : Covariant B) :
    trace volume (fun x => (B x).adjoint.comp (B x))=
      trace volume (fun x => (B x).comp (B x).adjoint) :=
  trace_adjoint_mul AsymptoticRationalGroup.measurePreserving B hB hc

omit [Group G] in
theorem eq_zero_of_columns (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g, B (delta g)=0) : B=0 := by
  classical
  apply lp.ext_continuousLinearMap (p:=2) (by norm_num)
  intro g
  apply DFunLike.ext
  intro c
  change B (lp.single 2 g c)=0
  have hs : lp.single 2 g c=c • delta g := by
    simpa [delta] using lp.single_smul (E:=fun _ : G => ℂ) (𝕜:=ℂ) 2 g c (1 : ℂ)
  rw [hs,map_smul,hB g,smul_zero]

omit [MulAction G α] in
theorem root_energy_measurable [Countable G]
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g, Measurable (fun x => matrix (B x) g 1)) :
    Measurable (fun x => ENNReal.ofReal (‖B x (delta 1)‖^2)) := by
  have hm : Measurable (fun x => ∑' g,ENNReal.ofReal (‖matrix (B x) g 1‖^2)) :=
    Measurable.tsum (fun g => ((hB g).norm.pow_const 2).ennreal_ofReal)
  simpa only [matrix,energy_sum] using hm

/-- Faithfulness on squares: zero rooted mass forces every column to
vanish almost everywhere, since every possible root is reached by a
measure-preserving re-rooting. Density then gives the zero operator. -/
theorem trace_gram_faithful [Countable G] {μ : Measure α}
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g, Measurable (fun x => matrix (B x) g 1)) (hc : Covariant B)
    (ht : trace μ (fun x => (B x).adjoint.comp (B x))=0) :
    ∀ᵐ x ∂μ, B x=0 := by
  rw [trace_gram] at ht
  have hz := (lintegral_eq_zero_iff (root_energy_measurable B hB)).mp ht
  have hr : ∀ᵐ x ∂μ, B x (delta 1)=0 := by
    filter_upwards [hz] with x hx
    apply norm_eq_zero.mp
    have he : ‖B x (delta 1)‖^2≤0 := ENNReal.ofReal_eq_zero.mp hx
    nlinarith [norm_nonneg (B x (delta 1))]
  have hall : ∀ᵐ x ∂μ, ∀ h : G, B (h • x) (delta 1)=0 :=
    ae_all_iff.mpr (fun h => (hmp h).quasiMeasurePreserving.ae hr)
  filter_upwards [hall] with x hx
  apply eq_zero_of_columns
  intro h
  apply lp.ext
  funext g
  change matrix (B x) g h=0
  have he := hc x h (g*h⁻¹) 1
  simp only [mul_assoc,inv_mul_cancel,mul_one,one_mul] at he
  rw [← he]
  change B (h • x) (delta 1) (g*h⁻¹)=0
  rw [hx h]
  rfl

omit [MeasurableSpace α] in
theorem covariant_adjoint (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hc : Covariant B) :
    Covariant (fun x => (B x).adjoint) := by
  intro x a g h
  simp only [matrix_adjoint,hc x a h g]

#print axioms energy_sum
#print axioms trace_adjoint_mul
#print axioms rational_trace_adjoint_mul
#print axioms trace_gram_faithful

end AsymptoticRegularTrace
