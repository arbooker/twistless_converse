module

public import QuantitativeMaassWaveGeneratorIdentificationV1
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous functional calculus acts on a genuine eigenvector by evaluation.
The proof uses polynomial density on the actual compact spectrum. -/
theorem cfcHom_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (s : spectrum ℝ A) (v : H) (hv : A v=(s:ℝ) • v)
    (f : C(spectrum ℝ A,ℝ)) : cfcHom hA f v=f s • v := by
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    change (cfcHom hA (algebraMap ℝ _ r)) v=r • v
    rw [AlgHomClass.commutes]
    simp
  | id => simpa only [cfcHom_id,ContinuousMap.restrict_apply,ContinuousMap.id_apply] using hv
  | star_id =>
    simpa only [star_trivial,cfcHom_id,ContinuousMap.restrict_apply,ContinuousMap.id_apply] using hv
  | add f g hf hg =>
    rw [map_add,add_apply,hf,hg]
    exact (add_smul (f s) (g s) v).symm
  | mul f g hf hg =>
    rw [map_mul]
    change cfcHom hA f (cfcHom hA g v)=(f s*g s) • v
    rw [hg,← algebraMap_smul ℂ (g s),map_smul,hf,algebraMap_smul,smul_smul,mul_comm]
  | frequently f hf =>
    have hc : IsClosed {g : C(spectrum ℝ A,ℝ) | cfcHom hA g v=g s • v} :=
      isClosed_eq ((ContinuousLinearMap.apply ℂ H v).continuous.comp (cfcHom_continuous hA))
        (by fun_prop)
    change f ∈ {g : C(spectrum ℝ A,ℝ) | cfcHom hA g v=g s • v}
    rw [← hc.closure_eq]
    exact mem_closure_of_frequently_of_tendsto hf tendsto_id

theorem eigen_mem_spectrum (A : H →L[ℂ] H) {s : ℝ} {v : H}
    (hv : A v=s • v) (hn : v≠0) : s∈spectrum ℝ A := by
  intro hu
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).injective
  apply hn
  apply hi
  simp only [sub_apply,map_zero,hv,Algebra.algebraMap_eq_smul_one,smul_apply,
    one_apply_eq_self,sub_self]

theorem cfc_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {s : ℝ} {v : H} (hv : A v=s • v) (f : ℝ→ℝ) (hf : Continuous f) :
    cfc f A v=f s • v := by
  by_cases hn : v=0
  · simp [hn]
  · rw [cfc_apply f A hA hf.continuousOn]
    exact cfcHom_eigen A hA ⟨s,eigen_mem_spectrum A hv hn⟩ v hv
      ⟨_,hf.comp continuous_subtype_val⟩

/-- Exact wave eigenaction, derived from the actual resolvent-range
construction and continuous calculus, rather than assumed spectrally. -/
theorem rangeCosine_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) {s : ℝ} (hs : s≠0) {v : H} (hv : A v=s • v) (t : ℝ) :
    rangeCosine A t v=Real.cos (t*Real.sqrt (s⁻¹-1)) • v := by
  have he := rangeCosine_range A hA hd t v
  change rangeCosine A t (A v)=cfc (dampedCosine t) A v at he
  rw [cfc_eigen A hA hv _ (dampedCosine_continuous t),hv,
    ← algebraMap_smul ℂ s,map_smul,algebraMap_smul] at he
  have he' := congrArg (fun w : H => s⁻¹ • w) he
  simpa [dampedCosine,smul_smul,hs] using he'

omit [CompleteSpace H] in
theorem inverse_eigen_of_graph (A : H →L[ℂ] H) {e : ℝ} (he : 0≤e)
    {v : H} (h : A (v+e • v)=v) : A v=(1+e)⁻¹ • v := by
  have hn : 1+e≠0 := by positivity
  have he : (1+e) • A v=v := by
    rw [← algebraMap_smul ℂ (1+e),← map_smul,algebraMap_smul,add_smul,one_smul]
    exact h
  have he' := congrArg (fun w : H => (1+e)⁻¹ • w) he
  simpa [smul_smul,hn] using he'

theorem rangeCosine_graph_eigen (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) {e : ℝ} (he : 0≤e) {v : H}
    (h : A (v+e • v)=v) (t : ℝ) :
    rangeCosine A t v=Real.cos (t*Real.sqrt e) • v := by
  have hn : (1+e)⁻¹≠0 := inv_ne_zero (by positivity)
  have he := rangeCosine_eigen A hA hd hn (inverse_eigen_of_graph A he h) t
  simpa only [inv_inv,add_sub_cancel_left] using he

theorem rangeCosine_graph_eigen_complex (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) {e : ℝ} (he : 0≤e) {v : H}
    (h : A (v+(e:ℂ) • v)=v) (t : ℝ) :
    rangeCosine A t v=(Real.cos (t*Real.sqrt e):ℂ) • v := by
  have h' : A (v+e • v)=v := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal] using h
  have hh := rangeCosine_graph_eigen A hA hd he h' t
  simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal] using hh

/-- Actual unshifted quotient wave action on a Friedrichs Laplacian
 eigenpair. Operator-domain membership is retained explicitly. -/
theorem quotientWave_eigen (N : ℕ) {e : ℝ} (he : 0≤e)
    {v : AutomorphicSpace N} (h : FriedrichsGraph N v ((e:ℂ) • v)) (t : ℝ) :
    quotientWave N t v=(Real.cos (t*Real.sqrt e):ℂ) • v :=
  rangeCosine_graph_eigen_complex (friedrichsResolvent N)
    (friedrichsResolvent_isSelfAdjoint N) (friedrichsResolvent_denseRange N) he h t

#print axioms cfcHom_eigen
#print axioms cfc_eigen
#print axioms rangeCosine_eigen
#print axioms quotientWave_eigen

end QuantitativeMaass.Wave
