module

public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCompactFredholm

open Filter Topology Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The defect of the compact fixed-point equation. -/
def defect (K : X →L[ℂ] X) : X →L[ℂ] X := ContinuousLinearMap.id ℂ X - K

@[simp] theorem defect_apply (K : X →L[ℂ] X) (x : X) : defect K x = x - K x := rfl

theorem mem_ker_defect (K : X →L[ℂ] X) (x : X) :
    x ∈ (defect K).ker ↔ K x = x := by
  change x - K x = 0 ↔ K x = x
  exact sub_eq_zero.trans eq_comm

/-- Compactness makes the fixed-point space finite dimensional. -/
theorem finite_ker {K : X →L[ℂ] X} (hK : IsCompactOperator K) :
    FiniteDimensional ℂ (defect K).ker := by
  let V := (defect K).ker
  have hV (x : V) : K x = x := (mem_ker_defect K x).mp x.property
  have hc := (hK.comp_clm V.subtypeL).codRestrict
    (fun x : V => show K x ∈ V by rw [hV]; exact x.property) (defect K).isClosed_ker
  apply FiniteDimensional.of_isCompactOperator_id (𝕜 := ℂ)
  convert hc using 1
  ext x
  exact (hV x).symm

/-- Once the range is closed, its quotient is finite dimensional: the
quotient map agrees with its composition with the compact operator. -/
theorem finite_coker_of_closed {K : X →L[ℂ] X} (hK : IsCompactOperator K)
    (hc : IsClosed ((defect K).range : Set X)) : (defect K).range.CoFG := by
  let V := (defect K).range
  let : IsClosed (V : Set X) := hc
  have heq (x : X) : V.mkQL (K x) = V.mkQL x := by
    apply sub_eq_zero.mp
    rw [← map_sub, Submodule.mkQL_apply]
    change Submodule.Quotient.mk (K x - x) = (0 : X ⧸ V)
    rw [Submodule.Quotient.mk_eq_zero]
    have hx : x - K x ∈ V := ⟨x, rfl⟩
    simpa only [neg_sub] using V.neg_mem hx
  have hq : IsCompactOperator V.mkQL := by
    convert hK.clm_comp V.mkQL using 1
    ext x
    exact (heq x).symm
  obtain ⟨C, hC, hn⟩ := hq
  have hn' : C ∈ 𝓝 (0 : X ⧸ V) := by
    rw [← map_zero V.mkQL, ← V.isOpenQuotientMap_mkQL.map_nhds_eq]
    exact hn
  exact FiniteDimensional.of_isCompactOperator_id (𝕜 := ℂ) ⟨C, hC, hn'⟩

#print axioms finite_ker
#print axioms finite_coker_of_closed

/-- On any closed subspace disjoint from the fixed points, the defect is
bounded below. Compactness rules out an approximate unit eigenvector. -/
theorem restricted_antilipschitz {K : X →L[ℂ] X} (hK : IsCompactOperator K)
    (V : Submodule ℂ X) (hV : IsClosed (V : Set X))
    (hd : Disjoint (defect K).ker V) :
    ∃ c, AntilipschitzWith c ((defect K).domRestrict V) := by
  let S := (defect K).domRestrict V
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra! h
  have hs : ∃ c > 0, ∀ ε > 0, ∃ x : V,
      ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖S x‖ < ε := by
    obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm ℂ
    refine ⟨‖C‖⁻¹, by positivity, fun ε hε => ?_⟩
    obtain ⟨x, hx⟩ := h ε hε
    have hx0 : x ≠ 0 := by aesop
    obtain ⟨η, hη, h₁, h₂, h₃⟩ := rescale_to_shell hC (ε := 1) (by simp) hx0
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc, hs⟩ := hs
  obtain ⟨φ, _, hφpos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  choose x hxup hxlo hxS using fun n => hs (φ n) (hφpos n)
  have hxS0 : Tendsto (fun n => S (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hxS n).le) hφ
  obtain ⟨C, hC, hCK⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨y, _, ψ, hψ, hψy⟩ := hC.tendsto_subseq
    (x := fun n => K (x n)) (fun n => hCK ⟨x n, by simpa using hxup n, rfl⟩)
  have hxy : Tendsto (fun n => (x (ψ n) : X)) atTop (𝓝 y) := by
    have hh := (hxS0.comp hψ.tendsto_atTop).add hψy
    simpa [S, defect] using hh
  have hyV : y ∈ V := hV.mem_of_tendsto hxy (Eventually.of_forall fun n => (x (ψ n)).property)
  have hyker : y ∈ (defect K).ker := by
    change defect K y = 0
    exact tendsto_nhds_unique ((defect K).continuous.continuousAt.tendsto.comp hxy)
      (hxS0.comp hψ.tendsto_atTop)
  have hy0 : y = 0 := Submodule.disjoint_def.mp hd y hyker hyV
  have hcy : c ≤ ‖y‖ := ge_of_tendsto hxy.norm (Eventually.of_forall fun n => hxlo (ψ n))
  simp [hy0, not_le.mpr hc] at hcy

#print axioms restricted_antilipschitz

variable [CompleteSpace X]

/-- The range of identity minus a compact operator is closed, and the map
is strict. No range or finite-codimension hypothesis is assumed. -/
theorem strict_closed_range {K : X →L[ℂ] X} (hK : IsCompactOperator K) :
    IsStrictMap (defect K) ∧ IsClosed ((defect K).range : Set X) := by
  have := finite_ker hK
  obtain ⟨V, hV⟩ := (Submodule.ClosedComplemented.of_finiteDimensional
    (defect K).ker).exists_isTopCompl
  have : V.CoFG := Submodule.FG.cofg_of_isCompl hV.isCompl .of_finite
  obtain ⟨c, hc⟩ := restricted_antilipschitz hK V hV.isClosed' hV.isCompl.disjoint
  have := hV.isClosed'.completeSpace_coe
  rw [(defect K).isStrictMap_isClosed_range_iff_restrict V hV.isClosed']
  exact ⟨(hc.isEmbedding ((defect K).domRestrict V).continuous).isStrictMap,
    hc.isClosed_range ((defect K).domRestrict V).uniformContinuous⟩

/-- Compact perturbations of the identity are Fredholm on complex Banach
spaces. This supplies actual complements for the reconstruction pencil. -/
theorem isFredholm {K : X →L[ℂ] X} (hK : IsCompactOperator K) :
    (defect K).IsFredholm := by
  have hf := finite_ker hK
  obtain ⟨hs, hr⟩ := strict_closed_range hK
  exact ⟨hs, hr, hf, finite_coker_of_closed hK hr,
    Submodule.ClosedComplemented.of_finiteDimensional _⟩

theorem nonempty_package {K : X →L[ℂ] X} (hK : IsCompactOperator K) :
    Nonempty (defect K).FredholmPackage := (isFredholm hK).nonempty_fredholmPackage

#print axioms strict_closed_range
#print axioms isFredholm
#print axioms nonempty_package

end FinitenessAllLevelCompactFredholm
