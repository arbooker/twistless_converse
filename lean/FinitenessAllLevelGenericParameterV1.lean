module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Data.Finsupp.Encodable

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelGenericParameter

open Complex Set Filter
open scoped Topology

/-- A nonzero holomorphic function on a connected planar domain has only
countably many zeros there. -/
theorem zeros_countable {U : Set ℂ} (hU : IsPreconnected U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hne : ¬ EqOn f 0 U) :
    {z | z ∈ U ∧ f z = 0}.Countable := by
  have hd := (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hU).resolve_left hne
  have hc : ({z | f z ≠ 0}ᶜ ∩ U).Countable := by
    apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (isDiscrete_of_codiscreteWithin _)
    simpa using! hd
  convert hc using 1
  ext z
  simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_not, and_comm]

/-- Simultaneously avoid accidental zeros in any countable holomorphic
family. The good parameters are dense in the given domain. -/
theorem generic_parameter {ι : Type*} [Countable ι] {U : Set ℂ}
    (hU : IsPreconnected U) (f : ι → ℂ → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) U) {V : Set ℂ}
    (hV : IsOpen V) (hVU : V ⊆ U) (hne : V.Nonempty) :
    ∃ w ∈ V, ∀ i, f i w = 0 → EqOn (f i) 0 U := by
  classical
  let bad : ι → Set ℂ := fun i => if EqOn (f i) 0 U then ∅ else {z | z ∈ U ∧ f i z = 0}
  have hb (i : ι) : (bad i).Countable := by
    dsimp [bad]
    split_ifs with h
    · exact countable_empty
    · exact zeros_countable hU (hf i) h
  have hd : Dense (⋃ i, bad i)ᶜ := (countable_iUnion hb).dense_compl ℂ
  obtain ⟨w, hwV, hwbad⟩ := hd.inter_open_nonempty V hV hne
  refine ⟨w, hwV, fun i hi => ?_⟩
  by_contra h
  apply hwbad
  exact mem_iUnion.mpr ⟨i, by simpa only [bad, ite_eq_right h, mem_ofPred_eq] using And.intro (hVU hwV) hi⟩

/-- There is a parameter at which every rational polynomial relation among
countably many holomorphic coefficient functions is already an identity on
the entire connected domain. This is a genuine specialization theorem. -/
theorem generic_polynomial_relations {ι : Type*} [Countable ι] {U : Set ℂ}
    (hU : IsPreconnected U) (g : ι → ℂ → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) {V : Set ℂ}
    (hV : IsOpen V) (hVU : V ⊆ U) (hne : V.Nonempty) :
    ∃ w ∈ V, ∀ p : MvPolynomial ι ℚ,
      MvPolynomial.aeval (fun i => g i w) p = 0 →
        ∀ z ∈ U, MvPolynomial.aeval (fun i => g i z) p = 0 := by
  refine generic_parameter hU (fun p z => MvPolynomial.aeval (fun i => g i z) p)
    (fun p z hz => ?_) hV hVU hne
  exact AnalyticAt.aeval_mvPolynomial (fun i => hg i z hz) p

#print axioms zeros_countable
#print axioms generic_parameter
#print axioms generic_polynomial_relations

end FinitenessAllLevelGenericParameter
