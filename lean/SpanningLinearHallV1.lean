module

public import SpanningHallLinearToolsV1

@[expose] public section

namespace SpanningLinearHall

open Module SpanningHallLinearTools

variable {I K:Type*} [Field K]

def Hall {V:Type*} [AddCommGroup V] [Module K V] (s:Finset I) (U:I → Submodule K V) : Prop :=
  ∀t:Finset I,t⊆s → t.card≤finrank K (familySpan U t)

theorem exists_representatives (V:Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (s:Finset I) (U:I → Submodule K V) (hh:Hall s U) :
    ∃v:I → V,(∀i∈s,v i∈U i) ∧ IndependentOn (K:=K) s v := by
  classical
  by_cases hs:s=∅
  · subst s
    exact ⟨fun _ => 0,by simp,by intro g _ i hi; simp at hi⟩
  by_cases htight:∃t:Finset I,t.Nonempty ∧ t⊂s ∧ finrank K (familySpan U t)=t.card
  · obtain ⟨t,htne,hts,htrank⟩ := htight
    have hthall : Hall t U := fun R hR => hh R (hR.trans hts.subset)
    obtain ⟨v,hv,hvi⟩ := exists_representatives V t U hthall
    let W := familySpan U t
    have hcomp : s\t⊂s := by
      refine ⟨Finset.sdiff_subset,?_⟩
      intro he
      obtain ⟨i,hi⟩ := htne
      have hmem : i∈s\t := he (hts.subset hi)
      exact (Finset.mem_sdiff.mp hmem).2 hi
    have hqhall : Hall (s\t) (fun i => (U i).map W.mkQ) := by
      intro R hR
      have hdis : Disjoint R t := by
        apply Finset.disjoint_left.mpr
        intro i hi hit
        exact (Finset.mem_sdiff.mp (hR hi)).2 hit
      have hsubset : R∪t⊆s := Finset.union_subset
        (hR.trans Finset.sdiff_subset) hts.subset
      have hr := hh (R∪t) hsubset
      rw [Finset.card_union_of_disjoint hdis] at hr
      have he := quotient_image_dimension (familySpan U R) W
      have hun : familySpan U (R∪t)=familySpan U R⊔W := Finset.sup_union
      rw [hun] at hr
      rw [familySpan_map]
      change finrank K W=t.card at htrank
      omega
    obtain ⟨w,hw,hwi⟩ := exists_representatives (V⧸W) (s\t) (fun i => (U i).map W.mkQ) hqhall
    have hdis : Disjoint t (s\t) :=
      Finset.disjoint_left.mpr (fun _ ht hst => (Finset.mem_sdiff.mp hst).2 ht)
    obtain ⟨z,hz,hzi⟩ := glue_representatives U W hdis v hv hvi
      (fun i hi => mem_familySpan U hi (hv i hi)) w hw hwi
    rw [Finset.union_sdiff_of_subset hts.subset] at hz hzi
    exact ⟨z,hz,hzi⟩
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hu : U i≠⊥ := by
      have hdim := hh {i} (Finset.singleton_subset_iff.mpr hi)
      have hsingle : familySpan U {i}=U i := Finset.sup_singleton
      rw [Finset.card_singleton,hsingle] at hdim
      intro he
      rw [he,finrank_bot] at hdim
      omega
    obtain ⟨v0,hv0,hvnonzero⟩ := (U i).ne_bot_iff.mp hu
    let W : Submodule K V := Submodule.span K {v0}
    have hW : finrank K W=1 := finrank_span_singleton hvnonzero
    have herase : s.erase i⊂s := Finset.erase_ssubset hi
    have hqhall : Hall (s.erase i) (fun j => (U j).map W.mkQ) := by
      intro R hR
      by_cases hRe:R=∅
      · subst R
        simp [familySpan]
      have hRs : R⊂s := by
        refine ⟨hR.trans (Finset.erase_subset _ _),?_⟩
        intro he
        have hmem := hR (he hi)
        exact (Finset.mem_erase.mp hmem).1 rfl
      have hdim := hh R hRs.subset
      have hneq : finrank K (familySpan U R)≠R.card := by
        intro he
        exact htight ⟨R,Finset.nonempty_iff_ne_empty.mpr hRe,hRs,he⟩
      have hstrict : R.card<finrank K (familySpan U R) := by omega
      have he := quotient_image_dimension (familySpan U R) W
      have hmono : finrank K (familySpan U R)≤finrank K (familySpan U R⊔W : Submodule K V) :=
        Submodule.finrank_mono le_sup_left
      rw [familySpan_map]
      omega
    obtain ⟨w,hw,hwi⟩ := exists_representatives (V⧸W) (s.erase i) (fun j => (U j).map W.mkQ) hqhall
    have hdis : Disjoint ({i}:Finset I) (s.erase i) := by simp
    obtain ⟨z,hz,hzi⟩ := glue_representatives U W hdis (fun _ => v0)
      (by intro j hj; have he := Finset.mem_singleton.mp hj; subst j; exact hv0)
      (independent_singleton hvnonzero)
      (by intro j _; exact Submodule.subset_span (Set.mem_singleton v0)) w hw hwi
    have he : ({i}:Finset I)∪s.erase i=s := by simp [Finset.insert_erase hi]
    rw [he] at hz hzi
    exact ⟨z,hz,hzi⟩
termination_by s.card
decreasing_by all_goals apply Finset.card_lt_card; assumption

theorem exists_obstruction [Fintype I] {V:Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U:I → Submodule K V)
    (hno:∀v:I → V,(∀i,v i∈U i) → ¬LinearIndependent K v) :
    ∃s:Finset I,s.Nonempty ∧ finrank K (familySpan U s)<s.card := by
  classical
  have hnot : ¬Hall Finset.univ U := by
    intro hh
    obtain ⟨v,hv,hi⟩ := exists_representatives V Finset.univ U hh
    have hli := (independentOn_iff Finset.univ v).mp hi
    have hli' : LinearIndependent K v := by simpa using hli
    exact hno v (fun i => hv i (Finset.mem_univ i)) hli'
  unfold Hall at hnot
  push Not at hnot
  obtain ⟨s,_,hs⟩ := hnot
  refine ⟨s,?_,hs⟩
  by_contra he
  have hz : s=∅ := Finset.not_nonempty_iff_eq_empty.mp he
  simp [hz,familySpan] at hs

#print axioms exists_obstruction
#print axioms exists_representatives

end SpanningLinearHall
