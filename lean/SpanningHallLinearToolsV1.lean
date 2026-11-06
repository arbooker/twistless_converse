module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SpanningHallLinearTools

open Module

variable {I K V W:Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def IndependentOn (s:Finset I) (v:I → V) : Prop :=
  ∀g:I → K,(∑i∈s,g i • v i)=0 → ∀i∈s,g i=0

theorem independentOn_iff (s:Finset I) (v:I → V) :
    IndependentOn (K:=K) s v ↔ LinearIndepOn K v (s:Set I) := by
  classical
  constructor
  · intro h
    apply linearIndepOn_iff'.mpr
    intro t g hts he i hi
    let a : I → K := fun i => if i∈t then g i else 0
    have ha : (∑i∈s,a i • v i)=0 := by
      calc
        (∑i∈s,a i • v i)=∑i∈t,a i • v i := by
          symm
          apply Finset.sum_subset (show t⊆s from hts)
          intro j _ hj
          simp [a,hj]
        _=∑i∈t,g i • v i := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [a,hj]
        _=0 := he
    simpa [a,hi] using h a ha i (hts hi)
  · intro h g hg
    exact linearIndepOn_iff'.mp h s g (by intro i hi; exact hi) hg

theorem independent_singleton [DecidableEq I] {i:I} {v:I → V} (hv:v i≠0) :
    IndependentOn (K:=K) {i} v := by
  intro g hg j hj
  have hji : j=i := Finset.mem_singleton.mp hj
  subst j
  simp only [Finset.sum_singleton] at hg
  exact (smul_eq_zero.mp hg).resolve_right hv

theorem independent_glue [DecidableEq I] {s t:Finset I} (hd:Disjoint s t)
    (v:I → V) (f:V →ₗ[K] W) (hs:IndependentOn (K:=K) s v)
    (hk:∀i∈s,f (v i)=0) (ht:IndependentOn (K:=K) t (fun i => f (v i))) :
    IndependentOn (K:=K) (s∪t) v := by
  intro g hg
  rw [Finset.sum_union hd] at hg
  have hmap := congrArg f hg
  rw [map_add,map_sum,map_sum,map_zero] at hmap
  simp only [map_smul] at hmap
  have hfirst : (∑i∈s,g i • f (v i))=0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hk i hi,smul_zero])
  rw [hfirst,zero_add] at hmap
  have htzero := ht g hmap
  have hsecond : (∑i∈t,g i • v i)=0 :=
    Finset.sum_eq_zero (fun i hi => by rw [htzero i hi,zero_smul])
  rw [hsecond,add_zero] at hg
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact hs g hg i hi
  · exact htzero i hi

abbrev familySpan (U:I → Submodule K V) (s:Finset I) : Submodule K V := s.sup U

theorem familySpan_mono (U:I → Submodule K V) {s t:Finset I} (h:s⊆t) :
    familySpan U s≤familySpan U t := Finset.sup_mono h

theorem mem_familySpan (U:I → Submodule K V) {s:Finset I} {i:I} (hi:i∈s)
    {v:V} (hv:v∈U i) : v∈familySpan U s :=
  (show U i≤familySpan U s from Finset.le_sup hi) hv

theorem familySpan_map (U:I → Submodule K V) (s:Finset I) (f:V →ₗ[K] W) :
    familySpan (fun i => (U i).map f) s=(familySpan U s).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [familySpan]
  | @insert i s hi ih => simp only [familySpan,Finset.sup_insert,Submodule.map_sup] at *; rw [ih]

theorem quotient_image_dimension [FiniteDimensional K V] (U T:Submodule K V) :
    finrank K (U.map T.mkQ)+finrank K T=finrank K (U⊔T : Submodule K V) := by
  have h1 := T.finrank_quotient_add_finrank
  have h2 := (U.map T.mkQ).finrank_quotient_add_finrank
  have h3 := (T⊔U).finrank_quotient_add_finrank
  have he := (Submodule.quotientQuotientEquivQuotientSup T U).finrank_eq
  rw [he] at h2
  rw [sup_comm T U] at h3 h2
  omega

theorem independent_congr {s:Finset I} {v w:I → V}
    (hv:IndependentOn (K:=K) s v) (he:∀i∈s,w i=v i) : IndependentOn (K:=K) s w := by
  intro g hg
  apply hv g
  have hh : (∑i∈s,g i • w i)=∑i∈s,g i • v i :=
    Finset.sum_congr rfl (fun i hi => by rw [he i hi])
  rwa [hh] at hg

theorem glue_representatives [DecidableEq I] (U:I → Submodule K V)
    (T:Submodule K V) {s t:Finset I} (hd:Disjoint s t)
    (v:I → V) (hv:∀i∈s,v i∈U i) (hvi:IndependentOn (K:=K) s v)
    (hT:∀i∈s,v i∈T) (w:I → V⧸T) (hw:∀i∈t,w i∈(U i).map T.mkQ)
    (hwi:IndependentOn (K:=K) t w) :
    ∃z:I → V,(∀i∈s∪t,z i∈U i) ∧ IndependentOn (K:=K) (s∪t) z := by
  classical
  have hl : ∀i:I,∃x:V,i∈t → x∈U i ∧ T.mkQ x=w i := by
    intro i
    by_cases hi:i∈t
    · obtain ⟨x,hx,he⟩ := Submodule.mem_map.mp (hw i hi)
      exact ⟨x,fun _ => ⟨hx,he⟩⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose z hz using hl
  let out : I → V := fun i => if i∈s then v i else z i
  have hsout : ∀i∈s,out i=v i := fun i hi => ite_eq_left hi
  have htout : ∀i∈t,out i=z i := by
    intro i hi
    exact ite_eq_right (fun hs => Finset.disjoint_left.mp hd hs hi)
  refine ⟨out,?_,?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · rw [hsout i hi]
      exact hv i hi
    · rw [htout i hi]
      exact (hz i hi).1
  · apply independent_glue hd out T.mkQ (independent_congr hvi hsout)
    · intro i hi
      rw [hsout i hi]
      exact (Submodule.Quotient.mk_eq_zero T).mpr (hT i hi)
    · apply independent_congr hwi
      intro i hi
      rw [htout i hi]
      exact (hz i hi).2

#print axioms glue_representatives
#print axioms independentOn_iff
#print axioms quotient_image_dimension

end SpanningHallLinearTools
