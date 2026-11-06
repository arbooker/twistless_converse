module

public import SpanningFailurePolynomialsV1
public import SpanningShiftFieldExtensionV1

@[expose] public section

namespace SpanningFailureDimensionDrop

open scoped BigOperators
open Module SpanningTraceAlgebra SpanningAdditionFailure SpanningFailurePolynomials
  SpanningCRTExponents SpanningPolynomialDeterminants SpanningHallLinearTools

theorem dimension_drop {K K' I:Type*} [Field K] [Field K'] [Fintype I] [DecidableEq I]
    {B L:ℕ} {ζ:K'} (σ:K→+*K') (hB:0<B) (hζ:IsPrimitiveRoot ζ B)
    (V:Submodule K (ℤ→K)) [FiniteDimensional K V]
    (hdim:finrank K V=Fintype.card I) (hpos:0<finrank K V)
    (hcyc:∀v∈V,Cyclic B v) (hzero:∀v∈V,∀n:ℕ,n<L→v n=0)
    (c:I→ℕ) (_hcpos:∀i,0<c i) (hcB:∀i,Nat.Coprime (c i) B)
    (hcp:Pairwise (fun i j => Nat.Coprime (c i) (c j)))
    (hsize:Fintype.card I*(∏i,c i)≤L) (hfail:∀i,ShiftFailure B (c i) V) :
    ∃W:Submodule K (ℤ→K),W≤V ∧
      0<finrank K W ∧ finrank K W<finrank K V ∧
      ∃s:Finset I,finrank K W<s.card ∧ ∀i∈s,ShiftFailure B (c i) W := by
  classical
  let e : (I→K)≃ₗ[K]V := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi,hdim])
  simp only [ShiftFailure] at hfail
  choose t ht v hn hv using hfail
  have hprodB : Nat.Coprime (∏i,c i) B := Nat.Coprime.prod_left (fun i _ => hcB i)
  obtain ⟨u,hu⟩ := negative_inverse_exists hB hprodB
  let a : ∀i,Fin (c i)→I→K := fun i r => e.symm (v i r)
  let w : ∀i,Fin (c i)→ℕ := fun i r => r.val*weight c i
  let F := polynomialRows a w
  let f : I→ℤ→K := fun i => e (Pi.single i 1)
  have hrel : ∀j,(∑i,SpanningPolynomialShift.shiftPolynomial (F j i) u (f i))=0 :=
    relation_in_coordinates e c hcB u hu hcyc t ht v hv
  have hI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let i0 : I := Classical.choice hI
  have hf0 : f i0≠0 := by
    intro he
    have he' : e (Pi.single i0 1)=0 := Subtype.ext he
    have hs := e.injective (he'.trans (e.map_zero).symm)
    have hh := congrFun hs i0
    simp at hh
  have hdet : F.det=0 := SpanningShiftFieldExtension.determinant_zero_over_extension σ hB hζ F u
    (negative_inverse_coprime hu) f (fun i => hcyc _ (e (Pi.single i 1)).property)
    hrel i0 hf0 L (hzero _ (e (Pi.single i0 1)).property)
    (determinant_degree_bound a w L (fun j => (exponent_bound c j).trans hsize))
  have hm := mixed_determinants_zero a w (exponent_injective c hcp) hdet
  obtain ⟨s,hs,hr⟩ := SpanningMixedDeterminants.obstruction_of_mixed_determinants a hm
  let U := familySpan (fun i => Submodule.span K (Set.range (a i))) s
  let g : (I→K)→ₗ[K](ℤ→K) := V.subtype.comp e.toLinearMap
  have hgi : Function.Injective g := Subtype.val_injective.comp e.injective
  let W := U.map g
  have hWrank : finrank K W=finrank K U :=
    (Submodule.equivMapOfInjective g hgi U).finrank_eq.symm
  have hmem : ∀i∈s,∀r,(v i r:ℤ→K)∈W := by
    intro i hi r
    refine ⟨a i r,mem_familySpan _ hi (Submodule.subset_span ⟨r,rfl⟩),?_⟩
    change (e (e.symm (v i r)):ℤ→K)=(v i r:ℤ→K)
    rw [e.apply_symm_apply]
  have hWle : W≤V := by
    rintro x ⟨y,_,rfl⟩
    exact (e y).property
  have hfinite : FiniteDimensional K W := Module.Finite.of_injective
    (Submodule.inclusion hWle) (Submodule.inclusion_injective hWle)
  let := hfinite
  have hWpos : 0<finrank K W := by
    obtain ⟨i,hi⟩ := hs
    obtain ⟨r,hnr⟩ := hn i
    apply Module.finrank_pos_iff.mpr
    apply nontrivial_of_ne (⟨(v i r:ℤ→K),hmem i hi r⟩:W) 0
    intro he
    apply hnr
    exact Subtype.ext (congrArg (fun x:W => (x:ℤ→K)) he)
  refine ⟨W,hWle,hWpos,?_,s,?_,?_⟩
  · rw [hWrank,hdim]
    exact hr.trans_le (Finset.card_le_univ s)
  · rwa [hWrank]
  · intro i hi
    refine ⟨t i,ht i,(fun r => ⟨(v i r:ℤ→K),hmem i hi r⟩),?_,hv i⟩
    obtain ⟨r,hnr⟩ := hn i
    refine ⟨r,?_⟩
    intro he
    exact hnr (Subtype.ext (congrArg (fun x:W => (x:ℤ→K)) he))

#print axioms dimension_drop

end SpanningFailureDimensionDrop
