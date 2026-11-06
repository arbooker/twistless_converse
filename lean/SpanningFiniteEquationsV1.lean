module

public import SpanningFiniteFieldTransferV1
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

namespace SpanningFiniteEquations

open Matrix

variable {I J K : Type*} [Fintype J] [Field K]

def Equations {R:Type*} [CommRing R] (E : I → J → R) (v : J → R) : Prop :=
  ∀i,dotProduct (E i) v=0

theorem dot_zero_of_mem_span (E : I → J → K) (v:J → K) (hv:Equations E v)
    {x:J → K} (hx:x∈Submodule.span K (Set.range E)) : dotProduct x v=0 := by
  have hle : Submodule.span K (Set.range E)≤LinearMap.ker ((dotProductBilin K K).flip v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hv i
  exact hle hx

theorem functional_coordinates [DecidableEq J] (g:(J → K) →ₗ[K] K) (x:J → K) :
    g x=∑j,x j*g (Pi.single j 1) := by
  have he : (∑j:J,x j • Pi.single j (1:K))=x := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [←he,map_sum]
  simp only [map_smul,smul_eq_mul]

theorem span_top_iff (E:I → J → K) :
    Submodule.span K (Set.range E)=⊤ ↔ ∀v,Equations E v → v=0 := by
  classical
  constructor
  · intro htop v hv
    funext j
    have he := dot_zero_of_mem_span E v hv (x:=Pi.single j 1)
      (by rw [htop]; trivial)
    simpa using he
  · intro hz
    by_contra hnot
    obtain ⟨g,hg,hgle⟩ := (Submodule.span K (Set.range E)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hnot)
    let v : J → K := fun j => g (Pi.single j 1)
    have hv : Equations E v := by
      intro i
      change (∑j,E i j*g (Pi.single j 1))=0
      rw [←functional_coordinates]
      exact hgle (Submodule.subset_span (Set.mem_range_self i))
    have hv0 := hz v hv
    apply hg
    apply LinearMap.ext
    intro x
    rw [functional_coordinates]
    change (∑j,x j*v j)=0
    simp [hv0]

theorem finite_equations (E:I → J → K) (hz:∀v,Equations E v → v=0) :
    ∃s:Finset I,∀v,(∀i∈s,dotProduct (E i) v=0) → v=0 := by
  classical
  have ht := (span_top_iff E).mpr hz
  have hfg : (Submodule.span K (Set.range E)).FG := by
    rw [ht]
    exact Module.finite_def.mp inferInstance
  obtain ⟨t,htsub,hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (Set.range E)).mp hfg
  have he : ∀x:t,∃i:I,E i=x.val := fun x => htsub x.property
  choose e he using he
  let s : Finset I := Finset.univ.image e
  refine ⟨s,?_⟩
  intro v hv
  apply hz v
  intro i
  have hzspan : ∀x∈Submodule.span K (t:Set (J → K)),dotProduct x v=0 := by
    intro x hx
    apply (show Submodule.span K (t:Set (J → K))≤
      LinearMap.ker ((dotProductBilin K K).flip v) from ?_) hx
    apply Submodule.span_le.mpr
    intro x hx
    have hi := hv (e ⟨x,hx⟩) (Finset.mem_image.mpr ⟨⟨x,hx⟩,Finset.mem_univ _,rfl⟩)
    rw [he] at hi
    exact hi
  apply hzspan
  rw [←hspan]
  exact Submodule.subset_span (Set.mem_range_self i)

theorem submatrix_injective (E:I → J → K) (s:Finset I)
    (hz:∀v,(∀i∈s,dotProduct (E i) v=0) → v=0) :
    Function.Injective (fun v:J → K => (fun i:s => dotProduct (E i.val) v)) := by
  intro v w he
  have hh : v-w=0 := hz (v-w) (by
    intro i hi
    rw [dotProduct_sub,sub_eq_zero]
    exact congrFun he ⟨i,hi⟩)
  exact sub_eq_zero.mp hh

theorem integer_system_mod_large_primes {E:I → J → ℤ}
    (hz:∀v:J → ℚ,Equations (fun i j => (E i j:ℚ)) v → v=0) :
    ∃D:ℕ,0<D ∧ ∀p:ℕ,p.Prime → D<p →
      ∀v:J → ZMod p,Equations (fun i j => (E i j:ZMod p)) v → v=0 := by
  classical
  obtain ⟨s,hs⟩ := finite_equations (fun i j => (E i j:ℚ)) hz
  let A : Matrix s J ℤ := fun i j => E i.val j
  have hA : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec :=
    submatrix_injective (fun i j => (E i j:ℚ)) s hs
  obtain ⟨D,hD,hp⟩ := SpanningFiniteFieldTransfer.rational_injective_mod_large_prime A hA
  refine ⟨D,hD,?_⟩
  intro p hprime hlarge v hv
  apply hp p hprime hlarge
  change (fun i:s => dotProduct (fun j => (E i.val j:ZMod p)) v)=
    (A.map (Int.castRingHom (ZMod p))).mulVec 0
  rw [Matrix.mulVec_zero]
  funext i
  exact hv i.val

theorem integer_system_finite_field_rational {E:I → J → ℤ}
    (p:ℕ) [Fact p.Prime]
    (hz:∀v:J → ZMod p,Equations (fun i j => (E i j:ZMod p)) v → v=0) :
    ∀v:J → ℚ,Equations (fun i j => (E i j:ℚ)) v → v=0 := by
  classical
  obtain ⟨s,hs⟩ := finite_equations (fun i j => (E i j:ZMod p)) hz
  let A : Matrix s J ℤ := fun i j => E i.val j
  have hA : Function.Injective (A.map (Int.castRingHom (ZMod p))).mulVec :=
    submatrix_injective (fun i j => (E i j:ZMod p)) s hs
  have hAQ := SpanningFiniteFieldTransfer.finite_field_injective_rational A p hA
  intro v hv
  apply hAQ
  rw [Matrix.mulVec_zero]
  funext i
  exact hv i.val

#print axioms integer_system_mod_large_primes
#print axioms integer_system_finite_field_rational
#print axioms span_top_iff
#print axioms finite_equations

end SpanningFiniteEquations
