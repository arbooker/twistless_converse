module

public import SpanningIntegerRowsV1

@[expose] public section

namespace SpanningAdditionIntegerSystem

open Matrix SpanningFiniteEquations SpanningIntegerRows SpanningCyclicCoordinates
  SpanningActualKernel SpanningTraceAlgebra SpanningSlicedAddition

def family {q B:ℕ} (hB:0<B) {K:Type*} [Zero K] (v:Fin q×Fin B → K) : ℕ → ℤ → K :=
  fun r n => if hr:r<q then v (⟨r,hr⟩,residue hB n) else 0

theorem family_slice {q B:ℕ} (hB:0<B) {K:Type*} [Zero K]
    (v:Fin q×Fin B → K) (r:Fin q) : family hB v r.val=extend hB (fun j => v (r,j)) := by
  funext n
  simp [family,extend,r.isLt]

theorem addition_congr {q B:ℕ} (hq:0<q) {K:Type*} [AddCommMonoid K]
    {w w':ℕ → ℤ → K} (he:∀r<q,w r=w' r) : addition q B w=addition q B w' := by
  funext n
  apply Finset.sum_congr rfl
  intro a _
  have hr : ((n+(a:ℤ)*B)%(q:ℤ)).toNat<q := (residue hq _).isLt
  rw [he _ hr]

def copyRow {q B:ℕ} (r:Fin q) (E:Fin B → ℤ) : Fin q×Fin B → ℤ :=
  fun x => if x.1=r then E x.2 else 0

theorem copyRow_eval {q B:ℕ} {K:Type*} [CommRing K]
    (r:Fin q) (E:Fin B → ℤ) (v:Fin q×Fin B → K) :
    dotProduct (fun x => (copyRow r E x:K)) v=
      dotProduct (fun j => (E j:K)) (fun j => v (r,j)) := by
  classical
  simp [dotProduct,copyRow,Fintype.sum_prod_type]

def additionRow {q B:ℕ} (hq:0<q) (hB:0<B) (n:ℤ) : Fin q×Fin B → ℤ :=
  sumRow (Finset.range q) (fun a => (residue hq (n+(a:ℤ)*B),
    residue hB ((n+(a:ℤ)*B)/(q:ℤ))))

theorem additionRow_eval {q B:ℕ} (hq:0<q) (hB:0<B) {K:Type*} [CommRing K]
    (n:ℤ) (v:Fin q×Fin B → K) :
    dotProduct (fun x => (additionRow hq hB n x:K)) v=addition q B (family hB v) n := by
  rw [additionRow,sumRow_eval]
  apply Finset.sum_congr rfl
  intro a _
  have hr : ((n+(a:ℤ)*B)%(q:ℤ)).toNat<q := (residue hq _).isLt
  simp only [family,dite_eq_left hr]
  rfl

def AdditionIndex (N:ℕ) (L:Set ℕ) (q B:ℕ) := (Fin q×AugIndex N L B) ⊕ ℤ

def additionRows (N:ℕ) (L:Set ℕ) {q B:ℕ} (hq:0<q) (hB:0<B) :
    AdditionIndex N L q B → Fin q×Fin B → ℤ
  | Sum.inl (r,i) => copyRow r (augmentedRows N L hB i)
  | Sum.inr n => additionRow hq hB n

theorem system_iff {N q B:ℕ} {L:Set ℕ} (hq:0<q) (hB:0<B)
    {K:Type*} [CommRing K] (v:Fin q×Fin B → K) :
    Equations (fun i x => (additionRows N L hq hB i x:K)) v ↔
      (∀r<q,Augmented N L B (family hB v r)) ∧ addition q B (family hB v)=0 := by
  constructor
  · intro hv
    constructor
    · intro r hr
      rw [family_slice hB v ⟨r,hr⟩]
      apply (augmented_iff_equations hB _).mpr
      intro i
      exact (copyRow_eval ⟨r,hr⟩ _ v).symm.trans (hv (Sum.inl (⟨r,hr⟩,i)))
    · funext n
      exact (additionRow_eval hq hB n v).symm.trans (hv (Sum.inr n))
  · rintro ⟨hv,ha⟩ i
    cases i with
    | inl x =>
      change dotProduct (fun z => (copyRow x.1 (augmentedRows N L hB x.2) z:K)) v=0
      rw [copyRow_eval]
      have hh := hv x.1.val x.1.isLt
      rw [family_slice] at hh
      exact (augmented_iff_equations hB _).mp hh x.2
    | inr n =>
      change dotProduct (fun z => (additionRow hq hB n z:K)) v=0
      rw [additionRow_eval]
      exact congrFun ha n

theorem addition_injective_iff {N q B:ℕ} {L:Set ℕ} (hq:0<q) (hB:0<B)
    {K:Type*} [CommRing K] :
    AdditionInjective q B {f:ℤ → K | Augmented N L B f} ↔
      ∀v:Fin q×Fin B → K,Equations (fun i x => (additionRows N L hq hB i x:K)) v → v=0 := by
  constructor
  · intro hinj v hv
    obtain ⟨hk,ha⟩ := (system_iff hq hB v).mp hv
    have hz := hinj (family hB v) hk ha
    funext x
    have he := hz x.1.val x.1.isLt
    rw [family_slice] at he
    have hc := congrArg (coordinates (Q:=B)) he
    rw [coordinates_extend] at hc
    exact congrFun hc x.2
  · intro hz w hw ha
    let v : Fin q×Fin B → K := fun x => w x.1.val x.2.val
    have he : ∀r<q,family hB v r=w r := by
      intro r hr
      rw [family_slice hB v ⟨r,hr⟩]
      exact extend_coordinates hB (hw r hr).1.1
    have hv : Equations (fun i x => (additionRows N L hq hB i x:K)) v := by
      apply (system_iff hq hB v).mpr
      constructor
      · intro r hr
        rw [he r hr]
        exact hw r hr
      · rw [addition_congr hq he,ha]
    have hv0 := hz v hv
    intro r hr
    rw [←he r hr,hv0]
    funext n
    simp [family]

theorem addition_injective_mod_large_primes {N q B:ℕ} {L:Set ℕ}
    (hq:0<q) (hB:0<B)
    (hinj:AdditionInjective q B {f:ℤ → ℚ | Augmented N L B f}) :
    ∃D:ℕ,0<D ∧ ∀p:ℕ,p.Prime → D<p →
      AdditionInjective q B {f:ℤ → ZMod p | Augmented N L B f} := by
  obtain ⟨D,hD,hp⟩ := integer_system_mod_large_primes ((addition_injective_iff hq hB).mp hinj)
  exact ⟨D,hD,fun p hprime hlarge =>
    (addition_injective_iff hq hB).mpr (hp p hprime hlarge)⟩

#print axioms addition_injective_iff
#print axioms addition_injective_mod_large_primes

end SpanningAdditionIntegerSystem
