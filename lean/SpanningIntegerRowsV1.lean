module

public import SpanningFiniteEquationsV1
public import SpanningLinearKernelsV1

@[expose] public section

namespace SpanningIntegerRows

open Matrix SpanningFiniteEquations SpanningCyclicCoordinates SpanningActualKernel
  SpanningTraceAlgebra SpanningWindows

def sumRow {T J:Type*} [DecidableEq J] (s:Finset T) (idx:T → J) : J → ℤ :=
  ∑a∈s,Pi.single (idx a) 1

theorem sumRow_eval {T J K:Type*} [Fintype J] [DecidableEq J] [CommRing K]
    (s:Finset T) (idx:T → J) (v:J → K) :
    dotProduct (fun j => (sumRow s idx j:K)) v=∑a∈s,v (idx a) := by
  classical
  unfold dotProduct sumRow
  simp only [Finset.sum_apply,Int.cast_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [Pi.single_apply]

def traceRow {Q:ℕ} (hQ:0<Q) (q B:ℕ) (u:ℤ) : Fin Q → ℤ :=
  sumRow (Finset.range q) (fun a => residue hQ (u+(a:ℤ)*B))

theorem traceRow_eval {Q:ℕ} (hQ:0<Q) {K:Type*} [CommRing K]
    (q B:ℕ) (u:ℤ) (v:Fin Q → K) :
    dotProduct (fun j => (traceRow hQ q B u j:K)) v=
      trace q B (extend hQ v) u := by
  exact sumRow_eval _ _ v

def RowIndex (N Q:ℕ) := {qu:ℕ×ℤ // qu.1∣Q ∧ Legal (radius N Q qu.1) qu.2}
def AugIndex (N:ℕ) (L:Set ℕ) (Q:ℕ) := RowIndex N Q ⊕ ({ell:ℕ // ell∈L}×ℤ)

def augmentedRows (N:ℕ) (L:Set ℕ) {Q:ℕ} (hQ:0<Q) : AugIndex N L Q → Fin Q → ℤ
  | Sum.inl x => traceRow hQ x.val.1 (Q/x.val.1) x.val.2
  | Sum.inr x => traceRow hQ x.1.val (Q/x.1.val) x.2

theorem augmented_iff_equations {N Q:ℕ} {L:Set ℕ} (hQ:0<Q)
    {K:Type*} [CommRing K] (v:Fin Q → K) :
    Augmented N L Q (extend hQ v) ↔
      Equations (fun i j => (augmentedRows N L hQ i j:K)) v := by
  constructor
  · intro hv i
    cases i with
    | inl x =>
      change dotProduct (fun j => (traceRow hQ x.val.1 (Q/x.val.1) x.val.2 j:K)) v=0
      rw [traceRow_eval]
      exact hv.1.2 _ x.property.1 _ x.property.2
    | inr x =>
      change dotProduct (fun j => (traceRow hQ x.1.val (Q/x.1.val) x.2 j:K)) v=0
      rw [traceRow_eval]
      exact congrFun (hv.2 x.1.val x.1.property) x.2
  · intro hv
    refine ⟨⟨extend_cyclic hQ v,?_⟩,?_⟩
    · intro q hq u hu
      exact (traceRow_eval hQ q (Q/q) u v).symm.trans (hv (Sum.inl ⟨(q,u),hq,hu⟩))
    · intro ell hell
      funext u
      exact (traceRow_eval hQ ell (Q/ell) u v).symm.trans
        (hv (Sum.inr (⟨ell,hell⟩,u)))

theorem augmented_zero_iff {N Q:ℕ} {L:Set ℕ} (hQ:0<Q)
    {K:Type*} [CommRing K] :
    (∀f:ℤ → K,Augmented N L Q f → f=0) ↔
      (∀v:Fin Q → K,Equations (fun i j => (augmentedRows N L hQ i j:K)) v → v=0) := by
  constructor
  · intro hz v hv
    have he := hz (extend hQ v) ((augmented_iff_equations hQ v).mpr hv)
    have hc := congrArg (coordinates (Q:=Q)) he
    rw [coordinates_extend] at hc
    exact hc
  · intro hz f hf
    have he := extend_coordinates hQ hf.1.1
    have hv := hz (coordinates f) ((augmented_iff_equations hQ _).mp (by rw [he]; exact hf))
    rw [←he,hv]
    rfl

theorem augmented_zero_mod_large_primes {N Q:ℕ} {L:Set ℕ} (hQ:0<Q)
    (hz:∀f:ℤ → ℚ,Augmented N L Q f → f=0) :
    ∃D:ℕ,0<D ∧ ∀p:ℕ,p.Prime → D<p →
      ∀f:ℤ → ZMod p,Augmented N L Q f → f=0 := by
  obtain ⟨D,hD,hp⟩ := integer_system_mod_large_primes ((augmented_zero_iff hQ).mp hz)
  exact ⟨D,hD,fun p hprime hlarge => (augmented_zero_iff hQ).mpr (hp p hprime hlarge)⟩

theorem augmented_zero_finite_field_rational {N Q:ℕ} {L:Set ℕ} (hQ:0<Q)
    (p:ℕ) [Fact p.Prime] (hz:∀f:ℤ → ZMod p,Augmented N L Q f → f=0) :
    ∀f:ℤ → ℚ,Augmented N L Q f → f=0 := by
  apply (augmented_zero_iff hQ).mpr
  exact integer_system_finite_field_rational p ((augmented_zero_iff hQ).mp hz)

def primitiveRow {Q:ℕ} (hQ:0<Q) (q B:ℕ) (u:ℤ) : Fin Q → ℤ :=
  sumRow ((Finset.range q).filter (fun a => Nat.Coprime a q))
    (fun a => residue hQ (u+(a:ℤ)*B))

theorem primitiveRow_eval {Q:ℕ} (hQ:0<Q) {K:Type*} [CommRing K]
    (q B:ℕ) (u:ℤ) (v:Fin Q → K) :
    dotProduct (fun j => (primitiveRow hQ q B u j:K)) v=
      primitive q B (extend hQ v) u := sumRow_eval _ _ v

def primitiveRows (N:ℕ) {Q:ℕ} (hQ:0<Q) : RowIndex N Q → Fin Q → ℤ :=
  fun x => primitiveRow hQ x.val.1 (Q/x.val.1) x.val.2

theorem primitive_iff_equations {N Q:ℕ} (hQ:0<Q)
    {K:Type*} [CommRing K] (v:Fin Q → K) :
    Kernel N Q (extend hQ v) ↔ Equations (fun i j => (primitiveRows N hQ i j:K)) v := by
  constructor
  · intro hv i
    change dotProduct (fun j => (primitiveRow hQ i.val.1 (Q/i.val.1) i.val.2 j:K)) v=0
    rw [primitiveRow_eval]
    exact hv.2 _ i.property.1 _ i.property.2
  · intro hv
    refine ⟨extend_cyclic hQ v,?_⟩
    intro q hq u hu
    exact (primitiveRow_eval hQ q (Q/q) u v).symm.trans (hv ⟨(q,u),hq,hu⟩)

theorem primitive_zero_iff {N Q:ℕ} (hQ:0<Q) {K:Type*} [CommRing K] :
    (∀f:ℤ → K,Kernel N Q f → f=0) ↔
      (∀v:Fin Q → K,Equations (fun i j => (primitiveRows N hQ i j:K)) v → v=0) := by
  constructor
  · intro hz v hv
    have he := hz (extend hQ v) ((primitive_iff_equations hQ v).mpr hv)
    have hc := congrArg (coordinates (Q:=Q)) he
    rw [coordinates_extend] at hc
    exact hc
  · intro hz f hf
    have he := extend_coordinates hQ hf.1
    have hv := hz (coordinates f) ((primitive_iff_equations hQ _).mp (by rw [he]; exact hf))
    rw [←he,hv]
    rfl

theorem primitive_span_top_iff {N Q:ℕ} (hQ:0<Q) {K:Type*} [Field K] :
    Submodule.span K (Set.range (fun i j => (primitiveRows N hQ i j:K)))=⊤ ↔
      (∀f:ℤ → K,Kernel N Q f → f=0) := by
  rw [SpanningFiniteEquations.span_top_iff,primitive_zero_iff hQ]

#print axioms primitive_span_top_iff
#print axioms augmented_iff_equations
#print axioms augmented_zero_finite_field_rational

end SpanningIntegerRows
