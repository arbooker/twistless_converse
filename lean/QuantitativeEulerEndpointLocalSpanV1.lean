module

public import QuantitativeEulerEndpointFrickeV1
public import AsymptoticAtkinLehnerOldTraceV1
public import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerDiamondDecode AsymptoticCongruenceStrip
open AsymptoticCongruenceLabels AsymptoticOrbitDecode AsymptoticAtkinLehner
open AsymptoticReconstructionBranch AsymptoticFreshMatrices
open scoped Classical

/-- The original ramified residual in the finite projective group algebra. -/
def ramifiedRow (p : ℕ) (hp : 0<p) (δ : ℂ) : Ring :=
  (∑ a : Fin p, symbol (ramifiedLabel p hp a))-δ • 1

abbrev LocalRowIndex (N : ℕ) := gamma N ⊕ Fin 2

def localObservationRow (N p : ℕ) (hN : 0<N) (hp : 0<p) (w δ : ℂ) :
    LocalRowIndex N → Ring
  | .inl γ => symbol γ.val-1
  | .inr i => if i=0 then frickeRow N hN w else ramifiedRow p hp δ

def localTranslatedRow (N p : ℕ) (hN : 0<N) (hp : 0<p) (w δ : ℂ)
    (i : LocalRowIndex N × G) : Ring :=
  localObservationRow N p hN hp w δ i.1*symbol i.2

def localRowSpan (N p : ℕ) (hN : 0<N) (hp : 0<p) (w δ : ℂ) : Subspace ℂ Ring :=
  Submodule.span ℂ (Set.range (localTranslatedRow N p hN hp w δ))

/-- The literal simple-prime trace, with its identity coset included. -/
def simpleTraceRow (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : Ring :=
  1+∑ a : Fin p, symbol (integralLabel (traceSL M p A B hAB a.val))

/-- Algebraic separation converts the exact vanishing theorem on ALL
coordinate functions into finite span membership. No Hilbert-space closure,
newness hypothesis, or unproved stability estimate is used. -/
theorem simpleTraceRow_mem_localRowSpan (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (w δ : ℂ) (hδ : δ^2=1) :
    simpleTraceRow M p A B hAB ∈
      localRowSpan (p*M) p (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (Fact.out : p.Prime).pos w δ := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
  intro φ hφ
  have hz (i : LocalRowIndex (p*M) × G) :
      φ (localTranslatedRow (p*M) p (Nat.mul_pos (Fact.out : p.Prime).pos hM)
        (Fact.out : p.Prime).pos w δ i)=0 :=
    (Submodule.mem_dualAnnihilator φ).mp hφ _ (Submodule.subset_span ⟨i,rfl⟩)
  let F : G → ℂ := fun g => φ (symbol g)
  have hF (a : gamma (p*M)) (g : G) : F (a.val*g)=F g := by
    have h := hz (.inl a,g)
    simpa [localTranslatedRow,localObservationRow,sub_mul,←map_mul,F] using
      sub_eq_zero.mp (show φ (symbol (a.val*g))-φ (symbol g)=0 by
        simpa [localTranslatedRow,localObservationRow,sub_mul,←map_mul] using h)
  have hW (g : G) :
      w*F (frickeLabel (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)*g)=F g := by
    have h := hz (.inr 0,g)
    have he : F g-w*F (frickeLabel (p*M)
        (Nat.mul_pos (Fact.out : p.Prime).pos hM)*g)=0 := by
      simpa [localTranslatedRow,localObservationRow,frickeRow,sub_mul,
        smul_mul_assoc,←map_mul,F] using h
    exact (sub_eq_zero.mp he).symm
  have hU (g : G) :
      ∑ a : Fin p, F (ramifiedLabel p (Fact.out : p.Prime).pos a*g)=δ*F g := by
    have h := hz (.inr 1,g)
    apply sub_eq_zero.mp
    simpa [localTranslatedRow,localObservationRow,ramifiedRow,sub_mul,
      Finset.sum_mul,smul_mul_assoc,←map_mul,F] using h
  have h := old_trace_zero M p hM hpM A B hAB F hF w δ hδ hW hU 1
  simpa [simpleTraceRow,F] using h

/-- A finite certificate exists before any compact region, cutoff, weight,
point or vector is chosen. Its coefficients depend only on the local data. -/
theorem simpleTraceRow_certificate (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (w δ : ℂ) (hδ : δ^2=1) :
    ∃ c : (LocalRowIndex (p*M) × G) →₀ ℂ,
      (c.sum fun i a => a • localTranslatedRow (p*M) p
        (Nat.mul_pos (Fact.out : p.Prime).pos hM) (Fact.out : p.Prime).pos w δ i)=
        simpleTraceRow M p A B hAB := by
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp
    (simpleTraceRow_mem_localRowSpan M p hM hpM A B hAB w δ hδ)

#print axioms simpleTraceRow_mem_localRowSpan
#print axioms simpleTraceRow_certificate
end QuantitativeEulerEndpointPrepared
