module

public import QuantitativeEulerEndpointLocalControlAlgebraV1
public import QuantitativeNewGapSectorIncidenceV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerDiamondDecode AsymptoticCongruenceStrip
open AsymptoticCongruenceLabels AsymptoticOrbitDecode AsymptoticAtkinLehner
open AsymptoticReconstructionBranch AsymptoticFreshMatrices
open scoped Classical

def localSignRow (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (δ : ℂ) : Ring :=
  symbol (localAtkin M p hM hp A B hAB)+δ • 1

/-- The canonical local Atkin sign residual has a finite certificate in
original congruence, Fricke and ramified rows, before analytic parameters. -/
theorem localSignRow_mem_localRowSpan (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (w δ : ℂ) (hδ : δ^2=1) :
    localSignRow M p hM (Fact.out : p.Prime).pos A B hAB δ ∈
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
  have h := local_eigen M p hM hpM A B hAB F hF w δ hδ hW hU 1
  have he : F (localAtkin M p hM (Fact.out : p.Prime).pos A B hAB)+δ*F 1=0 := by
    simpa only [mul_one,neg_mul,add_eq_zero_iff_eq_neg] using h
  simpa [localSignRow,F] using he

theorem globalSignRow_mem_localRowSpan (N p : ℕ) (hN : 0<N) (hp : 0<p)
    (w δ : ℂ) (hw : w*w=1) :
    symbol (frickeLabel N hN)-w • 1∈localRowSpan N p hN hp w δ := by
  have hm : frickeRow N hN w∈localRowSpan N p hN hp w δ := by
    have h := Submodule.subset_span (R:=ℂ)
      (show localTranslatedRow N p hN hp w δ (.inr 0,1)∈
        Set.range (localTranslatedRow N p hN hp w δ) from ⟨_,rfl⟩)
    simpa [localRowSpan,localTranslatedRow,localObservationRow] using h
  have he : (-w) • frickeRow N hN w=symbol (frickeLabel N hN)-w • 1 := by
    simp [frickeRow,smul_smul,neg_mul,hw,sub_eq_add_neg,add_comm]
  rw [←he]
  exact Submodule.smul_mem _ _ hm

#print axioms localSignRow_mem_localRowSpan
#print axioms globalSignRow_mem_localRowSpan
end QuantitativeEulerEndpointPrepared
