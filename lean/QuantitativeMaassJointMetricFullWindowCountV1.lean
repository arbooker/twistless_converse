module

public import QuantitativeMaassJointMetricWindowCountV1
public import QuantitativeMaassOriginalSectorEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns ContinuousLinearMap
open scoped SchwartzMap ContDiff BigOperators
namespace QuantitativeMaass.RawOriginalWindow

/-- The same positive full-terminal excess that enters compact canonical
subtraction, with the fixed metric and output constants from counting. -/
def jointMetricSectorExcess {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (cover : AdmissibleScalarCover N hN) (P : FinitenessGlobalHeight.Parameters A) (e : Sector N)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) : ℝ :=
  let P' := AsymptoticReconstructedCount.parameters A P
  let L := (cover.metric P'.epsilon_pos (show 1≤P'.s+3 by omega)).change
  let U := (fullTerminalTranslationIsometry A hN.1 P e).toContinuousLinearMap
  let C := U.comp (fullTerminalColumnOutput A hN.1 P e)
  let D := L.symm.toContinuousLinearMap
  let Qsrc := (RawCommonReconstruction.metricCylinderSource A P e L).starProjection
  let Qcan := cover.physicalNewSignProjection P'.epsilon_pos (show 1≤P'.s+3 by omega)
    (sectorCharacter N hN.1 e) (sectorCharacter_norm N hN.1 e)
  (‖L.toContinuousLinearMap‖^2*‖C‖^2)*
    columnLinearTrace (volume.restrict (AsymptoticCertificateOperators.highStrip P'.ε))
      (cylinderCenteredCappedColumn f hc he R hR hs P'.ε (P'.s+3))
      ((D.comp Qsrc).comp D.adjoint-(D.comp Qcan).comp D.adjoint)

/-- Summing all finite sign sectors gives the literal two-parity count,
with coefficient one on the full cuspidal newspace packet energy. -/
theorem bothWindow_joint_metric_count {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (cover : AdmissibleScalarCover N hN) (P : FinitenessGlobalHeight.Parameters A)
    {ι κ ρ : Type*} [Countable ι] [Countable κ]
    (b : HilbertBasis ι ℂ (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε))
    (c : HilbertBasis κ ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (d : HilbertBasis ρ ℂ (completedCuspidalNewSpace N hN.1)) (η : Sector N→Type*)
    (ds : ∀ e,HilbertBasis (η e) ℂ (completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e)))
    (t ε : ℝ) (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (hlower : ∀ r∈Icc t (t+ε),1≤(cosinePacket f r).re) :
    (QuantitativeConcreteGoals.maassWindow N 0 t ε).Finite ∧
    (QuantitativeConcreteGoals.maassWindow N 1 t ε).Finite ∧
    ((QuantitativeConcreteGoals.maassWindow N 0 t ε).ncard:ℝ)+
      ((QuantitativeConcreteGoals.maassWindow N 1 t ε).ncard:ℝ)≤
      hilbertSchmidtEnergy d (completedCuspidalNewTimePacket N hN.1 f (f.smooth ⊤) hc)+
        ∑ e : Sector N,jointMetricSectorExcess A hN cover P e f hc he R hR hs := by
  classical
  have hb (e : Sector N) := bothWindow_joint_metric_sector_count A hN cover P e b c (ds e)
    t ε f hc he hr R hR hs hlower
  let W := fun σ => QuantitativeConcreteGoals.maassWindow N σ t ε
  let V := fun σ e => {p : W σ // windowSector A P σ t ε p=e}
  let : ∀ e : Sector N,Finite (BothWindowSector A P e t ε) := fun e => (hb e).1
  let : ∀ e : Sector N,Finite (V 0 e) := fun e =>
    Finite.of_injective (fun x : V 0 e => (Sum.inl x : BothWindowSector A P e t ε)) Sum.inl_injective
  let : ∀ e : Sector N,Finite (V 1 e) := fun e =>
    Finite.of_injective (fun x : V 1 e => (Sum.inr x : BothWindowSector A P e t ε)) Sum.inr_injective
  let : Finite (W 0) := Finite.of_equiv (Σ e : Sector N,V 0 e)
    (Equiv.sigmaFiberEquiv (windowSector A P 0 t ε))
  let : Finite (W 1) := Finite.of_equiv (Σ e : Sector N,V 1 e)
    (Equiv.sigmaFiberEquiv (windowSector A P 1 t ε))
  refine ⟨Set.toFinite _,Set.toFinite _,?_⟩
  have hcard0 : Nat.card (W 0)=∑ e : Sector N,Nat.card (V 0 e) := by
    rw [←Nat.card_congr (Equiv.sigmaFiberEquiv (windowSector A P 0 t ε)),Nat.card_sigma]
  have hcard1 : Nat.card (W 1)=∑ e : Sector N,Nat.card (V 1 e) := by
    rw [←Nat.card_congr (Equiv.sigmaFiberEquiv (windowSector A P 1 t ε)),Nat.card_sigma]
  change ((W 0).ncard:ℝ)+((W 1).ncard:ℝ)≤_
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq,hcard0,hcard1,Nat.cast_sum,Nat.cast_sum,←Finset.sum_add_distrib]
  calc
    _=∑ e : Sector N,(Nat.card (BothWindowSector A P e t ε):ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [BothWindowSector,Nat.card_sum,Nat.cast_add]
      rfl
    _≤∑ e : Sector N,(hilbertSchmidtEnergy (ds e)
      (completedNewSignTimePacket N hN.1 (sectorCharacter N hN.1 e) f (f.smooth ⊤) he hc hr R hR hs)+
        jointMetricSectorExcess A hN cover P e f hc he R hR hs) :=
      Finset.sum_le_sum (fun e _ => (hb e).2)
    _≤_ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (original_sector_energy_le N hN.1 d η ds f (f.smooth ⊤) he hc hr R hR hs) le_rfl

#print axioms bothWindow_joint_metric_count
end QuantitativeMaass.RawOriginalWindow
