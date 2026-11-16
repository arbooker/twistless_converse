module

public import QuantitativeMaassRawTerminalColumnFactorV1
public import QuantitativeMaassIsometricPacketSummabilityV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory AsymptoticClassicalPetersson AsymptoticSectorSigns ContinuousLinearMap
open scoped SchwartzMap ContDiff
namespace QuantitativeMaass.RawOriginalWindow

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A)
    (e : Sector N) (t ε : ℝ)

abbrev BothWindowSector :=
  {p : QuantitativeConcreteGoals.maassWindow N 0 t ε //windowSector A P 0 t ε p=e} ⊕
  {p : QuantitativeConcreteGoals.maassWindow N 1 t ε //windowSector A P 1 t ε p=e}

def bothWindowDatum : BothWindowSector A P e t ε→
    AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε :=
  Sum.elim (fun p => windowDatum A P 0 t ε p.val) (fun p => windowDatum A P 1 t ε p.val)

def bothWindowParameter : BothWindowSector A P e t ε→ℝ :=
  Sum.elim (fun p => p.val.val.1) (fun p => p.val.val.1)

theorem bothWindowParameter_mem (p : BothWindowSector A P e t ε) :
    bothWindowParameter A P e t ε p∈Icc t (t+ε) := by
  cases p with
  | inl p => exact p.val.property.2.1
  | inr p => exact p.val.property.2.1

def bothWindowCylinderDatum : BothWindowSector A P e t ε→Lp ℂ 2 (quotientMeasure 0) :=
  fun p => fullTerminalTranslationIsometry A (NeZero.pos N) P e (bothWindowDatum A P e t ε p)

theorem bothWindowCylinderDatum_independent :
    LinearIndependent ℂ (bothWindowCylinderDatum A P e t ε) :=
  ((fullTerminalTranslationIsometry A (NeZero.pos N) P e).toLinearMap.linearIndependent_iff_of_injOn
    (fullTerminalTranslationIsometry A (NeZero.pos N) P e).injective.injOn).mpr
      (windowDatum_both_parities_independent A P t ε e)

theorem bothWindowCylinderDatum_source (p : BothWindowSector A P e t ε) :
    bothWindowCylinderDatum A P e t ε p∈RawCommonReconstruction.cylinderSource A P e := by
  cases p with
  | inl p => exact RawCommonReconstruction.cylinderSource_original A P e 0 t ε p.val p.property
  | inr p => exact RawCommonReconstruction.cylinderSource_original A P e 1 t ε p.val p.property

def extendedTerminalPacket
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0) :=
  let U := (fullTerminalTranslationIsometry A (NeZero.pos N) P e).toContinuousLinearMap
  U.comp ((EulerHilbert.FullTerminal.centeredTerminalPacket A (NeZero.pos N) P f hc he hr R hR hs e).comp U.adjoint)

theorem bothWindowCylinderDatum_eigen
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ s,star (f s)=f s)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    (p : BothWindowSector A P e t ε) :
    extendedTerminalPacket A P e f hc he hr R hR hs (bothWindowCylinderDatum A P e t ε p)=
      ((cosinePacket f (bothWindowParameter A P e t ε p)).re:ℂ) • bothWindowCylinderDatum A P e t ε p := by
  let U := (fullTerminalTranslationIsometry A (NeZero.pos N) P e).toContinuousLinearMap
  have hu (y) : U.adjoint (U y)=y := congrArg (fun B => B y)
    (fullTerminalTranslationIsometry A (NeZero.pos N) P e).adjoint_comp_self
  have hact (σ : ℕ) (q : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //windowSector A P σ t ε p=e}) :
      U (EulerHilbert.FullTerminal.centeredTerminalPacket A (NeZero.pos N) P f hc he hr R hR hs e
        (U.adjoint (U (windowDatum A P σ t ε q.val))))=
      ((cosinePacket f q.val.val.1).re:ℂ) • U (windowDatum A P σ t ε q.val) := by
    have hg := windowDatum_realizes A P σ t ε q.val
    rw [q.property] at hg
    rw [hu,EulerHilbert.FullTerminal.centeredTerminalPacket_original A (NeZero.pos N) P
      f hc he hr R hR hs e q.val.val.1 σ q.val.property.2.2 _ hg,map_smul,
      cosinePacket_real f hr q.val.val.1]
  cases p with
  | inl p => exact hact 0 p
  | inr p => exact hact 1 p

#print axioms bothWindowParameter_mem
#print axioms bothWindowCylinderDatum_independent
#print axioms bothWindowCylinderDatum_source
#print axioms bothWindowCylinderDatum_eigen
end QuantitativeMaass.RawOriginalWindow
