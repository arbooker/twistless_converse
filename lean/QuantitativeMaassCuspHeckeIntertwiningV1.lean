module

public import QuantitativeMaassHeckeHalfDensityV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

theorem logBandTranslate_cusp_representative_ae (N : ℕ) (hN : 0<N) (s : SL(2,ℤ))
    (A B t : ℝ) (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    (logBandTranslate A B t (cuspLogConstant N hN s (t+A) (t+B)
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)) : ℝ → ℂ)
      =ᵐ[volume.restrict (Icc A B)] fun x => logHalfDensity (cuspConstant N s f.val) (x+t) := by
  have hp : (fun x => (cuspLogConstant N hN s (t+A) (t+B)
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) : ℝ → ℂ) (x+t))
      =ᵐ[volume.restrict (Icc A B)] fun x => logHalfDensity (cuspConstant N s f.val) (x+t) :=
    (add_logBand_preserving A B t).quasiMeasurePreserving.ae
      (cuspLogConstant_representative_ae N hN s (t+A) (t+B) f hf)
  exact (logBandTranslate_ae A B t _).trans hp

/-- The actual bounded Hecke operator has the two-translation constant-term
law on continuous invariant representatives in local L2. -/
theorem cuspLogConstant_hecke_representative (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (s : SL(2,ℤ)) (A B : ℝ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    cuspLogConstant N hN s A B (HeckeL2.operator N p hN hpN a b hab
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f))=
      logBandTranslate A B (Real.log p) (cuspLogConstant N hN s (Real.log p+A) (Real.log p+B)
        (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f))+
      logBandTranslate A B (-Real.log p) (cuspLogConstant N hN s (-Real.log p+A) (-Real.log p+B)
        (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)) := by
  rw [HeckeL2.operator_on_representatives]
  apply Lp.ext
  have hl := cuspLogConstant_representative_ae N hN s A B
    (HeckeL2.heckeRepresentative N p hN hpN a b hab f)
    (heckeRepresentative_continuous N p hN hpN hNp a b hab f hf)
  have hp := logBandTranslate_cusp_representative_ae N hN s A B (Real.log p) f hf
  have hm := logBandTranslate_cusp_representative_ae N hN s A B (-Real.log p) f hf
  filter_upwards [hl,hp,hm,Lp.coeFn_add
    (logBandTranslate A B (Real.log p) (cuspLogConstant N hN s (Real.log p+A) (Real.log p+B)
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)))
    (logBandTranslate A B (-Real.log p) (cuspLogConstant N hN s (-Real.log p+A) (-Real.log p+B)
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)))] with x hl hp hm ha
  rw [hl,ha,Pi.add_apply,hp,hm,← normalizedCuspHecke_eq_representative N p hN hpN hNp a b hab f]
  simpa only [sub_eq_add_neg] using
    normalizedCuspHecke_logHalfDensity N p hNp hpres s f.val hf f.property.2.1 x

/-- Actual all-cusp Hecke intertwining for EVERY quotient L2 vector,
proved from the literal representative law by continuous Poincare-seed density. -/
theorem cuspLogConstant_hecke (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (s : SL(2,ℤ)) (A B : ℝ)
    (f : AutomorphicSpace N) :
    cuspLogConstant N hN s A B (HeckeL2.operator N p hN hpN a b hab f)=
      logBandTranslate A B (Real.log p) (cuspLogConstant N hN s (Real.log p+A) (Real.log p+B) f)+
      logBandTranslate A B (-Real.log p) (cuspLogConstant N hN s (-Real.log p+A) (-Real.log p+B) f) := by
  have he : (fun f : AutomorphicSpace N =>
      cuspLogConstant N hN s A B (HeckeL2.operator N p hN hpN a b hab f))=
      fun f => logBandTranslate A B (Real.log p)
        (cuspLogConstant N hN s (Real.log p+A) (Real.log p+B) f)+
        logBandTranslate A B (-Real.log p)
          (cuspLogConstant N hN s (-Real.log p+A) (-Real.log p+B) f) := by
    apply (poincareSeedVector_dense N).equalizer
      ((cuspLogConstant N hN s A B).continuous.comp (HeckeL2.operator N p hN hpN a b hab).continuous)
      (((logBandTranslate A B (Real.log p)).continuous.comp
        (cuspLogConstant N hN s (Real.log p+A) (Real.log p+B)).continuous).add
        ((logBandTranslate A B (-Real.log p)).continuous.comp
          (cuspLogConstant N hN s (-Real.log p+A) (-Real.log p+B)).continuous))
    funext v
    let vf : AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
      ⟨_,poincareSeed_representative N v⟩
    have hc : Continuous vf.val := by
      let : ContinuousConstSMul (gamma N) ℍ :=
        ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
      exact poincareSum_continuous (G := gamma N) _ v.compact (upperFunction_continuous v.smooth)
    exact cuspLogConstant_hecke_representative N p hN hpN hNp hpres a b hab s A B vf hc
  exact congrFun he f

#print axioms cuspLogConstant_hecke_representative
#print axioms cuspLogConstant_hecke

end QuantitativeMaass
