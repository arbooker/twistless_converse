module

public import QuantitativeMaassAbelOriginalTestRepresentationV1
public import QuantitativeMaassWaveBoundaryTestsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

theorem coshTimeOperator_real (F : ℝ → ℂ) (hr : ∀ q,star (F q)=F q) (q : ℝ) :
    star (coshTimeOperator F q)=coshTimeOperator F q := by
  have h1 := deriv_real_profile F hr
  have h2 := deriv_real_profile (deriv F) h1
  simp only [coshTimeOperator,star_add,star_mul,star_sub,star_pow,star_one]
  rw [h1,h2]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

/-- The original q-test graph identity, after the bounded spectral cutoff. -/
theorem regularizedAbel_original_equation (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Wave.resolventCutoffOperator (friedrichsResolvent N) ε
      (abelKernelOperator N (coshTimeOperator F) (coshTimeOperator_smooth F hF)
        (coshTimeOperator_compact F hc) R hR (coshTimeOperator_support F _ hs) f)=
    -regularizedShiftedGenerator N ε
      (Wave.resolventCutoffOperator (friedrichsResolvent N) ε (abelKernelOperator N F hF hc R hR hs f)) := by
  let P := Wave.resolventCutoffOperator (friedrichsResolvent N) ε
  let G := Wave.boundedResolventOperator (friedrichsResolvent N) ε
  have hg := Wave.friedrichsCutoff_generator_on_graph N ε hε
    (abelKernelOperator_graph N F hF hc R hR hs hr f)
  change P ((1/4:ℂ) • abelKernelOperator N F hF hc R hR hs f-
      abelKernelOperator N (coshTimeOperator F) (coshTimeOperator_smooth F hF)
        (coshTimeOperator_compact F hc) R hR (coshTimeOperator_support F _ hs) f)=
    G (P (abelKernelOperator N F hF hc R hR hs f)) at hg
  rw [map_sub,map_smul] at hg
  change P _= -(G (P _)-(1/4:ℂ) • P _)
  rw [← hg]
  abel

/-- A complex bounded Cauchy evolution has the literal q-test boundary flux.
No decay or growth assumption on the evolving vector is required. -/
theorem boundedCauchy_cosh_boundary {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) (c : H×H)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫ t in Ioi (0:ℝ),coshTimeOperator F (Real.cosh t) • boundedCauchyPosition (A.restrictScalars ℝ) c t)+
      A (∫ t in Ioi (0:ℝ),coshTimeTest F t • boundedCauchyPosition (A.restrictScalars ℝ) c t)=
      F 1 • (-c.2) := by
  let u := boundedCauchyPosition (A.restrictScalars ℝ) c
  have hu : Continuous u := boundedCauchyPosition_continuous _ c
  have h := compactTest_second_boundary (coshTimeTest F) (hF.comp Real.contDiff_cosh)
    (coshTimeTest_compact F R hR hs) u (boundedCauchyVelocity (A.restrictScalars ℝ) c)
    (fun t => -A (u t)) (boundedCauchyPosition_hasDerivAt _ c)
    (boundedCauchyVelocity_hasDerivAt _ c) (A.continuous.comp hu).neg
  have hi := (coshCurve_integrable F hF R hR hs u hu).integrableOn (s:=Ioi (0:ℝ))
  have hH := (coshCurve_integrable (coshTimeOperator F) (coshTimeOperator_smooth F hF)
    R hR (coshTimeOperator_support F _ hs) u hu).integrableOn (s:=Ioi (0:ℝ))
  simp only [coshTimeTest_second F hF,coshTimeTest_deriv_zero F hF,zero_smul,sub_zero,
    smul_neg,sub_neg_eq_add] at h
  have hm : (∫ t in Ioi (0:ℝ),coshTimeTest F t • A (u t))=
      A (∫ t in Ioi (0:ℝ),coshTimeTest F t • u t) := by
    simpa only [map_smul] using A.integral_comp_comm hi
  have hAi : IntegrableOn (fun t => coshTimeTest F t • A (u t)) (Ioi (0:ℝ)) := by
    change Integrable _ (volume.restrict (Ioi (0:ℝ)))
    simpa only [map_smul] using A.integrable_comp hi
  change IntegrableOn (fun t => coshTimeOperator F (Real.cosh t) • u t) (Ioi (0:ℝ)) at hH
  rw [integral_add hH hAi,hm] at h
  simpa only [coshTimeTest,Real.cosh_zero,(boundedCauchy_initial (A.restrictScalars ℝ) c).2] using h

/-- The actual recovered Abel evolution has zero initial velocity. The
endpoint condition is derived from the original q-test PDE, rather than
assumed from the equation on tests supported strictly inside positive time. -/
theorem regularizedAbelPosition_zero_velocity (N : ℕ) [NeZero N]
    (ε : ℝ) (hε : 0<ε) (f : AutomorphicSpace N)
    (c : AutomorphicSpace N×AutomorphicSpace N)
    (hcT : ∀ φ : PositiveSmoothTest,regularizedAbelDistribution N ε f φ=
      ∫ t,φ t • boundedCauchyPosition (regularizedShiftedGenerator N ε) c t) : c.2=0 := by
  let F := abelCutoff (Real.cosh 1-1)
  have hF : ContDiff ℝ ∞ F := abelCutoff_smooth _
  have hc : HasCompactSupport F := abelCutoff_compact _ (sub_pos.mpr (Real.one_lt_cosh.mpr (by norm_num)))
  have hr : ∀ q,star (F q)=F q := by
    intro q
    simp only [F,abelCutoff,Complex.star_def,Complex.conj_ofReal]
  have hs : Function.support F⊆Iic (Real.cosh 1) := abelCutoff_radius_support 1 (by norm_num)
  let A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
    Wave.boundedResolventOperator (friedrichsResolvent N) ε-(1/4:ℂ) • 1
  have he := regularizedAbel_original_equation N ε hε f F hF hc hr 1 (by norm_num) hs
  rw [regularizedAbelPosition_originalTest N ε f c hcT F hF hc hr 1 (by norm_num) hs,
    regularizedAbelPosition_originalTest N ε f c hcT (coshTimeOperator F)
      (coshTimeOperator_smooth F hF) (coshTimeOperator_compact F hc)
      (coshTimeOperator_real F hr) 1 (by norm_num) (coshTimeOperator_support F _ hs)] at he
  have hb := boundedCauchy_cosh_boundary A c F hF 1 (by norm_num) hs
  change (∫ t in Ioi (0:ℝ),coshTimeTest (coshTimeOperator F) t •
      boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)+
    regularizedShiftedGenerator N ε (∫ t in Ioi (0:ℝ),coshTimeTest F t •
      boundedCauchyPosition (regularizedShiftedGenerator N ε) c t)=F 1 • (-c.2) at hb
  rw [he,neg_add_cancel] at hb
  have hf1 : F 1=1 := by simp only [F,abelCutoff,abelCutoffReal_one,Complex.ofReal_one]
  rw [hf1,one_smul] at hb
  exact neg_eq_zero.mp hb.symm

#print axioms coshTimeOperator_real
#print axioms regularizedAbel_original_equation
#print axioms boundedCauchy_cosh_boundary
#print axioms regularizedAbelPosition_zero_velocity

end QuantitativeMaass
