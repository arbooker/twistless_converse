module

public import QuantitativeArithmeticPrimeSmallTwistConverseV4
public import QuantitativeArithmeticSmallLevelCircSpaceV1
public import QuantitativeArithmeticSmallLevelCircModularLSeriesTheoryV4
public import AsymptoticClassicalFrickeNewV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticPrimeSmallTwist

open Complex UpperHalfPlane FinitenessOriginalInput SmallLevelOriginal
open QuantitativeArithmeticSmallLevelCirc
open scoped ModularForm

/-- The modular trace and cusp-form trace have the same underlying function. -/
theorem cusp_arithmeticTrace_zero {G H : Subgroup (GL (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] [G.IsArithmetic] [H.IsArithmetic]
    [G.IsFiniteRelIndex H] (k : ℤ) (F : CuspForm G k)
    (h : ModularForm.trace H (CuspForm.toModularFormₗ F)=0) :
    AsymptoticClassicalCusp.arithmeticTrace G H k F=0 := by
  apply DFunLike.coe_injective
  have hh := congrArg (fun J : ModularForm H k => (J : ℍ → ℂ)) h
  exact hh

/-- The paper's trace-new modular conditions imply the classical cusp-new
conditions whenever the given form is cuspidal. This works at every level. -/
theorem cusp_new_of_isCirc {N k : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (F : CuspForm (level N) (k : ℤ))
    (hF : (F : ℍ → ℂ)=fourierFunction k f) (hc : IsCirc N hN k f) :
    F ∈ AsymptoticClassicalCusp.newSpace N hN (k : ℤ) := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨H,G,hH,hG,_,_,ht⟩ := hc
  have hHF : H=CuspForm.toModularFormₗ F := DFunLike.coe_injective (hH.trans hF.symm)
  subst H
  have hGF : G=CuspForm.toModularFormₗ (AsymptoticClassicalCusp.frickeOperator N hN (k : ℤ) F) := by
    apply DFunLike.coe_injective
    exact hG.trans ((AsymptoticClassicalCusp.frickeOperator_coe N hN (k : ℤ) F).trans
      (ModularLSeries.normalizedFricke_eq_detOne_slash N hN (k : ℤ) F)).symm
  rw [AsymptoticClassicalCusp.mem_newSpace]
  intro r
  let : NeZero (N/r.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN r.property.2) r.property.1.pos).ne'⟩
  let : (level N).IsFiniteRelIndex (level (N/r.val)) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level (N/r.val))).symm).1
  obtain ⟨htF,htG⟩ := ht r
  change ModularForm.trace (level (N/r.val)) (CuspForm.toModularFormₗ F)=0 at htF
  change ModularForm.trace (level (N/r.val)) G=0 at htG
  rw [hGF] at htG
  change AsymptoticClassicalCusp.arithmeticTrace (level N) (level (N/r.val)) (k : ℤ) F=0 ∧
    AsymptoticClassicalCusp.arithmeticTrace (level N)
      (AsymptoticClassicalCusp.frickeOldLevel N (N/r.val) hN) (k : ℤ) F=0
  exact ⟨cusp_arithmeticTrace_zero _ F htF,
    (AsymptoticClassicalCusp.fricke_trace_swap_zero_iff N (N/r.val) hN (k : ℤ) F).mp
      (cusp_arithmeticTrace_zero _ _ htG)⟩

/-- Corollary 5: the original Euler-product class and primitive multiplicative
twists in the strict small-conductor window give a genuine new cusp form,
and membership in the paper's actual M_k^circ. -/
theorem primitive_euler_corollary {p k : ℕ} (hp : p.Prime) (hk : 0<k) (heven : Even k)
    {f : ℕ → ℂ} (hf : IsSolution p k f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (h : PrimitiveTwistContinuationsBelowSqrt p k f ε) :
    ∃ F : CuspForm (level p) (k : ℤ),
      (F : ℍ → ℂ)=fourierFunction k f ∧
      F ∈ AsymptoticClassicalCusp.newSpace p hp.pos (k : ℤ) ∧
      CuspForm.toModularFormₗ F ∈ space p hp.pos k ∧
      (F : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke p hp.pos=
        (ε*Complex.I^(-(k : ℤ))) • (F : ℍ → ℂ) := by
  obtain ⟨F,hF,hW⟩ := primitive_small_conductor_converse hp heven hf.toEulerData ε hε h
  have hm : IsModular p k f := ⟨CuspForm.toModularFormₗ F,hF⟩
  have hc := original_modular_isCirc_even hp.pos hk heven hf hm
  obtain ⟨J,hJ⟩ := isCirc_iff_mem.mp hc
  have heq : J.val=CuspForm.toModularFormₗ F := DFunLike.coe_injective (hJ.trans hF.symm)
  refine ⟨F,hF,cusp_new_of_isCirc hp.pos F hF hc,?_,hW⟩
  exact heq ▸ J.property

#print axioms cusp_new_of_isCirc
#print axioms primitive_euler_corollary

end QuantitativeArithmeticPrimeSmallTwist
