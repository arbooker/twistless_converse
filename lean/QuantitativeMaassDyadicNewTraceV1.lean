module

public import QuantitativeMaassFrickeHalfV1
public import QuantitativeNinaMaassTraceDiamondsV1
public import AsymptoticProjectiveRamifiedCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticIntegralSubgroup
open QuantitativeNinaMaass AsymptoticClassicalPetersson
open AsymptoticFreshMatrices
open scoped MatrixGroups

namespace QuantitativeMaass

/-- The actual completed-space trace has the usual lower-transvection
sum at a repeated prime; the coset enumeration is proved over integers. -/
theorem ramified_levelTrace_formula (M q : ℕ) (hM : 0<M) (hq : 0<q) (hqM : q∣M)
    [NeZero (q*M)]
    (f : AutomorphicL2.representatives (gamma (q*M)) (quotientMeasure (q*M))) (z : ℍ) :
    (levelTraceRepresentative (Nat.dvd_mul_left M q) f).val z=
      ∑ j : Fin q,f.val ((integralLabel (lowerSL M (j.val:ℤ)))⁻¹ • z) := by
  classical
  let := Fintype.ofFinite (gamma M ⧸ (gamma (q*M)).subgroupOf (gamma M))
  change (∑ x : gamma M ⧸ (gamma (q*M)).subgroupOf (gamma M),
    CosetTrace.value _ f.val (fun a w => f.property.2.1 ⟨a.val.val,a.property⟩ w) x z)=_
  rw [←(AsymptoticRamifiedCosets.projectiveCosetEquiv M q hM hq hqM).sum_comp]
  rfl

/-- A zero two-term trace forces anti-invariance under the nontrivial
lower coset, before imposing any spectral condition. -/
theorem dyadic_trace_lower_anti (M : ℕ) (hM : 0<M) (h2 : 2∣M) [NeZero (2*M)]
    (f : AutomorphicL2.representatives (gamma (2*M)) (quotientMeasure (2*M)))
    (hf : Continuous f.val)
    (ht : levelTrace (Nat.dvd_mul_left M 2) (AutomorphicL2.denseEmbedding _ _ f)=0)
    (z : ℍ) : f.val (integralLabel (lowerSL M 1) • z)=-f.val z := by
  have hz := (continuous_trace_zero_iff (Nat.dvd_mul_left M 2) f hf).mp ht
  have he := congrFun hz (integralLabel (lowerSL M 1) • z)
  rw [ramified_levelTrace_formula M 2 hM (by decide) h2,Fin.sum_univ_two] at he
  have hzero : lowerSL M 0=1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerSL,AsymptoticFreshCRT.lower]
  simp only [Fin.val_zero,Fin.val_one,Int.natCast_zero,Int.natCast_one,hzero,map_one,
    inv_one,one_smul,inv_smul_smul,Pi.zero_apply] at he
  exact eq_neg_of_add_eq_zero_left he

/-- The second physical trace-new equation gives the half-translation
identity used in the admissible target metric. -/
theorem dyadic_new_half_translation (M : ℕ) (hM : 0<M) (h2 : 2∣M) [NeZero (2*M)]
    (f : AutomorphicL2.representatives (gamma (2*M)) (quotientMeasure (2*M)))
    (hf : Continuous f.val)
    (hnew : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel (Nat.mul_pos (by decide : 0<2) hM) (Nat.dvd_mul_left M 2))
    (z : ℍ) : f.val (translationLabel (1/2) • z)=-f.val z := by
  let hN := Nat.mul_pos (by decide : 0<2) hM
  have ht : levelTrace (Nat.dvd_mul_left M 2)
      (AutomorphicL2.denseEmbedding _ _ (frickeRepresentative (2*M) hN f))=0 := by
    rw [←frickeIsometry_apply]
    exact hnew.2
  have hl := dyadic_trace_lower_anti M hM h2 (frickeRepresentative (2*M) hN f)
    (frickeRepresentative_continuous (2*M) hN f hf) ht
  have hw : frickeLabel (2*M) hN*integralLabel (lowerSL M 1)=
      translationLabel (-1/2)*frickeLabel (2*M) hN := by
    obtain ⟨L,rfl⟩ := h2
    have hp : 0<L := by omega
    simpa only [show 2*(2*L)=4*L by omega] using fricke_lower_half L hp
  have hminus (w : ℍ) : f.val (translationLabel (-1/2) • w)=-f.val w := by
    have he := hl (frickeLabel (2*M) hN • w)
    change f.val (frickeLabel (2*M) hN •
      (integralLabel (lowerSL M 1) • (frickeLabel (2*M) hN • w)))=
      -f.val (frickeLabel (2*M) hN • (frickeLabel (2*M) hN • w)) at he
    have heq : frickeLabel (2*M) hN*integralLabel (lowerSL M 1)*frickeLabel (2*M) hN=
        translationLabel (-1/2) := by
      rw [hw,mul_assoc,frickeLabel_mul_self,mul_one]
    simpa only [←mul_smul,←mul_assoc,heq,frickeLabel_mul_self,one_smul] using he
  have he := hminus (translationLabel (1/2) • z)
  have hi : translationLabel (-1/2)=(translationLabel (1/2))⁻¹ := by
    rw [translationLabel_inv]
    congr 1
    ring
  rw [hi,inv_smul_smul] at he
  exact neg_eq_iff_eq_neg.mp he.symm

/-- At every level divisible by four, the genuine simultaneous newspace
forces the half-translation equation on each continuous representative. -/
theorem newSpace_half_translation (N : ℕ) (hN : 0<N) (h4 : 4∣N) [NeZero N]
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hv : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN)
    (z : ℍ) : f.val (translationLabel (1/2) • z)=-f.val z := by
  have h2 : 2∣N := (by decide : 2∣4).trans h4
  simp only [newSpace,Submodule.mem_iInf] at hv
  have ht := hv ⟨2,by decide,h2⟩
  obtain ⟨M,rfl⟩ := h2
  have hM : 0<M := by omega
  have hM2 : 2∣M := by omega
  have hdiv : 2*M/2=M := by omega
  have ht' : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel (Nat.mul_pos (by decide : 0<2) hM) (Nat.dvd_mul_left M 2) := by
    simpa only [hdiv] using ht
  exact dyadic_new_half_translation M hM hM2 f hf ht' z

#print axioms ramified_levelTrace_formula
#print axioms dyadic_trace_lower_anti
#print axioms dyadic_new_half_translation
#print axioms newSpace_half_translation

end QuantitativeMaass
