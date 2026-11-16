module

public import QuantitativeMaassCompletedNewSignSpaceV1
public import AsymptoticAtkinLehnerTraceCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticAtkinLehner AsymptoticFreshMatrices QuantitativeNinaMaass AsymptoticOrbitDecode

namespace QuantitativeMaass

/-- A completed normalizer eigenrelation is pointwise on its continuous
representative; no choice of an eigenfunction expansion is needed. -/
theorem normalizer_eigen_continuous (N : ℕ) (g : quotientNormalizerGroup N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (s : ℂ)
    (he : quotientNormalizerPullback N g (AutomorphicL2.denseEmbedding _ _ f)=
      s • AutomorphicL2.denseEmbedding _ _ f) (z : ℍ) :
    f.val (g.val • z)=s*f.val z := by
  have hr : quotientNormalizerRepresentative N g f=s • f := by
    apply continuous_representative_unique N _ (s • f)
    · exact hf.comp (AsymptoticRationalBranches.action_continuous g.val)
    · exact continuous_const.mul hf
    · rw [←quotientNormalizerPullback_representative,map_smul]
      exact he
  exact congrArg (fun h : AutomorphicL2.representatives (gamma N) (quotientMeasure N) => h.val z) hr

/-- The actual trace at a prime occurring once is the identity plus
its p explicit integral branches. -/
theorem simple_levelTrace_formula (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    [NeZero (p*M)]
    (f : AutomorphicL2.representatives (gamma (p*M)) (quotientMeasure (p*M))) (z : ℍ) :
    (levelTraceRepresentative (Nat.dvd_mul_left M p) f).val z=
      f.val z+∑ a : Fin p,f.val (integralLabel (traceSL M p A B hAB a.val) • z) := by
  classical
  let := Fintype.ofFinite (gamma M ⧸ (gamma (p*M)).subgroupOf (gamma M))
  change (∑ x : gamma M ⧸ (gamma (p*M)).subgroupOf (gamma M),
    CosetTrace.value _ f.val (fun a w => f.property.2.1 ⟨a.val.val,a.property⟩ w) x z)=_
  rw [←(traceCosetEquiv M p hM hpM A B hAB).sum_comp,Fintype.sum_option]
  have hv (a : Option (Fin p)) :
      CosetTrace.value _ f.val (fun a w => f.property.2.1 ⟨a.val.val,a.property⟩ w)
        (traceCosetEquiv M p hM hpM A B hAB a) z=
      f.val ((traceRepresentative M p A B hAB a).val⁻¹ • z) := rfl
  simp only [hv,traceRepresentative,Subgroup.coe_one,inv_one,one_smul,inv_inv]

/-- The genuine trace kernel and local Atkin equation force the
un-normalized ramified U_p equation. -/
theorem simple_trace_sign_ramified (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    [NeZero (p*M)]
    (f : AutomorphicL2.representatives (gamma (p*M)) (quotientMeasure (p*M)))
    (hf : Continuous f.val) (s : ℂ)
    (ht : levelTrace (Nat.dvd_mul_left M p) (AutomorphicL2.denseEmbedding _ _ f)=0)
    (hW : ∀ z,f.val (localAtkin M p hM (Fact.out : p.Prime).pos A B hAB • z)=s*f.val z)
    (z : ℍ) :
    ∑ a : Fin p,f.val (ramifiedLabel p (Fact.out : p.Prime).pos a • z)=-s*f.val z := by
  have he := congrFun ((continuous_trace_zero_iff (Nat.dvd_mul_left M p) f hf).mp ht) z
  rw [simple_levelTrace_formula M p hM hpM A B hAB] at he
  simp_rw [←localAtkin_mul_ramified M p hM (Fact.out : p.Prime).pos A B hAB,
    mul_smul,hW] at he
  rw [←Finset.mul_sum] at he
  change f.val z+s*(∑ a : Fin p,f.val (ramifiedLabel p (Fact.out : p.Prime).pos a • z))=0 at he
  have hs (y : ℍ) : s^2*f.val y=f.val y := by
    have hi := f.property.2.1
      ⟨_,localAtkin_square_mem M p hM (Fact.out : p.Prime).pos A B hAB⟩ y
    change f.val ((localAtkin M p hM (Fact.out : p.Prime).pos A B hAB*
      localAtkin M p hM (Fact.out : p.Prime).pos A B hAB) • y)=f.val y at hi
    rw [mul_smul,hW,hW] at hi
    simpa only [pow_two,mul_assoc] using hi
  have hsum : s^2*(∑ a : Fin p,f.val (ramifiedLabel p (Fact.out : p.Prime).pos a • z))=
      ∑ a : Fin p,f.val (ramifiedLabel p (Fact.out : p.Prime).pos a • z) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => hs _)
  linear_combination s*he-hsum

/-- In a completed generator sector, the local sign used in the
ramified equation is the specified actual Atkin eigenvalue. -/
theorem completedNewSign_simple_ramified (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    [NeZero (p*M)]
    (χ : admissibleGeneratorIndex (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) → ℂ)
    (f : AutomorphicL2.representatives (gamma (p*M)) (quotientMeasure (p*M)))
    (hf : Continuous f.val)
    (hx : AutomorphicL2.denseEmbedding _ _ f ∈
      completedNewSignSpace (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) χ)
    (z : ℍ) :
    ∑ a : Fin p,f.val (ramifiedLabel p (Fact.out : p.Prime).pos a • z)=
      -(χ ⟨exactAtkinLabel M p (Fact.out : p.Prime).pos A B hAB,
        admissibleNormalizerGenerator.atkin M p (Fact.out : p.Prime).pos A B hAB rfl⟩)*f.val z := by
  let hN := Nat.mul_pos (Fact.out : p.Prime).pos hM
  let i : admissibleGeneratorIndex (p*M) hN :=
    ⟨exactAtkinLabel M p (Fact.out : p.Prime).pos A B hAB,
      admissibleNormalizerGenerator.atkin M p (Fact.out : p.Prime).pos A B hAB rfl⟩
  have ht : levelTrace (Nat.dvd_mul_left M p) (AutomorphicL2.denseEmbedding _ _ f)=0 := by
    have hn : AutomorphicL2.denseEmbedding _ _ f ∈ QuantitativeNinaMaass.newSpace (p*M) hN := hx.2.1
    simp only [newSpace,Submodule.mem_iInf] at hn
    have h := hn ⟨p,Fact.out,Nat.dvd_mul_right p M⟩
    have hd : p*M/p=M := Nat.mul_div_cancel_left M (Fact.out : p.Prime).pos
    have hk : AutomorphicL2.denseEmbedding _ _ f ∈
        newTraceKernel hN (Nat.dvd_mul_left M p) := by
      simpa only [hd] using h
    exact hk.1
  apply simple_trace_sign_ramified M p hM hpM A B hAB f hf (χ i) ht
  intro w
  have he := normalizer_eigen_continuous (p*M) (admissibleGeneratorLift (p*M) hN i)
    f hf (χ i) (hx.2.2 i) w
  change f.val (exactAtkinLabel M p (Fact.out : p.Prime).pos A B hAB • w)=χ i*f.val w at he
  rwa [exactAtkinLabel_eq_localAtkin M p hM (Fact.out : p.Prime).pos A B hAB] at he

#print axioms normalizer_eigen_continuous
#print axioms simple_levelTrace_formula
#print axioms simple_trace_sign_ramified
#print axioms completedNewSign_simple_ramified

end QuantitativeMaass
