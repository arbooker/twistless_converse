module

public import QuantitativeMaassCompletedGeneratorMetricV1
public import QuantitativeMaassDyadicNewTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open AsymptoticFreshMatrices AsymptoticIntegralSubgroup QuantitativeNinaMaass
open scoped MatrixGroups

namespace QuantitativeMaass

/-- Pullback after the genuine two-coset trace is the sum of the identity
and the lower normalizer, on all completed vectors. -/
theorem dyadic_trace_operator_identity (M : ℕ) (hM : 0<M) (h2 : 2∣M) [NeZero (2*M)]
    (g : (quotientNormalizerGroup (2*M))) (hg : g.val=integralLabel (lowerSL M 1))
    (x : AutomorphicSpace (2*M)) :
    levelCover (Nat.dvd_mul_left M 2) (levelTrace (Nat.dvd_mul_left M 2) x)=
      x+quotientNormalizerPullback (2*M) g⁻¹ x := by
  have he : (fun x : AutomorphicSpace (2*M) =>
      levelCover (Nat.dvd_mul_left M 2) (levelTrace (Nat.dvd_mul_left M 2) x))=
      fun x => x+quotientNormalizerPullback (2*M) g⁻¹ x := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma (2*M)) (quotientMeasure (2*M))).equalizer
      ((levelCover (Nat.dvd_mul_left M 2)).continuous.comp (levelTrace (Nat.dvd_mul_left M 2)).continuous)
      (continuous_id.add (quotientNormalizerPullback (2*M) g⁻¹).continuous)
    funext f
    change levelCover (Nat.dvd_mul_left M 2)
      (levelTrace (Nat.dvd_mul_left M 2) (AutomorphicL2.denseEmbedding _ _ f))=
      AutomorphicL2.denseEmbedding _ _ f+
        quotientNormalizerPullback (2*M) g⁻¹ (AutomorphicL2.denseEmbedding _ _ f)
    simp only [levelTraceRepresentative_embedding,levelCover_apply,
      quotientNormalizerPullback_representative,←map_add]
    congr 1
    apply Subtype.ext
    funext z
    change (levelTraceRepresentative (Nat.dvd_mul_left M 2) f).val z=
      f.val z+f.val (g.val⁻¹ • z)
    rw [ramified_levelTrace_formula M 2 hM (by decide) h2,Fin.sum_univ_two,hg]
    have hzero : lowerSL M 0=1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lowerSL,AsymptoticFreshCRT.lower]
    simp only [Fin.val_zero,Fin.val_one,Int.natCast_zero,Int.natCast_one,hzero,map_one,inv_one,one_smul]
  exact congrFun he x

def completedFrickeNormalizer (N : ℕ) (hN : 0<N) : (quotientNormalizerGroup N) :=
  admissibleGeneratorLift N hN ⟨frickeLabel N hN,admissibleNormalizerGenerator.fricke⟩

def completedHalfNormalizer (N : ℕ) (hN : 0<N) (h4 : 4∣N) : (quotientNormalizerGroup N) :=
  admissibleGeneratorLift N hN ⟨translationLabel (1/2),admissibleNormalizerGenerator.half h4⟩

theorem completedFrickeNormalizer_action (N : ℕ) (hN : 0<N) (x : AutomorphicSpace N) :
    quotientNormalizerPullback N (completedFrickeNormalizer N hN) x=frickeIsometry N hN x := rfl

theorem completedFrickeNormalizer_square (N : ℕ) (hN : 0<N) :
    completedFrickeNormalizer N hN*completedFrickeNormalizer N hN=1 := by
  apply Subtype.ext
  exact frickeLabel_mul_self N hN

/-- The paired trace-new equations force half-translation anti-invariance
on the Hilbert space itself; continuity and representative choice disappear. -/
theorem dyadic_new_half_completed (M : ℕ) (hM : 0<M) (h2 : 2∣M) [NeZero (2*M)]
    (x : AutomorphicSpace (2*M))
    (hx : x∈newTraceKernel (Nat.mul_pos (by decide : 0<2) hM) (Nat.dvd_mul_left M 2)) :
    let hN := Nat.mul_pos (by decide : 0<2) hM
    let h4 : 4∣2*M := by obtain ⟨L,rfl⟩ := h2; exact ⟨L,by ring⟩
    quotientNormalizerPullback (2*M) (completedHalfNormalizer (2*M) hN h4) x=-x := by
  dsimp only
  let hN := Nat.mul_pos (by decide : 0<2) hM
  have h4 : 4∣2*M := by obtain ⟨L,rfl⟩ := h2; exact ⟨L,by ring⟩
  let W := completedFrickeNormalizer (2*M) hN
  let T := completedHalfNormalizer (2*M) hN h4
  let L := W*T⁻¹*W
  have hWW : W*W=1 := completedFrickeNormalizer_square (2*M) hN
  have hL : L.val=integralLabel (lowerSL M 1) := by
    have hw : frickeLabel (2*M) hN*integralLabel (lowerSL M 1)=
        translationLabel (-1/2)*frickeLabel (2*M) hN := by
      obtain ⟨K,rfl⟩ := h2
      have hp : 0<K := by omega
      simpa only [show 2*(2*K)=4*K by omega] using fricke_lower_half K hp
    have hi : (translationLabel (1/2))⁻¹=translationLabel (-1/2) := by
      rw [translationLabel_inv]
      congr 1
      ring
    change frickeLabel (2*M) hN*(translationLabel (1/2))⁻¹*frickeLabel (2*M) hN=_
    rw [hi,mul_assoc,←hw,←mul_assoc,frickeLabel_mul_self,one_mul]
  have htrace : levelTrace (Nat.dvd_mul_left M 2) (quotientNormalizerPullback (2*M) W x)=0 := hx.2
  have he := dyadic_trace_operator_identity M hM h2 L hL (quotientNormalizerPullback (2*M) W x)
  rw [htrace,map_zero] at he
  have hanti : quotientNormalizerPullback (2*M) L⁻¹ (quotientNormalizerPullback (2*M) W x)=
      -quotientNormalizerPullback (2*M) W x := eq_neg_of_add_eq_zero_right he.symm
  have hh := congrArg (quotientNormalizerPullback (2*M) W) hanti
  rw [map_neg,←quotientNormalizerPullback_mul,←quotientNormalizerPullback_mul,
    ←quotientNormalizerPullback_mul,hWW,quotientNormalizerPullback_one] at hh
  have hword : W*L⁻¹*W=T := by
    have hWi : W⁻¹=W := inv_eq_of_mul_eq_one_left hWW
    dsimp only [L]
    simp only [_root_.mul_inv_rev,inv_inv,hWi,←mul_assoc,hWW,one_mul]
    rw [mul_assoc,hWW,mul_one]
  change quotientNormalizerPullback (2*M) T x=-x
  simpa only [←mul_assoc,hword] using hh

#print axioms dyadic_trace_operator_identity
#print axioms completedFrickeNormalizer_action
#print axioms completedFrickeNormalizer_square
#print axioms dyadic_new_half_completed

end QuantitativeMaass
