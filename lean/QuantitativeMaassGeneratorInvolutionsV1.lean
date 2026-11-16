module

public import QuantitativeMaassCompletedGeneratorMetricV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticCongruenceLabels AsymptoticIntegralSubgroup AsymptoticAtkinLehner

namespace QuantitativeMaass

/-- A congruence-group element acts trivially on the actual completed quotient. -/
theorem quotientNormalizerPullback_gamma (N : ℕ) (g : quotientNormalizerGroup N)
    (hg : g.val∈gamma N) (x : AutomorphicSpace N) : quotientNormalizerPullback N g x=x := by
  have he : (fun x : AutomorphicSpace N => quotientNormalizerPullback N g x)=id := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (quotientNormalizerPullback N g).continuous continuous_id
    funext f
    rw [Function.comp_apply,Function.comp_apply,quotientNormalizerPullback_representative]
    congr 1
    apply Subtype.ext
    funext z
    exact f.property.2.1 ⟨g.val,hg⟩ z
  exact congrFun he x

/-- Representatives in the same left congruence coset give the same
bounded pullback on the completed quotient. -/
theorem quotientNormalizerPullback_left_gamma (N : ℕ) (g h : quotientNormalizerGroup N)
    (a : gamma N) (he : g.val=a.val*h.val) (x : AutomorphicSpace N) :
    quotientNormalizerPullback N g x=quotientNormalizerPullback N h x := by
  have hh : (fun x : AutomorphicSpace N => quotientNormalizerPullback N g x)=
      fun x => quotientNormalizerPullback N h x := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (quotientNormalizerPullback N g).continuous (quotientNormalizerPullback N h).continuous
    funext f
    change quotientNormalizerPullback N g (AutomorphicL2.denseEmbedding _ _ f)=
      quotientNormalizerPullback N h (AutomorphicL2.denseEmbedding _ _ f)
    rw [quotientNormalizerPullback_representative,quotientNormalizerPullback_representative]
    congr 1
    apply Subtype.ext
    funext z
    change f.val (g.val • z)=f.val (h.val • z)
    rw [he,mul_smul]
    exact f.property.2.1 a (h.val • z)
  exact congrFun hh x

/-- Every elementary generator squares to a congruence transformation,
including the half translation and composite exact Atkin divisors. -/
theorem admissibleGenerator_square_mem (N : ℕ) (hN : 0<N) (i : admissibleGeneratorIndex N hN) :
    i.val*i.val∈gamma N := by
  obtain ⟨g,hg⟩ := i
  change g*g∈gamma N
  cases hg with
  | fricke => rw [frickeLabel_mul_self]; exact (gamma N).one_mem
  | half h4 =>
    rw [translationLabel_mul]
    norm_num
    exact translation_mem N 1
  | atkin D Q hQ A B hAB hQD =>
    have hD : 0<D := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hzero : N=0 := by simpa only [hz,mul_zero] using hQD.symm
      exact hN.ne' hzero
    rw [exactAtkinLabel_eq_localAtkin D Q hD hQ A B hAB]
    simpa only [hQD] using localAtkin_square_mem D Q hD hQ A B hAB

/-- The elementary normalizers act as genuine involutions on all completed vectors. -/
theorem admissibleGeneratorPullback_involutive (N : ℕ) (hN : 0<N)
    (i : admissibleGeneratorIndex N hN) :
    Function.Involutive (quotientNormalizerPullback N (admissibleGeneratorLift N hN i)) := by
  intro x
  rw [←quotientNormalizerPullback_mul]
  exact quotientNormalizerPullback_gamma N _ (admissibleGenerator_square_mem N hN i) x

/-- A nonzero joint eigenvector forces every generator eigenvalue to
be a sign; arbitrary unit complex phases are not additional sectors. -/
theorem completedGeneratorSpace_eigenvalue_sign (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (x : AutomorphicSpace N)
    (hx : x∈completedGeneratorSpace N hN χ) (hx0 : x≠0) (i : admissibleGeneratorIndex N hN) :
    χ i=1 ∨ χ i= -1 := by
  have hh := admissibleGeneratorPullback_involutive N hN i x
  rw [hx i,map_smul,hx i,smul_smul] at hh
  have hs : χ i*χ i=1 := (smul_left_injective ℂ hx0) (hh.trans (one_smul ℂ x).symm)
  exact sq_eq_one_iff.mp (by simpa only [pow_two] using hs)

#print axioms quotientNormalizerPullback_left_gamma
#print axioms completedGeneratorSpace_eigenvalue_sign
#print axioms quotientNormalizerPullback_gamma
#print axioms admissibleGenerator_square_mem
#print axioms admissibleGeneratorPullback_involutive

end QuantitativeMaass
