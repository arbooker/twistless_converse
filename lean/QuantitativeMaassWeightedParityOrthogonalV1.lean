module

public import QuantitativeMaassWeightedCuspMeanV1
public import QuantitativeMaassCylinderEulerZeroModeV1
public import QuantitativeMaassEulerLevelOneParityV1
public import QuantitativeMaassCanonicalParitySpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticClassicalPetersson
open AsymptoticCongruenceStrip

namespace QuantitativeMaass

theorem cappedHeightWeight_reflection (ε : ℝ) (v : ℕ) (z : ℍ) :
    cappedHeightWeight ε v (J•z)=cappedHeightWeight ε v z := by
  simp only [cappedHeightWeight, UpperHalfPlane.im, coe_J_smul,
    Complex.neg_im, Complex.conj_im, neg_neg]

/-- Reflection commutes with the actual weighted quotient-to-cylinder map.
The assertion is proved first on invariant representatives, then by density. -/
theorem weightedQuotientEmbedding_reflection (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (x : AutomorphicSpace N) :
    reflectionIsometry 0 (cylinderAutomorphic (weightedQuotientEmbedding N hε hv x))=
      cylinderAutomorphic (weightedQuotientEmbedding N hε hv (reflectionIsometry N x)) := by
  have hh : (fun x => reflectionIsometry 0
      (cylinderAutomorphic (weightedQuotientEmbedding N hε hv x)))=
      (fun x => cylinderAutomorphic (weightedQuotientEmbedding N hε hv (reflectionIsometry N x))) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      ((reflectionIsometry 0).continuous.comp
        (cylinderAutomorphic.continuous.comp (weightedQuotientEmbedding N hε hv).continuous))
      (cylinderAutomorphic.continuous.comp
        ((weightedQuotientEmbedding N hε hv).continuous.comp (reflectionIsometry N).continuous))
    funext f
    dsimp only [Function.comp_apply]
    rw [weightedQuotientEmbedding_representative, ←weightedCylinderRepresentative_class,
      reflectionIsometry_apply, reflectionIsometry_apply,
      weightedQuotientEmbedding_representative, ←weightedCylinderRepresentative_class]
    apply congrArg (AutomorphicL2.denseEmbedding (gamma 0) (quotientMeasure 0))
    apply Subtype.ext
    funext z
    change (cappedHeightWeight ε v (J•z):ℂ)*f.val (J•z)=
      (cappedHeightWeight ε v z:ℂ)*f.val (J•z)
    rw [cappedHeightWeight_reflection]
  exact congrFun hh x

/-- The original Euler cylinder vector has its prescribed geometric parity
at every level, before any modularity conclusion is made. -/
theorem principalEulerCylinder_reflection {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ→ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    reflectionIsometry 0 (cylinderAutomorphic (principalEulerCylinderLp hN A P r σ hb))=
      (-1:ℂ)^σ • cylinderAutomorphic (principalEulerCylinderLp hN A P r σ hb) := by
  rw [←principalEulerCylinderRepresentative_class, reflectionIsometry_apply, ←map_smul]
  apply congrArg (AutomorphicL2.denseEmbedding (gamma 0) (quotientMeasure 0))
  apply Subtype.ext
  funext z
  change AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0
      (principalEulerPhysical b r σ) (J•z)=
    (-1:ℂ)^σ * AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0
      (principalEulerPhysical b r σ) z
  rw [weighted_zero_eq_capped, weighted_zero_eq_capped,
    cappedHeightWeight_reflection, principalEulerPhysical_reflection]
  ring

theorem reflection_opposite_inner_zero (N : ℕ) (η : ℝ) (hη : η^2=1)
    (u v : AutomorphicSpace N)
    (hu : reflectionIsometry N u=(η:ℂ) • u)
    (hv : reflectionIsometry N v=(-η:ℂ) • v) : inner ℂ u v=0 := by
  have hh := (reflectionIsometry N).inner_map_map u v
  rw [hu,hv] at hh
  rw [@inner_smul_left ℂ (AutomorphicSpace N) _ _ _ u ((-η:ℂ) • v) (η:ℂ),
    @inner_smul_right ℂ (AutomorphicSpace N) _ _ _ u v (-η:ℂ)] at hh
  simp only [Complex.conj_ofReal] at hh
  have hp : (η:ℂ)*(-η:ℂ)=-1 := by
    have h : (η:ℂ)^2=1 := by exact_mod_cast hη
    calc
      (η:ℂ)*(-η:ℂ)=-((η:ℂ)^2) := by ring
      _=-1 := by rw [h]
  rw [←mul_assoc,hp,neg_one_mul] at hh
  linear_combination -(1/2:ℂ)*hh

/-- Opposite canonical parity is exactly orthogonal to the original Euler
vector in the same weighted cylinder metric. -/
theorem principalEulerCylinder_orthogonal_opposite {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ→ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (x : AutomorphicSpace N) (hx : x∈completedParitySpace N (-((-1:ℝ)^σ))) :
    inner ℂ (principalEulerCylinderLp hN A P r σ hb)
      (weightedQuotientEmbedding N P.epsilon_pos (show 1≤P.s+3 by omega) x)=0 := by
  have hη : ((-1:ℝ)^σ)^2=1 := by rw [pow_right_comm]; norm_num
  have hu : reflectionIsometry 0 (cylinderAutomorphic (principalEulerCylinderLp hN A P r σ hb))=
      (((-1:ℝ)^σ:ℝ):ℂ) • cylinderAutomorphic (principalEulerCylinderLp hN A P r σ hb) := by
    simpa only [Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one] using
      principalEulerCylinder_reflection hN A P r σ hb
  have hv : reflectionIsometry N x= -Complex.ofReal ((-1:ℝ)^σ) • x := by
    have hp := parityProjection_eigen N (-((-1:ℝ)^σ)) (by simpa only [neg_sq] using hη) x
    rw [(mem_completedParitySpace N _ x).mp hx] at hp
    simpa only [Complex.ofReal_neg] using hp
  have hv' : reflectionIsometry 0
      (cylinderAutomorphic (weightedQuotientEmbedding N P.epsilon_pos (show 1≤P.s+3 by omega) x))=
      (-Complex.ofReal ((-1:ℝ)^σ)) •
        cylinderAutomorphic (weightedQuotientEmbedding N P.epsilon_pos (show 1≤P.s+3 by omega) x) := by
    rw [weightedQuotientEmbedding_reflection,hv,map_smul,map_smul]
  simpa only [cylinderAutomorphic.inner_map_map] using
    reflection_opposite_inner_zero 0 ((-1:ℝ)^σ) hη _ _ hu hv'

#print axioms weightedQuotientEmbedding_reflection
#print axioms principalEulerCylinder_reflection
#print axioms reflection_opposite_inner_zero
#print axioms principalEulerCylinder_orthogonal_opposite

end QuantitativeMaass
