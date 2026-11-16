module

public import QuantitativeMaassExactAtkinLabelV1
public import QuantitativeMaassReflectionOperatorV1
public import QuantitativeMaassCompletedLocalAtkinV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix UpperHalfPlane AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open AsymptoticCongruenceLabels AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open QuantitativeNewGap
open scoped MatrixGroups
namespace QuantitativeMaass

/-- Reflection of an exact Atkin representative differs by a literal
level-congruence matrix. -/
theorem exactAtkin_reflection_action (D Q : ℕ) (hQ : 0<Q) (A B : ℤ)
    (hAB : (Q:ℤ)*A+(D:ℤ)*B=1) :
    ∃ γ : gamma (Q*D),∀ z : ℍ,
      J • (exactAtkinLabel D Q hQ A B hAB • z)=
        γ • (exactAtkinLabel D Q hQ A B hAB • (J • z)) := by
  have hc : (Q:ℤ)*1*A-(D:ℤ)*(-B)*1=1 := by nlinarith [hAB]
  let C := exactAtkinComparison D Q A B 1 (-B) 1 A hAB hc
  have hC := exactAtkinComparison_mem D Q A B 1 (-B) 1 A hAB hc
  have hm := exactAtkinComparison_mul D Q A B 1 (-B) 1 A hAB hc
  let γ : gamma (Q*D) := ⟨integralLabel C,Subgroup.mem_map.mpr ⟨C,hC,rfl⟩⟩
  refine ⟨γ,?_⟩
  have hmat : J*realMatrix (exactAtkinGL D Q hQ A B hAB)=
      SpecialLinearGroup.mapGL ℝ C*realMatrix (exactAtkinGL D Q hQ A B hAB)*J := by
    apply Units.ext
    change J.val*(realMatrix (exactAtkinGL D Q hQ A B hAB)).val=
      (SpecialLinearGroup.mapGL ℝ C).val*(realMatrix (exactAtkinGL D Q hQ A B hAB)).val*J.val
    rw [exactAtkinGL_real_val]
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => (M i j : ℝ)) hm
    change ((C.val*exactAtkinMatrix D Q A B) i j : ℝ)=_ at hh
    fin_cases i <;> fin_cases j <;>
      simp [J,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two,
        exactAtkinMatrix] at hh ⊢ <;> nlinarith
  intro z
  change J • (exactAtkinLabel D Q hQ A B hAB • z)=
    integralLabel C • (exactAtkinLabel D Q hQ A B hAB • (J • z))
  rw [integralLabel_action]
  simp only [exactAtkinLabel,ofMatrix_action]
  have he := congrArg (fun g : GL (Fin 2) ℝ => g • z) hmat
  change J • (realMatrix (exactAtkinGL D Q hQ A B hAB) • z)=
    SpecialLinearGroup.mapGL ℝ C • (realMatrix (exactAtkinGL D Q hQ A B hAB) • (J • z))
  simpa only [mul_smul] using he

/-- A congruence identity on points extends to commutation of the actual
normalizer pullback and reflection on the completed quotient. -/
theorem quotientNormalizer_reflection_commute (N : ℕ) (g : quotientNormalizerGroup N)
    (γ : gamma N) (hγ : ∀ z : ℍ,J • (g.val • z)=γ • (g.val • (J • z))) :
    Commute (reflectionIsometry N).toContinuousLinearMap
      (quotientNormalizerPullback N g).toContinuousLinearMap := by
  have he : (fun x : AutomorphicSpace N => reflectionIsometry N (quotientNormalizerPullback N g x))=
      fun x => quotientNormalizerPullback N g (reflectionIsometry N x) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      ((reflectionIsometry N).continuous.comp (quotientNormalizerPullback N g).continuous)
      ((quotientNormalizerPullback N g).continuous.comp (reflectionIsometry N).continuous)
    funext f
    simp only [Function.comp_apply,quotientNormalizerPullback_representative,reflectionIsometry_apply]
    apply congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
    apply Subtype.ext
    funext z
    change f.val (g.val • (J • z))=f.val (J • (g.val • z))
    rw [hγ]
    exact (f.property.2.1 γ _).symm
  apply ContinuousLinearMap.ext
  intro x
  exact congrFun he x


/-- The canonical simple-prime Atkin action commutes with geometric
reflection on the actual completed automorphic Hilbert space. -/
theorem completedLocalAtkin_reflection_commute (N : ℕ) (hN : 0<N) (p : SimplePrime N) :
    Commute (reflectionIsometry N).toContinuousLinearMap
      (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p)).toContinuousLinearMap := by
  obtain ⟨γ,hγ⟩ := exactAtkin_reflection_action (N/p.val) p.val (simplePrime_prime p).pos
    (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)
  have hlevel : p.val*(N/p.val)=N := Nat.mul_div_cancel' (simplePrime_dvd p)
  let δ : gamma N := ⟨γ.val,by simpa only [hlevel] using γ.property⟩
  have he : exactAtkinLabel (N/p.val) p.val (simplePrime_prime p).pos
      (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)=
      localAtkinLabel N hN p :=
    exactAtkinLabel_eq_localAtkin (N/p.val) p.val (simplePrime_colevel_pos N hN p)
      (simplePrime_prime p).pos _ _ (simplePrime_bezout N p)
  apply quotientNormalizer_reflection_commute N (completedLocalAtkinNormalizer N hN p) δ
  intro z
  change J • (localAtkinLabel N hN p • z)=γ.val • (localAtkinLabel N hN p • (J • z))
  rw [←he]
  exact hγ z

#print axioms completedLocalAtkin_reflection_commute
#print axioms exactAtkin_reflection_action
#print axioms quotientNormalizer_reflection_commute
end QuantitativeMaass
