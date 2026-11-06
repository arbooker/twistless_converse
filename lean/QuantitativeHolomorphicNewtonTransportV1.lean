module

public import QuantitativeHolomorphicNewtonPerturbationV1
public import QuantitativeHolomorphicNewtonExpressionV1
public import QuantitativeHolomorphicCutNormalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap AsymptoticFiniteBranch

section Intertwining

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Polynomial transport is exact and does not require a spectral bound. -/
theorem real_polynomial_intertwines (M : E →L[ℂ] E) (N : F →L[ℂ] F)
    (S : E →L[ℂ] F) (hi : N.comp S = S.comp M) (p : Polynomial ℝ) :
    (Polynomial.aeval N p).comp S = S.comp (Polynomial.aeval M p) := by
  have hpoint (x : E) : N (S x) = S (M x) :=
    congrArg (fun T : E →L[ℂ] F => T x) hi
  have hp (j : ℕ) (x : E) : (N ^ j) (S x) = S ((M ^ j) x) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', pow_succ']
      change N ((N ^ j) (S x)) = S (M ((M ^ j) x))
      rw [ih, hpoint]
  apply ContinuousLinearMap.ext
  intro x
  simp only [polynomial_aeval_sum, comp_apply, sum_apply, smul_apply,
    map_sum, map_smul_of_tower, hp]

end Intertwining

section Isometries

variable {G E H : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient Gram polynomial equals the transported terminal Gram
polynomial, including its constant term on the ambient complement. -/
theorem polynomialNormalizedReconstruction_transport
    (S : G →L[ℂ] H) (hS : S.adjoint.comp S = 1)
    (L : E →L[ℂ] H) (hL : L.adjoint.comp L = 1) (V : G →L[ℂ] E) (n : ℕ) :
    polynomialNormalizedReconstruction (L.comp (V.comp S.adjoint)) n =
      L.comp ((polynomialNormalizedReconstruction V n).comp S.adjoint) := by
  let F := L.comp (V.comp S.adjoint)
  have hs (g : G) : S.adjoint (S g) = g := congrArg (fun T : G →L[ℂ] G => T g) hS
  have hl (e : E) : L.adjoint (L e) = e := congrArg (fun T : E →L[ℂ] E => T e) hL
  have hi : (V.adjoint.comp V).comp S.adjoint = S.adjoint.comp (F.adjoint.comp F) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [F, adjoint_comp, adjoint_adjoint, comp_apply, hl, hs]
  have hp := real_polynomial_intertwines (F.adjoint.comp F) (V.adjoint.comp V)
    S.adjoint hi (inverseSqrtPolynomial n)
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun T : H →L[ℂ] G => T x) hp
  change Polynomial.aeval (V.adjoint.comp V) (inverseSqrtPolynomial n) (S.adjoint x) =
    S.adjoint (Polynomial.aeval (F.adjoint.comp F) (inverseSqrtPolynomial n) x) at he
  change L (V (S.adjoint (Polynomial.aeval (F.adjoint.comp F) (inverseSqrtPolynomial n) x))) =
    L (V (Polynomial.aeval (V.adjoint.comp V) (inverseSqrtPolynomial n) (S.adjoint x)))
  rw [he]

/-- Isometric transport does not enlarge the proved approximation error. -/
theorem norm_isometric_transport_difference_le
    (S : G →L[ℂ] H) (hS : S.adjoint.comp S = 1)
    (L : E →L[ℂ] H) (hL : L.adjoint.comp L = 1) (V W : G →L[ℂ] E) :
    ‖L.comp (V.comp S.adjoint) - L.comp (W.comp S.adjoint)‖ ≤ ‖V - W‖ := by
  have hSn : ‖S.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    apply opNorm_le_bound _ zero_le_one
    intro g
    simpa only [one_mul] using ((norm_map_iff_adjoint_comp_self S).2 hS g).le
  have hLn : ‖L‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro g
    simpa only [one_mul] using ((norm_map_iff_adjoint_comp_self L).2 hL g).le
  rw [← comp_sub, ← sub_comp]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right hLn (norm_nonneg _)).trans
  rw [one_mul]
  exact (opNorm_comp_le _ _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hSn (norm_nonneg (V - W)))

end Isometries

/-- A finite branch expression for the reconstruction followed by the
Newton polynomial of its actual Gram operator. -/
def normalizedReconstructionExpression (e : Expression) (n : ℕ) : Expression :=
  composeExpression e (inverseSqrtExpression (composeExpression (adjointExpression e) e) n)

theorem holomorphicSum_normalizedReconstructionExpression (e : Expression) (n m : ℕ) :
    holomorphicSum (normalizedReconstructionExpression e n) m =
      polynomialNormalizedReconstruction (holomorphicSum e m) n := by
  rw [normalizedReconstructionExpression, holomorphicSum_compose,
    holomorphicSum_inverseSqrt, holomorphicSum_compose, holomorphicSum_adjoint]
  rfl

theorem regularSum_normalizedReconstructionExpression (e : Expression)
    (n : ℕ) (z : UpperHalfPlane) :
    regularSum (normalizedReconstructionExpression e n) z =
      polynomialNormalizedReconstruction (regularSum e z) n := by
  have hg : regularSum (composeExpression (adjointExpression e) e) z =
      (regularSum e z).adjoint.comp (regularSum e z) :=
    (regularSum_compose _ _ z).trans
      (congrArg (fun T => T.comp (regularSum e z)) (regularSum_adjoint e z))
  exact (regularSum_compose e _ z).trans
    (congrArg (fun T => (regularSum e z).comp T)
      ((regularSum_inverseSqrt _ n z).trans
        (congrArg (fun T => Polynomial.aeval T (inverseSqrtPolynomial n)) hg)))

theorem normalizedReconstructionExpression_complexity (e : Expression) (n : ℕ) :
    expressionBound (normalizedReconstructionExpression e n) ≤
      expressionBound e * (3 + expressionBound e ^ 2) ^ (4 ^ n) ∧
    (normalizedReconstructionExpression e n).length ≤
      e.length * (3 + e.length ^ 2) ^ (4 ^ n) := by
  constructor
  · rw [normalizedReconstructionExpression, expressionBound_compose]
    apply (mul_le_mul_of_nonneg_left (expressionBound_inverseSqrt_le _ n)
      (expressionBound_nonneg e)).trans_eq
    rw [expressionBound_compose, expressionBound_adjoint, pow_two]
  · rw [normalizedReconstructionExpression, length_composeExpression]
    apply (Nat.mul_le_mul_left e.length (length_inverseSqrt_le _ n)).trans_eq
    simp only [length_composeExpression, adjointExpression, List.length_map, pow_two]

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)

/-- The actual scaled compact reconstruction in the common branch language. -/
def scaledCutCountExpression (hN : 0 < N) (P : Parameters A) (e : Sector N)
    (Y : ℝ) (d J : ℕ) : Expression :=
  scaleExpression ((countReconstructionBound A P)⁻¹ : ℝ)
    (cutFullExpression A hN (AsymptoticReconstructedCount.parameters A P)
      (multiplier e) Y d (Finset.Icc (-(J : ℤ)) J))

theorem holomorphicSum_scaledCutCountExpression (hN : 0 < N) (P : Parameters A)
    (h : ℕ) (e : Sector N) (Y : ℝ) (d J : ℕ) :
    holomorphicSum (scaledCutCountExpression A hN P e Y d J) (h+1) =
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((scaledCutFiniteCountReconstruction A hN P h e Y d J).comp
          (AsymptoticCylinderTerminal.ambientLift
            (AsymptoticReconstructedCount.parameters A P).ε).adjoint) := by
  rw [scaledCutCountExpression, holomorphicSum_scale, holomorphicSum_cutFull_eq_cylinder]
  rw [scaledCutFiniteCountReconstruction, smul_comp, comp_smul]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (countReconstructionBound A P)⁻¹
    (AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
      ((AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d
        (Finset.Icc (-(J : ℤ)) J)).comp
          (AsymptoticCylinderTerminal.ambientLift
            (AsymptoticReconstructedCount.parameters A P).ε).adjoint))).symm

/-- Exact finite-branch realization of the polynomial normalization of the
literal counting reconstruction, after cylinder/terminal transport. -/
theorem holomorphicSum_normalizedCutCountExpression (hN : 0 < N) (P : Parameters A)
    (h n : ℕ) (e : Sector N) (Y : ℝ) (d J : ℕ) :
    holomorphicSum (normalizedReconstructionExpression
      (scaledCutCountExpression A hN P e Y d J) n) (h+1) =
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((polynomialNormalizedReconstruction
          (scaledCutFiniteCountReconstruction A hN P h e Y d J) n).comp
            (AsymptoticCylinderTerminal.ambientLift
              (AsymptoticReconstructedCount.parameters A P).ε).adjoint) := by
  rw [holomorphicSum_normalizedReconstructionExpression, holomorphicSum_scaledCutCountExpression]
  exact polynomialNormalizedReconstruction_transport _
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) _
    AsymptoticCylinderLift.lift.adjoint_comp_self _ n

/-- The finite common-branch expression approximates the exact normalized
counting map on the entire ambient Hilbert space, with all cutoffs explicit. -/
theorem normalizedCutCountExpression_ambient_error (hN : 0 < N) (P : Parameters A)
    (h n : ℕ) (e : Sector N) (Y : ℝ) (hY : 0 ≤ Y) (d J : ℕ) (hJ : 0 < J) :
    ‖holomorphicSum (normalizedReconstructionExpression
        (scaledCutCountExpression A hN P e Y d J) n) (h+1) -
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        ((normalizedCountReconstruction A hN P h e).comp
          (AsymptoticCylinderTerminal.ambientLift
            (AsymptoticReconstructedCount.parameters A P).ε).adjoint)‖ ≤
      cutCountReconstructionError A P Y d J * (1 + 3 * (3 ^ n : ℕ)) * (7 : ℝ) ^ (4 ^ n) +
        (1 - countGramLower A P) ^ (2 ^ n) / Real.sqrt (countGramLower A P) := by
  rw [holomorphicSum_normalizedCutCountExpression]
  exact (norm_isometric_transport_difference_le _
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) _
    AsymptoticCylinderLift.lift.adjoint_comp_self _ _).trans
      (cut_normalizedCountReconstruction_closed_error A hN P h n e Y hY d J hJ)

#print axioms normalizedCutCountExpression_ambient_error

#print axioms polynomialNormalizedReconstruction_transport
#print axioms normalizedReconstructionExpression_complexity
#print axioms holomorphicSum_normalizedCutCountExpression
#print axioms regularSum_normalizedReconstructionExpression

end QuantitativeHolomorphic
