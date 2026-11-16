module

public import QuantitativeMaassCompressedNewtonEnergyV1
public import QuantitativeMaassTargetProjectionApproxV1
public import QuantitativeHolomorphicNewtonTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open ContinuousLinearMap QuantitativeHolomorphic

namespace QuantitativeMaass

variable {V E F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Compression to an isometrically included subspace exactly intertwines
the extended ambient Gram and the genuine restricted Gram. -/
theorem extendedCompressedGram_restrict (R : E →L[ℂ] F) (J : V →L[ℂ] E)
    (hJ : J.adjoint.comp J=1) :
    ((R.comp J).adjoint.comp (R.comp J)).comp J.adjoint=
      J.adjoint.comp (extendedCompressedGram (R.adjoint.comp R) (J.comp J.adjoint)) := by
  have hj (v : V) : J.adjoint (J v)=v := congrArg (fun T : V →L[ℂ] V => T v) hJ
  ext x
  simp only [extendedCompressedGram,adjoint_comp,comp_apply,add_apply,sub_apply,
    mul_apply_eq_comp,one_apply_eq_self,map_add,map_sub,hj,sub_self,add_zero]

/-- The ambient polynomial is exactly the finite normalization of the
actual restricted embedding, followed by the adjoint inclusion. -/
theorem compressedNewtonPolynomial_transport (R : E →L[ℂ] F) (J : V →L[ℂ] E)
    (hJ : J.adjoint.comp J=1) (n : ℕ) :
    R.comp (compressedNewtonPolynomial (R.adjoint.comp R) (J.comp J.adjoint) n)=
      (polynomialNormalizedReconstruction (R.comp J) n).comp J.adjoint := by
  have hp := real_polynomial_intertwines
    (extendedCompressedGram (R.adjoint.comp R) (J.comp J.adjoint))
    ((R.comp J).adjoint.comp (R.comp J)) J.adjoint
    (extendedCompressedGram_restrict R J hJ) (inverseSqrtPolynomial n)
  ext x
  have hh := congrArg (fun T : E →L[ℂ] V => T x) hp
  change Polynomial.aeval ((R.comp J).adjoint.comp (R.comp J)) (inverseSqrtPolynomial n)
    (J.adjoint x)=J.adjoint (Polynomial.aeval
      (extendedCompressedGram (R.adjoint.comp R) (J.comp J.adjoint)) (inverseSqrtPolynomial n) x) at hh
  change R (J (J.adjoint (Polynomial.aeval
    (extendedCompressedGram (R.adjoint.comp R) (J.comp J.adjoint)) (inverseSqrtPolynomial n) x)))=
      R (J (Polynomial.aeval ((R.comp J).adjoint.comp (R.comp J))
        (inverseSqrtPolynomial n) (J.adjoint x)))
  rw [hh]

/-- The cogram of the extended polynomial approximates the orthogonal
projection onto the actual observed subspace, with the previously proved
uniform Newton error. -/
theorem compressedNewtonPolynomial_target_error (R : E →L[ℂ] F) (J : V →L[ℂ] E)
    (hJ : J.adjoint.comp J=1) [CompleteSpace (R.comp J).range]
    {κ : ℝ} (hκ : 0<κ) (hκ1 : κ≤1)
    (hR : ∀ v,κ*‖v‖^2≤‖(R.comp J) v‖^2) (hn : ‖R.comp J‖≤1) (n : ℕ) :
    let A := R.comp (compressedNewtonPolynomial (R.adjoint.comp R) (J.comp J.adjoint) n)
    ‖A.comp A.adjoint-(R.comp J).range.starProjection‖≤
      2*((1-κ)^(2^n)/Real.sqrt κ)+((1-κ)^(2^n)/Real.sqrt κ)^2 := by
  dsimp only
  rw [compressedNewtonPolynomial_transport R J hJ n,adjoint_comp,adjoint_adjoint]
  have he : ((polynomialNormalizedReconstruction (R.comp J) n).comp J.adjoint).comp
      (J.comp (polynomialNormalizedReconstruction (R.comp J) n).adjoint)=
      (polynomialNormalizedReconstruction (R.comp J) n).comp
        (polynomialNormalizedReconstruction (R.comp J) n).adjoint := by
    ext x
    have hj (v : V) : J.adjoint (J v)=v := congrArg (fun T : V →L[ℂ] V => T v) hJ
    simp only [comp_apply,hj]
  rw [he]
  exact (polynomial_embedding_projection_error (R.comp J) hκ hκ1 hR hn n).trans_eq (by ring)

#print axioms extendedCompressedGram_restrict
#print axioms compressedNewtonPolynomial_transport
#print axioms compressedNewtonPolynomial_target_error

end QuantitativeMaass
