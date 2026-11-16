module

public import QuantitativeMaassTwoProjectionSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Module QuantitativeArithmeticExceptionalOldSpace

namespace QuantitativeMaass

/-- Exact trace of an affine polynomial in a symmetric operator, using
its actual canonical orthonormal spectral basis. -/
theorem symmetric_affine_power_trace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric) (c : ℝ) (m : ℕ) :
    (LinearMap.trace ℂ E ((1-(c:ℂ) • S)^m)).re=
      ∑ i : Fin (finrank ℂ E),(1-c*hS.eigenvalues rfl i)^m := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (hS.eigenvectorBasis rfl).toBasis,
    ←LinearMap.toMatrix_pow,map_sub,map_smul,LinearMap.toMatrix_one,hS.toMatrix_eigenvectorBasis rfl]
  have hd : (1 : Matrix (Fin (finrank ℂ E)) (Fin (finrank ℂ E)) ℂ)-
      (c:ℂ) • Matrix.diagonal (fun i => (hS.eigenvalues rfl i:ℂ))=
      Matrix.diagonal (fun i => ((1-c*hS.eigenvalues rfl i:ℝ):ℂ)) := by
    ext i j
    by_cases hij : i=j <;> simp [hij,Complex.ofReal_sub,Complex.ofReal_mul]
  change ((1 - (c : ℂ) • Matrix.diagonal (fun i => (hS.eigenvalues rfl i : ℂ)))^m).trace.re = _
  rw [hd,Matrix.diagonal_pow]
  simp only [Matrix.trace_diagonal,Pi.pow_apply,Complex.re_sum,←Complex.ofReal_pow,Complex.ofReal_re]

#print axioms symmetric_affine_power_trace

/-- An actual finite-band polynomial trace bound with an exceptional-rank
error, replacing an unproved uniform positive spectral gap. -/
theorem low_rank_filter_trace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (heig : ∀ i,0≤hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤1)
    (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1) (m : ℕ) :
    (LinearMap.trace ℂ E ((1-S)^m)).re≤(finrank ℂ S.ker:ℝ)+
      (finrank ℂ (smallPositiveSpace hS δ):ℝ)+(1-δ)^m*(finrank ℂ E:ℝ) := by
  classical
  have htrace : (LinearMap.trace ℂ E ((1-S)^m)).re=
      ∑ i : Fin (finrank ℂ E),(1-hS.eigenvalues rfl i)^m := by
    simpa only [Complex.ofReal_one,one_smul,one_mul] using symmetric_affine_power_trace S hS 1 m
  rw [htrace,smallPositiveSpace_finrank_eq_card hS δ]
  have hk : Nat.card {i : Fin (finrank ℂ E) // hS.eigenvalues rfl i=0}=finrank ℂ S.ker := by
    have hh := hS.card_filter_eigenvalues_eq rfl (0:ℂ)
    rw [Module.End.eigenspace_zero] at hh
    simpa [Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  have hh := finite_low_spectrum_filter (hS.eigenvalues rfl) heig δ hδ hδ1 m
  simpa only [hk,Fintype.card_fin] using hh

/-- The version for a sum of two projections uses the actual interval
[0,2] and scales the operator by one half. -/
theorem half_low_rank_filter_trace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric)
    (heig : ∀ i,0≤hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤2)
    (δ : ℝ) (hδ : 0≤δ) (hδ2 : δ≤2) (m : ℕ) :
    (LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re≤(finrank ℂ S.ker:ℝ)+
      (finrank ℂ (smallPositiveSpace hS δ):ℝ)+(1-δ/2)^m*(finrank ℂ E:ℝ) := by
  classical
  have htrace : (LinearMap.trace ℂ E ((1-(1/2:ℂ) • S)^m)).re=
      ∑ i : Fin (finrank ℂ E),(1-hS.eigenvalues rfl i/2)^m := by
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,div_mul_eq_mul_div,one_mul]
      using symmetric_affine_power_trace S hS (1/2) m
  rw [htrace,smallPositiveSpace_finrank_eq_card hS δ]
  have hk : Nat.card {i : Fin (finrank ℂ E) // hS.eigenvalues rfl i=0}=finrank ℂ S.ker := by
    have hh := hS.card_filter_eigenvalues_eq rfl (0:ℂ)
    rw [Module.End.eigenspace_zero] at hh
    simpa [Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  have hh := finite_low_spectrum_filter (fun i => hS.eigenvalues rfl i/2)
    (fun i => by constructor <;> linarith only [(heig i).1,(heig i).2]) (δ/2)
    (by positivity) (by linarith only [hδ2]) m
  have hz (i : Fin (finrank ℂ E)) : hS.eigenvalues rfl i/2=0 ↔ hS.eigenvalues rfl i=0 := by
    constructor <;> intro h <;> linarith only [h]
  have hs (i : Fin (finrank ℂ E)) :
      (0<hS.eigenvalues rfl i/2 ∧ hS.eigenvalues rfl i/2≤δ/2) ↔
      (0<hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤δ) := by
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith only [ha,hb]
  simpa only [hz,hs,hk,Fintype.card_fin] using hh

/-- Polynomial approximation to the common kernel of two actual
orthogonal projections, with only a small-positive-rank error. -/
theorem two_projection_filter_trace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (P Q : E →ₗ[ℂ] E) (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q)
    (δ : ℝ) (hδ : 0≤δ) (hδ2 : δ≤2) (m : ℕ) :
    (LinearMap.trace ℂ E ((1-(1/2:ℂ) • (P+Q))^m)).re≤
      (finrank ℂ ↥(P.ker ⊓ Q.ker):ℝ)+
      (finrank ℂ (smallPositiveSpace (hP.add hQ) δ):ℝ)+(1-δ/2)^m*(finrank ℂ E:ℝ) := by
  have hh := half_low_rank_filter_trace (P+Q) (hP.add hQ)
    (two_projection_spectrum_bounds P Q hP hQ hPP hQQ) δ hδ hδ2 m
  rw [two_projection_kernel P Q hP hQ hPP hQQ] at hh
  exact hh

#print axioms half_low_rank_filter_trace
#print axioms two_projection_filter_trace

#print axioms low_rank_filter_trace

end QuantitativeMaass
