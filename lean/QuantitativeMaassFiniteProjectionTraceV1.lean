module

public import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open scoped InnerProductSpace

namespace QuantitativeMaass

/-- The sum of squared projected basis norms is exactly the dimension of
the range of a genuine finite-dimensional orthogonal projection. -/
theorem finite_projection_energy_eq_finrank {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (b : OrthonormalBasis ι ℂ H) (P : H →ₗ[ℂ] H)
    (hp : IsIdempotentElem P) (hs : P.IsSymmetric) :
    (∑ i,‖P (b i)‖^2)=(Module.finrank ℂ (LinearMap.range P):ℝ) := by
  have ht := (LinearMap.IsIdempotentElem.isProj_range P hp).trace
  rw [LinearMap.trace_eq_sum_inner P b] at ht
  have hre := congrArg Complex.re ht
  simp only [Complex.re_sum,Complex.natCast_re] at hre
  have he (i : ι) : (inner ℂ (b i) (P (b i))).re=‖P (b i)‖^2 := by
    have hh := hs (b i) (P (b i))
    have hid : P (P (b i))=P (b i) := DFunLike.congr_fun hp (b i)
    rw [hid] at hh
    have hn : (inner ℂ (P (b i)) (P (b i))).re=‖P (b i)‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) _
    exact (congrArg Complex.re hh).symm.trans hn
  simpa only [he] using hre

/-- Any diagonal dominated by the orthogonal projection energy is bounded
by the actual finite range dimension. -/
theorem finite_projection_weight_le_finrank {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (b : OrthonormalBasis ι ℂ H) (P : H →ₗ[ℂ] H)
    (hp : IsIdempotentElem P) (hs : P.IsSymmetric)
    (w : ι → ℝ) (hw : ∀ i,w i≤‖P (b i)‖^2) :
    (∑ i,w i)≤(Module.finrank ℂ (LinearMap.range P):ℝ) := by
  rw [← finite_projection_energy_eq_finrank b P hp hs]
  exact Finset.sum_le_sum (fun i _ => hw i)

/-- Complementary finite projections split the ambient dimension exactly. -/
theorem finite_complementary_projection_finrank {H : Type*} [AddCommGroup H]
    [Module ℂ H] [FiniteDimensional ℂ H] (P Q : H →ₗ[ℂ] H)
    (hp : IsIdempotentElem P) (hq : IsIdempotentElem Q) (hsum : P+Q=1) :
    Module.finrank ℂ (LinearMap.range P)+Module.finrank ℂ (LinearMap.range Q)=Module.finrank ℂ H := by
  have hh := congrArg (LinearMap.trace ℂ H) hsum
  rw [map_add,(LinearMap.IsIdempotentElem.isProj_range P hp).trace,
    (LinearMap.IsIdempotentElem.isProj_range Q hq).trace,LinearMap.trace_one] at hh
  exact_mod_cast hh

#print axioms finite_complementary_projection_finrank

#print axioms finite_projection_energy_eq_finrank
#print axioms finite_projection_weight_le_finrank

end QuantitativeMaass
