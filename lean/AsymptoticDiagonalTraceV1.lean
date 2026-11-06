module

public import AsymptoticObservationCompressionV1
public import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false

@[expose] public section

namespace AsymptoticDiagonalTrace

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct BigOperators ComplexConjugate

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The diagonal trace in a specified Hilbert basis. Summability is stated
explicitly in every bound using this real-valued sum. -/
noncomputable def trace (b : HilbertBasis ι ℂ H) (Q : H →L[ℂ] H) : ℝ :=
  ∑' i,(⟪Q (b i),b i⟫_ℂ).re

/-- A positive operator fixing W dominates the orthogonal projection onto W. -/
theorem projection_energy_le (Q : H →L[ℂ] H) (hQ : Q.IsPositive)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (hfix : ∀ w∈W,Q w=w) (x : H) :
    ‖W.starProjection x‖^2≤(⟪Q x,x⟫_ℂ).re := by
  let y := W.starProjection x
  let z := x-y
  have hyW : y∈W := (W.orthogonalProjectionOnto x).property
  have hy : Q y=y := hfix y hyW
  have hx : x=y+z := by dsimp [z]; abel
  have hzy : ⟪z,y⟫_ℂ=0 := W.starProjection_inner_eq_zero x y hyW
  have hyz : ⟪y,z⟫_ℂ=0 := by rw [← inner_conj_symm,hzy]; simp
  have hQzy : ⟪Q z,y⟫_ℂ=0 := by rw [hQ.inner_left_eq_inner_right,hy,hzy]
  have he : ⟪Q x,x⟫_ℂ=⟪y,y⟫_ℂ+⟪Q z,z⟫_ℂ := by
    calc
      ⟪Q x,x⟫_ℂ=⟪Q (y+z),y+z⟫_ℂ := by rw [← hx]
      _ = _ := by rw [map_add,hy,inner_add_left,inner_add_right,inner_add_right,hyz,hQzy]; simp
  have hpos : 0≤(⟪Q z,z⟫_ℂ).re := hQ.re_inner_nonneg_left z
  have hyy := norm_sq_eq_re_inner (𝕜:=ℂ) y
  change ‖y‖^2=(⟪y,y⟫_ℂ).re at hyy
  change ‖y‖^2≤(⟪Q x,x⟫_ℂ).re
  rw [he,Complex.add_re]
  linarith

/-- Parseval in the real nonnegative form used by the diagonal trace. -/
theorem hasSum_sq_inner (b : HilbertBasis ι ℂ H) (w : H) :
    HasSum (fun i => ‖⟪w,b i⟫_ℂ‖^2) (‖w‖^2) := by
  have hh := Complex.hasSum_re (b.hasSum_inner_mul_inner w w)
  have hnorm : (⟪w,w⟫_ℂ).re=‖w‖^2 := (norm_sq_eq_re_inner (𝕜:=ℂ) w).symm
  rw [hnorm] at hh
  convert hh using 1
  funext i
  change ‖⟪w,b i⟫_ℂ‖^2=RCLike.re (⟪w,b i⟫_ℂ*⟪b i,w⟫_ℂ)
  rw [inner_mul_symm_re_eq_norm,norm_mul,norm_inner_symm (b i) w]
  ring

/-- The diagonal trace of a finite-rank orthogonal projection is its rank,
in any Hilbert basis of the ambient space. -/
theorem projection_hasSum (b : HilbertBasis ι ℂ H) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] :
    HasSum (fun i => ‖W.starProjection (b i)‖^2) (Module.finrank ℂ W:ℝ) := by
  classical
  let u := stdOrthonormalBasis ℂ W
  have hu : ∀ j, ‖(u j:H)‖^2=1 := by
    intro j
    have hh : ‖(u j:H)‖=1 := u.orthonormal.norm_eq_one j
    rw [hh]
    norm_num
  have hsum : HasSum (fun i => ∑ j,‖⟪(u j:H),b i⟫_ℂ‖^2)
      (∑ j,‖(u j:H)‖^2) := hasSum_sum (fun j _ => hasSum_sq_inner b (u j:H))
  simp only [hu,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hsum
  convert hsum using 1
  funext i
  have he := u.sum_sq_norm_inner_right (W.orthogonalProjectionOnto (b i))
  simp only [W.inner_orthogonalProjectionOnto_eq_of_mem_left] at he
  exact he.symm

/-- The finite-dimensional one-eigenspace bound needed for the asymptotic
count. The trace is an actual summable diagonal, not a separate numerical
quantity assumed to dominate the dimension. -/
theorem finrank_le_trace (b : HilbertBasis ι ℂ H) (Q : H →L[ℂ] H)
    (hQ : Q.IsPositive) (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hfix : ∀ w∈W,Q w=w) (htrace : Summable (fun i => (⟪Q (b i),b i⟫_ℂ).re)) :
    (Module.finrank ℂ W:ℝ)≤trace b Q := by
  rw [← (projection_hasSum b W).tsum_eq]
  exact (projection_hasSum b W).summable.tsum_le_tsum
    (fun i => projection_energy_le Q hQ W hfix (b i)) htrace

#print axioms projection_energy_le
#print axioms projection_hasSum
#print axioms finrank_le_trace

end AsymptoticDiagonalTrace
