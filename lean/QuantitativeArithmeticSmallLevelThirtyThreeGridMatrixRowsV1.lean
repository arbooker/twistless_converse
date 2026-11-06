module

public import QuantitativeArithmeticSmallLevelThirtyThreeGridGeometryRealV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessNormalizedTwistProduct
open SmallLevelAdditive Complex Set
open scoped MatrixGroups ModularForm

def gridMatrixScalar (m : ℕ) (f : ℕ→ℂ) (η : ℂ) (i : Fin 588) (n : ℕ) (s : ℂ) : ℂ :=
  character η (root 33 f 3) (sourceWord (groupSource i))*(groupRate i:ℂ)^(s-(m:ℂ))*
    (Complex.I*(groupDerivative i:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

/-- The 588 selected matrix rows of the actual closed 66-grid system.
The leading term and every positive shift use the same grid coordinate. -/
theorem grid_matrix_rows_of_fricke (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ} (hf : IsSolution 33 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] (fricke 33 (by decide))=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (i : Fin 588) :
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        grid (2*m) f 66 ((groupIndex i:ℕ):ℤ) s-
          gridMatrixScalar m f η i 0 s*
            grid (2*m) f 66 (groupTarget i) s=
        error M s+∑ n∈Finset.range M,gridMatrixScalar m f η i (n+1) s*
          grid (2*m) f 66 (groupTarget i) (s+((n:ℂ)+1)) := by
  obtain ⟨B,error,hrows⟩:=source_taylor_of_fricke m hm hf hη hW
    (groupSource i) (((groupIndex i:ℕ):ℝ)/66) (by
      simpa only [mul_div_assoc] using (group_geometry_real i).1)
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  refine ⟨?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_one] using (hrows (M+1)).1
  intro s hs
  have hh:=(hrows (M+1)).2 s hs
  rw [(group_geometry_real i).2.1] at hh
  rw [(group_geometry_real i).2.2.1,(group_geometry_real i).2.2.2.1,
    Finset.sum_range_succ'] at hh
  simp only [Complex.ofReal_ratCast,Nat.cast_zero,add_zero,pow_zero,
    Ring.choose_zero_right,one_mul,Nat.cast_add,Nat.cast_one] at hh
  simp only [gridMatrixScalar,Nat.cast_zero,add_zero,pow_zero,
    Ring.choose_zero_right,mul_one,Nat.cast_add,Nat.cast_one]
  rw [mul_add,Finset.mul_sum] at hh
  simp only [← mul_assoc] at hh
  simp only [grid,Int.cast_natCast,Nat.cast_ofNat] at hh ⊢
  linear_combination hh

#print axioms grid_matrix_rows_of_fricke
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
