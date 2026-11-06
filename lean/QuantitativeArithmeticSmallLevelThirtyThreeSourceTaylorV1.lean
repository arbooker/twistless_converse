module
public import QuantitativeArithmeticSmallLevelThirtyThreeSourceGeometryV1
public import QuantitativeArithmeticSmallLevelThirtyThreeRawTaylorV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix UpperHalfPlane SmallLevelOriginal SmallLevelNormalized
open FinitenessOriginalInput FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set
open scoped MatrixGroups ModularForm

def sourceRate (i : Fin 223) (r : ℝ) : ℝ :=
  ((sourceMatrix i 1 0:ℝ)*r+(sourceMatrix i 1 1:ℝ))^2/((sourceMatrix i).det:ℝ)

def sourceDerivative (i : Fin 223) (r : ℝ) : ℝ :=
  (sourceMatrix i 1 0:ℝ)*((sourceMatrix i 1 0:ℝ)*r+(sourceMatrix i 1 1:ℝ))/((sourceMatrix i).det:ℝ)

def sourcePartner (i : Fin 223) (r : ℝ) : ℝ :=
  ((sourceMatrix i 0 0:ℝ)*r+(sourceMatrix i 0 1:ℝ))/
    ((sourceMatrix i 1 0:ℝ)*r+(sourceMatrix i 1 1:ℝ))

/-- All 223 source matrices have original-input Taylor expansions of every
order, with the same physical Fricke sign as the Ramanujan rows. -/
theorem source_taylor_of_fricke (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ} (hf : IsSolution 33 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] (fricke 33 (by decide))=η • fourierFunction (2*m) f)
    (i : Fin 223) (r : ℝ) (hr : (sourceMatrix i 1 0:ℝ)*r+(sourceMatrix i 1 1:ℝ)≠0) :
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        original (2*m) f r s-character η (root 33 f 3) (sourceWord i)*
          (sourceRate i r:ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*(sourceDerivative i r:ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            original (2*m) f (sourcePartner i r) (s+(n:ℂ)))=error M s := by
  have hc : (value (sourceWord i)).val=
      (wordScale (sourceWord i)*(sourceScale i:ℝ)) •
        !![(sourceMatrix i 0 0:ℝ),(sourceMatrix i 0 1:ℝ);
           (sourceMatrix i 1 0:ℝ),(sourceMatrix i 1 1:ℝ)] := by
    rw [source_coordinates]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  have hd : (sourceMatrix i 0 0:ℝ)*(sourceMatrix i 1 1:ℝ)-
      (sourceMatrix i 0 1:ℝ)*(sourceMatrix i 1 0:ℝ)=((sourceMatrix i).det:ℝ) := by
    simp only [det_fin_two,Int.cast_sub,Int.cast_mul]
  have hC : (sourceMatrix i 1 0:ℝ)≠0 := by exact_mod_cast source_nonaffine i
  have hpos : 0<(sourceMatrix i 0 0:ℝ)*(sourceMatrix i 1 1:ℝ)-
      (sourceMatrix i 0 1:ℝ)*(sourceMatrix i 1 0:ℝ) := by
    rw [hd]
    exact_mod_cast source_det_pos i
  have hh:=raw_word_taylor_of_fricke m hm hf hη hW (sourceWord i)
    (sourceMatrix i 0 0) (sourceMatrix i 0 1) (sourceMatrix i 1 0) (sourceMatrix i 1 1)
    (wordScale (sourceWord i)*(sourceScale i:ℝ)) r hc hC hpos hr
  simpa only [hd,sourceRate,sourceDerivative,sourcePartner] using hh

#print axioms source_taylor_of_fricke
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
