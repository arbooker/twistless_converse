module

public import QuantitativeArithmeticSmallLevelThirtyFiveKnownWordFourierV1
public import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Matrix SmallLevelNormalized
open scoped MatrixGroups

/-- Integral seed representatives; the Fricke representative has determinant35. -/
def rawSeed (i : Fin 5) : Matrix (Fin 2) (Fin 2) ℝ :=
  if i=4 then !![0,-1;35,0] else (seed i).val

def seedScale (i : Fin 5) : ℝ := if i=4 then (Real.sqrt 35)⁻¹ else 1

/-- Adjugation represents projective inversion without introducing any
rational denominators. -/
def raw : Word → Matrix (Fin 2) (Fin 2) ℝ
  | .one => 1
  | .generator i => rawSeed i
  | .mul u v => raw u*raw v
  | .inv w => (raw w).adjugate

def wordScale : Word → ℝ
  | .one => 1
  | .generator i => seedScale i
  | .mul u v => wordScale u*wordScale v
  | .inv w => wordScale w

theorem seedScale_pos (i : Fin 5) : 0<seedScale i := by
  unfold seedScale
  split
  · exact inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  · norm_num

theorem wordScale_pos (w : Word) : 0<wordScale w := by
  induction w with
  | one => norm_num [wordScale]
  | generator i => exact seedScale_pos i
  | mul u v hu hv => exact mul_pos hu hv
  | inv w hw => exact hw

theorem seed_raw (i : Fin 5) : (seed i).val=seedScale i • rawSeed i := by
  by_cases hi : i=4
  · subst i
    have hs : (Real.sqrt (35:ℝ))^2=35 := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt (35:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [seed,seedScale,rawSeed,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.smul_apply,smul_eq_mul]
    · simp only [div_eq_mul_inv,neg_mul,one_mul]
    · calc
        Real.sqrt 35 = (Real.sqrt 35)⁻¹*(Real.sqrt 35*Real.sqrt 35) := by
          rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]
        _ = (Real.sqrt 35)⁻¹*35 := by rw [← pow_two,hs]
  · simp [seedScale,rawSeed,hi]

theorem inverse_val_adjugate (g : GL (Fin 2) ℝ)
    (hg : (GeneralLinearGroup.det g:ℝ)=1) : g⁻¹.val=g.val.adjugate := by
  have hdet : g.val.det=1 := hg
  have ha : g.val*g.val.adjugate=1 := by
    rw [Matrix.mul_adjugate,hdet,one_smul]
  calc
    g⁻¹.val = g⁻¹.val*1 := by rw [Matrix.mul_one]
    _ = g⁻¹.val*(g.val*g.val.adjugate) := by rw [ha]
    _ = g.val.adjugate := by rw [← Matrix.mul_assoc,Units.inv_mul,Matrix.one_mul]

/-- Actual normalized matrix values equal positive scalars times the
integer projective representatives, for arbitrary words and inverses. -/
theorem value_raw (w : Word) : (value w).val=wordScale w • raw w := by
  induction w with
  | one => simp [value,wordScale,raw]
  | generator i => exact seed_raw i
  | mul u v hu hv =>
    change (value u).val*(value v).val=(wordScale u*wordScale v) • (raw u*raw v)
    rw [hu,hv,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  | inv w hw =>
    change (value w)⁻¹.val=wordScale w • (raw w).adjugate
    rw [inverse_val_adjugate _ (value_det w),hw,Matrix.adjugate_smul]
    simp

theorem raw_det_scale (w : Word) : (wordScale w)^2*(raw w).det=1 := by
  have hd : (value w).val.det=1 := value_det w
  rw [value_raw,Matrix.det_smul] at hd
  simpa using hd

theorem raw_det_pos (w : Word) : 0<(raw w).det := by
  have hs := sq_pos_of_pos (wordScale_pos w)
  have hd := raw_det_scale w
  nlinarith

#print axioms seed_raw
#print axioms inverse_val_adjugate
#print axioms value_raw
#print axioms raw_det_scale
#print axioms raw_det_pos
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
