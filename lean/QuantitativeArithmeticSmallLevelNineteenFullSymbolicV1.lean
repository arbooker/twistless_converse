module
public import QuantitativeArithmeticSmallLevelNineteenFullSystemTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenFullRamanujanTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenGridSystemTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullRamanujan
open Complex SmallLevelTaylor
open QuantitativeArithmeticSmallLevelNineteenGridSystem (primeParameter phaseRoot badNineteen)
open QuantitativeArithmeticSmallLevelNineteenFullGroup (primeParameter_shift)

def derivativeRate (i : Fin 96) : ℝ := (rowL i:ℝ)*(rowT i:ℝ)/114

theorem first_coefficient (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 96) :
    rowCoefficient (2*m) f ε i 1 (s-1)=I*(s-((2*m:ℕ):ℂ))*(derivativeRate i:ℂ)*
      symbolic (phaseRoot m ε) (badNineteen f)
        (primeParameter 2 m s/2) (primeParameter 3 m s/3) (primeParameter 19 m s/19) i := by
  have h0 := coefficient_laurent m f ε (s-1) i
  simp only [primeParameter_shift (by decide : 2≠0),
    primeParameter_shift (by decide : 3≠0),primeParameter_shift (by decide : 19≠0)] at h0
  norm_num only [Nat.cast_ofNat] at h0
  simp only [rowCoefficient,taylorRowScalar,pow_zero,Ring.choose_zero_right,mul_one] at h0
  simp only [rowCoefficient,taylorRowScalar,pow_one,Ring.choose_one_right,Nat.cast_one,sub_add_cancel]
  rw [← h0]
  unfold derivativeRate
  push_cast
  ring

end QuantitativeArithmeticSmallLevelNineteenFullRamanujan
namespace QuantitativeArithmeticSmallLevelNineteenFullSystem
open Complex
open QuantitativeArithmeticSmallLevelNineteenFullGroup
open QuantitativeArithmeticSmallLevelNineteenFullRamanujan
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic (gridIndex)
open QuantitativeArithmeticSmallLevelNineteenGridSystem
  (primeParameter primeParameter_inverse phaseRoot badNineteen symbolicHecke heckeRow_symbolic)

def symbolicHeckeRow (χ X Y Z a b : ℂ) (i : Fin 101) (v : Fin 114→ℂ) : ℂ :=
  if (QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).1=19 then
    (∑ j∈Finset.range 19, v (gridIndex
      (((QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).2+j*(114/19):ℕ):ℤ)))-
      χ/Z*v (gridIndex ((19*(QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).2:ℕ):ℤ))
  else symbolicHecke X Y a b (QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).1
    (QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).2 v

theorem actual_hecke_row (i : Fin 101) (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 114→ℂ) :
    QuantitativeArithmeticSmallLevelNineteenFullHecke.row i m f s v=
      symbolicHeckeRow (badNineteen f) (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 19 m s) ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) i v := by
  by_cases hp : (QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).1=19
  · simp only [QuantitativeArithmeticSmallLevelNineteenFullHecke.row,symbolicHeckeRow,hp,ite_true,
      QuantitativeArithmeticSmallLevelNineteenFullHecke.ramifiedRow,badNineteen,
      div_eq_mul_inv]
    have hinv := primeParameter_inverse 19 m s
    norm_num only [Nat.cast_ofNat] at hinv
    norm_num only [Nat.cast_ofNat]
    rw [hinv]
  · simp only [QuantitativeArithmeticSmallLevelNineteenFullHecke.row,symbolicHeckeRow,hp,ite_false]
    apply heckeRow_symbolic
    have hs : (QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).1=2 ∨
        (QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).1=3 ∨
        (QuantitativeArithmeticSmallLevelNineteenFullHecke.specs i).1=19 := by
      revert i
      decide
    tauto

def symbolicRows (χ δ X Y Z a b : ℂ) (v : Fin 114→ℂ) : Fin 734→ℂ :=
  assemble (fun i => v (gridIndex (source i))-
      QuantitativeArithmeticSmallLevelNineteenFullGroup.symbolic X Y Z i*v (gridIndex (partner i)))
    (fun i => plusRows v i-QuantitativeArithmeticSmallLevelNineteenFullRamanujan.symbolic χ δ X Y Z i*minusRows v i)
    (entireRows v) (fun i => v (gridIndex (centerGrid i)))
    (fun i => symbolicHeckeRow δ X Y Z a b i v)

def firstRows (χ δ X Y Z : ℂ) (v : Fin 114→ℂ) : Fin 734→ℂ :=
  assemble (fun i => (QuantitativeArithmeticSmallLevelNineteenFullGroup.derivativeRate i:ℂ)*
      QuantitativeArithmeticSmallLevelNineteenFullGroup.symbolic (X/2) (Y/3) (Z/19) i*v (gridIndex (partner i)))
    (fun i => (QuantitativeArithmeticSmallLevelNineteenFullRamanujan.derivativeRate i:ℂ)*
      QuantitativeArithmeticSmallLevelNineteenFullRamanujan.symbolic χ δ (X/2) (Y/3) (Z/19) i*minusRows v i) 0 0 0

theorem actual_leading_rows (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 114→ℂ) :
    leadingRows m f ε s v=symbolicRows (phaseRoot m ε) (badNineteen f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 19 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  funext i
  cases hi : rowKind i with
  | group j => simp only [leadingRows,symbolicRows,assemble,hi,
      QuantitativeArithmeticSmallLevelNineteenFullGroup.coefficient_laurent]
  | taylor j => simp only [leadingRows,symbolicRows,assemble,hi,
      QuantitativeArithmeticSmallLevelNineteenFullRamanujan.coefficient_laurent]
  | entire j => simp only [leadingRows,symbolicRows,assemble,hi]
  | center j => simp only [leadingRows,symbolicRows,assemble,hi]
  | hecke j => simp only [leadingRows,symbolicRows,assemble,hi,actual_hecke_row]

theorem actual_first_rows (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin 114→ℂ) :
    shiftRows m f ε 0 (s-1) v=
      (I*(s-((2*m:ℕ):ℂ))) • firstRows (phaseRoot m ε) (badNineteen f)
        (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 19 m s) v := by
  funext i
  cases hi : rowKind i <;>
    simp only [shiftRows,firstRows,assemble,hi,Nat.zero_add,
      QuantitativeArithmeticSmallLevelNineteenFullGroup.first_coefficient,
      QuantitativeArithmeticSmallLevelNineteenFullRamanujan.first_coefficient,
      Pi.smul_apply,smul_eq_mul,Pi.zero_apply] <;> ring

#print axioms actual_leading_rows
#print axioms actual_first_rows
end QuantitativeArithmeticSmallLevelNineteenFullSystem
