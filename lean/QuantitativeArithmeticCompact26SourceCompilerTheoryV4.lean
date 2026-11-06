module

public import QuantitativeArithmeticCompact26JetReductionV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import SmallLevelTwentySixGermDAGSourceDefinitionV1

/-! Consolidated chapter: QuantitativeArithmeticCompact26SourceCompiler. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticCompact26SourceCompilerBaseV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section

/-! UNVERIFIED draft. One symbolic compiler for the five original source
constructors, at the original fixed MMM signs. No stored row is consulted. -/
namespace QuantitativeArithmeticCompact26SourceCompiler
open QuantitativeArithmeticSevenLaurentRows
open SmallLevelTwentySixGermSources
open SmallLevelTwentySixGrid (gridWordSign gridBaseSign)

abbrev zeroExponent : Exponent := (0,0,0,0,0,0,0)

def point (r : ℚ) (e : Exponent) (j : Fin 780) : Poly :=
  [(r, SmallLevelTwentySixGermDAG.sourceCoordinate 0 j, e)]

def rangeTerms (r : ℚ) (e : Exponent) (index : ℕ → Fin 780)
    (keep : ℕ → Bool) : ℕ → Poly
  | 0 => []
  | n+1 => rangeTerms r e index keep n ++
      if keep n then point r e (index n) else []

def sample (q : ℕ) (t : ℤ) (r : ℚ) (e : Exponent) : Poly :=
  rangeTerms r e (fun j => gridIndex (t+(j:ℤ)*(780/q:ℕ)))
    (fun j => decide (Nat.Coprime j q)) q

def wordSign : List (Fin 4 × Bool) → ℚ
  | [] => 1
  | i :: w => (if i.1=3 then -1 else 1) * wordSign w

def fourExponent (e : ℤ×ℤ×ℤ×ℤ) : Exponent :=
  (e.1,e.2.1,e.2.2.1,e.2.2.2,0,0,0)

def wordRow (i : Fin 235) : Poly :=
  point 1 zeroExponent (gridGroupIndex i) ++
    point (-wordSign (sourceWord (gridGroupSource i)))
      (fourExponent (groupPowers i)) (gridGroupTarget i)

def taylorRow (i : Fin 53) : Poly :=
  sample (gridTaylorQ i) (gridTaylorT i) 1 zeroExponent ++
    sample (gridTaylorQ i) (gridTaylorPartner i) 1
      (fourExponent (taylorPowers i))

def inverseExponent (p n : ℕ) : Exponent :=
  (if p=2 then -(n:ℤ) else 0,
   if p=3 then -(n:ℤ) else 0,
   if p=13 then -(n:ℤ) else 0,
   if p=2 ∨ p=3 ∨ p=13 then 0 else -(n:ℤ),0,0,0)

def eigenInverseExponent (p : ℕ) : Exponent :=
  (if p=2 then -1 else 0,
   if p=3 then -1 else 0,
   if p=13 then -1 else 0,
   if p=2 ∨ p=3 ∨ p=13 then 0 else -1,
   if p=3 then 1 else 0,
   if p=2 ∨ p=3 ∨ p=13 then 0 else 1,0)

def heckeRow (i : Fin 96) : Poly :=
  rangeTerms 1 zeroExponent
    (fun j => gridIndex (gridHeckeT i+(j:ℤ)*(780/gridHeckeP i:ℕ)))
    (fun _ => true) (gridHeckeP i) ++
  point (if gridHeckeP i=2 ∨ gridHeckeP i=13 then 1 else -1)
    (eigenInverseExponent (gridHeckeP i))
    (gridIndex ((gridHeckeP i:ℤ)*gridHeckeT i)) ++
  if gridHeckeP i∣26 then [] else
    point 1 (inverseExponent (gridHeckeP i) 2)
      (gridIndex ((gridHeckeP i:ℤ)^2*gridHeckeT i))

def compileBase : GridSource → Poly
  | .word i => wordRow i
  | .taylor i => taylorRow i
  | .entire i => sample (gridEntireQ i) 0 1 zeroExponent
  | .hecke i => heckeRow i
  | .infinity i => point 1 zeroExponent (gridInfinityIndex i)

theorem eval_point (X Y Z W a b : ℂ) (v : ℕ → ℂ)
    (r : ℚ) (e : Exponent) (j : Fin 780) :
    eval X Y Z W a b 1 v (point r e j) =
      (r:ℂ)*monomial X Y Z W a b 1 e*
        v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j) := by
  simp only [point, eval_cons, eval_nil, add_zero]

theorem eval_rangeTerms (X Y Z W a b : ℂ) (v : ℕ → ℂ)
    (r : ℚ) (e : Exponent) (index : ℕ → Fin 780) (keep : ℕ → Bool) (n : ℕ) :
    eval X Y Z W a b 1 v (rangeTerms r e index keep n) =
      (r:ℂ)*monomial X Y Z W a b 1 e*
        ∑ j ∈ Finset.range n, if keep j then
          v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 (index j)) else 0 := by
  induction n with
  | zero => simp [rangeTerms]
  | succ n ih =>
    cases hk : keep n <;>
      simp [rangeTerms,hk,eval_append,eval_point,ih,Finset.sum_range_succ,mul_add]

theorem eval_sample (X Y Z W a b : ℂ) (v : ℕ → ℂ)
    (q : ℕ) (t : ℤ) (r : ℚ) (e : Exponent) :
    eval X Y Z W a b 1 v (sample q t r e) =
      (r:ℂ)*monomial X Y Z W a b 1 e*
        gridSample q t (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j)) := by
  simp only [sample,eval_rangeTerms,gridSample,FinitenessRamanujanSum.residues,
    Finset.sum_filter,decide_eq_true_eq]

theorem wordSign_cast (w : List (Fin 4 × Bool)) :
    (wordSign w : ℂ) = gridWordSign 1 (-1) w := by
  induction w with
  | nil => simp [wordSign,gridWordSign]
  | cons i w ih =>
    rcases i with ⟨i, inverse⟩
    fin_cases i <;> simp [wordSign,gridWordSign,gridBaseSign,ih]

theorem monomial_zero (X Y Z W a b : ℂ) :
    monomial X Y Z W a b 1 zeroExponent = 1 := by simp [monomial]

theorem monomial_four (X Y Z W a b : ℂ) (e : ℤ×ℤ×ℤ×ℤ) :
    monomial X Y Z W a b 1 (fourExponent e) =
      SmallLevelFourPrimeRates.monomial e X Y Z W := by
  simp [monomial,fourExponent,SmallLevelFourPrimeRates.monomial]

theorem eigenInverse_coefficient (X Y Z W a b : ℂ) (p : ℕ) :
    ((if p=2 ∨ p=13 then 1 else -1 : ℚ):ℂ)*
      monomial X Y Z W a b 1 (eigenInverseExponent p) =
      -primeEigenvalue p (-1) (-1) a b*(primeParameter p X Y Z W)⁻¹ := by
  by_cases h2 : p=2 <;> by_cases h3 : p=3 <;> by_cases h13 : p=13 <;>
    simp [eigenInverseExponent,monomial,primeEigenvalue,primeParameter,h2,h3,h13] <;>
    ring

theorem monomial_inverseSquare (X Y Z W a b : ℂ) (p : ℕ) :
    monomial X Y Z W a b 1 (inverseExponent p 2) =
      ((primeParameter p X Y Z W)⁻¹)^2 := by
  by_cases h2 : p=2 <;> by_cases h3 : p=3 <;> by_cases h13 : p=13 <;>
    simp [inverseExponent,monomial,primeParameter,h2,h3,h13,zpow_neg,inv_pow]

theorem eval_word (X Y Z W a b : ℂ) (v : ℕ → ℂ) (i : Fin 235) :
    eval X Y Z W a b 1 v (wordRow i) =
      laurentRows X Y Z W (-1) (-1) (-1) a b
        (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j)) (.word i) := by
  simp only [wordRow,eval_append,eval_point,monomial_zero,monomial_four,
    Rat.cast_one,Rat.cast_neg,wordSign_cast,laurentRows,neg_neg,one_mul]
  ring

theorem eval_taylor (X Y Z W a b : ℂ) (v : ℕ → ℂ) (i : Fin 53) :
    eval X Y Z W a b 1 v (taylorRow i) =
      laurentRows X Y Z W (-1) (-1) (-1) a b
        (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j)) (.taylor i) := by
  simp [taylorRow,eval_append,eval_sample,monomial_zero,monomial_four,laurentRows]

theorem eval_hecke (X Y Z W a b : ℂ) (v : ℕ → ℂ) (i : Fin 96) :
    eval X Y Z W a b 1 v (heckeRow i) =
      laurentRows X Y Z W (-1) (-1) (-1) a b
        (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j)) (.hecke i) := by
  by_cases h : gridHeckeP i∣26 <;>
    simp [heckeRow,h,eval_append,eval_rangeTerms,eval_point,monomial_zero,
      eigenInverse_coefficient,monomial_inverseSquare,laurentRows,laurentHecke] <;>
    ring

/-- Constructor correctness is valid even at zero formal parameters. -/
theorem compileBase_correct (X Y Z W a b : ℂ) (v : ℕ → ℂ) (i : GridSource) :
    eval X Y Z W a b 1 v (compileBase i) =
      laurentRows X Y Z W (-1) (-1) (-1) a b
        (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j)) i := by
  cases i with
  | word i => exact eval_word X Y Z W a b v i
  | taylor i => exact eval_taylor X Y Z W a b v i
  | hecke i => exact eval_hecke X Y Z W a b v i
  | entire i => simp [compileBase,eval_sample,monomial_zero,laurentRows]
  | infinity i => simp [compileBase,eval_point,monomial_zero,laurentRows]

#print axioms compileBase_correct
end QuantitativeArithmeticCompact26SourceCompiler
end
end

/-! ## QuantitativeArithmeticCompact26SourceCompilerJetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section

/-! UNVERIFIED draft. The uniform Taylor construction uses the new symbolic
base compiler, original source metadata, and the existing general rescaling
and jet-reduction lemmas. It imports no source-match theorem. -/

namespace QuantitativeArithmeticCompact26SourceCompiler
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticCompact26JetReduction
open SmallLevelTwentySixGermSources

def coordinate (j : ℕ) : Poly := [(1,j,(0,0,0,0,0,0,0))]

/-- The recursive range avoids noncomputable choices of a list representing
a finite set. Its evaluation is the Ramanujan sum over coprime residues. -/
def samplePrefix (q : ℕ) (t : ℤ) : ℕ → Poly
  | 0 => []
  | m+1 => samplePrefix q t m ++
      if Nat.Coprime m q then
        coordinate (SmallLevelTwentySixGermDAG.sourceCoordinate 0
          (gridIndex (t+(m:ℤ)*(780/q:ℕ))))
      else []

def anchorPolynomial : GridSource → Poly
  | .word j => coordinate (SmallLevelTwentySixGermDAG.sourceCoordinate 0 (gridGroupIndex j))
  | .taylor j => samplePrefix (gridTaylorQ j) (gridTaylorT j) (gridTaylorQ j)
  | _ => []

def baseRow (i : Fin 397) : Poly :=
  compileBase (SmallLevelTwentySixGermDAG.selectedSource i)

def tailPolynomial (i : Fin 397) : Poly :=
  match SmallLevelTwentySixGermDAG.selectedSource i with
  | .word j => anchorPolynomial (.word j) ++ coefficientScale (-1) (baseRow i)
  | .taylor j => anchorPolynomial (.taylor j) ++ coefficientScale (-1) (baseRow i)
  | _ => []

def lowerPrefix (n : ℕ) (i : Fin 397) : ℕ → Poly
  | 0 => []
  | h+1 => lowerPrefix n i h ++
      coefficientScale
        (-((derivativeRate (SmallLevelTwentySixGermDAG.selectedSource i))^(n-h) /
          ((n-h).factorial : ℚ)))
        (relabel (layerIndex h) (tailPolynomial i))

def polynomial (n : ℕ) (i : Fin 397) : Poly :=
  dilate ((2:ℚ)^n) ((3:ℚ)^n) ((13:ℚ)^n) ((5:ℚ)^n)
    (relabel (layerIndex n) (baseRow i) ++ lowerPrefix n i n)

theorem eval_coordinate (X Y Z W a b : ℂ) (v : ℕ → ℂ) (j : ℕ) :
    eval X Y Z W a b 1 v (coordinate j) = v j := by
  simp [coordinate, eval, monomial]

#print axioms eval_coordinate

theorem eval_samplePrefix (X Y Z W a b : ℂ) (v : ℕ → ℂ)
    (q : ℕ) (t : ℤ) (m : ℕ) :
    eval X Y Z W a b 1 v (samplePrefix q t m) =
      ∑ j ∈ Finset.range m, if Nat.Coprime j q then
        v (SmallLevelTwentySixGermDAG.sourceCoordinate 0
          (gridIndex (t+(j:ℤ)*(780/q:ℕ)))) else 0 := by
  induction m with
  | zero => simp [samplePrefix]
  | succ m ih =>
    simp only [samplePrefix, eval_append, Finset.sum_range_succ, ih]
    split_ifs <;> simp [eval_coordinate]

#print axioms eval_samplePrefix

theorem eval_anchorPolynomial (X Y Z W a b : ℂ) (v : ℕ → ℂ) (i : GridSource) :
    eval X Y Z W a b 1 v (anchorPolynomial i) =
      anchor (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j)) i := by
  cases i <;> simp [anchorPolynomial, anchor, eval_coordinate, eval_samplePrefix,
    gridSample, FinitenessRamanujanSum.residues, Finset.sum_filter]

#print axioms eval_anchorPolynomial

theorem eval_baseRow (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0) (v : ℕ → ℂ) (i : Fin 397) :
    eval X Y Z W a b 1 v (baseRow i) =
      laurentRows X Y Z W (-1) (-1) (-1) a b
        (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j))
        (SmallLevelTwentySixGermDAG.selectedSource i) :=
  compileBase_correct X Y Z W a b v _

#print axioms eval_baseRow

theorem eval_tailPolynomial (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : ℕ → ℂ) (i : Fin 397) :
    eval X Y Z W a b 1 v (tailPolynomial i) =
      tail X Y Z W (-1) (-1) (-1) a b
        (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate 0 j))
        (SmallLevelTwentySixGermDAG.selectedSource i) := by
  cases hi : SmallLevelTwentySixGermDAG.selectedSource i <;>
    simp [tailPolynomial, hi, eval_coefficientScale, eval_anchorPolynomial,
      eval_baseRow X Y Z W a b hX hY hZ hW, tail, sub_eq_add_neg]

#print axioms eval_tailPolynomial

theorem eval_lowerPrefix (n m : ℕ) (i : Fin 397) (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : ℕ → ℂ) :
    eval X Y Z W a b 1 v (lowerPrefix n i m) =
      -(∑ h ∈ Finset.range m,
        (derivativeRate (SmallLevelTwentySixGermDAG.selectedSource i) : ℂ)^(n-h) *
          tail X Y Z W (-1) (-1) (-1) a b
            (fun j => v (SmallLevelTwentySixGermDAG.sourceCoordinate h j))
            (SmallLevelTwentySixGermDAG.selectedSource i) / ((n-h).factorial : ℂ)) := by
  induction m with
  | zero => simp [lowerPrefix]
  | succ m ih =>
    simp only [lowerPrefix, eval_append, eval_coefficientScale, eval_relabel,
      eval_tailPolynomial X Y Z W a b hX hY hZ hW, Rat.cast_neg, Rat.cast_div,
      Rat.cast_pow, Rat.cast_natCast, Finset.sum_range_succ, ih]
    simp_rw [← sourceCoordinate_eq_layerIndex]
    ring

#print axioms eval_lowerPrefix

/-- The polynomial construction is the actual Taylor row for every order;
its base case is the generic symbolic compiler. -/
theorem eval_polynomial (n : ℕ) (i : Fin 397) (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : ℕ → ℂ) :
    eval X Y Z W a b 1 v (polynomial n i) =
      SmallLevelTwentySixGermDAG.replayJetRow n X Y Z W a b v i := by
  have hX' : X/(2:ℂ)^n≠0 := div_ne_zero hX (pow_ne_zero n (by norm_num))
  have hY' : Y/(3:ℂ)^n≠0 := div_ne_zero hY (pow_ne_zero n (by norm_num))
  have hZ' : Z/(13:ℂ)^n≠0 := div_ne_zero hZ (pow_ne_zero n (by norm_num))
  have hW' : W/(5:ℂ)^n≠0 := div_ne_zero hW (pow_ne_zero n (by norm_num))
  rw [polynomial, eval_dilate]
  simp only [Rat.cast_pow, Rat.cast_ofNat]
  rw [eval_append, eval_relabel,
    eval_baseRow _ _ _ _ a b hX' hY' hZ' hW',
    eval_lowerPrefix n n i _ _ _ _ a b hX' hY' hZ' hW']
  simp_rw [← sourceCoordinate_eq_layerIndex]
  simp only [SmallLevelTwentySixGermDAG.replayJetRow, jet_eq_base_sub_tails, sub_eq_add_neg]

#print axioms eval_polynomial

end QuantitativeArithmeticCompact26SourceCompiler
end
end
