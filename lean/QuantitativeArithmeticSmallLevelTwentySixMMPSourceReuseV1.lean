module
public import QuantitativeArithmeticSmallLevelTwentySixJetSignFlipV1
public import QuantitativeArithmeticSmallLevelTwentySixSignedJetV1
public import SmallLevelTwentySixGermDAGSourceMatchAllV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPSourceReuse
open QuantitativeArithmeticSevenLaurentRows
open SmallLevelTwentySixGermSources SmallLevelTwentySixGermDAG FinitenessRamanujanSum
open QuantitativeArithmeticSmallLevelTwentySixJetSignFlip
open QuantitativeArithmeticSmallLevelTwentySixSignedJet

def zeroExponent : Exponent := (0,0,0,0,0,0,0)

/-- Computable finite encoding of twice the untranslated top-layer sample. -/
def twiceSample (n q : ℕ) (t : ℤ) : Poly :=
  List.ofFn (fun j : Fin q =>
    (if Nat.Coprime j.val q then (2:ℚ) else 0,
     sourceCoordinate n (gridIndex (t+(j.val:ℤ)*(780/q:ℕ))),zeroExponent))

theorem eval_twiceSample (n q : ℕ) (t : ℤ) (X Y Z W a b : ℂ) (v : ℕ→ℂ) :
    eval X Y Z W a b 1 v (twiceSample n q t)=
      2*gridSample q t (fun j => v (sourceCoordinate n j)) := by
  simp [twiceSample,eval,monomial,zeroExponent,List.map_ofFn,List.sum_ofFn,
    gridSample,residues,Finset.sum_filter,Finset.mul_sum]
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> norm_num

/-- Reuse every MMM source polynomial, modifying only the five ramified
Ramanujan rows. This avoids another1191 separately expanded source proofs. -/
def source (n : ℕ) (i : Fin 397) : Poly :=
  let old := sourceRows (n*397+i.val)
  match selectedSource i with
  | .taylor j => if 13∣gridTaylorQ j then
      twiceSample n (gridTaylorQ j) (gridTaylorT j)++shift (-1) zeroExponent old
      else old
  | _ => old

theorem source_match (n : Fin 3) (i : Fin 397) (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : ℕ→ℂ) :
    eval X Y Z W a b 1 v (source n i)=
      signedReplayJetRow 1 n X Y Z W a b v i := by
  have hold := source_rows_match X Y Z W a b hX hY hZ hW v n i
  unfold replayJetRow at hold
  unfold signedReplayJetRow
  cases hi : selectedSource i with
  | word j => simpa only [source,hi,laurentJetRow,laurentRows,laurentSlopeRows] using hold
  | entire j => simpa only [source,hi,laurentJetRow,laurentRows,laurentSlopeRows] using hold
  | infinity j => simpa only [source,hi,laurentJetRow,laurentRows,laurentSlopeRows] using hold
  | hecke j =>
    rw [hi] at hold
    simp only [source,hi]
    rw [hold]
    exact jet_independent n X Y Z W (-1) (-1) (-1) 1 a b
      (fun h j => v (sourceCoordinate h j)) (.hecke j) (selected_hecke_independent j)
  | taylor j =>
    rw [hi] at hold
    by_cases hj : 13∣gridTaylorQ j
    · simp only [source,hi,hj,↓reduceIte,eval_append,eval_twiceSample,
        eval_shift X Y Z W a b 1 v hX hY hZ hW,zeroExponent,monomial,
        zpow_zero,pow_zero,mul_one,Rat.cast_neg,Rat.cast_one,neg_one_mul]
      rw [hold]
      have h := jet_taylor_flip n X Y Z W (-1) (-1) a b
        (fun h j => v (sourceCoordinate h j)) j hj
      linear_combination -h
    · simp only [source,hi,hj,↓reduceIte]
      rw [hold]
      exact jet_independent n X Y Z W (-1) (-1) (-1) 1 a b
        (fun h j => v (sourceCoordinate h j)) (.taylor j) hj

#print axioms eval_twiceSample
#print axioms source_match
end QuantitativeArithmeticSmallLevelTwentySixMMPSourceReuse
