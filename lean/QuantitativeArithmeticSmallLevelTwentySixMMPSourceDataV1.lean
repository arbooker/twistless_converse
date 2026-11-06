module
public import SmallLevelTwentySixGermCoordinateDataV4
public import SmallLevelTwentySixGermDAGSourceRowsV1
public import QuantitativeArithmeticLaurentNormalizeV1
set_option autoImplicit false
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPSourceData
open QuantitativeArithmeticSevenLaurentRows
open SmallLevelTwentySixGermSources SmallLevelTwentySixGermDAG
def zeroExponent : Exponent := (0,0,0,0,0,0,0)

/-- Computable finite encoding of twice the untranslated top-layer sample. -/
def twiceSample (n q : ℕ) (t : ℤ) : Poly :=
  List.ofFn (fun j : Fin q =>
    (if Nat.Coprime j.val q then (2:ℚ) else 0,
     sourceCoordinate n (gridIndex (t+(j.val:ℤ)*(780/q:ℕ))),zeroExponent))

/-- Reuse every MMM source polynomial, modifying only the five ramified
Ramanujan rows. This avoids another1191 separately expanded source proofs. -/
def source (n : ℕ) (i : Fin 397) : Poly :=
  let old := sourceRows (n*397+i.val)
  match selectedSource i with
  | .taylor j => if 13∣gridTaylorQ j then
      twiceSample n (gridTaylorQ j) (gridTaylorT j)++shift (-1) zeroExponent old
      else old
  | _ => old

def normalizedSourceRows (i : ℕ) : Poly :=
  QuantitativeArithmeticLaurentNormalize.normalize
    (source (i/397) ⟨i%397,Nat.mod_lt _ (by decide)⟩)
end QuantitativeArithmeticSmallLevelTwentySixMMPSourceData
