module
public import SmallLevelTwentySixGermDAGSourceDataBundleV4
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation

def sourceRows (i : ℕ) : Poly :=
  match i/40 with
  | 0 => sourcePart00 (i%40)
  | 1 => sourcePart01 (i%40)
  | 2 => sourcePart02 (i%40)
  | 3 => sourcePart03 (i%40)
  | 4 => sourcePart04 (i%40)
  | 5 => sourcePart05 (i%40)
  | 6 => sourcePart06 (i%40)
  | 7 => sourcePart07 (i%40)
  | 8 => sourcePart08 (i%40)
  | 9 => sourcePart09 (i%40)
  | 10 => sourcePart10 (i%40)
  | 11 => sourcePart11 (i%40)
  | 12 => sourcePart12 (i%40)
  | 13 => sourcePart13 (i%40)
  | 14 => sourcePart14 (i%40)
  | 15 => sourcePart15 (i%40)
  | 16 => sourcePart16 (i%40)
  | 17 => sourcePart17 (i%40)
  | 18 => sourcePart18 (i%40)
  | 19 => sourcePart19 (i%40)
  | 20 => sourcePart20 (i%40)
  | 21 => sourcePart21 (i%40)
  | 22 => sourcePart22 (i%40)
  | 23 => sourcePart23 (i%40)
  | 24 => sourcePart24 (i%40)
  | 25 => sourcePart25 (i%40)
  | 26 => sourcePart26 (i%40)
  | 27 => sourcePart27 (i%40)
  | 28 => sourcePart28 (i%40)
  | 29 => sourcePart29 (i%40)
  | _ => []

end SmallLevelTwentySixGermDAG
