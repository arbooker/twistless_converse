module
public import QuantitativeArithmeticFiniteRangeCertificatesV1

public import QuantitativeArithmeticSmallLevelTwentySevenZeroJetCodeV1
public import QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStagesTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenZeroJetTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusSourceBinding. Original statements and local scopes are retained; interval proofs share the general join lemma. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusSourceBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family with shared interval proofs. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusSourceBinding
open QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily (Source)
open QuantitativeArithmeticSmallLevelTwentySevenZeroJet

def entryPart0 : ℕ → Source × ℕ
  | 0 => (sourceRaw14,1)
  | 1 => (sourceRaw45,1)
  | 2 => (sourceRaw72,1)
  | 3 => (sourceRaw568,1)
  | 4 => (sourceRaw14,0)
  | 5 => (sourceRaw50,1)
  | 6 => (sourceRaw0,1)
  | 7 => (sourceRaw24,1)
  | 8 => (sourceRaw19,1)
  | 9 => (sourceRaw27,1)
  | 10 => (sourceRaw51,1)
  | 11 => (sourceRaw68,1)
  | _ => (sourceRaw14,0)
theorem bindingPart0 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (0+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart0 i.val).1 (-1) (entryPart0 i.val).2 := by decide +kernel
theorem supportPart0 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart0 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart0 : ∀ i : Fin 12, (entryPart0 i.val).2≤1 := by decide +kernel

def entryPart1 : ℕ → Source × ℕ
  | 0 => (sourceRaw32,1)
  | 1 => (sourceRaw144,1)
  | 2 => (sourceRaw2,0)
  | 3 => (sourceRaw31,0)
  | 4 => (sourceRaw17,0)
  | 5 => (sourceRaw77,0)
  | 6 => (sourceRaw83,0)
  | 7 => (sourceRaw144,0)
  | 8 => (sourceRaw149,0)
  | 9 => (sourceRaw236,0)
  | 10 => (sourceRaw568,0)
  | 11 => (sourceRaw18,1)
  | _ => (sourceRaw14,0)
theorem bindingPart1 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (12+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart1 i.val).1 (-1) (entryPart1 i.val).2 := by decide +kernel
theorem supportPart1 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart1 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart1 : ∀ i : Fin 12, (entryPart1 i.val).2≤1 := by decide +kernel

def entryPart2 : ℕ → Source × ℕ
  | 0 => (sourceRaw1,1)
  | 1 => (sourceRaw569,1)
  | 2 => (sourceRaw1568,1)
  | 3 => (sourceRaw569,0)
  | 4 => (sourceRaw570,0)
  | 5 => (sourceRaw1249,0)
  | 6 => (sourceRaw1250,0)
  | 7 => (sourceRaw1282,0)
  | 8 => (sourceRaw1365,0)
  | 9 => (sourceRaw1373,0)
  | 10 => (sourceRaw1395,0)
  | 11 => (sourceRaw1428,0)
  | _ => (sourceRaw14,0)
theorem bindingPart2 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (24+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart2 i.val).1 (-1) (entryPart2 i.val).2 := by decide +kernel
theorem supportPart2 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart2 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart2 : ∀ i : Fin 12, (entryPart2 i.val).2≤1 := by decide +kernel

def entryPart3 : ℕ → Source × ℕ
  | 0 => (sourceRaw1465,0)
  | 1 => (sourceRaw1568,0)
  | 2 => (sourceRaw1831,0)
  | 3 => (sourceRaw1832,0)
  | 4 => (sourceRaw1833,0)
  | 5 => (sourceRaw1834,0)
  | 6 => (sourceRaw1838,0)
  | 7 => (sourceRaw2651,0)
  | 8 => (sourceRaw666,1)
  | 9 => (sourceRaw970,1)
  | 10 => (sourceRaw978,1)
  | 11 => (sourceRaw2257,1)
  | _ => (sourceRaw14,0)
theorem bindingPart3 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (36+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart3 i.val).1 (-1) (entryPart3 i.val).2 := by decide +kernel
theorem supportPart3 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart3 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart3 : ∀ i : Fin 12, (entryPart3 i.val).2≤1 := by decide +kernel

def entryPart4 : ℕ → Source × ℕ
  | 0 => (sourceRaw3,0)
  | 1 => (sourceRaw4,0)
  | 2 => (sourceRaw5,0)
  | 3 => (sourceRaw6,0)
  | 4 => (sourceRaw7,0)
  | 5 => (sourceRaw8,0)
  | 6 => (sourceRaw9,0)
  | 7 => (sourceRaw10,0)
  | 8 => (sourceRaw11,0)
  | 9 => (sourceRaw12,0)
  | 10 => (sourceRaw13,0)
  | 11 => (sourceRaw15,0)
  | _ => (sourceRaw14,0)
theorem bindingPart4 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (48+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart4 i.val).1 (-1) (entryPart4 i.val).2 := by decide +kernel
theorem supportPart4 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart4 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart4 : ∀ i : Fin 12, (entryPart4 i.val).2≤1 := by decide +kernel

def entryPart5 : ℕ → Source × ℕ
  | 0 => (sourceRaw16,0)
  | 1 => (sourceRaw20,0)
  | 2 => (sourceRaw21,0)
  | 3 => (sourceRaw22,0)
  | 4 => (sourceRaw23,0)
  | 5 => (sourceRaw25,0)
  | 6 => (sourceRaw26,0)
  | 7 => (sourceRaw28,0)
  | 8 => (sourceRaw29,0)
  | 9 => (sourceRaw30,0)
  | 10 => (sourceRaw33,0)
  | 11 => (sourceRaw34,0)
  | _ => (sourceRaw14,0)
theorem bindingPart5 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (60+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart5 i.val).1 (-1) (entryPart5 i.val).2 := by decide +kernel
theorem supportPart5 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart5 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart5 : ∀ i : Fin 12, (entryPart5 i.val).2≤1 := by decide +kernel

def entryPart6 : ℕ → Source × ℕ
  | 0 => (sourceRaw35,0)
  | 1 => (sourceRaw36,0)
  | 2 => (sourceRaw37,0)
  | 3 => (sourceRaw38,0)
  | 4 => (sourceRaw39,0)
  | 5 => (sourceRaw40,0)
  | 6 => (sourceRaw41,0)
  | 7 => (sourceRaw42,0)
  | 8 => (sourceRaw43,0)
  | 9 => (sourceRaw44,0)
  | 10 => (sourceRaw46,0)
  | 11 => (sourceRaw47,0)
  | _ => (sourceRaw14,0)
theorem bindingPart6 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (72+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart6 i.val).1 (-1) (entryPart6 i.val).2 := by decide +kernel
theorem supportPart6 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart6 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart6 : ∀ i : Fin 12, (entryPart6 i.val).2≤1 := by decide +kernel

def entryPart7 : ℕ → Source × ℕ
  | 0 => (sourceRaw48,0)
  | 1 => (sourceRaw73,0)
  | 2 => (sourceRaw74,0)
  | 3 => (sourceRaw75,0)
  | 4 => (sourceRaw79,0)
  | 5 => (sourceRaw80,0)
  | 6 => (sourceRaw81,0)
  | 7 => (sourceRaw112,0)
  | 8 => (sourceRaw116,0)
  | 9 => (sourceRaw120,0)
  | 10 => (sourceRaw145,0)
  | 11 => (sourceRaw235,0)
  | _ => (sourceRaw14,0)
theorem bindingPart7 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (84+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart7 i.val).1 (-1) (entryPart7 i.val).2 := by decide +kernel
theorem supportPart7 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart7 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart7 : ∀ i : Fin 12, (entryPart7 i.val).2≤1 := by decide +kernel

def entryPart8 : ℕ → Source × ℕ
  | 0 => (sourceRaw573,0)
  | 1 => (sourceRaw574,0)
  | 2 => (sourceRaw585,0)
  | 3 => (sourceRaw586,0)
  | 4 => (sourceRaw593,0)
  | 5 => (sourceRaw594,0)
  | 6 => (sourceRaw595,0)
  | 7 => (sourceRaw596,0)
  | 8 => (sourceRaw599,0)
  | 9 => (sourceRaw600,0)
  | 10 => (sourceRaw603,0)
  | 11 => (sourceRaw604,0)
  | _ => (sourceRaw14,0)
theorem bindingPart8 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (96+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart8 i.val).1 (-1) (entryPart8 i.val).2 := by decide +kernel
theorem supportPart8 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart8 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart8 : ∀ i : Fin 12, (entryPart8 i.val).2≤1 := by decide +kernel

def entryPart9 : ℕ → Source × ℕ
  | 0 => (sourceRaw666,0)
  | 1 => (sourceRaw675,1)
  | 2 => (sourceRaw682,1)
  | 3 => (sourceRaw723,1)
  | 4 => (sourceRaw667,0)
  | 5 => (sourceRaw668,0)
  | 6 => (sourceRaw669,0)
  | 7 => (sourceRaw670,0)
  | 8 => (sourceRaw675,0)
  | 9 => (sourceRaw676,0)
  | 10 => (sourceRaw681,0)
  | 11 => (sourceRaw695,0)
  | _ => (sourceRaw14,0)
theorem bindingPart9 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (108+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart9 i.val).1 (-1) (entryPart9 i.val).2 := by decide +kernel
theorem supportPart9 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart9 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart9 : ∀ i : Fin 12, (entryPart9 i.val).2≤1 := by decide +kernel

def entryPart10 : ℕ → Source × ℕ
  | 0 => (sourceRaw696,0)
  | 1 => (sourceRaw673,0)
  | 2 => (sourceRaw674,0)
  | 3 => (sourceRaw689,0)
  | 4 => (sourceRaw690,0)
  | 5 => (sourceRaw765,0)
  | 6 => (sourceRaw766,0)
  | 7 => (sourceRaw769,0)
  | 8 => (sourceRaw770,0)
  | 9 => (sourceRaw970,0)
  | 10 => (sourceRaw739,0)
  | 11 => (sourceRaw972,0)
  | _ => (sourceRaw14,0)
theorem bindingPart10 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (120+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart10 i.val).1 (-1) (entryPart10 i.val).2 := by decide +kernel
theorem supportPart10 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart10 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart10 : ∀ i : Fin 12, (entryPart10 i.val).2≤1 := by decide +kernel

def entryPart11 : ℕ → Source × ℕ
  | 0 => (sourceRaw974,0)
  | 1 => (sourceRaw685,0)
  | 2 => (sourceRaw697,0)
  | 3 => (sourceRaw698,0)
  | 4 => (sourceRaw686,0)
  | 5 => (sourceRaw853,0)
  | 6 => (sourceRaw993,0)
  | 7 => (sourceRaw975,0)
  | 8 => (sourceRaw995,0)
  | 9 => (sourceRaw844,0)
  | 10 => (sourceRaw1002,0)
  | 11 => (sourceRaw1003,0)
  | _ => (sourceRaw14,0)
theorem bindingPart11 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (132+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart11 i.val).1 (-1) (entryPart11 i.val).2 := by decide +kernel
theorem supportPart11 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart11 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart11 : ∀ i : Fin 12, (entryPart11 i.val).2≤1 := by decide +kernel

def entryPart12 : ℕ → Source × ℕ
  | 0 => (sourceRaw1004,0)
  | 1 => (sourceRaw680,0)
  | 2 => (sourceRaw679,0)
  | 3 => (sourceRaw1033,0)
  | 4 => (sourceRaw1035,0)
  | 5 => (sourceRaw1036,0)
  | 6 => (sourceRaw1038,0)
  | 7 => (sourceRaw1068,0)
  | 8 => (sourceRaw1069,0)
  | 9 => (sourceRaw1083,0)
  | 10 => (sourceRaw944,0)
  | 11 => (sourceRaw1096,0)
  | _ => (sourceRaw14,0)
theorem bindingPart12 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (144+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart12 i.val).1 (-1) (entryPart12 i.val).2 := by decide +kernel
theorem supportPart12 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart12 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart12 : ∀ i : Fin 12, (entryPart12 i.val).2≤1 := by decide +kernel

def entryPart13 : ℕ → Source × ℕ
  | 0 => (sourceRaw1211,0)
  | 1 => (sourceRaw687,0)
  | 2 => (sourceRaw798,0)
  | 3 => (sourceRaw986,0)
  | 4 => (sourceRaw694,0)
  | 5 => (sourceRaw1008,0)
  | 6 => (sourceRaw1018,0)
  | 7 => (sourceRaw1040,0)
  | 8 => (sourceRaw693,0)
  | 9 => (sourceRaw1247,0)
  | 10 => (sourceRaw1252,0)
  | 11 => (sourceRaw1253,0)
  | _ => (sourceRaw14,0)
theorem bindingPart13 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (156+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart13 i.val).1 (-1) (entryPart13 i.val).2 := by decide +kernel
theorem supportPart13 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart13 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart13 : ∀ i : Fin 12, (entryPart13 i.val).2≤1 := by decide +kernel

def entryPart14 : ℕ → Source × ℕ
  | 0 => (sourceRaw1254,0)
  | 1 => (sourceRaw1255,0)
  | 2 => (sourceRaw1256,0)
  | 3 => (sourceRaw1260,0)
  | 4 => (sourceRaw1261,0)
  | 5 => (sourceRaw1262,0)
  | 6 => (sourceRaw1264,0)
  | 7 => (sourceRaw1265,0)
  | 8 => (sourceRaw1266,0)
  | 9 => (sourceRaw1270,0)
  | 10 => (sourceRaw1271,0)
  | 11 => (sourceRaw1275,0)
  | _ => (sourceRaw14,0)
theorem bindingPart14 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (168+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart14 i.val).1 (-1) (entryPart14 i.val).2 := by decide +kernel
theorem supportPart14 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart14 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart14 : ∀ i : Fin 12, (entryPart14 i.val).2≤1 := by decide +kernel

def entryPart15 : ℕ → Source × ℕ
  | 0 => (sourceRaw1276,0)
  | 1 => (sourceRaw1277,0)
  | 2 => (sourceRaw1280,0)
  | 3 => (sourceRaw1281,0)
  | 4 => (sourceRaw1283,0)
  | 5 => (sourceRaw1284,0)
  | 6 => (sourceRaw1285,0)
  | 7 => (sourceRaw1289,0)
  | 8 => (sourceRaw1290,0)
  | 9 => (sourceRaw1294,0)
  | 10 => (sourceRaw1295,0)
  | 11 => (sourceRaw1303,0)
  | _ => (sourceRaw14,0)
theorem bindingPart15 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (180+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart15 i.val).1 (-1) (entryPart15 i.val).2 := by decide +kernel
theorem supportPart15 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart15 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart15 : ∀ i : Fin 12, (entryPart15 i.val).2≤1 := by decide +kernel

def entryPart16 : ℕ → Source × ℕ
  | 0 => (sourceRaw1325,0)
  | 1 => (sourceRaw1326,0)
  | 2 => (sourceRaw1330,0)
  | 3 => (sourceRaw1331,0)
  | 4 => (sourceRaw1336,0)
  | 5 => (sourceRaw1338,0)
  | 6 => (sourceRaw1366,0)
  | 7 => (sourceRaw1372,0)
  | 8 => (sourceRaw1377,0)
  | 9 => (sourceRaw1396,0)
  | 10 => (sourceRaw1400,0)
  | 11 => (sourceRaw1401,0)
  | _ => (sourceRaw14,0)
theorem bindingPart16 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (192+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart16 i.val).1 (-1) (entryPart16 i.val).2 := by decide +kernel
theorem supportPart16 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart16 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart16 : ∀ i : Fin 12, (entryPart16 i.val).2≤1 := by decide +kernel

def entryPart17 : ℕ → Source × ℕ
  | 0 => (sourceRaw1429,0)
  | 1 => (sourceRaw1694,0)
  | 2 => (sourceRaw1696,0)
  | 3 => (sourceRaw1835,0)
  | 4 => (sourceRaw1836,0)
  | 5 => (sourceRaw1857,0)
  | 6 => (sourceRaw1858,0)
  | 7 => (sourceRaw1861,0)
  | 8 => (sourceRaw1862,0)
  | 9 => (sourceRaw1863,0)
  | 10 => (sourceRaw1864,0)
  | 11 => (sourceRaw1914,0)
  | _ => (sourceRaw14,0)
theorem bindingPart17 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (204+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart17 i.val).1 (-1) (entryPart17 i.val).2 := by decide +kernel
theorem supportPart17 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart17 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart17 : ∀ i : Fin 12, (entryPart17 i.val).2≤1 := by decide +kernel

def entryPart18 : ℕ → Source × ℕ
  | 0 => (sourceRaw1915,0)
  | 1 => (sourceRaw1929,0)
  | 2 => (sourceRaw1930,0)
  | 3 => (sourceRaw1931,0)
  | 4 => (sourceRaw1932,0)
  | 5 => (sourceRaw1935,0)
  | 6 => (sourceRaw1936,0)
  | 7 => (sourceRaw1947,0)
  | 8 => (sourceRaw1948,0)
  | 9 => (sourceRaw1951,0)
  | 10 => (sourceRaw1952,0)
  | 11 => (sourceRaw1955,0)
  | _ => (sourceRaw14,0)
theorem bindingPart18 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (216+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart18 i.val).1 (-1) (entryPart18 i.val).2 := by decide +kernel
theorem supportPart18 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart18 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart18 : ∀ i : Fin 12, (entryPart18 i.val).2≤1 := by decide +kernel

def entryPart19 : ℕ → Source × ℕ
  | 0 => (sourceRaw1956,0)
  | 1 => (sourceRaw1961,0)
  | 2 => (sourceRaw1962,0)
  | 3 => (sourceRaw2002,0)
  | 4 => (sourceRaw2003,0)
  | 5 => (sourceRaw2235,0)
  | 6 => (sourceRaw2243,0)
  | 7 => (sourceRaw2248,0)
  | 8 => (sourceRaw2259,0)
  | 9 => (sourceRaw2266,0)
  | 10 => (sourceRaw2275,0)
  | 11 => (sourceRaw2277,0)
  | _ => (sourceRaw14,0)
theorem bindingPart19 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (228+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart19 i.val).1 (-1) (entryPart19 i.val).2 := by decide +kernel
theorem supportPart19 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart19 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart19 : ∀ i : Fin 12, (entryPart19 i.val).2≤1 := by decide +kernel

def entryPart20 : ℕ → Source × ℕ
  | 0 => (sourceRaw2284,0)
  | 1 => (sourceRaw1942,0)
  | 2 => (sourceRaw2302,0)
  | 3 => (sourceRaw1941,0)
  | 4 => (sourceRaw2106,0)
  | 5 => (sourceRaw2311,0)
  | 6 => (sourceRaw2320,0)
  | 7 => (sourceRaw2324,0)
  | 8 => (sourceRaw2325,0)
  | 9 => (sourceRaw2372,0)
  | 10 => (sourceRaw2374,0)
  | 11 => (sourceRaw2178,0)
  | _ => (sourceRaw14,0)
theorem bindingPart20 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (240+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart20 i.val).1 (-1) (entryPart20 i.val).2 := by decide +kernel
theorem supportPart20 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart20 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart20 : ∀ i : Fin 12, (entryPart20 i.val).2≤1 := by decide +kernel

def entryPart21 : ℕ → Source × ℕ
  | 0 => (sourceRaw2390,0)
  | 1 => (sourceRaw2406,0)
  | 2 => (sourceRaw2414,0)
  | 3 => (sourceRaw2432,0)
  | 4 => (sourceRaw2448,0)
  | 5 => (sourceRaw2516,0)
  | 6 => (sourceRaw2532,0)
  | 7 => (sourceRaw2637,0)
  | 8 => (sourceRaw2644,0)
  | 9 => (sourceRaw2649,0)
  | 10 => (sourceRaw2652,0)
  | 11 => (sourceRaw2653,0)
  | _ => (sourceRaw14,0)
theorem bindingPart21 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (252+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart21 i.val).1 (-1) (entryPart21 i.val).2 := by decide +kernel
theorem supportPart21 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart21 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart21 : ∀ i : Fin 12, (entryPart21 i.val).2≤1 := by decide +kernel

def entryPart22 : ℕ → Source × ℕ
  | 0 => (sourceRaw2654,0)
  | 1 => (sourceRaw2656,0)
  | 2 => (sourceRaw2657,0)
  | 3 => (sourceRaw2658,0)
  | 4 => (sourceRaw2674,0)
  | 5 => (sourceRaw768,0)
  | 6 => (sourceRaw1091,0)
  | 7 => (sourceRaw2675,0)
  | 8 => (sourceRaw767,0)
  | 9 => (sourceRaw980,0)
  | 10 => (sourceRaw2676,0)
  | 11 => (sourceRaw2005,0)
  | _ => (sourceRaw14,0)
theorem bindingPart22 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (264+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart22 i.val).1 (-1) (entryPart22 i.val).2 := by decide +kernel
theorem supportPart22 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart22 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart22 : ∀ i : Fin 12, (entryPart22 i.val).2≤1 := by decide +kernel

def entryPart23 : ℕ → Source × ℕ
  | 0 => (sourceRaw2245,0)
  | 1 => (sourceRaw2678,0)
  | 2 => (sourceRaw749,0)
  | 3 => (sourceRaw683,0)
  | 4 => (sourceRaw800,0)
  | 5 => (sourceRaw751,0)
  | 6 => (sourceRaw678,0)
  | 7 => (sourceRaw1007,0)
  | 8 => (sourceRaw1016,0)
  | 9 => (sourceRaw671,0)
  | 10 => (sourceRaw1025,0)
  | 11 => (sourceRaw795,0)
  | _ => (sourceRaw14,0)
theorem bindingPart23 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (276+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart23 i.val).1 (-1) (entryPart23 i.val).2 := by decide +kernel
theorem supportPart23 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart23 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart23 : ∀ i : Fin 12, (entryPart23 i.val).2≤1 := by decide +kernel

def entryPart24 : ℕ → Source × ℕ
  | 0 => (sourceRaw858,0)
  | 1 => (sourceRaw1052,0)
  | 2 => (sourceRaw744,0)
  | 3 => (sourceRaw3,1)
  | 4 => (sourceRaw8,1)
  | 5 => (sourceRaw9,1)
  | 6 => (sourceRaw11,1)
  | 7 => (sourceRaw13,1)
  | 8 => (sourceRaw20,1)
  | 9 => (sourceRaw22,1)
  | 10 => (sourceRaw26,1)
  | 11 => (sourceRaw28,1)
  | _ => (sourceRaw14,0)
theorem bindingPart24 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (288+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart24 i.val).1 (-1) (entryPart24 i.val).2 := by decide +kernel
theorem supportPart24 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart24 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart24 : ∀ i : Fin 12, (entryPart24 i.val).2≤1 := by decide +kernel

def entryPart25 : ℕ → Source × ℕ
  | 0 => (sourceRaw30,1)
  | 1 => (sourceRaw38,1)
  | 2 => (sourceRaw39,1)
  | 3 => (sourceRaw40,1)
  | 4 => (sourceRaw41,1)
  | 5 => (sourceRaw42,1)
  | 6 => (sourceRaw47,1)
  | 7 => (sourceRaw69,1)
  | 8 => (sourceRaw70,1)
  | 9 => (sourceRaw71,1)
  | 10 => (sourceRaw74,1)
  | 11 => (sourceRaw109,1)
  | _ => (sourceRaw14,0)
theorem bindingPart25 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (300+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart25 i.val).1 (-1) (entryPart25 i.val).2 := by decide +kernel
theorem supportPart25 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart25 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart25 : ∀ i : Fin 12, (entryPart25 i.val).2≤1 := by decide +kernel

def entryPart26 : ℕ → Source × ℕ
  | 0 => (sourceRaw145,1)
  | 1 => (sourceRaw160,1)
  | 2 => (sourceRaw316,1)
  | 3 => (sourceRaw573,1)
  | 4 => (sourceRaw699,1)
  | 5 => (sourceRaw579,1)
  | 6 => (sourceRaw700,1)
  | 7 => (sourceRaw690,1)
  | 8 => (sourceRaw585,1)
  | 9 => (sourceRaw971,1)
  | 10 => (sourceRaw586,1)
  | 11 => (sourceRaw974,1)
  | _ => (sourceRaw14,0)
theorem bindingPart26 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (312+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart26 i.val).1 (-1) (entryPart26 i.val).2 := by decide +kernel
theorem supportPart26 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart26 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart26 : ∀ i : Fin 12, (entryPart26 i.val).2≤1 := by decide +kernel

def entryPart27 : ℕ → Source × ℕ
  | 0 => (sourceRaw685,1)
  | 1 => (sourceRaw599,1)
  | 2 => (sourceRaw697,1)
  | 3 => (sourceRaw603,1)
  | 4 => (sourceRaw701,1)
  | 5 => (sourceRaw702,1)
  | 6 => (sourceRaw600,1)
  | 7 => (sourceRaw686,1)
  | 8 => (sourceRaw698,1)
  | 9 => (sourceRaw604,1)
  | 10 => (sourceRaw1004,1)
  | 11 => (sourceRaw680,1)
  | _ => (sourceRaw14,0)
theorem bindingPart27 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (324+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart27 i.val).1 (-1) (entryPart27 i.val).2 := by decide +kernel
theorem supportPart27 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart27 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart27 : ∀ i : Fin 12, (entryPart27 i.val).2≤1 := by decide +kernel

def entryPart28 : ℕ → Source × ℕ
  | 0 => (sourceRaw1022,1)
  | 1 => (sourceRaw1261,1)
  | 2 => (sourceRaw1266,1)
  | 3 => (sourceRaw1326,1)
  | 4 => (sourceRaw1336,1)
  | 5 => (sourceRaw1361,1)
  | 6 => (sourceRaw1413,1)
  | 7 => (sourceRaw1857,1)
  | 8 => (sourceRaw1858,1)
  | 9 => (sourceRaw1951,1)
  | 10 => (sourceRaw1952,1)
  | 11 => (sourceRaw593,1)
  | _ => (sourceRaw14,0)
theorem bindingPart28 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (336+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart28 i.val).1 (-1) (entryPart28 i.val).2 := by decide +kernel
theorem supportPart28 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart28 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart28 : ∀ i : Fin 12, (entryPart28 i.val).2≤1 := by decide +kernel

def entryPart29 : ℕ → Source × ℕ
  | 0 => (sourceRaw594,1)
  | 1 => (sourceRaw595,1)
  | 2 => (sourceRaw596,1)
  | 3 => (sourceRaw678,1)
  | 4 => (sourceRaw683,1)
  | 5 => (sourceRaw687,1)
  | 6 => (sourceRaw688,1)
  | 7 => (sourceRaw689,1)
  | 8 => (sourceRaw693,1)
  | 9 => (sourceRaw739,1)
  | 10 => (sourceRaw767,1)
  | 11 => (sourceRaw795,1)
  | _ => (sourceRaw14,0)
theorem bindingPart29 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (348+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart29 i.val).1 (-1) (entryPart29 i.val).2 := by decide +kernel
theorem supportPart29 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart29 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart29 : ∀ i : Fin 12, (entryPart29 i.val).2≤1 := by decide +kernel

def entryPart30 : ℕ → Source × ℕ
  | 0 => (sourceRaw800,1)
  | 1 => (sourceRaw844,1)
  | 2 => (sourceRaw989,1)
  | 3 => (sourceRaw993,1)
  | 4 => (sourceRaw1025,1)
  | 5 => (sourceRaw1034,1)
  | 6 => (sourceRaw1863,1)
  | 7 => (sourceRaw1864,1)
  | 8 => (sourceRaw1914,1)
  | 9 => (sourceRaw1937,1)
  | 10 => (sourceRaw1938,1)
  | 11 => (sourceRaw1947,1)
  | _ => (sourceRaw14,0)
theorem bindingPart30 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (360+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart30 i.val).1 (-1) (entryPart30 i.val).2 := by decide +kernel
theorem supportPart30 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart30 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart30 : ∀ i : Fin 12, (entryPart30 i.val).2≤1 := by decide +kernel

def entryPart31 : ℕ → Source × ℕ
  | 0 => (sourceRaw1948,1)
  | 1 => (sourceRaw1955,1)
  | 2 => (sourceRaw1956,1)
  | 3 => (sourceRaw1962,1)
  | 4 => (sourceRaw1991,1)
  | 5 => (sourceRaw1992,1)
  | 6 => (sourceRaw2004,1)
  | 7 => (sourceRaw2005,1)
  | 8 => (sourceRaw2023,1)
  | 9 => (sourceRaw2060,1)
  | 10 => (sourceRaw2067,1)
  | 11 => (sourceRaw2070,1)
  | _ => (sourceRaw14,0)
theorem bindingPart31 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (372+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart31 i.val).1 (-1) (entryPart31 i.val).2 := by decide +kernel
theorem supportPart31 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart31 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart31 : ∀ i : Fin 12, (entryPart31 i.val).2≤1 := by decide +kernel

def entryPart32 : ℕ → Source × ℕ
  | 0 => (sourceRaw2087,1)
  | 1 => (sourceRaw2090,1)
  | 2 => (sourceRaw2248,1)
  | 3 => (sourceRaw2266,1)
  | 4 => (sourceRaw2275,1)
  | 5 => (sourceRaw2320,1)
  | 6 => (sourceRaw672,0)
  | 7 => (sourceRaw677,0)
  | 8 => (sourceRaw684,0)
  | 9 => (sourceRaw748,0)
  | 10 => (sourceRaw750,0)
  | 11 => (sourceRaw794,0)
  | _ => (sourceRaw14,0)
theorem bindingPart32 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (384+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart32 i.val).1 (-1) (entryPart32 i.val).2 := by decide +kernel
theorem supportPart32 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart32 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart32 : ∀ i : Fin 12, (entryPart32 i.val).2≤1 := by decide +kernel

def entryPart33 : ℕ → Source × ℕ
  | 0 => (sourceRaw801,0)
  | 1 => (sourceRaw802,0)
  | 2 => (sourceRaw803,0)
  | 3 => (sourceRaw845,0)
  | 4 => (sourceRaw846,0)
  | 5 => (sourceRaw976,0)
  | 6 => (sourceRaw979,0)
  | 7 => (sourceRaw981,0)
  | 8 => (sourceRaw982,0)
  | 9 => (sourceRaw984,0)
  | 10 => (sourceRaw985,0)
  | 11 => (sourceRaw987,0)
  | _ => (sourceRaw14,0)
theorem bindingPart33 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (396+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart33 i.val).1 (-1) (entryPart33 i.val).2 := by decide +kernel
theorem supportPart33 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart33 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart33 : ∀ i : Fin 12, (entryPart33 i.val).2≤1 := by decide +kernel

def entryPart34 : ℕ → Source × ℕ
  | 0 => (sourceRaw990,0)
  | 1 => (sourceRaw991,0)
  | 2 => (sourceRaw992,0)
  | 3 => (sourceRaw996,0)
  | 4 => (sourceRaw997,0)
  | 5 => (sourceRaw999,0)
  | 6 => (sourceRaw1000,0)
  | 7 => (sourceRaw1001,0)
  | 8 => (sourceRaw745,0)
  | 9 => (sourceRaw1005,0)
  | 10 => (sourceRaw1006,0)
  | 11 => (sourceRaw1009,0)
  | _ => (sourceRaw14,0)
theorem bindingPart34 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (408+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart34 i.val).1 (-1) (entryPart34 i.val).2 := by decide +kernel
theorem supportPart34 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart34 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart34 : ∀ i : Fin 12, (entryPart34 i.val).2≤1 := by decide +kernel

def entryPart35 : ℕ → Source × ℕ
  | 0 => (sourceRaw1010,0)
  | 1 => (sourceRaw1014,0)
  | 2 => (sourceRaw1017,0)
  | 3 => (sourceRaw1020,0)
  | 4 => (sourceRaw1021,0)
  | 5 => (sourceRaw1026,0)
  | 6 => (sourceRaw1027,0)
  | 7 => (sourceRaw1029,0)
  | 8 => (sourceRaw1030,0)
  | 9 => (sourceRaw1032,0)
  | 10 => (sourceRaw1039,0)
  | 11 => (sourceRaw1041,0)
  | _ => (sourceRaw14,0)
theorem bindingPart35 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (420+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart35 i.val).1 (-1) (entryPart35 i.val).2 := by decide +kernel
theorem supportPart35 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart35 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart35 : ∀ i : Fin 12, (entryPart35 i.val).2≤1 := by decide +kernel

def entryPart36 : ℕ → Source × ℕ
  | 0 => (sourceRaw1044,0)
  | 1 => (sourceRaw1045,0)
  | 2 => (sourceRaw1047,0)
  | 3 => (sourceRaw1051,0)
  | 4 => (sourceRaw1065,0)
  | 5 => (sourceRaw1066,0)
  | 6 => (sourceRaw1071,0)
  | 7 => (sourceRaw1072,0)
  | 8 => (sourceRaw1075,0)
  | 9 => (sourceRaw1077,0)
  | 10 => (sourceRaw1084,0)
  | 11 => (sourceRaw1086,0)
  | _ => (sourceRaw14,0)
theorem bindingPart36 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (432+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart36 i.val).1 (-1) (entryPart36 i.val).2 := by decide +kernel
theorem supportPart36 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart36 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart36 : ∀ i : Fin 12, (entryPart36 i.val).2≤1 := by decide +kernel

def entryPart37 : ℕ → Source × ℕ
  | 0 => (sourceRaw1087,0)
  | 1 => (sourceRaw1089,0)
  | 2 => (sourceRaw1090,0)
  | 3 => (sourceRaw1095,0)
  | 4 => (sourceRaw1111,0)
  | 5 => (sourceRaw1114,0)
  | 6 => (sourceRaw1024,0)
  | 7 => (sourceRaw1117,0)
  | 8 => (sourceRaw880,0)
  | 9 => (sourceRaw1054,0)
  | 10 => (sourceRaw898,0)
  | 11 => (sourceRaw1119,0)
  | _ => (sourceRaw14,0)
theorem bindingPart37 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (444+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart37 i.val).1 (-1) (entryPart37 i.val).2 := by decide +kernel
theorem supportPart37 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart37 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart37 : ∀ i : Fin 12, (entryPart37 i.val).2≤1 := by decide +kernel

def entryPart38 : ℕ → Source × ℕ
  | 0 => (sourceRaw879,0)
  | 1 => (sourceRaw1062,0)
  | 2 => (sourceRaw1125,0)
  | 3 => (sourceRaw1080,0)
  | 4 => (sourceRaw1126,0)
  | 5 => (sourceRaw1081,0)
  | 6 => (sourceRaw901,0)
  | 7 => (sourceRaw933,0)
  | 8 => (sourceRaw792,0)
  | 9 => (sourceRaw927,0)
  | 10 => (sourceRaw1131,0)
  | 11 => (sourceRaw793,0)
  | _ => (sourceRaw14,0)
theorem bindingPart38 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (456+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart38 i.val).1 (-1) (entryPart38 i.val).2 := by decide +kernel
theorem supportPart38 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart38 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart38 : ∀ i : Fin 12, (entryPart38 i.val).2≤1 := by decide +kernel

def entryPart39 : ℕ → Source × ℕ
  | 0 => (sourceRaw1110,0)
  | 1 => (sourceRaw900,0)
  | 2 => (sourceRaw952,0)
  | 3 => (sourceRaw1092,0)
  | 4 => (sourceRaw926,0)
  | 5 => (sourceRaw1933,0)
  | 6 => (sourceRaw1934,0)
  | 7 => (sourceRaw1943,0)
  | 8 => (sourceRaw1986,1)
  | 9 => (sourceRaw1944,0)
  | 10 => (sourceRaw2056,0)
  | 11 => (sourceRaw2057,0)
  | _ => (sourceRaw14,0)
theorem bindingPart39 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (468+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart39 i.val).1 (-1) (entryPart39 i.val).2 := by decide +kernel
theorem supportPart39 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart39 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart39 : ∀ i : Fin 12, (entryPart39 i.val).2≤1 := by decide +kernel

def entryPart40 : ℕ → Source × ℕ
  | 0 => (sourceRaw2060,0)
  | 1 => (sourceRaw2061,0)
  | 2 => (sourceRaw2308,0)
  | 3 => (sourceRaw2066,0)
  | 4 => (sourceRaw2071,0)
  | 5 => (sourceRaw2240,0)
  | 6 => (sourceRaw2241,0)
  | 7 => (sourceRaw2246,0)
  | 8 => (sourceRaw2247,0)
  | 9 => (sourceRaw2249,0)
  | 10 => (sourceRaw2250,0)
  | 11 => (sourceRaw2252,0)
  | _ => (sourceRaw14,0)
theorem bindingPart40 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (480+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart40 i.val).1 (-1) (entryPart40 i.val).2 := by decide +kernel
theorem supportPart40 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart40 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart40 : ∀ i : Fin 12, (entryPart40 i.val).2≤1 := by decide +kernel

def entryPart41 : ℕ → Source × ℕ
  | 0 => (sourceRaw2253,0)
  | 1 => (sourceRaw2254,0)
  | 2 => (sourceRaw2255,0)
  | 3 => (sourceRaw2256,0)
  | 4 => (sourceRaw2260,0)
  | 5 => (sourceRaw2261,0)
  | 6 => (sourceRaw2262,0)
  | 7 => (sourceRaw2264,0)
  | 8 => (sourceRaw2267,0)
  | 9 => (sourceRaw2268,0)
  | 10 => (sourceRaw2270,0)
  | 11 => (sourceRaw2271,0)
  | _ => (sourceRaw14,0)
theorem bindingPart41 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (492+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart41 i.val).1 (-1) (entryPart41 i.val).2 := by decide +kernel
theorem supportPart41 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart41 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart41 : ∀ i : Fin 12, (entryPart41 i.val).2≤1 := by decide +kernel

def entryPart42 : ℕ → Source × ℕ
  | 0 => (sourceRaw2273,0)
  | 1 => (sourceRaw2274,0)
  | 2 => (sourceRaw2276,0)
  | 3 => (sourceRaw2280,0)
  | 4 => (sourceRaw2281,0)
  | 5 => (sourceRaw2282,0)
  | 6 => (sourceRaw2283,0)
  | 7 => (sourceRaw2285,0)
  | 8 => (sourceRaw2287,0)
  | 9 => (sourceRaw2288,0)
  | 10 => (sourceRaw2289,0)
  | 11 => (sourceRaw2290,0)
  | _ => (sourceRaw14,0)
theorem bindingPart42 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (504+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart42 i.val).1 (-1) (entryPart42 i.val).2 := by decide +kernel
theorem supportPart42 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart42 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart42 : ∀ i : Fin 12, (entryPart42 i.val).2≤1 := by decide +kernel

def entryPart43 : ℕ → Source × ℕ
  | 0 => (sourceRaw2297,0)
  | 1 => (sourceRaw2298,0)
  | 2 => (sourceRaw2299,0)
  | 3 => (sourceRaw2301,0)
  | 4 => (sourceRaw2303,0)
  | 5 => (sourceRaw2304,0)
  | 6 => (sourceRaw2305,0)
  | 7 => (sourceRaw2306,0)
  | 8 => (sourceRaw2310,0)
  | 9 => (sourceRaw2312,0)
  | 10 => (sourceRaw2313,0)
  | 11 => (sourceRaw2315,0)
  | _ => (sourceRaw14,0)
theorem bindingPart43 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (516+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart43 i.val).1 (-1) (entryPart43 i.val).2 := by decide +kernel
theorem supportPart43 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart43 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart43 : ∀ i : Fin 12, (entryPart43 i.val).2≤1 := by decide +kernel

def entryPart44 : ℕ → Source × ℕ
  | 0 => (sourceRaw2316,0)
  | 1 => (sourceRaw2318,0)
  | 2 => (sourceRaw2319,0)
  | 3 => (sourceRaw2322,0)
  | 4 => (sourceRaw2323,0)
  | 5 => (sourceRaw2326,0)
  | 6 => (sourceRaw2330,0)
  | 7 => (sourceRaw2331,0)
  | 8 => (sourceRaw2332,0)
  | 9 => (sourceRaw2269,0)
  | 10 => (sourceRaw2333,0)
  | 11 => (sourceRaw2334,0)
  | _ => (sourceRaw14,0)
theorem bindingPart44 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (528+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart44 i.val).1 (-1) (entryPart44 i.val).2 := by decide +kernel
theorem supportPart44 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart44 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart44 : ∀ i : Fin 12, (entryPart44 i.val).2≤1 := by decide +kernel

def entryPart45 : ℕ → Source × ℕ
  | 0 => (sourceRaw2336,0)
  | 1 => (sourceRaw2337,0)
  | 2 => (sourceRaw2339,0)
  | 3 => (sourceRaw2340,0)
  | 4 => (sourceRaw2345,0)
  | 5 => (sourceRaw2346,0)
  | 6 => (sourceRaw2348,0)
  | 7 => (sourceRaw2351,0)
  | 8 => (sourceRaw2361,0)
  | 9 => (sourceRaw2362,0)
  | 10 => (sourceRaw2364,0)
  | 11 => (sourceRaw2366,0)
  | _ => (sourceRaw14,0)
theorem bindingPart45 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (540+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart45 i.val).1 (-1) (entryPart45 i.val).2 := by decide +kernel
theorem supportPart45 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart45 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart45 : ∀ i : Fin 12, (entryPart45 i.val).2≤1 := by decide +kernel

def entryPart46 : ℕ → Source × ℕ
  | 0 => (sourceRaw2367,0)
  | 1 => (sourceRaw2371,0)
  | 2 => (sourceRaw2373,0)
  | 3 => (sourceRaw2375,0)
  | 4 => (sourceRaw2376,0)
  | 5 => (sourceRaw2378,0)
  | 6 => (sourceRaw2379,0)
  | 7 => (sourceRaw2381,0)
  | 8 => (sourceRaw2382,0)
  | 9 => (sourceRaw2393,0)
  | 10 => (sourceRaw2394,0)
  | 11 => (sourceRaw2396,0)
  | _ => (sourceRaw14,0)
theorem bindingPart46 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (552+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart46 i.val).1 (-1) (entryPart46 i.val).2 := by decide +kernel
theorem supportPart46 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart46 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart46 : ∀ i : Fin 12, (entryPart46 i.val).2≤1 := by decide +kernel

def entryPart47 : ℕ → Source × ℕ
  | 0 => (sourceRaw2397,0)
  | 1 => (sourceRaw2399,0)
  | 2 => (sourceRaw2400,0)
  | 3 => (sourceRaw2402,0)
  | 4 => (sourceRaw2404,0)
  | 5 => (sourceRaw2407,0)
  | 6 => (sourceRaw2408,0)
  | 7 => (sourceRaw2409,0)
  | 8 => (sourceRaw2427,0)
  | 9 => (sourceRaw2429,0)
  | 10 => (sourceRaw2327,0)
  | 11 => (sourceRaw2435,0)
  | _ => (sourceRaw14,0)
theorem bindingPart47 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (564+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart47 i.val).1 (-1) (entryPart47 i.val).2 := by decide +kernel
theorem supportPart47 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart47 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart47 : ∀ i : Fin 12, (entryPart47 i.val).2≤1 := by decide +kernel

def entryPart48 : ℕ → Source × ℕ
  | 0 => (sourceRaw2309,0)
  | 1 => (sourceRaw2360,0)
  | 2 => (sourceRaw2439,0)
  | 3 => (sourceRaw2117,0)
  | 4 => (sourceRaw2424,0)
  | 5 => (sourceRaw2436,0)
  | 6 => (sourceRaw2053,0)
  | 7 => (sourceRaw2441,0)
  | 8 => (sourceRaw2116,0)
  | 9 => (sourceRaw2445,0)
  | 10 => (sourceRaw2163,0)
  | 11 => (sourceRaw2352,0)
  | _ => (sourceRaw14,0)
theorem bindingPart48 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (576+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart48 i.val).1 (-1) (entryPart48 i.val).2 := by decide +kernel
theorem supportPart48 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart48 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart48 : ∀ i : Fin 12, (entryPart48 i.val).2≤1 := by decide +kernel

def entryPart49 : ℕ → Source × ℕ
  | 0 => (sourceRaw2403,0)
  | 1 => (sourceRaw2450,0)
  | 2 => (sourceRaw2387,0)
  | 3 => (sourceRaw2165,0)
  | 4 => (sourceRaw2369,0)
  | 5 => (sourceRaw2189,0)
  | 6 => (sourceRaw2161,0)
  | 7 => (sourceRaw2438,0)
  | 8 => (sourceRaw2055,0)
  | 9 => (sourceRaw2451,0)
  | 10 => (sourceRaw2388,0)
  | 11 => (sourceRaw2456,0)
  | _ => (sourceRaw14,0)
theorem bindingPart49 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (588+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart49 i.val).1 (-1) (entryPart49 i.val).2 := by decide +kernel
theorem supportPart49 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart49 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart49 : ∀ i : Fin 12, (entryPart49 i.val).2≤1 := by decide +kernel

def entryPart50 : ℕ → Source × ℕ
  | 0 => (sourceRaw2162,0)
  | 1 => (sourceRaw2198,0)
  | 2 => (sourceRaw2052,0)
  | 3 => (sourceRaw2195,0)
  | 4 => (sourceRaw2463,0)
  | 5 => (sourceRaw2054,0)
  | 6 => (sourceRaw2430,0)
  | 7 => (sourceRaw2164,0)
  | 8 => (sourceRaw2197,0)
  | 9 => (sourceRaw2188,0)
  | 10 => (sourceRaw2196,0)
  | 11 => (sourceRaw692,1)
  | _ => (sourceRaw14,0)
theorem bindingPart50 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (600+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart50 i.val).1 (-1) (entryPart50 i.val).2 := by decide +kernel
theorem supportPart50 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart50 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart50 : ∀ i : Fin 12, (entryPart50 i.val).2≤1 := by decide +kernel

def entryPart51 : ℕ → Source × ℕ
  | 0 => (sourceRaw847,1)
  | 1 => (sourceRaw1007,1)
  | 2 => (sourceRaw1196,1)
  | 3 => (sourceRaw744,1)
  | 4 => (sourceRaw2026,1)
  | 5 => (sourceRaw2302,1)
  | 6 => (sourceRaw749,1)
  | 7 => (sourceRaw743,0)
  | 8 => (sourceRaw747,0)
  | 9 => (sourceRaw741,0)
  | 10 => (sourceRaw796,0)
  | 11 => (sourceRaw790,0)
  | _ => (sourceRaw14,0)
theorem bindingPart51 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (612+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart51 i.val).1 (-1) (entryPart51 i.val).2 := by decide +kernel
theorem supportPart51 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart51 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart51 : ∀ i : Fin 12, (entryPart51 i.val).2≤1 := by decide +kernel

def entryPart52 : ℕ → Source × ℕ
  | 0 => (sourceRaw1011,0)
  | 1 => (sourceRaw1200,0)
  | 2 => (sourceRaw1201,0)
  | 3 => (sourceRaw1240,0)
  | 4 => (sourceRaw2037,0)
  | 5 => (sourceRaw2109,0)
  | 6 => (sourceRaw2160,0)
  | 7 => (sourceRaw2263,0)
  | 8 => (sourceRaw2295,0)
  | 9 => (sourceRaw2296,0)
  | 10 => (sourceRaw2317,0)
  | 11 => (sourceRaw2344,0)
  | _ => (sourceRaw14,0)
theorem bindingPart52 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (624+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart52 i.val).1 (-1) (entryPart52 i.val).2 := by decide +kernel
theorem supportPart52 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart52 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart52 : ∀ i : Fin 12, (entryPart52 i.val).2≤1 := by decide +kernel

def entryPart53 : ℕ → Source × ℕ
  | 0 => (sourceRaw2064,0)
  | 1 => (sourceRaw2199,0)
  | 2 => (sourceRaw2368,0)
  | 3 => (sourceRaw740,1)
  | 4 => (sourceRaw740,0)
  | 5 => (sourceRaw742,0)
  | 6 => (sourceRaw746,0)
  | 7 => (sourceRaw791,0)
  | 8 => (sourceRaw1012,0)
  | 9 => (sourceRaw1015,0)
  | 10 => (sourceRaw1198,0)
  | 11 => (sourceRaw1203,0)
  | _ => (sourceRaw14,0)
theorem bindingPart53 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (636+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart53 i.val).1 (-1) (entryPart53 i.val).2 := by decide +kernel
theorem supportPart53 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart53 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart53 : ∀ i : Fin 12, (entryPart53 i.val).2≤1 := by decide +kernel

def entryPart54 : ℕ → Source × ℕ
  | 0 => (sourceRaw1206,0)
  | 1 => (sourceRaw2032,0)
  | 2 => (sourceRaw2036,0)
  | 3 => (sourceRaw2031,0)
  | 4 => (sourceRaw2065,0)
  | 5 => (sourceRaw2107,0)
  | 6 => (sourceRaw2108,0)
  | 7 => (sourceRaw2291,0)
  | 8 => (sourceRaw2292,0)
  | 9 => (sourceRaw2294,0)
  | 10 => (sourceRaw2583,0)
  | 11 => (sourceRaw2030,0)
  | _ => (sourceRaw14,0)
theorem bindingPart54 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (648+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart54 i.val).1 (-1) (entryPart54 i.val).2 := by decide +kernel
theorem supportPart54 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart54 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart54 : ∀ i : Fin 12, (entryPart54 i.val).2≤1 := by decide +kernel

def entryPart55 : ℕ → Source × ℕ
  | 0 => (sourceRaw2555,0)
  | 1 => (sourceRaw2698,0)
  | 2 => (sourceRaw2036,1)
  | 3 => (sourceRaw2038,1)
  | 4 => (sourceRaw2109,1)
  | 5 => (sourceRaw2027,0)
  | 6 => (sourceRaw2028,0)
  | 7 => (sourceRaw2029,0)
  | 8 => (sourceRaw2552,0)
  | 9 => (sourceRaw2553,0)
  | 10 => (sourceRaw2558,0)
  | 11 => (sourceRaw2550,0)
  | _ => (sourceRaw14,0)
theorem bindingPart55 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs (660+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart55 i.val).1 (-1) (entryPart55 i.val).2 := by decide +kernel
theorem supportPart55 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart55 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart55 : ∀ i : Fin 12, (entryPart55 i.val).2≤1 := by decide +kernel

end QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusSourceBinding
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusSourceBindingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusSourceBinding
open QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily (Source)
open QuantitativeArithmeticSmallLevelTwentySevenZeroJet
def entryNode0_1 (n : ℕ) : Source × ℕ := entryPart0 (n-0)
theorem entryNode0_1_binding (n : ℕ) (hl : 0≤n) (hh : n<12) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_1 n).1 (-1) (entryNode0_1 n).2 := by
  have hn : n-0<12 := by omega
  have he : 0+(n-0)=n := by omega
  simpa only [entryNode0_1,he] using bindingPart0 ⟨n-0,hn⟩
theorem entryNode0_1_support (n : ℕ) (hl : 0≤n) (hh : n<12) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_1 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-0<12 := by omega
  have he : 0+(n-0)=n := by omega
  simpa only [entryNode0_1,he] using supportPart0 ⟨n-0,hn⟩
theorem entryNode0_1_depth (n : ℕ) (hl : 0≤n) (hh : n<12) : (entryNode0_1 n).2≤1 := by
  have hn : n-0<12 := by omega
  have he : 0+(n-0)=n := by omega
  simpa only [entryNode0_1,he] using depthPart0 ⟨n-0,hn⟩
def entryNode1_2 (n : ℕ) : Source × ℕ := entryPart1 (n-12)
theorem entryNode1_2_binding (n : ℕ) (hl : 12≤n) (hh : n<24) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode1_2 n).1 (-1) (entryNode1_2 n).2 := by
  have hn : n-12<12 := by omega
  have he : 12+(n-12)=n := by omega
  simpa only [entryNode1_2,he] using bindingPart1 ⟨n-12,hn⟩
theorem entryNode1_2_support (n : ℕ) (hl : 12≤n) (hh : n<24) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode1_2 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-12<12 := by omega
  have he : 12+(n-12)=n := by omega
  simpa only [entryNode1_2,he] using supportPart1 ⟨n-12,hn⟩
theorem entryNode1_2_depth (n : ℕ) (hl : 12≤n) (hh : n<24) : (entryNode1_2 n).2≤1 := by
  have hn : n-12<12 := by omega
  have he : 12+(n-12)=n := by omega
  simpa only [entryNode1_2,he] using depthPart1 ⟨n-12,hn⟩
def entryNode2_3 (n : ℕ) : Source × ℕ := entryPart2 (n-24)
theorem entryNode2_3_binding (n : ℕ) (hl : 24≤n) (hh : n<36) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode2_3 n).1 (-1) (entryNode2_3 n).2 := by
  have hn : n-24<12 := by omega
  have he : 24+(n-24)=n := by omega
  simpa only [entryNode2_3,he] using bindingPart2 ⟨n-24,hn⟩
theorem entryNode2_3_support (n : ℕ) (hl : 24≤n) (hh : n<36) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode2_3 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-24<12 := by omega
  have he : 24+(n-24)=n := by omega
  simpa only [entryNode2_3,he] using supportPart2 ⟨n-24,hn⟩
theorem entryNode2_3_depth (n : ℕ) (hl : 24≤n) (hh : n<36) : (entryNode2_3 n).2≤1 := by
  have hn : n-24<12 := by omega
  have he : 24+(n-24)=n := by omega
  simpa only [entryNode2_3,he] using depthPart2 ⟨n-24,hn⟩
def entryNode1_3 (n : ℕ) : Source × ℕ := if n<24 then entryNode1_2 n else entryNode2_3 n
theorem entryNode1_3_binding (n : ℕ) (hl : 12≤n) (hh : n<36) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode1_3 n).1 (-1) (entryNode1_3 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode1_2_binding entryNode2_3_binding n hl hh
theorem entryNode1_3_support (n : ℕ) (hl : 12≤n) (hh : n<36) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode1_3 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode1_2_support entryNode2_3_support n hl hh
theorem entryNode1_3_depth (n : ℕ) (hl : 12≤n) (hh : n<36) : (entryNode1_3 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode1_2_depth entryNode2_3_depth n hl hh
def entryNode0_3 (n : ℕ) : Source × ℕ := if n<12 then entryNode0_1 n else entryNode1_3 n
theorem entryNode0_3_binding (n : ℕ) (hl : 0≤n) (hh : n<36) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_3 n).1 (-1) (entryNode0_3 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_1_binding entryNode1_3_binding n hl hh
theorem entryNode0_3_support (n : ℕ) (hl : 0≤n) (hh : n<36) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_3 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_1_support entryNode1_3_support n hl hh
theorem entryNode0_3_depth (n : ℕ) (hl : 0≤n) (hh : n<36) : (entryNode0_3 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_1_depth entryNode1_3_depth n hl hh
def entryNode3_4 (n : ℕ) : Source × ℕ := entryPart3 (n-36)
theorem entryNode3_4_binding (n : ℕ) (hl : 36≤n) (hh : n<48) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode3_4 n).1 (-1) (entryNode3_4 n).2 := by
  have hn : n-36<12 := by omega
  have he : 36+(n-36)=n := by omega
  simpa only [entryNode3_4,he] using bindingPart3 ⟨n-36,hn⟩
theorem entryNode3_4_support (n : ℕ) (hl : 36≤n) (hh : n<48) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode3_4 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-36<12 := by omega
  have he : 36+(n-36)=n := by omega
  simpa only [entryNode3_4,he] using supportPart3 ⟨n-36,hn⟩
theorem entryNode3_4_depth (n : ℕ) (hl : 36≤n) (hh : n<48) : (entryNode3_4 n).2≤1 := by
  have hn : n-36<12 := by omega
  have he : 36+(n-36)=n := by omega
  simpa only [entryNode3_4,he] using depthPart3 ⟨n-36,hn⟩
def entryNode4_5 (n : ℕ) : Source × ℕ := entryPart4 (n-48)
theorem entryNode4_5_binding (n : ℕ) (hl : 48≤n) (hh : n<60) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode4_5 n).1 (-1) (entryNode4_5 n).2 := by
  have hn : n-48<12 := by omega
  have he : 48+(n-48)=n := by omega
  simpa only [entryNode4_5,he] using bindingPart4 ⟨n-48,hn⟩
theorem entryNode4_5_support (n : ℕ) (hl : 48≤n) (hh : n<60) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode4_5 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-48<12 := by omega
  have he : 48+(n-48)=n := by omega
  simpa only [entryNode4_5,he] using supportPart4 ⟨n-48,hn⟩
theorem entryNode4_5_depth (n : ℕ) (hl : 48≤n) (hh : n<60) : (entryNode4_5 n).2≤1 := by
  have hn : n-48<12 := by omega
  have he : 48+(n-48)=n := by omega
  simpa only [entryNode4_5,he] using depthPart4 ⟨n-48,hn⟩
def entryNode3_5 (n : ℕ) : Source × ℕ := if n<48 then entryNode3_4 n else entryNode4_5 n
theorem entryNode3_5_binding (n : ℕ) (hl : 36≤n) (hh : n<60) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode3_5 n).1 (-1) (entryNode3_5 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode3_4_binding entryNode4_5_binding n hl hh
theorem entryNode3_5_support (n : ℕ) (hl : 36≤n) (hh : n<60) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode3_5 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode3_4_support entryNode4_5_support n hl hh
theorem entryNode3_5_depth (n : ℕ) (hl : 36≤n) (hh : n<60) : (entryNode3_5 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode3_4_depth entryNode4_5_depth n hl hh
def entryNode5_6 (n : ℕ) : Source × ℕ := entryPart5 (n-60)
theorem entryNode5_6_binding (n : ℕ) (hl : 60≤n) (hh : n<72) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode5_6 n).1 (-1) (entryNode5_6 n).2 := by
  have hn : n-60<12 := by omega
  have he : 60+(n-60)=n := by omega
  simpa only [entryNode5_6,he] using bindingPart5 ⟨n-60,hn⟩
theorem entryNode5_6_support (n : ℕ) (hl : 60≤n) (hh : n<72) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode5_6 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-60<12 := by omega
  have he : 60+(n-60)=n := by omega
  simpa only [entryNode5_6,he] using supportPart5 ⟨n-60,hn⟩
theorem entryNode5_6_depth (n : ℕ) (hl : 60≤n) (hh : n<72) : (entryNode5_6 n).2≤1 := by
  have hn : n-60<12 := by omega
  have he : 60+(n-60)=n := by omega
  simpa only [entryNode5_6,he] using depthPart5 ⟨n-60,hn⟩
def entryNode6_7 (n : ℕ) : Source × ℕ := entryPart6 (n-72)
theorem entryNode6_7_binding (n : ℕ) (hl : 72≤n) (hh : n<84) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode6_7 n).1 (-1) (entryNode6_7 n).2 := by
  have hn : n-72<12 := by omega
  have he : 72+(n-72)=n := by omega
  simpa only [entryNode6_7,he] using bindingPart6 ⟨n-72,hn⟩
theorem entryNode6_7_support (n : ℕ) (hl : 72≤n) (hh : n<84) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode6_7 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-72<12 := by omega
  have he : 72+(n-72)=n := by omega
  simpa only [entryNode6_7,he] using supportPart6 ⟨n-72,hn⟩
theorem entryNode6_7_depth (n : ℕ) (hl : 72≤n) (hh : n<84) : (entryNode6_7 n).2≤1 := by
  have hn : n-72<12 := by omega
  have he : 72+(n-72)=n := by omega
  simpa only [entryNode6_7,he] using depthPart6 ⟨n-72,hn⟩
def entryNode5_7 (n : ℕ) : Source × ℕ := if n<72 then entryNode5_6 n else entryNode6_7 n
theorem entryNode5_7_binding (n : ℕ) (hl : 60≤n) (hh : n<84) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode5_7 n).1 (-1) (entryNode5_7 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode5_6_binding entryNode6_7_binding n hl hh
theorem entryNode5_7_support (n : ℕ) (hl : 60≤n) (hh : n<84) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode5_7 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode5_6_support entryNode6_7_support n hl hh
theorem entryNode5_7_depth (n : ℕ) (hl : 60≤n) (hh : n<84) : (entryNode5_7 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode5_6_depth entryNode6_7_depth n hl hh
def entryNode3_7 (n : ℕ) : Source × ℕ := if n<60 then entryNode3_5 n else entryNode5_7 n
theorem entryNode3_7_binding (n : ℕ) (hl : 36≤n) (hh : n<84) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode3_7 n).1 (-1) (entryNode3_7 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode3_5_binding entryNode5_7_binding n hl hh
theorem entryNode3_7_support (n : ℕ) (hl : 36≤n) (hh : n<84) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode3_7 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode3_5_support entryNode5_7_support n hl hh
theorem entryNode3_7_depth (n : ℕ) (hl : 36≤n) (hh : n<84) : (entryNode3_7 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode3_5_depth entryNode5_7_depth n hl hh
def entryNode0_7 (n : ℕ) : Source × ℕ := if n<36 then entryNode0_3 n else entryNode3_7 n
theorem entryNode0_7_binding (n : ℕ) (hl : 0≤n) (hh : n<84) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_7 n).1 (-1) (entryNode0_7 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_3_binding entryNode3_7_binding n hl hh
theorem entryNode0_7_support (n : ℕ) (hl : 0≤n) (hh : n<84) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_7 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_3_support entryNode3_7_support n hl hh
theorem entryNode0_7_depth (n : ℕ) (hl : 0≤n) (hh : n<84) : (entryNode0_7 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_3_depth entryNode3_7_depth n hl hh
def entryNode7_8 (n : ℕ) : Source × ℕ := entryPart7 (n-84)
theorem entryNode7_8_binding (n : ℕ) (hl : 84≤n) (hh : n<96) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode7_8 n).1 (-1) (entryNode7_8 n).2 := by
  have hn : n-84<12 := by omega
  have he : 84+(n-84)=n := by omega
  simpa only [entryNode7_8,he] using bindingPart7 ⟨n-84,hn⟩
theorem entryNode7_8_support (n : ℕ) (hl : 84≤n) (hh : n<96) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode7_8 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-84<12 := by omega
  have he : 84+(n-84)=n := by omega
  simpa only [entryNode7_8,he] using supportPart7 ⟨n-84,hn⟩
theorem entryNode7_8_depth (n : ℕ) (hl : 84≤n) (hh : n<96) : (entryNode7_8 n).2≤1 := by
  have hn : n-84<12 := by omega
  have he : 84+(n-84)=n := by omega
  simpa only [entryNode7_8,he] using depthPart7 ⟨n-84,hn⟩
def entryNode8_9 (n : ℕ) : Source × ℕ := entryPart8 (n-96)
theorem entryNode8_9_binding (n : ℕ) (hl : 96≤n) (hh : n<108) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode8_9 n).1 (-1) (entryNode8_9 n).2 := by
  have hn : n-96<12 := by omega
  have he : 96+(n-96)=n := by omega
  simpa only [entryNode8_9,he] using bindingPart8 ⟨n-96,hn⟩
theorem entryNode8_9_support (n : ℕ) (hl : 96≤n) (hh : n<108) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode8_9 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-96<12 := by omega
  have he : 96+(n-96)=n := by omega
  simpa only [entryNode8_9,he] using supportPart8 ⟨n-96,hn⟩
theorem entryNode8_9_depth (n : ℕ) (hl : 96≤n) (hh : n<108) : (entryNode8_9 n).2≤1 := by
  have hn : n-96<12 := by omega
  have he : 96+(n-96)=n := by omega
  simpa only [entryNode8_9,he] using depthPart8 ⟨n-96,hn⟩
def entryNode9_10 (n : ℕ) : Source × ℕ := entryPart9 (n-108)
theorem entryNode9_10_binding (n : ℕ) (hl : 108≤n) (hh : n<120) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode9_10 n).1 (-1) (entryNode9_10 n).2 := by
  have hn : n-108<12 := by omega
  have he : 108+(n-108)=n := by omega
  simpa only [entryNode9_10,he] using bindingPart9 ⟨n-108,hn⟩
theorem entryNode9_10_support (n : ℕ) (hl : 108≤n) (hh : n<120) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode9_10 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-108<12 := by omega
  have he : 108+(n-108)=n := by omega
  simpa only [entryNode9_10,he] using supportPart9 ⟨n-108,hn⟩
theorem entryNode9_10_depth (n : ℕ) (hl : 108≤n) (hh : n<120) : (entryNode9_10 n).2≤1 := by
  have hn : n-108<12 := by omega
  have he : 108+(n-108)=n := by omega
  simpa only [entryNode9_10,he] using depthPart9 ⟨n-108,hn⟩
def entryNode8_10 (n : ℕ) : Source × ℕ := if n<108 then entryNode8_9 n else entryNode9_10 n
theorem entryNode8_10_binding (n : ℕ) (hl : 96≤n) (hh : n<120) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode8_10 n).1 (-1) (entryNode8_10 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode8_9_binding entryNode9_10_binding n hl hh
theorem entryNode8_10_support (n : ℕ) (hl : 96≤n) (hh : n<120) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode8_10 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode8_9_support entryNode9_10_support n hl hh
theorem entryNode8_10_depth (n : ℕ) (hl : 96≤n) (hh : n<120) : (entryNode8_10 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode8_9_depth entryNode9_10_depth n hl hh
def entryNode7_10 (n : ℕ) : Source × ℕ := if n<96 then entryNode7_8 n else entryNode8_10 n
theorem entryNode7_10_binding (n : ℕ) (hl : 84≤n) (hh : n<120) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode7_10 n).1 (-1) (entryNode7_10 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode7_8_binding entryNode8_10_binding n hl hh
theorem entryNode7_10_support (n : ℕ) (hl : 84≤n) (hh : n<120) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode7_10 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode7_8_support entryNode8_10_support n hl hh
theorem entryNode7_10_depth (n : ℕ) (hl : 84≤n) (hh : n<120) : (entryNode7_10 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode7_8_depth entryNode8_10_depth n hl hh
def entryNode10_11 (n : ℕ) : Source × ℕ := entryPart10 (n-120)
theorem entryNode10_11_binding (n : ℕ) (hl : 120≤n) (hh : n<132) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode10_11 n).1 (-1) (entryNode10_11 n).2 := by
  have hn : n-120<12 := by omega
  have he : 120+(n-120)=n := by omega
  simpa only [entryNode10_11,he] using bindingPart10 ⟨n-120,hn⟩
theorem entryNode10_11_support (n : ℕ) (hl : 120≤n) (hh : n<132) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode10_11 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-120<12 := by omega
  have he : 120+(n-120)=n := by omega
  simpa only [entryNode10_11,he] using supportPart10 ⟨n-120,hn⟩
theorem entryNode10_11_depth (n : ℕ) (hl : 120≤n) (hh : n<132) : (entryNode10_11 n).2≤1 := by
  have hn : n-120<12 := by omega
  have he : 120+(n-120)=n := by omega
  simpa only [entryNode10_11,he] using depthPart10 ⟨n-120,hn⟩
def entryNode11_12 (n : ℕ) : Source × ℕ := entryPart11 (n-132)
theorem entryNode11_12_binding (n : ℕ) (hl : 132≤n) (hh : n<144) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode11_12 n).1 (-1) (entryNode11_12 n).2 := by
  have hn : n-132<12 := by omega
  have he : 132+(n-132)=n := by omega
  simpa only [entryNode11_12,he] using bindingPart11 ⟨n-132,hn⟩
theorem entryNode11_12_support (n : ℕ) (hl : 132≤n) (hh : n<144) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode11_12 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-132<12 := by omega
  have he : 132+(n-132)=n := by omega
  simpa only [entryNode11_12,he] using supportPart11 ⟨n-132,hn⟩
theorem entryNode11_12_depth (n : ℕ) (hl : 132≤n) (hh : n<144) : (entryNode11_12 n).2≤1 := by
  have hn : n-132<12 := by omega
  have he : 132+(n-132)=n := by omega
  simpa only [entryNode11_12,he] using depthPart11 ⟨n-132,hn⟩
def entryNode10_12 (n : ℕ) : Source × ℕ := if n<132 then entryNode10_11 n else entryNode11_12 n
theorem entryNode10_12_binding (n : ℕ) (hl : 120≤n) (hh : n<144) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode10_12 n).1 (-1) (entryNode10_12 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode10_11_binding entryNode11_12_binding n hl hh
theorem entryNode10_12_support (n : ℕ) (hl : 120≤n) (hh : n<144) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode10_12 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode10_11_support entryNode11_12_support n hl hh
theorem entryNode10_12_depth (n : ℕ) (hl : 120≤n) (hh : n<144) : (entryNode10_12 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode10_11_depth entryNode11_12_depth n hl hh
def entryNode12_13 (n : ℕ) : Source × ℕ := entryPart12 (n-144)
theorem entryNode12_13_binding (n : ℕ) (hl : 144≤n) (hh : n<156) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode12_13 n).1 (-1) (entryNode12_13 n).2 := by
  have hn : n-144<12 := by omega
  have he : 144+(n-144)=n := by omega
  simpa only [entryNode12_13,he] using bindingPart12 ⟨n-144,hn⟩
theorem entryNode12_13_support (n : ℕ) (hl : 144≤n) (hh : n<156) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode12_13 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-144<12 := by omega
  have he : 144+(n-144)=n := by omega
  simpa only [entryNode12_13,he] using supportPart12 ⟨n-144,hn⟩
theorem entryNode12_13_depth (n : ℕ) (hl : 144≤n) (hh : n<156) : (entryNode12_13 n).2≤1 := by
  have hn : n-144<12 := by omega
  have he : 144+(n-144)=n := by omega
  simpa only [entryNode12_13,he] using depthPart12 ⟨n-144,hn⟩
def entryNode13_14 (n : ℕ) : Source × ℕ := entryPart13 (n-156)
theorem entryNode13_14_binding (n : ℕ) (hl : 156≤n) (hh : n<168) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode13_14 n).1 (-1) (entryNode13_14 n).2 := by
  have hn : n-156<12 := by omega
  have he : 156+(n-156)=n := by omega
  simpa only [entryNode13_14,he] using bindingPart13 ⟨n-156,hn⟩
theorem entryNode13_14_support (n : ℕ) (hl : 156≤n) (hh : n<168) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode13_14 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-156<12 := by omega
  have he : 156+(n-156)=n := by omega
  simpa only [entryNode13_14,he] using supportPart13 ⟨n-156,hn⟩
theorem entryNode13_14_depth (n : ℕ) (hl : 156≤n) (hh : n<168) : (entryNode13_14 n).2≤1 := by
  have hn : n-156<12 := by omega
  have he : 156+(n-156)=n := by omega
  simpa only [entryNode13_14,he] using depthPart13 ⟨n-156,hn⟩
def entryNode12_14 (n : ℕ) : Source × ℕ := if n<156 then entryNode12_13 n else entryNode13_14 n
theorem entryNode12_14_binding (n : ℕ) (hl : 144≤n) (hh : n<168) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode12_14 n).1 (-1) (entryNode12_14 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode12_13_binding entryNode13_14_binding n hl hh
theorem entryNode12_14_support (n : ℕ) (hl : 144≤n) (hh : n<168) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode12_14 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode12_13_support entryNode13_14_support n hl hh
theorem entryNode12_14_depth (n : ℕ) (hl : 144≤n) (hh : n<168) : (entryNode12_14 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode12_13_depth entryNode13_14_depth n hl hh
def entryNode10_14 (n : ℕ) : Source × ℕ := if n<144 then entryNode10_12 n else entryNode12_14 n
theorem entryNode10_14_binding (n : ℕ) (hl : 120≤n) (hh : n<168) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode10_14 n).1 (-1) (entryNode10_14 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode10_12_binding entryNode12_14_binding n hl hh
theorem entryNode10_14_support (n : ℕ) (hl : 120≤n) (hh : n<168) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode10_14 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode10_12_support entryNode12_14_support n hl hh
theorem entryNode10_14_depth (n : ℕ) (hl : 120≤n) (hh : n<168) : (entryNode10_14 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode10_12_depth entryNode12_14_depth n hl hh
def entryNode7_14 (n : ℕ) : Source × ℕ := if n<120 then entryNode7_10 n else entryNode10_14 n
theorem entryNode7_14_binding (n : ℕ) (hl : 84≤n) (hh : n<168) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode7_14 n).1 (-1) (entryNode7_14 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode7_10_binding entryNode10_14_binding n hl hh
theorem entryNode7_14_support (n : ℕ) (hl : 84≤n) (hh : n<168) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode7_14 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode7_10_support entryNode10_14_support n hl hh
theorem entryNode7_14_depth (n : ℕ) (hl : 84≤n) (hh : n<168) : (entryNode7_14 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode7_10_depth entryNode10_14_depth n hl hh
def entryNode0_14 (n : ℕ) : Source × ℕ := if n<84 then entryNode0_7 n else entryNode7_14 n
theorem entryNode0_14_binding (n : ℕ) (hl : 0≤n) (hh : n<168) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_14 n).1 (-1) (entryNode0_14 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_7_binding entryNode7_14_binding n hl hh
theorem entryNode0_14_support (n : ℕ) (hl : 0≤n) (hh : n<168) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_14 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_7_support entryNode7_14_support n hl hh
theorem entryNode0_14_depth (n : ℕ) (hl : 0≤n) (hh : n<168) : (entryNode0_14 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_7_depth entryNode7_14_depth n hl hh
def entryNode14_15 (n : ℕ) : Source × ℕ := entryPart14 (n-168)
theorem entryNode14_15_binding (n : ℕ) (hl : 168≤n) (hh : n<180) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode14_15 n).1 (-1) (entryNode14_15 n).2 := by
  have hn : n-168<12 := by omega
  have he : 168+(n-168)=n := by omega
  simpa only [entryNode14_15,he] using bindingPart14 ⟨n-168,hn⟩
theorem entryNode14_15_support (n : ℕ) (hl : 168≤n) (hh : n<180) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode14_15 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-168<12 := by omega
  have he : 168+(n-168)=n := by omega
  simpa only [entryNode14_15,he] using supportPart14 ⟨n-168,hn⟩
theorem entryNode14_15_depth (n : ℕ) (hl : 168≤n) (hh : n<180) : (entryNode14_15 n).2≤1 := by
  have hn : n-168<12 := by omega
  have he : 168+(n-168)=n := by omega
  simpa only [entryNode14_15,he] using depthPart14 ⟨n-168,hn⟩
def entryNode15_16 (n : ℕ) : Source × ℕ := entryPart15 (n-180)
theorem entryNode15_16_binding (n : ℕ) (hl : 180≤n) (hh : n<192) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode15_16 n).1 (-1) (entryNode15_16 n).2 := by
  have hn : n-180<12 := by omega
  have he : 180+(n-180)=n := by omega
  simpa only [entryNode15_16,he] using bindingPart15 ⟨n-180,hn⟩
theorem entryNode15_16_support (n : ℕ) (hl : 180≤n) (hh : n<192) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode15_16 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-180<12 := by omega
  have he : 180+(n-180)=n := by omega
  simpa only [entryNode15_16,he] using supportPart15 ⟨n-180,hn⟩
theorem entryNode15_16_depth (n : ℕ) (hl : 180≤n) (hh : n<192) : (entryNode15_16 n).2≤1 := by
  have hn : n-180<12 := by omega
  have he : 180+(n-180)=n := by omega
  simpa only [entryNode15_16,he] using depthPart15 ⟨n-180,hn⟩
def entryNode16_17 (n : ℕ) : Source × ℕ := entryPart16 (n-192)
theorem entryNode16_17_binding (n : ℕ) (hl : 192≤n) (hh : n<204) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode16_17 n).1 (-1) (entryNode16_17 n).2 := by
  have hn : n-192<12 := by omega
  have he : 192+(n-192)=n := by omega
  simpa only [entryNode16_17,he] using bindingPart16 ⟨n-192,hn⟩
theorem entryNode16_17_support (n : ℕ) (hl : 192≤n) (hh : n<204) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode16_17 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-192<12 := by omega
  have he : 192+(n-192)=n := by omega
  simpa only [entryNode16_17,he] using supportPart16 ⟨n-192,hn⟩
theorem entryNode16_17_depth (n : ℕ) (hl : 192≤n) (hh : n<204) : (entryNode16_17 n).2≤1 := by
  have hn : n-192<12 := by omega
  have he : 192+(n-192)=n := by omega
  simpa only [entryNode16_17,he] using depthPart16 ⟨n-192,hn⟩
def entryNode15_17 (n : ℕ) : Source × ℕ := if n<192 then entryNode15_16 n else entryNode16_17 n
theorem entryNode15_17_binding (n : ℕ) (hl : 180≤n) (hh : n<204) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode15_17 n).1 (-1) (entryNode15_17 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode15_16_binding entryNode16_17_binding n hl hh
theorem entryNode15_17_support (n : ℕ) (hl : 180≤n) (hh : n<204) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode15_17 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode15_16_support entryNode16_17_support n hl hh
theorem entryNode15_17_depth (n : ℕ) (hl : 180≤n) (hh : n<204) : (entryNode15_17 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode15_16_depth entryNode16_17_depth n hl hh
def entryNode14_17 (n : ℕ) : Source × ℕ := if n<180 then entryNode14_15 n else entryNode15_17 n
theorem entryNode14_17_binding (n : ℕ) (hl : 168≤n) (hh : n<204) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode14_17 n).1 (-1) (entryNode14_17 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode14_15_binding entryNode15_17_binding n hl hh
theorem entryNode14_17_support (n : ℕ) (hl : 168≤n) (hh : n<204) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode14_17 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode14_15_support entryNode15_17_support n hl hh
theorem entryNode14_17_depth (n : ℕ) (hl : 168≤n) (hh : n<204) : (entryNode14_17 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode14_15_depth entryNode15_17_depth n hl hh
def entryNode17_18 (n : ℕ) : Source × ℕ := entryPart17 (n-204)
theorem entryNode17_18_binding (n : ℕ) (hl : 204≤n) (hh : n<216) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode17_18 n).1 (-1) (entryNode17_18 n).2 := by
  have hn : n-204<12 := by omega
  have he : 204+(n-204)=n := by omega
  simpa only [entryNode17_18,he] using bindingPart17 ⟨n-204,hn⟩
theorem entryNode17_18_support (n : ℕ) (hl : 204≤n) (hh : n<216) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode17_18 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-204<12 := by omega
  have he : 204+(n-204)=n := by omega
  simpa only [entryNode17_18,he] using supportPart17 ⟨n-204,hn⟩
theorem entryNode17_18_depth (n : ℕ) (hl : 204≤n) (hh : n<216) : (entryNode17_18 n).2≤1 := by
  have hn : n-204<12 := by omega
  have he : 204+(n-204)=n := by omega
  simpa only [entryNode17_18,he] using depthPart17 ⟨n-204,hn⟩
def entryNode18_19 (n : ℕ) : Source × ℕ := entryPart18 (n-216)
theorem entryNode18_19_binding (n : ℕ) (hl : 216≤n) (hh : n<228) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode18_19 n).1 (-1) (entryNode18_19 n).2 := by
  have hn : n-216<12 := by omega
  have he : 216+(n-216)=n := by omega
  simpa only [entryNode18_19,he] using bindingPart18 ⟨n-216,hn⟩
theorem entryNode18_19_support (n : ℕ) (hl : 216≤n) (hh : n<228) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode18_19 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-216<12 := by omega
  have he : 216+(n-216)=n := by omega
  simpa only [entryNode18_19,he] using supportPart18 ⟨n-216,hn⟩
theorem entryNode18_19_depth (n : ℕ) (hl : 216≤n) (hh : n<228) : (entryNode18_19 n).2≤1 := by
  have hn : n-216<12 := by omega
  have he : 216+(n-216)=n := by omega
  simpa only [entryNode18_19,he] using depthPart18 ⟨n-216,hn⟩
def entryNode17_19 (n : ℕ) : Source × ℕ := if n<216 then entryNode17_18 n else entryNode18_19 n
theorem entryNode17_19_binding (n : ℕ) (hl : 204≤n) (hh : n<228) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode17_19 n).1 (-1) (entryNode17_19 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode17_18_binding entryNode18_19_binding n hl hh
theorem entryNode17_19_support (n : ℕ) (hl : 204≤n) (hh : n<228) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode17_19 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode17_18_support entryNode18_19_support n hl hh
theorem entryNode17_19_depth (n : ℕ) (hl : 204≤n) (hh : n<228) : (entryNode17_19 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode17_18_depth entryNode18_19_depth n hl hh
def entryNode19_20 (n : ℕ) : Source × ℕ := entryPart19 (n-228)
theorem entryNode19_20_binding (n : ℕ) (hl : 228≤n) (hh : n<240) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode19_20 n).1 (-1) (entryNode19_20 n).2 := by
  have hn : n-228<12 := by omega
  have he : 228+(n-228)=n := by omega
  simpa only [entryNode19_20,he] using bindingPart19 ⟨n-228,hn⟩
theorem entryNode19_20_support (n : ℕ) (hl : 228≤n) (hh : n<240) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode19_20 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-228<12 := by omega
  have he : 228+(n-228)=n := by omega
  simpa only [entryNode19_20,he] using supportPart19 ⟨n-228,hn⟩
theorem entryNode19_20_depth (n : ℕ) (hl : 228≤n) (hh : n<240) : (entryNode19_20 n).2≤1 := by
  have hn : n-228<12 := by omega
  have he : 228+(n-228)=n := by omega
  simpa only [entryNode19_20,he] using depthPart19 ⟨n-228,hn⟩
def entryNode20_21 (n : ℕ) : Source × ℕ := entryPart20 (n-240)
theorem entryNode20_21_binding (n : ℕ) (hl : 240≤n) (hh : n<252) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode20_21 n).1 (-1) (entryNode20_21 n).2 := by
  have hn : n-240<12 := by omega
  have he : 240+(n-240)=n := by omega
  simpa only [entryNode20_21,he] using bindingPart20 ⟨n-240,hn⟩
theorem entryNode20_21_support (n : ℕ) (hl : 240≤n) (hh : n<252) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode20_21 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-240<12 := by omega
  have he : 240+(n-240)=n := by omega
  simpa only [entryNode20_21,he] using supportPart20 ⟨n-240,hn⟩
theorem entryNode20_21_depth (n : ℕ) (hl : 240≤n) (hh : n<252) : (entryNode20_21 n).2≤1 := by
  have hn : n-240<12 := by omega
  have he : 240+(n-240)=n := by omega
  simpa only [entryNode20_21,he] using depthPart20 ⟨n-240,hn⟩
def entryNode19_21 (n : ℕ) : Source × ℕ := if n<240 then entryNode19_20 n else entryNode20_21 n
theorem entryNode19_21_binding (n : ℕ) (hl : 228≤n) (hh : n<252) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode19_21 n).1 (-1) (entryNode19_21 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode19_20_binding entryNode20_21_binding n hl hh
theorem entryNode19_21_support (n : ℕ) (hl : 228≤n) (hh : n<252) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode19_21 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode19_20_support entryNode20_21_support n hl hh
theorem entryNode19_21_depth (n : ℕ) (hl : 228≤n) (hh : n<252) : (entryNode19_21 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode19_20_depth entryNode20_21_depth n hl hh
def entryNode17_21 (n : ℕ) : Source × ℕ := if n<228 then entryNode17_19 n else entryNode19_21 n
theorem entryNode17_21_binding (n : ℕ) (hl : 204≤n) (hh : n<252) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode17_21 n).1 (-1) (entryNode17_21 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode17_19_binding entryNode19_21_binding n hl hh
theorem entryNode17_21_support (n : ℕ) (hl : 204≤n) (hh : n<252) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode17_21 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode17_19_support entryNode19_21_support n hl hh
theorem entryNode17_21_depth (n : ℕ) (hl : 204≤n) (hh : n<252) : (entryNode17_21 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode17_19_depth entryNode19_21_depth n hl hh
def entryNode14_21 (n : ℕ) : Source × ℕ := if n<204 then entryNode14_17 n else entryNode17_21 n
theorem entryNode14_21_binding (n : ℕ) (hl : 168≤n) (hh : n<252) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode14_21 n).1 (-1) (entryNode14_21 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode14_17_binding entryNode17_21_binding n hl hh
theorem entryNode14_21_support (n : ℕ) (hl : 168≤n) (hh : n<252) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode14_21 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode14_17_support entryNode17_21_support n hl hh
theorem entryNode14_21_depth (n : ℕ) (hl : 168≤n) (hh : n<252) : (entryNode14_21 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode14_17_depth entryNode17_21_depth n hl hh
def entryNode21_22 (n : ℕ) : Source × ℕ := entryPart21 (n-252)
theorem entryNode21_22_binding (n : ℕ) (hl : 252≤n) (hh : n<264) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode21_22 n).1 (-1) (entryNode21_22 n).2 := by
  have hn : n-252<12 := by omega
  have he : 252+(n-252)=n := by omega
  simpa only [entryNode21_22,he] using bindingPart21 ⟨n-252,hn⟩
theorem entryNode21_22_support (n : ℕ) (hl : 252≤n) (hh : n<264) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode21_22 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-252<12 := by omega
  have he : 252+(n-252)=n := by omega
  simpa only [entryNode21_22,he] using supportPart21 ⟨n-252,hn⟩
theorem entryNode21_22_depth (n : ℕ) (hl : 252≤n) (hh : n<264) : (entryNode21_22 n).2≤1 := by
  have hn : n-252<12 := by omega
  have he : 252+(n-252)=n := by omega
  simpa only [entryNode21_22,he] using depthPart21 ⟨n-252,hn⟩
def entryNode22_23 (n : ℕ) : Source × ℕ := entryPart22 (n-264)
theorem entryNode22_23_binding (n : ℕ) (hl : 264≤n) (hh : n<276) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode22_23 n).1 (-1) (entryNode22_23 n).2 := by
  have hn : n-264<12 := by omega
  have he : 264+(n-264)=n := by omega
  simpa only [entryNode22_23,he] using bindingPart22 ⟨n-264,hn⟩
theorem entryNode22_23_support (n : ℕ) (hl : 264≤n) (hh : n<276) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode22_23 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-264<12 := by omega
  have he : 264+(n-264)=n := by omega
  simpa only [entryNode22_23,he] using supportPart22 ⟨n-264,hn⟩
theorem entryNode22_23_depth (n : ℕ) (hl : 264≤n) (hh : n<276) : (entryNode22_23 n).2≤1 := by
  have hn : n-264<12 := by omega
  have he : 264+(n-264)=n := by omega
  simpa only [entryNode22_23,he] using depthPart22 ⟨n-264,hn⟩
def entryNode23_24 (n : ℕ) : Source × ℕ := entryPart23 (n-276)
theorem entryNode23_24_binding (n : ℕ) (hl : 276≤n) (hh : n<288) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode23_24 n).1 (-1) (entryNode23_24 n).2 := by
  have hn : n-276<12 := by omega
  have he : 276+(n-276)=n := by omega
  simpa only [entryNode23_24,he] using bindingPart23 ⟨n-276,hn⟩
theorem entryNode23_24_support (n : ℕ) (hl : 276≤n) (hh : n<288) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode23_24 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-276<12 := by omega
  have he : 276+(n-276)=n := by omega
  simpa only [entryNode23_24,he] using supportPart23 ⟨n-276,hn⟩
theorem entryNode23_24_depth (n : ℕ) (hl : 276≤n) (hh : n<288) : (entryNode23_24 n).2≤1 := by
  have hn : n-276<12 := by omega
  have he : 276+(n-276)=n := by omega
  simpa only [entryNode23_24,he] using depthPart23 ⟨n-276,hn⟩
def entryNode22_24 (n : ℕ) : Source × ℕ := if n<276 then entryNode22_23 n else entryNode23_24 n
theorem entryNode22_24_binding (n : ℕ) (hl : 264≤n) (hh : n<288) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode22_24 n).1 (-1) (entryNode22_24 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode22_23_binding entryNode23_24_binding n hl hh
theorem entryNode22_24_support (n : ℕ) (hl : 264≤n) (hh : n<288) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode22_24 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode22_23_support entryNode23_24_support n hl hh
theorem entryNode22_24_depth (n : ℕ) (hl : 264≤n) (hh : n<288) : (entryNode22_24 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode22_23_depth entryNode23_24_depth n hl hh
def entryNode21_24 (n : ℕ) : Source × ℕ := if n<264 then entryNode21_22 n else entryNode22_24 n
theorem entryNode21_24_binding (n : ℕ) (hl : 252≤n) (hh : n<288) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode21_24 n).1 (-1) (entryNode21_24 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode21_22_binding entryNode22_24_binding n hl hh
theorem entryNode21_24_support (n : ℕ) (hl : 252≤n) (hh : n<288) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode21_24 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode21_22_support entryNode22_24_support n hl hh
theorem entryNode21_24_depth (n : ℕ) (hl : 252≤n) (hh : n<288) : (entryNode21_24 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode21_22_depth entryNode22_24_depth n hl hh
def entryNode24_25 (n : ℕ) : Source × ℕ := entryPart24 (n-288)
theorem entryNode24_25_binding (n : ℕ) (hl : 288≤n) (hh : n<300) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode24_25 n).1 (-1) (entryNode24_25 n).2 := by
  have hn : n-288<12 := by omega
  have he : 288+(n-288)=n := by omega
  simpa only [entryNode24_25,he] using bindingPart24 ⟨n-288,hn⟩
theorem entryNode24_25_support (n : ℕ) (hl : 288≤n) (hh : n<300) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode24_25 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-288<12 := by omega
  have he : 288+(n-288)=n := by omega
  simpa only [entryNode24_25,he] using supportPart24 ⟨n-288,hn⟩
theorem entryNode24_25_depth (n : ℕ) (hl : 288≤n) (hh : n<300) : (entryNode24_25 n).2≤1 := by
  have hn : n-288<12 := by omega
  have he : 288+(n-288)=n := by omega
  simpa only [entryNode24_25,he] using depthPart24 ⟨n-288,hn⟩
def entryNode25_26 (n : ℕ) : Source × ℕ := entryPart25 (n-300)
theorem entryNode25_26_binding (n : ℕ) (hl : 300≤n) (hh : n<312) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode25_26 n).1 (-1) (entryNode25_26 n).2 := by
  have hn : n-300<12 := by omega
  have he : 300+(n-300)=n := by omega
  simpa only [entryNode25_26,he] using bindingPart25 ⟨n-300,hn⟩
theorem entryNode25_26_support (n : ℕ) (hl : 300≤n) (hh : n<312) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode25_26 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-300<12 := by omega
  have he : 300+(n-300)=n := by omega
  simpa only [entryNode25_26,he] using supportPart25 ⟨n-300,hn⟩
theorem entryNode25_26_depth (n : ℕ) (hl : 300≤n) (hh : n<312) : (entryNode25_26 n).2≤1 := by
  have hn : n-300<12 := by omega
  have he : 300+(n-300)=n := by omega
  simpa only [entryNode25_26,he] using depthPart25 ⟨n-300,hn⟩
def entryNode24_26 (n : ℕ) : Source × ℕ := if n<300 then entryNode24_25 n else entryNode25_26 n
theorem entryNode24_26_binding (n : ℕ) (hl : 288≤n) (hh : n<312) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode24_26 n).1 (-1) (entryNode24_26 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode24_25_binding entryNode25_26_binding n hl hh
theorem entryNode24_26_support (n : ℕ) (hl : 288≤n) (hh : n<312) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode24_26 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode24_25_support entryNode25_26_support n hl hh
theorem entryNode24_26_depth (n : ℕ) (hl : 288≤n) (hh : n<312) : (entryNode24_26 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode24_25_depth entryNode25_26_depth n hl hh
def entryNode26_27 (n : ℕ) : Source × ℕ := entryPart26 (n-312)
theorem entryNode26_27_binding (n : ℕ) (hl : 312≤n) (hh : n<324) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode26_27 n).1 (-1) (entryNode26_27 n).2 := by
  have hn : n-312<12 := by omega
  have he : 312+(n-312)=n := by omega
  simpa only [entryNode26_27,he] using bindingPart26 ⟨n-312,hn⟩
theorem entryNode26_27_support (n : ℕ) (hl : 312≤n) (hh : n<324) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode26_27 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-312<12 := by omega
  have he : 312+(n-312)=n := by omega
  simpa only [entryNode26_27,he] using supportPart26 ⟨n-312,hn⟩
theorem entryNode26_27_depth (n : ℕ) (hl : 312≤n) (hh : n<324) : (entryNode26_27 n).2≤1 := by
  have hn : n-312<12 := by omega
  have he : 312+(n-312)=n := by omega
  simpa only [entryNode26_27,he] using depthPart26 ⟨n-312,hn⟩
def entryNode27_28 (n : ℕ) : Source × ℕ := entryPart27 (n-324)
theorem entryNode27_28_binding (n : ℕ) (hl : 324≤n) (hh : n<336) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode27_28 n).1 (-1) (entryNode27_28 n).2 := by
  have hn : n-324<12 := by omega
  have he : 324+(n-324)=n := by omega
  simpa only [entryNode27_28,he] using bindingPart27 ⟨n-324,hn⟩
theorem entryNode27_28_support (n : ℕ) (hl : 324≤n) (hh : n<336) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode27_28 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-324<12 := by omega
  have he : 324+(n-324)=n := by omega
  simpa only [entryNode27_28,he] using supportPart27 ⟨n-324,hn⟩
theorem entryNode27_28_depth (n : ℕ) (hl : 324≤n) (hh : n<336) : (entryNode27_28 n).2≤1 := by
  have hn : n-324<12 := by omega
  have he : 324+(n-324)=n := by omega
  simpa only [entryNode27_28,he] using depthPart27 ⟨n-324,hn⟩
def entryNode26_28 (n : ℕ) : Source × ℕ := if n<324 then entryNode26_27 n else entryNode27_28 n
theorem entryNode26_28_binding (n : ℕ) (hl : 312≤n) (hh : n<336) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode26_28 n).1 (-1) (entryNode26_28 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode26_27_binding entryNode27_28_binding n hl hh
theorem entryNode26_28_support (n : ℕ) (hl : 312≤n) (hh : n<336) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode26_28 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode26_27_support entryNode27_28_support n hl hh
theorem entryNode26_28_depth (n : ℕ) (hl : 312≤n) (hh : n<336) : (entryNode26_28 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode26_27_depth entryNode27_28_depth n hl hh
def entryNode24_28 (n : ℕ) : Source × ℕ := if n<312 then entryNode24_26 n else entryNode26_28 n
theorem entryNode24_28_binding (n : ℕ) (hl : 288≤n) (hh : n<336) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode24_28 n).1 (-1) (entryNode24_28 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode24_26_binding entryNode26_28_binding n hl hh
theorem entryNode24_28_support (n : ℕ) (hl : 288≤n) (hh : n<336) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode24_28 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode24_26_support entryNode26_28_support n hl hh
theorem entryNode24_28_depth (n : ℕ) (hl : 288≤n) (hh : n<336) : (entryNode24_28 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode24_26_depth entryNode26_28_depth n hl hh
def entryNode21_28 (n : ℕ) : Source × ℕ := if n<288 then entryNode21_24 n else entryNode24_28 n
theorem entryNode21_28_binding (n : ℕ) (hl : 252≤n) (hh : n<336) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode21_28 n).1 (-1) (entryNode21_28 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode21_24_binding entryNode24_28_binding n hl hh
theorem entryNode21_28_support (n : ℕ) (hl : 252≤n) (hh : n<336) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode21_28 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode21_24_support entryNode24_28_support n hl hh
theorem entryNode21_28_depth (n : ℕ) (hl : 252≤n) (hh : n<336) : (entryNode21_28 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode21_24_depth entryNode24_28_depth n hl hh
def entryNode14_28 (n : ℕ) : Source × ℕ := if n<252 then entryNode14_21 n else entryNode21_28 n
theorem entryNode14_28_binding (n : ℕ) (hl : 168≤n) (hh : n<336) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode14_28 n).1 (-1) (entryNode14_28 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode14_21_binding entryNode21_28_binding n hl hh
theorem entryNode14_28_support (n : ℕ) (hl : 168≤n) (hh : n<336) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode14_28 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode14_21_support entryNode21_28_support n hl hh
theorem entryNode14_28_depth (n : ℕ) (hl : 168≤n) (hh : n<336) : (entryNode14_28 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode14_21_depth entryNode21_28_depth n hl hh
def entryNode0_28 (n : ℕ) : Source × ℕ := if n<168 then entryNode0_14 n else entryNode14_28 n
theorem entryNode0_28_binding (n : ℕ) (hl : 0≤n) (hh : n<336) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_28 n).1 (-1) (entryNode0_28 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_14_binding entryNode14_28_binding n hl hh
theorem entryNode0_28_support (n : ℕ) (hl : 0≤n) (hh : n<336) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_28 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_14_support entryNode14_28_support n hl hh
theorem entryNode0_28_depth (n : ℕ) (hl : 0≤n) (hh : n<336) : (entryNode0_28 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_14_depth entryNode14_28_depth n hl hh
def entryNode28_29 (n : ℕ) : Source × ℕ := entryPart28 (n-336)
theorem entryNode28_29_binding (n : ℕ) (hl : 336≤n) (hh : n<348) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode28_29 n).1 (-1) (entryNode28_29 n).2 := by
  have hn : n-336<12 := by omega
  have he : 336+(n-336)=n := by omega
  simpa only [entryNode28_29,he] using bindingPart28 ⟨n-336,hn⟩
theorem entryNode28_29_support (n : ℕ) (hl : 336≤n) (hh : n<348) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode28_29 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-336<12 := by omega
  have he : 336+(n-336)=n := by omega
  simpa only [entryNode28_29,he] using supportPart28 ⟨n-336,hn⟩
theorem entryNode28_29_depth (n : ℕ) (hl : 336≤n) (hh : n<348) : (entryNode28_29 n).2≤1 := by
  have hn : n-336<12 := by omega
  have he : 336+(n-336)=n := by omega
  simpa only [entryNode28_29,he] using depthPart28 ⟨n-336,hn⟩
def entryNode29_30 (n : ℕ) : Source × ℕ := entryPart29 (n-348)
theorem entryNode29_30_binding (n : ℕ) (hl : 348≤n) (hh : n<360) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode29_30 n).1 (-1) (entryNode29_30 n).2 := by
  have hn : n-348<12 := by omega
  have he : 348+(n-348)=n := by omega
  simpa only [entryNode29_30,he] using bindingPart29 ⟨n-348,hn⟩
theorem entryNode29_30_support (n : ℕ) (hl : 348≤n) (hh : n<360) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode29_30 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-348<12 := by omega
  have he : 348+(n-348)=n := by omega
  simpa only [entryNode29_30,he] using supportPart29 ⟨n-348,hn⟩
theorem entryNode29_30_depth (n : ℕ) (hl : 348≤n) (hh : n<360) : (entryNode29_30 n).2≤1 := by
  have hn : n-348<12 := by omega
  have he : 348+(n-348)=n := by omega
  simpa only [entryNode29_30,he] using depthPart29 ⟨n-348,hn⟩
def entryNode30_31 (n : ℕ) : Source × ℕ := entryPart30 (n-360)
theorem entryNode30_31_binding (n : ℕ) (hl : 360≤n) (hh : n<372) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode30_31 n).1 (-1) (entryNode30_31 n).2 := by
  have hn : n-360<12 := by omega
  have he : 360+(n-360)=n := by omega
  simpa only [entryNode30_31,he] using bindingPart30 ⟨n-360,hn⟩
theorem entryNode30_31_support (n : ℕ) (hl : 360≤n) (hh : n<372) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode30_31 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-360<12 := by omega
  have he : 360+(n-360)=n := by omega
  simpa only [entryNode30_31,he] using supportPart30 ⟨n-360,hn⟩
theorem entryNode30_31_depth (n : ℕ) (hl : 360≤n) (hh : n<372) : (entryNode30_31 n).2≤1 := by
  have hn : n-360<12 := by omega
  have he : 360+(n-360)=n := by omega
  simpa only [entryNode30_31,he] using depthPart30 ⟨n-360,hn⟩
def entryNode29_31 (n : ℕ) : Source × ℕ := if n<360 then entryNode29_30 n else entryNode30_31 n
theorem entryNode29_31_binding (n : ℕ) (hl : 348≤n) (hh : n<372) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode29_31 n).1 (-1) (entryNode29_31 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode29_30_binding entryNode30_31_binding n hl hh
theorem entryNode29_31_support (n : ℕ) (hl : 348≤n) (hh : n<372) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode29_31 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode29_30_support entryNode30_31_support n hl hh
theorem entryNode29_31_depth (n : ℕ) (hl : 348≤n) (hh : n<372) : (entryNode29_31 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode29_30_depth entryNode30_31_depth n hl hh
def entryNode28_31 (n : ℕ) : Source × ℕ := if n<348 then entryNode28_29 n else entryNode29_31 n
theorem entryNode28_31_binding (n : ℕ) (hl : 336≤n) (hh : n<372) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode28_31 n).1 (-1) (entryNode28_31 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode28_29_binding entryNode29_31_binding n hl hh
theorem entryNode28_31_support (n : ℕ) (hl : 336≤n) (hh : n<372) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode28_31 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode28_29_support entryNode29_31_support n hl hh
theorem entryNode28_31_depth (n : ℕ) (hl : 336≤n) (hh : n<372) : (entryNode28_31 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode28_29_depth entryNode29_31_depth n hl hh
def entryNode31_32 (n : ℕ) : Source × ℕ := entryPart31 (n-372)
theorem entryNode31_32_binding (n : ℕ) (hl : 372≤n) (hh : n<384) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode31_32 n).1 (-1) (entryNode31_32 n).2 := by
  have hn : n-372<12 := by omega
  have he : 372+(n-372)=n := by omega
  simpa only [entryNode31_32,he] using bindingPart31 ⟨n-372,hn⟩
theorem entryNode31_32_support (n : ℕ) (hl : 372≤n) (hh : n<384) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode31_32 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-372<12 := by omega
  have he : 372+(n-372)=n := by omega
  simpa only [entryNode31_32,he] using supportPart31 ⟨n-372,hn⟩
theorem entryNode31_32_depth (n : ℕ) (hl : 372≤n) (hh : n<384) : (entryNode31_32 n).2≤1 := by
  have hn : n-372<12 := by omega
  have he : 372+(n-372)=n := by omega
  simpa only [entryNode31_32,he] using depthPart31 ⟨n-372,hn⟩
def entryNode32_33 (n : ℕ) : Source × ℕ := entryPart32 (n-384)
theorem entryNode32_33_binding (n : ℕ) (hl : 384≤n) (hh : n<396) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode32_33 n).1 (-1) (entryNode32_33 n).2 := by
  have hn : n-384<12 := by omega
  have he : 384+(n-384)=n := by omega
  simpa only [entryNode32_33,he] using bindingPart32 ⟨n-384,hn⟩
theorem entryNode32_33_support (n : ℕ) (hl : 384≤n) (hh : n<396) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode32_33 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-384<12 := by omega
  have he : 384+(n-384)=n := by omega
  simpa only [entryNode32_33,he] using supportPart32 ⟨n-384,hn⟩
theorem entryNode32_33_depth (n : ℕ) (hl : 384≤n) (hh : n<396) : (entryNode32_33 n).2≤1 := by
  have hn : n-384<12 := by omega
  have he : 384+(n-384)=n := by omega
  simpa only [entryNode32_33,he] using depthPart32 ⟨n-384,hn⟩
def entryNode31_33 (n : ℕ) : Source × ℕ := if n<384 then entryNode31_32 n else entryNode32_33 n
theorem entryNode31_33_binding (n : ℕ) (hl : 372≤n) (hh : n<396) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode31_33 n).1 (-1) (entryNode31_33 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode31_32_binding entryNode32_33_binding n hl hh
theorem entryNode31_33_support (n : ℕ) (hl : 372≤n) (hh : n<396) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode31_33 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode31_32_support entryNode32_33_support n hl hh
theorem entryNode31_33_depth (n : ℕ) (hl : 372≤n) (hh : n<396) : (entryNode31_33 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode31_32_depth entryNode32_33_depth n hl hh
def entryNode33_34 (n : ℕ) : Source × ℕ := entryPart33 (n-396)
theorem entryNode33_34_binding (n : ℕ) (hl : 396≤n) (hh : n<408) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode33_34 n).1 (-1) (entryNode33_34 n).2 := by
  have hn : n-396<12 := by omega
  have he : 396+(n-396)=n := by omega
  simpa only [entryNode33_34,he] using bindingPart33 ⟨n-396,hn⟩
theorem entryNode33_34_support (n : ℕ) (hl : 396≤n) (hh : n<408) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode33_34 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-396<12 := by omega
  have he : 396+(n-396)=n := by omega
  simpa only [entryNode33_34,he] using supportPart33 ⟨n-396,hn⟩
theorem entryNode33_34_depth (n : ℕ) (hl : 396≤n) (hh : n<408) : (entryNode33_34 n).2≤1 := by
  have hn : n-396<12 := by omega
  have he : 396+(n-396)=n := by omega
  simpa only [entryNode33_34,he] using depthPart33 ⟨n-396,hn⟩
def entryNode34_35 (n : ℕ) : Source × ℕ := entryPart34 (n-408)
theorem entryNode34_35_binding (n : ℕ) (hl : 408≤n) (hh : n<420) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode34_35 n).1 (-1) (entryNode34_35 n).2 := by
  have hn : n-408<12 := by omega
  have he : 408+(n-408)=n := by omega
  simpa only [entryNode34_35,he] using bindingPart34 ⟨n-408,hn⟩
theorem entryNode34_35_support (n : ℕ) (hl : 408≤n) (hh : n<420) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode34_35 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-408<12 := by omega
  have he : 408+(n-408)=n := by omega
  simpa only [entryNode34_35,he] using supportPart34 ⟨n-408,hn⟩
theorem entryNode34_35_depth (n : ℕ) (hl : 408≤n) (hh : n<420) : (entryNode34_35 n).2≤1 := by
  have hn : n-408<12 := by omega
  have he : 408+(n-408)=n := by omega
  simpa only [entryNode34_35,he] using depthPart34 ⟨n-408,hn⟩
def entryNode33_35 (n : ℕ) : Source × ℕ := if n<408 then entryNode33_34 n else entryNode34_35 n
theorem entryNode33_35_binding (n : ℕ) (hl : 396≤n) (hh : n<420) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode33_35 n).1 (-1) (entryNode33_35 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode33_34_binding entryNode34_35_binding n hl hh
theorem entryNode33_35_support (n : ℕ) (hl : 396≤n) (hh : n<420) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode33_35 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode33_34_support entryNode34_35_support n hl hh
theorem entryNode33_35_depth (n : ℕ) (hl : 396≤n) (hh : n<420) : (entryNode33_35 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode33_34_depth entryNode34_35_depth n hl hh
def entryNode31_35 (n : ℕ) : Source × ℕ := if n<396 then entryNode31_33 n else entryNode33_35 n
theorem entryNode31_35_binding (n : ℕ) (hl : 372≤n) (hh : n<420) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode31_35 n).1 (-1) (entryNode31_35 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode31_33_binding entryNode33_35_binding n hl hh
theorem entryNode31_35_support (n : ℕ) (hl : 372≤n) (hh : n<420) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode31_35 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode31_33_support entryNode33_35_support n hl hh
theorem entryNode31_35_depth (n : ℕ) (hl : 372≤n) (hh : n<420) : (entryNode31_35 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode31_33_depth entryNode33_35_depth n hl hh
def entryNode28_35 (n : ℕ) : Source × ℕ := if n<372 then entryNode28_31 n else entryNode31_35 n
theorem entryNode28_35_binding (n : ℕ) (hl : 336≤n) (hh : n<420) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode28_35 n).1 (-1) (entryNode28_35 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode28_31_binding entryNode31_35_binding n hl hh
theorem entryNode28_35_support (n : ℕ) (hl : 336≤n) (hh : n<420) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode28_35 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode28_31_support entryNode31_35_support n hl hh
theorem entryNode28_35_depth (n : ℕ) (hl : 336≤n) (hh : n<420) : (entryNode28_35 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode28_31_depth entryNode31_35_depth n hl hh
def entryNode35_36 (n : ℕ) : Source × ℕ := entryPart35 (n-420)
theorem entryNode35_36_binding (n : ℕ) (hl : 420≤n) (hh : n<432) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode35_36 n).1 (-1) (entryNode35_36 n).2 := by
  have hn : n-420<12 := by omega
  have he : 420+(n-420)=n := by omega
  simpa only [entryNode35_36,he] using bindingPart35 ⟨n-420,hn⟩
theorem entryNode35_36_support (n : ℕ) (hl : 420≤n) (hh : n<432) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode35_36 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-420<12 := by omega
  have he : 420+(n-420)=n := by omega
  simpa only [entryNode35_36,he] using supportPart35 ⟨n-420,hn⟩
theorem entryNode35_36_depth (n : ℕ) (hl : 420≤n) (hh : n<432) : (entryNode35_36 n).2≤1 := by
  have hn : n-420<12 := by omega
  have he : 420+(n-420)=n := by omega
  simpa only [entryNode35_36,he] using depthPart35 ⟨n-420,hn⟩
def entryNode36_37 (n : ℕ) : Source × ℕ := entryPart36 (n-432)
theorem entryNode36_37_binding (n : ℕ) (hl : 432≤n) (hh : n<444) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode36_37 n).1 (-1) (entryNode36_37 n).2 := by
  have hn : n-432<12 := by omega
  have he : 432+(n-432)=n := by omega
  simpa only [entryNode36_37,he] using bindingPart36 ⟨n-432,hn⟩
theorem entryNode36_37_support (n : ℕ) (hl : 432≤n) (hh : n<444) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode36_37 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-432<12 := by omega
  have he : 432+(n-432)=n := by omega
  simpa only [entryNode36_37,he] using supportPart36 ⟨n-432,hn⟩
theorem entryNode36_37_depth (n : ℕ) (hl : 432≤n) (hh : n<444) : (entryNode36_37 n).2≤1 := by
  have hn : n-432<12 := by omega
  have he : 432+(n-432)=n := by omega
  simpa only [entryNode36_37,he] using depthPart36 ⟨n-432,hn⟩
def entryNode37_38 (n : ℕ) : Source × ℕ := entryPart37 (n-444)
theorem entryNode37_38_binding (n : ℕ) (hl : 444≤n) (hh : n<456) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode37_38 n).1 (-1) (entryNode37_38 n).2 := by
  have hn : n-444<12 := by omega
  have he : 444+(n-444)=n := by omega
  simpa only [entryNode37_38,he] using bindingPart37 ⟨n-444,hn⟩
theorem entryNode37_38_support (n : ℕ) (hl : 444≤n) (hh : n<456) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode37_38 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-444<12 := by omega
  have he : 444+(n-444)=n := by omega
  simpa only [entryNode37_38,he] using supportPart37 ⟨n-444,hn⟩
theorem entryNode37_38_depth (n : ℕ) (hl : 444≤n) (hh : n<456) : (entryNode37_38 n).2≤1 := by
  have hn : n-444<12 := by omega
  have he : 444+(n-444)=n := by omega
  simpa only [entryNode37_38,he] using depthPart37 ⟨n-444,hn⟩
def entryNode36_38 (n : ℕ) : Source × ℕ := if n<444 then entryNode36_37 n else entryNode37_38 n
theorem entryNode36_38_binding (n : ℕ) (hl : 432≤n) (hh : n<456) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode36_38 n).1 (-1) (entryNode36_38 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode36_37_binding entryNode37_38_binding n hl hh
theorem entryNode36_38_support (n : ℕ) (hl : 432≤n) (hh : n<456) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode36_38 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode36_37_support entryNode37_38_support n hl hh
theorem entryNode36_38_depth (n : ℕ) (hl : 432≤n) (hh : n<456) : (entryNode36_38 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode36_37_depth entryNode37_38_depth n hl hh
def entryNode35_38 (n : ℕ) : Source × ℕ := if n<432 then entryNode35_36 n else entryNode36_38 n
theorem entryNode35_38_binding (n : ℕ) (hl : 420≤n) (hh : n<456) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode35_38 n).1 (-1) (entryNode35_38 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode35_36_binding entryNode36_38_binding n hl hh
theorem entryNode35_38_support (n : ℕ) (hl : 420≤n) (hh : n<456) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode35_38 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode35_36_support entryNode36_38_support n hl hh
theorem entryNode35_38_depth (n : ℕ) (hl : 420≤n) (hh : n<456) : (entryNode35_38 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode35_36_depth entryNode36_38_depth n hl hh
def entryNode38_39 (n : ℕ) : Source × ℕ := entryPart38 (n-456)
theorem entryNode38_39_binding (n : ℕ) (hl : 456≤n) (hh : n<468) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode38_39 n).1 (-1) (entryNode38_39 n).2 := by
  have hn : n-456<12 := by omega
  have he : 456+(n-456)=n := by omega
  simpa only [entryNode38_39,he] using bindingPart38 ⟨n-456,hn⟩
theorem entryNode38_39_support (n : ℕ) (hl : 456≤n) (hh : n<468) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode38_39 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-456<12 := by omega
  have he : 456+(n-456)=n := by omega
  simpa only [entryNode38_39,he] using supportPart38 ⟨n-456,hn⟩
theorem entryNode38_39_depth (n : ℕ) (hl : 456≤n) (hh : n<468) : (entryNode38_39 n).2≤1 := by
  have hn : n-456<12 := by omega
  have he : 456+(n-456)=n := by omega
  simpa only [entryNode38_39,he] using depthPart38 ⟨n-456,hn⟩
def entryNode39_40 (n : ℕ) : Source × ℕ := entryPart39 (n-468)
theorem entryNode39_40_binding (n : ℕ) (hl : 468≤n) (hh : n<480) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode39_40 n).1 (-1) (entryNode39_40 n).2 := by
  have hn : n-468<12 := by omega
  have he : 468+(n-468)=n := by omega
  simpa only [entryNode39_40,he] using bindingPart39 ⟨n-468,hn⟩
theorem entryNode39_40_support (n : ℕ) (hl : 468≤n) (hh : n<480) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode39_40 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-468<12 := by omega
  have he : 468+(n-468)=n := by omega
  simpa only [entryNode39_40,he] using supportPart39 ⟨n-468,hn⟩
theorem entryNode39_40_depth (n : ℕ) (hl : 468≤n) (hh : n<480) : (entryNode39_40 n).2≤1 := by
  have hn : n-468<12 := by omega
  have he : 468+(n-468)=n := by omega
  simpa only [entryNode39_40,he] using depthPart39 ⟨n-468,hn⟩
def entryNode38_40 (n : ℕ) : Source × ℕ := if n<468 then entryNode38_39 n else entryNode39_40 n
theorem entryNode38_40_binding (n : ℕ) (hl : 456≤n) (hh : n<480) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode38_40 n).1 (-1) (entryNode38_40 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode38_39_binding entryNode39_40_binding n hl hh
theorem entryNode38_40_support (n : ℕ) (hl : 456≤n) (hh : n<480) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode38_40 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode38_39_support entryNode39_40_support n hl hh
theorem entryNode38_40_depth (n : ℕ) (hl : 456≤n) (hh : n<480) : (entryNode38_40 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode38_39_depth entryNode39_40_depth n hl hh
def entryNode40_41 (n : ℕ) : Source × ℕ := entryPart40 (n-480)
theorem entryNode40_41_binding (n : ℕ) (hl : 480≤n) (hh : n<492) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode40_41 n).1 (-1) (entryNode40_41 n).2 := by
  have hn : n-480<12 := by omega
  have he : 480+(n-480)=n := by omega
  simpa only [entryNode40_41,he] using bindingPart40 ⟨n-480,hn⟩
theorem entryNode40_41_support (n : ℕ) (hl : 480≤n) (hh : n<492) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode40_41 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-480<12 := by omega
  have he : 480+(n-480)=n := by omega
  simpa only [entryNode40_41,he] using supportPart40 ⟨n-480,hn⟩
theorem entryNode40_41_depth (n : ℕ) (hl : 480≤n) (hh : n<492) : (entryNode40_41 n).2≤1 := by
  have hn : n-480<12 := by omega
  have he : 480+(n-480)=n := by omega
  simpa only [entryNode40_41,he] using depthPart40 ⟨n-480,hn⟩
def entryNode41_42 (n : ℕ) : Source × ℕ := entryPart41 (n-492)
theorem entryNode41_42_binding (n : ℕ) (hl : 492≤n) (hh : n<504) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode41_42 n).1 (-1) (entryNode41_42 n).2 := by
  have hn : n-492<12 := by omega
  have he : 492+(n-492)=n := by omega
  simpa only [entryNode41_42,he] using bindingPart41 ⟨n-492,hn⟩
theorem entryNode41_42_support (n : ℕ) (hl : 492≤n) (hh : n<504) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode41_42 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-492<12 := by omega
  have he : 492+(n-492)=n := by omega
  simpa only [entryNode41_42,he] using supportPart41 ⟨n-492,hn⟩
theorem entryNode41_42_depth (n : ℕ) (hl : 492≤n) (hh : n<504) : (entryNode41_42 n).2≤1 := by
  have hn : n-492<12 := by omega
  have he : 492+(n-492)=n := by omega
  simpa only [entryNode41_42,he] using depthPart41 ⟨n-492,hn⟩
def entryNode40_42 (n : ℕ) : Source × ℕ := if n<492 then entryNode40_41 n else entryNode41_42 n
theorem entryNode40_42_binding (n : ℕ) (hl : 480≤n) (hh : n<504) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode40_42 n).1 (-1) (entryNode40_42 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode40_41_binding entryNode41_42_binding n hl hh
theorem entryNode40_42_support (n : ℕ) (hl : 480≤n) (hh : n<504) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode40_42 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode40_41_support entryNode41_42_support n hl hh
theorem entryNode40_42_depth (n : ℕ) (hl : 480≤n) (hh : n<504) : (entryNode40_42 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode40_41_depth entryNode41_42_depth n hl hh
def entryNode38_42 (n : ℕ) : Source × ℕ := if n<480 then entryNode38_40 n else entryNode40_42 n
theorem entryNode38_42_binding (n : ℕ) (hl : 456≤n) (hh : n<504) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode38_42 n).1 (-1) (entryNode38_42 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode38_40_binding entryNode40_42_binding n hl hh
theorem entryNode38_42_support (n : ℕ) (hl : 456≤n) (hh : n<504) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode38_42 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode38_40_support entryNode40_42_support n hl hh
theorem entryNode38_42_depth (n : ℕ) (hl : 456≤n) (hh : n<504) : (entryNode38_42 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode38_40_depth entryNode40_42_depth n hl hh
def entryNode35_42 (n : ℕ) : Source × ℕ := if n<456 then entryNode35_38 n else entryNode38_42 n
theorem entryNode35_42_binding (n : ℕ) (hl : 420≤n) (hh : n<504) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode35_42 n).1 (-1) (entryNode35_42 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode35_38_binding entryNode38_42_binding n hl hh
theorem entryNode35_42_support (n : ℕ) (hl : 420≤n) (hh : n<504) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode35_42 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode35_38_support entryNode38_42_support n hl hh
theorem entryNode35_42_depth (n : ℕ) (hl : 420≤n) (hh : n<504) : (entryNode35_42 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode35_38_depth entryNode38_42_depth n hl hh
def entryNode28_42 (n : ℕ) : Source × ℕ := if n<420 then entryNode28_35 n else entryNode35_42 n
theorem entryNode28_42_binding (n : ℕ) (hl : 336≤n) (hh : n<504) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode28_42 n).1 (-1) (entryNode28_42 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode28_35_binding entryNode35_42_binding n hl hh
theorem entryNode28_42_support (n : ℕ) (hl : 336≤n) (hh : n<504) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode28_42 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode28_35_support entryNode35_42_support n hl hh
theorem entryNode28_42_depth (n : ℕ) (hl : 336≤n) (hh : n<504) : (entryNode28_42 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode28_35_depth entryNode35_42_depth n hl hh
def entryNode42_43 (n : ℕ) : Source × ℕ := entryPart42 (n-504)
theorem entryNode42_43_binding (n : ℕ) (hl : 504≤n) (hh : n<516) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode42_43 n).1 (-1) (entryNode42_43 n).2 := by
  have hn : n-504<12 := by omega
  have he : 504+(n-504)=n := by omega
  simpa only [entryNode42_43,he] using bindingPart42 ⟨n-504,hn⟩
theorem entryNode42_43_support (n : ℕ) (hl : 504≤n) (hh : n<516) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode42_43 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-504<12 := by omega
  have he : 504+(n-504)=n := by omega
  simpa only [entryNode42_43,he] using supportPart42 ⟨n-504,hn⟩
theorem entryNode42_43_depth (n : ℕ) (hl : 504≤n) (hh : n<516) : (entryNode42_43 n).2≤1 := by
  have hn : n-504<12 := by omega
  have he : 504+(n-504)=n := by omega
  simpa only [entryNode42_43,he] using depthPart42 ⟨n-504,hn⟩
def entryNode43_44 (n : ℕ) : Source × ℕ := entryPart43 (n-516)
theorem entryNode43_44_binding (n : ℕ) (hl : 516≤n) (hh : n<528) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode43_44 n).1 (-1) (entryNode43_44 n).2 := by
  have hn : n-516<12 := by omega
  have he : 516+(n-516)=n := by omega
  simpa only [entryNode43_44,he] using bindingPart43 ⟨n-516,hn⟩
theorem entryNode43_44_support (n : ℕ) (hl : 516≤n) (hh : n<528) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode43_44 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-516<12 := by omega
  have he : 516+(n-516)=n := by omega
  simpa only [entryNode43_44,he] using supportPart43 ⟨n-516,hn⟩
theorem entryNode43_44_depth (n : ℕ) (hl : 516≤n) (hh : n<528) : (entryNode43_44 n).2≤1 := by
  have hn : n-516<12 := by omega
  have he : 516+(n-516)=n := by omega
  simpa only [entryNode43_44,he] using depthPart43 ⟨n-516,hn⟩
def entryNode44_45 (n : ℕ) : Source × ℕ := entryPart44 (n-528)
theorem entryNode44_45_binding (n : ℕ) (hl : 528≤n) (hh : n<540) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode44_45 n).1 (-1) (entryNode44_45 n).2 := by
  have hn : n-528<12 := by omega
  have he : 528+(n-528)=n := by omega
  simpa only [entryNode44_45,he] using bindingPart44 ⟨n-528,hn⟩
theorem entryNode44_45_support (n : ℕ) (hl : 528≤n) (hh : n<540) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode44_45 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-528<12 := by omega
  have he : 528+(n-528)=n := by omega
  simpa only [entryNode44_45,he] using supportPart44 ⟨n-528,hn⟩
theorem entryNode44_45_depth (n : ℕ) (hl : 528≤n) (hh : n<540) : (entryNode44_45 n).2≤1 := by
  have hn : n-528<12 := by omega
  have he : 528+(n-528)=n := by omega
  simpa only [entryNode44_45,he] using depthPart44 ⟨n-528,hn⟩
def entryNode43_45 (n : ℕ) : Source × ℕ := if n<528 then entryNode43_44 n else entryNode44_45 n
theorem entryNode43_45_binding (n : ℕ) (hl : 516≤n) (hh : n<540) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode43_45 n).1 (-1) (entryNode43_45 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode43_44_binding entryNode44_45_binding n hl hh
theorem entryNode43_45_support (n : ℕ) (hl : 516≤n) (hh : n<540) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode43_45 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode43_44_support entryNode44_45_support n hl hh
theorem entryNode43_45_depth (n : ℕ) (hl : 516≤n) (hh : n<540) : (entryNode43_45 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode43_44_depth entryNode44_45_depth n hl hh
def entryNode42_45 (n : ℕ) : Source × ℕ := if n<516 then entryNode42_43 n else entryNode43_45 n
theorem entryNode42_45_binding (n : ℕ) (hl : 504≤n) (hh : n<540) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode42_45 n).1 (-1) (entryNode42_45 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode42_43_binding entryNode43_45_binding n hl hh
theorem entryNode42_45_support (n : ℕ) (hl : 504≤n) (hh : n<540) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode42_45 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode42_43_support entryNode43_45_support n hl hh
theorem entryNode42_45_depth (n : ℕ) (hl : 504≤n) (hh : n<540) : (entryNode42_45 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode42_43_depth entryNode43_45_depth n hl hh
def entryNode45_46 (n : ℕ) : Source × ℕ := entryPart45 (n-540)
theorem entryNode45_46_binding (n : ℕ) (hl : 540≤n) (hh : n<552) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode45_46 n).1 (-1) (entryNode45_46 n).2 := by
  have hn : n-540<12 := by omega
  have he : 540+(n-540)=n := by omega
  simpa only [entryNode45_46,he] using bindingPart45 ⟨n-540,hn⟩
theorem entryNode45_46_support (n : ℕ) (hl : 540≤n) (hh : n<552) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode45_46 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-540<12 := by omega
  have he : 540+(n-540)=n := by omega
  simpa only [entryNode45_46,he] using supportPart45 ⟨n-540,hn⟩
theorem entryNode45_46_depth (n : ℕ) (hl : 540≤n) (hh : n<552) : (entryNode45_46 n).2≤1 := by
  have hn : n-540<12 := by omega
  have he : 540+(n-540)=n := by omega
  simpa only [entryNode45_46,he] using depthPart45 ⟨n-540,hn⟩
def entryNode46_47 (n : ℕ) : Source × ℕ := entryPart46 (n-552)
theorem entryNode46_47_binding (n : ℕ) (hl : 552≤n) (hh : n<564) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode46_47 n).1 (-1) (entryNode46_47 n).2 := by
  have hn : n-552<12 := by omega
  have he : 552+(n-552)=n := by omega
  simpa only [entryNode46_47,he] using bindingPart46 ⟨n-552,hn⟩
theorem entryNode46_47_support (n : ℕ) (hl : 552≤n) (hh : n<564) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode46_47 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-552<12 := by omega
  have he : 552+(n-552)=n := by omega
  simpa only [entryNode46_47,he] using supportPart46 ⟨n-552,hn⟩
theorem entryNode46_47_depth (n : ℕ) (hl : 552≤n) (hh : n<564) : (entryNode46_47 n).2≤1 := by
  have hn : n-552<12 := by omega
  have he : 552+(n-552)=n := by omega
  simpa only [entryNode46_47,he] using depthPart46 ⟨n-552,hn⟩
def entryNode45_47 (n : ℕ) : Source × ℕ := if n<552 then entryNode45_46 n else entryNode46_47 n
theorem entryNode45_47_binding (n : ℕ) (hl : 540≤n) (hh : n<564) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode45_47 n).1 (-1) (entryNode45_47 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode45_46_binding entryNode46_47_binding n hl hh
theorem entryNode45_47_support (n : ℕ) (hl : 540≤n) (hh : n<564) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode45_47 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode45_46_support entryNode46_47_support n hl hh
theorem entryNode45_47_depth (n : ℕ) (hl : 540≤n) (hh : n<564) : (entryNode45_47 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode45_46_depth entryNode46_47_depth n hl hh
def entryNode47_48 (n : ℕ) : Source × ℕ := entryPart47 (n-564)
theorem entryNode47_48_binding (n : ℕ) (hl : 564≤n) (hh : n<576) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode47_48 n).1 (-1) (entryNode47_48 n).2 := by
  have hn : n-564<12 := by omega
  have he : 564+(n-564)=n := by omega
  simpa only [entryNode47_48,he] using bindingPart47 ⟨n-564,hn⟩
theorem entryNode47_48_support (n : ℕ) (hl : 564≤n) (hh : n<576) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode47_48 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-564<12 := by omega
  have he : 564+(n-564)=n := by omega
  simpa only [entryNode47_48,he] using supportPart47 ⟨n-564,hn⟩
theorem entryNode47_48_depth (n : ℕ) (hl : 564≤n) (hh : n<576) : (entryNode47_48 n).2≤1 := by
  have hn : n-564<12 := by omega
  have he : 564+(n-564)=n := by omega
  simpa only [entryNode47_48,he] using depthPart47 ⟨n-564,hn⟩
def entryNode48_49 (n : ℕ) : Source × ℕ := entryPart48 (n-576)
theorem entryNode48_49_binding (n : ℕ) (hl : 576≤n) (hh : n<588) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode48_49 n).1 (-1) (entryNode48_49 n).2 := by
  have hn : n-576<12 := by omega
  have he : 576+(n-576)=n := by omega
  simpa only [entryNode48_49,he] using bindingPart48 ⟨n-576,hn⟩
theorem entryNode48_49_support (n : ℕ) (hl : 576≤n) (hh : n<588) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode48_49 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-576<12 := by omega
  have he : 576+(n-576)=n := by omega
  simpa only [entryNode48_49,he] using supportPart48 ⟨n-576,hn⟩
theorem entryNode48_49_depth (n : ℕ) (hl : 576≤n) (hh : n<588) : (entryNode48_49 n).2≤1 := by
  have hn : n-576<12 := by omega
  have he : 576+(n-576)=n := by omega
  simpa only [entryNode48_49,he] using depthPart48 ⟨n-576,hn⟩
def entryNode47_49 (n : ℕ) : Source × ℕ := if n<576 then entryNode47_48 n else entryNode48_49 n
theorem entryNode47_49_binding (n : ℕ) (hl : 564≤n) (hh : n<588) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode47_49 n).1 (-1) (entryNode47_49 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode47_48_binding entryNode48_49_binding n hl hh
theorem entryNode47_49_support (n : ℕ) (hl : 564≤n) (hh : n<588) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode47_49 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode47_48_support entryNode48_49_support n hl hh
theorem entryNode47_49_depth (n : ℕ) (hl : 564≤n) (hh : n<588) : (entryNode47_49 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode47_48_depth entryNode48_49_depth n hl hh
def entryNode45_49 (n : ℕ) : Source × ℕ := if n<564 then entryNode45_47 n else entryNode47_49 n
theorem entryNode45_49_binding (n : ℕ) (hl : 540≤n) (hh : n<588) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode45_49 n).1 (-1) (entryNode45_49 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode45_47_binding entryNode47_49_binding n hl hh
theorem entryNode45_49_support (n : ℕ) (hl : 540≤n) (hh : n<588) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode45_49 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode45_47_support entryNode47_49_support n hl hh
theorem entryNode45_49_depth (n : ℕ) (hl : 540≤n) (hh : n<588) : (entryNode45_49 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode45_47_depth entryNode47_49_depth n hl hh
def entryNode42_49 (n : ℕ) : Source × ℕ := if n<540 then entryNode42_45 n else entryNode45_49 n
theorem entryNode42_49_binding (n : ℕ) (hl : 504≤n) (hh : n<588) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode42_49 n).1 (-1) (entryNode42_49 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode42_45_binding entryNode45_49_binding n hl hh
theorem entryNode42_49_support (n : ℕ) (hl : 504≤n) (hh : n<588) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode42_49 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode42_45_support entryNode45_49_support n hl hh
theorem entryNode42_49_depth (n : ℕ) (hl : 504≤n) (hh : n<588) : (entryNode42_49 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode42_45_depth entryNode45_49_depth n hl hh
def entryNode49_50 (n : ℕ) : Source × ℕ := entryPart49 (n-588)
theorem entryNode49_50_binding (n : ℕ) (hl : 588≤n) (hh : n<600) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode49_50 n).1 (-1) (entryNode49_50 n).2 := by
  have hn : n-588<12 := by omega
  have he : 588+(n-588)=n := by omega
  simpa only [entryNode49_50,he] using bindingPart49 ⟨n-588,hn⟩
theorem entryNode49_50_support (n : ℕ) (hl : 588≤n) (hh : n<600) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode49_50 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-588<12 := by omega
  have he : 588+(n-588)=n := by omega
  simpa only [entryNode49_50,he] using supportPart49 ⟨n-588,hn⟩
theorem entryNode49_50_depth (n : ℕ) (hl : 588≤n) (hh : n<600) : (entryNode49_50 n).2≤1 := by
  have hn : n-588<12 := by omega
  have he : 588+(n-588)=n := by omega
  simpa only [entryNode49_50,he] using depthPart49 ⟨n-588,hn⟩
def entryNode50_51 (n : ℕ) : Source × ℕ := entryPart50 (n-600)
theorem entryNode50_51_binding (n : ℕ) (hl : 600≤n) (hh : n<612) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode50_51 n).1 (-1) (entryNode50_51 n).2 := by
  have hn : n-600<12 := by omega
  have he : 600+(n-600)=n := by omega
  simpa only [entryNode50_51,he] using bindingPart50 ⟨n-600,hn⟩
theorem entryNode50_51_support (n : ℕ) (hl : 600≤n) (hh : n<612) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode50_51 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-600<12 := by omega
  have he : 600+(n-600)=n := by omega
  simpa only [entryNode50_51,he] using supportPart50 ⟨n-600,hn⟩
theorem entryNode50_51_depth (n : ℕ) (hl : 600≤n) (hh : n<612) : (entryNode50_51 n).2≤1 := by
  have hn : n-600<12 := by omega
  have he : 600+(n-600)=n := by omega
  simpa only [entryNode50_51,he] using depthPart50 ⟨n-600,hn⟩
def entryNode51_52 (n : ℕ) : Source × ℕ := entryPart51 (n-612)
theorem entryNode51_52_binding (n : ℕ) (hl : 612≤n) (hh : n<624) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode51_52 n).1 (-1) (entryNode51_52 n).2 := by
  have hn : n-612<12 := by omega
  have he : 612+(n-612)=n := by omega
  simpa only [entryNode51_52,he] using bindingPart51 ⟨n-612,hn⟩
theorem entryNode51_52_support (n : ℕ) (hl : 612≤n) (hh : n<624) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode51_52 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-612<12 := by omega
  have he : 612+(n-612)=n := by omega
  simpa only [entryNode51_52,he] using supportPart51 ⟨n-612,hn⟩
theorem entryNode51_52_depth (n : ℕ) (hl : 612≤n) (hh : n<624) : (entryNode51_52 n).2≤1 := by
  have hn : n-612<12 := by omega
  have he : 612+(n-612)=n := by omega
  simpa only [entryNode51_52,he] using depthPart51 ⟨n-612,hn⟩
def entryNode50_52 (n : ℕ) : Source × ℕ := if n<612 then entryNode50_51 n else entryNode51_52 n
theorem entryNode50_52_binding (n : ℕ) (hl : 600≤n) (hh : n<624) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode50_52 n).1 (-1) (entryNode50_52 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode50_51_binding entryNode51_52_binding n hl hh
theorem entryNode50_52_support (n : ℕ) (hl : 600≤n) (hh : n<624) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode50_52 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode50_51_support entryNode51_52_support n hl hh
theorem entryNode50_52_depth (n : ℕ) (hl : 600≤n) (hh : n<624) : (entryNode50_52 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode50_51_depth entryNode51_52_depth n hl hh
def entryNode49_52 (n : ℕ) : Source × ℕ := if n<600 then entryNode49_50 n else entryNode50_52 n
theorem entryNode49_52_binding (n : ℕ) (hl : 588≤n) (hh : n<624) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode49_52 n).1 (-1) (entryNode49_52 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode49_50_binding entryNode50_52_binding n hl hh
theorem entryNode49_52_support (n : ℕ) (hl : 588≤n) (hh : n<624) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode49_52 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode49_50_support entryNode50_52_support n hl hh
theorem entryNode49_52_depth (n : ℕ) (hl : 588≤n) (hh : n<624) : (entryNode49_52 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode49_50_depth entryNode50_52_depth n hl hh
def entryNode52_53 (n : ℕ) : Source × ℕ := entryPart52 (n-624)
theorem entryNode52_53_binding (n : ℕ) (hl : 624≤n) (hh : n<636) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode52_53 n).1 (-1) (entryNode52_53 n).2 := by
  have hn : n-624<12 := by omega
  have he : 624+(n-624)=n := by omega
  simpa only [entryNode52_53,he] using bindingPart52 ⟨n-624,hn⟩
theorem entryNode52_53_support (n : ℕ) (hl : 624≤n) (hh : n<636) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode52_53 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-624<12 := by omega
  have he : 624+(n-624)=n := by omega
  simpa only [entryNode52_53,he] using supportPart52 ⟨n-624,hn⟩
theorem entryNode52_53_depth (n : ℕ) (hl : 624≤n) (hh : n<636) : (entryNode52_53 n).2≤1 := by
  have hn : n-624<12 := by omega
  have he : 624+(n-624)=n := by omega
  simpa only [entryNode52_53,he] using depthPart52 ⟨n-624,hn⟩
def entryNode53_54 (n : ℕ) : Source × ℕ := entryPart53 (n-636)
theorem entryNode53_54_binding (n : ℕ) (hl : 636≤n) (hh : n<648) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode53_54 n).1 (-1) (entryNode53_54 n).2 := by
  have hn : n-636<12 := by omega
  have he : 636+(n-636)=n := by omega
  simpa only [entryNode53_54,he] using bindingPart53 ⟨n-636,hn⟩
theorem entryNode53_54_support (n : ℕ) (hl : 636≤n) (hh : n<648) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode53_54 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-636<12 := by omega
  have he : 636+(n-636)=n := by omega
  simpa only [entryNode53_54,he] using supportPart53 ⟨n-636,hn⟩
theorem entryNode53_54_depth (n : ℕ) (hl : 636≤n) (hh : n<648) : (entryNode53_54 n).2≤1 := by
  have hn : n-636<12 := by omega
  have he : 636+(n-636)=n := by omega
  simpa only [entryNode53_54,he] using depthPart53 ⟨n-636,hn⟩
def entryNode52_54 (n : ℕ) : Source × ℕ := if n<636 then entryNode52_53 n else entryNode53_54 n
theorem entryNode52_54_binding (n : ℕ) (hl : 624≤n) (hh : n<648) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode52_54 n).1 (-1) (entryNode52_54 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode52_53_binding entryNode53_54_binding n hl hh
theorem entryNode52_54_support (n : ℕ) (hl : 624≤n) (hh : n<648) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode52_54 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode52_53_support entryNode53_54_support n hl hh
theorem entryNode52_54_depth (n : ℕ) (hl : 624≤n) (hh : n<648) : (entryNode52_54 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode52_53_depth entryNode53_54_depth n hl hh
def entryNode54_55 (n : ℕ) : Source × ℕ := entryPart54 (n-648)
theorem entryNode54_55_binding (n : ℕ) (hl : 648≤n) (hh : n<660) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode54_55 n).1 (-1) (entryNode54_55 n).2 := by
  have hn : n-648<12 := by omega
  have he : 648+(n-648)=n := by omega
  simpa only [entryNode54_55,he] using bindingPart54 ⟨n-648,hn⟩
theorem entryNode54_55_support (n : ℕ) (hl : 648≤n) (hh : n<660) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode54_55 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-648<12 := by omega
  have he : 648+(n-648)=n := by omega
  simpa only [entryNode54_55,he] using supportPart54 ⟨n-648,hn⟩
theorem entryNode54_55_depth (n : ℕ) (hl : 648≤n) (hh : n<660) : (entryNode54_55 n).2≤1 := by
  have hn : n-648<12 := by omega
  have he : 648+(n-648)=n := by omega
  simpa only [entryNode54_55,he] using depthPart54 ⟨n-648,hn⟩
def entryNode55_56 (n : ℕ) : Source × ℕ := entryPart55 (n-660)
theorem entryNode55_56_binding (n : ℕ) (hl : 660≤n) (hh : n<672) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode55_56 n).1 (-1) (entryNode55_56 n).2 := by
  have hn : n-660<12 := by omega
  have he : 660+(n-660)=n := by omega
  simpa only [entryNode55_56,he] using bindingPart55 ⟨n-660,hn⟩
theorem entryNode55_56_support (n : ℕ) (hl : 660≤n) (hh : n<672) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode55_56 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-660<12 := by omega
  have he : 660+(n-660)=n := by omega
  simpa only [entryNode55_56,he] using supportPart55 ⟨n-660,hn⟩
theorem entryNode55_56_depth (n : ℕ) (hl : 660≤n) (hh : n<672) : (entryNode55_56 n).2≤1 := by
  have hn : n-660<12 := by omega
  have he : 660+(n-660)=n := by omega
  simpa only [entryNode55_56,he] using depthPart55 ⟨n-660,hn⟩
def entryNode54_56 (n : ℕ) : Source × ℕ := if n<660 then entryNode54_55 n else entryNode55_56 n
theorem entryNode54_56_binding (n : ℕ) (hl : 648≤n) (hh : n<672) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode54_56 n).1 (-1) (entryNode54_56 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode54_55_binding entryNode55_56_binding n hl hh
theorem entryNode54_56_support (n : ℕ) (hl : 648≤n) (hh : n<672) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode54_56 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode54_55_support entryNode55_56_support n hl hh
theorem entryNode54_56_depth (n : ℕ) (hl : 648≤n) (hh : n<672) : (entryNode54_56 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode54_55_depth entryNode55_56_depth n hl hh
def entryNode52_56 (n : ℕ) : Source × ℕ := if n<648 then entryNode52_54 n else entryNode54_56 n
theorem entryNode52_56_binding (n : ℕ) (hl : 624≤n) (hh : n<672) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode52_56 n).1 (-1) (entryNode52_56 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode52_54_binding entryNode54_56_binding n hl hh
theorem entryNode52_56_support (n : ℕ) (hl : 624≤n) (hh : n<672) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode52_56 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode52_54_support entryNode54_56_support n hl hh
theorem entryNode52_56_depth (n : ℕ) (hl : 624≤n) (hh : n<672) : (entryNode52_56 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode52_54_depth entryNode54_56_depth n hl hh
def entryNode49_56 (n : ℕ) : Source × ℕ := if n<624 then entryNode49_52 n else entryNode52_56 n
theorem entryNode49_56_binding (n : ℕ) (hl : 588≤n) (hh : n<672) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode49_56 n).1 (-1) (entryNode49_56 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode49_52_binding entryNode52_56_binding n hl hh
theorem entryNode49_56_support (n : ℕ) (hl : 588≤n) (hh : n<672) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode49_56 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode49_52_support entryNode52_56_support n hl hh
theorem entryNode49_56_depth (n : ℕ) (hl : 588≤n) (hh : n<672) : (entryNode49_56 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode49_52_depth entryNode52_56_depth n hl hh
def entryNode42_56 (n : ℕ) : Source × ℕ := if n<588 then entryNode42_49 n else entryNode49_56 n
theorem entryNode42_56_binding (n : ℕ) (hl : 504≤n) (hh : n<672) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode42_56 n).1 (-1) (entryNode42_56 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode42_49_binding entryNode49_56_binding n hl hh
theorem entryNode42_56_support (n : ℕ) (hl : 504≤n) (hh : n<672) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode42_56 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode42_49_support entryNode49_56_support n hl hh
theorem entryNode42_56_depth (n : ℕ) (hl : 504≤n) (hh : n<672) : (entryNode42_56 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode42_49_depth entryNode49_56_depth n hl hh
def entryNode28_56 (n : ℕ) : Source × ℕ := if n<504 then entryNode28_42 n else entryNode42_56 n
theorem entryNode28_56_binding (n : ℕ) (hl : 336≤n) (hh : n<672) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode28_56 n).1 (-1) (entryNode28_56 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode28_42_binding entryNode42_56_binding n hl hh
theorem entryNode28_56_support (n : ℕ) (hl : 336≤n) (hh : n<672) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode28_56 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode28_42_support entryNode42_56_support n hl hh
theorem entryNode28_56_depth (n : ℕ) (hl : 336≤n) (hh : n<672) : (entryNode28_56 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode28_42_depth entryNode42_56_depth n hl hh
def entryNode0_56 (n : ℕ) : Source × ℕ := if n<336 then entryNode0_28 n else entryNode28_56 n
theorem entryNode0_56_binding (n : ℕ) (hl : 0≤n) (hh : n<672) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_56 n).1 (-1) (entryNode0_56 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_28_binding entryNode28_56_binding n hl hh
theorem entryNode0_56_support (n : ℕ) (hl : 0≤n) (hh : n<672) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_56 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_28_support entryNode28_56_support n hl hh
theorem entryNode0_56_depth (n : ℕ) (hl : 0≤n) (hh : n<672) : (entryNode0_56 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_28_depth entryNode28_56_depth n hl hh
def entry (i : Fin 672) : Source × ℕ := entryNode0_56 i.val
theorem input_binding (i : Fin 672) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusStages.inputs i.val=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entry i).1 (-1) (entry i).2 := entryNode0_56_binding i.val (Nat.zero_le _) i.isLt
theorem depth_bound (i : Fin 672) : (entry i).2≤1 := entryNode0_56_depth i.val (Nat.zero_le _) i.isLt
theorem leading_support (i : Fin 672) : ∀ t∈QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entry i).1 (-1), t.2.1<607 := by
  intro t ht
  exact of_decide_eq_true ((List.all_eq_true.mp (entryNode0_56_support i.val (Nat.zero_le _) i.isLt)) t ht)
#print axioms input_binding
#print axioms leading_support
#print axioms depth_bound
end QuantitativeArithmeticSmallLevelTwentySevenZeroJetSecondMinusSourceBinding
end
end
