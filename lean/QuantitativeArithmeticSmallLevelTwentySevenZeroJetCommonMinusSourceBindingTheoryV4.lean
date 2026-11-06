module
public import QuantitativeArithmeticFiniteRangeCertificatesV1

public import QuantitativeArithmeticSmallLevelTwentySevenZeroJetCodeV1
public import QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStagesTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenZeroJetTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusSourceBinding. Original statements and local scopes are retained; interval proofs share the general join lemma. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusSourceBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family with shared interval proofs. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusSourceBinding
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
theorem bindingPart0 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (0+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart0 i.val).1 (-1) (entryPart0 i.val).2 := by decide +kernel
theorem supportPart0 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart0 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart0 : ∀ i : Fin 12, (entryPart0 i.val).2≤1 := by decide +kernel

def entryPart1 : ℕ → Source × ℕ
  | 0 => (sourceRaw32,1)
  | 1 => (sourceRaw77,1)
  | 2 => (sourceRaw144,1)
  | 3 => (sourceRaw2,0)
  | 4 => (sourceRaw31,0)
  | 5 => (sourceRaw17,0)
  | 6 => (sourceRaw77,0)
  | 7 => (sourceRaw83,0)
  | 8 => (sourceRaw144,0)
  | 9 => (sourceRaw149,0)
  | 10 => (sourceRaw236,0)
  | 11 => (sourceRaw568,0)
  | _ => (sourceRaw14,0)
theorem bindingPart1 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (12+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart1 i.val).1 (-1) (entryPart1 i.val).2 := by decide +kernel
theorem supportPart1 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart1 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart1 : ∀ i : Fin 12, (entryPart1 i.val).2≤1 := by decide +kernel

def entryPart2 : ℕ → Source × ℕ
  | 0 => (sourceRaw18,1)
  | 1 => (sourceRaw1,1)
  | 2 => (sourceRaw569,1)
  | 3 => (sourceRaw1568,1)
  | 4 => (sourceRaw569,0)
  | 5 => (sourceRaw570,0)
  | 6 => (sourceRaw1249,0)
  | 7 => (sourceRaw1250,0)
  | 8 => (sourceRaw1282,0)
  | 9 => (sourceRaw1365,0)
  | 10 => (sourceRaw1373,0)
  | 11 => (sourceRaw1395,0)
  | _ => (sourceRaw14,0)
theorem bindingPart2 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (24+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart2 i.val).1 (-1) (entryPart2 i.val).2 := by decide +kernel
theorem supportPart2 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart2 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart2 : ∀ i : Fin 12, (entryPart2 i.val).2≤1 := by decide +kernel

def entryPart3 : ℕ → Source × ℕ
  | 0 => (sourceRaw1428,0)
  | 1 => (sourceRaw1465,0)
  | 2 => (sourceRaw1568,0)
  | 3 => (sourceRaw1831,0)
  | 4 => (sourceRaw1832,0)
  | 5 => (sourceRaw1833,0)
  | 6 => (sourceRaw1834,0)
  | 7 => (sourceRaw1838,0)
  | 8 => (sourceRaw2651,0)
  | 9 => (sourceRaw666,1)
  | 10 => (sourceRaw970,1)
  | 11 => (sourceRaw978,1)
  | _ => (sourceRaw14,0)
theorem bindingPart3 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (36+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart3 i.val).1 (-1) (entryPart3 i.val).2 := by decide +kernel
theorem supportPart3 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart3 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart3 : ∀ i : Fin 12, (entryPart3 i.val).2≤1 := by decide +kernel

def entryPart4 : ℕ → Source × ℕ
  | 0 => (sourceRaw988,1)
  | 1 => (sourceRaw1003,1)
  | 2 => (sourceRaw1033,1)
  | 3 => (sourceRaw2257,1)
  | 4 => (sourceRaw3,0)
  | 5 => (sourceRaw4,0)
  | 6 => (sourceRaw5,0)
  | 7 => (sourceRaw6,0)
  | 8 => (sourceRaw7,0)
  | 9 => (sourceRaw8,0)
  | 10 => (sourceRaw9,0)
  | 11 => (sourceRaw10,0)
  | _ => (sourceRaw14,0)
theorem bindingPart4 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (48+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart4 i.val).1 (-1) (entryPart4 i.val).2 := by decide +kernel
theorem supportPart4 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart4 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart4 : ∀ i : Fin 12, (entryPart4 i.val).2≤1 := by decide +kernel

def entryPart5 : ℕ → Source × ℕ
  | 0 => (sourceRaw11,0)
  | 1 => (sourceRaw12,0)
  | 2 => (sourceRaw13,0)
  | 3 => (sourceRaw15,0)
  | 4 => (sourceRaw16,0)
  | 5 => (sourceRaw20,0)
  | 6 => (sourceRaw21,0)
  | 7 => (sourceRaw22,0)
  | 8 => (sourceRaw23,0)
  | 9 => (sourceRaw25,0)
  | 10 => (sourceRaw26,0)
  | 11 => (sourceRaw28,0)
  | _ => (sourceRaw14,0)
theorem bindingPart5 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (60+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart5 i.val).1 (-1) (entryPart5 i.val).2 := by decide +kernel
theorem supportPart5 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart5 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart5 : ∀ i : Fin 12, (entryPart5 i.val).2≤1 := by decide +kernel

def entryPart6 : ℕ → Source × ℕ
  | 0 => (sourceRaw29,0)
  | 1 => (sourceRaw30,0)
  | 2 => (sourceRaw33,0)
  | 3 => (sourceRaw34,0)
  | 4 => (sourceRaw35,0)
  | 5 => (sourceRaw36,0)
  | 6 => (sourceRaw37,0)
  | 7 => (sourceRaw38,0)
  | 8 => (sourceRaw39,0)
  | 9 => (sourceRaw40,0)
  | 10 => (sourceRaw41,0)
  | 11 => (sourceRaw42,0)
  | _ => (sourceRaw14,0)
theorem bindingPart6 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (72+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart6 i.val).1 (-1) (entryPart6 i.val).2 := by decide +kernel
theorem supportPart6 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart6 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart6 : ∀ i : Fin 12, (entryPart6 i.val).2≤1 := by decide +kernel

def entryPart7 : ℕ → Source × ℕ
  | 0 => (sourceRaw43,0)
  | 1 => (sourceRaw44,0)
  | 2 => (sourceRaw46,0)
  | 3 => (sourceRaw47,0)
  | 4 => (sourceRaw48,0)
  | 5 => (sourceRaw73,0)
  | 6 => (sourceRaw74,0)
  | 7 => (sourceRaw75,0)
  | 8 => (sourceRaw79,0)
  | 9 => (sourceRaw80,0)
  | 10 => (sourceRaw81,0)
  | 11 => (sourceRaw112,0)
  | _ => (sourceRaw14,0)
theorem bindingPart7 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (84+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart7 i.val).1 (-1) (entryPart7 i.val).2 := by decide +kernel
theorem supportPart7 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart7 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart7 : ∀ i : Fin 12, (entryPart7 i.val).2≤1 := by decide +kernel

def entryPart8 : ℕ → Source × ℕ
  | 0 => (sourceRaw116,0)
  | 1 => (sourceRaw120,0)
  | 2 => (sourceRaw145,0)
  | 3 => (sourceRaw235,0)
  | 4 => (sourceRaw573,0)
  | 5 => (sourceRaw574,0)
  | 6 => (sourceRaw585,0)
  | 7 => (sourceRaw586,0)
  | 8 => (sourceRaw593,0)
  | 9 => (sourceRaw594,0)
  | 10 => (sourceRaw595,0)
  | 11 => (sourceRaw596,0)
  | _ => (sourceRaw14,0)
theorem bindingPart8 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (96+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart8 i.val).1 (-1) (entryPart8 i.val).2 := by decide +kernel
theorem supportPart8 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart8 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart8 : ∀ i : Fin 12, (entryPart8 i.val).2≤1 := by decide +kernel

def entryPart9 : ℕ → Source × ℕ
  | 0 => (sourceRaw599,0)
  | 1 => (sourceRaw600,0)
  | 2 => (sourceRaw603,0)
  | 3 => (sourceRaw604,0)
  | 4 => (sourceRaw666,0)
  | 5 => (sourceRaw682,1)
  | 6 => (sourceRaw723,1)
  | 7 => (sourceRaw667,0)
  | 8 => (sourceRaw668,0)
  | 9 => (sourceRaw669,0)
  | 10 => (sourceRaw670,0)
  | 11 => (sourceRaw675,0)
  | _ => (sourceRaw14,0)
theorem bindingPart9 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (108+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart9 i.val).1 (-1) (entryPart9 i.val).2 := by decide +kernel
theorem supportPart9 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart9 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart9 : ∀ i : Fin 12, (entryPart9 i.val).2≤1 := by decide +kernel

def entryPart10 : ℕ → Source × ℕ
  | 0 => (sourceRaw676,0)
  | 1 => (sourceRaw681,0)
  | 2 => (sourceRaw695,0)
  | 3 => (sourceRaw696,0)
  | 4 => (sourceRaw673,0)
  | 5 => (sourceRaw674,0)
  | 6 => (sourceRaw689,0)
  | 7 => (sourceRaw690,0)
  | 8 => (sourceRaw765,0)
  | 9 => (sourceRaw766,0)
  | 10 => (sourceRaw769,0)
  | 11 => (sourceRaw770,0)
  | _ => (sourceRaw14,0)
theorem bindingPart10 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (120+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart10 i.val).1 (-1) (entryPart10 i.val).2 := by decide +kernel
theorem supportPart10 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart10 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart10 : ∀ i : Fin 12, (entryPart10 i.val).2≤1 := by decide +kernel

def entryPart11 : ℕ → Source × ℕ
  | 0 => (sourceRaw970,0)
  | 1 => (sourceRaw739,0)
  | 2 => (sourceRaw972,0)
  | 3 => (sourceRaw974,0)
  | 4 => (sourceRaw685,0)
  | 5 => (sourceRaw697,0)
  | 6 => (sourceRaw698,0)
  | 7 => (sourceRaw686,0)
  | 8 => (sourceRaw853,0)
  | 9 => (sourceRaw993,0)
  | 10 => (sourceRaw975,0)
  | 11 => (sourceRaw995,0)
  | _ => (sourceRaw14,0)
theorem bindingPart11 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (132+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart11 i.val).1 (-1) (entryPart11 i.val).2 := by decide +kernel
theorem supportPart11 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart11 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart11 : ∀ i : Fin 12, (entryPart11 i.val).2≤1 := by decide +kernel

def entryPart12 : ℕ → Source × ℕ
  | 0 => (sourceRaw844,0)
  | 1 => (sourceRaw1002,0)
  | 2 => (sourceRaw1003,0)
  | 3 => (sourceRaw1004,0)
  | 4 => (sourceRaw680,0)
  | 5 => (sourceRaw679,0)
  | 6 => (sourceRaw1033,0)
  | 7 => (sourceRaw1035,0)
  | 8 => (sourceRaw1036,0)
  | 9 => (sourceRaw1038,0)
  | 10 => (sourceRaw1068,0)
  | 11 => (sourceRaw1069,0)
  | _ => (sourceRaw14,0)
theorem bindingPart12 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (144+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart12 i.val).1 (-1) (entryPart12 i.val).2 := by decide +kernel
theorem supportPart12 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart12 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart12 : ∀ i : Fin 12, (entryPart12 i.val).2≤1 := by decide +kernel

def entryPart13 : ℕ → Source × ℕ
  | 0 => (sourceRaw1083,0)
  | 1 => (sourceRaw944,0)
  | 2 => (sourceRaw1096,0)
  | 3 => (sourceRaw1211,0)
  | 4 => (sourceRaw687,0)
  | 5 => (sourceRaw798,0)
  | 6 => (sourceRaw986,0)
  | 7 => (sourceRaw694,0)
  | 8 => (sourceRaw1008,0)
  | 9 => (sourceRaw1018,0)
  | 10 => (sourceRaw1040,0)
  | 11 => (sourceRaw693,0)
  | _ => (sourceRaw14,0)
theorem bindingPart13 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (156+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart13 i.val).1 (-1) (entryPart13 i.val).2 := by decide +kernel
theorem supportPart13 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart13 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart13 : ∀ i : Fin 12, (entryPart13 i.val).2≤1 := by decide +kernel

def entryPart14 : ℕ → Source × ℕ
  | 0 => (sourceRaw1247,0)
  | 1 => (sourceRaw1252,0)
  | 2 => (sourceRaw1253,0)
  | 3 => (sourceRaw1254,0)
  | 4 => (sourceRaw1255,0)
  | 5 => (sourceRaw1256,0)
  | 6 => (sourceRaw1260,0)
  | 7 => (sourceRaw1261,0)
  | 8 => (sourceRaw1262,0)
  | 9 => (sourceRaw1264,0)
  | 10 => (sourceRaw1265,0)
  | 11 => (sourceRaw1266,0)
  | _ => (sourceRaw14,0)
theorem bindingPart14 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (168+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart14 i.val).1 (-1) (entryPart14 i.val).2 := by decide +kernel
theorem supportPart14 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart14 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart14 : ∀ i : Fin 12, (entryPart14 i.val).2≤1 := by decide +kernel

def entryPart15 : ℕ → Source × ℕ
  | 0 => (sourceRaw1270,0)
  | 1 => (sourceRaw1271,0)
  | 2 => (sourceRaw1275,0)
  | 3 => (sourceRaw1276,0)
  | 4 => (sourceRaw1277,0)
  | 5 => (sourceRaw1280,0)
  | 6 => (sourceRaw1281,0)
  | 7 => (sourceRaw1283,0)
  | 8 => (sourceRaw1284,0)
  | 9 => (sourceRaw1285,0)
  | 10 => (sourceRaw1289,0)
  | 11 => (sourceRaw1290,0)
  | _ => (sourceRaw14,0)
theorem bindingPart15 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (180+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart15 i.val).1 (-1) (entryPart15 i.val).2 := by decide +kernel
theorem supportPart15 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart15 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart15 : ∀ i : Fin 12, (entryPart15 i.val).2≤1 := by decide +kernel

def entryPart16 : ℕ → Source × ℕ
  | 0 => (sourceRaw1294,0)
  | 1 => (sourceRaw1295,0)
  | 2 => (sourceRaw1303,0)
  | 3 => (sourceRaw1325,0)
  | 4 => (sourceRaw1326,0)
  | 5 => (sourceRaw1330,0)
  | 6 => (sourceRaw1331,0)
  | 7 => (sourceRaw1336,0)
  | 8 => (sourceRaw1338,0)
  | 9 => (sourceRaw1366,0)
  | 10 => (sourceRaw1372,0)
  | 11 => (sourceRaw1377,0)
  | _ => (sourceRaw14,0)
theorem bindingPart16 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (192+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart16 i.val).1 (-1) (entryPart16 i.val).2 := by decide +kernel
theorem supportPart16 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart16 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart16 : ∀ i : Fin 12, (entryPart16 i.val).2≤1 := by decide +kernel

def entryPart17 : ℕ → Source × ℕ
  | 0 => (sourceRaw1396,0)
  | 1 => (sourceRaw1400,0)
  | 2 => (sourceRaw1401,0)
  | 3 => (sourceRaw1429,0)
  | 4 => (sourceRaw1694,0)
  | 5 => (sourceRaw1696,0)
  | 6 => (sourceRaw1835,0)
  | 7 => (sourceRaw1836,0)
  | 8 => (sourceRaw1857,0)
  | 9 => (sourceRaw1858,0)
  | 10 => (sourceRaw1861,0)
  | 11 => (sourceRaw1862,0)
  | _ => (sourceRaw14,0)
theorem bindingPart17 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (204+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart17 i.val).1 (-1) (entryPart17 i.val).2 := by decide +kernel
theorem supportPart17 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart17 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart17 : ∀ i : Fin 12, (entryPart17 i.val).2≤1 := by decide +kernel

def entryPart18 : ℕ → Source × ℕ
  | 0 => (sourceRaw1863,0)
  | 1 => (sourceRaw1864,0)
  | 2 => (sourceRaw1914,0)
  | 3 => (sourceRaw1915,0)
  | 4 => (sourceRaw1929,0)
  | 5 => (sourceRaw1930,0)
  | 6 => (sourceRaw1931,0)
  | 7 => (sourceRaw1932,0)
  | 8 => (sourceRaw1935,0)
  | 9 => (sourceRaw1936,0)
  | 10 => (sourceRaw1947,0)
  | 11 => (sourceRaw1948,0)
  | _ => (sourceRaw14,0)
theorem bindingPart18 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (216+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart18 i.val).1 (-1) (entryPart18 i.val).2 := by decide +kernel
theorem supportPart18 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart18 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart18 : ∀ i : Fin 12, (entryPart18 i.val).2≤1 := by decide +kernel

def entryPart19 : ℕ → Source × ℕ
  | 0 => (sourceRaw1951,0)
  | 1 => (sourceRaw1952,0)
  | 2 => (sourceRaw1955,0)
  | 3 => (sourceRaw1956,0)
  | 4 => (sourceRaw1961,0)
  | 5 => (sourceRaw1962,0)
  | 6 => (sourceRaw2002,0)
  | 7 => (sourceRaw2003,0)
  | 8 => (sourceRaw2235,0)
  | 9 => (sourceRaw2243,0)
  | 10 => (sourceRaw2248,0)
  | 11 => (sourceRaw2259,0)
  | _ => (sourceRaw14,0)
theorem bindingPart19 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (228+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart19 i.val).1 (-1) (entryPart19 i.val).2 := by decide +kernel
theorem supportPart19 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart19 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart19 : ∀ i : Fin 12, (entryPart19 i.val).2≤1 := by decide +kernel

def entryPart20 : ℕ → Source × ℕ
  | 0 => (sourceRaw2266,0)
  | 1 => (sourceRaw2275,0)
  | 2 => (sourceRaw2277,0)
  | 3 => (sourceRaw2284,0)
  | 4 => (sourceRaw1942,0)
  | 5 => (sourceRaw2302,0)
  | 6 => (sourceRaw1941,0)
  | 7 => (sourceRaw2106,0)
  | 8 => (sourceRaw2311,0)
  | 9 => (sourceRaw2320,0)
  | 10 => (sourceRaw2324,0)
  | 11 => (sourceRaw2325,0)
  | _ => (sourceRaw14,0)
theorem bindingPart20 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (240+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart20 i.val).1 (-1) (entryPart20 i.val).2 := by decide +kernel
theorem supportPart20 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart20 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart20 : ∀ i : Fin 12, (entryPart20 i.val).2≤1 := by decide +kernel

def entryPart21 : ℕ → Source × ℕ
  | 0 => (sourceRaw2372,0)
  | 1 => (sourceRaw2374,0)
  | 2 => (sourceRaw2178,0)
  | 3 => (sourceRaw2390,0)
  | 4 => (sourceRaw2406,0)
  | 5 => (sourceRaw2414,0)
  | 6 => (sourceRaw2432,0)
  | 7 => (sourceRaw2448,0)
  | 8 => (sourceRaw2516,0)
  | 9 => (sourceRaw2532,0)
  | 10 => (sourceRaw2637,0)
  | 11 => (sourceRaw2644,0)
  | _ => (sourceRaw14,0)
theorem bindingPart21 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (252+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart21 i.val).1 (-1) (entryPart21 i.val).2 := by decide +kernel
theorem supportPart21 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart21 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart21 : ∀ i : Fin 12, (entryPart21 i.val).2≤1 := by decide +kernel

def entryPart22 : ℕ → Source × ℕ
  | 0 => (sourceRaw2649,0)
  | 1 => (sourceRaw2652,0)
  | 2 => (sourceRaw2653,0)
  | 3 => (sourceRaw2654,0)
  | 4 => (sourceRaw2656,0)
  | 5 => (sourceRaw2657,0)
  | 6 => (sourceRaw2658,0)
  | 7 => (sourceRaw2674,0)
  | 8 => (sourceRaw768,0)
  | 9 => (sourceRaw1091,0)
  | 10 => (sourceRaw2675,0)
  | 11 => (sourceRaw767,0)
  | _ => (sourceRaw14,0)
theorem bindingPart22 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (264+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart22 i.val).1 (-1) (entryPart22 i.val).2 := by decide +kernel
theorem supportPart22 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart22 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart22 : ∀ i : Fin 12, (entryPart22 i.val).2≤1 := by decide +kernel

def entryPart23 : ℕ → Source × ℕ
  | 0 => (sourceRaw980,0)
  | 1 => (sourceRaw2676,0)
  | 2 => (sourceRaw2005,0)
  | 3 => (sourceRaw2245,0)
  | 4 => (sourceRaw2678,0)
  | 5 => (sourceRaw749,0)
  | 6 => (sourceRaw683,0)
  | 7 => (sourceRaw800,0)
  | 8 => (sourceRaw751,0)
  | 9 => (sourceRaw678,0)
  | 10 => (sourceRaw989,0)
  | 11 => (sourceRaw1007,0)
  | _ => (sourceRaw14,0)
theorem bindingPart23 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (276+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart23 i.val).1 (-1) (entryPart23 i.val).2 := by decide +kernel
theorem supportPart23 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart23 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart23 : ∀ i : Fin 12, (entryPart23 i.val).2≤1 := by decide +kernel

def entryPart24 : ℕ → Source × ℕ
  | 0 => (sourceRaw1016,0)
  | 1 => (sourceRaw671,0)
  | 2 => (sourceRaw1025,0)
  | 3 => (sourceRaw795,0)
  | 4 => (sourceRaw858,0)
  | 5 => (sourceRaw1052,0)
  | 6 => (sourceRaw744,0)
  | 7 => (sourceRaw3,1)
  | 8 => (sourceRaw8,1)
  | 9 => (sourceRaw9,1)
  | 10 => (sourceRaw11,1)
  | 11 => (sourceRaw13,1)
  | _ => (sourceRaw14,0)
theorem bindingPart24 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (288+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart24 i.val).1 (-1) (entryPart24 i.val).2 := by decide +kernel
theorem supportPart24 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart24 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart24 : ∀ i : Fin 12, (entryPart24 i.val).2≤1 := by decide +kernel

def entryPart25 : ℕ → Source × ℕ
  | 0 => (sourceRaw20,1)
  | 1 => (sourceRaw22,1)
  | 2 => (sourceRaw26,1)
  | 3 => (sourceRaw28,1)
  | 4 => (sourceRaw30,1)
  | 5 => (sourceRaw38,1)
  | 6 => (sourceRaw39,1)
  | 7 => (sourceRaw40,1)
  | 8 => (sourceRaw41,1)
  | 9 => (sourceRaw42,1)
  | 10 => (sourceRaw47,1)
  | 11 => (sourceRaw69,1)
  | _ => (sourceRaw14,0)
theorem bindingPart25 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (300+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart25 i.val).1 (-1) (entryPart25 i.val).2 := by decide +kernel
theorem supportPart25 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart25 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart25 : ∀ i : Fin 12, (entryPart25 i.val).2≤1 := by decide +kernel

def entryPart26 : ℕ → Source × ℕ
  | 0 => (sourceRaw70,1)
  | 1 => (sourceRaw71,1)
  | 2 => (sourceRaw74,1)
  | 3 => (sourceRaw109,1)
  | 4 => (sourceRaw145,1)
  | 5 => (sourceRaw160,1)
  | 6 => (sourceRaw212,1)
  | 7 => (sourceRaw316,1)
  | 8 => (sourceRaw573,1)
  | 9 => (sourceRaw579,1)
  | 10 => (sourceRaw585,1)
  | 11 => (sourceRaw586,1)
  | _ => (sourceRaw14,0)
theorem bindingPart26 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (312+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart26 i.val).1 (-1) (entryPart26 i.val).2 := by decide +kernel
theorem supportPart26 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart26 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart26 : ∀ i : Fin 12, (entryPart26 i.val).2≤1 := by decide +kernel

def entryPart27 : ℕ → Source × ℕ
  | 0 => (sourceRaw593,1)
  | 1 => (sourceRaw594,1)
  | 2 => (sourceRaw595,1)
  | 3 => (sourceRaw596,1)
  | 4 => (sourceRaw599,1)
  | 5 => (sourceRaw600,1)
  | 6 => (sourceRaw695,1)
  | 7 => (sourceRaw971,1)
  | 8 => (sourceRaw696,1)
  | 9 => (sourceRaw974,1)
  | 10 => (sourceRaw685,1)
  | 11 => (sourceRaw697,1)
  | _ => (sourceRaw14,0)
theorem bindingPart27 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (324+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart27 i.val).1 (-1) (entryPart27 i.val).2 := by decide +kernel
theorem supportPart27 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart27 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart27 : ∀ i : Fin 12, (entryPart27 i.val).2≤1 := by decide +kernel

def entryPart28 : ℕ → Source × ℕ
  | 0 => (sourceRaw701,1)
  | 1 => (sourceRaw702,1)
  | 2 => (sourceRaw686,1)
  | 3 => (sourceRaw698,1)
  | 4 => (sourceRaw1004,1)
  | 5 => (sourceRaw680,1)
  | 6 => (sourceRaw1022,1)
  | 7 => (sourceRaw1326,1)
  | 8 => (sourceRaw678,1)
  | 9 => (sourceRaw683,1)
  | 10 => (sourceRaw687,1)
  | 11 => (sourceRaw688,1)
  | _ => (sourceRaw14,0)
theorem bindingPart28 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (336+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart28 i.val).1 (-1) (entryPart28 i.val).2 := by decide +kernel
theorem supportPart28 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart28 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart28 : ∀ i : Fin 12, (entryPart28 i.val).2≤1 := by decide +kernel

def entryPart29 : ℕ → Source × ℕ
  | 0 => (sourceRaw689,1)
  | 1 => (sourceRaw690,1)
  | 2 => (sourceRaw739,1)
  | 3 => (sourceRaw692,1)
  | 4 => (sourceRaw767,1)
  | 5 => (sourceRaw800,1)
  | 6 => (sourceRaw844,1)
  | 7 => (sourceRaw989,1)
  | 8 => (sourceRaw1007,1)
  | 9 => (sourceRaw1034,1)
  | 10 => (sourceRaw1863,1)
  | 11 => (sourceRaw1864,1)
  | _ => (sourceRaw14,0)
theorem bindingPart29 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (348+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart29 i.val).1 (-1) (entryPart29 i.val).2 := by decide +kernel
theorem supportPart29 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart29 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart29 : ∀ i : Fin 12, (entryPart29 i.val).2≤1 := by decide +kernel

def entryPart30 : ℕ → Source × ℕ
  | 0 => (sourceRaw1914,1)
  | 1 => (sourceRaw1915,1)
  | 2 => (sourceRaw1947,1)
  | 3 => (sourceRaw1956,1)
  | 4 => (sourceRaw2026,1)
  | 5 => (sourceRaw2675,1)
  | 6 => (sourceRaw2678,1)
  | 7 => (sourceRaw749,1)
  | 8 => (sourceRaw847,1)
  | 9 => (sourceRaw1025,1)
  | 10 => (sourceRaw693,1)
  | 11 => (sourceRaw744,1)
  | _ => (sourceRaw14,0)
theorem bindingPart30 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (360+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart30 i.val).1 (-1) (entryPart30 i.val).2 := by decide +kernel
theorem supportPart30 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart30 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart30 : ∀ i : Fin 12, (entryPart30 i.val).2≤1 := by decide +kernel

def entryPart31 : ℕ → Source × ℕ
  | 0 => (sourceRaw795,1)
  | 1 => (sourceRaw798,1)
  | 2 => (sourceRaw672,0)
  | 3 => (sourceRaw677,0)
  | 4 => (sourceRaw684,0)
  | 5 => (sourceRaw748,0)
  | 6 => (sourceRaw750,0)
  | 7 => (sourceRaw794,0)
  | 8 => (sourceRaw801,0)
  | 9 => (sourceRaw802,0)
  | 10 => (sourceRaw803,0)
  | 11 => (sourceRaw845,0)
  | _ => (sourceRaw14,0)
theorem bindingPart31 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (372+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart31 i.val).1 (-1) (entryPart31 i.val).2 := by decide +kernel
theorem supportPart31 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart31 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart31 : ∀ i : Fin 12, (entryPart31 i.val).2≤1 := by decide +kernel

def entryPart32 : ℕ → Source × ℕ
  | 0 => (sourceRaw846,0)
  | 1 => (sourceRaw976,0)
  | 2 => (sourceRaw979,0)
  | 3 => (sourceRaw982,0)
  | 4 => (sourceRaw984,0)
  | 5 => (sourceRaw987,0)
  | 6 => (sourceRaw990,0)
  | 7 => (sourceRaw992,0)
  | 8 => (sourceRaw996,0)
  | 9 => (sourceRaw1000,0)
  | 10 => (sourceRaw1001,0)
  | 11 => (sourceRaw745,0)
  | _ => (sourceRaw14,0)
theorem bindingPart32 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (384+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart32 i.val).1 (-1) (entryPart32 i.val).2 := by decide +kernel
theorem supportPart32 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart32 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart32 : ∀ i : Fin 12, (entryPart32 i.val).2≤1 := by decide +kernel

def entryPart33 : ℕ → Source × ℕ
  | 0 => (sourceRaw1010,0)
  | 1 => (sourceRaw1030,0)
  | 2 => (sourceRaw1032,0)
  | 3 => (sourceRaw1039,0)
  | 4 => (sourceRaw1041,0)
  | 5 => (sourceRaw1071,0)
  | 6 => (sourceRaw1075,0)
  | 7 => (sourceRaw1081,0)
  | 8 => (sourceRaw1084,0)
  | 9 => (sourceRaw1087,0)
  | 10 => (sourceRaw1089,0)
  | 11 => (sourceRaw1092,0)
  | _ => (sourceRaw14,0)
theorem bindingPart33 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (396+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart33 i.val).1 (-1) (entryPart33 i.val).2 := by decide +kernel
theorem supportPart33 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart33 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart33 : ∀ i : Fin 12, (entryPart33 i.val).2≤1 := by decide +kernel

def entryPart34 : ℕ → Source × ℕ
  | 0 => (sourceRaw1095,0)
  | 1 => (sourceRaw1110,0)
  | 2 => (sourceRaw1111,0)
  | 3 => (sourceRaw1114,0)
  | 4 => (sourceRaw1117,0)
  | 5 => (sourceRaw880,0)
  | 6 => (sourceRaw1119,0)
  | 7 => (sourceRaw879,0)
  | 8 => (sourceRaw1122,0)
  | 9 => (sourceRaw1125,0)
  | 10 => (sourceRaw1131,0)
  | 11 => (sourceRaw1141,0)
  | _ => (sourceRaw14,0)
theorem bindingPart34 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (408+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart34 i.val).1 (-1) (entryPart34 i.val).2 := by decide +kernel
theorem supportPart34 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart34 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart34 : ∀ i : Fin 12, (entryPart34 i.val).2≤1 := by decide +kernel

def entryPart35 : ℕ → Source × ℕ
  | 0 => (sourceRaw901,0)
  | 1 => (sourceRaw933,0)
  | 2 => (sourceRaw1144,0)
  | 3 => (sourceRaw898,0)
  | 4 => (sourceRaw1146,0)
  | 5 => (sourceRaw1150,0)
  | 6 => (sourceRaw1152,0)
  | 7 => (sourceRaw899,0)
  | 8 => (sourceRaw1155,0)
  | 9 => (sourceRaw900,0)
  | 10 => (sourceRaw1186,0)
  | 11 => (sourceRaw1933,0)
  | _ => (sourceRaw14,0)
theorem bindingPart35 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (420+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart35 i.val).1 (-1) (entryPart35 i.val).2 := by decide +kernel
theorem supportPart35 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart35 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart35 : ∀ i : Fin 12, (entryPart35 i.val).2≤1 := by decide +kernel

def entryPart36 : ℕ → Source × ℕ
  | 0 => (sourceRaw1934,0)
  | 1 => (sourceRaw1937,0)
  | 2 => (sourceRaw1938,0)
  | 3 => (sourceRaw1943,0)
  | 4 => (sourceRaw1944,0)
  | 5 => (sourceRaw2004,0)
  | 6 => (sourceRaw2061,0)
  | 7 => (sourceRaw2066,0)
  | 8 => (sourceRaw2067,0)
  | 9 => (sourceRaw2070,0)
  | 10 => (sourceRaw2071,0)
  | 11 => (sourceRaw2240,0)
  | _ => (sourceRaw14,0)
theorem bindingPart36 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (432+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart36 i.val).1 (-1) (entryPart36 i.val).2 := by decide +kernel
theorem supportPart36 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart36 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart36 : ∀ i : Fin 12, (entryPart36 i.val).2≤1 := by decide +kernel

def entryPart37 : ℕ → Source × ℕ
  | 0 => (sourceRaw2241,0)
  | 1 => (sourceRaw2242,0)
  | 2 => (sourceRaw2246,0)
  | 3 => (sourceRaw2250,0)
  | 4 => (sourceRaw2254,0)
  | 5 => (sourceRaw2256,0)
  | 6 => (sourceRaw2260,0)
  | 7 => (sourceRaw2262,0)
  | 8 => (sourceRaw2276,0)
  | 9 => (sourceRaw2278,0)
  | 10 => (sourceRaw2280,0)
  | 11 => (sourceRaw2281,0)
  | _ => (sourceRaw14,0)
theorem bindingPart37 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (444+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart37 i.val).1 (-1) (entryPart37 i.val).2 := by decide +kernel
theorem supportPart37 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart37 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart37 : ∀ i : Fin 12, (entryPart37 i.val).2≤1 := by decide +kernel

def entryPart38 : ℕ → Source × ℕ
  | 0 => (sourceRaw2290,0)
  | 1 => (sourceRaw2308,0)
  | 2 => (sourceRaw2317,0)
  | 3 => (sourceRaw2318,0)
  | 4 => (sourceRaw2322,0)
  | 5 => (sourceRaw2323,0)
  | 6 => (sourceRaw2326,0)
  | 7 => (sourceRaw2327,0)
  | 8 => (sourceRaw2331,0)
  | 9 => (sourceRaw2332,0)
  | 10 => (sourceRaw2369,0)
  | 11 => (sourceRaw2371,0)
  | _ => (sourceRaw14,0)
theorem bindingPart38 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (456+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart38 i.val).1 (-1) (entryPart38 i.val).2 := by decide +kernel
theorem supportPart38 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart38 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart38 : ∀ i : Fin 12, (entryPart38 i.val).2≤1 := by decide +kernel

def entryPart39 : ℕ → Source × ℕ
  | 0 => (sourceRaw2373,0)
  | 1 => (sourceRaw2387,0)
  | 2 => (sourceRaw2389,0)
  | 3 => (sourceRaw2393,0)
  | 4 => (sourceRaw2395,0)
  | 5 => (sourceRaw2399,0)
  | 6 => (sourceRaw2403,0)
  | 7 => (sourceRaw2404,0)
  | 8 => (sourceRaw2407,0)
  | 9 => (sourceRaw2408,0)
  | 10 => (sourceRaw2409,0)
  | 11 => (sourceRaw2424,0)
  | _ => (sourceRaw14,0)
theorem bindingPart39 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (468+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart39 i.val).1 (-1) (entryPart39 i.val).2 := by decide +kernel
theorem supportPart39 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart39 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart39 : ∀ i : Fin 12, (entryPart39 i.val).2≤1 := by decide +kernel

def entryPart40 : ℕ → Source × ℕ
  | 0 => (sourceRaw2427,0)
  | 1 => (sourceRaw2429,0)
  | 2 => (sourceRaw2435,0)
  | 3 => (sourceRaw2439,0)
  | 4 => (sourceRaw2445,0)
  | 5 => (sourceRaw2451,0)
  | 6 => (sourceRaw2471,0)
  | 7 => (sourceRaw2165,0)
  | 8 => (sourceRaw2474,0)
  | 9 => (sourceRaw2476,0)
  | 10 => (sourceRaw2160,0)
  | 11 => (sourceRaw2477,0)
  | _ => (sourceRaw14,0)
theorem bindingPart40 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (480+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart40 i.val).1 (-1) (entryPart40 i.val).2 := by decide +kernel
theorem supportPart40 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart40 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart40 : ∀ i : Fin 12, (entryPart40 i.val).2≤1 := by decide +kernel

def entryPart41 : ℕ → Source × ℕ
  | 0 => (sourceRaw2162,0)
  | 1 => (sourceRaw2478,0)
  | 2 => (sourceRaw2480,0)
  | 3 => (sourceRaw2484,0)
  | 4 => (sourceRaw2486,0)
  | 5 => (sourceRaw2487,0)
  | 6 => (sourceRaw2163,0)
  | 7 => (sourceRaw2488,0)
  | 8 => (sourceRaw2161,0)
  | 9 => (sourceRaw2493,0)
  | 10 => (sourceRaw2164,0)
  | 11 => (sourceRaw2525,0)
  | _ => (sourceRaw14,0)
theorem bindingPart41 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (492+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart41 i.val).1 (-1) (entryPart41 i.val).2 := by decide +kernel
theorem supportPart41 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart41 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart41 : ∀ i : Fin 12, (entryPart41 i.val).2≤1 := by decide +kernel

def entryPart42 : ℕ → Source × ℕ
  | 0 => (sourceRaw2537,0)
  | 1 => (sourceRaw2540,0)
  | 2 => (sourceRaw740,0)
  | 3 => (sourceRaw741,0)
  | 4 => (sourceRaw742,0)
  | 5 => (sourceRaw743,0)
  | 6 => (sourceRaw746,0)
  | 7 => (sourceRaw747,0)
  | 8 => (sourceRaw856,0)
  | 9 => (sourceRaw797,0)
  | 10 => (sourceRaw857,0)
  | 11 => (sourceRaw796,0)
  | _ => (sourceRaw14,0)
theorem bindingPart42 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (504+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart42 i.val).1 (-1) (entryPart42 i.val).2 := by decide +kernel
theorem supportPart42 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart42 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart42 : ∀ i : Fin 12, (entryPart42 i.val).2≤1 := by decide +kernel

def entryPart43 : ℕ → Source × ℕ
  | 0 => (sourceRaw981,0)
  | 1 => (sourceRaw985,0)
  | 2 => (sourceRaw991,0)
  | 3 => (sourceRaw927,0)
  | 4 => (sourceRaw999,0)
  | 5 => (sourceRaw1006,0)
  | 6 => (sourceRaw1012,0)
  | 7 => (sourceRaw1014,0)
  | 8 => (sourceRaw1020,0)
  | 9 => (sourceRaw1072,0)
  | 10 => (sourceRaw1080,0)
  | 11 => (sourceRaw1086,0)
  | _ => (sourceRaw14,0)
theorem bindingPart43 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (516+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart43 i.val).1 (-1) (entryPart43 i.val).2 := by decide +kernel
theorem supportPart43 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart43 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart43 : ∀ i : Fin 12, (entryPart43 i.val).2≤1 := by decide +kernel

def entryPart44 : ℕ → Source × ℕ
  | 0 => (sourceRaw1090,0)
  | 1 => (sourceRaw1132,0)
  | 2 => (sourceRaw1164,0)
  | 3 => (sourceRaw1201,0)
  | 4 => (sourceRaw1203,0)
  | 5 => (sourceRaw1207,0)
  | 6 => (sourceRaw1209,0)
  | 7 => (sourceRaw1212,0)
  | 8 => (sourceRaw1213,0)
  | 9 => (sourceRaw2037,0)
  | 10 => (sourceRaw2035,0)
  | 11 => (sourceRaw2032,0)
  | _ => (sourceRaw14,0)
theorem bindingPart44 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (528+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart44 i.val).1 (-1) (entryPart44 i.val).2 := by decide +kernel
theorem supportPart44 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart44 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart44 : ∀ i : Fin 12, (entryPart44 i.val).2≤1 := by decide +kernel

def entryPart45 : ℕ → Source × ℕ
  | 0 => (sourceRaw2056,0)
  | 1 => (sourceRaw2057,0)
  | 2 => (sourceRaw2060,0)
  | 3 => (sourceRaw2116,0)
  | 4 => (sourceRaw2117,0)
  | 5 => (sourceRaw2247,0)
  | 6 => (sourceRaw2249,0)
  | 7 => (sourceRaw2253,0)
  | 8 => (sourceRaw2255,0)
  | 9 => (sourceRaw2261,0)
  | 10 => (sourceRaw2263,0)
  | 11 => (sourceRaw2065,0)
  | _ => (sourceRaw14,0)
theorem bindingPart45 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (540+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart45 i.val).1 (-1) (entryPart45 i.val).2 := by decide +kernel
theorem supportPart45 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart45 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart45 : ∀ i : Fin 12, (entryPart45 i.val).2≤1 := by decide +kernel

def entryPart46 : ℕ → Source × ℕ
  | 0 => (sourceRaw2140,0)
  | 1 => (sourceRaw2064,0)
  | 2 => (sourceRaw2264,0)
  | 3 => (sourceRaw2189,0)
  | 4 => (sourceRaw2198,0)
  | 5 => (sourceRaw2058,0)
  | 6 => (sourceRaw2201,0)
  | 7 => (sourceRaw2055,0)
  | 8 => (sourceRaw2268,0)
  | 9 => (sourceRaw2270,0)
  | 10 => (sourceRaw2274,0)
  | 11 => (sourceRaw2282,0)
  | _ => (sourceRaw14,0)
theorem bindingPart46 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (552+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart46 i.val).1 (-1) (entryPart46 i.val).2 := by decide +kernel
theorem supportPart46 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart46 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart46 : ∀ i : Fin 12, (entryPart46 i.val).2≤1 := by decide +kernel

def entryPart47 : ℕ → Source × ℕ
  | 0 => (sourceRaw2283,0)
  | 1 => (sourceRaw2285,0)
  | 2 => (sourceRaw2287,0)
  | 3 => (sourceRaw2288,0)
  | 4 => (sourceRaw2289,0)
  | 5 => (sourceRaw2291,0)
  | 6 => (sourceRaw2292,0)
  | 7 => (sourceRaw2294,0)
  | 8 => (sourceRaw2295,0)
  | 9 => (sourceRaw2296,0)
  | 10 => (sourceRaw2297,0)
  | 11 => (sourceRaw2298,0)
  | _ => (sourceRaw14,0)
theorem bindingPart47 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (564+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart47 i.val).1 (-1) (entryPart47 i.val).2 := by decide +kernel
theorem supportPart47 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart47 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart47 : ∀ i : Fin 12, (entryPart47 i.val).2≤1 := by decide +kernel

def entryPart48 : ℕ → Source × ℕ
  | 0 => (sourceRaw2301,0)
  | 1 => (sourceRaw2303,0)
  | 2 => (sourceRaw2304,0)
  | 3 => (sourceRaw2305,0)
  | 4 => (sourceRaw2309,0)
  | 5 => (sourceRaw2310,0)
  | 6 => (sourceRaw2313,0)
  | 7 => (sourceRaw2316,0)
  | 8 => (sourceRaw2334,0)
  | 9 => (sourceRaw2336,0)
  | 10 => (sourceRaw2337,0)
  | 11 => (sourceRaw2339,0)
  | _ => (sourceRaw14,0)
theorem bindingPart48 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (576+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart48 i.val).1 (-1) (entryPart48 i.val).2 := by decide +kernel
theorem supportPart48 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart48 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart48 : ∀ i : Fin 12, (entryPart48 i.val).2≤1 := by decide +kernel

def entryPart49 : ℕ → Source × ℕ
  | 0 => (sourceRaw2340,0)
  | 1 => (sourceRaw2343,0)
  | 2 => (sourceRaw2188,0)
  | 3 => (sourceRaw2197,0)
  | 4 => (sourceRaw2059,0)
  | 5 => (sourceRaw2202,0)
  | 6 => (sourceRaw2054,0)
  | 7 => (sourceRaw2375,0)
  | 8 => (sourceRaw2378,0)
  | 9 => (sourceRaw2379,0)
  | 10 => (sourceRaw2381,0)
  | 11 => (sourceRaw2388,0)
  | _ => (sourceRaw14,0)
theorem bindingPart49 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (588+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart49 i.val).1 (-1) (entryPart49 i.val).2 := by decide +kernel
theorem supportPart49 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart49 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart49 : ∀ i : Fin 12, (entryPart49 i.val).2≤1 := by decide +kernel

def entryPart50 : ℕ → Source × ℕ
  | 0 => (sourceRaw2394,0)
  | 1 => (sourceRaw2397,0)
  | 2 => (sourceRaw2456,0)
  | 3 => (sourceRaw2504,0)
  | 4 => (sourceRaw2508,0)
  | 5 => (sourceRaw740,1)
  | 6 => (sourceRaw790,0)
  | 7 => (sourceRaw791,0)
  | 8 => (sourceRaw792,0)
  | 9 => (sourceRaw793,0)
  | 10 => (sourceRaw854,0)
  | 11 => (sourceRaw855,0)
  | _ => (sourceRaw14,0)
theorem bindingPart50 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (600+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart50 i.val).1 (-1) (entryPart50 i.val).2 := by decide +kernel
theorem supportPart50 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart50 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart50 : ∀ i : Fin 12, (entryPart50 i.val).2≤1 := by decide +kernel

def entryPart51 : ℕ → Source × ℕ
  | 0 => (sourceRaw926,0)
  | 1 => (sourceRaw1029,0)
  | 2 => (sourceRaw1240,0)
  | 3 => (sourceRaw2038,0)
  | 4 => (sourceRaw2052,0)
  | 5 => (sourceRaw2108,0)
  | 6 => (sourceRaw2196,0)
  | 7 => (sourceRaw2271,0)
  | 8 => (sourceRaw2053,0)
  | 9 => (sourceRaw2333,0)
  | 10 => (sourceRaw2345,0)
  | 11 => (sourceRaw2195,0)
  | _ => (sourceRaw14,0)
theorem bindingPart51 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (612+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart51 i.val).1 (-1) (entryPart51 i.val).2 := by decide +kernel
theorem supportPart51 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart51 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart51 : ∀ i : Fin 12, (entryPart51 i.val).2≤1 := by decide +kernel

def entryPart52 : ℕ → Source × ℕ
  | 0 => (sourceRaw2346,0)
  | 1 => (sourceRaw2366,0)
  | 2 => (sourceRaw2402,0)
  | 3 => (sourceRaw2583,0)
  | 4 => (sourceRaw2698,0)
  | 5 => (sourceRaw997,0)
  | 6 => (sourceRaw1009,0)
  | 7 => (sourceRaw1011,0)
  | 8 => (sourceRaw1017,0)
  | 9 => (sourceRaw2028,0)
  | 10 => (sourceRaw2030,0)
  | 11 => (sourceRaw2031,0)
  | _ => (sourceRaw14,0)
theorem bindingPart52 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (624+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart52 i.val).1 (-1) (entryPart52 i.val).2 := by decide +kernel
theorem supportPart52 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart52 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart52 : ∀ i : Fin 12, (entryPart52 i.val).2≤1 := by decide +kernel

def entryPart53 : ℕ → Source × ℕ
  | 0 => (sourceRaw2107,0)
  | 1 => (sourceRaw2136,0)
  | 2 => (sourceRaw2222,0)
  | 3 => (sourceRaw2252,0)
  | 4 => (sourceRaw2267,0)
  | 5 => (sourceRaw2029,0)
  | 6 => (sourceRaw2319,0)
  | 7 => (sourceRaw2555,0)
  | 8 => (sourceRaw2564,0)
  | 9 => (sourceRaw2027,0)
  | 10 => (sourceRaw2552,0)
  | 11 => (sourceRaw2553,0)
  | _ => (sourceRaw14,0)
theorem bindingPart53 : ∀ i : Fin 12, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (636+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart53 i.val).1 (-1) (entryPart53 i.val).2 := by decide +kernel
theorem supportPart53 : ∀ i : Fin 12, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart53 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart53 : ∀ i : Fin 12, (entryPart53 i.val).2≤1 := by decide +kernel

def entryPart54 : ℕ → Source × ℕ
  | 0 => (sourceRaw2550,0)
  | _ => (sourceRaw14,0)
theorem bindingPart54 : ∀ i : Fin 1, QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs (648+i.val)=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryPart54 i.val).1 (-1) (entryPart54 i.val).2 := by decide +kernel
theorem supportPart54 : ∀ i : Fin 1, (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryPart54 i.val).1 (-1)).all (fun t => decide (t.2.1<607))=true := by decide +kernel
theorem depthPart54 : ∀ i : Fin 1, (entryPart54 i.val).2≤1 := by decide +kernel

end QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusSourceBinding
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusSourceBindingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusSourceBinding
open QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily (Source)
open QuantitativeArithmeticSmallLevelTwentySevenZeroJet
def entryNode0_1 (n : ℕ) : Source × ℕ := entryPart0 (n-0)
theorem entryNode0_1_binding (n : ℕ) (hl : 0≤n) (hh : n<12) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_1 n).1 (-1) (entryNode0_1 n).2 := by
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
theorem entryNode1_2_binding (n : ℕ) (hl : 12≤n) (hh : n<24) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode1_2 n).1 (-1) (entryNode1_2 n).2 := by
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
theorem entryNode2_3_binding (n : ℕ) (hl : 24≤n) (hh : n<36) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode2_3 n).1 (-1) (entryNode2_3 n).2 := by
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
theorem entryNode1_3_binding (n : ℕ) (hl : 12≤n) (hh : n<36) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode1_3 n).1 (-1) (entryNode1_3 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode1_2_binding entryNode2_3_binding n hl hh
theorem entryNode1_3_support (n : ℕ) (hl : 12≤n) (hh : n<36) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode1_3 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode1_2_support entryNode2_3_support n hl hh
theorem entryNode1_3_depth (n : ℕ) (hl : 12≤n) (hh : n<36) : (entryNode1_3 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode1_2_depth entryNode2_3_depth n hl hh
def entryNode0_3 (n : ℕ) : Source × ℕ := if n<12 then entryNode0_1 n else entryNode1_3 n
theorem entryNode0_3_binding (n : ℕ) (hl : 0≤n) (hh : n<36) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_3 n).1 (-1) (entryNode0_3 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_1_binding entryNode1_3_binding n hl hh
theorem entryNode0_3_support (n : ℕ) (hl : 0≤n) (hh : n<36) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_3 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_1_support entryNode1_3_support n hl hh
theorem entryNode0_3_depth (n : ℕ) (hl : 0≤n) (hh : n<36) : (entryNode0_3 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_1_depth entryNode1_3_depth n hl hh
def entryNode3_4 (n : ℕ) : Source × ℕ := entryPart3 (n-36)
theorem entryNode3_4_binding (n : ℕ) (hl : 36≤n) (hh : n<48) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode3_4 n).1 (-1) (entryNode3_4 n).2 := by
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
theorem entryNode4_5_binding (n : ℕ) (hl : 48≤n) (hh : n<60) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode4_5 n).1 (-1) (entryNode4_5 n).2 := by
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
def entryNode5_6 (n : ℕ) : Source × ℕ := entryPart5 (n-60)
theorem entryNode5_6_binding (n : ℕ) (hl : 60≤n) (hh : n<72) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode5_6 n).1 (-1) (entryNode5_6 n).2 := by
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
def entryNode4_6 (n : ℕ) : Source × ℕ := if n<60 then entryNode4_5 n else entryNode5_6 n
theorem entryNode4_6_binding (n : ℕ) (hl : 48≤n) (hh : n<72) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode4_6 n).1 (-1) (entryNode4_6 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode4_5_binding entryNode5_6_binding n hl hh
theorem entryNode4_6_support (n : ℕ) (hl : 48≤n) (hh : n<72) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode4_6 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode4_5_support entryNode5_6_support n hl hh
theorem entryNode4_6_depth (n : ℕ) (hl : 48≤n) (hh : n<72) : (entryNode4_6 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode4_5_depth entryNode5_6_depth n hl hh
def entryNode3_6 (n : ℕ) : Source × ℕ := if n<48 then entryNode3_4 n else entryNode4_6 n
theorem entryNode3_6_binding (n : ℕ) (hl : 36≤n) (hh : n<72) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode3_6 n).1 (-1) (entryNode3_6 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode3_4_binding entryNode4_6_binding n hl hh
theorem entryNode3_6_support (n : ℕ) (hl : 36≤n) (hh : n<72) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode3_6 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode3_4_support entryNode4_6_support n hl hh
theorem entryNode3_6_depth (n : ℕ) (hl : 36≤n) (hh : n<72) : (entryNode3_6 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode3_4_depth entryNode4_6_depth n hl hh
def entryNode0_6 (n : ℕ) : Source × ℕ := if n<36 then entryNode0_3 n else entryNode3_6 n
theorem entryNode0_6_binding (n : ℕ) (hl : 0≤n) (hh : n<72) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_6 n).1 (-1) (entryNode0_6 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_3_binding entryNode3_6_binding n hl hh
theorem entryNode0_6_support (n : ℕ) (hl : 0≤n) (hh : n<72) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_6 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_3_support entryNode3_6_support n hl hh
theorem entryNode0_6_depth (n : ℕ) (hl : 0≤n) (hh : n<72) : (entryNode0_6 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_3_depth entryNode3_6_depth n hl hh
def entryNode6_7 (n : ℕ) : Source × ℕ := entryPart6 (n-72)
theorem entryNode6_7_binding (n : ℕ) (hl : 72≤n) (hh : n<84) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode6_7 n).1 (-1) (entryNode6_7 n).2 := by
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
def entryNode7_8 (n : ℕ) : Source × ℕ := entryPart7 (n-84)
theorem entryNode7_8_binding (n : ℕ) (hl : 84≤n) (hh : n<96) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode7_8 n).1 (-1) (entryNode7_8 n).2 := by
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
theorem entryNode8_9_binding (n : ℕ) (hl : 96≤n) (hh : n<108) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode8_9 n).1 (-1) (entryNode8_9 n).2 := by
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
def entryNode7_9 (n : ℕ) : Source × ℕ := if n<96 then entryNode7_8 n else entryNode8_9 n
theorem entryNode7_9_binding (n : ℕ) (hl : 84≤n) (hh : n<108) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode7_9 n).1 (-1) (entryNode7_9 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode7_8_binding entryNode8_9_binding n hl hh
theorem entryNode7_9_support (n : ℕ) (hl : 84≤n) (hh : n<108) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode7_9 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode7_8_support entryNode8_9_support n hl hh
theorem entryNode7_9_depth (n : ℕ) (hl : 84≤n) (hh : n<108) : (entryNode7_9 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode7_8_depth entryNode8_9_depth n hl hh
def entryNode6_9 (n : ℕ) : Source × ℕ := if n<84 then entryNode6_7 n else entryNode7_9 n
theorem entryNode6_9_binding (n : ℕ) (hl : 72≤n) (hh : n<108) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode6_9 n).1 (-1) (entryNode6_9 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode6_7_binding entryNode7_9_binding n hl hh
theorem entryNode6_9_support (n : ℕ) (hl : 72≤n) (hh : n<108) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode6_9 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode6_7_support entryNode7_9_support n hl hh
theorem entryNode6_9_depth (n : ℕ) (hl : 72≤n) (hh : n<108) : (entryNode6_9 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode6_7_depth entryNode7_9_depth n hl hh
def entryNode9_10 (n : ℕ) : Source × ℕ := entryPart9 (n-108)
theorem entryNode9_10_binding (n : ℕ) (hl : 108≤n) (hh : n<120) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode9_10 n).1 (-1) (entryNode9_10 n).2 := by
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
def entryNode10_11 (n : ℕ) : Source × ℕ := entryPart10 (n-120)
theorem entryNode10_11_binding (n : ℕ) (hl : 120≤n) (hh : n<132) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode10_11 n).1 (-1) (entryNode10_11 n).2 := by
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
def entryNode9_11 (n : ℕ) : Source × ℕ := if n<120 then entryNode9_10 n else entryNode10_11 n
theorem entryNode9_11_binding (n : ℕ) (hl : 108≤n) (hh : n<132) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode9_11 n).1 (-1) (entryNode9_11 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode9_10_binding entryNode10_11_binding n hl hh
theorem entryNode9_11_support (n : ℕ) (hl : 108≤n) (hh : n<132) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode9_11 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode9_10_support entryNode10_11_support n hl hh
theorem entryNode9_11_depth (n : ℕ) (hl : 108≤n) (hh : n<132) : (entryNode9_11 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode9_10_depth entryNode10_11_depth n hl hh
def entryNode11_12 (n : ℕ) : Source × ℕ := entryPart11 (n-132)
theorem entryNode11_12_binding (n : ℕ) (hl : 132≤n) (hh : n<144) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode11_12 n).1 (-1) (entryNode11_12 n).2 := by
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
def entryNode12_13 (n : ℕ) : Source × ℕ := entryPart12 (n-144)
theorem entryNode12_13_binding (n : ℕ) (hl : 144≤n) (hh : n<156) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode12_13 n).1 (-1) (entryNode12_13 n).2 := by
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
def entryNode11_13 (n : ℕ) : Source × ℕ := if n<144 then entryNode11_12 n else entryNode12_13 n
theorem entryNode11_13_binding (n : ℕ) (hl : 132≤n) (hh : n<156) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode11_13 n).1 (-1) (entryNode11_13 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode11_12_binding entryNode12_13_binding n hl hh
theorem entryNode11_13_support (n : ℕ) (hl : 132≤n) (hh : n<156) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode11_13 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode11_12_support entryNode12_13_support n hl hh
theorem entryNode11_13_depth (n : ℕ) (hl : 132≤n) (hh : n<156) : (entryNode11_13 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode11_12_depth entryNode12_13_depth n hl hh
def entryNode9_13 (n : ℕ) : Source × ℕ := if n<132 then entryNode9_11 n else entryNode11_13 n
theorem entryNode9_13_binding (n : ℕ) (hl : 108≤n) (hh : n<156) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode9_13 n).1 (-1) (entryNode9_13 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode9_11_binding entryNode11_13_binding n hl hh
theorem entryNode9_13_support (n : ℕ) (hl : 108≤n) (hh : n<156) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode9_13 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode9_11_support entryNode11_13_support n hl hh
theorem entryNode9_13_depth (n : ℕ) (hl : 108≤n) (hh : n<156) : (entryNode9_13 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode9_11_depth entryNode11_13_depth n hl hh
def entryNode6_13 (n : ℕ) : Source × ℕ := if n<108 then entryNode6_9 n else entryNode9_13 n
theorem entryNode6_13_binding (n : ℕ) (hl : 72≤n) (hh : n<156) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode6_13 n).1 (-1) (entryNode6_13 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode6_9_binding entryNode9_13_binding n hl hh
theorem entryNode6_13_support (n : ℕ) (hl : 72≤n) (hh : n<156) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode6_13 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode6_9_support entryNode9_13_support n hl hh
theorem entryNode6_13_depth (n : ℕ) (hl : 72≤n) (hh : n<156) : (entryNode6_13 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode6_9_depth entryNode9_13_depth n hl hh
def entryNode0_13 (n : ℕ) : Source × ℕ := if n<72 then entryNode0_6 n else entryNode6_13 n
theorem entryNode0_13_binding (n : ℕ) (hl : 0≤n) (hh : n<156) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_13 n).1 (-1) (entryNode0_13 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_6_binding entryNode6_13_binding n hl hh
theorem entryNode0_13_support (n : ℕ) (hl : 0≤n) (hh : n<156) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_13 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_6_support entryNode6_13_support n hl hh
theorem entryNode0_13_depth (n : ℕ) (hl : 0≤n) (hh : n<156) : (entryNode0_13 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_6_depth entryNode6_13_depth n hl hh
def entryNode13_14 (n : ℕ) : Source × ℕ := entryPart13 (n-156)
theorem entryNode13_14_binding (n : ℕ) (hl : 156≤n) (hh : n<168) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode13_14 n).1 (-1) (entryNode13_14 n).2 := by
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
def entryNode14_15 (n : ℕ) : Source × ℕ := entryPart14 (n-168)
theorem entryNode14_15_binding (n : ℕ) (hl : 168≤n) (hh : n<180) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode14_15 n).1 (-1) (entryNode14_15 n).2 := by
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
theorem entryNode15_16_binding (n : ℕ) (hl : 180≤n) (hh : n<192) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode15_16 n).1 (-1) (entryNode15_16 n).2 := by
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
def entryNode14_16 (n : ℕ) : Source × ℕ := if n<180 then entryNode14_15 n else entryNode15_16 n
theorem entryNode14_16_binding (n : ℕ) (hl : 168≤n) (hh : n<192) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode14_16 n).1 (-1) (entryNode14_16 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode14_15_binding entryNode15_16_binding n hl hh
theorem entryNode14_16_support (n : ℕ) (hl : 168≤n) (hh : n<192) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode14_16 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode14_15_support entryNode15_16_support n hl hh
theorem entryNode14_16_depth (n : ℕ) (hl : 168≤n) (hh : n<192) : (entryNode14_16 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode14_15_depth entryNode15_16_depth n hl hh
def entryNode13_16 (n : ℕ) : Source × ℕ := if n<168 then entryNode13_14 n else entryNode14_16 n
theorem entryNode13_16_binding (n : ℕ) (hl : 156≤n) (hh : n<192) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode13_16 n).1 (-1) (entryNode13_16 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode13_14_binding entryNode14_16_binding n hl hh
theorem entryNode13_16_support (n : ℕ) (hl : 156≤n) (hh : n<192) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode13_16 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode13_14_support entryNode14_16_support n hl hh
theorem entryNode13_16_depth (n : ℕ) (hl : 156≤n) (hh : n<192) : (entryNode13_16 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode13_14_depth entryNode14_16_depth n hl hh
def entryNode16_17 (n : ℕ) : Source × ℕ := entryPart16 (n-192)
theorem entryNode16_17_binding (n : ℕ) (hl : 192≤n) (hh : n<204) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode16_17 n).1 (-1) (entryNode16_17 n).2 := by
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
def entryNode17_18 (n : ℕ) : Source × ℕ := entryPart17 (n-204)
theorem entryNode17_18_binding (n : ℕ) (hl : 204≤n) (hh : n<216) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode17_18 n).1 (-1) (entryNode17_18 n).2 := by
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
def entryNode16_18 (n : ℕ) : Source × ℕ := if n<204 then entryNode16_17 n else entryNode17_18 n
theorem entryNode16_18_binding (n : ℕ) (hl : 192≤n) (hh : n<216) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode16_18 n).1 (-1) (entryNode16_18 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode16_17_binding entryNode17_18_binding n hl hh
theorem entryNode16_18_support (n : ℕ) (hl : 192≤n) (hh : n<216) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode16_18 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode16_17_support entryNode17_18_support n hl hh
theorem entryNode16_18_depth (n : ℕ) (hl : 192≤n) (hh : n<216) : (entryNode16_18 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode16_17_depth entryNode17_18_depth n hl hh
def entryNode18_19 (n : ℕ) : Source × ℕ := entryPart18 (n-216)
theorem entryNode18_19_binding (n : ℕ) (hl : 216≤n) (hh : n<228) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode18_19 n).1 (-1) (entryNode18_19 n).2 := by
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
def entryNode19_20 (n : ℕ) : Source × ℕ := entryPart19 (n-228)
theorem entryNode19_20_binding (n : ℕ) (hl : 228≤n) (hh : n<240) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode19_20 n).1 (-1) (entryNode19_20 n).2 := by
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
def entryNode18_20 (n : ℕ) : Source × ℕ := if n<228 then entryNode18_19 n else entryNode19_20 n
theorem entryNode18_20_binding (n : ℕ) (hl : 216≤n) (hh : n<240) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode18_20 n).1 (-1) (entryNode18_20 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode18_19_binding entryNode19_20_binding n hl hh
theorem entryNode18_20_support (n : ℕ) (hl : 216≤n) (hh : n<240) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode18_20 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode18_19_support entryNode19_20_support n hl hh
theorem entryNode18_20_depth (n : ℕ) (hl : 216≤n) (hh : n<240) : (entryNode18_20 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode18_19_depth entryNode19_20_depth n hl hh
def entryNode16_20 (n : ℕ) : Source × ℕ := if n<216 then entryNode16_18 n else entryNode18_20 n
theorem entryNode16_20_binding (n : ℕ) (hl : 192≤n) (hh : n<240) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode16_20 n).1 (-1) (entryNode16_20 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode16_18_binding entryNode18_20_binding n hl hh
theorem entryNode16_20_support (n : ℕ) (hl : 192≤n) (hh : n<240) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode16_20 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode16_18_support entryNode18_20_support n hl hh
theorem entryNode16_20_depth (n : ℕ) (hl : 192≤n) (hh : n<240) : (entryNode16_20 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode16_18_depth entryNode18_20_depth n hl hh
def entryNode13_20 (n : ℕ) : Source × ℕ := if n<192 then entryNode13_16 n else entryNode16_20 n
theorem entryNode13_20_binding (n : ℕ) (hl : 156≤n) (hh : n<240) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode13_20 n).1 (-1) (entryNode13_20 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode13_16_binding entryNode16_20_binding n hl hh
theorem entryNode13_20_support (n : ℕ) (hl : 156≤n) (hh : n<240) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode13_20 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode13_16_support entryNode16_20_support n hl hh
theorem entryNode13_20_depth (n : ℕ) (hl : 156≤n) (hh : n<240) : (entryNode13_20 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode13_16_depth entryNode16_20_depth n hl hh
def entryNode20_21 (n : ℕ) : Source × ℕ := entryPart20 (n-240)
theorem entryNode20_21_binding (n : ℕ) (hl : 240≤n) (hh : n<252) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode20_21 n).1 (-1) (entryNode20_21 n).2 := by
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
def entryNode21_22 (n : ℕ) : Source × ℕ := entryPart21 (n-252)
theorem entryNode21_22_binding (n : ℕ) (hl : 252≤n) (hh : n<264) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode21_22 n).1 (-1) (entryNode21_22 n).2 := by
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
theorem entryNode22_23_binding (n : ℕ) (hl : 264≤n) (hh : n<276) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode22_23 n).1 (-1) (entryNode22_23 n).2 := by
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
def entryNode21_23 (n : ℕ) : Source × ℕ := if n<264 then entryNode21_22 n else entryNode22_23 n
theorem entryNode21_23_binding (n : ℕ) (hl : 252≤n) (hh : n<276) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode21_23 n).1 (-1) (entryNode21_23 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode21_22_binding entryNode22_23_binding n hl hh
theorem entryNode21_23_support (n : ℕ) (hl : 252≤n) (hh : n<276) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode21_23 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode21_22_support entryNode22_23_support n hl hh
theorem entryNode21_23_depth (n : ℕ) (hl : 252≤n) (hh : n<276) : (entryNode21_23 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode21_22_depth entryNode22_23_depth n hl hh
def entryNode20_23 (n : ℕ) : Source × ℕ := if n<252 then entryNode20_21 n else entryNode21_23 n
theorem entryNode20_23_binding (n : ℕ) (hl : 240≤n) (hh : n<276) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode20_23 n).1 (-1) (entryNode20_23 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode20_21_binding entryNode21_23_binding n hl hh
theorem entryNode20_23_support (n : ℕ) (hl : 240≤n) (hh : n<276) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode20_23 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode20_21_support entryNode21_23_support n hl hh
theorem entryNode20_23_depth (n : ℕ) (hl : 240≤n) (hh : n<276) : (entryNode20_23 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode20_21_depth entryNode21_23_depth n hl hh
def entryNode23_24 (n : ℕ) : Source × ℕ := entryPart23 (n-276)
theorem entryNode23_24_binding (n : ℕ) (hl : 276≤n) (hh : n<288) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode23_24 n).1 (-1) (entryNode23_24 n).2 := by
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
def entryNode24_25 (n : ℕ) : Source × ℕ := entryPart24 (n-288)
theorem entryNode24_25_binding (n : ℕ) (hl : 288≤n) (hh : n<300) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode24_25 n).1 (-1) (entryNode24_25 n).2 := by
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
def entryNode23_25 (n : ℕ) : Source × ℕ := if n<288 then entryNode23_24 n else entryNode24_25 n
theorem entryNode23_25_binding (n : ℕ) (hl : 276≤n) (hh : n<300) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode23_25 n).1 (-1) (entryNode23_25 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode23_24_binding entryNode24_25_binding n hl hh
theorem entryNode23_25_support (n : ℕ) (hl : 276≤n) (hh : n<300) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode23_25 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode23_24_support entryNode24_25_support n hl hh
theorem entryNode23_25_depth (n : ℕ) (hl : 276≤n) (hh : n<300) : (entryNode23_25 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode23_24_depth entryNode24_25_depth n hl hh
def entryNode25_26 (n : ℕ) : Source × ℕ := entryPart25 (n-300)
theorem entryNode25_26_binding (n : ℕ) (hl : 300≤n) (hh : n<312) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode25_26 n).1 (-1) (entryNode25_26 n).2 := by
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
def entryNode26_27 (n : ℕ) : Source × ℕ := entryPart26 (n-312)
theorem entryNode26_27_binding (n : ℕ) (hl : 312≤n) (hh : n<324) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode26_27 n).1 (-1) (entryNode26_27 n).2 := by
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
def entryNode25_27 (n : ℕ) : Source × ℕ := if n<312 then entryNode25_26 n else entryNode26_27 n
theorem entryNode25_27_binding (n : ℕ) (hl : 300≤n) (hh : n<324) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode25_27 n).1 (-1) (entryNode25_27 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode25_26_binding entryNode26_27_binding n hl hh
theorem entryNode25_27_support (n : ℕ) (hl : 300≤n) (hh : n<324) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode25_27 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode25_26_support entryNode26_27_support n hl hh
theorem entryNode25_27_depth (n : ℕ) (hl : 300≤n) (hh : n<324) : (entryNode25_27 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode25_26_depth entryNode26_27_depth n hl hh
def entryNode23_27 (n : ℕ) : Source × ℕ := if n<300 then entryNode23_25 n else entryNode25_27 n
theorem entryNode23_27_binding (n : ℕ) (hl : 276≤n) (hh : n<324) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode23_27 n).1 (-1) (entryNode23_27 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode23_25_binding entryNode25_27_binding n hl hh
theorem entryNode23_27_support (n : ℕ) (hl : 276≤n) (hh : n<324) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode23_27 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode23_25_support entryNode25_27_support n hl hh
theorem entryNode23_27_depth (n : ℕ) (hl : 276≤n) (hh : n<324) : (entryNode23_27 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode23_25_depth entryNode25_27_depth n hl hh
def entryNode20_27 (n : ℕ) : Source × ℕ := if n<276 then entryNode20_23 n else entryNode23_27 n
theorem entryNode20_27_binding (n : ℕ) (hl : 240≤n) (hh : n<324) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode20_27 n).1 (-1) (entryNode20_27 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode20_23_binding entryNode23_27_binding n hl hh
theorem entryNode20_27_support (n : ℕ) (hl : 240≤n) (hh : n<324) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode20_27 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode20_23_support entryNode23_27_support n hl hh
theorem entryNode20_27_depth (n : ℕ) (hl : 240≤n) (hh : n<324) : (entryNode20_27 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode20_23_depth entryNode23_27_depth n hl hh
def entryNode13_27 (n : ℕ) : Source × ℕ := if n<240 then entryNode13_20 n else entryNode20_27 n
theorem entryNode13_27_binding (n : ℕ) (hl : 156≤n) (hh : n<324) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode13_27 n).1 (-1) (entryNode13_27 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode13_20_binding entryNode20_27_binding n hl hh
theorem entryNode13_27_support (n : ℕ) (hl : 156≤n) (hh : n<324) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode13_27 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode13_20_support entryNode20_27_support n hl hh
theorem entryNode13_27_depth (n : ℕ) (hl : 156≤n) (hh : n<324) : (entryNode13_27 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode13_20_depth entryNode20_27_depth n hl hh
def entryNode0_27 (n : ℕ) : Source × ℕ := if n<156 then entryNode0_13 n else entryNode13_27 n
theorem entryNode0_27_binding (n : ℕ) (hl : 0≤n) (hh : n<324) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_27 n).1 (-1) (entryNode0_27 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_13_binding entryNode13_27_binding n hl hh
theorem entryNode0_27_support (n : ℕ) (hl : 0≤n) (hh : n<324) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_27 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_13_support entryNode13_27_support n hl hh
theorem entryNode0_27_depth (n : ℕ) (hl : 0≤n) (hh : n<324) : (entryNode0_27 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_13_depth entryNode13_27_depth n hl hh
def entryNode27_28 (n : ℕ) : Source × ℕ := entryPart27 (n-324)
theorem entryNode27_28_binding (n : ℕ) (hl : 324≤n) (hh : n<336) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode27_28 n).1 (-1) (entryNode27_28 n).2 := by
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
def entryNode28_29 (n : ℕ) : Source × ℕ := entryPart28 (n-336)
theorem entryNode28_29_binding (n : ℕ) (hl : 336≤n) (hh : n<348) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode28_29 n).1 (-1) (entryNode28_29 n).2 := by
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
theorem entryNode29_30_binding (n : ℕ) (hl : 348≤n) (hh : n<360) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode29_30 n).1 (-1) (entryNode29_30 n).2 := by
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
def entryNode28_30 (n : ℕ) : Source × ℕ := if n<348 then entryNode28_29 n else entryNode29_30 n
theorem entryNode28_30_binding (n : ℕ) (hl : 336≤n) (hh : n<360) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode28_30 n).1 (-1) (entryNode28_30 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode28_29_binding entryNode29_30_binding n hl hh
theorem entryNode28_30_support (n : ℕ) (hl : 336≤n) (hh : n<360) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode28_30 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode28_29_support entryNode29_30_support n hl hh
theorem entryNode28_30_depth (n : ℕ) (hl : 336≤n) (hh : n<360) : (entryNode28_30 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode28_29_depth entryNode29_30_depth n hl hh
def entryNode27_30 (n : ℕ) : Source × ℕ := if n<336 then entryNode27_28 n else entryNode28_30 n
theorem entryNode27_30_binding (n : ℕ) (hl : 324≤n) (hh : n<360) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode27_30 n).1 (-1) (entryNode27_30 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode27_28_binding entryNode28_30_binding n hl hh
theorem entryNode27_30_support (n : ℕ) (hl : 324≤n) (hh : n<360) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode27_30 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode27_28_support entryNode28_30_support n hl hh
theorem entryNode27_30_depth (n : ℕ) (hl : 324≤n) (hh : n<360) : (entryNode27_30 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode27_28_depth entryNode28_30_depth n hl hh
def entryNode30_31 (n : ℕ) : Source × ℕ := entryPart30 (n-360)
theorem entryNode30_31_binding (n : ℕ) (hl : 360≤n) (hh : n<372) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode30_31 n).1 (-1) (entryNode30_31 n).2 := by
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
def entryNode31_32 (n : ℕ) : Source × ℕ := entryPart31 (n-372)
theorem entryNode31_32_binding (n : ℕ) (hl : 372≤n) (hh : n<384) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode31_32 n).1 (-1) (entryNode31_32 n).2 := by
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
def entryNode30_32 (n : ℕ) : Source × ℕ := if n<372 then entryNode30_31 n else entryNode31_32 n
theorem entryNode30_32_binding (n : ℕ) (hl : 360≤n) (hh : n<384) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode30_32 n).1 (-1) (entryNode30_32 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode30_31_binding entryNode31_32_binding n hl hh
theorem entryNode30_32_support (n : ℕ) (hl : 360≤n) (hh : n<384) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode30_32 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode30_31_support entryNode31_32_support n hl hh
theorem entryNode30_32_depth (n : ℕ) (hl : 360≤n) (hh : n<384) : (entryNode30_32 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode30_31_depth entryNode31_32_depth n hl hh
def entryNode32_33 (n : ℕ) : Source × ℕ := entryPart32 (n-384)
theorem entryNode32_33_binding (n : ℕ) (hl : 384≤n) (hh : n<396) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode32_33 n).1 (-1) (entryNode32_33 n).2 := by
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
def entryNode33_34 (n : ℕ) : Source × ℕ := entryPart33 (n-396)
theorem entryNode33_34_binding (n : ℕ) (hl : 396≤n) (hh : n<408) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode33_34 n).1 (-1) (entryNode33_34 n).2 := by
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
def entryNode32_34 (n : ℕ) : Source × ℕ := if n<396 then entryNode32_33 n else entryNode33_34 n
theorem entryNode32_34_binding (n : ℕ) (hl : 384≤n) (hh : n<408) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode32_34 n).1 (-1) (entryNode32_34 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode32_33_binding entryNode33_34_binding n hl hh
theorem entryNode32_34_support (n : ℕ) (hl : 384≤n) (hh : n<408) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode32_34 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode32_33_support entryNode33_34_support n hl hh
theorem entryNode32_34_depth (n : ℕ) (hl : 384≤n) (hh : n<408) : (entryNode32_34 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode32_33_depth entryNode33_34_depth n hl hh
def entryNode30_34 (n : ℕ) : Source × ℕ := if n<384 then entryNode30_32 n else entryNode32_34 n
theorem entryNode30_34_binding (n : ℕ) (hl : 360≤n) (hh : n<408) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode30_34 n).1 (-1) (entryNode30_34 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode30_32_binding entryNode32_34_binding n hl hh
theorem entryNode30_34_support (n : ℕ) (hl : 360≤n) (hh : n<408) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode30_34 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode30_32_support entryNode32_34_support n hl hh
theorem entryNode30_34_depth (n : ℕ) (hl : 360≤n) (hh : n<408) : (entryNode30_34 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode30_32_depth entryNode32_34_depth n hl hh
def entryNode27_34 (n : ℕ) : Source × ℕ := if n<360 then entryNode27_30 n else entryNode30_34 n
theorem entryNode27_34_binding (n : ℕ) (hl : 324≤n) (hh : n<408) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode27_34 n).1 (-1) (entryNode27_34 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode27_30_binding entryNode30_34_binding n hl hh
theorem entryNode27_34_support (n : ℕ) (hl : 324≤n) (hh : n<408) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode27_34 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode27_30_support entryNode30_34_support n hl hh
theorem entryNode27_34_depth (n : ℕ) (hl : 324≤n) (hh : n<408) : (entryNode27_34 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode27_30_depth entryNode30_34_depth n hl hh
def entryNode34_35 (n : ℕ) : Source × ℕ := entryPart34 (n-408)
theorem entryNode34_35_binding (n : ℕ) (hl : 408≤n) (hh : n<420) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode34_35 n).1 (-1) (entryNode34_35 n).2 := by
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
def entryNode35_36 (n : ℕ) : Source × ℕ := entryPart35 (n-420)
theorem entryNode35_36_binding (n : ℕ) (hl : 420≤n) (hh : n<432) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode35_36 n).1 (-1) (entryNode35_36 n).2 := by
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
theorem entryNode36_37_binding (n : ℕ) (hl : 432≤n) (hh : n<444) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode36_37 n).1 (-1) (entryNode36_37 n).2 := by
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
def entryNode35_37 (n : ℕ) : Source × ℕ := if n<432 then entryNode35_36 n else entryNode36_37 n
theorem entryNode35_37_binding (n : ℕ) (hl : 420≤n) (hh : n<444) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode35_37 n).1 (-1) (entryNode35_37 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode35_36_binding entryNode36_37_binding n hl hh
theorem entryNode35_37_support (n : ℕ) (hl : 420≤n) (hh : n<444) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode35_37 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode35_36_support entryNode36_37_support n hl hh
theorem entryNode35_37_depth (n : ℕ) (hl : 420≤n) (hh : n<444) : (entryNode35_37 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode35_36_depth entryNode36_37_depth n hl hh
def entryNode34_37 (n : ℕ) : Source × ℕ := if n<420 then entryNode34_35 n else entryNode35_37 n
theorem entryNode34_37_binding (n : ℕ) (hl : 408≤n) (hh : n<444) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode34_37 n).1 (-1) (entryNode34_37 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode34_35_binding entryNode35_37_binding n hl hh
theorem entryNode34_37_support (n : ℕ) (hl : 408≤n) (hh : n<444) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode34_37 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode34_35_support entryNode35_37_support n hl hh
theorem entryNode34_37_depth (n : ℕ) (hl : 408≤n) (hh : n<444) : (entryNode34_37 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode34_35_depth entryNode35_37_depth n hl hh
def entryNode37_38 (n : ℕ) : Source × ℕ := entryPart37 (n-444)
theorem entryNode37_38_binding (n : ℕ) (hl : 444≤n) (hh : n<456) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode37_38 n).1 (-1) (entryNode37_38 n).2 := by
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
def entryNode38_39 (n : ℕ) : Source × ℕ := entryPart38 (n-456)
theorem entryNode38_39_binding (n : ℕ) (hl : 456≤n) (hh : n<468) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode38_39 n).1 (-1) (entryNode38_39 n).2 := by
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
def entryNode37_39 (n : ℕ) : Source × ℕ := if n<456 then entryNode37_38 n else entryNode38_39 n
theorem entryNode37_39_binding (n : ℕ) (hl : 444≤n) (hh : n<468) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode37_39 n).1 (-1) (entryNode37_39 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode37_38_binding entryNode38_39_binding n hl hh
theorem entryNode37_39_support (n : ℕ) (hl : 444≤n) (hh : n<468) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode37_39 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode37_38_support entryNode38_39_support n hl hh
theorem entryNode37_39_depth (n : ℕ) (hl : 444≤n) (hh : n<468) : (entryNode37_39 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode37_38_depth entryNode38_39_depth n hl hh
def entryNode39_40 (n : ℕ) : Source × ℕ := entryPart39 (n-468)
theorem entryNode39_40_binding (n : ℕ) (hl : 468≤n) (hh : n<480) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode39_40 n).1 (-1) (entryNode39_40 n).2 := by
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
def entryNode40_41 (n : ℕ) : Source × ℕ := entryPart40 (n-480)
theorem entryNode40_41_binding (n : ℕ) (hl : 480≤n) (hh : n<492) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode40_41 n).1 (-1) (entryNode40_41 n).2 := by
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
def entryNode39_41 (n : ℕ) : Source × ℕ := if n<480 then entryNode39_40 n else entryNode40_41 n
theorem entryNode39_41_binding (n : ℕ) (hl : 468≤n) (hh : n<492) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode39_41 n).1 (-1) (entryNode39_41 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode39_40_binding entryNode40_41_binding n hl hh
theorem entryNode39_41_support (n : ℕ) (hl : 468≤n) (hh : n<492) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode39_41 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode39_40_support entryNode40_41_support n hl hh
theorem entryNode39_41_depth (n : ℕ) (hl : 468≤n) (hh : n<492) : (entryNode39_41 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode39_40_depth entryNode40_41_depth n hl hh
def entryNode37_41 (n : ℕ) : Source × ℕ := if n<468 then entryNode37_39 n else entryNode39_41 n
theorem entryNode37_41_binding (n : ℕ) (hl : 444≤n) (hh : n<492) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode37_41 n).1 (-1) (entryNode37_41 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode37_39_binding entryNode39_41_binding n hl hh
theorem entryNode37_41_support (n : ℕ) (hl : 444≤n) (hh : n<492) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode37_41 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode37_39_support entryNode39_41_support n hl hh
theorem entryNode37_41_depth (n : ℕ) (hl : 444≤n) (hh : n<492) : (entryNode37_41 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode37_39_depth entryNode39_41_depth n hl hh
def entryNode34_41 (n : ℕ) : Source × ℕ := if n<444 then entryNode34_37 n else entryNode37_41 n
theorem entryNode34_41_binding (n : ℕ) (hl : 408≤n) (hh : n<492) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode34_41 n).1 (-1) (entryNode34_41 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode34_37_binding entryNode37_41_binding n hl hh
theorem entryNode34_41_support (n : ℕ) (hl : 408≤n) (hh : n<492) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode34_41 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode34_37_support entryNode37_41_support n hl hh
theorem entryNode34_41_depth (n : ℕ) (hl : 408≤n) (hh : n<492) : (entryNode34_41 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode34_37_depth entryNode37_41_depth n hl hh
def entryNode27_41 (n : ℕ) : Source × ℕ := if n<408 then entryNode27_34 n else entryNode34_41 n
theorem entryNode27_41_binding (n : ℕ) (hl : 324≤n) (hh : n<492) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode27_41 n).1 (-1) (entryNode27_41 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode27_34_binding entryNode34_41_binding n hl hh
theorem entryNode27_41_support (n : ℕ) (hl : 324≤n) (hh : n<492) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode27_41 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode27_34_support entryNode34_41_support n hl hh
theorem entryNode27_41_depth (n : ℕ) (hl : 324≤n) (hh : n<492) : (entryNode27_41 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode27_34_depth entryNode34_41_depth n hl hh
def entryNode41_42 (n : ℕ) : Source × ℕ := entryPart41 (n-492)
theorem entryNode41_42_binding (n : ℕ) (hl : 492≤n) (hh : n<504) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode41_42 n).1 (-1) (entryNode41_42 n).2 := by
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
def entryNode42_43 (n : ℕ) : Source × ℕ := entryPart42 (n-504)
theorem entryNode42_43_binding (n : ℕ) (hl : 504≤n) (hh : n<516) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode42_43 n).1 (-1) (entryNode42_43 n).2 := by
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
theorem entryNode43_44_binding (n : ℕ) (hl : 516≤n) (hh : n<528) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode43_44 n).1 (-1) (entryNode43_44 n).2 := by
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
def entryNode42_44 (n : ℕ) : Source × ℕ := if n<516 then entryNode42_43 n else entryNode43_44 n
theorem entryNode42_44_binding (n : ℕ) (hl : 504≤n) (hh : n<528) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode42_44 n).1 (-1) (entryNode42_44 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode42_43_binding entryNode43_44_binding n hl hh
theorem entryNode42_44_support (n : ℕ) (hl : 504≤n) (hh : n<528) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode42_44 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode42_43_support entryNode43_44_support n hl hh
theorem entryNode42_44_depth (n : ℕ) (hl : 504≤n) (hh : n<528) : (entryNode42_44 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode42_43_depth entryNode43_44_depth n hl hh
def entryNode41_44 (n : ℕ) : Source × ℕ := if n<504 then entryNode41_42 n else entryNode42_44 n
theorem entryNode41_44_binding (n : ℕ) (hl : 492≤n) (hh : n<528) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode41_44 n).1 (-1) (entryNode41_44 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode41_42_binding entryNode42_44_binding n hl hh
theorem entryNode41_44_support (n : ℕ) (hl : 492≤n) (hh : n<528) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode41_44 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode41_42_support entryNode42_44_support n hl hh
theorem entryNode41_44_depth (n : ℕ) (hl : 492≤n) (hh : n<528) : (entryNode41_44 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode41_42_depth entryNode42_44_depth n hl hh
def entryNode44_45 (n : ℕ) : Source × ℕ := entryPart44 (n-528)
theorem entryNode44_45_binding (n : ℕ) (hl : 528≤n) (hh : n<540) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode44_45 n).1 (-1) (entryNode44_45 n).2 := by
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
def entryNode45_46 (n : ℕ) : Source × ℕ := entryPart45 (n-540)
theorem entryNode45_46_binding (n : ℕ) (hl : 540≤n) (hh : n<552) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode45_46 n).1 (-1) (entryNode45_46 n).2 := by
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
def entryNode44_46 (n : ℕ) : Source × ℕ := if n<540 then entryNode44_45 n else entryNode45_46 n
theorem entryNode44_46_binding (n : ℕ) (hl : 528≤n) (hh : n<552) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode44_46 n).1 (-1) (entryNode44_46 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode44_45_binding entryNode45_46_binding n hl hh
theorem entryNode44_46_support (n : ℕ) (hl : 528≤n) (hh : n<552) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode44_46 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode44_45_support entryNode45_46_support n hl hh
theorem entryNode44_46_depth (n : ℕ) (hl : 528≤n) (hh : n<552) : (entryNode44_46 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode44_45_depth entryNode45_46_depth n hl hh
def entryNode46_47 (n : ℕ) : Source × ℕ := entryPart46 (n-552)
theorem entryNode46_47_binding (n : ℕ) (hl : 552≤n) (hh : n<564) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode46_47 n).1 (-1) (entryNode46_47 n).2 := by
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
def entryNode47_48 (n : ℕ) : Source × ℕ := entryPart47 (n-564)
theorem entryNode47_48_binding (n : ℕ) (hl : 564≤n) (hh : n<576) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode47_48 n).1 (-1) (entryNode47_48 n).2 := by
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
def entryNode46_48 (n : ℕ) : Source × ℕ := if n<564 then entryNode46_47 n else entryNode47_48 n
theorem entryNode46_48_binding (n : ℕ) (hl : 552≤n) (hh : n<576) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode46_48 n).1 (-1) (entryNode46_48 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode46_47_binding entryNode47_48_binding n hl hh
theorem entryNode46_48_support (n : ℕ) (hl : 552≤n) (hh : n<576) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode46_48 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode46_47_support entryNode47_48_support n hl hh
theorem entryNode46_48_depth (n : ℕ) (hl : 552≤n) (hh : n<576) : (entryNode46_48 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode46_47_depth entryNode47_48_depth n hl hh
def entryNode44_48 (n : ℕ) : Source × ℕ := if n<552 then entryNode44_46 n else entryNode46_48 n
theorem entryNode44_48_binding (n : ℕ) (hl : 528≤n) (hh : n<576) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode44_48 n).1 (-1) (entryNode44_48 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode44_46_binding entryNode46_48_binding n hl hh
theorem entryNode44_48_support (n : ℕ) (hl : 528≤n) (hh : n<576) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode44_48 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode44_46_support entryNode46_48_support n hl hh
theorem entryNode44_48_depth (n : ℕ) (hl : 528≤n) (hh : n<576) : (entryNode44_48 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode44_46_depth entryNode46_48_depth n hl hh
def entryNode41_48 (n : ℕ) : Source × ℕ := if n<528 then entryNode41_44 n else entryNode44_48 n
theorem entryNode41_48_binding (n : ℕ) (hl : 492≤n) (hh : n<576) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode41_48 n).1 (-1) (entryNode41_48 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode41_44_binding entryNode44_48_binding n hl hh
theorem entryNode41_48_support (n : ℕ) (hl : 492≤n) (hh : n<576) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode41_48 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode41_44_support entryNode44_48_support n hl hh
theorem entryNode41_48_depth (n : ℕ) (hl : 492≤n) (hh : n<576) : (entryNode41_48 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode41_44_depth entryNode44_48_depth n hl hh
def entryNode48_49 (n : ℕ) : Source × ℕ := entryPart48 (n-576)
theorem entryNode48_49_binding (n : ℕ) (hl : 576≤n) (hh : n<588) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode48_49 n).1 (-1) (entryNode48_49 n).2 := by
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
def entryNode49_50 (n : ℕ) : Source × ℕ := entryPart49 (n-588)
theorem entryNode49_50_binding (n : ℕ) (hl : 588≤n) (hh : n<600) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode49_50 n).1 (-1) (entryNode49_50 n).2 := by
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
theorem entryNode50_51_binding (n : ℕ) (hl : 600≤n) (hh : n<612) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode50_51 n).1 (-1) (entryNode50_51 n).2 := by
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
def entryNode49_51 (n : ℕ) : Source × ℕ := if n<600 then entryNode49_50 n else entryNode50_51 n
theorem entryNode49_51_binding (n : ℕ) (hl : 588≤n) (hh : n<612) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode49_51 n).1 (-1) (entryNode49_51 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode49_50_binding entryNode50_51_binding n hl hh
theorem entryNode49_51_support (n : ℕ) (hl : 588≤n) (hh : n<612) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode49_51 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode49_50_support entryNode50_51_support n hl hh
theorem entryNode49_51_depth (n : ℕ) (hl : 588≤n) (hh : n<612) : (entryNode49_51 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode49_50_depth entryNode50_51_depth n hl hh
def entryNode48_51 (n : ℕ) : Source × ℕ := if n<588 then entryNode48_49 n else entryNode49_51 n
theorem entryNode48_51_binding (n : ℕ) (hl : 576≤n) (hh : n<612) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode48_51 n).1 (-1) (entryNode48_51 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode48_49_binding entryNode49_51_binding n hl hh
theorem entryNode48_51_support (n : ℕ) (hl : 576≤n) (hh : n<612) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode48_51 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode48_49_support entryNode49_51_support n hl hh
theorem entryNode48_51_depth (n : ℕ) (hl : 576≤n) (hh : n<612) : (entryNode48_51 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode48_49_depth entryNode49_51_depth n hl hh
def entryNode51_52 (n : ℕ) : Source × ℕ := entryPart51 (n-612)
theorem entryNode51_52_binding (n : ℕ) (hl : 612≤n) (hh : n<624) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode51_52 n).1 (-1) (entryNode51_52 n).2 := by
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
def entryNode52_53 (n : ℕ) : Source × ℕ := entryPart52 (n-624)
theorem entryNode52_53_binding (n : ℕ) (hl : 624≤n) (hh : n<636) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode52_53 n).1 (-1) (entryNode52_53 n).2 := by
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
def entryNode51_53 (n : ℕ) : Source × ℕ := if n<624 then entryNode51_52 n else entryNode52_53 n
theorem entryNode51_53_binding (n : ℕ) (hl : 612≤n) (hh : n<636) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode51_53 n).1 (-1) (entryNode51_53 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode51_52_binding entryNode52_53_binding n hl hh
theorem entryNode51_53_support (n : ℕ) (hl : 612≤n) (hh : n<636) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode51_53 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode51_52_support entryNode52_53_support n hl hh
theorem entryNode51_53_depth (n : ℕ) (hl : 612≤n) (hh : n<636) : (entryNode51_53 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode51_52_depth entryNode52_53_depth n hl hh
def entryNode53_54 (n : ℕ) : Source × ℕ := entryPart53 (n-636)
theorem entryNode53_54_binding (n : ℕ) (hl : 636≤n) (hh : n<648) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode53_54 n).1 (-1) (entryNode53_54 n).2 := by
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
def entryNode54_55 (n : ℕ) : Source × ℕ := entryPart54 (n-648)
theorem entryNode54_55_binding (n : ℕ) (hl : 648≤n) (hh : n<649) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode54_55 n).1 (-1) (entryNode54_55 n).2 := by
  have hn : n-648<1 := by omega
  have he : 648+(n-648)=n := by omega
  simpa only [entryNode54_55,he] using bindingPart54 ⟨n-648,hn⟩
theorem entryNode54_55_support (n : ℕ) (hl : 648≤n) (hh : n<649) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode54_55 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  have hn : n-648<1 := by omega
  have he : 648+(n-648)=n := by omega
  simpa only [entryNode54_55,he] using supportPart54 ⟨n-648,hn⟩
theorem entryNode54_55_depth (n : ℕ) (hl : 648≤n) (hh : n<649) : (entryNode54_55 n).2≤1 := by
  have hn : n-648<1 := by omega
  have he : 648+(n-648)=n := by omega
  simpa only [entryNode54_55,he] using depthPart54 ⟨n-648,hn⟩
def entryNode53_55 (n : ℕ) : Source × ℕ := if n<648 then entryNode53_54 n else entryNode54_55 n
theorem entryNode53_55_binding (n : ℕ) (hl : 636≤n) (hh : n<649) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode53_55 n).1 (-1) (entryNode53_55 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode53_54_binding entryNode54_55_binding n hl hh
theorem entryNode53_55_support (n : ℕ) (hl : 636≤n) (hh : n<649) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode53_55 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode53_54_support entryNode54_55_support n hl hh
theorem entryNode53_55_depth (n : ℕ) (hl : 636≤n) (hh : n<649) : (entryNode53_55 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode53_54_depth entryNode54_55_depth n hl hh
def entryNode51_55 (n : ℕ) : Source × ℕ := if n<636 then entryNode51_53 n else entryNode53_55 n
theorem entryNode51_55_binding (n : ℕ) (hl : 612≤n) (hh : n<649) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode51_55 n).1 (-1) (entryNode51_55 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode51_53_binding entryNode53_55_binding n hl hh
theorem entryNode51_55_support (n : ℕ) (hl : 612≤n) (hh : n<649) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode51_55 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode51_53_support entryNode53_55_support n hl hh
theorem entryNode51_55_depth (n : ℕ) (hl : 612≤n) (hh : n<649) : (entryNode51_55 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode51_53_depth entryNode53_55_depth n hl hh
def entryNode48_55 (n : ℕ) : Source × ℕ := if n<612 then entryNode48_51 n else entryNode51_55 n
theorem entryNode48_55_binding (n : ℕ) (hl : 576≤n) (hh : n<649) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode48_55 n).1 (-1) (entryNode48_55 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode48_51_binding entryNode51_55_binding n hl hh
theorem entryNode48_55_support (n : ℕ) (hl : 576≤n) (hh : n<649) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode48_55 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode48_51_support entryNode51_55_support n hl hh
theorem entryNode48_55_depth (n : ℕ) (hl : 576≤n) (hh : n<649) : (entryNode48_55 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode48_51_depth entryNode51_55_depth n hl hh
def entryNode41_55 (n : ℕ) : Source × ℕ := if n<576 then entryNode41_48 n else entryNode48_55 n
theorem entryNode41_55_binding (n : ℕ) (hl : 492≤n) (hh : n<649) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode41_55 n).1 (-1) (entryNode41_55 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode41_48_binding entryNode48_55_binding n hl hh
theorem entryNode41_55_support (n : ℕ) (hl : 492≤n) (hh : n<649) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode41_55 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode41_48_support entryNode48_55_support n hl hh
theorem entryNode41_55_depth (n : ℕ) (hl : 492≤n) (hh : n<649) : (entryNode41_55 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode41_48_depth entryNode48_55_depth n hl hh
def entryNode27_55 (n : ℕ) : Source × ℕ := if n<492 then entryNode27_41 n else entryNode41_55 n
theorem entryNode27_55_binding (n : ℕ) (hl : 324≤n) (hh : n<649) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode27_55 n).1 (-1) (entryNode27_55 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode27_41_binding entryNode41_55_binding n hl hh
theorem entryNode27_55_support (n : ℕ) (hl : 324≤n) (hh : n<649) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode27_55 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode27_41_support entryNode41_55_support n hl hh
theorem entryNode27_55_depth (n : ℕ) (hl : 324≤n) (hh : n<649) : (entryNode27_55 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode27_41_depth entryNode41_55_depth n hl hh
def entryNode0_55 (n : ℕ) : Source × ℕ := if n<324 then entryNode0_27 n else entryNode27_55 n
theorem entryNode0_55_binding (n : ℕ) (hl : 0≤n) (hh : n<649) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entryNode0_55 n).1 (-1) (entryNode0_55 n).2 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun n (row : Source × ℕ) => QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs n=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (row).1 (-1) (row).2) _ _ entryNode0_27_binding entryNode27_55_binding n hl hh
theorem entryNode0_55_support (n : ℕ) (hl : 0≤n) (hh : n<649) : (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entryNode0_55 n).1 (-1)).all (fun t => decide (t.2.1<607))=true := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (row).1 (-1)).all (fun t => decide (t.2.1<607))=true) _ _ entryNode0_27_support entryNode27_55_support n hl hh
theorem entryNode0_55_depth (n : ℕ) (hl : 0≤n) (hh : n<649) : (entryNode0_55 n).2≤1 := by
  exact QuantitativeArithmeticFiniteRangeCertificates.selected_join (fun _ (row : Source × ℕ) => (row).2≤1) _ _ entryNode0_27_depth entryNode27_55_depth n hl hh
def entry (i : Fin 649) : Source × ℕ := entryNode0_55 i.val
theorem input_binding (i : Fin 649) : QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusStages.inputs i.val=QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.jetPolynomial (entry i).1 (-1) (entry i).2 := entryNode0_55_binding i.val (Nat.zero_le _) i.isLt
theorem depth_bound (i : Fin 649) : (entry i).2≤1 := entryNode0_55_depth i.val (Nat.zero_le _) i.isLt
theorem leading_support (i : Fin 649) : ∀ t∈QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode.leadingCode (entry i).1 (-1), t.2.1<607 := by
  intro t ht
  exact of_decide_eq_true ((List.all_eq_true.mp (entryNode0_55_support i.val (Nat.zero_le _) i.isLt)) t ht)
#print axioms input_binding
#print axioms leading_support
#print axioms depth_bound
end QuantitativeArithmeticSmallLevelTwentySevenZeroJetCommonMinusSourceBinding
end
end
