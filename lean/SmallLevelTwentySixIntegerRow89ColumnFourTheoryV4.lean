module

public import QuantitativeArithmeticCoefficientSlicesV1
public import QuantitativeArithmeticExponentEncodingV1
public import SmallLevelTwentySixIntegerRowIndexColumnFourSourcesSeriesV4

/-! Consolidated chapter: SmallLevelTwentySixIntegerRow89ColumnFour. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticCompact26Column89FourBoundsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace SmallLevelTwentySixIntegerRow89ColumnFour
open QuantitativeArithmeticIntegerSevenLaurentRows QuantitativeArithmeticExponentEncoding

def operationData : Poly := [((-7381125000),0,(6,0,0,0,0,0,0)),
((-2332800),0,(4,1,0,1,0,0,0)),
((-6561000000),0,(5,0,0,0,1,0,0)),
(58320000,0,(4,1,0,0,0,1,0)),
(29524500000,0,(5,0,0,0,0,0,0)),
((-1458000000),0,(4,1,0,0,0,0,0)),
(144000000,0,(3,2,0,0,0,0,0)),
(9331200,0,(3,1,0,1,0,0,0)),
(26244000000,0,(4,0,0,0,1,0,0)),
((-233280000),0,(3,1,0,0,0,1,0)),
(5832000000,0,(3,1,0,0,0,0,0)),
((-576000000),0,(2,2,0,0,0,0,0)),
((-755827200),0,(3,0,0,1,0,0,0)),
(18895680000,0,(3,0,0,0,0,1,0)),
((-472392000000),0,(3,0,0,0,0,0,0)),
(46656000000,0,(2,1,0,0,0,0,0)),
((-1476225),3,(5,0,0,0,0,0,0)),
(3600,3,(3,2,0,0,0,0,0)),
(32400,3,(3,1,0,0,1,0,0)),
(5904900,3,(4,0,0,0,0,0,0)),
(291600,3,(3,1,0,0,0,0,0)),
((-14400),3,(2,2,0,0,0,0,0)),
((-129600),3,(2,1,0,0,1,0,0)),
(10497600,3,(2,0,0,0,1,0,0)),
(94478400,3,(2,0,0,0,0,0,0)),
(249482025,4,(6,0,0,0,0,0,0)),
(12320100,4,(5,1,0,0,0,0,0)),
((-110880900),4,(5,0,0,0,1,0,0)),
(1995856200,4,(5,0,0,0,0,0,0)),
((-98560800),4,(4,1,0,0,0,0,0)),
(4867200,4,(3,2,0,0,0,0,0)),
(23619600,4,(4,0,1,0,0,0,0)),
(887047200,4,(4,0,0,0,1,0,0)),
(19958562000,4,(4,0,0,0,0,0,0)),
((-19468800),4,(2,2,0,0,0,0,0)),
(1576972800,4,(2,1,0,0,0,0,0)),
((-1),5,(0,0,0,0,0,0,0))]

theorem input_bounds : ∀ i : Fin 6,
    (inputs i).all (fun t => decide (Small t.2.2)) = true := by decide +kernel

theorem operation_bounds : operationData.all (fun t => decide (t.2.1 < 6 ∧ Small t.2.2)) = true := by decide +kernel

theorem semantic_bounds : ∀ t ∈ operationData, Small t.2.2 ∧ ∀ u ∈ inputs t.2.1, Small u.2.2 := by
  intro t ht
  have h : t.2.1 < 6 ∧ Small t.2.2 := of_decide_eq_true (List.all_eq_true.mp operation_bounds t ht)
  refine ⟨h.2, ?_⟩
  intro u hu
  exact of_decide_eq_true (List.all_eq_true.mp (input_bounds ⟨t.2.1,h.1⟩) u hu)

#print axioms input_bounds
#print axioms operation_bounds
#print axioms semantic_bounds
end SmallLevelTwentySixIntegerRow89ColumnFour
end
end

/-! ## QuantitativeArithmeticCompact26FilteredColumn89FourV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace SmallLevelTwentySixIntegerRow89ColumnFour
open QuantitativeArithmeticIntegerSevenLaurentRows

theorem bucket_0 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 0 = [] := by decide +kernel
#print axioms bucket_0

theorem bucket_1 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 1 = [] := by decide +kernel
#print axioms bucket_1

theorem bucket_2 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 2 = [] := by decide +kernel
#print axioms bucket_2

theorem bucket_3 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 3 = [] := by decide +kernel
#print axioms bucket_3

theorem bucket_4 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 4 = [] := by decide +kernel
#print axioms bucket_4

theorem bucket_5 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 5 = [] := by decide +kernel
#print axioms bucket_5

theorem bucket_6 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 6 = [] := by decide +kernel
#print axioms bucket_6

theorem bucket_7 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 7 = [] := by decide +kernel
#print axioms bucket_7

theorem bucket_8 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 8 = [] := by decide +kernel
#print axioms bucket_8

theorem bucket_9 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 9 = [] := by decide +kernel
#print axioms bucket_9

theorem bucket_10 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 10 = [] := by decide +kernel
#print axioms bucket_10

theorem bucket_11 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 11 = [] := by decide +kernel
#print axioms bucket_11

theorem bucket_12 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 12 = [] := by decide +kernel
#print axioms bucket_12

theorem bucket_13 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 13 = [] := by decide +kernel
#print axioms bucket_13

theorem bucket_14 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 14 = [] := by decide +kernel
#print axioms bucket_14

theorem bucket_15 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 15 = [] := by decide +kernel
#print axioms bucket_15

theorem bucket_16 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 16 = [] := by decide +kernel
#print axioms bucket_16

theorem bucket_17 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 17 = [] := by decide +kernel
#print axioms bucket_17

theorem bucket_18 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 18 = [] := by decide +kernel
#print axioms bucket_18

theorem bucket_19 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 19 = [] := by decide +kernel
#print axioms bucket_19

theorem bucket_20 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 20 = [] := by decide +kernel
#print axioms bucket_20

theorem bucket_21 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 21 = [] := by decide +kernel
#print axioms bucket_21

theorem bucket_22 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 22 = [] := by decide +kernel
#print axioms bucket_22

theorem bucket_23 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 23 = [] := by decide +kernel
#print axioms bucket_23

theorem bucket_24 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 24 = [] := by decide +kernel
#print axioms bucket_24

theorem bucket_25 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 25 = [] := by decide +kernel
#print axioms bucket_25

theorem bucket_26 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 26 = [] := by decide +kernel
#print axioms bucket_26

theorem bucket_27 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 27 = [] := by decide +kernel
#print axioms bucket_27

theorem bucket_28 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 28 = [] := by decide +kernel
#print axioms bucket_28

theorem bucket_29 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 29 = [] := by decide +kernel
#print axioms bucket_29

theorem bucket_30 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 30 = [] := by decide +kernel
#print axioms bucket_30

theorem bucket_31 : QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 31 = [] := by decide +kernel
#print axioms bucket_31

theorem bucket_certificates : ∀ j < 32, QuantitativeArithmeticCoefficientSlices.substitute inputs operationData 32 j = [] := by
  intro j hj
  interval_cases j
  · exact bucket_0
  · exact bucket_1
  · exact bucket_2
  · exact bucket_3
  · exact bucket_4
  · exact bucket_5
  · exact bucket_6
  · exact bucket_7
  · exact bucket_8
  · exact bucket_9
  · exact bucket_10
  · exact bucket_11
  · exact bucket_12
  · exact bucket_13
  · exact bucket_14
  · exact bucket_15
  · exact bucket_16
  · exact bucket_17
  · exact bucket_18
  · exact bucket_19
  · exact bucket_20
  · exact bucket_21
  · exact bucket_22
  · exact bucket_23
  · exact bucket_24
  · exact bucket_25
  · exact bucket_26
  · exact bucket_27
  · exact bucket_28
  · exact bucket_29
  · exact bucket_30
  · exact bucket_31

theorem column_certificate (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    eval x y z w a b c (fun i => eval x y z w a b c (fun _ => 1) (inputs i)) operationData=0 :=
  QuantitativeArithmeticCoefficientSlices.substitution_zero x y z w a b c hx hy hz hw inputs operationData 32 (by decide) semantic_bounds bucket_certificates

#print axioms bucket_certificates
#print axioms column_certificate
end SmallLevelTwentySixIntegerRow89ColumnFour
end
end
