module
public import SmallLevelTwentySixGermDAGInputGermsV1
public import SmallLevelTwentySixGermDAGAllV1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation

def rawRows : Fin 90→Poly :=
  ![SmallLevelTwentySixGermPrimitiveSparseMMM.Row00.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row01.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row02.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row03.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row04.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row05.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row06.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row07.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row08.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row09.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row10.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row11.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row12.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row13.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row14.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row15.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row16.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row17.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row18.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row19.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row20.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row21.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row22.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row23.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row24.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row25.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row26.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row27.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row28.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row29.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row30.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row31.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row32.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row33.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row34.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row35.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row36.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row37.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row38.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row39.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row40.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row41.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row42.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row43.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row44.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row45.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row46.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row47.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row48.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row49.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row50.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row51.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row52.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row53.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row54.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row55.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row56.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row57.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row58.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row59.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row60.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row61.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row62.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row63.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row64.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row65.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row66.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row67.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row68.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row69.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row70.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row71.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row72.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row73.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row74.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row75.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row76.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row77.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row78.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row79.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row80.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row81.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row82.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row83.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row84.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row85.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row86.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row87.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row88.rawData,
    SmallLevelTwentySixGermPrimitiveSparseMMM.Row89.rawData]

theorem rawRows_derived (i : Fin 90) : ∃ p : Poly, Derived sourceRows 1191 p ∧ p.Perm (rawRows i) := by
  fin_cases i
  · exact primitive_raw_00
  · exact primitive_raw_01
  · exact primitive_raw_02
  · exact primitive_raw_03
  · exact primitive_raw_04
  · exact primitive_raw_05
  · exact primitive_raw_06
  · exact primitive_raw_07
  · exact primitive_raw_08
  · exact primitive_raw_09
  · exact primitive_raw_10
  · exact primitive_raw_11
  · exact primitive_raw_12
  · exact primitive_raw_13
  · exact primitive_raw_14
  · exact primitive_raw_15
  · exact primitive_raw_16
  · exact primitive_raw_17
  · exact primitive_raw_18
  · exact primitive_raw_19
  · exact primitive_raw_20
  · exact primitive_raw_21
  · exact primitive_raw_22
  · exact primitive_raw_23
  · exact primitive_raw_24
  · exact primitive_raw_25
  · exact primitive_raw_26
  · exact primitive_raw_27
  · exact primitive_raw_28
  · exact primitive_raw_29
  · exact primitive_raw_30
  · exact primitive_raw_31
  · exact primitive_raw_32
  · exact primitive_raw_33
  · exact primitive_raw_34
  · exact primitive_raw_35
  · exact primitive_raw_36
  · exact primitive_raw_37
  · exact primitive_raw_38
  · exact primitive_raw_39
  · exact primitive_raw_40
  · exact primitive_raw_41
  · exact primitive_raw_42
  · exact primitive_raw_43
  · exact primitive_raw_44
  · exact primitive_raw_45
  · exact primitive_raw_46
  · exact primitive_raw_47
  · exact primitive_raw_48
  · exact primitive_raw_49
  · exact primitive_raw_50
  · exact primitive_raw_51
  · exact primitive_raw_52
  · exact primitive_raw_53
  · exact primitive_raw_54
  · exact primitive_raw_55
  · exact primitive_raw_56
  · exact primitive_raw_57
  · exact primitive_raw_58
  · exact primitive_raw_59
  · exact primitive_raw_60
  · exact primitive_raw_61
  · exact primitive_raw_62
  · exact primitive_raw_63
  · exact primitive_raw_64
  · exact primitive_raw_65
  · exact primitive_raw_66
  · exact primitive_raw_67
  · exact primitive_raw_68
  · exact primitive_raw_69
  · exact primitive_raw_70
  · exact primitive_raw_71
  · exact primitive_raw_72
  · exact primitive_raw_73
  · exact primitive_raw_74
  · exact primitive_raw_75
  · exact primitive_raw_76
  · exact primitive_raw_77
  · exact primitive_raw_78
  · exact primitive_raw_79
  · exact primitive_raw_80
  · exact primitive_raw_81
  · exact primitive_raw_82
  · exact primitive_raw_83
  · exact primitive_raw_84
  · exact primitive_raw_85
  · exact primitive_raw_86
  · exact primitive_raw_87
  · exact primitive_raw_88
  · exact primitive_raw_89

/-- The ninety raw three-layer rows hold for the original continuation in
this sign chart. No row-elimination certificate is an external hypothesis. -/
theorem original_raw_germs {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -1) (hs2 : badParameter f 2= -1) (hs13 : badParameter f 13= -1)
    (i : Fin 90) :
    HasAnalyticGerm (fun z => eval (parameter 2 m z) (parameter 3 m z)
      (parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
      1 (replayVector m S.G z) (rawRows i)) x := by
  obtain ⟨p,hd,hperm⟩ := rawRows_derived i
  have hh := original_derived_germ S x hshift hx hx1 hη hs2 hs13 hd
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  unfold eval
  exact (hperm.map _).sum_eq

#print axioms rawRows_derived
#print axioms original_raw_germs
end SmallLevelTwentySixGermDAG
