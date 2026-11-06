module
public meta import QuantitativeArithmeticFiniteRangeCommandsV4

public import QuantitativeArithmeticFiniteRangeCertificatesV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModelTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxMinusLaurentTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveCuspMinusLaurentTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.FullMinusLeading. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveFullMinusLeadingDataV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FullMinusLeading
open QuantitativeArithmeticSevenLaurentRows
def gaugeCoordinates : List ℕ := [52, 58, 62, 116, 162, 166, 172, 174, 186, 216, 234, 244, 264, 278, 282, 332, 348, 354, 365, 386, 396, 398, 402, 408, 410, 426, 432, 444, 474, 512, 576, 580, 604, 606, 618, 624, 634, 642, 646, 648, 664, 676, 688, 694, 696, 702, 706, 712, 718, 768, 794, 796, 810, 834, 838, 848, 864, 876, 884, 888, 902, 914, 934, 936, 986, 992, 998, 1016]
def source (i : ℕ) : Poly := if i<4450 then AuxMinusLaurent.source i else [(1,gaugeCoordinates.getD (i-4450) 0,(0,0,0,0,0,0,0))]
end QuantitativeArithmeticSmallLevelTwentyFive.FullMinusLeading
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveFullMinusLeadingPhysicalV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FullMinusLeading
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

theorem physical_flag_0 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+0))=true := by decide +kernel
theorem physical_flag_1 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+64))=true := by decide +kernel
theorem physical_flag_2 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+128))=true := by decide +kernel
theorem physical_flag_3 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+192))=true := by decide +kernel
theorem physical_flag_4 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+256))=true := by decide +kernel
theorem physical_flag_5 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+320))=true := by decide +kernel
theorem physical_flag_6 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+384))=true := by decide +kernel
theorem physical_flag_7 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+448))=true := by decide +kernel
theorem physical_flag_8 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+512))=true := by decide +kernel
theorem physical_flag_9 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+576))=true := by decide +kernel
theorem physical_flag_10 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+640))=true := by decide +kernel
theorem physical_flag_11 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+704))=true := by decide +kernel
theorem physical_flag_12 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+768))=true := by decide +kernel
theorem physical_flag_13 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+832))=true := by decide +kernel
theorem physical_flag_14 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+896))=true := by decide +kernel
theorem physical_flag_15 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+960))=true := by decide +kernel
theorem physical_flag_16 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1024))=true := by decide +kernel
theorem physical_flag_17 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1088))=true := by decide +kernel
theorem physical_flag_18 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1152))=true := by decide +kernel
theorem physical_flag_19 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1216))=true := by decide +kernel
theorem physical_flag_20 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1280))=true := by decide +kernel
theorem physical_flag_21 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1344))=true := by decide +kernel
theorem physical_flag_22 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1408))=true := by decide +kernel
theorem physical_flag_23 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1472))=true := by decide +kernel
theorem physical_flag_24 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1536))=true := by decide +kernel
theorem physical_flag_25 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1600))=true := by decide +kernel
theorem physical_flag_26 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1664))=true := by decide +kernel
theorem physical_flag_27 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1728))=true := by decide +kernel
theorem physical_flag_28 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1792))=true := by decide +kernel
theorem physical_flag_29 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1856))=true := by decide +kernel
theorem physical_flag_30 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1920))=true := by decide +kernel
theorem physical_flag_31 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+1984))=true := by decide +kernel
theorem physical_flag_32 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2048))=true := by decide +kernel
theorem physical_flag_33 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2112))=true := by decide +kernel
theorem physical_flag_34 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2176))=true := by decide +kernel
theorem physical_flag_35 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2240))=true := by decide +kernel
theorem physical_flag_36 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2304))=true := by decide +kernel
theorem physical_flag_37 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2368))=true := by decide +kernel
theorem physical_flag_38 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2432))=true := by decide +kernel
theorem physical_flag_39 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2496))=true := by decide +kernel
theorem physical_flag_40 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2560))=true := by decide +kernel
theorem physical_flag_41 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2624))=true := by decide +kernel
theorem physical_flag_42 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2688))=true := by decide +kernel
theorem physical_flag_43 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2752))=true := by decide +kernel
theorem physical_flag_44 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2816))=true := by decide +kernel
theorem physical_flag_45 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2880))=true := by decide +kernel
theorem physical_flag_46 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+2944))=true := by decide +kernel
theorem physical_flag_47 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3008))=true := by decide +kernel
theorem physical_flag_48 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3072))=true := by decide +kernel
theorem physical_flag_49 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3136))=true := by decide +kernel
theorem physical_flag_50 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3200))=true := by decide +kernel
theorem physical_flag_51 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3264))=true := by decide +kernel
theorem physical_flag_52 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3328))=true := by decide +kernel
theorem physical_flag_53 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3392))=true := by decide +kernel
theorem physical_flag_54 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3456))=true := by decide +kernel
theorem physical_flag_55 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3520))=true := by decide +kernel
theorem physical_flag_56 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3584))=true := by decide +kernel
theorem physical_flag_57 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3648))=true := by decide +kernel
theorem physical_flag_58 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3712))=true := by decide +kernel
theorem physical_flag_59 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3776))=true := by decide +kernel
theorem physical_flag_60 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3840))=true := by decide +kernel
theorem physical_flag_61 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3904))=true := by decide +kernel
theorem physical_flag_62 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+3968))=true := by decide +kernel
theorem physical_flag_63 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+4032))=true := by decide +kernel
theorem physical_flag_64 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+4096))=true := by decide +kernel
theorem physical_flag_65 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+4160))=true := by decide +kernel
theorem physical_flag_66 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+4224))=true := by decide +kernel
theorem physical_flag_67 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+4288))=true := by decide +kernel
theorem physical_flag_68 : ∀ j : Fin 64, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+4352))=true := by decide +kernel
theorem physical_flag_69 : ∀ j : Fin 34, CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual (j.val+4416))=true := by decide +kernel
theorem all_physical_flag : ∀ i : Fin 4450,
    CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual i.val)=true := by
  let P : ℕ → Prop := fun i => CuspMinusLaurent.physicalFlag (AuxMinusLaurent.actual i)=true
  have h : ∀ i<4450, P (i+0) := (finite_range% P 0 [
    64 => (fun i hi => physical_flag_0 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_1 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_2 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_3 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_4 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_5 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_6 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_7 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_8 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_9 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_10 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_11 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_12 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_13 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_14 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_15 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_16 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_17 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_18 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_19 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_20 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_21 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_22 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_23 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_24 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_25 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_26 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_27 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_28 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_29 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_30 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_31 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_32 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_33 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_34 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_35 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_36 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_37 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_38 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_39 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_40 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_41 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_42 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_43 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_44 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_45 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_46 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_47 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_48 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_49 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_50 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_51 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_52 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_53 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_54 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_55 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_56 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_57 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_58 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_59 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_60 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_61 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_62 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_63 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_64 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_65 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_66 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_67 ⟨i,hi⟩),
    64 => (fun i hi => physical_flag_68 ⟨i,hi⟩),
    34 => (fun i hi => physical_flag_69 ⟨i,hi⟩)
  ])
  intro i
  exact h i.val i.isLt

theorem source_physical (i : Fin 4450) : AuxMinusLaurent.actual i.val=
    .physical (CuspMinusLaurent.physicalPart (AuxMinusLaurent.actual i.val)) :=
  CuspMinusLaurent.physicalPart_eq _ (all_physical_flag i)

theorem gauge_coordinate (i : Fin 68) : gaugeCoordinates.getD i.val 0=
    (AuxMinusLaurent.freeCoordinate i).val := by
  revert i
  decide +kernel

#print axioms all_physical_flag
#print axioms source_physical
#print axioms gauge_coordinate
end QuantitativeArithmeticSmallLevelTwentyFive.FullMinusLeading
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveFullMinusLeadingPoleRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FullMinusLeading
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector

/-- The 4518 source equations follow from the original positive-phase
hypotheses and the canonical gauge, with a simple weight pole allowed. -/
theorem original_pole_rows_allowed
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(-1)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge AuxMinusLaurent.basis
      AuxMinusLaurent.freeCoordinate m f z (gridVector 1050 (2*m) f z))
    (s : ℂ) (v : Fin 1050 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ,0<n → (s+n)≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hweight : ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)) :
    ∀ i<4518, eval (primeParameter 2 m s) (primeParameter 3 m s)
      (primeParameter 5 m s) (primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
      (periodicVector v) (source i)=0 := by
  intro i hi
  by_cases hip : i<4450
  · have hr := source_physical ⟨i,hip⟩
    have hp := AuxMinusLaurent.all_actual_source ⟨i,by omega⟩
    have hq := AuxMinusLaurent.all_actual_tail ⟨i,by omega⟩
    rw [hr] at hp hq
    have hl := physical_leading_pole_allowed AuxMinusLaurent.basis AuxMinusLaurent.freeCoordinate
      AuxMinusLaurent.basis_periodic (CuspMinusLaurent.physicalPart (AuxMinusLaurent.actual i)) (-1)
      (AuxMinusLaurent.source i) (AuxMinusLaurent.tail i) hp hq
      (AuxMinusLaurent.all_source_zero ⟨i,by omega⟩) (AuxMinusLaurent.all_tail_zero ⟨i,by omega⟩)
      hm hf ε hε hlaw (by simpa using hχ) BG G hG hGF s v hv hshift hweight
    have hn (p : ℕ) (hp0 : p≠0) : primeParameter p m s≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp0))
    have he := eval_rawSourcePoly
      (.physical (CuspMinusLaurent.physicalPart (AuxMinusLaurent.actual i))) hf ε s (-1)
      (by simpa using hχ) v
    rw [← eval_normalizedPoly _ _ _ _ _ _ _ _ (hn 2 (by decide)) (hn 3 (by decide))
      (hn 5 (by decide)) (hn 7 (by decide)),hp] at he
    simpa only [source,ite_eq_left hip,sourceLeading] using he.trans hl
  · have hj : i-4450<68 := by omega
    have hg := continued_free_zero AuxMinusLaurent.basis AuxMinusLaurent.freeCoordinate
      AuxMinusLaurent.basis_free_coordinate m f BG G hG hGF
    have hfree : v (AuxMinusLaurent.freeCoordinate ⟨i-4450,hj⟩)=0 := by
      classical
      have h := hv.2 (fun _ t => if t=AuxMinusLaurent.freeCoordinate ⟨i-4450,hj⟩ then 1 else 0)
        (fun _ => 0) (fun _ => analyticAt_const) analyticAt_const (by
          filter_upwards [] with z
          simp [hg])
      simpa using h
    simp only [source,ite_eq_right hip,eval,monomial,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,Rat.cast_one,zpow_zero,pow_zero,mul_one,one_mul,add_zero]
    rw [gauge_coordinate ⟨i-4450,hj⟩,periodicVector_fin]
    exact hfree

#print axioms original_pole_rows_allowed
end QuantitativeArithmeticSmallLevelTwentyFive.FullMinusLeading
end
end
