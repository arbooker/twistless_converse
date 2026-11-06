module
public import SmallLevelTwentySixGridLeadingSupportDataV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGrid
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

theorem taylorSource_restrict_0 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 0) (gridTaylorT 0) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 0) (gridTaylorT 0) v := by
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  simp only [show gridTaylorQ 0=3 from rfl,show gridTaylorT 0=(-130:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h130,h390]

theorem taylorSource_restrict_1 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 1) (gridTaylorT 1) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 1) (gridTaylorT 1) v := by
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h455 : extension support (fun a => v (support a)) 455=v 455 :=
    extend_at support support_injective (fun a => v (support a)) 205
  simp only [show gridTaylorQ 1=3 from rfl,show gridTaylorT 1=(-65:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h195,h455]

theorem taylorSource_restrict_2 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 2) (gridTaylorT 2) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 2) (gridTaylorT 2) v := by
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  simp only [show gridTaylorQ 2=3 from rfl,show gridTaylorT 2=(-50:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h210,h470]

theorem taylorSource_restrict_3 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 3) (gridTaylorT 3) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 3) (gridTaylorT 3) v := by
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  simp only [show gridTaylorQ 3=3 from rfl,show gridTaylorT 3=(-40:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h220,h480]

theorem taylorSource_restrict_4 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 4) (gridTaylorT 4) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 4) (gridTaylorT 4) v := by
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  simp only [show gridTaylorQ 4=3 from rfl,show gridTaylorT 4=(-26:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h234,h494]

theorem taylorSource_restrict_5 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 5) (gridTaylorT 5) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 5) (gridTaylorT 5) v := by
  have h235 : extension support (fun a => v (support a)) 235=v 235 :=
    extend_at support support_injective (fun a => v (support a)) 98
  have h495 : extension support (fun a => v (support a)) 495=v 495 :=
    extend_at support support_injective (fun a => v (support a)) 215
  simp only [show gridTaylorQ 5=3 from rfl,show gridTaylorT 5=(-25:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h235,h495]

theorem taylorSource_restrict_6 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 6) (gridTaylorT 6) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 6) (gridTaylorT 6) v := by
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  simp only [show gridTaylorQ 6=3 from rfl,show gridTaylorT 6=(-20:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h240,h500]

theorem taylorSource_restrict_7 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 7) (gridTaylorT 7) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 7) (gridTaylorT 7) v := by
  have h247 : extension support (fun a => v (support a)) 247=v 247 :=
    extend_at support support_injective (fun a => v (support a)) 100
  have h507 : extension support (fun a => v (support a)) 507=v 507 :=
    extend_at support support_injective (fun a => v (support a)) 217
  simp only [show gridTaylorQ 7=3 from rfl,show gridTaylorT 7=(-13:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h247,h507]

theorem taylorSource_restrict_8 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 8) (gridTaylorT 8) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 8) (gridTaylorT 8) v := by
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  simp only [show gridTaylorQ 8=3 from rfl,show gridTaylorT 8=(-10:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h250,h510]

theorem taylorSource_restrict_9 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 9) (gridTaylorT 9) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 9) (gridTaylorT 9) v := by
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  simp only [show gridTaylorQ 9=3 from rfl,show gridTaylorT 9=(10:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h270,h530]

theorem taylorSource_restrict_10 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 10) (gridTaylorT 10) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 10) (gridTaylorT 10) v := by
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h533 : extension support (fun a => v (support a)) 533=v 533 :=
    extend_at support support_injective (fun a => v (support a)) 221
  simp only [show gridTaylorQ 10=3 from rfl,show gridTaylorT 10=(13:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h273,h533]

theorem taylorSource_restrict_11 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 11) (gridTaylorT 11) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 11) (gridTaylorT 11) v := by
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  simp only [show gridTaylorQ 11=3 from rfl,show gridTaylorT 11=(20:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h280,h540]

theorem taylorSource_restrict_12 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 12) (gridTaylorT 12) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 12) (gridTaylorT 12) v := by
  have h285 : extension support (fun a => v (support a)) 285=v 285 :=
    extend_at support support_injective (fun a => v (support a)) 106
  have h545 : extension support (fun a => v (support a)) 545=v 545 :=
    extend_at support support_injective (fun a => v (support a)) 223
  simp only [show gridTaylorQ 12=3 from rfl,show gridTaylorT 12=(25:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h285,h545]

theorem taylorSource_restrict_13 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 13) (gridTaylorT 13) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 13) (gridTaylorT 13) v := by
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  simp only [show gridTaylorQ 13=3 from rfl,show gridTaylorT 13=(26:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h286,h546]

theorem taylorSource_restrict_14 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 14) (gridTaylorT 14) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 14) (gridTaylorT 14) v := by
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  simp only [show gridTaylorQ 14=3 from rfl,show gridTaylorT 14=(40:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h300,h560]

theorem taylorSource_restrict_15 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 15) (gridTaylorT 15) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 15) (gridTaylorT 15) v := by
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  simp only [show gridTaylorQ 15=3 from rfl,show gridTaylorT 15=(50:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h310,h570]

theorem taylorSource_restrict_16 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 16) (gridTaylorT 16) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 16) (gridTaylorT 16) v := by
  have h325 : extension support (fun a => v (support a)) 325=v 325 :=
    extend_at support support_injective (fun a => v (support a)) 116
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  simp only [show gridTaylorQ 16=3 from rfl,show gridTaylorT 16=(65:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h325,h585]

theorem taylorSource_restrict_17 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 17) (gridTaylorT 17) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 17) (gridTaylorT 17) v := by
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  simp only [show gridTaylorQ 17=3 from rfl,show gridTaylorT 17=(130:ℤ) from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h390,h650]

theorem taylorSource_restrict_18 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 18) (gridTaylorT 18) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 18) (gridTaylorT 18) v := by
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  simp only [show gridTaylorQ 18=4 from rfl,show gridTaylorT 18=(-25:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h170,h560]

theorem taylorSource_restrict_19 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 19) (gridTaylorT 19) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 19) (gridTaylorT 19) v := by
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  simp only [show gridTaylorQ 19=4 from rfl,show gridTaylorT 19=(-15:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h180,h570]

theorem taylorSource_restrict_20 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 20) (gridTaylorT 20) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 20) (gridTaylorT 20) v := by
  have h182 : extension support (fun a => v (support a)) 182=v 182 :=
    extend_at support support_injective (fun a => v (support a)) 85
  have h572 : extension support (fun a => v (support a)) 572=v 572 :=
    extend_at support support_injective (fun a => v (support a)) 230
  simp only [show gridTaylorQ 20=4 from rfl,show gridTaylorT 20=(-13:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h182,h572]

theorem taylorSource_restrict_21 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 21) (gridTaylorT 21) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 21) (gridTaylorT 21) v := by
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  simp only [show gridTaylorQ 21=4 from rfl,show gridTaylorT 21=(-5:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h190,h580]

theorem taylorSource_restrict_22 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 22) (gridTaylorT 22) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 22) (gridTaylorT 22) v := by
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  simp only [show gridTaylorQ 22=4 from rfl,show gridTaylorT 22=(5:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h200,h590]

theorem taylorSource_restrict_23 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 23) (gridTaylorT 23) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 23) (gridTaylorT 23) v := by
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h598 : extension support (fun a => v (support a)) 598=v 598 :=
    extend_at support support_injective (fun a => v (support a)) 236
  simp only [show gridTaylorQ 23=4 from rfl,show gridTaylorT 23=(13:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h208,h598]

theorem taylorSource_restrict_24 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 24) (gridTaylorT 24) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 24) (gridTaylorT 24) v := by
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  simp only [show gridTaylorQ 24=4 from rfl,show gridTaylorT 24=(15:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h210,h600]

theorem taylorSource_restrict_25 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 25) (gridTaylorT 25) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 25) (gridTaylorT 25) v := by
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  simp only [show gridTaylorQ 25=4 from rfl,show gridTaylorT 25=(25:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h220,h610]

theorem taylorSource_restrict_26 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 26) (gridTaylorT 26) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 26) (gridTaylorT 26) v := by
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  simp only [show gridTaylorQ 26=4 from rfl,show gridTaylorT 26=(39:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h234,h624]

theorem taylorSource_restrict_27 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 27) (gridTaylorT 27) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 27) (gridTaylorT 27) v := by
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  simp only [show gridTaylorQ 27=4 from rfl,show gridTaylorT 27=(45:ℤ) from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h240,h630]

theorem taylorSource_restrict_28 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 28) (gridTaylorT 28) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 28) (gridTaylorT 28) v := by
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  simp only [show gridTaylorQ 28=6 from rfl,show gridTaylorT 28=(-26:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h104,h624]

theorem taylorSource_restrict_29 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 29) (gridTaylorT 29) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 29) (gridTaylorT 29) v := by
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h625 : extension support (fun a => v (support a)) 625=v 625 :=
    extend_at support support_injective (fun a => v (support a)) 243
  simp only [show gridTaylorQ 29=6 from rfl,show gridTaylorT 29=(-25:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h105,h625]

theorem taylorSource_restrict_30 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 30) (gridTaylorT 30) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 30) (gridTaylorT 30) v := by
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  simp only [show gridTaylorQ 30=6 from rfl,show gridTaylorT 30=(-20:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h110,h630]

theorem taylorSource_restrict_31 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 31) (gridTaylorT 31) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 31) (gridTaylorT 31) v := by
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h637 : extension support (fun a => v (support a)) 637=v 637 :=
    extend_at support support_injective (fun a => v (support a)) 245
  simp only [show gridTaylorQ 31=6 from rfl,show gridTaylorT 31=(-13:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h117,h637]

theorem taylorSource_restrict_32 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 32) (gridTaylorT 32) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 32) (gridTaylorT 32) v := by
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  simp only [show gridTaylorQ 32=6 from rfl,show gridTaylorT 32=(-10:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h120,h640]

theorem taylorSource_restrict_33 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 33) (gridTaylorT 33) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 33) (gridTaylorT 33) v := by
  have h128 : extension support (fun a => v (support a)) 128=v 128 :=
    extend_at support support_injective (fun a => v (support a)) 72
  have h648 : extension support (fun a => v (support a)) 648=v 648 :=
    extend_at support support_injective (fun a => v (support a)) 247
  simp only [show gridTaylorQ 33=6 from rfl,show gridTaylorT 33=(-2:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h128,h648]

theorem taylorSource_restrict_34 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 34) (gridTaylorT 34) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 34) (gridTaylorT 34) v := by
  have h132 : extension support (fun a => v (support a)) 132=v 132 :=
    extend_at support support_injective (fun a => v (support a)) 74
  have h652 : extension support (fun a => v (support a)) 652=v 652 :=
    extend_at support support_injective (fun a => v (support a)) 249
  simp only [show gridTaylorQ 34=6 from rfl,show gridTaylorT 34=(2:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h132,h652]

theorem taylorSource_restrict_35 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 35) (gridTaylorT 35) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 35) (gridTaylorT 35) v := by
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  simp only [show gridTaylorQ 35=6 from rfl,show gridTaylorT 35=(10:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h140,h660]

theorem taylorSource_restrict_36 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 36) (gridTaylorT 36) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 36) (gridTaylorT 36) v := by
  have h143 : extension support (fun a => v (support a)) 143=v 143 :=
    extend_at support support_injective (fun a => v (support a)) 76
  have h663 : extension support (fun a => v (support a)) 663=v 663 :=
    extend_at support support_injective (fun a => v (support a)) 251
  simp only [show gridTaylorQ 36=6 from rfl,show gridTaylorT 36=(13:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h143,h663]

theorem taylorSource_restrict_37 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 37) (gridTaylorT 37) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 37) (gridTaylorT 37) v := by
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  simp only [show gridTaylorQ 37=6 from rfl,show gridTaylorT 37=(20:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h150,h670]

theorem taylorSource_restrict_38 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 38) (gridTaylorT 38) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 38) (gridTaylorT 38) v := by
  have h155 : extension support (fun a => v (support a)) 155=v 155 :=
    extend_at support support_injective (fun a => v (support a)) 78
  have h675 : extension support (fun a => v (support a)) 675=v 675 :=
    extend_at support support_injective (fun a => v (support a)) 253
  simp only [show gridTaylorQ 38=6 from rfl,show gridTaylorT 38=(25:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h155,h675]

theorem taylorSource_restrict_39 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 39) (gridTaylorT 39) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 39) (gridTaylorT 39) v := by
  have h156 : extension support (fun a => v (support a)) 156=v 156 :=
    extend_at support support_injective (fun a => v (support a)) 79
  have h676 : extension support (fun a => v (support a)) 676=v 676 :=
    extend_at support support_injective (fun a => v (support a)) 254
  simp only [show gridTaylorQ 39=6 from rfl,show gridTaylorT 39=(26:ℤ) from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h156,h676]

theorem taylorSource_restrict_40 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 40) (gridTaylorT 40) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 40) (gridTaylorT 40) v := by
  have h72 : extension support (fun a => v (support a)) 72=v 72 :=
    extend_at support support_injective (fun a => v (support a)) 58
  have h228 : extension support (fun a => v (support a)) 228=v 228 :=
    extend_at support support_injective (fun a => v (support a)) 95
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h696 : extension support (fun a => v (support a)) 696=v 696 :=
    extend_at support support_injective (fun a => v (support a)) 259
  simp only [show gridTaylorQ 40=10 from rfl,show gridTaylorT 40=(-6:ℤ) from rfl,gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h72,h228,h540,h696]

theorem taylorSource_restrict_41 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 41) (gridTaylorT 41) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 41) (gridTaylorT 41) v := by
  have h84 : extension support (fun a => v (support a)) 84=v 84 :=
    extend_at support support_injective (fun a => v (support a)) 62
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h552 : extension support (fun a => v (support a)) 552=v 552 :=
    extend_at support support_injective (fun a => v (support a)) 226
  have h708 : extension support (fun a => v (support a)) 708=v 708 :=
    extend_at support support_injective (fun a => v (support a)) 263
  simp only [show gridTaylorQ 41=10 from rfl,show gridTaylorT 41=(6:ℤ) from rfl,gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h84,h240,h552,h708]

theorem taylorSource_restrict_42 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 42) (gridTaylorT 42) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 42) (gridTaylorT 42) v := by
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  simp only [show gridTaylorQ 42=12 from rfl,show gridTaylorT 42=(-5:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h60,h320,h450,h710]

theorem taylorSource_restrict_43 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 43) (gridTaylorT 43) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 43) (gridTaylorT 43) v := by
  have h64 : extension support (fun a => v (support a)) 64=v 64 :=
    extend_at support support_injective (fun a => v (support a)) 53
  have h324 : extension support (fun a => v (support a)) 324=v 324 :=
    extend_at support support_injective (fun a => v (support a)) 115
  have h454 : extension support (fun a => v (support a)) 454=v 454 :=
    extend_at support support_injective (fun a => v (support a)) 204
  have h714 : extension support (fun a => v (support a)) 714=v 714 :=
    extend_at support support_injective (fun a => v (support a)) 266
  simp only [show gridTaylorQ 43=12 from rfl,show gridTaylorT 43=(-1:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h64,h324,h454,h714]

theorem taylorSource_restrict_44 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 44) (gridTaylorT 44) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 44) (gridTaylorT 44) v := by
  have h66 : extension support (fun a => v (support a)) 66=v 66 :=
    extend_at support support_injective (fun a => v (support a)) 55
  have h326 : extension support (fun a => v (support a)) 326=v 326 :=
    extend_at support support_injective (fun a => v (support a)) 117
  have h456 : extension support (fun a => v (support a)) 456=v 456 :=
    extend_at support support_injective (fun a => v (support a)) 206
  have h716 : extension support (fun a => v (support a)) 716=v 716 :=
    extend_at support support_injective (fun a => v (support a)) 268
  simp only [show gridTaylorQ 44=12 from rfl,show gridTaylorT 44=(1:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h66,h326,h456,h716]

theorem taylorSource_restrict_45 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 45) (gridTaylorT 45) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 45) (gridTaylorT 45) v := by
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [show gridTaylorQ 45=12 from rfl,show gridTaylorT 45=(5:ℤ) from rfl,gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h70,h330,h460,h720]

theorem taylorSource_restrict_46 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 46) (gridTaylorT 46) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 46) (gridTaylorT 46) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [show gridTaylorQ 46=13 from rfl,show gridTaylorT 46=(-180:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h60,h120,h180,h240,h300,h360,h420,h480,h540,h660,h720]

theorem taylorSource_restrict_47 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 47) (gridTaylorT 47) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 47) (gridTaylorT 47) v := by
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [show gridTaylorQ 47=13 from rfl,show gridTaylorT 47=(-90:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h30,h90,h150,h210,h270,h330,h390,h450,h510,h570,h630,h750]

theorem taylorSource_restrict_48 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 48) (gridTaylorT 48) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 48) (gridTaylorT 48) v := by
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h400 : extension support (fun a => v (support a)) 400=v 400 :=
    extend_at support support_injective (fun a => v (support a)) 170
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  simp only [show gridTaylorQ 48=13 from rfl,show gridTaylorT 48=(-20:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h40,h100,h160,h220,h280,h340,h400,h460,h520,h580,h640,h700]

theorem taylorSource_restrict_49 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 49) (gridTaylorT 49) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 49) (gridTaylorT 49) v := by
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  simp only [show gridTaylorQ 49=13 from rfl,show gridTaylorT 49=(-10:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h50,h110,h170,h230,h290,h350,h410,h470,h530,h590,h650,h710]

theorem taylorSource_restrict_50 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 50) (gridTaylorT 50) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 50) (gridTaylorT 50) v := by
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  simp only [show gridTaylorQ 50=13 from rfl,show gridTaylorT 50=(10:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h70,h130,h190,h250,h310,h370,h430,h490,h550,h610,h670,h730]

theorem taylorSource_restrict_51 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 51) (gridTaylorT 51) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 51) (gridTaylorT 51) v := by
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [show gridTaylorQ 51=13 from rfl,show gridTaylorT 51=(20:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h80,h140,h200,h260,h320,h380,h440,h500,h560,h620,h680,h740]

theorem taylorSource_restrict_52 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 52) (gridTaylorT 52) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 52) (gridTaylorT 52) v := by
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [show gridTaylorQ 52=13 from rfl,show gridTaylorT 52=(30:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h90,h150,h210,h270,h330,h390,h450,h510,h570,h630,h690,h750]

theorem taylorSource_restrict_53 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 53) (gridTaylorT 53) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 53) (gridTaylorT 53) v := by
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [show gridTaylorQ 53=13 from rfl,show gridTaylorT 53=(90:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h30,h150,h210,h270,h330,h390,h450,h510,h570,h630,h690,h750]

theorem taylorSource_restrict_54 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 54) (gridTaylorT 54) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 54) (gridTaylorT 54) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [show gridTaylorQ 54=13 from rfl,show gridTaylorT 54=(180:ℤ) from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h60,h120,h240,h300,h360,h420,h480,h540,h600,h660,h720]

theorem taylorSource_restrict_55 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 55) (gridTaylorT 55) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 55) (gridTaylorT 55) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [show gridTaylorQ 55=26 from rfl,show gridTaylorT 55=(-90:ℤ) from rfl,gridSample,show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h60,h120,h180,h240,h360,h420,h480,h540,h600,h660,h720]

theorem taylorSource_restrict_56 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 56) (gridTaylorT 56) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 56) (gridTaylorT 56) v := by
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [show gridTaylorQ 56=26 from rfl,show gridTaylorT 56=(-10:ℤ) from rfl,gridSample,show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h20,h80,h140,h200,h260,h320,h440,h500,h560,h620,h680,h740]

theorem taylorSource_restrict_57 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 57) (gridTaylorT 57) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 57) (gridTaylorT 57) v := by
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [show gridTaylorQ 57=26 from rfl,show gridTaylorT 57=(10:ℤ) from rfl,gridSample,show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h40,h100,h160,h220,h280,h340,h460,h520,h580,h640,h700,h760]

theorem taylorSource_restrict_58 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 58) (gridTaylorT 58) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 58) (gridTaylorT 58) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [show gridTaylorQ 58=26 from rfl,show gridTaylorT 58=(90:ℤ) from rfl,gridSample,show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h60,h120,h180,h240,h300,h360,h420,h540,h600,h660,h720]

theorem taylorSource_restrict_59 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 59) (gridTaylorT 59) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 59) (gridTaylorT 59) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [show gridTaylorQ 59=39 from rfl,show gridTaylorT 59=(-20:ℤ) from rfl,gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h20,h60,h80,h120,h140,h180,h200,h260,h300,h320,h360,h380,h420,h440,h480,h540,h560,h600,h620,h660,h680,h720,h740]

theorem taylorSource_restrict_60 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 60) (gridTaylorT 60) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 60) (gridTaylorT 60) v := by
  have h10 : extension support (fun a => v (support a)) 10=v 10 :=
    extend_at support support_injective (fun a => v (support a)) 10
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [show gridTaylorQ 60=39 from rfl,show gridTaylorT 60=(-10:ℤ) from rfl,gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h10,h30,h70,h90,h130,h150,h190,h210,h270,h310,h330,h370,h390,h430,h450,h490,h550,h570,h610,h630,h670,h690,h730,h750]

theorem taylorSource_restrict_61 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 61) (gridTaylorT 61) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 61) (gridTaylorT 61) v := by
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  have h770 : extension support (fun a => v (support a)) 770=v 770 :=
    extend_at support support_injective (fun a => v (support a)) 311
  simp only [show gridTaylorQ 61=39 from rfl,show gridTaylorT 61=(10:ℤ) from rfl,gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h30,h50,h90,h110,h150,h170,h210,h230,h290,h330,h350,h390,h410,h450,h470,h510,h570,h590,h630,h650,h690,h710,h750,h770]

theorem taylorSource_restrict_62 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 62) (gridTaylorT 62) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 62) (gridTaylorT 62) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h400 : extension support (fun a => v (support a)) 400=v 400 :=
    extend_at support support_injective (fun a => v (support a)) 170
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [show gridTaylorQ 62=39 from rfl,show gridTaylorT 62=(20:ℤ) from rfl,gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h40,h60,h100,h120,h160,h180,h220,h240,h300,h340,h360,h400,h420,h460,h480,h520,h580,h600,h640,h660,h700,h720,h760]

theorem taylorSource_restrict_63 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 63) (gridTaylorT 63) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 63) (gridTaylorT 63) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [show gridTaylorQ 63=52 from rfl,show gridTaylorT 63=(-45:ℤ) from rfl,gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h30,h60,h90,h120,h180,h210,h240,h270,h300,h330,h360,h390,h420,h450,h480,h510,h570,h600,h630,h660,h690,h720,h750]

theorem taylorSource_restrict_64 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 64) (gridTaylorT 64) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 64) (gridTaylorT 64) v := by
  have h10 : extension support (fun a => v (support a)) 10=v 10 :=
    extend_at support support_injective (fun a => v (support a)) 10
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h400 : extension support (fun a => v (support a)) 400=v 400 :=
    extend_at support support_injective (fun a => v (support a)) 170
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [show gridTaylorQ 64=52 from rfl,show gridTaylorT 64=(-5:ℤ) from rfl,gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h10,h40,h70,h100,h130,h160,h220,h250,h280,h310,h340,h370,h400,h430,h460,h490,h520,h550,h610,h640,h670,h700,h730,h760]

theorem taylorSource_restrict_65 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 65) (gridTaylorT 65) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 65) (gridTaylorT 65) v := by
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  have h770 : extension support (fun a => v (support a)) 770=v 770 :=
    extend_at support support_injective (fun a => v (support a)) 311
  simp only [show gridTaylorQ 65=52 from rfl,show gridTaylorT 65=(5:ℤ) from rfl,gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h20,h50,h80,h110,h140,h170,h230,h260,h290,h320,h350,h380,h410,h440,h470,h500,h530,h560,h620,h650,h680,h710,h740,h770]

theorem taylorSource_restrict_66 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 66) (gridTaylorT 66) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 66) (gridTaylorT 66) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  simp only [show gridTaylorQ 66=52 from rfl,show gridTaylorT 66=(45:ℤ) from rfl,gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h30,h60,h90,h120,h150,h180,h210,h270,h300,h330,h360,h390,h420,h450,h480,h510,h540,h570,h600,h660,h690,h720,h750]

theorem taylorSource_restrict_67 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 67) (gridTaylorT 67) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 67) (gridTaylorT 67) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h400 : extension support (fun a => v (support a)) 400=v 400 :=
    extend_at support support_injective (fun a => v (support a)) 170
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [show gridTaylorQ 67=78 from rfl,show gridTaylorT 67=(-10:ℤ) from rfl,gridSample,show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h40,h60,h100,h160,h180,h220,h240,h280,h300,h340,h360,h400,h420,h460,h480,h520,h540,h580,h600,h660,h700,h720,h760]

theorem taylorSource_restrict_68 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 68) (gridTaylorT 68) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 68) (gridTaylorT 68) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [show gridTaylorQ 68=78 from rfl,show gridTaylorT 68=(10:ℤ) from rfl,gridSample,show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h20,h60,h80,h120,h180,h200,h240,h260,h300,h320,h360,h380,h420,h440,h480,h500,h540,h560,h600,h620,h680,h720,h740]

theorem taylorSource_restrict_69 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 69) (gridTaylorT 69) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 69) (gridTaylorT 69) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  have h770 : extension support (fun a => v (support a)) 770=v 770 :=
    extend_at support support_injective (fun a => v (support a)) 311
  simp only [show gridTaylorQ 69=156 from rfl,show gridTaylorT 69=(-5:ℤ) from rfl,gridSample,show residues 156=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77,79,83,85,89,95,97,101,103,107,109,113,115,119,121,125,127,131,133,137,139,145,149,151,155}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h20,h30,h50,h80,h90,h110,h120,h140,h150,h170,h180,h200,h210,h230,h240,h260,h270,h290,h300,h330,h350,h360,h380,h390,h410,h420,h440,h470,h480,h500,h510,h530,h540,h560,h570,h590,h600,h620,h630,h650,h660,h680,h690,h720,h740,h750,h770]

theorem taylorSource_restrict_70 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 70) (gridTaylorT 70) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 70) (gridTaylorT 70) v := by
  have h0 : extension support (fun a => v (support a)) 0=v 0 :=
    extend_at support support_injective (fun a => v (support a)) 0
  have h10 : extension support (fun a => v (support a)) 10=v 10 :=
    extend_at support support_injective (fun a => v (support a)) 10
  have h30 : extension support (fun a => v (support a)) 30=v 30 :=
    extend_at support support_injective (fun a => v (support a)) 28
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h90 : extension support (fun a => v (support a)) 90=v 90 :=
    extend_at support support_injective (fun a => v (support a)) 63
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h270 : extension support (fun a => v (support a)) 270=v 270 :=
    extend_at support support_injective (fun a => v (support a)) 103
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h390 : extension support (fun a => v (support a)) 390=v 390 :=
    extend_at support support_injective (fun a => v (support a)) 160
  have h400 : extension support (fun a => v (support a)) 400=v 400 :=
    extend_at support support_injective (fun a => v (support a)) 170
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h510 : extension support (fun a => v (support a)) 510=v 510 :=
    extend_at support support_injective (fun a => v (support a)) 218
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  have h690 : extension support (fun a => v (support a)) 690=v 690 :=
    extend_at support support_injective (fun a => v (support a)) 258
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  have h750 : extension support (fun a => v (support a)) 750=v 750 :=
    extend_at support support_injective (fun a => v (support a)) 293
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [show gridTaylorQ 70=156 from rfl,show gridTaylorT 70=(5:ℤ) from rfl,gridSample,show residues 156=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77,79,83,85,89,95,97,101,103,107,109,113,115,119,121,125,127,131,133,137,139,145,149,151,155}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h0,h10,h30,h40,h60,h90,h100,h120,h130,h150,h160,h180,h190,h210,h220,h240,h250,h270,h280,h300,h310,h340,h360,h370,h390,h400,h420,h430,h450,h480,h490,h510,h520,h540,h550,h570,h580,h600,h610,h630,h640,h660,h670,h690,h700,h730,h750,h760]

theorem entireSource_restrict_0 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 0) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 0) 0 v := by
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  simp only [show gridEntireQ 0=3 from rfl,gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h260,h520]

theorem entireSource_restrict_1 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 1) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 1) 0 v := by
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  simp only [show gridEntireQ 1=4 from rfl,gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h195,h585]

theorem entireSource_restrict_2 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 2) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 2) 0 v := by
  have h156 : extension support (fun a => v (support a)) 156=v 156 :=
    extend_at support support_injective (fun a => v (support a)) 79
  have h312 : extension support (fun a => v (support a)) 312=v 312 :=
    extend_at support support_injective (fun a => v (support a)) 112
  have h468 : extension support (fun a => v (support a)) 468=v 468 :=
    extend_at support support_injective (fun a => v (support a)) 209
  have h624 : extension support (fun a => v (support a)) 624=v 624 :=
    extend_at support support_injective (fun a => v (support a)) 242
  simp only [show gridEntireQ 2=5 from rfl,gridSample,show residues 5=({1,2,3,4}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h156,h312,h468,h624]

theorem entireSource_restrict_3 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 3) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 3) 0 v := by
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  simp only [show gridEntireQ 3=6 from rfl,gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h130,h650]

theorem entireSource_restrict_4 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 4) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 4) 0 v := by
  have h78 : extension support (fun a => v (support a)) 78=v 78 :=
    extend_at support support_injective (fun a => v (support a)) 60
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  have h702 : extension support (fun a => v (support a)) 702=v 702 :=
    extend_at support support_injective (fun a => v (support a)) 261
  simp only [show gridEntireQ 4=10 from rfl,gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h78,h234,h546,h702]

theorem entireSource_restrict_5 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 5) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 5) 0 v := by
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  simp only [show gridEntireQ 5=13 from rfl,gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h60,h120,h180,h240,h300,h360,h420,h480,h540,h600,h660,h720]

theorem entireSource_restrict_6 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 6) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 6) 0 v := by
  have h52 : extension support (fun a => v (support a)) 52=v 52 :=
    extend_at support support_injective (fun a => v (support a)) 42
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h364 : extension support (fun a => v (support a)) 364=v 364 :=
    extend_at support support_injective (fun a => v (support a)) 138
  have h416 : extension support (fun a => v (support a)) 416=v 416 :=
    extend_at support support_injective (fun a => v (support a)) 183
  have h572 : extension support (fun a => v (support a)) 572=v 572 :=
    extend_at support support_injective (fun a => v (support a)) 230
  have h676 : extension support (fun a => v (support a)) 676=v 676 :=
    extend_at support support_injective (fun a => v (support a)) 254
  have h728 : extension support (fun a => v (support a)) 728=v 728 :=
    extend_at support support_injective (fun a => v (support a)) 279
  simp only [show gridEntireQ 6=15 from rfl,gridSample,show residues 15=({1,2,4,7,8,11,13,14}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h52,h104,h208,h364,h416,h572,h676,h728]

theorem entireSource_restrict_7 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 7) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 7) 0 v := by
  have h39 : extension support (fun a => v (support a)) 39=v 39 :=
    extend_at support support_injective (fun a => v (support a)) 34
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h351 : extension support (fun a => v (support a)) 351=v 351 :=
    extend_at support support_injective (fun a => v (support a)) 126
  have h429 : extension support (fun a => v (support a)) 429=v 429 :=
    extend_at support support_injective (fun a => v (support a)) 195
  have h507 : extension support (fun a => v (support a)) 507=v 507 :=
    extend_at support support_injective (fun a => v (support a)) 217
  have h663 : extension support (fun a => v (support a)) 663=v 663 :=
    extend_at support support_injective (fun a => v (support a)) 251
  have h741 : extension support (fun a => v (support a)) 741=v 741 :=
    extend_at support support_injective (fun a => v (support a)) 287
  simp only [show gridEntireQ 7=20 from rfl,gridSample,show residues 20=({1,3,7,9,11,13,17,19}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h39,h117,h273,h351,h429,h507,h663,h741]

theorem entireSource_restrict_8 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 8) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 8) 0 v := by
  have h26 : extension support (fun a => v (support a)) 26=v 26 :=
    extend_at support support_injective (fun a => v (support a)) 24
  have h182 : extension support (fun a => v (support a)) 182=v 182 :=
    extend_at support support_injective (fun a => v (support a)) 85
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h338 : extension support (fun a => v (support a)) 338=v 338 :=
    extend_at support support_injective (fun a => v (support a)) 120
  have h442 : extension support (fun a => v (support a)) 442=v 442 :=
    extend_at support support_injective (fun a => v (support a)) 201
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  have h598 : extension support (fun a => v (support a)) 598=v 598 :=
    extend_at support support_injective (fun a => v (support a)) 236
  have h754 : extension support (fun a => v (support a)) 754=v 754 :=
    extend_at support support_injective (fun a => v (support a)) 297
  simp only [show gridEntireQ 8=30 from rfl,gridSample,show residues 30=({1,7,11,13,17,19,23,29}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h26,h182,h286,h338,h442,h494,h598,h754]

theorem entireSource_restrict_9 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 9) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 9) 0 v := by
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h400 : extension support (fun a => v (support a)) 400=v 400 :=
    extend_at support support_injective (fun a => v (support a)) 170
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [show gridEntireQ 9=39 from rfl,gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h20,h40,h80,h100,h140,h160,h200,h220,h280,h320,h340,h380,h400,h440,h460,h500,h560,h580,h620,h640,h680,h700,h740,h760]

theorem entireSource_restrict_10 (v : Fin 780→ℂ) :
    gridSample (gridEntireQ 10) 0 (extension support (fun j => v (support j)))=
      gridSample (gridEntireQ 10) 0 v := by
  have h10 : extension support (fun a => v (support a)) 10=v 10 :=
    extend_at support support_injective (fun a => v (support a)) 10
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  have h770 : extension support (fun a => v (support a)) 770=v 770 :=
    extend_at support support_injective (fun a => v (support a)) 311
  simp only [show gridEntireQ 10=78 from rfl,gridSample,show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]
  norm_num [gridIndex,Finset.sum_range_succ,h10,h50,h70,h110,h170,h190,h230,h250,h290,h310,h350,h370,h410,h430,h470,h490,h530,h550,h590,h610,h670,h710,h730,h770]

theorem heckeSource_restrict_0 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 0=
      gridHeckeLeading m f s v 0 := by
  have h7 : extension support (fun a => v (support a)) 7=v 7 :=
    extend_at support support_injective (fun a => v (support a)) 7
  have h14 : extension support (fun a => v (support a)) 14=v 14 :=
    extend_at support support_injective (fun a => v (support a)) 14
  have h397 : extension support (fun a => v (support a)) 397=v 397 :=
    extend_at support support_injective (fun a => v (support a)) 167
  simp only [gridHeckeLeading,show gridHeckeP 0=2 from rfl,show gridHeckeT 0=(7:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h7,h14,h397]

theorem heckeSource_restrict_1 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 1=
      gridHeckeLeading m f s v 1 := by
  have h8 : extension support (fun a => v (support a)) 8=v 8 :=
    extend_at support support_injective (fun a => v (support a)) 8
  have h16 : extension support (fun a => v (support a)) 16=v 16 :=
    extend_at support support_injective (fun a => v (support a)) 16
  have h398 : extension support (fun a => v (support a)) 398=v 398 :=
    extend_at support support_injective (fun a => v (support a)) 168
  simp only [gridHeckeLeading,show gridHeckeP 1=2 from rfl,show gridHeckeT 1=(8:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h8,h16,h398]

theorem heckeSource_restrict_2 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 2=
      gridHeckeLeading m f s v 2 := by
  have h9 : extension support (fun a => v (support a)) 9=v 9 :=
    extend_at support support_injective (fun a => v (support a)) 9
  have h18 : extension support (fun a => v (support a)) 18=v 18 :=
    extend_at support support_injective (fun a => v (support a)) 17
  have h399 : extension support (fun a => v (support a)) 399=v 399 :=
    extend_at support support_injective (fun a => v (support a)) 169
  simp only [gridHeckeLeading,show gridHeckeP 2=2 from rfl,show gridHeckeT 2=(9:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h9,h18,h399]

theorem heckeSource_restrict_3 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 3=
      gridHeckeLeading m f s v 3 := by
  have h11 : extension support (fun a => v (support a)) 11=v 11 :=
    extend_at support support_injective (fun a => v (support a)) 11
  have h22 : extension support (fun a => v (support a)) 22=v 22 :=
    extend_at support support_injective (fun a => v (support a)) 21
  have h401 : extension support (fun a => v (support a)) 401=v 401 :=
    extend_at support support_injective (fun a => v (support a)) 171
  simp only [gridHeckeLeading,show gridHeckeP 3=2 from rfl,show gridHeckeT 3=(11:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h11,h22,h401]

theorem heckeSource_restrict_4 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 4=
      gridHeckeLeading m f s v 4 := by
  have h22 : extension support (fun a => v (support a)) 22=v 22 :=
    extend_at support support_injective (fun a => v (support a)) 21
  have h44 : extension support (fun a => v (support a)) 44=v 44 :=
    extend_at support support_injective (fun a => v (support a)) 37
  have h412 : extension support (fun a => v (support a)) 412=v 412 :=
    extend_at support support_injective (fun a => v (support a)) 180
  simp only [gridHeckeLeading,show gridHeckeP 4=2 from rfl,show gridHeckeT 4=(22:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h22,h44,h412]

theorem heckeSource_restrict_5 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 5=
      gridHeckeLeading m f s v 5 := by
  have h42 : extension support (fun a => v (support a)) 42=v 42 :=
    extend_at support support_injective (fun a => v (support a)) 36
  have h84 : extension support (fun a => v (support a)) 84=v 84 :=
    extend_at support support_injective (fun a => v (support a)) 62
  have h432 : extension support (fun a => v (support a)) 432=v 432 :=
    extend_at support support_injective (fun a => v (support a)) 197
  simp only [gridHeckeLeading,show gridHeckeP 5=2 from rfl,show gridHeckeT 5=(42:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h42,h84,h432]

theorem heckeSource_restrict_6 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 6=
      gridHeckeLeading m f s v 6 := by
  have h52 : extension support (fun a => v (support a)) 52=v 52 :=
    extend_at support support_injective (fun a => v (support a)) 42
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h442 : extension support (fun a => v (support a)) 442=v 442 :=
    extend_at support support_injective (fun a => v (support a)) 201
  simp only [gridHeckeLeading,show gridHeckeP 6=2 from rfl,show gridHeckeT 6=(52:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h52,h104,h442]

theorem heckeSource_restrict_7 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 7=
      gridHeckeLeading m f s v 7 := by
  have h55 : extension support (fun a => v (support a)) 55=v 55 :=
    extend_at support support_injective (fun a => v (support a)) 44
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h445 : extension support (fun a => v (support a)) 445=v 445 :=
    extend_at support support_injective (fun a => v (support a)) 202
  simp only [gridHeckeLeading,show gridHeckeP 7=2 from rfl,show gridHeckeT 7=(55:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h55,h110,h445]

theorem heckeSource_restrict_8 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 8=
      gridHeckeLeading m f s v 8 := by
  have h66 : extension support (fun a => v (support a)) 66=v 66 :=
    extend_at support support_injective (fun a => v (support a)) 55
  have h132 : extension support (fun a => v (support a)) 132=v 132 :=
    extend_at support support_injective (fun a => v (support a)) 74
  have h456 : extension support (fun a => v (support a)) 456=v 456 :=
    extend_at support support_injective (fun a => v (support a)) 206
  simp only [gridHeckeLeading,show gridHeckeP 8=2 from rfl,show gridHeckeT 8=(66:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h66,h132,h456]

theorem heckeSource_restrict_9 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 9=
      gridHeckeLeading m f s v 9 := by
  have h95 : extension support (fun a => v (support a)) 95=v 95 :=
    extend_at support support_injective (fun a => v (support a)) 64
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h485 : extension support (fun a => v (support a)) 485=v 485 :=
    extend_at support support_injective (fun a => v (support a)) 212
  simp only [gridHeckeLeading,show gridHeckeP 9=2 from rfl,show gridHeckeT 9=(95:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h95,h190,h485]

theorem heckeSource_restrict_10 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 10=
      gridHeckeLeading m f s v 10 := by
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  simp only [gridHeckeLeading,show gridHeckeP 10=2 from rfl,show gridHeckeT 10=(100:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h100,h200,h490]

theorem heckeSource_restrict_11 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 11=
      gridHeckeLeading m f s v 11 := by
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  simp only [gridHeckeLeading,show gridHeckeP 11=2 from rfl,show gridHeckeT 11=(104:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h104,h208,h494]

theorem heckeSource_restrict_12 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 12=
      gridHeckeLeading m f s v 12 := by
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h495 : extension support (fun a => v (support a)) 495=v 495 :=
    extend_at support support_injective (fun a => v (support a)) 215
  simp only [gridHeckeLeading,show gridHeckeP 12=2 from rfl,show gridHeckeT 12=(105:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h105,h210,h495]

theorem heckeSource_restrict_13 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 13=
      gridHeckeLeading m f s v 13 := by
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  simp only [gridHeckeLeading,show gridHeckeP 13=2 from rfl,show gridHeckeT 13=(110:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h110,h220,h500]

theorem heckeSource_restrict_14 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 14=
      gridHeckeLeading m f s v 14 := by
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  simp only [gridHeckeLeading,show gridHeckeP 14=2 from rfl,show gridHeckeT 14=(140:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h140,h280,h530]

theorem heckeSource_restrict_15 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 15=
      gridHeckeLeading m f s v 15 := by
  have h143 : extension support (fun a => v (support a)) 143=v 143 :=
    extend_at support support_injective (fun a => v (support a)) 76
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h533 : extension support (fun a => v (support a)) 533=v 533 :=
    extend_at support support_injective (fun a => v (support a)) 221
  simp only [gridHeckeLeading,show gridHeckeP 15=2 from rfl,show gridHeckeT 15=(143:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h143,h286,h533]

theorem heckeSource_restrict_16 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 16=
      gridHeckeLeading m f s v 16 := by
  have h162 : extension support (fun a => v (support a)) 162=v 162 :=
    extend_at support support_injective (fun a => v (support a)) 81
  have h324 : extension support (fun a => v (support a)) 324=v 324 :=
    extend_at support support_injective (fun a => v (support a)) 115
  have h552 : extension support (fun a => v (support a)) 552=v 552 :=
    extend_at support support_injective (fun a => v (support a)) 226
  simp only [gridHeckeLeading,show gridHeckeP 16=2 from rfl,show gridHeckeT 16=(162:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h162,h324,h552]

theorem heckeSource_restrict_17 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 17=
      gridHeckeLeading m f s v 17 := by
  have h185 : extension support (fun a => v (support a)) 185=v 185 :=
    extend_at support support_injective (fun a => v (support a)) 86
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h575 : extension support (fun a => v (support a)) 575=v 575 :=
    extend_at support support_injective (fun a => v (support a)) 231
  simp only [gridHeckeLeading,show gridHeckeP 17=2 from rfl,show gridHeckeT 17=(185:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h185,h370,h575]

theorem heckeSource_restrict_18 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 18=
      gridHeckeLeading m f s v 18 := by
  have h205 : extension support (fun a => v (support a)) 205=v 205 :=
    extend_at support support_injective (fun a => v (support a)) 90
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h595 : extension support (fun a => v (support a)) 595=v 595 :=
    extend_at support support_injective (fun a => v (support a)) 235
  simp only [gridHeckeLeading,show gridHeckeP 18=2 from rfl,show gridHeckeT 18=(205:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h205,h410,h595]

theorem heckeSource_restrict_19 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 19=
      gridHeckeLeading m f s v 19 := by
  have h225 : extension support (fun a => v (support a)) 225=v 225 :=
    extend_at support support_injective (fun a => v (support a)) 94
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h615 : extension support (fun a => v (support a)) 615=v 615 :=
    extend_at support support_injective (fun a => v (support a)) 239
  simp only [gridHeckeLeading,show gridHeckeP 19=2 from rfl,show gridHeckeT 19=(225:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h225,h450,h615]

theorem heckeSource_restrict_20 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 20=
      gridHeckeLeading m f s v 20 := by
  have h228 : extension support (fun a => v (support a)) 228=v 228 :=
    extend_at support support_injective (fun a => v (support a)) 95
  have h456 : extension support (fun a => v (support a)) 456=v 456 :=
    extend_at support support_injective (fun a => v (support a)) 206
  have h618 : extension support (fun a => v (support a)) 618=v 618 :=
    extend_at support support_injective (fun a => v (support a)) 240
  simp only [gridHeckeLeading,show gridHeckeP 20=2 from rfl,show gridHeckeT 20=(228:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h228,h456,h618]

theorem heckeSource_restrict_21 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 21=
      gridHeckeLeading m f s v 21 := by
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  simp only [gridHeckeLeading,show gridHeckeP 21=2 from rfl,show gridHeckeT 21=(250:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h250,h500,h640]

theorem heckeSource_restrict_22 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 22=
      gridHeckeLeading m f s v 22 := by
  have h295 : extension support (fun a => v (support a)) 295=v 295 :=
    extend_at support support_injective (fun a => v (support a)) 109
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h685 : extension support (fun a => v (support a)) 685=v 685 :=
    extend_at support support_injective (fun a => v (support a)) 257
  simp only [gridHeckeLeading,show gridHeckeP 22=2 from rfl,show gridHeckeT 22=(295:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h295,h590,h685]

theorem heckeSource_restrict_23 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 23=
      gridHeckeLeading m f s v 23 := by
  have h368 : extension support (fun a => v (support a)) 368=v 368 :=
    extend_at support support_injective (fun a => v (support a)) 141
  have h736 : extension support (fun a => v (support a)) 736=v 736 :=
    extend_at support support_injective (fun a => v (support a)) 284
  have h758 : extension support (fun a => v (support a)) 758=v 758 :=
    extend_at support support_injective (fun a => v (support a)) 300
  simp only [gridHeckeLeading,show gridHeckeP 23=2 from rfl,show gridHeckeT 23=(368:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h368,h736,h758]

theorem heckeSource_restrict_24 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 24=
      gridHeckeLeading m f s v 24 := by
  have h13 : extension support (fun a => v (support a)) 13=v 13 :=
    extend_at support support_injective (fun a => v (support a)) 13
  have h39 : extension support (fun a => v (support a)) 39=v 39 :=
    extend_at support support_injective (fun a => v (support a)) 34
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h533 : extension support (fun a => v (support a)) 533=v 533 :=
    extend_at support support_injective (fun a => v (support a)) 221
  simp only [gridHeckeLeading,show gridHeckeP 24=3 from rfl,show gridHeckeT 24=(13:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h13,h39,h117,h273,h533]

theorem heckeSource_restrict_25 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 25=
      gridHeckeLeading m f s v 25 := by
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h60 : extension support (fun a => v (support a)) 60=v 60 :=
    extend_at support support_injective (fun a => v (support a)) 49
  have h180 : extension support (fun a => v (support a)) 180=v 180 :=
    extend_at support support_injective (fun a => v (support a)) 84
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h540 : extension support (fun a => v (support a)) 540=v 540 :=
    extend_at support support_injective (fun a => v (support a)) 222
  simp only [gridHeckeLeading,show gridHeckeP 25=3 from rfl,show gridHeckeT 25=(20:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h20,h60,h180,h280,h540]

theorem heckeSource_restrict_26 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 26=
      gridHeckeLeading m f s v 26 := by
  have h25 : extension support (fun a => v (support a)) 25=v 25 :=
    extend_at support support_injective (fun a => v (support a)) 23
  have h75 : extension support (fun a => v (support a)) 75=v 75 :=
    extend_at support support_injective (fun a => v (support a)) 59
  have h225 : extension support (fun a => v (support a)) 225=v 225 :=
    extend_at support support_injective (fun a => v (support a)) 94
  have h285 : extension support (fun a => v (support a)) 285=v 285 :=
    extend_at support support_injective (fun a => v (support a)) 106
  have h545 : extension support (fun a => v (support a)) 545=v 545 :=
    extend_at support support_injective (fun a => v (support a)) 223
  simp only [gridHeckeLeading,show gridHeckeP 26=3 from rfl,show gridHeckeT 26=(25:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h25,h75,h225,h285,h545]

theorem heckeSource_restrict_27 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 27=
      gridHeckeLeading m f s v 27 := by
  have h26 : extension support (fun a => v (support a)) 26=v 26 :=
    extend_at support support_injective (fun a => v (support a)) 24
  have h78 : extension support (fun a => v (support a)) 78=v 78 :=
    extend_at support support_injective (fun a => v (support a)) 60
  have h234 : extension support (fun a => v (support a)) 234=v 234 :=
    extend_at support support_injective (fun a => v (support a)) 97
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h546 : extension support (fun a => v (support a)) 546=v 546 :=
    extend_at support support_injective (fun a => v (support a)) 224
  simp only [gridHeckeLeading,show gridHeckeP 27=3 from rfl,show gridHeckeT 27=(26:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h26,h78,h234,h286,h546]

theorem heckeSource_restrict_28 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 28=
      gridHeckeLeading m f s v 28 := by
  have h35 : extension support (fun a => v (support a)) 35=v 35 :=
    extend_at support support_injective (fun a => v (support a)) 32
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h295 : extension support (fun a => v (support a)) 295=v 295 :=
    extend_at support support_injective (fun a => v (support a)) 109
  have h315 : extension support (fun a => v (support a)) 315=v 315 :=
    extend_at support support_injective (fun a => v (support a)) 113
  have h555 : extension support (fun a => v (support a)) 555=v 555 :=
    extend_at support support_injective (fun a => v (support a)) 227
  simp only [gridHeckeLeading,show gridHeckeP 28=3 from rfl,show gridHeckeT 28=(35:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h35,h105,h295,h315,h555]

theorem heckeSource_restrict_29 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 29=
      gridHeckeLeading m f s v 29 := by
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h120 : extension support (fun a => v (support a)) 120=v 120 :=
    extend_at support support_injective (fun a => v (support a)) 71
  have h300 : extension support (fun a => v (support a)) 300=v 300 :=
    extend_at support support_injective (fun a => v (support a)) 110
  have h360 : extension support (fun a => v (support a)) 360=v 360 :=
    extend_at support support_injective (fun a => v (support a)) 134
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  simp only [gridHeckeLeading,show gridHeckeP 29=3 from rfl,show gridHeckeT 29=(40:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h40,h120,h300,h360,h560]

theorem heckeSource_restrict_30 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 30=
      gridHeckeLeading m f s v 30 := by
  have h55 : extension support (fun a => v (support a)) 55=v 55 :=
    extend_at support support_injective (fun a => v (support a)) 44
  have h165 : extension support (fun a => v (support a)) 165=v 165 :=
    extend_at support support_injective (fun a => v (support a)) 82
  have h315 : extension support (fun a => v (support a)) 315=v 315 :=
    extend_at support support_injective (fun a => v (support a)) 113
  have h495 : extension support (fun a => v (support a)) 495=v 495 :=
    extend_at support support_injective (fun a => v (support a)) 215
  have h575 : extension support (fun a => v (support a)) 575=v 575 :=
    extend_at support support_injective (fun a => v (support a)) 231
  simp only [gridHeckeLeading,show gridHeckeP 30=3 from rfl,show gridHeckeT 30=(55:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h55,h165,h315,h495,h575]

theorem heckeSource_restrict_31 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 31=
      gridHeckeLeading m f s v 31 := by
  have h65 : extension support (fun a => v (support a)) 65=v 65 :=
    extend_at support support_injective (fun a => v (support a)) 54
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h325 : extension support (fun a => v (support a)) 325=v 325 :=
    extend_at support support_injective (fun a => v (support a)) 116
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  simp only [gridHeckeLeading,show gridHeckeP 31=3 from rfl,show gridHeckeT 31=(65:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h65,h195,h325,h585]

theorem heckeSource_restrict_32 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 32=
      gridHeckeLeading m f s v 32 := by
  have h75 : extension support (fun a => v (support a)) 75=v 75 :=
    extend_at support support_injective (fun a => v (support a)) 59
  have h225 : extension support (fun a => v (support a)) 225=v 225 :=
    extend_at support support_injective (fun a => v (support a)) 94
  have h335 : extension support (fun a => v (support a)) 335=v 335 :=
    extend_at support support_injective (fun a => v (support a)) 119
  have h595 : extension support (fun a => v (support a)) 595=v 595 :=
    extend_at support support_injective (fun a => v (support a)) 235
  have h675 : extension support (fun a => v (support a)) 675=v 675 :=
    extend_at support support_injective (fun a => v (support a)) 253
  simp only [gridHeckeLeading,show gridHeckeP 32=3 from rfl,show gridHeckeT 32=(75:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h75,h225,h335,h595,h675]

theorem heckeSource_restrict_33 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 33=
      gridHeckeLeading m f s v 33 := by
  have h75 : extension support (fun a => v (support a)) 75=v 75 :=
    extend_at support support_injective (fun a => v (support a)) 59
  have h95 : extension support (fun a => v (support a)) 95=v 95 :=
    extend_at support support_injective (fun a => v (support a)) 64
  have h285 : extension support (fun a => v (support a)) 285=v 285 :=
    extend_at support support_injective (fun a => v (support a)) 106
  have h355 : extension support (fun a => v (support a)) 355=v 355 :=
    extend_at support support_injective (fun a => v (support a)) 129
  have h615 : extension support (fun a => v (support a)) 615=v 615 :=
    extend_at support support_injective (fun a => v (support a)) 239
  simp only [gridHeckeLeading,show gridHeckeP 33=3 from rfl,show gridHeckeT 33=(95:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h75,h95,h285,h355,h615]

theorem heckeSource_restrict_34 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 34=
      gridHeckeLeading m f s v 34 := by
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h210 : extension support (fun a => v (support a)) 210=v 210 :=
    extend_at support support_injective (fun a => v (support a)) 92
  have h330 : extension support (fun a => v (support a)) 330=v 330 :=
    extend_at support support_injective (fun a => v (support a)) 118
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h630 : extension support (fun a => v (support a)) 630=v 630 :=
    extend_at support support_injective (fun a => v (support a)) 244
  simp only [gridHeckeLeading,show gridHeckeP 34=3 from rfl,show gridHeckeT 34=(110:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h110,h210,h330,h370,h630]

theorem heckeSource_restrict_35 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 35=
      gridHeckeLeading m f s v 35 := by
  have h150 : extension support (fun a => v (support a)) 150=v 150 :=
    extend_at support support_injective (fun a => v (support a)) 77
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h450 : extension support (fun a => v (support a)) 450=v 450 :=
    extend_at support support_injective (fun a => v (support a)) 203
  have h570 : extension support (fun a => v (support a)) 570=v 570 :=
    extend_at support support_injective (fun a => v (support a)) 229
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  simp only [gridHeckeLeading,show gridHeckeP 35=3 from rfl,show gridHeckeT 35=(150:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h150,h410,h450,h570,h670]

theorem heckeSource_restrict_36 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 36=
      gridHeckeLeading m f s v 36 := by
  have h105 : extension support (fun a => v (support a)) 105=v 105 :=
    extend_at support support_injective (fun a => v (support a)) 68
  have h185 : extension support (fun a => v (support a)) 185=v 185 :=
    extend_at support support_injective (fun a => v (support a)) 86
  have h445 : extension support (fun a => v (support a)) 445=v 445 :=
    extend_at support support_injective (fun a => v (support a)) 202
  have h555 : extension support (fun a => v (support a)) 555=v 555 :=
    extend_at support support_injective (fun a => v (support a)) 227
  have h705 : extension support (fun a => v (support a)) 705=v 705 :=
    extend_at support support_injective (fun a => v (support a)) 262
  simp only [gridHeckeLeading,show gridHeckeP 36=3 from rfl,show gridHeckeT 36=(185:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h105,h185,h445,h555,h705]

theorem heckeSource_restrict_37 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 37=
      gridHeckeLeading m f s v 37 := by
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h455 : extension support (fun a => v (support a)) 455=v 455 :=
    extend_at support support_injective (fun a => v (support a)) 205
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  have h715 : extension support (fun a => v (support a)) 715=v 715 :=
    extend_at support support_injective (fun a => v (support a)) 267
  simp only [gridHeckeLeading,show gridHeckeP 37=3 from rfl,show gridHeckeT 37=(195:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h195,h455,h585,h715]

theorem heckeSource_restrict_38 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 38=
      gridHeckeLeading m f s v 38 := by
  have h205 : extension support (fun a => v (support a)) 205=v 205 :=
    extend_at support support_injective (fun a => v (support a)) 90
  have h285 : extension support (fun a => v (support a)) 285=v 285 :=
    extend_at support support_injective (fun a => v (support a)) 106
  have h465 : extension support (fun a => v (support a)) 465=v 465 :=
    extend_at support support_injective (fun a => v (support a)) 208
  have h615 : extension support (fun a => v (support a)) 615=v 615 :=
    extend_at support support_injective (fun a => v (support a)) 239
  have h725 : extension support (fun a => v (support a)) 725=v 725 :=
    extend_at support support_injective (fun a => v (support a)) 277
  simp only [gridHeckeLeading,show gridHeckeP 38=3 from rfl,show gridHeckeT 38=(205:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h205,h285,h465,h615,h725]

theorem heckeSource_restrict_39 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 39=
      gridHeckeLeading m f s v 39 := by
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h420 : extension support (fun a => v (support a)) 420=v 420 :=
    extend_at support support_injective (fun a => v (support a)) 187
  have h480 : extension support (fun a => v (support a)) 480=v 480 :=
    extend_at support support_injective (fun a => v (support a)) 211
  have h660 : extension support (fun a => v (support a)) 660=v 660 :=
    extend_at support support_injective (fun a => v (support a)) 250
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [gridHeckeLeading,show gridHeckeP 39=3 from rfl,show gridHeckeT 39=(220:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h220,h420,h480,h660,h740]

theorem heckeSource_restrict_40 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 40=
      gridHeckeLeading m f s v 40 := by
  have h240 : extension support (fun a => v (support a)) 240=v 240 :=
    extend_at support support_injective (fun a => v (support a)) 99
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h600 : extension support (fun a => v (support a)) 600=v 600 :=
    extend_at support support_injective (fun a => v (support a)) 237
  have h720 : extension support (fun a => v (support a)) 720=v 720 :=
    extend_at support support_injective (fun a => v (support a)) 272
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [gridHeckeLeading,show gridHeckeP 40=3 from rfl,show gridHeckeT 40=(240:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h240,h500,h600,h720,h760]

theorem heckeSource_restrict_41 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 41=
      gridHeckeLeading m f s v 41 := by
  have h26 : extension support (fun a => v (support a)) 26=v 26 :=
    extend_at support support_injective (fun a => v (support a)) 24
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h182 : extension support (fun a => v (support a)) 182=v 182 :=
    extend_at support support_injective (fun a => v (support a)) 85
  have h338 : extension support (fun a => v (support a)) 338=v 338 :=
    extend_at support support_injective (fun a => v (support a)) 120
  have h494 : extension support (fun a => v (support a)) 494=v 494 :=
    extend_at support support_injective (fun a => v (support a)) 214
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  simp only [gridHeckeLeading,show gridHeckeP 41=5 from rfl,show gridHeckeT 41=(26:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h26,h130,h182,h338,h494,h650]

theorem heckeSource_restrict_42 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 42=
      gridHeckeLeading m f s v 42 := by
  have h39 : extension support (fun a => v (support a)) 39=v 39 :=
    extend_at support support_injective (fun a => v (support a)) 34
  have h195 : extension support (fun a => v (support a)) 195=v 195 :=
    extend_at support support_injective (fun a => v (support a)) 88
  have h351 : extension support (fun a => v (support a)) 351=v 351 :=
    extend_at support support_injective (fun a => v (support a)) 126
  have h507 : extension support (fun a => v (support a)) 507=v 507 :=
    extend_at support support_injective (fun a => v (support a)) 217
  have h663 : extension support (fun a => v (support a)) 663=v 663 :=
    extend_at support support_injective (fun a => v (support a)) 251
  simp only [gridHeckeLeading,show gridHeckeP 42=5 from rfl,show gridHeckeT 42=(39:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h39,h195,h351,h507,h663]

theorem heckeSource_restrict_43 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 43=
      gridHeckeLeading m f s v 43 := by
  have h52 : extension support (fun a => v (support a)) 52=v 52 :=
    extend_at support support_injective (fun a => v (support a)) 42
  have h208 : extension support (fun a => v (support a)) 208=v 208 :=
    extend_at support support_injective (fun a => v (support a)) 91
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h364 : extension support (fun a => v (support a)) 364=v 364 :=
    extend_at support support_injective (fun a => v (support a)) 138
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h676 : extension support (fun a => v (support a)) 676=v 676 :=
    extend_at support support_injective (fun a => v (support a)) 254
  simp only [gridHeckeLeading,show gridHeckeP 43=5 from rfl,show gridHeckeT 43=(52:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h52,h208,h260,h364,h520,h676]

theorem heckeSource_restrict_44 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 44=
      gridHeckeLeading m f s v 44 := by
  have h104 : extension support (fun a => v (support a)) 104=v 104 :=
    extend_at support support_injective (fun a => v (support a)) 67
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h416 : extension support (fun a => v (support a)) 416=v 416 :=
    extend_at support support_injective (fun a => v (support a)) 183
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h572 : extension support (fun a => v (support a)) 572=v 572 :=
    extend_at support support_injective (fun a => v (support a)) 230
  have h728 : extension support (fun a => v (support a)) 728=v 728 :=
    extend_at support support_injective (fun a => v (support a)) 279
  simp only [gridHeckeLeading,show gridHeckeP 44=5 from rfl,show gridHeckeT 44=(104:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h104,h260,h416,h520,h572,h728]

theorem heckeSource_restrict_45 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 45=
      gridHeckeLeading m f s v 45 := by
  have h117 : extension support (fun a => v (support a)) 117=v 117 :=
    extend_at support support_injective (fun a => v (support a)) 70
  have h273 : extension support (fun a => v (support a)) 273=v 273 :=
    extend_at support support_injective (fun a => v (support a)) 104
  have h429 : extension support (fun a => v (support a)) 429=v 429 :=
    extend_at support support_injective (fun a => v (support a)) 195
  have h585 : extension support (fun a => v (support a)) 585=v 585 :=
    extend_at support support_injective (fun a => v (support a)) 233
  have h741 : extension support (fun a => v (support a)) 741=v 741 :=
    extend_at support support_injective (fun a => v (support a)) 287
  simp only [gridHeckeLeading,show gridHeckeP 45=5 from rfl,show gridHeckeT 45=(117:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h117,h273,h429,h585,h741]

theorem heckeSource_restrict_46 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 46=
      gridHeckeLeading m f s v 46 := by
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h286 : extension support (fun a => v (support a)) 286=v 286 :=
    extend_at support support_injective (fun a => v (support a)) 107
  have h442 : extension support (fun a => v (support a)) 442=v 442 :=
    extend_at support support_injective (fun a => v (support a)) 201
  have h598 : extension support (fun a => v (support a)) 598=v 598 :=
    extend_at support support_injective (fun a => v (support a)) 236
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  have h754 : extension support (fun a => v (support a)) 754=v 754 :=
    extend_at support support_injective (fun a => v (support a)) 297
  simp only [gridHeckeLeading,show gridHeckeP 46=5 from rfl,show gridHeckeT 46=(130:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h130,h286,h442,h598,h650,h754]

theorem heckeSource_restrict_47 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 47=
      gridHeckeLeading m f s v 47 := by
  have h10 : extension support (fun a => v (support a)) 10=v 10 :=
    extend_at support support_injective (fun a => v (support a)) 10
  have h70 : extension support (fun a => v (support a)) 70=v 70 :=
    extend_at support support_injective (fun a => v (support a)) 57
  have h130 : extension support (fun a => v (support a)) 130=v 130 :=
    extend_at support support_injective (fun a => v (support a)) 73
  have h190 : extension support (fun a => v (support a)) 190=v 190 :=
    extend_at support support_injective (fun a => v (support a)) 87
  have h250 : extension support (fun a => v (support a)) 250=v 250 :=
    extend_at support support_injective (fun a => v (support a)) 101
  have h310 : extension support (fun a => v (support a)) 310=v 310 :=
    extend_at support support_injective (fun a => v (support a)) 111
  have h370 : extension support (fun a => v (support a)) 370=v 370 :=
    extend_at support support_injective (fun a => v (support a)) 143
  have h430 : extension support (fun a => v (support a)) 430=v 430 :=
    extend_at support support_injective (fun a => v (support a)) 196
  have h490 : extension support (fun a => v (support a)) 490=v 490 :=
    extend_at support support_injective (fun a => v (support a)) 213
  have h550 : extension support (fun a => v (support a)) 550=v 550 :=
    extend_at support support_injective (fun a => v (support a)) 225
  have h610 : extension support (fun a => v (support a)) 610=v 610 :=
    extend_at support support_injective (fun a => v (support a)) 238
  have h670 : extension support (fun a => v (support a)) 670=v 670 :=
    extend_at support support_injective (fun a => v (support a)) 252
  have h730 : extension support (fun a => v (support a)) 730=v 730 :=
    extend_at support support_injective (fun a => v (support a)) 281
  simp only [gridHeckeLeading,show gridHeckeP 47=13 from rfl,show gridHeckeT 47=(10:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h10,h70,h130,h190,h250,h310,h370,h430,h490,h550,h610,h670,h730]

theorem heckeSource_restrict_48 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 48=
      gridHeckeLeading m f s v 48 := by
  have h20 : extension support (fun a => v (support a)) 20=v 20 :=
    extend_at support support_injective (fun a => v (support a)) 19
  have h80 : extension support (fun a => v (support a)) 80=v 80 :=
    extend_at support support_injective (fun a => v (support a)) 61
  have h140 : extension support (fun a => v (support a)) 140=v 140 :=
    extend_at support support_injective (fun a => v (support a)) 75
  have h200 : extension support (fun a => v (support a)) 200=v 200 :=
    extend_at support support_injective (fun a => v (support a)) 89
  have h260 : extension support (fun a => v (support a)) 260=v 260 :=
    extend_at support support_injective (fun a => v (support a)) 102
  have h320 : extension support (fun a => v (support a)) 320=v 320 :=
    extend_at support support_injective (fun a => v (support a)) 114
  have h380 : extension support (fun a => v (support a)) 380=v 380 :=
    extend_at support support_injective (fun a => v (support a)) 151
  have h440 : extension support (fun a => v (support a)) 440=v 440 :=
    extend_at support support_injective (fun a => v (support a)) 200
  have h500 : extension support (fun a => v (support a)) 500=v 500 :=
    extend_at support support_injective (fun a => v (support a)) 216
  have h560 : extension support (fun a => v (support a)) 560=v 560 :=
    extend_at support support_injective (fun a => v (support a)) 228
  have h620 : extension support (fun a => v (support a)) 620=v 620 :=
    extend_at support support_injective (fun a => v (support a)) 241
  have h680 : extension support (fun a => v (support a)) 680=v 680 :=
    extend_at support support_injective (fun a => v (support a)) 255
  have h740 : extension support (fun a => v (support a)) 740=v 740 :=
    extend_at support support_injective (fun a => v (support a)) 286
  simp only [gridHeckeLeading,show gridHeckeP 48=13 from rfl,show gridHeckeT 48=(20:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h20,h80,h140,h200,h260,h320,h380,h440,h500,h560,h620,h680,h740]

theorem heckeSource_restrict_49 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 49=
      gridHeckeLeading m f s v 49 := by
  have h40 : extension support (fun a => v (support a)) 40=v 40 :=
    extend_at support support_injective (fun a => v (support a)) 35
  have h100 : extension support (fun a => v (support a)) 100=v 100 :=
    extend_at support support_injective (fun a => v (support a)) 66
  have h160 : extension support (fun a => v (support a)) 160=v 160 :=
    extend_at support support_injective (fun a => v (support a)) 80
  have h220 : extension support (fun a => v (support a)) 220=v 220 :=
    extend_at support support_injective (fun a => v (support a)) 93
  have h280 : extension support (fun a => v (support a)) 280=v 280 :=
    extend_at support support_injective (fun a => v (support a)) 105
  have h340 : extension support (fun a => v (support a)) 340=v 340 :=
    extend_at support support_injective (fun a => v (support a)) 121
  have h400 : extension support (fun a => v (support a)) 400=v 400 :=
    extend_at support support_injective (fun a => v (support a)) 170
  have h460 : extension support (fun a => v (support a)) 460=v 460 :=
    extend_at support support_injective (fun a => v (support a)) 207
  have h520 : extension support (fun a => v (support a)) 520=v 520 :=
    extend_at support support_injective (fun a => v (support a)) 219
  have h580 : extension support (fun a => v (support a)) 580=v 580 :=
    extend_at support support_injective (fun a => v (support a)) 232
  have h640 : extension support (fun a => v (support a)) 640=v 640 :=
    extend_at support support_injective (fun a => v (support a)) 246
  have h700 : extension support (fun a => v (support a)) 700=v 700 :=
    extend_at support support_injective (fun a => v (support a)) 260
  have h760 : extension support (fun a => v (support a)) 760=v 760 :=
    extend_at support support_injective (fun a => v (support a)) 302
  simp only [gridHeckeLeading,show gridHeckeP 49=13 from rfl,show gridHeckeT 49=(40:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h40,h100,h160,h220,h280,h340,h400,h460,h520,h580,h640,h700,h760]

theorem heckeSource_restrict_50 (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (v : Fin 780→ℂ) :
    gridHeckeLeading m f s (extension support (fun j => v (support j))) 50=
      gridHeckeLeading m f s v 50 := by
  have h50 : extension support (fun a => v (support a)) 50=v 50 :=
    extend_at support support_injective (fun a => v (support a)) 40
  have h110 : extension support (fun a => v (support a)) 110=v 110 :=
    extend_at support support_injective (fun a => v (support a)) 69
  have h170 : extension support (fun a => v (support a)) 170=v 170 :=
    extend_at support support_injective (fun a => v (support a)) 83
  have h230 : extension support (fun a => v (support a)) 230=v 230 :=
    extend_at support support_injective (fun a => v (support a)) 96
  have h290 : extension support (fun a => v (support a)) 290=v 290 :=
    extend_at support support_injective (fun a => v (support a)) 108
  have h350 : extension support (fun a => v (support a)) 350=v 350 :=
    extend_at support support_injective (fun a => v (support a)) 125
  have h410 : extension support (fun a => v (support a)) 410=v 410 :=
    extend_at support support_injective (fun a => v (support a)) 178
  have h470 : extension support (fun a => v (support a)) 470=v 470 :=
    extend_at support support_injective (fun a => v (support a)) 210
  have h530 : extension support (fun a => v (support a)) 530=v 530 :=
    extend_at support support_injective (fun a => v (support a)) 220
  have h590 : extension support (fun a => v (support a)) 590=v 590 :=
    extend_at support support_injective (fun a => v (support a)) 234
  have h650 : extension support (fun a => v (support a)) 650=v 650 :=
    extend_at support support_injective (fun a => v (support a)) 248
  have h710 : extension support (fun a => v (support a)) 710=v 710 :=
    extend_at support support_injective (fun a => v (support a)) 264
  have h770 : extension support (fun a => v (support a)) 770=v 770 :=
    extend_at support support_injective (fun a => v (support a)) 311
  simp only [gridHeckeLeading,show gridHeckeP 50=13 from rfl,show gridHeckeT 50=(50:ℤ) from rfl]
  norm_num [gridIndex,Finset.sum_range_succ,h50,h110,h170,h230,h290,h350,h410,h470,h530,h590,h650,h710,h770]

end SmallLevelTwentySixGrid
