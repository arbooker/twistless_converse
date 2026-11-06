module
public import SmallLevelTwentySixGridShiftSupportDataV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGrid
open SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM FinitenessRamanujanSum

theorem taylorTarget_restrict_0 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 0) (gridTaylorPartner 0) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 0) (gridTaylorPartner 0) v := by
  have h280 : extension support (fun t => v (support t)) 280=v 280 :=
    extend_at support support_injective (fun t => v (support t)) 105
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  simp only [show gridTaylorQ 0=3 from rfl,show gridTaylorPartner 0=(20:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h280,h540]

theorem taylorTarget_restrict_1 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 1) (gridTaylorPartner 1) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 1) (gridTaylorPartner 1) v := by
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h560 : extension support (fun t => v (support t)) 560=v 560 :=
    extend_at support support_injective (fun t => v (support t)) 228
  simp only [show gridTaylorQ 1=3 from rfl,show gridTaylorPartner 1=(40:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h300,h560]

theorem taylorTarget_restrict_2 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 2) (gridTaylorPartner 2) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 2) (gridTaylorPartner 2) v := by
  have h312 : extension support (fun t => v (support t)) 312=v 312 :=
    extend_at support support_injective (fun t => v (support t)) 112
  have h572 : extension support (fun t => v (support t)) 572=v 572 :=
    extend_at support support_injective (fun t => v (support t)) 230
  simp only [show gridTaylorQ 2=3 from rfl,show gridTaylorPartner 2=(52:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h312,h572]

theorem taylorTarget_restrict_3 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 3) (gridTaylorPartner 3) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 3) (gridTaylorPartner 3) v := by
  have h325 : extension support (fun t => v (support t)) 325=v 325 :=
    extend_at support support_injective (fun t => v (support t)) 116
  have h585 : extension support (fun t => v (support t)) 585=v 585 :=
    extend_at support support_injective (fun t => v (support t)) 233
  simp only [show gridTaylorQ 3=3 from rfl,show gridTaylorPartner 3=(65:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h325,h585]

theorem taylorTarget_restrict_4 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 4) (gridTaylorPartner 4) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 4) (gridTaylorPartner 4) v := by
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  simp only [show gridTaylorQ 4=3 from rfl,show gridTaylorPartner 4=(100:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h360,h620]

theorem taylorTarget_restrict_5 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 5) (gridTaylorPartner 5) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 5) (gridTaylorPartner 5) v := by
  have h364 : extension support (fun t => v (support t)) 364=v 364 :=
    extend_at support support_injective (fun t => v (support t)) 138
  have h624 : extension support (fun t => v (support t)) 624=v 624 :=
    extend_at support support_injective (fun t => v (support t)) 242
  simp only [show gridTaylorQ 5=3 from rfl,show gridTaylorPartner 5=(104:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h364,h624]

theorem taylorTarget_restrict_6 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 6) (gridTaylorPartner 6) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 6) (gridTaylorPartner 6) v := by
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  simp only [show gridTaylorQ 6=3 from rfl,show gridTaylorPartner 6=(130:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h390,h650]

theorem taylorTarget_restrict_7 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 7) (gridTaylorPartner 7) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 7) (gridTaylorPartner 7) v := by
  have h460 : extension support (fun t => v (support t)) 460=v 460 :=
    extend_at support support_injective (fun t => v (support t)) 207
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  simp only [show gridTaylorQ 7=3 from rfl,show gridTaylorPartner 7=(200:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h460,h720]

theorem taylorTarget_restrict_8 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 8) (gridTaylorPartner 8) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 8) (gridTaylorPartner 8) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 8=3 from rfl,show gridTaylorPartner 8=(260:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h520]

theorem taylorTarget_restrict_9 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 9) (gridTaylorPartner 9) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 9) (gridTaylorPartner 9) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  simp only [show gridTaylorQ 9=3 from rfl,show gridTaylorPartner 9=(-260:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260]

theorem taylorTarget_restrict_10 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 10) (gridTaylorPartner 10) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 10) (gridTaylorPartner 10) v := by
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h320 : extension support (fun t => v (support t)) 320=v 320 :=
    extend_at support support_injective (fun t => v (support t)) 114
  simp only [show gridTaylorQ 10=3 from rfl,show gridTaylorPartner 10=(-200:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h60,h320]

theorem taylorTarget_restrict_11 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 11) (gridTaylorPartner 11) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 11) (gridTaylorPartner 11) v := by
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 11=3 from rfl,show gridTaylorPartner 11=(-130:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h130,h390]

theorem taylorTarget_restrict_12 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 12) (gridTaylorPartner 12) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 12) (gridTaylorPartner 12) v := by
  have h156 : extension support (fun t => v (support t)) 156=v 156 :=
    extend_at support support_injective (fun t => v (support t)) 79
  have h416 : extension support (fun t => v (support t)) 416=v 416 :=
    extend_at support support_injective (fun t => v (support t)) 183
  simp only [show gridTaylorQ 12=3 from rfl,show gridTaylorPartner 12=(-104:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h156,h416]

theorem taylorTarget_restrict_13 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 13) (gridTaylorPartner 13) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 13) (gridTaylorPartner 13) v := by
  have h160 : extension support (fun t => v (support t)) 160=v 160 :=
    extend_at support support_injective (fun t => v (support t)) 80
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  simp only [show gridTaylorQ 13=3 from rfl,show gridTaylorPartner 13=(-100:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h160,h420]

theorem taylorTarget_restrict_14 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 14) (gridTaylorPartner 14) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 14) (gridTaylorPartner 14) v := by
  have h195 : extension support (fun t => v (support t)) 195=v 195 :=
    extend_at support support_injective (fun t => v (support t)) 88
  have h455 : extension support (fun t => v (support t)) 455=v 455 :=
    extend_at support support_injective (fun t => v (support t)) 205
  simp only [show gridTaylorQ 14=3 from rfl,show gridTaylorPartner 14=(-65:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h195,h455]

theorem taylorTarget_restrict_15 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 15) (gridTaylorPartner 15) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 15) (gridTaylorPartner 15) v := by
  have h208 : extension support (fun t => v (support t)) 208=v 208 :=
    extend_at support support_injective (fun t => v (support t)) 91
  have h468 : extension support (fun t => v (support t)) 468=v 468 :=
    extend_at support support_injective (fun t => v (support t)) 209
  simp only [show gridTaylorQ 15=3 from rfl,show gridTaylorPartner 15=(-52:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h208,h468]

theorem taylorTarget_restrict_16 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 16) (gridTaylorPartner 16) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 16) (gridTaylorPartner 16) v := by
  have h220 : extension support (fun t => v (support t)) 220=v 220 :=
    extend_at support support_injective (fun t => v (support t)) 93
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  simp only [show gridTaylorQ 16=3 from rfl,show gridTaylorPartner 16=(-40:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h220,h480]

theorem taylorTarget_restrict_17 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 17) (gridTaylorPartner 17) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 17) (gridTaylorPartner 17) v := by
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h500 : extension support (fun t => v (support t)) 500=v 500 :=
    extend_at support support_injective (fun t => v (support t)) 216
  simp only [show gridTaylorQ 17=3 from rfl,show gridTaylorPartner 17=(-20:ℤ) from rfl,
    gridSample,show residues 3=({1,2}:Finset ℕ) from by decide]
  norm_num [gridIndex,h240,h500]

theorem taylorTarget_restrict_18 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 18) (gridTaylorPartner 18) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 18) (gridTaylorPartner 18) v := by
  have h312 : extension support (fun t => v (support t)) 312=v 312 :=
    extend_at support support_injective (fun t => v (support t)) 112
  have h702 : extension support (fun t => v (support t)) 702=v 702 :=
    extend_at support support_injective (fun t => v (support t)) 261
  simp only [show gridTaylorQ 18=4 from rfl,show gridTaylorPartner 18=(117:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h312,h702]

theorem taylorTarget_restrict_19 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 19) (gridTaylorPartner 19) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 19) (gridTaylorPartner 19) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 19=4 from rfl,show gridTaylorPartner 19=(195:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h390]

theorem taylorTarget_restrict_20 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 20) (gridTaylorPartner 20) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 20) (gridTaylorPartner 20) v := by
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  simp only [show gridTaylorQ 20=4 from rfl,show gridTaylorPartner 20=(225:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h30,h420]

theorem taylorTarget_restrict_21 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 21) (gridTaylorPartner 21) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 21) (gridTaylorPartner 21) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 21=4 from rfl,show gridTaylorPartner 21=(585:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h390]

theorem taylorTarget_restrict_22 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 22) (gridTaylorPartner 22) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 22) (gridTaylorPartner 22) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 22=4 from rfl,show gridTaylorPartner 22=(-585:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h390]

theorem taylorTarget_restrict_23 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 23) (gridTaylorPartner 23) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 23) (gridTaylorPartner 23) v := by
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 23=4 from rfl,show gridTaylorPartner 23=(-225:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h360,h750]

theorem taylorTarget_restrict_24 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 24) (gridTaylorPartner 24) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 24) (gridTaylorPartner 24) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  simp only [show gridTaylorQ 24=4 from rfl,show gridTaylorPartner 24=(-195:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h390]

theorem taylorTarget_restrict_25 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 25) (gridTaylorPartner 25) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 25) (gridTaylorPartner 25) v := by
  have h78 : extension support (fun t => v (support t)) 78=v 78 :=
    extend_at support support_injective (fun t => v (support t)) 60
  have h468 : extension support (fun t => v (support t)) 468=v 468 :=
    extend_at support support_injective (fun t => v (support t)) 209
  simp only [show gridTaylorQ 25=4 from rfl,show gridTaylorPartner 25=(-117:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h78,h468]

theorem taylorTarget_restrict_26 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 26) (gridTaylorPartner 26) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 26) (gridTaylorPartner 26) v := by
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  simp only [show gridTaylorQ 26=4 from rfl,show gridTaylorPartner 26=(-75:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h120,h510]

theorem taylorTarget_restrict_27 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 27) (gridTaylorPartner 27) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 27) (gridTaylorPartner 27) v := by
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 27=4 from rfl,show gridTaylorPartner 27=(-65:ℤ) from rfl,
    gridSample,show residues 4=({1,3}:Finset ℕ) from by decide]
  norm_num [gridIndex,h130,h520]

theorem taylorTarget_restrict_28 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 28) (gridTaylorPartner 28) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 28) (gridTaylorPartner 28) v := by
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h700 : extension support (fun t => v (support t)) 700=v 700 :=
    extend_at support support_injective (fun t => v (support t)) 260
  simp only [show gridTaylorQ 28=6 from rfl,show gridTaylorPartner 28=(50:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h180,h700]

theorem taylorTarget_restrict_29 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 29) (gridTaylorPartner 29) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 29) (gridTaylorPartner 29) v := by
  have h182 : extension support (fun t => v (support t)) 182=v 182 :=
    extend_at support support_injective (fun t => v (support t)) 85
  have h702 : extension support (fun t => v (support t)) 702=v 702 :=
    extend_at support support_injective (fun t => v (support t)) 261
  simp only [show gridTaylorQ 29=6 from rfl,show gridTaylorPartner 29=(52:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h182,h702]

theorem taylorTarget_restrict_30 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 30) (gridTaylorPartner 30) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 30) (gridTaylorPartner 30) v := by
  have h195 : extension support (fun t => v (support t)) 195=v 195 :=
    extend_at support support_injective (fun t => v (support t)) 88
  have h715 : extension support (fun t => v (support t)) 715=v 715 :=
    extend_at support support_injective (fun t => v (support t)) 267
  simp only [show gridTaylorQ 30=6 from rfl,show gridTaylorPartner 30=(65:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h195,h715]

theorem taylorTarget_restrict_31 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 31) (gridTaylorPartner 31) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 31) (gridTaylorPartner 31) v := by
  have h230 : extension support (fun t => v (support t)) 230=v 230 :=
    extend_at support support_injective (fun t => v (support t)) 96
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 31=6 from rfl,show gridTaylorPartner 31=(100:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h230,h750]

theorem taylorTarget_restrict_32 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 32) (gridTaylorPartner 32) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 32) (gridTaylorPartner 32) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  simp only [show gridTaylorQ 32=6 from rfl,show gridTaylorPartner 32=(130:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260]

theorem taylorTarget_restrict_33 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 33) (gridTaylorPartner 33) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 33) (gridTaylorPartner 33) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 33=6 from rfl,show gridTaylorPartner 33=(650:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h520]

theorem taylorTarget_restrict_34 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 34) (gridTaylorPartner 34) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 34) (gridTaylorPartner 34) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  simp only [show gridTaylorQ 34=6 from rfl,show gridTaylorPartner 34=(-650:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260]

theorem taylorTarget_restrict_35 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 35) (gridTaylorPartner 35) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 35) (gridTaylorPartner 35) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 35=6 from rfl,show gridTaylorPartner 35=(-130:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h520]

theorem taylorTarget_restrict_36 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 36) (gridTaylorPartner 36) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 36) (gridTaylorPartner 36) v := by
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h550 : extension support (fun t => v (support t)) 550=v 550 :=
    extend_at support support_injective (fun t => v (support t)) 225
  simp only [show gridTaylorQ 36=6 from rfl,show gridTaylorPartner 36=(-100:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h30,h550]

theorem taylorTarget_restrict_37 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 37) (gridTaylorPartner 37) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 37) (gridTaylorPartner 37) v := by
  have h65 : extension support (fun t => v (support t)) 65=v 65 :=
    extend_at support support_injective (fun t => v (support t)) 54
  have h585 : extension support (fun t => v (support t)) 585=v 585 :=
    extend_at support support_injective (fun t => v (support t)) 233
  simp only [show gridTaylorQ 37=6 from rfl,show gridTaylorPartner 37=(-65:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h65,h585]

theorem taylorTarget_restrict_38 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 38) (gridTaylorPartner 38) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 38) (gridTaylorPartner 38) v := by
  have h78 : extension support (fun t => v (support t)) 78=v 78 :=
    extend_at support support_injective (fun t => v (support t)) 60
  have h598 : extension support (fun t => v (support t)) 598=v 598 :=
    extend_at support support_injective (fun t => v (support t)) 236
  simp only [show gridTaylorQ 38=6 from rfl,show gridTaylorPartner 38=(-52:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h78,h598]

theorem taylorTarget_restrict_39 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 39) (gridTaylorPartner 39) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 39) (gridTaylorPartner 39) v := by
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  simp only [show gridTaylorQ 39=6 from rfl,show gridTaylorPartner 39=(-50:ℤ) from rfl,
    gridSample,show residues 6=({1,5}:Finset ℕ) from by decide]
  norm_num [gridIndex,h80,h600]

theorem taylorTarget_restrict_40 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 40) (gridTaylorPartner 40) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 40) (gridTaylorPartner 40) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h156 : extension support (fun t => v (support t)) 156=v 156 :=
    extend_at support support_injective (fun t => v (support t)) 79
  have h312 : extension support (fun t => v (support t)) 312=v 312 :=
    extend_at support support_injective (fun t => v (support t)) 112
  have h624 : extension support (fun t => v (support t)) 624=v 624 :=
    extend_at support support_injective (fun t => v (support t)) 242
  simp only [show gridTaylorQ 40=10 from rfl,show gridTaylorPartner 40=(78:ℤ) from rfl,
    gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h156,h312,h624]

theorem taylorTarget_restrict_41 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 41) (gridTaylorPartner 41) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 41) (gridTaylorPartner 41) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h156 : extension support (fun t => v (support t)) 156=v 156 :=
    extend_at support support_injective (fun t => v (support t)) 79
  have h468 : extension support (fun t => v (support t)) 468=v 468 :=
    extend_at support support_injective (fun t => v (support t)) 209
  have h624 : extension support (fun t => v (support t)) 624=v 624 :=
    extend_at support support_injective (fun t => v (support t)) 242
  simp only [show gridTaylorQ 41=10 from rfl,show gridTaylorPartner 41=(-78:ℤ) from rfl,
    gridSample,show residues 10=({1,3,7,9}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h156,h468,h624]

theorem taylorTarget_restrict_42 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 42) (gridTaylorPartner 42) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 42) (gridTaylorPartner 42) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 42=12 from rfl,show gridTaylorPartner 42=(65:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h130,h390,h520]

theorem taylorTarget_restrict_43 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 43) (gridTaylorPartner 43) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 43) (gridTaylorPartner 43) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  simp only [show gridTaylorQ 43=12 from rfl,show gridTaylorPartner 43=(325:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260,h390,h650]

theorem taylorTarget_restrict_44 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 44) (gridTaylorPartner 44) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 44) (gridTaylorPartner 44) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  simp only [show gridTaylorQ 44=12 from rfl,show gridTaylorPartner 44=(-325:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h130,h390,h520]

theorem taylorTarget_restrict_45 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 45) (gridTaylorPartner 45) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 45) (gridTaylorPartner 45) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  simp only [show gridTaylorQ 45=12 from rfl,show gridTaylorPartner 45=(-65:ℤ) from rfl,
    gridSample,show residues 12=({1,5,7,11}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h260,h390,h650]

theorem taylorTarget_restrict_46 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 46) (gridTaylorPartner 46) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 46) (gridTaylorPartner 46) v := by
  have h70 : extension support (fun t => v (support t)) 70=v 70 :=
    extend_at support support_injective (fun t => v (support t)) 57
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h190 : extension support (fun t => v (support t)) 190=v 190 :=
    extend_at support support_injective (fun t => v (support t)) 87
  have h250 : extension support (fun t => v (support t)) 250=v 250 :=
    extend_at support support_injective (fun t => v (support t)) 101
  have h310 : extension support (fun t => v (support t)) 310=v 310 :=
    extend_at support support_injective (fun t => v (support t)) 111
  have h370 : extension support (fun t => v (support t)) 370=v 370 :=
    extend_at support support_injective (fun t => v (support t)) 143
  have h430 : extension support (fun t => v (support t)) 430=v 430 :=
    extend_at support support_injective (fun t => v (support t)) 196
  have h490 : extension support (fun t => v (support t)) 490=v 490 :=
    extend_at support support_injective (fun t => v (support t)) 213
  have h550 : extension support (fun t => v (support t)) 550=v 550 :=
    extend_at support support_injective (fun t => v (support t)) 225
  have h610 : extension support (fun t => v (support t)) 610=v 610 :=
    extend_at support support_injective (fun t => v (support t)) 238
  have h670 : extension support (fun t => v (support t)) 670=v 670 :=
    extend_at support support_injective (fun t => v (support t)) 252
  have h730 : extension support (fun t => v (support t)) 730=v 730 :=
    extend_at support support_injective (fun t => v (support t)) 281
  simp only [show gridTaylorQ 46=13 from rfl,show gridTaylorPartner 46=(10:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h70,h130,h190,h250,h310,h370,h430,h490,h550,h610,h670,h730]

theorem taylorTarget_restrict_47 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 47) (gridTaylorPartner 47) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 47) (gridTaylorPartner 47) v := by
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h140 : extension support (fun t => v (support t)) 140=v 140 :=
    extend_at support support_injective (fun t => v (support t)) 75
  have h200 : extension support (fun t => v (support t)) 200=v 200 :=
    extend_at support support_injective (fun t => v (support t)) 89
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h320 : extension support (fun t => v (support t)) 320=v 320 :=
    extend_at support support_injective (fun t => v (support t)) 114
  have h380 : extension support (fun t => v (support t)) 380=v 380 :=
    extend_at support support_injective (fun t => v (support t)) 151
  have h440 : extension support (fun t => v (support t)) 440=v 440 :=
    extend_at support support_injective (fun t => v (support t)) 200
  have h500 : extension support (fun t => v (support t)) 500=v 500 :=
    extend_at support support_injective (fun t => v (support t)) 216
  have h560 : extension support (fun t => v (support t)) 560=v 560 :=
    extend_at support support_injective (fun t => v (support t)) 228
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  have h680 : extension support (fun t => v (support t)) 680=v 680 :=
    extend_at support support_injective (fun t => v (support t)) 255
  have h740 : extension support (fun t => v (support t)) 740=v 740 :=
    extend_at support support_injective (fun t => v (support t)) 286
  simp only [show gridTaylorQ 47=13 from rfl,show gridTaylorPartner 47=(20:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h80,h140,h200,h260,h320,h380,h440,h500,h560,h620,h680,h740]

theorem taylorTarget_restrict_48 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 48) (gridTaylorPartner 48) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 48) (gridTaylorPartner 48) v := by
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 48=13 from rfl,show gridTaylorPartner 48=(90:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h30,h150,h210,h270,h330,h390,h450,h510,h570,h630,h690,h750]

theorem taylorTarget_restrict_49 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 49) (gridTaylorPartner 49) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 49) (gridTaylorPartner 49) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  simp only [show gridTaylorQ 49=13 from rfl,show gridTaylorPartner 49=(180:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h60,h120,h240,h300,h360,h420,h480,h540,h600,h660,h720]

theorem taylorTarget_restrict_50 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 50) (gridTaylorPartner 50) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 50) (gridTaylorPartner 50) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  simp only [show gridTaylorQ 50=13 from rfl,show gridTaylorPartner 50=(-180:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h60,h120,h180,h240,h300,h360,h420,h480,h540,h660,h720]

theorem taylorTarget_restrict_51 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 51) (gridTaylorPartner 51) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 51) (gridTaylorPartner 51) v := by
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 51=13 from rfl,show gridTaylorPartner 51=(-90:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h30,h90,h150,h210,h270,h330,h390,h450,h510,h570,h630,h750]

theorem taylorTarget_restrict_52 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 52) (gridTaylorPartner 52) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 52) (gridTaylorPartner 52) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  simp only [show gridTaylorQ 52=13 from rfl,show gridTaylorPartner 52=(-60:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h60,h120,h180,h240,h300,h360,h420,h480,h540,h600,h660]

theorem taylorTarget_restrict_53 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 53) (gridTaylorPartner 53) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 53) (gridTaylorPartner 53) v := by
  have h40 : extension support (fun t => v (support t)) 40=v 40 :=
    extend_at support support_injective (fun t => v (support t)) 35
  have h100 : extension support (fun t => v (support t)) 100=v 100 :=
    extend_at support support_injective (fun t => v (support t)) 66
  have h160 : extension support (fun t => v (support t)) 160=v 160 :=
    extend_at support support_injective (fun t => v (support t)) 80
  have h220 : extension support (fun t => v (support t)) 220=v 220 :=
    extend_at support support_injective (fun t => v (support t)) 93
  have h280 : extension support (fun t => v (support t)) 280=v 280 :=
    extend_at support support_injective (fun t => v (support t)) 105
  have h340 : extension support (fun t => v (support t)) 340=v 340 :=
    extend_at support support_injective (fun t => v (support t)) 121
  have h400 : extension support (fun t => v (support t)) 400=v 400 :=
    extend_at support support_injective (fun t => v (support t)) 170
  have h460 : extension support (fun t => v (support t)) 460=v 460 :=
    extend_at support support_injective (fun t => v (support t)) 207
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  have h580 : extension support (fun t => v (support t)) 580=v 580 :=
    extend_at support support_injective (fun t => v (support t)) 232
  have h640 : extension support (fun t => v (support t)) 640=v 640 :=
    extend_at support support_injective (fun t => v (support t)) 246
  have h700 : extension support (fun t => v (support t)) 700=v 700 :=
    extend_at support support_injective (fun t => v (support t)) 260
  simp only [show gridTaylorQ 53=13 from rfl,show gridTaylorPartner 53=(-20:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h40,h100,h160,h220,h280,h340,h400,h460,h520,h580,h640,h700]

theorem taylorTarget_restrict_54 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 54) (gridTaylorPartner 54) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 54) (gridTaylorPartner 54) v := by
  have h50 : extension support (fun t => v (support t)) 50=v 50 :=
    extend_at support support_injective (fun t => v (support t)) 40
  have h110 : extension support (fun t => v (support t)) 110=v 110 :=
    extend_at support support_injective (fun t => v (support t)) 69
  have h170 : extension support (fun t => v (support t)) 170=v 170 :=
    extend_at support support_injective (fun t => v (support t)) 83
  have h230 : extension support (fun t => v (support t)) 230=v 230 :=
    extend_at support support_injective (fun t => v (support t)) 96
  have h290 : extension support (fun t => v (support t)) 290=v 290 :=
    extend_at support support_injective (fun t => v (support t)) 108
  have h350 : extension support (fun t => v (support t)) 350=v 350 :=
    extend_at support support_injective (fun t => v (support t)) 125
  have h410 : extension support (fun t => v (support t)) 410=v 410 :=
    extend_at support support_injective (fun t => v (support t)) 178
  have h470 : extension support (fun t => v (support t)) 470=v 470 :=
    extend_at support support_injective (fun t => v (support t)) 210
  have h530 : extension support (fun t => v (support t)) 530=v 530 :=
    extend_at support support_injective (fun t => v (support t)) 220
  have h590 : extension support (fun t => v (support t)) 590=v 590 :=
    extend_at support support_injective (fun t => v (support t)) 234
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  have h710 : extension support (fun t => v (support t)) 710=v 710 :=
    extend_at support support_injective (fun t => v (support t)) 264
  simp only [show gridTaylorQ 54=13 from rfl,show gridTaylorPartner 54=(-10:ℤ) from rfl,
    gridSample,show residues 13=({1,2,3,4,5,6,7,8,9,10,11,12}:Finset ℕ) from by decide]
  norm_num [gridIndex,h50,h110,h170,h230,h290,h350,h410,h470,h530,h590,h650,h710]

theorem taylorTarget_restrict_55 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 55) (gridTaylorPartner 55) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 55) (gridTaylorPartner 55) v := by
  have h40 : extension support (fun t => v (support t)) 40=v 40 :=
    extend_at support support_injective (fun t => v (support t)) 35
  have h100 : extension support (fun t => v (support t)) 100=v 100 :=
    extend_at support support_injective (fun t => v (support t)) 66
  have h160 : extension support (fun t => v (support t)) 160=v 160 :=
    extend_at support support_injective (fun t => v (support t)) 80
  have h220 : extension support (fun t => v (support t)) 220=v 220 :=
    extend_at support support_injective (fun t => v (support t)) 93
  have h280 : extension support (fun t => v (support t)) 280=v 280 :=
    extend_at support support_injective (fun t => v (support t)) 105
  have h340 : extension support (fun t => v (support t)) 340=v 340 :=
    extend_at support support_injective (fun t => v (support t)) 121
  have h460 : extension support (fun t => v (support t)) 460=v 460 :=
    extend_at support support_injective (fun t => v (support t)) 207
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  have h580 : extension support (fun t => v (support t)) 580=v 580 :=
    extend_at support support_injective (fun t => v (support t)) 232
  have h640 : extension support (fun t => v (support t)) 640=v 640 :=
    extend_at support support_injective (fun t => v (support t)) 246
  have h700 : extension support (fun t => v (support t)) 700=v 700 :=
    extend_at support support_injective (fun t => v (support t)) 260
  have h760 : extension support (fun t => v (support t)) 760=v 760 :=
    extend_at support support_injective (fun t => v (support t)) 302
  simp only [show gridTaylorQ 55=26 from rfl,show gridTaylorPartner 55=(10:ℤ) from rfl,
    gridSample,show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]
  norm_num [gridIndex,h40,h100,h160,h220,h280,h340,h460,h520,h580,h640,h700,h760]

theorem taylorTarget_restrict_56 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 56) (gridTaylorPartner 56) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 56) (gridTaylorPartner 56) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  simp only [show gridTaylorQ 56=26 from rfl,show gridTaylorPartner 56=(90:ℤ) from rfl,
    gridSample,show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h60,h120,h180,h240,h300,h360,h420,h540,h600,h660,h720]

theorem taylorTarget_restrict_57 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 57) (gridTaylorPartner 57) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 57) (gridTaylorPartner 57) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  simp only [show gridTaylorQ 57=26 from rfl,show gridTaylorPartner 57=(-90:ℤ) from rfl,
    gridSample,show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h60,h120,h180,h240,h360,h420,h480,h540,h600,h660,h720]

theorem taylorTarget_restrict_58 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 58) (gridTaylorPartner 58) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 58) (gridTaylorPartner 58) v := by
  have h20 : extension support (fun t => v (support t)) 20=v 20 :=
    extend_at support support_injective (fun t => v (support t)) 19
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h140 : extension support (fun t => v (support t)) 140=v 140 :=
    extend_at support support_injective (fun t => v (support t)) 75
  have h200 : extension support (fun t => v (support t)) 200=v 200 :=
    extend_at support support_injective (fun t => v (support t)) 89
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h320 : extension support (fun t => v (support t)) 320=v 320 :=
    extend_at support support_injective (fun t => v (support t)) 114
  have h440 : extension support (fun t => v (support t)) 440=v 440 :=
    extend_at support support_injective (fun t => v (support t)) 200
  have h500 : extension support (fun t => v (support t)) 500=v 500 :=
    extend_at support support_injective (fun t => v (support t)) 216
  have h560 : extension support (fun t => v (support t)) 560=v 560 :=
    extend_at support support_injective (fun t => v (support t)) 228
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  have h680 : extension support (fun t => v (support t)) 680=v 680 :=
    extend_at support support_injective (fun t => v (support t)) 255
  have h740 : extension support (fun t => v (support t)) 740=v 740 :=
    extend_at support support_injective (fun t => v (support t)) 286
  simp only [show gridTaylorQ 58=26 from rfl,show gridTaylorPartner 58=(-10:ℤ) from rfl,
    gridSample,show residues 26=({1,3,5,7,9,11,15,17,19,21,23,25}:Finset ℕ) from by decide]
  norm_num [gridIndex,h20,h80,h140,h200,h260,h320,h440,h500,h560,h620,h680,h740]

theorem taylorTarget_restrict_59 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 59) (gridTaylorPartner 59) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 59) (gridTaylorPartner 59) v := by
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h50 : extension support (fun t => v (support t)) 50=v 50 :=
    extend_at support support_injective (fun t => v (support t)) 40
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h110 : extension support (fun t => v (support t)) 110=v 110 :=
    extend_at support support_injective (fun t => v (support t)) 69
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h170 : extension support (fun t => v (support t)) 170=v 170 :=
    extend_at support support_injective (fun t => v (support t)) 83
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h230 : extension support (fun t => v (support t)) 230=v 230 :=
    extend_at support support_injective (fun t => v (support t)) 96
  have h290 : extension support (fun t => v (support t)) 290=v 290 :=
    extend_at support support_injective (fun t => v (support t)) 108
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h350 : extension support (fun t => v (support t)) 350=v 350 :=
    extend_at support support_injective (fun t => v (support t)) 125
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h410 : extension support (fun t => v (support t)) 410=v 410 :=
    extend_at support support_injective (fun t => v (support t)) 178
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h470 : extension support (fun t => v (support t)) 470=v 470 :=
    extend_at support support_injective (fun t => v (support t)) 210
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h590 : extension support (fun t => v (support t)) 590=v 590 :=
    extend_at support support_injective (fun t => v (support t)) 234
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  have h710 : extension support (fun t => v (support t)) 710=v 710 :=
    extend_at support support_injective (fun t => v (support t)) 264
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  have h770 : extension support (fun t => v (support t)) 770=v 770 :=
    extend_at support support_injective (fun t => v (support t)) 311
  simp only [show gridTaylorQ 59=39 from rfl,show gridTaylorPartner 59=(10:ℤ) from rfl,
    gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,h30,h50,h90,h110,h150,h170,h210,h230,h290,h330,h350,h390,h410,h450,h470,h510,h570,h590,h630,h650,h690,h710,h750,h770]

theorem taylorTarget_restrict_60 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 60) (gridTaylorPartner 60) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 60) (gridTaylorPartner 60) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h40 : extension support (fun t => v (support t)) 40=v 40 :=
    extend_at support support_injective (fun t => v (support t)) 35
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h100 : extension support (fun t => v (support t)) 100=v 100 :=
    extend_at support support_injective (fun t => v (support t)) 66
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h160 : extension support (fun t => v (support t)) 160=v 160 :=
    extend_at support support_injective (fun t => v (support t)) 80
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h220 : extension support (fun t => v (support t)) 220=v 220 :=
    extend_at support support_injective (fun t => v (support t)) 93
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h340 : extension support (fun t => v (support t)) 340=v 340 :=
    extend_at support support_injective (fun t => v (support t)) 121
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h400 : extension support (fun t => v (support t)) 400=v 400 :=
    extend_at support support_injective (fun t => v (support t)) 170
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h460 : extension support (fun t => v (support t)) 460=v 460 :=
    extend_at support support_injective (fun t => v (support t)) 207
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  have h580 : extension support (fun t => v (support t)) 580=v 580 :=
    extend_at support support_injective (fun t => v (support t)) 232
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h640 : extension support (fun t => v (support t)) 640=v 640 :=
    extend_at support support_injective (fun t => v (support t)) 246
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h700 : extension support (fun t => v (support t)) 700=v 700 :=
    extend_at support support_injective (fun t => v (support t)) 260
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  have h760 : extension support (fun t => v (support t)) 760=v 760 :=
    extend_at support support_injective (fun t => v (support t)) 302
  simp only [show gridTaylorQ 60=39 from rfl,show gridTaylorPartner 60=(20:ℤ) from rfl,
    gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h40,h60,h100,h120,h160,h180,h220,h240,h300,h340,h360,h400,h420,h460,h480,h520,h580,h600,h640,h660,h700,h720,h760]

theorem taylorTarget_restrict_61 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 61) (gridTaylorPartner 61) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 61) (gridTaylorPartner 61) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h20 : extension support (fun t => v (support t)) 20=v 20 :=
    extend_at support support_injective (fun t => v (support t)) 19
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h140 : extension support (fun t => v (support t)) 140=v 140 :=
    extend_at support support_injective (fun t => v (support t)) 75
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h200 : extension support (fun t => v (support t)) 200=v 200 :=
    extend_at support support_injective (fun t => v (support t)) 89
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h320 : extension support (fun t => v (support t)) 320=v 320 :=
    extend_at support support_injective (fun t => v (support t)) 114
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h380 : extension support (fun t => v (support t)) 380=v 380 :=
    extend_at support support_injective (fun t => v (support t)) 151
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h440 : extension support (fun t => v (support t)) 440=v 440 :=
    extend_at support support_injective (fun t => v (support t)) 200
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h560 : extension support (fun t => v (support t)) 560=v 560 :=
    extend_at support support_injective (fun t => v (support t)) 228
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h680 : extension support (fun t => v (support t)) 680=v 680 :=
    extend_at support support_injective (fun t => v (support t)) 255
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  have h740 : extension support (fun t => v (support t)) 740=v 740 :=
    extend_at support support_injective (fun t => v (support t)) 286
  simp only [show gridTaylorQ 61=39 from rfl,show gridTaylorPartner 61=(-20:ℤ) from rfl,
    gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h20,h60,h80,h120,h140,h180,h200,h260,h300,h320,h360,h380,h420,h440,h480,h540,h560,h600,h620,h660,h680,h720,h740]

theorem taylorTarget_restrict_62 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 62) (gridTaylorPartner 62) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 62) (gridTaylorPartner 62) v := by
  have h10 : extension support (fun t => v (support t)) 10=v 10 :=
    extend_at support support_injective (fun t => v (support t)) 10
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h70 : extension support (fun t => v (support t)) 70=v 70 :=
    extend_at support support_injective (fun t => v (support t)) 57
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h190 : extension support (fun t => v (support t)) 190=v 190 :=
    extend_at support support_injective (fun t => v (support t)) 87
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h310 : extension support (fun t => v (support t)) 310=v 310 :=
    extend_at support support_injective (fun t => v (support t)) 111
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h370 : extension support (fun t => v (support t)) 370=v 370 :=
    extend_at support support_injective (fun t => v (support t)) 143
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h430 : extension support (fun t => v (support t)) 430=v 430 :=
    extend_at support support_injective (fun t => v (support t)) 196
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h490 : extension support (fun t => v (support t)) 490=v 490 :=
    extend_at support support_injective (fun t => v (support t)) 213
  have h550 : extension support (fun t => v (support t)) 550=v 550 :=
    extend_at support support_injective (fun t => v (support t)) 225
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h610 : extension support (fun t => v (support t)) 610=v 610 :=
    extend_at support support_injective (fun t => v (support t)) 238
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h670 : extension support (fun t => v (support t)) 670=v 670 :=
    extend_at support support_injective (fun t => v (support t)) 252
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  have h730 : extension support (fun t => v (support t)) 730=v 730 :=
    extend_at support support_injective (fun t => v (support t)) 281
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 62=39 from rfl,show gridTaylorPartner 62=(-10:ℤ) from rfl,
    gridSample,show residues 39=({1,2,4,5,7,8,10,11,14,16,17,19,20,22,23,25,28,29,31,32,34,35,37,38}:Finset ℕ) from by decide]
  norm_num [gridIndex,h10,h30,h70,h90,h130,h150,h190,h210,h270,h310,h330,h370,h390,h430,h450,h490,h550,h570,h610,h630,h670,h690,h730,h750]

theorem taylorTarget_restrict_63 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 63) (gridTaylorPartner 63) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 63) (gridTaylorPartner 63) v := by
  have h20 : extension support (fun t => v (support t)) 20=v 20 :=
    extend_at support support_injective (fun t => v (support t)) 19
  have h50 : extension support (fun t => v (support t)) 50=v 50 :=
    extend_at support support_injective (fun t => v (support t)) 40
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h110 : extension support (fun t => v (support t)) 110=v 110 :=
    extend_at support support_injective (fun t => v (support t)) 69
  have h140 : extension support (fun t => v (support t)) 140=v 140 :=
    extend_at support support_injective (fun t => v (support t)) 75
  have h170 : extension support (fun t => v (support t)) 170=v 170 :=
    extend_at support support_injective (fun t => v (support t)) 83
  have h230 : extension support (fun t => v (support t)) 230=v 230 :=
    extend_at support support_injective (fun t => v (support t)) 96
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h290 : extension support (fun t => v (support t)) 290=v 290 :=
    extend_at support support_injective (fun t => v (support t)) 108
  have h320 : extension support (fun t => v (support t)) 320=v 320 :=
    extend_at support support_injective (fun t => v (support t)) 114
  have h350 : extension support (fun t => v (support t)) 350=v 350 :=
    extend_at support support_injective (fun t => v (support t)) 125
  have h380 : extension support (fun t => v (support t)) 380=v 380 :=
    extend_at support support_injective (fun t => v (support t)) 151
  have h410 : extension support (fun t => v (support t)) 410=v 410 :=
    extend_at support support_injective (fun t => v (support t)) 178
  have h440 : extension support (fun t => v (support t)) 440=v 440 :=
    extend_at support support_injective (fun t => v (support t)) 200
  have h470 : extension support (fun t => v (support t)) 470=v 470 :=
    extend_at support support_injective (fun t => v (support t)) 210
  have h500 : extension support (fun t => v (support t)) 500=v 500 :=
    extend_at support support_injective (fun t => v (support t)) 216
  have h530 : extension support (fun t => v (support t)) 530=v 530 :=
    extend_at support support_injective (fun t => v (support t)) 220
  have h560 : extension support (fun t => v (support t)) 560=v 560 :=
    extend_at support support_injective (fun t => v (support t)) 228
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  have h680 : extension support (fun t => v (support t)) 680=v 680 :=
    extend_at support support_injective (fun t => v (support t)) 255
  have h710 : extension support (fun t => v (support t)) 710=v 710 :=
    extend_at support support_injective (fun t => v (support t)) 264
  have h740 : extension support (fun t => v (support t)) 740=v 740 :=
    extend_at support support_injective (fun t => v (support t)) 286
  have h770 : extension support (fun t => v (support t)) 770=v 770 :=
    extend_at support support_injective (fun t => v (support t)) 311
  simp only [show gridTaylorQ 63=52 from rfl,show gridTaylorPartner 63=(5:ℤ) from rfl,
    gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,h20,h50,h80,h110,h140,h170,h230,h260,h290,h320,h350,h380,h410,h440,h470,h500,h530,h560,h620,h650,h680,h710,h740,h770]

theorem taylorTarget_restrict_64 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 64) (gridTaylorPartner 64) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 64) (gridTaylorPartner 64) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 64=52 from rfl,show gridTaylorPartner 64=(45:ℤ) from rfl,
    gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h30,h60,h90,h120,h150,h180,h210,h270,h300,h330,h360,h390,h420,h450,h480,h510,h540,h570,h600,h660,h690,h720,h750]

theorem taylorTarget_restrict_65 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 65) (gridTaylorPartner 65) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 65) (gridTaylorPartner 65) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  simp only [show gridTaylorQ 65=52 from rfl,show gridTaylorPartner 65=(-45:ℤ) from rfl,
    gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h30,h60,h90,h120,h180,h210,h240,h270,h300,h330,h360,h390,h420,h450,h480,h510,h570,h600,h630,h660,h690,h720,h750]

theorem taylorTarget_restrict_66 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 66) (gridTaylorPartner 66) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 66) (gridTaylorPartner 66) v := by
  have h10 : extension support (fun t => v (support t)) 10=v 10 :=
    extend_at support support_injective (fun t => v (support t)) 10
  have h40 : extension support (fun t => v (support t)) 40=v 40 :=
    extend_at support support_injective (fun t => v (support t)) 35
  have h70 : extension support (fun t => v (support t)) 70=v 70 :=
    extend_at support support_injective (fun t => v (support t)) 57
  have h100 : extension support (fun t => v (support t)) 100=v 100 :=
    extend_at support support_injective (fun t => v (support t)) 66
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h160 : extension support (fun t => v (support t)) 160=v 160 :=
    extend_at support support_injective (fun t => v (support t)) 80
  have h220 : extension support (fun t => v (support t)) 220=v 220 :=
    extend_at support support_injective (fun t => v (support t)) 93
  have h250 : extension support (fun t => v (support t)) 250=v 250 :=
    extend_at support support_injective (fun t => v (support t)) 101
  have h280 : extension support (fun t => v (support t)) 280=v 280 :=
    extend_at support support_injective (fun t => v (support t)) 105
  have h310 : extension support (fun t => v (support t)) 310=v 310 :=
    extend_at support support_injective (fun t => v (support t)) 111
  have h340 : extension support (fun t => v (support t)) 340=v 340 :=
    extend_at support support_injective (fun t => v (support t)) 121
  have h370 : extension support (fun t => v (support t)) 370=v 370 :=
    extend_at support support_injective (fun t => v (support t)) 143
  have h400 : extension support (fun t => v (support t)) 400=v 400 :=
    extend_at support support_injective (fun t => v (support t)) 170
  have h430 : extension support (fun t => v (support t)) 430=v 430 :=
    extend_at support support_injective (fun t => v (support t)) 196
  have h460 : extension support (fun t => v (support t)) 460=v 460 :=
    extend_at support support_injective (fun t => v (support t)) 207
  have h490 : extension support (fun t => v (support t)) 490=v 490 :=
    extend_at support support_injective (fun t => v (support t)) 213
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  have h550 : extension support (fun t => v (support t)) 550=v 550 :=
    extend_at support support_injective (fun t => v (support t)) 225
  have h610 : extension support (fun t => v (support t)) 610=v 610 :=
    extend_at support support_injective (fun t => v (support t)) 238
  have h640 : extension support (fun t => v (support t)) 640=v 640 :=
    extend_at support support_injective (fun t => v (support t)) 246
  have h670 : extension support (fun t => v (support t)) 670=v 670 :=
    extend_at support support_injective (fun t => v (support t)) 252
  have h700 : extension support (fun t => v (support t)) 700=v 700 :=
    extend_at support support_injective (fun t => v (support t)) 260
  have h730 : extension support (fun t => v (support t)) 730=v 730 :=
    extend_at support support_injective (fun t => v (support t)) 281
  have h760 : extension support (fun t => v (support t)) 760=v 760 :=
    extend_at support support_injective (fun t => v (support t)) 302
  simp only [show gridTaylorQ 66=52 from rfl,show gridTaylorPartner 66=(-5:ℤ) from rfl,
    gridSample,show residues 52=({1,3,5,7,9,11,15,17,19,21,23,25,27,29,31,33,35,37,41,43,45,47,49,51}:Finset ℕ) from by decide]
  norm_num [gridIndex,h10,h40,h70,h100,h130,h160,h220,h250,h280,h310,h340,h370,h400,h430,h460,h490,h520,h550,h610,h640,h670,h700,h730,h760]

theorem taylorTarget_restrict_67 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 67) (gridTaylorPartner 67) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 67) (gridTaylorPartner 67) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h20 : extension support (fun t => v (support t)) 20=v 20 :=
    extend_at support support_injective (fun t => v (support t)) 19
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h200 : extension support (fun t => v (support t)) 200=v 200 :=
    extend_at support support_injective (fun t => v (support t)) 89
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h320 : extension support (fun t => v (support t)) 320=v 320 :=
    extend_at support support_injective (fun t => v (support t)) 114
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h380 : extension support (fun t => v (support t)) 380=v 380 :=
    extend_at support support_injective (fun t => v (support t)) 151
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h440 : extension support (fun t => v (support t)) 440=v 440 :=
    extend_at support support_injective (fun t => v (support t)) 200
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h500 : extension support (fun t => v (support t)) 500=v 500 :=
    extend_at support support_injective (fun t => v (support t)) 216
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h560 : extension support (fun t => v (support t)) 560=v 560 :=
    extend_at support support_injective (fun t => v (support t)) 228
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  have h680 : extension support (fun t => v (support t)) 680=v 680 :=
    extend_at support support_injective (fun t => v (support t)) 255
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  have h740 : extension support (fun t => v (support t)) 740=v 740 :=
    extend_at support support_injective (fun t => v (support t)) 286
  simp only [show gridTaylorQ 67=78 from rfl,show gridTaylorPartner 67=(10:ℤ) from rfl,
    gridSample,show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h20,h60,h80,h120,h180,h200,h240,h260,h300,h320,h360,h380,h420,h440,h480,h500,h540,h560,h600,h620,h680,h720,h740]

theorem taylorTarget_restrict_68 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 68) (gridTaylorPartner 68) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 68) (gridTaylorPartner 68) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h40 : extension support (fun t => v (support t)) 40=v 40 :=
    extend_at support support_injective (fun t => v (support t)) 35
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h100 : extension support (fun t => v (support t)) 100=v 100 :=
    extend_at support support_injective (fun t => v (support t)) 66
  have h160 : extension support (fun t => v (support t)) 160=v 160 :=
    extend_at support support_injective (fun t => v (support t)) 80
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h220 : extension support (fun t => v (support t)) 220=v 220 :=
    extend_at support support_injective (fun t => v (support t)) 93
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h280 : extension support (fun t => v (support t)) 280=v 280 :=
    extend_at support support_injective (fun t => v (support t)) 105
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h340 : extension support (fun t => v (support t)) 340=v 340 :=
    extend_at support support_injective (fun t => v (support t)) 121
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h400 : extension support (fun t => v (support t)) 400=v 400 :=
    extend_at support support_injective (fun t => v (support t)) 170
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h460 : extension support (fun t => v (support t)) 460=v 460 :=
    extend_at support support_injective (fun t => v (support t)) 207
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h580 : extension support (fun t => v (support t)) 580=v 580 :=
    extend_at support support_injective (fun t => v (support t)) 232
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h700 : extension support (fun t => v (support t)) 700=v 700 :=
    extend_at support support_injective (fun t => v (support t)) 260
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  have h760 : extension support (fun t => v (support t)) 760=v 760 :=
    extend_at support support_injective (fun t => v (support t)) 302
  simp only [show gridTaylorQ 68=78 from rfl,show gridTaylorPartner 68=(-10:ℤ) from rfl,
    gridSample,show residues 78=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h40,h60,h100,h160,h180,h220,h240,h280,h300,h340,h360,h400,h420,h460,h480,h520,h540,h580,h600,h660,h700,h720,h760]

theorem taylorTarget_restrict_69 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 69) (gridTaylorPartner 69) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 69) (gridTaylorPartner 69) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h10 : extension support (fun t => v (support t)) 10=v 10 :=
    extend_at support support_injective (fun t => v (support t)) 10
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h40 : extension support (fun t => v (support t)) 40=v 40 :=
    extend_at support support_injective (fun t => v (support t)) 35
  have h60 : extension support (fun t => v (support t)) 60=v 60 :=
    extend_at support support_injective (fun t => v (support t)) 49
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h100 : extension support (fun t => v (support t)) 100=v 100 :=
    extend_at support support_injective (fun t => v (support t)) 66
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h130 : extension support (fun t => v (support t)) 130=v 130 :=
    extend_at support support_injective (fun t => v (support t)) 73
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h160 : extension support (fun t => v (support t)) 160=v 160 :=
    extend_at support support_injective (fun t => v (support t)) 80
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h190 : extension support (fun t => v (support t)) 190=v 190 :=
    extend_at support support_injective (fun t => v (support t)) 87
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h220 : extension support (fun t => v (support t)) 220=v 220 :=
    extend_at support support_injective (fun t => v (support t)) 93
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h250 : extension support (fun t => v (support t)) 250=v 250 :=
    extend_at support support_injective (fun t => v (support t)) 101
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h280 : extension support (fun t => v (support t)) 280=v 280 :=
    extend_at support support_injective (fun t => v (support t)) 105
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h310 : extension support (fun t => v (support t)) 310=v 310 :=
    extend_at support support_injective (fun t => v (support t)) 111
  have h340 : extension support (fun t => v (support t)) 340=v 340 :=
    extend_at support support_injective (fun t => v (support t)) 121
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h370 : extension support (fun t => v (support t)) 370=v 370 :=
    extend_at support support_injective (fun t => v (support t)) 143
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h400 : extension support (fun t => v (support t)) 400=v 400 :=
    extend_at support support_injective (fun t => v (support t)) 170
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h430 : extension support (fun t => v (support t)) 430=v 430 :=
    extend_at support support_injective (fun t => v (support t)) 196
  have h450 : extension support (fun t => v (support t)) 450=v 450 :=
    extend_at support support_injective (fun t => v (support t)) 203
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h490 : extension support (fun t => v (support t)) 490=v 490 :=
    extend_at support support_injective (fun t => v (support t)) 213
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h520 : extension support (fun t => v (support t)) 520=v 520 :=
    extend_at support support_injective (fun t => v (support t)) 219
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h550 : extension support (fun t => v (support t)) 550=v 550 :=
    extend_at support support_injective (fun t => v (support t)) 225
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h580 : extension support (fun t => v (support t)) 580=v 580 :=
    extend_at support support_injective (fun t => v (support t)) 232
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h610 : extension support (fun t => v (support t)) 610=v 610 :=
    extend_at support support_injective (fun t => v (support t)) 238
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h640 : extension support (fun t => v (support t)) 640=v 640 :=
    extend_at support support_injective (fun t => v (support t)) 246
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h670 : extension support (fun t => v (support t)) 670=v 670 :=
    extend_at support support_injective (fun t => v (support t)) 252
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  have h700 : extension support (fun t => v (support t)) 700=v 700 :=
    extend_at support support_injective (fun t => v (support t)) 260
  have h730 : extension support (fun t => v (support t)) 730=v 730 :=
    extend_at support support_injective (fun t => v (support t)) 281
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  have h760 : extension support (fun t => v (support t)) 760=v 760 :=
    extend_at support support_injective (fun t => v (support t)) 302
  simp only [show gridTaylorQ 69=156 from rfl,show gridTaylorPartner 69=(5:ℤ) from rfl,
    gridSample,show residues 156=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77,79,83,85,89,95,97,101,103,107,109,113,115,119,121,125,127,131,133,137,139,145,149,151,155}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h10,h30,h40,h60,h90,h100,h120,h130,h150,h160,h180,h190,h210,h220,h240,h250,h270,h280,h300,h310,h340,h360,h370,h390,h400,h420,h430,h450,h480,h490,h510,h520,h540,h550,h570,h580,h600,h610,h630,h640,h660,h670,h690,h700,h730,h750,h760]

theorem taylorTarget_restrict_70 (v : Fin 780→ℂ) :
    gridSample (gridTaylorQ 70) (gridTaylorPartner 70) (extension support (fun j => v (support j)))=
      gridSample (gridTaylorQ 70) (gridTaylorPartner 70) v := by
  have h0 : extension support (fun t => v (support t)) 0=v 0 :=
    extend_at support support_injective (fun t => v (support t)) 0
  have h20 : extension support (fun t => v (support t)) 20=v 20 :=
    extend_at support support_injective (fun t => v (support t)) 19
  have h30 : extension support (fun t => v (support t)) 30=v 30 :=
    extend_at support support_injective (fun t => v (support t)) 28
  have h50 : extension support (fun t => v (support t)) 50=v 50 :=
    extend_at support support_injective (fun t => v (support t)) 40
  have h80 : extension support (fun t => v (support t)) 80=v 80 :=
    extend_at support support_injective (fun t => v (support t)) 61
  have h90 : extension support (fun t => v (support t)) 90=v 90 :=
    extend_at support support_injective (fun t => v (support t)) 63
  have h110 : extension support (fun t => v (support t)) 110=v 110 :=
    extend_at support support_injective (fun t => v (support t)) 69
  have h120 : extension support (fun t => v (support t)) 120=v 120 :=
    extend_at support support_injective (fun t => v (support t)) 71
  have h140 : extension support (fun t => v (support t)) 140=v 140 :=
    extend_at support support_injective (fun t => v (support t)) 75
  have h150 : extension support (fun t => v (support t)) 150=v 150 :=
    extend_at support support_injective (fun t => v (support t)) 77
  have h170 : extension support (fun t => v (support t)) 170=v 170 :=
    extend_at support support_injective (fun t => v (support t)) 83
  have h180 : extension support (fun t => v (support t)) 180=v 180 :=
    extend_at support support_injective (fun t => v (support t)) 84
  have h200 : extension support (fun t => v (support t)) 200=v 200 :=
    extend_at support support_injective (fun t => v (support t)) 89
  have h210 : extension support (fun t => v (support t)) 210=v 210 :=
    extend_at support support_injective (fun t => v (support t)) 92
  have h230 : extension support (fun t => v (support t)) 230=v 230 :=
    extend_at support support_injective (fun t => v (support t)) 96
  have h240 : extension support (fun t => v (support t)) 240=v 240 :=
    extend_at support support_injective (fun t => v (support t)) 99
  have h260 : extension support (fun t => v (support t)) 260=v 260 :=
    extend_at support support_injective (fun t => v (support t)) 102
  have h270 : extension support (fun t => v (support t)) 270=v 270 :=
    extend_at support support_injective (fun t => v (support t)) 103
  have h290 : extension support (fun t => v (support t)) 290=v 290 :=
    extend_at support support_injective (fun t => v (support t)) 108
  have h300 : extension support (fun t => v (support t)) 300=v 300 :=
    extend_at support support_injective (fun t => v (support t)) 110
  have h330 : extension support (fun t => v (support t)) 330=v 330 :=
    extend_at support support_injective (fun t => v (support t)) 118
  have h350 : extension support (fun t => v (support t)) 350=v 350 :=
    extend_at support support_injective (fun t => v (support t)) 125
  have h360 : extension support (fun t => v (support t)) 360=v 360 :=
    extend_at support support_injective (fun t => v (support t)) 134
  have h380 : extension support (fun t => v (support t)) 380=v 380 :=
    extend_at support support_injective (fun t => v (support t)) 151
  have h390 : extension support (fun t => v (support t)) 390=v 390 :=
    extend_at support support_injective (fun t => v (support t)) 160
  have h410 : extension support (fun t => v (support t)) 410=v 410 :=
    extend_at support support_injective (fun t => v (support t)) 178
  have h420 : extension support (fun t => v (support t)) 420=v 420 :=
    extend_at support support_injective (fun t => v (support t)) 187
  have h440 : extension support (fun t => v (support t)) 440=v 440 :=
    extend_at support support_injective (fun t => v (support t)) 200
  have h470 : extension support (fun t => v (support t)) 470=v 470 :=
    extend_at support support_injective (fun t => v (support t)) 210
  have h480 : extension support (fun t => v (support t)) 480=v 480 :=
    extend_at support support_injective (fun t => v (support t)) 211
  have h500 : extension support (fun t => v (support t)) 500=v 500 :=
    extend_at support support_injective (fun t => v (support t)) 216
  have h510 : extension support (fun t => v (support t)) 510=v 510 :=
    extend_at support support_injective (fun t => v (support t)) 218
  have h530 : extension support (fun t => v (support t)) 530=v 530 :=
    extend_at support support_injective (fun t => v (support t)) 220
  have h540 : extension support (fun t => v (support t)) 540=v 540 :=
    extend_at support support_injective (fun t => v (support t)) 222
  have h560 : extension support (fun t => v (support t)) 560=v 560 :=
    extend_at support support_injective (fun t => v (support t)) 228
  have h570 : extension support (fun t => v (support t)) 570=v 570 :=
    extend_at support support_injective (fun t => v (support t)) 229
  have h590 : extension support (fun t => v (support t)) 590=v 590 :=
    extend_at support support_injective (fun t => v (support t)) 234
  have h600 : extension support (fun t => v (support t)) 600=v 600 :=
    extend_at support support_injective (fun t => v (support t)) 237
  have h620 : extension support (fun t => v (support t)) 620=v 620 :=
    extend_at support support_injective (fun t => v (support t)) 241
  have h630 : extension support (fun t => v (support t)) 630=v 630 :=
    extend_at support support_injective (fun t => v (support t)) 244
  have h650 : extension support (fun t => v (support t)) 650=v 650 :=
    extend_at support support_injective (fun t => v (support t)) 248
  have h660 : extension support (fun t => v (support t)) 660=v 660 :=
    extend_at support support_injective (fun t => v (support t)) 250
  have h680 : extension support (fun t => v (support t)) 680=v 680 :=
    extend_at support support_injective (fun t => v (support t)) 255
  have h690 : extension support (fun t => v (support t)) 690=v 690 :=
    extend_at support support_injective (fun t => v (support t)) 258
  have h720 : extension support (fun t => v (support t)) 720=v 720 :=
    extend_at support support_injective (fun t => v (support t)) 272
  have h740 : extension support (fun t => v (support t)) 740=v 740 :=
    extend_at support support_injective (fun t => v (support t)) 286
  have h750 : extension support (fun t => v (support t)) 750=v 750 :=
    extend_at support support_injective (fun t => v (support t)) 293
  have h770 : extension support (fun t => v (support t)) 770=v 770 :=
    extend_at support support_injective (fun t => v (support t)) 311
  simp only [show gridTaylorQ 70=156 from rfl,show gridTaylorPartner 70=(-5:ℤ) from rfl,
    gridSample,show residues 156=({1,5,7,11,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,67,71,73,77,79,83,85,89,95,97,101,103,107,109,113,115,119,121,125,127,131,133,137,139,145,149,151,155}:Finset ℕ) from by decide]
  norm_num [gridIndex,h0,h20,h30,h50,h80,h90,h110,h120,h140,h150,h170,h180,h200,h210,h230,h240,h260,h270,h290,h300,h330,h350,h360,h380,h390,h410,h420,h440,h470,h480,h500,h510,h530,h540,h560,h570,h590,h600,h620,h630,h650,h660,h680,h690,h720,h740,h750,h770]

end SmallLevelTwentySixGrid
