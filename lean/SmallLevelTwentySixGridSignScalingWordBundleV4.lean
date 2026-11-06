module
public import SmallLevelTwentySixGridRateDataV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGrid

theorem word_scale_sign_0 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 0))*u^(groupPowers 0).1*v^(groupPowers 0).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 0)) := by
  simp only [show gridGroupSource 0=(23:Fin 27) from rfl,
    show sourceWord 23=[(3,false),(0,false),(0,false)] from rfl,show groupPowers 0=(3, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_1 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 1))*u^(groupPowers 1).1*v^(groupPowers 1).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 1)) := by
  simp only [show gridGroupSource 1=(23:Fin 27) from rfl,
    show sourceWord 23=[(3,false),(0,false),(0,false)] from rfl,show groupPowers 1=(3, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_2 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 2))*u^(groupPowers 2).1*v^(groupPowers 2).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 2)) := by
  simp only [show gridGroupSource 2=(23:Fin 27) from rfl,
    show sourceWord 23=[(3,false),(0,false),(0,false)] from rfl,show groupPowers 2=(-1, 0, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_3 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 3))*u^(groupPowers 3).1*v^(groupPowers 3).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 3)) := by
  simp only [show gridGroupSource 3=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,show groupPowers 3=(1, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_4 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 4))*u^(groupPowers 4).1*v^(groupPowers 4).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 4)) := by
  simp only [show gridGroupSource 4=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,show groupPowers 4=(1, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_5 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 5))*u^(groupPowers 5).1*v^(groupPowers 5).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 5)) := by
  simp only [show gridGroupSource 5=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,show groupPowers 5=(3, 2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_6 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 6))*u^(groupPowers 6).1*v^(groupPowers 6).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 6)) := by
  simp only [show gridGroupSource 6=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,show groupPowers 6=(-3, 0, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_7 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 7))*u^(groupPowers 7).1*v^(groupPowers 7).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 7)) := by
  simp only [show gridGroupSource 7=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,show groupPowers 7=(-1, 2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_8 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 8))*u^(groupPowers 8).1*v^(groupPowers 8).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 8)) := by
  simp only [show gridGroupSource 8=(22:Fin 27) from rfl,
    show sourceWord 22=[(3,false),(0,false)] from rfl,show groupPowers 8=(1, -2, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_9 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 9))*u^(groupPowers 9).1*v^(groupPowers 9).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 9)) := by
  simp only [show gridGroupSource 9=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 9=(-3, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_10 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 10))*u^(groupPowers 10).1*v^(groupPowers 10).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 10)) := by
  simp only [show gridGroupSource 10=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 10=(-1, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_11 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 11))*u^(groupPowers 11).1*v^(groupPowers 11).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 11)) := by
  simp only [show gridGroupSource 11=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 11=(-3, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_12 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 12))*u^(groupPowers 12).1*v^(groupPowers 12).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 12)) := by
  simp only [show gridGroupSource 12=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 12=(1, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_13 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 13))*u^(groupPowers 13).1*v^(groupPowers 13).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 13)) := by
  simp only [show gridGroupSource 13=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 13=(-3, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_14 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 14))*u^(groupPowers 14).1*v^(groupPowers 14).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 14)) := by
  simp only [show gridGroupSource 14=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 14=(-1, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_15 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 15))*u^(groupPowers 15).1*v^(groupPowers 15).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 15)) := by
  simp only [show gridGroupSource 15=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 15=(3, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_16 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 16))*u^(groupPowers 16).1*v^(groupPowers 16).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 16)) := by
  simp only [show gridGroupSource 16=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 16=(-3, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_17 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 17))*u^(groupPowers 17).1*v^(groupPowers 17).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 17)) := by
  simp only [show gridGroupSource 17=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 17=(-1, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_18 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 18))*u^(groupPowers 18).1*v^(groupPowers 18).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 18)) := by
  simp only [show gridGroupSource 18=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 18=(1, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_19 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 19))*u^(groupPowers 19).1*v^(groupPowers 19).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 19)) := by
  simp only [show gridGroupSource 19=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 19=(-3, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_20 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 20))*u^(groupPowers 20).1*v^(groupPowers 20).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 20)) := by
  simp only [show gridGroupSource 20=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 20=(-3, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_21 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 21))*u^(groupPowers 21).1*v^(groupPowers 21).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 21)) := by
  simp only [show gridGroupSource 21=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 21=(-1, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_22 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 22))*u^(groupPowers 22).1*v^(groupPowers 22).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 22)) := by
  simp only [show gridGroupSource 22=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 22=(1, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_23 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 23))*u^(groupPowers 23).1*v^(groupPowers 23).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 23)) := by
  simp only [show gridGroupSource 23=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 23=(3, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_24 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 24))*u^(groupPowers 24).1*v^(groupPowers 24).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 24)) := by
  simp only [show gridGroupSource 24=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 24=(-3, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_25 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 25))*u^(groupPowers 25).1*v^(groupPowers 25).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 25)) := by
  simp only [show gridGroupSource 25=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 25=(-1, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_26 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 26))*u^(groupPowers 26).1*v^(groupPowers 26).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 26)) := by
  simp only [show gridGroupSource 26=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 26=(-1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_27 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 27))*u^(groupPowers 27).1*v^(groupPowers 27).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 27)) := by
  simp only [show gridGroupSource 27=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 27=(1, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_28 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 28))*u^(groupPowers 28).1*v^(groupPowers 28).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 28)) := by
  simp only [show gridGroupSource 28=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 28=(-3, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_29 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 29))*u^(groupPowers 29).1*v^(groupPowers 29).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 29)) := by
  simp only [show gridGroupSource 29=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 29=(3, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_30 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 30))*u^(groupPowers 30).1*v^(groupPowers 30).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 30)) := by
  simp only [show gridGroupSource 30=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 30=(-3, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_31 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 31))*u^(groupPowers 31).1*v^(groupPowers 31).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 31)) := by
  simp only [show gridGroupSource 31=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 31=(-1, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_32 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 32))*u^(groupPowers 32).1*v^(groupPowers 32).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 32)) := by
  simp only [show gridGroupSource 32=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 32=(1, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_33 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 33))*u^(groupPowers 33).1*v^(groupPowers 33).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 33)) := by
  simp only [show gridGroupSource 33=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 33=(1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_34 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 34))*u^(groupPowers 34).1*v^(groupPowers 34).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 34)) := by
  simp only [show gridGroupSource 34=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 34=(-3, -2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_35 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 35))*u^(groupPowers 35).1*v^(groupPowers 35).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 35)) := by
  simp only [show gridGroupSource 35=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 35=(3, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_36 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 36))*u^(groupPowers 36).1*v^(groupPowers 36).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 36)) := by
  simp only [show gridGroupSource 36=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 36=(-3, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_37 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 37))*u^(groupPowers 37).1*v^(groupPowers 37).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 37)) := by
  simp only [show gridGroupSource 37=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 37=(-1, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_38 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 38))*u^(groupPowers 38).1*v^(groupPowers 38).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 38)) := by
  simp only [show gridGroupSource 38=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 38=(-1, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_39 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 39))*u^(groupPowers 39).1*v^(groupPowers 39).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 39)) := by
  simp only [show gridGroupSource 39=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 39=(1, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_40 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 40))*u^(groupPowers 40).1*v^(groupPowers 40).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 40)) := by
  simp only [show gridGroupSource 40=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 40=(3, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_41 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 41))*u^(groupPowers 41).1*v^(groupPowers 41).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 41)) := by
  simp only [show gridGroupSource 41=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 41=(-3, 2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_42 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 42))*u^(groupPowers 42).1*v^(groupPowers 42).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 42)) := by
  simp only [show gridGroupSource 42=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 42=(3, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_43 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 43))*u^(groupPowers 43).1*v^(groupPowers 43).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 43)) := by
  simp only [show gridGroupSource 43=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 43=(-1, -2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_44 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 44))*u^(groupPowers 44).1*v^(groupPowers 44).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 44)) := by
  simp only [show gridGroupSource 44=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 44=(-1, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_45 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 45))*u^(groupPowers 45).1*v^(groupPowers 45).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 45)) := by
  simp only [show gridGroupSource 45=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 45=(1, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_46 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 46))*u^(groupPowers 46).1*v^(groupPowers 46).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 46)) := by
  simp only [show gridGroupSource 46=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 46=(1, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_47 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 47))*u^(groupPowers 47).1*v^(groupPowers 47).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 47)) := by
  simp only [show gridGroupSource 47=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 47=(-3, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_48 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 48))*u^(groupPowers 48).1*v^(groupPowers 48).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 48)) := by
  simp only [show gridGroupSource 48=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 48=(3, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_49 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 49))*u^(groupPowers 49).1*v^(groupPowers 49).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 49)) := by
  simp only [show gridGroupSource 49=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 49=(-3, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_50 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 50))*u^(groupPowers 50).1*v^(groupPowers 50).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 50)) := by
  simp only [show gridGroupSource 50=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 50=(-1, 2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_51 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 51))*u^(groupPowers 51).1*v^(groupPowers 51).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 51)) := by
  simp only [show gridGroupSource 51=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 51=(1, -2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_52 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 52))*u^(groupPowers 52).1*v^(groupPowers 52).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 52)) := by
  simp only [show gridGroupSource 52=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 52=(1, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_53 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 53))*u^(groupPowers 53).1*v^(groupPowers 53).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 53)) := by
  simp only [show gridGroupSource 53=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 53=(3, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_54 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 54))*u^(groupPowers 54).1*v^(groupPowers 54).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 54)) := by
  simp only [show gridGroupSource 54=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 54=(-3, -2, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_55 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 55))*u^(groupPowers 55).1*v^(groupPowers 55).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 55)) := by
  simp only [show gridGroupSource 55=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 55=(3, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_56 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 56))*u^(groupPowers 56).1*v^(groupPowers 56).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 56)) := by
  simp only [show gridGroupSource 56=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 56=(-1, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_57 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 57))*u^(groupPowers 57).1*v^(groupPowers 57).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 57)) := by
  simp only [show gridGroupSource 57=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 57=(-1, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_58 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 58))*u^(groupPowers 58).1*v^(groupPowers 58).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 58)) := by
  simp only [show gridGroupSource 58=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 58=(1, 2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_59 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 59))*u^(groupPowers 59).1*v^(groupPowers 59).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 59)) := by
  simp only [show gridGroupSource 59=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 59=(3, -2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_60 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 60))*u^(groupPowers 60).1*v^(groupPowers 60).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 60)) := by
  simp only [show gridGroupSource 60=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 60=(-3, 2, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_61 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 61))*u^(groupPowers 61).1*v^(groupPowers 61).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 61)) := by
  simp only [show gridGroupSource 61=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 61=(3, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_62 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 62))*u^(groupPowers 62).1*v^(groupPowers 62).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 62)) := by
  simp only [show gridGroupSource 62=(21:Fin 27) from rfl,
    show sourceWord 21=[(3,false)] from rfl,show groupPowers 62=(-1, -2, 1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_63 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 63))*u^(groupPowers 63).1*v^(groupPowers 63).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 63)) := by
  simp only [show gridGroupSource 63=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 63=(-1, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_64 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 64))*u^(groupPowers 64).1*v^(groupPowers 64).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 64)) := by
  simp only [show gridGroupSource 64=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 64=(-3, 2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_65 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 65))*u^(groupPowers 65).1*v^(groupPowers 65).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 65)) := by
  simp only [show gridGroupSource 65=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 65=(3, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_66 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 66))*u^(groupPowers 66).1*v^(groupPowers 66).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 66)) := by
  simp only [show gridGroupSource 66=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 66=(-1, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_67 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 67))*u^(groupPowers 67).1*v^(groupPowers 67).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 67)) := by
  simp only [show gridGroupSource 67=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 67=(-3, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_68 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 68))*u^(groupPowers 68).1*v^(groupPowers 68).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 68)) := by
  simp only [show gridGroupSource 68=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 68=(1, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_69 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 69))*u^(groupPowers 69).1*v^(groupPowers 69).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 69)) := by
  simp only [show gridGroupSource 69=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 69=(-3, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_70 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 70))*u^(groupPowers 70).1*v^(groupPowers 70).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 70)) := by
  simp only [show gridGroupSource 70=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 70=(-1, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_71 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 71))*u^(groupPowers 71).1*v^(groupPowers 71).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 71)) := by
  simp only [show gridGroupSource 71=(24:Fin 27) from rfl,
    show sourceWord 24=[(3,false),(0,true)] from rfl,show groupPowers 71=(-3, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_72 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 72))*u^(groupPowers 72).1*v^(groupPowers 72).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 72)) := by
  simp only [show gridGroupSource 72=(9:Fin 27) from rfl,
    show sourceWord 9=[(1,true),(0,true),(0,true)] from rfl,show groupPowers 72=(2, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_73 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 73))*u^(groupPowers 73).1*v^(groupPowers 73).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 73)) := by
  simp only [show gridGroupSource 73=(1:Fin 27) from rfl,
    show sourceWord 1=[(1,false),(0,true),(0,true)] from rfl,show groupPowers 73=(2, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_74 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 74))*u^(groupPowers 74).1*v^(groupPowers 74).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 74)) := by
  simp only [show gridGroupSource 74=(10:Fin 27) from rfl,
    show sourceWord 10=[(1,true),(1,true),(0,true)] from rfl,show groupPowers 74=(0, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_75 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 75))*u^(groupPowers 75).1*v^(groupPowers 75).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 75)) := by
  simp only [show gridGroupSource 75=(8:Fin 27) from rfl,
    show sourceWord 8=[(1,true),(0,true)] from rfl,show groupPowers 75=(0, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_76 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 76))*u^(groupPowers 76).1*v^(groupPowers 76).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 76)) := by
  simp only [show gridGroupSource 76=(8:Fin 27) from rfl,
    show sourceWord 8=[(1,true),(0,true)] from rfl,show groupPowers 76=(2, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_77 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 77))*u^(groupPowers 77).1*v^(groupPowers 77).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 77)) := by
  simp only [show gridGroupSource 77=(8:Fin 27) from rfl,
    show sourceWord 8=[(1,true),(0,true)] from rfl,show groupPowers 77=(2, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_78 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 78))*u^(groupPowers 78).1*v^(groupPowers 78).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 78)) := by
  simp only [show gridGroupSource 78=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 78=(0, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_79 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 79))*u^(groupPowers 79).1*v^(groupPowers 79).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 79)) := by
  simp only [show gridGroupSource 79=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 79=(2, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_80 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 80))*u^(groupPowers 80).1*v^(groupPowers 80).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 80)) := by
  simp only [show gridGroupSource 80=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 80=(2, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_81 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 81))*u^(groupPowers 81).1*v^(groupPowers 81).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 81)) := by
  simp only [show gridGroupSource 81=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 81=(-2, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_82 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 82))*u^(groupPowers 82).1*v^(groupPowers 82).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 82)) := by
  simp only [show gridGroupSource 82=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 82=(0, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_83 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 83))*u^(groupPowers 83).1*v^(groupPowers 83).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 83)) := by
  simp only [show gridGroupSource 83=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 83=(2, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_84 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 84))*u^(groupPowers 84).1*v^(groupPowers 84).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 84)) := by
  simp only [show gridGroupSource 84=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 84=(-2, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_85 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 85))*u^(groupPowers 85).1*v^(groupPowers 85).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 85)) := by
  simp only [show gridGroupSource 85=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 85=(0, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_86 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 86))*u^(groupPowers 86).1*v^(groupPowers 86).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 86)) := by
  simp only [show gridGroupSource 86=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 86=(2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_87 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 87))*u^(groupPowers 87).1*v^(groupPowers 87).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 87)) := by
  simp only [show gridGroupSource 87=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 87=(-2, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_88 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 88))*u^(groupPowers 88).1*v^(groupPowers 88).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 88)) := by
  simp only [show gridGroupSource 88=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 88=(-2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_89 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 89))*u^(groupPowers 89).1*v^(groupPowers 89).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 89)) := by
  simp only [show gridGroupSource 89=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 89=(0, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_90 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 90))*u^(groupPowers 90).1*v^(groupPowers 90).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 90)) := by
  simp only [show gridGroupSource 90=(0:Fin 27) from rfl,
    show sourceWord 0=[(1,false),(0,true)] from rfl,show groupPowers 90=(-2, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_91 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 91))*u^(groupPowers 91).1*v^(groupPowers 91).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 91)) := by
  simp only [show gridGroupSource 91=(2:Fin 27) from rfl,
    show sourceWord 2=[(1,false),(1,false),(0,true)] from rfl,show groupPowers 91=(0, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_92 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 92))*u^(groupPowers 92).1*v^(groupPowers 92).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 92)) := by
  simp only [show gridGroupSource 92=(2:Fin 27) from rfl,
    show sourceWord 2=[(1,false),(1,false),(0,true)] from rfl,show groupPowers 92=(0, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_93 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 93))*u^(groupPowers 93).1*v^(groupPowers 93).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 93)) := by
  simp only [show gridGroupSource 93=(11:Fin 27) from rfl,
    show sourceWord 11=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 93=(-2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_94 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 94))*u^(groupPowers 94).1*v^(groupPowers 94).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 94)) := by
  simp only [show gridGroupSource 94=(11:Fin 27) from rfl,
    show sourceWord 11=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 94=(2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_95 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 95))*u^(groupPowers 95).1*v^(groupPowers 95).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 95)) := by
  simp only [show gridGroupSource 95=(11:Fin 27) from rfl,
    show sourceWord 11=[(1,true),(1,true),(1,true)] from rfl,show groupPowers 95=(2, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_96 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 96))*u^(groupPowers 96).1*v^(groupPowers 96).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 96)) := by
  simp only [show gridGroupSource 96=(7:Fin 27) from rfl,
    show sourceWord 7=[(1,true)] from rfl,show groupPowers 96=(-2, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_97 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 97))*u^(groupPowers 97).1*v^(groupPowers 97).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 97)) := by
  simp only [show gridGroupSource 97=(7:Fin 27) from rfl,
    show sourceWord 7=[(1,true)] from rfl,show groupPowers 97=(-2, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_98 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 98))*u^(groupPowers 98).1*v^(groupPowers 98).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 98)) := by
  simp only [show gridGroupSource 98=(7:Fin 27) from rfl,
    show sourceWord 7=[(1,true)] from rfl,show groupPowers 98=(0, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_99 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 99))*u^(groupPowers 99).1*v^(groupPowers 99).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 99)) := by
  simp only [show gridGroupSource 99=(7:Fin 27) from rfl,
    show sourceWord 7=[(1,true)] from rfl,show groupPowers 99=(-2, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_100 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 100))*u^(groupPowers 100).1*v^(groupPowers 100).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 100)) := by
  simp only [show gridGroupSource 100=(18:Fin 27) from rfl,
    show sourceWord 18=[(2,false),(0,true),(0,true)] from rfl,show groupPowers 100=(3, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_101 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 101))*u^(groupPowers 101).1*v^(groupPowers 101).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 101)) := by
  simp only [show gridGroupSource 101=(17:Fin 27) from rfl,
    show sourceWord 17=[(2,false),(0,true)] from rfl,show groupPowers 101=(1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_102 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 102))*u^(groupPowers 102).1*v^(groupPowers 102).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 102)) := by
  simp only [show gridGroupSource 102=(17:Fin 27) from rfl,
    show sourceWord 17=[(2,false),(0,true)] from rfl,show groupPowers 102=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_103 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 103))*u^(groupPowers 103).1*v^(groupPowers 103).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 103)) := by
  simp only [show gridGroupSource 103=(17:Fin 27) from rfl,
    show sourceWord 17=[(2,false),(0,true)] from rfl,show groupPowers 103=(-1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_104 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 104))*u^(groupPowers 104).1*v^(groupPowers 104).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 104)) := by
  simp only [show gridGroupSource 104=(6:Fin 27) from rfl,
    show sourceWord 6=[(1,false),(2,false),(0,true)] from rfl,show groupPowers 104=(1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_105 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 105))*u^(groupPowers 105).1*v^(groupPowers 105).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 105)) := by
  simp only [show gridGroupSource 105=(6:Fin 27) from rfl,
    show sourceWord 6=[(1,false),(2,false),(0,true)] from rfl,show groupPowers 105=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_106 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 106))*u^(groupPowers 106).1*v^(groupPowers 106).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 106)) := by
  simp only [show gridGroupSource 106=(6:Fin 27) from rfl,
    show sourceWord 6=[(1,false),(2,false),(0,true)] from rfl,show groupPowers 106=(-1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_107 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 107))*u^(groupPowers 107).1*v^(groupPowers 107).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 107)) := by
  simp only [show gridGroupSource 107=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 107=(3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_108 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 108))*u^(groupPowers 108).1*v^(groupPowers 108).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 108)) := by
  simp only [show gridGroupSource 108=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 108=(1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_109 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 109))*u^(groupPowers 109).1*v^(groupPowers 109).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 109)) := by
  simp only [show gridGroupSource 109=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 109=(3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_110 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 110))*u^(groupPowers 110).1*v^(groupPowers 110).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 110)) := by
  simp only [show gridGroupSource 110=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 110=(-1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_111 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 111))*u^(groupPowers 111).1*v^(groupPowers 111).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 111)) := by
  simp only [show gridGroupSource 111=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 111=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_112 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 112))*u^(groupPowers 112).1*v^(groupPowers 112).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 112)) := by
  simp only [show gridGroupSource 112=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 112=(-3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_113 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 113))*u^(groupPowers 113).1*v^(groupPowers 113).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 113)) := by
  simp only [show gridGroupSource 113=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 113=(3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_114 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 114))*u^(groupPowers 114).1*v^(groupPowers 114).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 114)) := by
  simp only [show gridGroupSource 114=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 114=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_115 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 115))*u^(groupPowers 115).1*v^(groupPowers 115).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 115)) := by
  simp only [show gridGroupSource 115=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 115=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_116 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 116))*u^(groupPowers 116).1*v^(groupPowers 116).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 116)) := by
  simp only [show gridGroupSource 116=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 116=(-3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_117 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 117))*u^(groupPowers 117).1*v^(groupPowers 117).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 117)) := by
  simp only [show gridGroupSource 117=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 117=(-1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_118 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 118))*u^(groupPowers 118).1*v^(groupPowers 118).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 118)) := by
  simp only [show gridGroupSource 118=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 118=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_119 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 119))*u^(groupPowers 119).1*v^(groupPowers 119).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 119)) := by
  simp only [show gridGroupSource 119=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 119=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_120 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 120))*u^(groupPowers 120).1*v^(groupPowers 120).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 120)) := by
  simp only [show gridGroupSource 120=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 120=(-1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_121 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 121))*u^(groupPowers 121).1*v^(groupPowers 121).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 121)) := by
  simp only [show gridGroupSource 121=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 121=(-3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_122 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 122))*u^(groupPowers 122).1*v^(groupPowers 122).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 122)) := by
  simp only [show gridGroupSource 122=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 122=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_123 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 123))*u^(groupPowers 123).1*v^(groupPowers 123).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 123)) := by
  simp only [show gridGroupSource 123=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 123=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_124 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 124))*u^(groupPowers 124).1*v^(groupPowers 124).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 124)) := by
  simp only [show gridGroupSource 124=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 124=(3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_125 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 125))*u^(groupPowers 125).1*v^(groupPowers 125).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 125)) := by
  simp only [show gridGroupSource 125=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 125=(-3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_126 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 126))*u^(groupPowers 126).1*v^(groupPowers 126).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 126)) := by
  simp only [show gridGroupSource 126=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 126=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_127 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 127))*u^(groupPowers 127).1*v^(groupPowers 127).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 127)) := by
  simp only [show gridGroupSource 127=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 127=(-1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_128 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 128))*u^(groupPowers 128).1*v^(groupPowers 128).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 128)) := by
  simp only [show gridGroupSource 128=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 128=(3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_129 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 129))*u^(groupPowers 129).1*v^(groupPowers 129).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 129)) := by
  simp only [show gridGroupSource 129=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 129=(1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_130 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 130))*u^(groupPowers 130).1*v^(groupPowers 130).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 130)) := by
  simp only [show gridGroupSource 130=(12:Fin 27) from rfl,
    show sourceWord 12=[(1,true),(1,true),(2,false)] from rfl,show groupPowers 130=(3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_131 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 131))*u^(groupPowers 131).1*v^(groupPowers 131).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 131)) := by
  simp only [show gridGroupSource 131=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 131=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_132 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 132))*u^(groupPowers 132).1*v^(groupPowers 132).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 132)) := by
  simp only [show gridGroupSource 132=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 132=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_133 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 133))*u^(groupPowers 133).1*v^(groupPowers 133).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 133)) := by
  simp only [show gridGroupSource 133=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 133=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_134 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 134))*u^(groupPowers 134).1*v^(groupPowers 134).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 134)) := by
  simp only [show gridGroupSource 134=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 134=(-3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_135 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 135))*u^(groupPowers 135).1*v^(groupPowers 135).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 135)) := by
  simp only [show gridGroupSource 135=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 135=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_136 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 136))*u^(groupPowers 136).1*v^(groupPowers 136).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 136)) := by
  simp only [show gridGroupSource 136=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 136=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_137 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 137))*u^(groupPowers 137).1*v^(groupPowers 137).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 137)) := by
  simp only [show gridGroupSource 137=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 137=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_138 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 138))*u^(groupPowers 138).1*v^(groupPowers 138).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 138)) := by
  simp only [show gridGroupSource 138=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 138=(-3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_139 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 139))*u^(groupPowers 139).1*v^(groupPowers 139).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 139)) := by
  simp only [show gridGroupSource 139=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 139=(3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_140 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 140))*u^(groupPowers 140).1*v^(groupPowers 140).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 140)) := by
  simp only [show gridGroupSource 140=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 140=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_141 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 141))*u^(groupPowers 141).1*v^(groupPowers 141).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 141)) := by
  simp only [show gridGroupSource 141=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 141=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_142 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 142))*u^(groupPowers 142).1*v^(groupPowers 142).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 142)) := by
  simp only [show gridGroupSource 142=(13:Fin 27) from rfl,
    show sourceWord 13=[(1,true),(2,false)] from rfl,show groupPowers 142=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_143 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 143))*u^(groupPowers 143).1*v^(groupPowers 143).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 143)) := by
  simp only [show gridGroupSource 143=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 143=(3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_144 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 144))*u^(groupPowers 144).1*v^(groupPowers 144).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 144)) := by
  simp only [show gridGroupSource 144=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 144=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_145 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 145))*u^(groupPowers 145).1*v^(groupPowers 145).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 145)) := by
  simp only [show gridGroupSource 145=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 145=(3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_146 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 146))*u^(groupPowers 146).1*v^(groupPowers 146).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 146)) := by
  simp only [show gridGroupSource 146=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 146=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_147 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 147))*u^(groupPowers 147).1*v^(groupPowers 147).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 147)) := by
  simp only [show gridGroupSource 147=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 147=(1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_148 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 148))*u^(groupPowers 148).1*v^(groupPowers 148).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 148)) := by
  simp only [show gridGroupSource 148=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 148=(-1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_149 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 149))*u^(groupPowers 149).1*v^(groupPowers 149).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 149)) := by
  simp only [show gridGroupSource 149=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 149=(-3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_150 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 150))*u^(groupPowers 150).1*v^(groupPowers 150).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 150)) := by
  simp only [show gridGroupSource 150=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 150=(3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_151 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 151))*u^(groupPowers 151).1*v^(groupPowers 151).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 151)) := by
  simp only [show gridGroupSource 151=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 151=(-1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_152 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 152))*u^(groupPowers 152).1*v^(groupPowers 152).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 152)) := by
  simp only [show gridGroupSource 152=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 152=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_153 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 153))*u^(groupPowers 153).1*v^(groupPowers 153).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 153)) := by
  simp only [show gridGroupSource 153=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 153=(3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_154 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 154))*u^(groupPowers 154).1*v^(groupPowers 154).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 154)) := by
  simp only [show gridGroupSource 154=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 154=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_155 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 155))*u^(groupPowers 155).1*v^(groupPowers 155).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 155)) := by
  simp only [show gridGroupSource 155=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 155=(1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_156 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 156))*u^(groupPowers 156).1*v^(groupPowers 156).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 156)) := by
  simp only [show gridGroupSource 156=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 156=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_157 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 157))*u^(groupPowers 157).1*v^(groupPowers 157).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 157)) := by
  simp only [show gridGroupSource 157=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 157=(-1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_158 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 158))*u^(groupPowers 158).1*v^(groupPowers 158).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 158)) := by
  simp only [show gridGroupSource 158=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 158=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_159 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 159))*u^(groupPowers 159).1*v^(groupPowers 159).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 159)) := by
  simp only [show gridGroupSource 159=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 159=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_160 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 160))*u^(groupPowers 160).1*v^(groupPowers 160).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 160)) := by
  simp only [show gridGroupSource 160=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 160=(-1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_161 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 161))*u^(groupPowers 161).1*v^(groupPowers 161).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 161)) := by
  simp only [show gridGroupSource 161=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 161=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_162 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 162))*u^(groupPowers 162).1*v^(groupPowers 162).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 162)) := by
  simp only [show gridGroupSource 162=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 162=(1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_163 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 163))*u^(groupPowers 163).1*v^(groupPowers 163).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 163)) := by
  simp only [show gridGroupSource 163=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 163=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_164 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 164))*u^(groupPowers 164).1*v^(groupPowers 164).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 164)) := by
  simp only [show gridGroupSource 164=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 164=(3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_165 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 165))*u^(groupPowers 165).1*v^(groupPowers 165).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 165)) := by
  simp only [show gridGroupSource 165=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 165=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_166 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 166))*u^(groupPowers 166).1*v^(groupPowers 166).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 166)) := by
  simp only [show gridGroupSource 166=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 166=(-1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_167 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 167))*u^(groupPowers 167).1*v^(groupPowers 167).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 167)) := by
  simp only [show gridGroupSource 167=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 167=(-3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_168 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 168))*u^(groupPowers 168).1*v^(groupPowers 168).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 168)) := by
  simp only [show gridGroupSource 168=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 168=(-1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_169 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 169))*u^(groupPowers 169).1*v^(groupPowers 169).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 169)) := by
  simp only [show gridGroupSource 169=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 169=(-3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_170 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 170))*u^(groupPowers 170).1*v^(groupPowers 170).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 170)) := by
  simp only [show gridGroupSource 170=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 170=(1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_171 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 171))*u^(groupPowers 171).1*v^(groupPowers 171).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 171)) := by
  simp only [show gridGroupSource 171=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 171=(3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_172 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 172))*u^(groupPowers 172).1*v^(groupPowers 172).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 172)) := by
  simp only [show gridGroupSource 172=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 172=(-3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_173 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 173))*u^(groupPowers 173).1*v^(groupPowers 173).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 173)) := by
  simp only [show gridGroupSource 173=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 173=(-1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_174 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 174))*u^(groupPowers 174).1*v^(groupPowers 174).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 174)) := by
  simp only [show gridGroupSource 174=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 174=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_175 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 175))*u^(groupPowers 175).1*v^(groupPowers 175).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 175)) := by
  simp only [show gridGroupSource 175=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 175=(-3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_176 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 176))*u^(groupPowers 176).1*v^(groupPowers 176).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 176)) := by
  simp only [show gridGroupSource 176=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 176=(-1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_177 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 177))*u^(groupPowers 177).1*v^(groupPowers 177).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 177)) := by
  simp only [show gridGroupSource 177=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 177=(3, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_178 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 178))*u^(groupPowers 178).1*v^(groupPowers 178).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 178)) := by
  simp only [show gridGroupSource 178=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 178=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_179 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 179))*u^(groupPowers 179).1*v^(groupPowers 179).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 179)) := by
  simp only [show gridGroupSource 179=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 179=(3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_180 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 180))*u^(groupPowers 180).1*v^(groupPowers 180).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 180)) := by
  simp only [show gridGroupSource 180=(14:Fin 27) from rfl,
    show sourceWord 14=[(2,false)] from rfl,show groupPowers 180=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_181 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 181))*u^(groupPowers 181).1*v^(groupPowers 181).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 181)) := by
  simp only [show gridGroupSource 181=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 181=(3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_182 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 182))*u^(groupPowers 182).1*v^(groupPowers 182).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 182)) := by
  simp only [show gridGroupSource 182=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 182=(1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_183 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 183))*u^(groupPowers 183).1*v^(groupPowers 183).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 183)) := by
  simp only [show gridGroupSource 183=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 183=(-1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_184 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 184))*u^(groupPowers 184).1*v^(groupPowers 184).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 184)) := by
  simp only [show gridGroupSource 184=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 184=(-3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_185 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 185))*u^(groupPowers 185).1*v^(groupPowers 185).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 185)) := by
  simp only [show gridGroupSource 185=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 185=(-1, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_186 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 186))*u^(groupPowers 186).1*v^(groupPowers 186).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 186)) := by
  simp only [show gridGroupSource 186=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 186=(-3, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_187 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 187))*u^(groupPowers 187).1*v^(groupPowers 187).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 187)) := by
  simp only [show gridGroupSource 187=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 187=(-3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_188 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 188))*u^(groupPowers 188).1*v^(groupPowers 188).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 188)) := by
  simp only [show gridGroupSource 188=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 188=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_189 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 189))*u^(groupPowers 189).1*v^(groupPowers 189).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 189)) := by
  simp only [show gridGroupSource 189=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 189=(-1, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_190 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 190))*u^(groupPowers 190).1*v^(groupPowers 190).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 190)) := by
  simp only [show gridGroupSource 190=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 190=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_191 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 191))*u^(groupPowers 191).1*v^(groupPowers 191).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 191)) := by
  simp only [show gridGroupSource 191=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 191=(3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_192 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 192))*u^(groupPowers 192).1*v^(groupPowers 192).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 192)) := by
  simp only [show gridGroupSource 192=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 192=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_193 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 193))*u^(groupPowers 193).1*v^(groupPowers 193).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 193)) := by
  simp only [show gridGroupSource 193=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 193=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_194 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 194))*u^(groupPowers 194).1*v^(groupPowers 194).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 194)) := by
  simp only [show gridGroupSource 194=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 194=(1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_195 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 195))*u^(groupPowers 195).1*v^(groupPowers 195).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 195)) := by
  simp only [show gridGroupSource 195=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 195=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_196 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 196))*u^(groupPowers 196).1*v^(groupPowers 196).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 196)) := by
  simp only [show gridGroupSource 196=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 196=(-1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_197 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 197))*u^(groupPowers 197).1*v^(groupPowers 197).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 197)) := by
  simp only [show gridGroupSource 197=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 197=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_198 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 198))*u^(groupPowers 198).1*v^(groupPowers 198).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 198)) := by
  simp only [show gridGroupSource 198=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 198=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_199 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 199))*u^(groupPowers 199).1*v^(groupPowers 199).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 199)) := by
  simp only [show gridGroupSource 199=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 199=(-1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_200 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 200))*u^(groupPowers 200).1*v^(groupPowers 200).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 200)) := by
  simp only [show gridGroupSource 200=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 200=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_201 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 201))*u^(groupPowers 201).1*v^(groupPowers 201).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 201)) := by
  simp only [show gridGroupSource 201=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 201=(1, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_202 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 202))*u^(groupPowers 202).1*v^(groupPowers 202).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 202)) := by
  simp only [show gridGroupSource 202=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 202=(-3, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_203 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 203))*u^(groupPowers 203).1*v^(groupPowers 203).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 203)) := by
  simp only [show gridGroupSource 203=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 203=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_204 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 204))*u^(groupPowers 204).1*v^(groupPowers 204).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 204)) := by
  simp only [show gridGroupSource 204=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 204=(3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_205 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 205))*u^(groupPowers 205).1*v^(groupPowers 205).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 205)) := by
  simp only [show gridGroupSource 205=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 205=(-3, 2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_206 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 206))*u^(groupPowers 206).1*v^(groupPowers 206).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 206)) := by
  simp only [show gridGroupSource 206=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 206=(-3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_207 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 207))*u^(groupPowers 207).1*v^(groupPowers 207).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 207)) := by
  simp only [show gridGroupSource 207=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 207=(3, -2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_208 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 208))*u^(groupPowers 208).1*v^(groupPowers 208).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 208)) := by
  simp only [show gridGroupSource 208=(4:Fin 27) from rfl,
    show sourceWord 4=[(1,false),(2,false)] from rfl,show groupPowers 208=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_209 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 209))*u^(groupPowers 209).1*v^(groupPowers 209).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 209)) := by
  simp only [show gridGroupSource 209=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,show groupPowers 209=(1, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_210 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 210))*u^(groupPowers 210).1*v^(groupPowers 210).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 210)) := by
  simp only [show gridGroupSource 210=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,show groupPowers 210=(1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_211 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 211))*u^(groupPowers 211).1*v^(groupPowers 211).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 211)) := by
  simp only [show gridGroupSource 211=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,show groupPowers 211=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_212 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 212))*u^(groupPowers 212).1*v^(groupPowers 212).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 212)) := by
  simp only [show gridGroupSource 212=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,show groupPowers 212=(-3, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_213 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 213))*u^(groupPowers 213).1*v^(groupPowers 213).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 213)) := by
  simp only [show gridGroupSource 213=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,show groupPowers 213=(-1, 0, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_214 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 214))*u^(groupPowers 214).1*v^(groupPowers 214).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 214)) := by
  simp only [show gridGroupSource 214=(3:Fin 27) from rfl,
    show sourceWord 3=[(1,false),(1,false),(2,false)] from rfl,show groupPowers 214=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_215 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 215))*u^(groupPowers 215).1*v^(groupPowers 215).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 215)) := by
  simp only [show gridGroupSource 215=(15:Fin 27) from rfl,
    show sourceWord 15=[(2,false),(0,false)] from rfl,show groupPowers 215=(-1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_216 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 216))*u^(groupPowers 216).1*v^(groupPowers 216).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 216)) := by
  simp only [show gridGroupSource 216=(15:Fin 27) from rfl,
    show sourceWord 15=[(2,false),(0,false)] from rfl,show groupPowers 216=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_217 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 217))*u^(groupPowers 217).1*v^(groupPowers 217).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 217)) := by
  simp only [show gridGroupSource 217=(15:Fin 27) from rfl,
    show sourceWord 15=[(2,false),(0,false)] from rfl,show groupPowers 217=(1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_218 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 218))*u^(groupPowers 218).1*v^(groupPowers 218).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 218)) := by
  simp only [show gridGroupSource 218=(5:Fin 27) from rfl,
    show sourceWord 5=[(1,false),(2,false),(0,false)] from rfl,show groupPowers 218=(-1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_219 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 219))*u^(groupPowers 219).1*v^(groupPowers 219).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 219)) := by
  simp only [show gridGroupSource 219=(5:Fin 27) from rfl,
    show sourceWord 5=[(1,false),(2,false),(0,false)] from rfl,show groupPowers 219=(3, 0, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_220 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 220))*u^(groupPowers 220).1*v^(groupPowers 220).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 220)) := by
  simp only [show gridGroupSource 220=(5:Fin 27) from rfl,
    show sourceWord 5=[(1,false),(2,false),(0,false)] from rfl,show groupPowers 220=(1, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_221 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 221))*u^(groupPowers 221).1*v^(groupPowers 221).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 221)) := by
  simp only [show gridGroupSource 221=(16:Fin 27) from rfl,
    show sourceWord 16=[(2,false),(0,false),(0,false)] from rfl,show groupPowers 221=(3, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_222 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 222))*u^(groupPowers 222).1*v^(groupPowers 222).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 222)) := by
  simp only [show gridGroupSource 222=(19:Fin 27) from rfl,
    show sourceWord 19=[(2,true),(1,true)] from rfl,show groupPowers 222=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_223 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 223))*u^(groupPowers 223).1*v^(groupPowers 223).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 223)) := by
  simp only [show gridGroupSource 223=(19:Fin 27) from rfl,
    show sourceWord 19=[(2,true),(1,true)] from rfl,show groupPowers 223=(-3, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_224 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 224))*u^(groupPowers 224).1*v^(groupPowers 224).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 224)) := by
  simp only [show gridGroupSource 224=(26:Fin 27) from rfl,
    show sourceWord 26=[(3,false),(2,false),(0,true)] from rfl,show groupPowers 224=(2, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_225 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 225))*u^(groupPowers 225).1*v^(groupPowers 225).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 225)) := by
  simp only [show gridGroupSource 225=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,show groupPowers 225=(-2, 2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_226 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 226))*u^(groupPowers 226).1*v^(groupPowers 226).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 226)) := by
  simp only [show gridGroupSource 226=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,show groupPowers 226=(-2, 2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_227 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 227))*u^(groupPowers 227).1*v^(groupPowers 227).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 227)) := by
  simp only [show gridGroupSource 227=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,show groupPowers 227=(2, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_228 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 228))*u^(groupPowers 228).1*v^(groupPowers 228).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 228)) := by
  simp only [show gridGroupSource 228=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,show groupPowers 228=(2, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_229 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 229))*u^(groupPowers 229).1*v^(groupPowers 229).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 229)) := by
  simp only [show gridGroupSource 229=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,show groupPowers 229=(-2, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_230 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 230))*u^(groupPowers 230).1*v^(groupPowers 230).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 230)) := by
  simp only [show gridGroupSource 230=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,show groupPowers 230=(2, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_231 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 231))*u^(groupPowers 231).1*v^(groupPowers 231).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 231)) := by
  simp only [show gridGroupSource 231=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,show groupPowers 231=(-2, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_232 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 232))*u^(groupPowers 232).1*v^(groupPowers 232).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 232)) := by
  simp only [show gridGroupSource 232=(25:Fin 27) from rfl,
    show sourceWord 25=[(3,false),(2,false)] from rfl,show groupPowers 232=(-2, -2, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_233 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 233))*u^(groupPowers 233).1*v^(groupPowers 233).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 233)) := by
  simp only [show gridGroupSource 233=(20:Fin 27) from rfl,
    show sourceWord 20=[(2,true),(1,true),(2,false)] from rfl,show groupPowers 233=(0, -2, 0, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

theorem word_scale_sign_234 (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource 234))*u^(groupPowers 234).1*v^(groupPowers 234).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource 234)) := by
  simp only [show gridGroupSource 234=(20:Fin 27) from rfl,
    show sourceWord 20=[(2,true),(1,true),(2,false)] from rfl,show groupPowers 234=(0, 2, 0, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    norm_num [gridWordSign,gridBaseSign]

end SmallLevelTwentySixGrid
