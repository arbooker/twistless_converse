module
public import SmallLevelTwentySixGridRateDataV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGrid

theorem groupRate_factor_0 :
    gridGroupRate 0=(2:ℚ)^(groupPowers 0).1*(3:ℚ)^(groupPowers 0).2.1*
      (13:ℚ)^(groupPowers 0).2.2.1*(5:ℚ)^(groupPowers 0).2.2.2 := by
  simp only [show gridGroupRate 0=(104:ℚ) from rfl,
      show groupPowers 0=(3, 0, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_1 :
    gridGroupRate 1=(2:ℚ)^(groupPowers 1).1*(3:ℚ)^(groupPowers 1).2.1*
      (13:ℚ)^(groupPowers 1).2.2.1*(5:ℚ)^(groupPowers 1).2.2.2 := by
  simp only [show gridGroupRate 1=((1800/13):ℚ) from rfl,
      show groupPowers 1=(3, 2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_2 :
    gridGroupRate 2=(2:ℚ)^(groupPowers 2).1*(3:ℚ)^(groupPowers 2).2.1*
      (13:ℚ)^(groupPowers 2).2.2.1*(5:ℚ)^(groupPowers 2).2.2.2 := by
  simp only [show gridGroupRate 2=((325/2):ℚ) from rfl,
      show groupPowers 2=(-1, 0, 1, 2) from rfl]
  norm_num

theorem groupRate_factor_3 :
    gridGroupRate 3=(2:ℚ)^(groupPowers 3).1*(3:ℚ)^(groupPowers 3).2.1*
      (13:ℚ)^(groupPowers 3).2.2.1*(5:ℚ)^(groupPowers 3).2.2.2 := by
  simp only [show gridGroupRate 3=(26:ℚ) from rfl,
      show groupPowers 3=(1, 0, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_4 :
    gridGroupRate 4=(2:ℚ)^(groupPowers 4).1*(3:ℚ)^(groupPowers 4).2.1*
      (13:ℚ)^(groupPowers 4).2.2.1*(5:ℚ)^(groupPowers 4).2.2.2 := by
  simp only [show gridGroupRate 4=((450/13):ℚ) from rfl,
      show groupPowers 4=(1, 2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_5 :
    gridGroupRate 5=(2:ℚ)^(groupPowers 5).1*(3:ℚ)^(groupPowers 5).2.1*
      (13:ℚ)^(groupPowers 5).2.2.1*(5:ℚ)^(groupPowers 5).2.2.2 := by
  simp only [show gridGroupRate 5=((936/25):ℚ) from rfl,
      show groupPowers 5=(3, 2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_6 :
    gridGroupRate 6=(2:ℚ)^(groupPowers 6).1*(3:ℚ)^(groupPowers 6).2.1*
      (13:ℚ)^(groupPowers 6).2.2.1*(5:ℚ)^(groupPowers 6).2.2.2 := by
  simp only [show gridGroupRate 6=((325/8):ℚ) from rfl,
      show groupPowers 6=(-3, 0, 1, 2) from rfl]
  norm_num

theorem groupRate_factor_7 :
    gridGroupRate 7=(2:ℚ)^(groupPowers 7).1*(3:ℚ)^(groupPowers 7).2.1*
      (13:ℚ)^(groupPowers 7).2.2.1*(5:ℚ)^(groupPowers 7).2.2.2 := by
  simp only [show gridGroupRate 7=((117/2):ℚ) from rfl,
      show groupPowers 7=(-1, 2, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_8 :
    gridGroupRate 8=(2:ℚ)^(groupPowers 8).1*(3:ℚ)^(groupPowers 8).2.1*
      (13:ℚ)^(groupPowers 8).2.2.1*(5:ℚ)^(groupPowers 8).2.2.2 := by
  simp only [show gridGroupRate 8=((650/9):ℚ) from rfl,
      show groupPowers 8=(1, -2, 1, 2) from rfl]
  norm_num

theorem groupRate_factor_9 :
    gridGroupRate 9=(2:ℚ)^(groupPowers 9).1*(3:ℚ)^(groupPowers 9).2.1*
      (13:ℚ)^(groupPowers 9).2.2.1*(5:ℚ)^(groupPowers 9).2.2.2 := by
  simp only [show gridGroupRate 9=((1/23400):ℚ) from rfl,
      show groupPowers 9=(-3, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_10 :
    gridGroupRate 10=(2:ℚ)^(groupPowers 10).1*(3:ℚ)^(groupPowers 10).2.1*
      (13:ℚ)^(groupPowers 10).2.2.1*(5:ℚ)^(groupPowers 10).2.2.2 := by
  simp only [show gridGroupRate 10=((1/5850):ℚ) from rfl,
      show groupPowers 10=(-1, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_11 :
    gridGroupRate 11=(2:ℚ)^(groupPowers 11).1*(3:ℚ)^(groupPowers 11).2.1*
      (13:ℚ)^(groupPowers 11).2.2.1*(5:ℚ)^(groupPowers 11).2.2.2 := by
  simp only [show gridGroupRate 11=((1/2600):ℚ) from rfl,
      show groupPowers 11=(-3, 0, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_12 :
    gridGroupRate 12=(2:ℚ)^(groupPowers 12).1*(3:ℚ)^(groupPowers 12).2.1*
      (13:ℚ)^(groupPowers 12).2.2.1*(5:ℚ)^(groupPowers 12).2.2.2 := by
  simp only [show gridGroupRate 12=((2/2925):ℚ) from rfl,
      show groupPowers 12=(1, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_13 :
    gridGroupRate 13=(2:ℚ)^(groupPowers 13).1*(3:ℚ)^(groupPowers 13).2.1*
      (13:ℚ)^(groupPowers 13).2.2.1*(5:ℚ)^(groupPowers 13).2.2.2 := by
  simp only [show gridGroupRate 13=((1/936):ℚ) from rfl,
      show groupPowers 13=(-3, -2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_14 :
    gridGroupRate 14=(2:ℚ)^(groupPowers 14).1*(3:ℚ)^(groupPowers 14).2.1*
      (13:ℚ)^(groupPowers 14).2.2.1*(5:ℚ)^(groupPowers 14).2.2.2 := by
  simp only [show gridGroupRate 14=((1/650):ℚ) from rfl,
      show groupPowers 14=(-1, 0, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_15 :
    gridGroupRate 15=(2:ℚ)^(groupPowers 15).1*(3:ℚ)^(groupPowers 15).2.1*
      (13:ℚ)^(groupPowers 15).2.2.1*(5:ℚ)^(groupPowers 15).2.2.2 := by
  simp only [show gridGroupRate 15=((8/2925):ℚ) from rfl,
      show groupPowers 15=(3, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_16 :
    gridGroupRate 16=(2:ℚ)^(groupPowers 16).1*(3:ℚ)^(groupPowers 16).2.1*
      (13:ℚ)^(groupPowers 16).2.2.1*(5:ℚ)^(groupPowers 16).2.2.2 := by
  simp only [show gridGroupRate 16=((9/2600):ℚ) from rfl,
      show groupPowers 16=(-3, 2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_17 :
    gridGroupRate 17=(2:ℚ)^(groupPowers 17).1*(3:ℚ)^(groupPowers 17).2.1*
      (13:ℚ)^(groupPowers 17).2.2.1*(5:ℚ)^(groupPowers 17).2.2.2 := by
  simp only [show gridGroupRate 17=((1/234):ℚ) from rfl,
      show groupPowers 17=(-1, -2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_18 :
    gridGroupRate 18=(2:ℚ)^(groupPowers 18).1*(3:ℚ)^(groupPowers 18).2.1*
      (13:ℚ)^(groupPowers 18).2.2.1*(5:ℚ)^(groupPowers 18).2.2.2 := by
  simp only [show gridGroupRate 18=((2/325):ℚ) from rfl,
      show groupPowers 18=(1, 0, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_19 :
    gridGroupRate 19=(2:ℚ)^(groupPowers 19).1*(3:ℚ)^(groupPowers 19).2.1*
      (13:ℚ)^(groupPowers 19).2.2.1*(5:ℚ)^(groupPowers 19).2.2.2 := by
  simp only [show gridGroupRate 19=((13/1800):ℚ) from rfl,
      show groupPowers 19=(-3, -2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_20 :
    gridGroupRate 20=(2:ℚ)^(groupPowers 20).1*(3:ℚ)^(groupPowers 20).2.1*
      (13:ℚ)^(groupPowers 20).2.2.1*(5:ℚ)^(groupPowers 20).2.2.2 := by
  simp only [show gridGroupRate 20=((1/104):ℚ) from rfl,
      show groupPowers 20=(-3, 0, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_21 :
    gridGroupRate 21=(2:ℚ)^(groupPowers 21).1*(3:ℚ)^(groupPowers 21).2.1*
      (13:ℚ)^(groupPowers 21).2.2.1*(5:ℚ)^(groupPowers 21).2.2.2 := by
  simp only [show gridGroupRate 21=((9/650):ℚ) from rfl,
      show groupPowers 21=(-1, 2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_22 :
    gridGroupRate 22=(2:ℚ)^(groupPowers 22).1*(3:ℚ)^(groupPowers 22).2.1*
      (13:ℚ)^(groupPowers 22).2.2.1*(5:ℚ)^(groupPowers 22).2.2.2 := by
  simp only [show gridGroupRate 22=((2/117):ℚ) from rfl,
      show groupPowers 22=(1, -2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_23 :
    gridGroupRate 23=(2:ℚ)^(groupPowers 23).1*(3:ℚ)^(groupPowers 23).2.1*
      (13:ℚ)^(groupPowers 23).2.2.1*(5:ℚ)^(groupPowers 23).2.2.2 := by
  simp only [show gridGroupRate 23=((8/325):ℚ) from rfl,
      show groupPowers 23=(3, 0, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_24 :
    gridGroupRate 24=(2:ℚ)^(groupPowers 24).1*(3:ℚ)^(groupPowers 24).2.1*
      (13:ℚ)^(groupPowers 24).2.2.1*(5:ℚ)^(groupPowers 24).2.2.2 := by
  simp only [show gridGroupRate 24=((25/936):ℚ) from rfl,
      show groupPowers 24=(-3, -2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_25 :
    gridGroupRate 25=(2:ℚ)^(groupPowers 25).1*(3:ℚ)^(groupPowers 25).2.1*
      (13:ℚ)^(groupPowers 25).2.2.1*(5:ℚ)^(groupPowers 25).2.2.2 := by
  simp only [show gridGroupRate 25=((13/450):ℚ) from rfl,
      show groupPowers 25=(-1, -2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_26 :
    gridGroupRate 26=(2:ℚ)^(groupPowers 26).1*(3:ℚ)^(groupPowers 26).2.1*
      (13:ℚ)^(groupPowers 26).2.2.1*(5:ℚ)^(groupPowers 26).2.2.2 := by
  simp only [show gridGroupRate 26=((1/26):ℚ) from rfl,
      show groupPowers 26=(-1, 0, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_27 :
    gridGroupRate 27=(2:ℚ)^(groupPowers 27).1*(3:ℚ)^(groupPowers 27).2.1*
      (13:ℚ)^(groupPowers 27).2.2.1*(5:ℚ)^(groupPowers 27).2.2.2 := by
  simp only [show gridGroupRate 27=((18/325):ℚ) from rfl,
      show groupPowers 27=(1, 2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_28 :
    gridGroupRate 28=(2:ℚ)^(groupPowers 28).1*(3:ℚ)^(groupPowers 28).2.1*
      (13:ℚ)^(groupPowers 28).2.2.1*(5:ℚ)^(groupPowers 28).2.2.2 := by
  simp only [show gridGroupRate 28=((13/200):ℚ) from rfl,
      show groupPowers 28=(-3, 0, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_29 :
    gridGroupRate 29=(2:ℚ)^(groupPowers 29).1*(3:ℚ)^(groupPowers 29).2.1*
      (13:ℚ)^(groupPowers 29).2.2.1*(5:ℚ)^(groupPowers 29).2.2.2 := by
  simp only [show gridGroupRate 29=((8/117):ℚ) from rfl,
      show groupPowers 29=(3, -2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_30 :
    gridGroupRate 30=(2:ℚ)^(groupPowers 30).1*(3:ℚ)^(groupPowers 30).2.1*
      (13:ℚ)^(groupPowers 30).2.2.1*(5:ℚ)^(groupPowers 30).2.2.2 := by
  simp only [show gridGroupRate 30=((9/104):ℚ) from rfl,
      show groupPowers 30=(-3, 2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_31 :
    gridGroupRate 31=(2:ℚ)^(groupPowers 31).1*(3:ℚ)^(groupPowers 31).2.1*
      (13:ℚ)^(groupPowers 31).2.2.1*(5:ℚ)^(groupPowers 31).2.2.2 := by
  simp only [show gridGroupRate 31=((25/234):ℚ) from rfl,
      show groupPowers 31=(-1, -2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_32 :
    gridGroupRate 32=(2:ℚ)^(groupPowers 32).1*(3:ℚ)^(groupPowers 32).2.1*
      (13:ℚ)^(groupPowers 32).2.2.1*(5:ℚ)^(groupPowers 32).2.2.2 := by
  simp only [show gridGroupRate 32=((26/225):ℚ) from rfl,
      show groupPowers 32=(1, -2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_33 :
    gridGroupRate 33=(2:ℚ)^(groupPowers 33).1*(3:ℚ)^(groupPowers 33).2.1*
      (13:ℚ)^(groupPowers 33).2.2.1*(5:ℚ)^(groupPowers 33).2.2.2 := by
  simp only [show gridGroupRate 33=((2/13):ℚ) from rfl,
      show groupPowers 33=(1, 0, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_34 :
    gridGroupRate 34=(2:ℚ)^(groupPowers 34).1*(3:ℚ)^(groupPowers 34).2.1*
      (13:ℚ)^(groupPowers 34).2.2.1*(5:ℚ)^(groupPowers 34).2.2.2 := by
  simp only [show gridGroupRate 34=((13/72):ℚ) from rfl,
      show groupPowers 34=(-3, -2, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_35 :
    gridGroupRate 35=(2:ℚ)^(groupPowers 35).1*(3:ℚ)^(groupPowers 35).2.1*
      (13:ℚ)^(groupPowers 35).2.2.1*(5:ℚ)^(groupPowers 35).2.2.2 := by
  simp only [show gridGroupRate 35=((72/325):ℚ) from rfl,
      show groupPowers 35=(3, 2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_36 :
    gridGroupRate 36=(2:ℚ)^(groupPowers 36).1*(3:ℚ)^(groupPowers 36).2.1*
      (13:ℚ)^(groupPowers 36).2.2.1*(5:ℚ)^(groupPowers 36).2.2.2 := by
  simp only [show gridGroupRate 36=((25/104):ℚ) from rfl,
      show groupPowers 36=(-3, 0, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_37 :
    gridGroupRate 37=(2:ℚ)^(groupPowers 37).1*(3:ℚ)^(groupPowers 37).2.1*
      (13:ℚ)^(groupPowers 37).2.2.1*(5:ℚ)^(groupPowers 37).2.2.2 := by
  simp only [show gridGroupRate 37=((13/50):ℚ) from rfl,
      show groupPowers 37=(-1, 0, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_38 :
    gridGroupRate 38=(2:ℚ)^(groupPowers 38).1*(3:ℚ)^(groupPowers 38).2.1*
      (13:ℚ)^(groupPowers 38).2.2.1*(5:ℚ)^(groupPowers 38).2.2.2 := by
  simp only [show gridGroupRate 38=((9/26):ℚ) from rfl,
      show groupPowers 38=(-1, 2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_39 :
    gridGroupRate 39=(2:ℚ)^(groupPowers 39).1*(3:ℚ)^(groupPowers 39).2.1*
      (13:ℚ)^(groupPowers 39).2.2.1*(5:ℚ)^(groupPowers 39).2.2.2 := by
  simp only [show gridGroupRate 39=((50/117):ℚ) from rfl,
      show groupPowers 39=(1, -2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_40 :
    gridGroupRate 40=(2:ℚ)^(groupPowers 40).1*(3:ℚ)^(groupPowers 40).2.1*
      (13:ℚ)^(groupPowers 40).2.2.1*(5:ℚ)^(groupPowers 40).2.2.2 := by
  simp only [show gridGroupRate 40=((104/225):ℚ) from rfl,
      show groupPowers 40=(3, -2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_41 :
    gridGroupRate 41=(2:ℚ)^(groupPowers 41).1*(3:ℚ)^(groupPowers 41).2.1*
      (13:ℚ)^(groupPowers 41).2.2.1*(5:ℚ)^(groupPowers 41).2.2.2 := by
  simp only [show gridGroupRate 41=((117/200):ℚ) from rfl,
      show groupPowers 41=(-3, 2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_42 :
    gridGroupRate 42=(2:ℚ)^(groupPowers 42).1*(3:ℚ)^(groupPowers 42).2.1*
      (13:ℚ)^(groupPowers 42).2.2.1*(5:ℚ)^(groupPowers 42).2.2.2 := by
  simp only [show gridGroupRate 42=((8/13):ℚ) from rfl,
      show groupPowers 42=(3, 0, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_43 :
    gridGroupRate 43=(2:ℚ)^(groupPowers 43).1*(3:ℚ)^(groupPowers 43).2.1*
      (13:ℚ)^(groupPowers 43).2.2.1*(5:ℚ)^(groupPowers 43).2.2.2 := by
  simp only [show gridGroupRate 43=((13/18):ℚ) from rfl,
      show groupPowers 43=(-1, -2, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_44 :
    gridGroupRate 44=(2:ℚ)^(groupPowers 44).1*(3:ℚ)^(groupPowers 44).2.1*
      (13:ℚ)^(groupPowers 44).2.2.1*(5:ℚ)^(groupPowers 44).2.2.2 := by
  simp only [show gridGroupRate 44=((25/26):ℚ) from rfl,
      show groupPowers 44=(-1, 0, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_45 :
    gridGroupRate 45=(2:ℚ)^(groupPowers 45).1*(3:ℚ)^(groupPowers 45).2.1*
      (13:ℚ)^(groupPowers 45).2.2.1*(5:ℚ)^(groupPowers 45).2.2.2 := by
  simp only [show gridGroupRate 45=((26/25):ℚ) from rfl,
      show groupPowers 45=(1, 0, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_46 :
    gridGroupRate 46=(2:ℚ)^(groupPowers 46).1*(3:ℚ)^(groupPowers 46).2.1*
      (13:ℚ)^(groupPowers 46).2.2.1*(5:ℚ)^(groupPowers 46).2.2.2 := by
  simp only [show gridGroupRate 46=((18/13):ℚ) from rfl,
      show groupPowers 46=(1, 2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_47 :
    gridGroupRate 47=(2:ℚ)^(groupPowers 47).1*(3:ℚ)^(groupPowers 47).2.1*
      (13:ℚ)^(groupPowers 47).2.2.1*(5:ℚ)^(groupPowers 47).2.2.2 := by
  simp only [show gridGroupRate 47=((13/8):ℚ) from rfl,
      show groupPowers 47=(-3, 0, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_48 :
    gridGroupRate 48=(2:ℚ)^(groupPowers 48).1*(3:ℚ)^(groupPowers 48).2.1*
      (13:ℚ)^(groupPowers 48).2.2.1*(5:ℚ)^(groupPowers 48).2.2.2 := by
  simp only [show gridGroupRate 48=((200/117):ℚ) from rfl,
      show groupPowers 48=(3, -2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_49 :
    gridGroupRate 49=(2:ℚ)^(groupPowers 49).1*(3:ℚ)^(groupPowers 49).2.1*
      (13:ℚ)^(groupPowers 49).2.2.1*(5:ℚ)^(groupPowers 49).2.2.2 := by
  simp only [show gridGroupRate 49=((225/104):ℚ) from rfl,
      show groupPowers 49=(-3, 2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_50 :
    gridGroupRate 50=(2:ℚ)^(groupPowers 50).1*(3:ℚ)^(groupPowers 50).2.1*
      (13:ℚ)^(groupPowers 50).2.2.1*(5:ℚ)^(groupPowers 50).2.2.2 := by
  simp only [show gridGroupRate 50=((117/50):ℚ) from rfl,
      show groupPowers 50=(-1, 2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_51 :
    gridGroupRate 51=(2:ℚ)^(groupPowers 51).1*(3:ℚ)^(groupPowers 51).2.1*
      (13:ℚ)^(groupPowers 51).2.2.1*(5:ℚ)^(groupPowers 51).2.2.2 := by
  simp only [show gridGroupRate 51=((26/9):ℚ) from rfl,
      show groupPowers 51=(1, -2, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_52 :
    gridGroupRate 52=(2:ℚ)^(groupPowers 52).1*(3:ℚ)^(groupPowers 52).2.1*
      (13:ℚ)^(groupPowers 52).2.2.1*(5:ℚ)^(groupPowers 52).2.2.2 := by
  simp only [show gridGroupRate 52=((50/13):ℚ) from rfl,
      show groupPowers 52=(1, 0, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_53 :
    gridGroupRate 53=(2:ℚ)^(groupPowers 53).1*(3:ℚ)^(groupPowers 53).2.1*
      (13:ℚ)^(groupPowers 53).2.2.1*(5:ℚ)^(groupPowers 53).2.2.2 := by
  simp only [show gridGroupRate 53=((104/25):ℚ) from rfl,
      show groupPowers 53=(3, 0, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_54 :
    gridGroupRate 54=(2:ℚ)^(groupPowers 54).1*(3:ℚ)^(groupPowers 54).2.1*
      (13:ℚ)^(groupPowers 54).2.2.1*(5:ℚ)^(groupPowers 54).2.2.2 := by
  simp only [show gridGroupRate 54=((325/72):ℚ) from rfl,
      show groupPowers 54=(-3, -2, 1, 2) from rfl]
  norm_num

theorem groupRate_factor_55 :
    gridGroupRate 55=(2:ℚ)^(groupPowers 55).1*(3:ℚ)^(groupPowers 55).2.1*
      (13:ℚ)^(groupPowers 55).2.2.1*(5:ℚ)^(groupPowers 55).2.2.2 := by
  simp only [show gridGroupRate 55=((72/13):ℚ) from rfl,
      show groupPowers 55=(3, 2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_56 :
    gridGroupRate 56=(2:ℚ)^(groupPowers 56).1*(3:ℚ)^(groupPowers 56).2.1*
      (13:ℚ)^(groupPowers 56).2.2.1*(5:ℚ)^(groupPowers 56).2.2.2 := by
  simp only [show gridGroupRate 56=((13/2):ℚ) from rfl,
      show groupPowers 56=(-1, 0, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_57 :
    gridGroupRate 57=(2:ℚ)^(groupPowers 57).1*(3:ℚ)^(groupPowers 57).2.1*
      (13:ℚ)^(groupPowers 57).2.2.1*(5:ℚ)^(groupPowers 57).2.2.2 := by
  simp only [show gridGroupRate 57=((225/26):ℚ) from rfl,
      show groupPowers 57=(-1, 2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_58 :
    gridGroupRate 58=(2:ℚ)^(groupPowers 58).1*(3:ℚ)^(groupPowers 58).2.1*
      (13:ℚ)^(groupPowers 58).2.2.1*(5:ℚ)^(groupPowers 58).2.2.2 := by
  simp only [show gridGroupRate 58=((234/25):ℚ) from rfl,
      show groupPowers 58=(1, 2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_59 :
    gridGroupRate 59=(2:ℚ)^(groupPowers 59).1*(3:ℚ)^(groupPowers 59).2.1*
      (13:ℚ)^(groupPowers 59).2.2.1*(5:ℚ)^(groupPowers 59).2.2.2 := by
  simp only [show gridGroupRate 59=((104/9):ℚ) from rfl,
      show groupPowers 59=(3, -2, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_60 :
    gridGroupRate 60=(2:ℚ)^(groupPowers 60).1*(3:ℚ)^(groupPowers 60).2.1*
      (13:ℚ)^(groupPowers 60).2.2.1*(5:ℚ)^(groupPowers 60).2.2.2 := by
  simp only [show gridGroupRate 60=((117/8):ℚ) from rfl,
      show groupPowers 60=(-3, 2, 1, 0) from rfl]
  norm_num

theorem groupRate_factor_61 :
    gridGroupRate 61=(2:ℚ)^(groupPowers 61).1*(3:ℚ)^(groupPowers 61).2.1*
      (13:ℚ)^(groupPowers 61).2.2.1*(5:ℚ)^(groupPowers 61).2.2.2 := by
  simp only [show gridGroupRate 61=((200/13):ℚ) from rfl,
      show groupPowers 61=(3, 0, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_62 :
    gridGroupRate 62=(2:ℚ)^(groupPowers 62).1*(3:ℚ)^(groupPowers 62).2.1*
      (13:ℚ)^(groupPowers 62).2.2.1*(5:ℚ)^(groupPowers 62).2.2.2 := by
  simp only [show gridGroupRate 62=((325/18):ℚ) from rfl,
      show groupPowers 62=(-1, -2, 1, 2) from rfl]
  norm_num

theorem groupRate_factor_63 :
    gridGroupRate 63=(2:ℚ)^(groupPowers 63).1*(3:ℚ)^(groupPowers 63).2.1*
      (13:ℚ)^(groupPowers 63).2.2.1*(5:ℚ)^(groupPowers 63).2.2.2 := by
  simp only [show gridGroupRate 63=((1/234):ℚ) from rfl,
      show groupPowers 63=(-1, -2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_64 :
    gridGroupRate 64=(2:ℚ)^(groupPowers 64).1*(3:ℚ)^(groupPowers 64).2.1*
      (13:ℚ)^(groupPowers 64).2.2.1*(5:ℚ)^(groupPowers 64).2.2.2 := by
  simp only [show gridGroupRate 64=((9/2600):ℚ) from rfl,
      show groupPowers 64=(-3, 2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_65 :
    gridGroupRate 65=(2:ℚ)^(groupPowers 65).1*(3:ℚ)^(groupPowers 65).2.1*
      (13:ℚ)^(groupPowers 65).2.2.1*(5:ℚ)^(groupPowers 65).2.2.2 := by
  simp only [show gridGroupRate 65=((8/2925):ℚ) from rfl,
      show groupPowers 65=(3, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_66 :
    gridGroupRate 66=(2:ℚ)^(groupPowers 66).1*(3:ℚ)^(groupPowers 66).2.1*
      (13:ℚ)^(groupPowers 66).2.2.1*(5:ℚ)^(groupPowers 66).2.2.2 := by
  simp only [show gridGroupRate 66=((1/650):ℚ) from rfl,
      show groupPowers 66=(-1, 0, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_67 :
    gridGroupRate 67=(2:ℚ)^(groupPowers 67).1*(3:ℚ)^(groupPowers 67).2.1*
      (13:ℚ)^(groupPowers 67).2.2.1*(5:ℚ)^(groupPowers 67).2.2.2 := by
  simp only [show gridGroupRate 67=((1/936):ℚ) from rfl,
      show groupPowers 67=(-3, -2, -1, 0) from rfl]
  norm_num

theorem groupRate_factor_68 :
    gridGroupRate 68=(2:ℚ)^(groupPowers 68).1*(3:ℚ)^(groupPowers 68).2.1*
      (13:ℚ)^(groupPowers 68).2.2.1*(5:ℚ)^(groupPowers 68).2.2.2 := by
  simp only [show gridGroupRate 68=((2/2925):ℚ) from rfl,
      show groupPowers 68=(1, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_69 :
    gridGroupRate 69=(2:ℚ)^(groupPowers 69).1*(3:ℚ)^(groupPowers 69).2.1*
      (13:ℚ)^(groupPowers 69).2.2.1*(5:ℚ)^(groupPowers 69).2.2.2 := by
  simp only [show gridGroupRate 69=((1/2600):ℚ) from rfl,
      show groupPowers 69=(-3, 0, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_70 :
    gridGroupRate 70=(2:ℚ)^(groupPowers 70).1*(3:ℚ)^(groupPowers 70).2.1*
      (13:ℚ)^(groupPowers 70).2.2.1*(5:ℚ)^(groupPowers 70).2.2.2 := by
  simp only [show gridGroupRate 70=((1/5850):ℚ) from rfl,
      show groupPowers 70=(-1, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_71 :
    gridGroupRate 71=(2:ℚ)^(groupPowers 71).1*(3:ℚ)^(groupPowers 71).2.1*
      (13:ℚ)^(groupPowers 71).2.2.1*(5:ℚ)^(groupPowers 71).2.2.2 := by
  simp only [show gridGroupRate 71=((1/23400):ℚ) from rfl,
      show groupPowers 71=(-3, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_72 :
    gridGroupRate 72=(2:ℚ)^(groupPowers 72).1*(3:ℚ)^(groupPowers 72).2.1*
      (13:ℚ)^(groupPowers 72).2.2.1*(5:ℚ)^(groupPowers 72).2.2.2 := by
  simp only [show gridGroupRate 72=(900:ℚ) from rfl,
      show groupPowers 72=(2, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_73 :
    gridGroupRate 73=(2:ℚ)^(groupPowers 73).1*(3:ℚ)^(groupPowers 73).2.1*
      (13:ℚ)^(groupPowers 73).2.2.1*(5:ℚ)^(groupPowers 73).2.2.2 := by
  simp only [show gridGroupRate 73=(900:ℚ) from rfl,
      show groupPowers 73=(2, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_74 :
    gridGroupRate 74=(2:ℚ)^(groupPowers 74).1*(3:ℚ)^(groupPowers 74).2.1*
      (13:ℚ)^(groupPowers 74).2.2.1*(5:ℚ)^(groupPowers 74).2.2.2 := by
  simp only [show gridGroupRate 74=(225:ℚ) from rfl,
      show groupPowers 74=(0, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_75 :
    gridGroupRate 75=(2:ℚ)^(groupPowers 75).1*(3:ℚ)^(groupPowers 75).2.1*
      (13:ℚ)^(groupPowers 75).2.2.1*(5:ℚ)^(groupPowers 75).2.2.2 := by
  simp only [show gridGroupRate 75=(225:ℚ) from rfl,
      show groupPowers 75=(0, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_76 :
    gridGroupRate 76=(2:ℚ)^(groupPowers 76).1*(3:ℚ)^(groupPowers 76).2.1*
      (13:ℚ)^(groupPowers 76).2.2.1*(5:ℚ)^(groupPowers 76).2.2.2 := by
  simp only [show gridGroupRate 76=(100:ℚ) from rfl,
      show groupPowers 76=(2, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_77 :
    gridGroupRate 77=(2:ℚ)^(groupPowers 77).1*(3:ℚ)^(groupPowers 77).2.1*
      (13:ℚ)^(groupPowers 77).2.2.1*(5:ℚ)^(groupPowers 77).2.2.2 := by
  simp only [show gridGroupRate 77=((100/9):ℚ) from rfl,
      show groupPowers 77=(2, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_78 :
    gridGroupRate 78=(2:ℚ)^(groupPowers 78).1*(3:ℚ)^(groupPowers 78).2.1*
      (13:ℚ)^(groupPowers 78).2.2.1*(5:ℚ)^(groupPowers 78).2.2.2 := by
  simp only [show gridGroupRate 78=(225:ℚ) from rfl,
      show groupPowers 78=(0, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_79 :
    gridGroupRate 79=(2:ℚ)^(groupPowers 79).1*(3:ℚ)^(groupPowers 79).2.1*
      (13:ℚ)^(groupPowers 79).2.2.1*(5:ℚ)^(groupPowers 79).2.2.2 := by
  simp only [show gridGroupRate 79=(100:ℚ) from rfl,
      show groupPowers 79=(2, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_80 :
    gridGroupRate 80=(2:ℚ)^(groupPowers 80).1*(3:ℚ)^(groupPowers 80).2.1*
      (13:ℚ)^(groupPowers 80).2.2.1*(5:ℚ)^(groupPowers 80).2.2.2 := by
  simp only [show gridGroupRate 80=(36:ℚ) from rfl,
      show groupPowers 80=(2, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_81 :
    gridGroupRate 81=(2:ℚ)^(groupPowers 81).1*(3:ℚ)^(groupPowers 81).2.1*
      (13:ℚ)^(groupPowers 81).2.2.1*(5:ℚ)^(groupPowers 81).2.2.2 := by
  simp only [show gridGroupRate 81=((25/4):ℚ) from rfl,
      show groupPowers 81=(-2, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_82 :
    gridGroupRate 82=(2:ℚ)^(groupPowers 82).1*(3:ℚ)^(groupPowers 82).2.1*
      (13:ℚ)^(groupPowers 82).2.2.1*(5:ℚ)^(groupPowers 82).2.2.2 := by
  simp only [show gridGroupRate 82=((25/9):ℚ) from rfl,
      show groupPowers 82=(0, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_83 :
    gridGroupRate 83=(2:ℚ)^(groupPowers 83).1*(3:ℚ)^(groupPowers 83).2.1*
      (13:ℚ)^(groupPowers 83).2.2.1*(5:ℚ)^(groupPowers 83).2.2.2 := by
  simp only [show gridGroupRate 83=((36/25):ℚ) from rfl,
      show groupPowers 83=(2, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_84 :
    gridGroupRate 84=(2:ℚ)^(groupPowers 84).1*(3:ℚ)^(groupPowers 84).2.1*
      (13:ℚ)^(groupPowers 84).2.2.1*(5:ℚ)^(groupPowers 84).2.2.2 := by
  simp only [show gridGroupRate 84=((25/36):ℚ) from rfl,
      show groupPowers 84=(-2, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_85 :
    gridGroupRate 85=(2:ℚ)^(groupPowers 85).1*(3:ℚ)^(groupPowers 85).2.1*
      (13:ℚ)^(groupPowers 85).2.2.1*(5:ℚ)^(groupPowers 85).2.2.2 := by
  simp only [show gridGroupRate 85=((9/25):ℚ) from rfl,
      show groupPowers 85=(0, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_86 :
    gridGroupRate 86=(2:ℚ)^(groupPowers 86).1*(3:ℚ)^(groupPowers 86).2.1*
      (13:ℚ)^(groupPowers 86).2.2.1*(5:ℚ)^(groupPowers 86).2.2.2 := by
  simp only [show gridGroupRate 86=((4/25):ℚ) from rfl,
      show groupPowers 86=(2, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_87 :
    gridGroupRate 87=(2:ℚ)^(groupPowers 87).1*(3:ℚ)^(groupPowers 87).2.1*
      (13:ℚ)^(groupPowers 87).2.2.1*(5:ℚ)^(groupPowers 87).2.2.2 := by
  simp only [show gridGroupRate 87=((1/36):ℚ) from rfl,
      show groupPowers 87=(-2, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_88 :
    gridGroupRate 88=(2:ℚ)^(groupPowers 88).1*(3:ℚ)^(groupPowers 88).2.1*
      (13:ℚ)^(groupPowers 88).2.2.1*(5:ℚ)^(groupPowers 88).2.2.2 := by
  simp only [show gridGroupRate 88=((1/100):ℚ) from rfl,
      show groupPowers 88=(-2, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_89 :
    gridGroupRate 89=(2:ℚ)^(groupPowers 89).1*(3:ℚ)^(groupPowers 89).2.1*
      (13:ℚ)^(groupPowers 89).2.2.1*(5:ℚ)^(groupPowers 89).2.2.2 := by
  simp only [show gridGroupRate 89=((1/225):ℚ) from rfl,
      show groupPowers 89=(0, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_90 :
    gridGroupRate 90=(2:ℚ)^(groupPowers 90).1*(3:ℚ)^(groupPowers 90).2.1*
      (13:ℚ)^(groupPowers 90).2.2.1*(5:ℚ)^(groupPowers 90).2.2.2 := by
  simp only [show gridGroupRate 90=((1/900):ℚ) from rfl,
      show groupPowers 90=(-2, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_91 :
    gridGroupRate 91=(2:ℚ)^(groupPowers 91).1*(3:ℚ)^(groupPowers 91).2.1*
      (13:ℚ)^(groupPowers 91).2.2.1*(5:ℚ)^(groupPowers 91).2.2.2 := by
  simp only [show gridGroupRate 91=(225:ℚ) from rfl,
      show groupPowers 91=(0, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_92 :
    gridGroupRate 92=(2:ℚ)^(groupPowers 92).1*(3:ℚ)^(groupPowers 92).2.1*
      (13:ℚ)^(groupPowers 92).2.2.1*(5:ℚ)^(groupPowers 92).2.2.2 := by
  simp only [show gridGroupRate 92=((1/225):ℚ) from rfl,
      show groupPowers 92=(0, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_93 :
    gridGroupRate 93=(2:ℚ)^(groupPowers 93).1*(3:ℚ)^(groupPowers 93).2.1*
      (13:ℚ)^(groupPowers 93).2.2.1*(5:ℚ)^(groupPowers 93).2.2.2 := by
  simp only [show gridGroupRate 93=((1/100):ℚ) from rfl,
      show groupPowers 93=(-2, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_94 :
    gridGroupRate 94=(2:ℚ)^(groupPowers 94).1*(3:ℚ)^(groupPowers 94).2.1*
      (13:ℚ)^(groupPowers 94).2.2.1*(5:ℚ)^(groupPowers 94).2.2.2 := by
  simp only [show gridGroupRate 94=((4/25):ℚ) from rfl,
      show groupPowers 94=(2, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_95 :
    gridGroupRate 95=(2:ℚ)^(groupPowers 95).1*(3:ℚ)^(groupPowers 95).2.1*
      (13:ℚ)^(groupPowers 95).2.2.1*(5:ℚ)^(groupPowers 95).2.2.2 := by
  simp only [show gridGroupRate 95=(100:ℚ) from rfl,
      show groupPowers 95=(2, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_96 :
    gridGroupRate 96=(2:ℚ)^(groupPowers 96).1*(3:ℚ)^(groupPowers 96).2.1*
      (13:ℚ)^(groupPowers 96).2.2.1*(5:ℚ)^(groupPowers 96).2.2.2 := by
  simp only [show gridGroupRate 96=((9/100):ℚ) from rfl,
      show groupPowers 96=(-2, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_97 :
    gridGroupRate 97=(2:ℚ)^(groupPowers 97).1*(3:ℚ)^(groupPowers 97).2.1*
      (13:ℚ)^(groupPowers 97).2.2.1*(5:ℚ)^(groupPowers 97).2.2.2 := by
  simp only [show gridGroupRate 97=((1/100):ℚ) from rfl,
      show groupPowers 97=(-2, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_98 :
    gridGroupRate 98=(2:ℚ)^(groupPowers 98).1*(3:ℚ)^(groupPowers 98).2.1*
      (13:ℚ)^(groupPowers 98).2.2.1*(5:ℚ)^(groupPowers 98).2.2.2 := by
  simp only [show gridGroupRate 98=((1/225):ℚ) from rfl,
      show groupPowers 98=(0, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_99 :
    gridGroupRate 99=(2:ℚ)^(groupPowers 99).1*(3:ℚ)^(groupPowers 99).2.1*
      (13:ℚ)^(groupPowers 99).2.2.1*(5:ℚ)^(groupPowers 99).2.2.2 := by
  simp only [show gridGroupRate 99=((1/900):ℚ) from rfl,
      show groupPowers 99=(-2, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_100 :
    gridGroupRate 100=(2:ℚ)^(groupPowers 100).1*(3:ℚ)^(groupPowers 100).2.1*
      (13:ℚ)^(groupPowers 100).2.2.1*(5:ℚ)^(groupPowers 100).2.2.2 := by
  simp only [show gridGroupRate 100=(1800:ℚ) from rfl,
      show groupPowers 100=(3, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_101 :
    gridGroupRate 101=(2:ℚ)^(groupPowers 101).1*(3:ℚ)^(groupPowers 101).2.1*
      (13:ℚ)^(groupPowers 101).2.2.1*(5:ℚ)^(groupPowers 101).2.2.2 := by
  simp only [show gridGroupRate 101=(450:ℚ) from rfl,
      show groupPowers 101=(1, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_102 :
    gridGroupRate 102=(2:ℚ)^(groupPowers 102).1*(3:ℚ)^(groupPowers 102).2.1*
      (13:ℚ)^(groupPowers 102).2.2.1*(5:ℚ)^(groupPowers 102).2.2.2 := by
  simp only [show gridGroupRate 102=(200:ℚ) from rfl,
      show groupPowers 102=(3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_103 :
    gridGroupRate 103=(2:ℚ)^(groupPowers 103).1*(3:ℚ)^(groupPowers 103).2.1*
      (13:ℚ)^(groupPowers 103).2.2.1*(5:ℚ)^(groupPowers 103).2.2.2 := by
  simp only [show gridGroupRate 103=((225/2):ℚ) from rfl,
      show groupPowers 103=(-1, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_104 :
    gridGroupRate 104=(2:ℚ)^(groupPowers 104).1*(3:ℚ)^(groupPowers 104).2.1*
      (13:ℚ)^(groupPowers 104).2.2.1*(5:ℚ)^(groupPowers 104).2.2.2 := by
  simp only [show gridGroupRate 104=(450:ℚ) from rfl,
      show groupPowers 104=(1, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_105 :
    gridGroupRate 105=(2:ℚ)^(groupPowers 105).1*(3:ℚ)^(groupPowers 105).2.1*
      (13:ℚ)^(groupPowers 105).2.2.1*(5:ℚ)^(groupPowers 105).2.2.2 := by
  simp only [show gridGroupRate 105=(200:ℚ) from rfl,
      show groupPowers 105=(3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_106 :
    gridGroupRate 106=(2:ℚ)^(groupPowers 106).1*(3:ℚ)^(groupPowers 106).2.1*
      (13:ℚ)^(groupPowers 106).2.2.1*(5:ℚ)^(groupPowers 106).2.2.2 := by
  simp only [show gridGroupRate 106=((225/2):ℚ) from rfl,
      show groupPowers 106=(-1, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_107 :
    gridGroupRate 107=(2:ℚ)^(groupPowers 107).1*(3:ℚ)^(groupPowers 107).2.1*
      (13:ℚ)^(groupPowers 107).2.2.1*(5:ℚ)^(groupPowers 107).2.2.2 := by
  simp only [show gridGroupRate 107=(72:ℚ) from rfl,
      show groupPowers 107=(3, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_108 :
    gridGroupRate 108=(2:ℚ)^(groupPowers 108).1*(3:ℚ)^(groupPowers 108).2.1*
      (13:ℚ)^(groupPowers 108).2.2.1*(5:ℚ)^(groupPowers 108).2.2.2 := by
  simp only [show gridGroupRate 108=(18:ℚ) from rfl,
      show groupPowers 108=(1, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_109 :
    gridGroupRate 109=(2:ℚ)^(groupPowers 109).1*(3:ℚ)^(groupPowers 109).2.1*
      (13:ℚ)^(groupPowers 109).2.2.1*(5:ℚ)^(groupPowers 109).2.2.2 := by
  simp only [show gridGroupRate 109=(8:ℚ) from rfl,
      show groupPowers 109=(3, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_110 :
    gridGroupRate 110=(2:ℚ)^(groupPowers 110).1*(3:ℚ)^(groupPowers 110).2.1*
      (13:ℚ)^(groupPowers 110).2.2.1*(5:ℚ)^(groupPowers 110).2.2.2 := by
  simp only [show gridGroupRate 110=((9/2):ℚ) from rfl,
      show groupPowers 110=(-1, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_111 :
    gridGroupRate 111=(2:ℚ)^(groupPowers 111).1*(3:ℚ)^(groupPowers 111).2.1*
      (13:ℚ)^(groupPowers 111).2.2.1*(5:ℚ)^(groupPowers 111).2.2.2 := by
  simp only [show gridGroupRate 111=(2:ℚ) from rfl,
      show groupPowers 111=(1, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_112 :
    gridGroupRate 112=(2:ℚ)^(groupPowers 112).1*(3:ℚ)^(groupPowers 112).2.1*
      (13:ℚ)^(groupPowers 112).2.2.1*(5:ℚ)^(groupPowers 112).2.2.2 := by
  simp only [show gridGroupRate 112=((9/8):ℚ) from rfl,
      show groupPowers 112=(-3, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_113 :
    gridGroupRate 113=(2:ℚ)^(groupPowers 113).1*(3:ℚ)^(groupPowers 113).2.1*
      (13:ℚ)^(groupPowers 113).2.2.1*(5:ℚ)^(groupPowers 113).2.2.2 := by
  simp only [show gridGroupRate 113=((8/9):ℚ) from rfl,
      show groupPowers 113=(3, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_114 :
    gridGroupRate 114=(2:ℚ)^(groupPowers 114).1*(3:ℚ)^(groupPowers 114).2.1*
      (13:ℚ)^(groupPowers 114).2.2.1*(5:ℚ)^(groupPowers 114).2.2.2 := by
  simp only [show gridGroupRate 114=((1/2):ℚ) from rfl,
      show groupPowers 114=(-1, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_115 :
    gridGroupRate 115=(2:ℚ)^(groupPowers 115).1*(3:ℚ)^(groupPowers 115).2.1*
      (13:ℚ)^(groupPowers 115).2.2.1*(5:ℚ)^(groupPowers 115).2.2.2 := by
  simp only [show gridGroupRate 115=((2/9):ℚ) from rfl,
      show groupPowers 115=(1, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_116 :
    gridGroupRate 116=(2:ℚ)^(groupPowers 116).1*(3:ℚ)^(groupPowers 116).2.1*
      (13:ℚ)^(groupPowers 116).2.2.1*(5:ℚ)^(groupPowers 116).2.2.2 := by
  simp only [show gridGroupRate 116=((1/8):ℚ) from rfl,
      show groupPowers 116=(-3, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_117 :
    gridGroupRate 117=(2:ℚ)^(groupPowers 117).1*(3:ℚ)^(groupPowers 117).2.1*
      (13:ℚ)^(groupPowers 117).2.2.1*(5:ℚ)^(groupPowers 117).2.2.2 := by
  simp only [show gridGroupRate 117=((1/18):ℚ) from rfl,
      show groupPowers 117=(-1, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_118 :
    gridGroupRate 118=(2:ℚ)^(groupPowers 118).1*(3:ℚ)^(groupPowers 118).2.1*
      (13:ℚ)^(groupPowers 118).2.2.1*(5:ℚ)^(groupPowers 118).2.2.2 := by
  simp only [show gridGroupRate 118=((1/72):ℚ) from rfl,
      show groupPowers 118=(-3, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_119 :
    gridGroupRate 119=(2:ℚ)^(groupPowers 119).1*(3:ℚ)^(groupPowers 119).2.1*
      (13:ℚ)^(groupPowers 119).2.2.1*(5:ℚ)^(groupPowers 119).2.2.2 := by
  simp only [show gridGroupRate 119=((1/72):ℚ) from rfl,
      show groupPowers 119=(-3, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_120 :
    gridGroupRate 120=(2:ℚ)^(groupPowers 120).1*(3:ℚ)^(groupPowers 120).2.1*
      (13:ℚ)^(groupPowers 120).2.2.1*(5:ℚ)^(groupPowers 120).2.2.2 := by
  simp only [show gridGroupRate 120=((1/18):ℚ) from rfl,
      show groupPowers 120=(-1, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_121 :
    gridGroupRate 121=(2:ℚ)^(groupPowers 121).1*(3:ℚ)^(groupPowers 121).2.1*
      (13:ℚ)^(groupPowers 121).2.2.1*(5:ℚ)^(groupPowers 121).2.2.2 := by
  simp only [show gridGroupRate 121=((1/8):ℚ) from rfl,
      show groupPowers 121=(-3, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_122 :
    gridGroupRate 122=(2:ℚ)^(groupPowers 122).1*(3:ℚ)^(groupPowers 122).2.1*
      (13:ℚ)^(groupPowers 122).2.2.1*(5:ℚ)^(groupPowers 122).2.2.2 := by
  simp only [show gridGroupRate 122=((2/9):ℚ) from rfl,
      show groupPowers 122=(1, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_123 :
    gridGroupRate 123=(2:ℚ)^(groupPowers 123).1*(3:ℚ)^(groupPowers 123).2.1*
      (13:ℚ)^(groupPowers 123).2.2.1*(5:ℚ)^(groupPowers 123).2.2.2 := by
  simp only [show gridGroupRate 123=((1/2):ℚ) from rfl,
      show groupPowers 123=(-1, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_124 :
    gridGroupRate 124=(2:ℚ)^(groupPowers 124).1*(3:ℚ)^(groupPowers 124).2.1*
      (13:ℚ)^(groupPowers 124).2.2.1*(5:ℚ)^(groupPowers 124).2.2.2 := by
  simp only [show gridGroupRate 124=((8/9):ℚ) from rfl,
      show groupPowers 124=(3, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_125 :
    gridGroupRate 125=(2:ℚ)^(groupPowers 125).1*(3:ℚ)^(groupPowers 125).2.1*
      (13:ℚ)^(groupPowers 125).2.2.1*(5:ℚ)^(groupPowers 125).2.2.2 := by
  simp only [show gridGroupRate 125=((9/8):ℚ) from rfl,
      show groupPowers 125=(-3, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_126 :
    gridGroupRate 126=(2:ℚ)^(groupPowers 126).1*(3:ℚ)^(groupPowers 126).2.1*
      (13:ℚ)^(groupPowers 126).2.2.1*(5:ℚ)^(groupPowers 126).2.2.2 := by
  simp only [show gridGroupRate 126=(2:ℚ) from rfl,
      show groupPowers 126=(1, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_127 :
    gridGroupRate 127=(2:ℚ)^(groupPowers 127).1*(3:ℚ)^(groupPowers 127).2.1*
      (13:ℚ)^(groupPowers 127).2.2.1*(5:ℚ)^(groupPowers 127).2.2.2 := by
  simp only [show gridGroupRate 127=((9/2):ℚ) from rfl,
      show groupPowers 127=(-1, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_128 :
    gridGroupRate 128=(2:ℚ)^(groupPowers 128).1*(3:ℚ)^(groupPowers 128).2.1*
      (13:ℚ)^(groupPowers 128).2.2.1*(5:ℚ)^(groupPowers 128).2.2.2 := by
  simp only [show gridGroupRate 128=(8:ℚ) from rfl,
      show groupPowers 128=(3, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_129 :
    gridGroupRate 129=(2:ℚ)^(groupPowers 129).1*(3:ℚ)^(groupPowers 129).2.1*
      (13:ℚ)^(groupPowers 129).2.2.1*(5:ℚ)^(groupPowers 129).2.2.2 := by
  simp only [show gridGroupRate 129=(18:ℚ) from rfl,
      show groupPowers 129=(1, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_130 :
    gridGroupRate 130=(2:ℚ)^(groupPowers 130).1*(3:ℚ)^(groupPowers 130).2.1*
      (13:ℚ)^(groupPowers 130).2.2.1*(5:ℚ)^(groupPowers 130).2.2.2 := by
  simp only [show gridGroupRate 130=(72:ℚ) from rfl,
      show groupPowers 130=(3, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_131 :
    gridGroupRate 131=(2:ℚ)^(groupPowers 131).1*(3:ℚ)^(groupPowers 131).2.1*
      (13:ℚ)^(groupPowers 131).2.2.1*(5:ℚ)^(groupPowers 131).2.2.2 := by
  simp only [show gridGroupRate 131=(200:ℚ) from rfl,
      show groupPowers 131=(3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_132 :
    gridGroupRate 132=(2:ℚ)^(groupPowers 132).1*(3:ℚ)^(groupPowers 132).2.1*
      (13:ℚ)^(groupPowers 132).2.2.1*(5:ℚ)^(groupPowers 132).2.2.2 := by
  simp only [show gridGroupRate 132=(50:ℚ) from rfl,
      show groupPowers 132=(1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_133 :
    gridGroupRate 133=(2:ℚ)^(groupPowers 133).1*(3:ℚ)^(groupPowers 133).2.1*
      (13:ℚ)^(groupPowers 133).2.2.1*(5:ℚ)^(groupPowers 133).2.2.2 := by
  simp only [show gridGroupRate 133=((25/2):ℚ) from rfl,
      show groupPowers 133=(-1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_134 :
    gridGroupRate 134=(2:ℚ)^(groupPowers 134).1*(3:ℚ)^(groupPowers 134).2.1*
      (13:ℚ)^(groupPowers 134).2.2.1*(5:ℚ)^(groupPowers 134).2.2.2 := by
  simp only [show gridGroupRate 134=((25/8):ℚ) from rfl,
      show groupPowers 134=(-3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_135 :
    gridGroupRate 135=(2:ℚ)^(groupPowers 135).1*(3:ℚ)^(groupPowers 135).2.1*
      (13:ℚ)^(groupPowers 135).2.2.1*(5:ℚ)^(groupPowers 135).2.2.2 := by
  simp only [show gridGroupRate 135=(2:ℚ) from rfl,
      show groupPowers 135=(1, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_136 :
    gridGroupRate 136=(2:ℚ)^(groupPowers 136).1*(3:ℚ)^(groupPowers 136).2.1*
      (13:ℚ)^(groupPowers 136).2.2.1*(5:ℚ)^(groupPowers 136).2.2.2 := by
  simp only [show gridGroupRate 136=((1/200):ℚ) from rfl,
      show groupPowers 136=(-3, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_137 :
    gridGroupRate 137=(2:ℚ)^(groupPowers 137).1*(3:ℚ)^(groupPowers 137).2.1*
      (13:ℚ)^(groupPowers 137).2.2.1*(5:ℚ)^(groupPowers 137).2.2.2 := by
  simp only [show gridGroupRate 137=((1/2):ℚ) from rfl,
      show groupPowers 137=(-1, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_138 :
    gridGroupRate 138=(2:ℚ)^(groupPowers 138).1*(3:ℚ)^(groupPowers 138).2.1*
      (13:ℚ)^(groupPowers 138).2.2.1*(5:ℚ)^(groupPowers 138).2.2.2 := by
  simp only [show gridGroupRate 138=((25/8):ℚ) from rfl,
      show groupPowers 138=(-3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_139 :
    gridGroupRate 139=(2:ℚ)^(groupPowers 139).1*(3:ℚ)^(groupPowers 139).2.1*
      (13:ℚ)^(groupPowers 139).2.2.1*(5:ℚ)^(groupPowers 139).2.2.2 := by
  simp only [show gridGroupRate 139=(8:ℚ) from rfl,
      show groupPowers 139=(3, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_140 :
    gridGroupRate 140=(2:ℚ)^(groupPowers 140).1*(3:ℚ)^(groupPowers 140).2.1*
      (13:ℚ)^(groupPowers 140).2.2.1*(5:ℚ)^(groupPowers 140).2.2.2 := by
  simp only [show gridGroupRate 140=((25/2):ℚ) from rfl,
      show groupPowers 140=(-1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_141 :
    gridGroupRate 141=(2:ℚ)^(groupPowers 141).1*(3:ℚ)^(groupPowers 141).2.1*
      (13:ℚ)^(groupPowers 141).2.2.1*(5:ℚ)^(groupPowers 141).2.2.2 := by
  simp only [show gridGroupRate 141=(50:ℚ) from rfl,
      show groupPowers 141=(1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_142 :
    gridGroupRate 142=(2:ℚ)^(groupPowers 142).1*(3:ℚ)^(groupPowers 142).2.1*
      (13:ℚ)^(groupPowers 142).2.2.1*(5:ℚ)^(groupPowers 142).2.2.2 := by
  simp only [show gridGroupRate 142=(200:ℚ) from rfl,
      show groupPowers 142=(3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_143 :
    gridGroupRate 143=(2:ℚ)^(groupPowers 143).1*(3:ℚ)^(groupPowers 143).2.1*
      (13:ℚ)^(groupPowers 143).2.2.1*(5:ℚ)^(groupPowers 143).2.2.2 := by
  simp only [show gridGroupRate 143=(72:ℚ) from rfl,
      show groupPowers 143=(3, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_144 :
    gridGroupRate 144=(2:ℚ)^(groupPowers 144).1*(3:ℚ)^(groupPowers 144).2.1*
      (13:ℚ)^(groupPowers 144).2.2.1*(5:ℚ)^(groupPowers 144).2.2.2 := by
  simp only [show gridGroupRate 144=(50:ℚ) from rfl,
      show groupPowers 144=(1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_145 :
    gridGroupRate 145=(2:ℚ)^(groupPowers 145).1*(3:ℚ)^(groupPowers 145).2.1*
      (13:ℚ)^(groupPowers 145).2.2.1*(5:ℚ)^(groupPowers 145).2.2.2 := by
  simp only [show gridGroupRate 145=((200/9):ℚ) from rfl,
      show groupPowers 145=(3, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_146 :
    gridGroupRate 146=(2:ℚ)^(groupPowers 146).1*(3:ℚ)^(groupPowers 146).2.1*
      (13:ℚ)^(groupPowers 146).2.2.1*(5:ℚ)^(groupPowers 146).2.2.2 := by
  simp only [show gridGroupRate 146=((25/2):ℚ) from rfl,
      show groupPowers 146=(-1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_147 :
    gridGroupRate 147=(2:ℚ)^(groupPowers 147).1*(3:ℚ)^(groupPowers 147).2.1*
      (13:ℚ)^(groupPowers 147).2.2.1*(5:ℚ)^(groupPowers 147).2.2.2 := by
  simp only [show gridGroupRate 147=((50/9):ℚ) from rfl,
      show groupPowers 147=(1, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_148 :
    gridGroupRate 148=(2:ℚ)^(groupPowers 148).1*(3:ℚ)^(groupPowers 148).2.1*
      (13:ℚ)^(groupPowers 148).2.2.1*(5:ℚ)^(groupPowers 148).2.2.2 := by
  simp only [show gridGroupRate 148=((9/2):ℚ) from rfl,
      show groupPowers 148=(-1, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_149 :
    gridGroupRate 149=(2:ℚ)^(groupPowers 149).1*(3:ℚ)^(groupPowers 149).2.1*
      (13:ℚ)^(groupPowers 149).2.2.1*(5:ℚ)^(groupPowers 149).2.2.2 := by
  simp only [show gridGroupRate 149=((25/8):ℚ) from rfl,
      show groupPowers 149=(-3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_150 :
    gridGroupRate 150=(2:ℚ)^(groupPowers 150).1*(3:ℚ)^(groupPowers 150).2.1*
      (13:ℚ)^(groupPowers 150).2.2.1*(5:ℚ)^(groupPowers 150).2.2.2 := by
  simp only [show gridGroupRate 150=((72/25):ℚ) from rfl,
      show groupPowers 150=(3, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_151 :
    gridGroupRate 151=(2:ℚ)^(groupPowers 151).1*(3:ℚ)^(groupPowers 151).2.1*
      (13:ℚ)^(groupPowers 151).2.2.1*(5:ℚ)^(groupPowers 151).2.2.2 := by
  simp only [show gridGroupRate 151=((25/18):ℚ) from rfl,
      show groupPowers 151=(-1, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_152 :
    gridGroupRate 152=(2:ℚ)^(groupPowers 152).1*(3:ℚ)^(groupPowers 152).2.1*
      (13:ℚ)^(groupPowers 152).2.2.1*(5:ℚ)^(groupPowers 152).2.2.2 := by
  simp only [show gridGroupRate 152=((9/200):ℚ) from rfl,
      show groupPowers 152=(-3, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_153 :
    gridGroupRate 153=(2:ℚ)^(groupPowers 153).1*(3:ℚ)^(groupPowers 153).2.1*
      (13:ℚ)^(groupPowers 153).2.2.1*(5:ℚ)^(groupPowers 153).2.2.2 := by
  simp only [show gridGroupRate 153=((8/225):ℚ) from rfl,
      show groupPowers 153=(3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_154 :
    gridGroupRate 154=(2:ℚ)^(groupPowers 154).1*(3:ℚ)^(groupPowers 154).2.1*
      (13:ℚ)^(groupPowers 154).2.2.1*(5:ℚ)^(groupPowers 154).2.2.2 := by
  simp only [show gridGroupRate 154=((1/72):ℚ) from rfl,
      show groupPowers 154=(-3, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_155 :
    gridGroupRate 155=(2:ℚ)^(groupPowers 155).1*(3:ℚ)^(groupPowers 155).2.1*
      (13:ℚ)^(groupPowers 155).2.2.1*(5:ℚ)^(groupPowers 155).2.2.2 := by
  simp only [show gridGroupRate 155=((2/225):ℚ) from rfl,
      show groupPowers 155=(1, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_156 :
    gridGroupRate 156=(2:ℚ)^(groupPowers 156).1*(3:ℚ)^(groupPowers 156).2.1*
      (13:ℚ)^(groupPowers 156).2.2.1*(5:ℚ)^(groupPowers 156).2.2.2 := by
  simp only [show gridGroupRate 156=((1/200):ℚ) from rfl,
      show groupPowers 156=(-3, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_157 :
    gridGroupRate 157=(2:ℚ)^(groupPowers 157).1*(3:ℚ)^(groupPowers 157).2.1*
      (13:ℚ)^(groupPowers 157).2.2.1*(5:ℚ)^(groupPowers 157).2.2.2 := by
  simp only [show gridGroupRate 157=((1/450):ℚ) from rfl,
      show groupPowers 157=(-1, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_158 :
    gridGroupRate 158=(2:ℚ)^(groupPowers 158).1*(3:ℚ)^(groupPowers 158).2.1*
      (13:ℚ)^(groupPowers 158).2.2.1*(5:ℚ)^(groupPowers 158).2.2.2 := by
  simp only [show gridGroupRate 158=((1/1800):ℚ) from rfl,
      show groupPowers 158=(-3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_159 :
    gridGroupRate 159=(2:ℚ)^(groupPowers 159).1*(3:ℚ)^(groupPowers 159).2.1*
      (13:ℚ)^(groupPowers 159).2.2.1*(5:ℚ)^(groupPowers 159).2.2.2 := by
  simp only [show gridGroupRate 159=((1/1800):ℚ) from rfl,
      show groupPowers 159=(-3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_160 :
    gridGroupRate 160=(2:ℚ)^(groupPowers 160).1*(3:ℚ)^(groupPowers 160).2.1*
      (13:ℚ)^(groupPowers 160).2.2.1*(5:ℚ)^(groupPowers 160).2.2.2 := by
  simp only [show gridGroupRate 160=((1/450):ℚ) from rfl,
      show groupPowers 160=(-1, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_161 :
    gridGroupRate 161=(2:ℚ)^(groupPowers 161).1*(3:ℚ)^(groupPowers 161).2.1*
      (13:ℚ)^(groupPowers 161).2.2.1*(5:ℚ)^(groupPowers 161).2.2.2 := by
  simp only [show gridGroupRate 161=((1/200):ℚ) from rfl,
      show groupPowers 161=(-3, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_162 :
    gridGroupRate 162=(2:ℚ)^(groupPowers 162).1*(3:ℚ)^(groupPowers 162).2.1*
      (13:ℚ)^(groupPowers 162).2.2.1*(5:ℚ)^(groupPowers 162).2.2.2 := by
  simp only [show gridGroupRate 162=((2/225):ℚ) from rfl,
      show groupPowers 162=(1, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_163 :
    gridGroupRate 163=(2:ℚ)^(groupPowers 163).1*(3:ℚ)^(groupPowers 163).2.1*
      (13:ℚ)^(groupPowers 163).2.2.1*(5:ℚ)^(groupPowers 163).2.2.2 := by
  simp only [show gridGroupRate 163=((1/50):ℚ) from rfl,
      show groupPowers 163=(-1, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_164 :
    gridGroupRate 164=(2:ℚ)^(groupPowers 164).1*(3:ℚ)^(groupPowers 164).2.1*
      (13:ℚ)^(groupPowers 164).2.2.1*(5:ℚ)^(groupPowers 164).2.2.2 := by
  simp only [show gridGroupRate 164=((8/225):ℚ) from rfl,
      show groupPowers 164=(3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_165 :
    gridGroupRate 165=(2:ℚ)^(groupPowers 165).1*(3:ℚ)^(groupPowers 165).2.1*
      (13:ℚ)^(groupPowers 165).2.2.1*(5:ℚ)^(groupPowers 165).2.2.2 := by
  simp only [show gridGroupRate 165=((9/200):ℚ) from rfl,
      show groupPowers 165=(-3, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_166 :
    gridGroupRate 166=(2:ℚ)^(groupPowers 166).1*(3:ℚ)^(groupPowers 166).2.1*
      (13:ℚ)^(groupPowers 166).2.2.1*(5:ℚ)^(groupPowers 166).2.2.2 := by
  simp only [show gridGroupRate 166=((1/18):ℚ) from rfl,
      show groupPowers 166=(-1, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_167 :
    gridGroupRate 167=(2:ℚ)^(groupPowers 167).1*(3:ℚ)^(groupPowers 167).2.1*
      (13:ℚ)^(groupPowers 167).2.2.1*(5:ℚ)^(groupPowers 167).2.2.2 := by
  simp only [show gridGroupRate 167=((1/8):ℚ) from rfl,
      show groupPowers 167=(-3, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_168 :
    gridGroupRate 168=(2:ℚ)^(groupPowers 168).1*(3:ℚ)^(groupPowers 168).2.1*
      (13:ℚ)^(groupPowers 168).2.2.1*(5:ℚ)^(groupPowers 168).2.2.2 := by
  simp only [show gridGroupRate 168=((9/50):ℚ) from rfl,
      show groupPowers 168=(-1, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_169 :
    gridGroupRate 169=(2:ℚ)^(groupPowers 169).1*(3:ℚ)^(groupPowers 169).2.1*
      (13:ℚ)^(groupPowers 169).2.2.1*(5:ℚ)^(groupPowers 169).2.2.2 := by
  simp only [show gridGroupRate 169=((25/72):ℚ) from rfl,
      show groupPowers 169=(-3, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_170 :
    gridGroupRate 170=(2:ℚ)^(groupPowers 170).1*(3:ℚ)^(groupPowers 170).2.1*
      (13:ℚ)^(groupPowers 170).2.2.1*(5:ℚ)^(groupPowers 170).2.2.2 := by
  simp only [show gridGroupRate 170=((18/25):ℚ) from rfl,
      show groupPowers 170=(1, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_171 :
    gridGroupRate 171=(2:ℚ)^(groupPowers 171).1*(3:ℚ)^(groupPowers 171).2.1*
      (13:ℚ)^(groupPowers 171).2.2.1*(5:ℚ)^(groupPowers 171).2.2.2 := by
  simp only [show gridGroupRate 171=((8/9):ℚ) from rfl,
      show groupPowers 171=(3, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_172 :
    gridGroupRate 172=(2:ℚ)^(groupPowers 172).1*(3:ℚ)^(groupPowers 172).2.1*
      (13:ℚ)^(groupPowers 172).2.2.1*(5:ℚ)^(groupPowers 172).2.2.2 := by
  simp only [show gridGroupRate 172=((9/8):ℚ) from rfl,
      show groupPowers 172=(-3, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_173 :
    gridGroupRate 173=(2:ℚ)^(groupPowers 173).1*(3:ℚ)^(groupPowers 173).2.1*
      (13:ℚ)^(groupPowers 173).2.2.1*(5:ℚ)^(groupPowers 173).2.2.2 := by
  simp only [show gridGroupRate 173=((25/18):ℚ) from rfl,
      show groupPowers 173=(-1, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_174 :
    gridGroupRate 174=(2:ℚ)^(groupPowers 174).1*(3:ℚ)^(groupPowers 174).2.1*
      (13:ℚ)^(groupPowers 174).2.2.1*(5:ℚ)^(groupPowers 174).2.2.2 := by
  simp only [show gridGroupRate 174=(2:ℚ) from rfl,
      show groupPowers 174=(1, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_175 :
    gridGroupRate 175=(2:ℚ)^(groupPowers 175).1*(3:ℚ)^(groupPowers 175).2.1*
      (13:ℚ)^(groupPowers 175).2.2.1*(5:ℚ)^(groupPowers 175).2.2.2 := by
  simp only [show gridGroupRate 175=((25/8):ℚ) from rfl,
      show groupPowers 175=(-3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_176 :
    gridGroupRate 176=(2:ℚ)^(groupPowers 176).1*(3:ℚ)^(groupPowers 176).2.1*
      (13:ℚ)^(groupPowers 176).2.2.1*(5:ℚ)^(groupPowers 176).2.2.2 := by
  simp only [show gridGroupRate 176=((9/2):ℚ) from rfl,
      show groupPowers 176=(-1, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_177 :
    gridGroupRate 177=(2:ℚ)^(groupPowers 177).1*(3:ℚ)^(groupPowers 177).2.1*
      (13:ℚ)^(groupPowers 177).2.2.1*(5:ℚ)^(groupPowers 177).2.2.2 := by
  simp only [show gridGroupRate 177=(8:ℚ) from rfl,
      show groupPowers 177=(3, 0, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_178 :
    gridGroupRate 178=(2:ℚ)^(groupPowers 178).1*(3:ℚ)^(groupPowers 178).2.1*
      (13:ℚ)^(groupPowers 178).2.2.1*(5:ℚ)^(groupPowers 178).2.2.2 := by
  simp only [show gridGroupRate 178=((25/2):ℚ) from rfl,
      show groupPowers 178=(-1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_179 :
    gridGroupRate 179=(2:ℚ)^(groupPowers 179).1*(3:ℚ)^(groupPowers 179).2.1*
      (13:ℚ)^(groupPowers 179).2.2.1*(5:ℚ)^(groupPowers 179).2.2.2 := by
  simp only [show gridGroupRate 179=((200/9):ℚ) from rfl,
      show groupPowers 179=(3, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_180 :
    gridGroupRate 180=(2:ℚ)^(groupPowers 180).1*(3:ℚ)^(groupPowers 180).2.1*
      (13:ℚ)^(groupPowers 180).2.2.1*(5:ℚ)^(groupPowers 180).2.2.2 := by
  simp only [show gridGroupRate 180=(50:ℚ) from rfl,
      show groupPowers 180=(1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_181 :
    gridGroupRate 181=(2:ℚ)^(groupPowers 181).1*(3:ℚ)^(groupPowers 181).2.1*
      (13:ℚ)^(groupPowers 181).2.2.1*(5:ℚ)^(groupPowers 181).2.2.2 := by
  simp only [show gridGroupRate 181=((200/9):ℚ) from rfl,
      show groupPowers 181=(3, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_182 :
    gridGroupRate 182=(2:ℚ)^(groupPowers 182).1*(3:ℚ)^(groupPowers 182).2.1*
      (13:ℚ)^(groupPowers 182).2.2.1*(5:ℚ)^(groupPowers 182).2.2.2 := by
  simp only [show gridGroupRate 182=(18:ℚ) from rfl,
      show groupPowers 182=(1, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_183 :
    gridGroupRate 183=(2:ℚ)^(groupPowers 183).1*(3:ℚ)^(groupPowers 183).2.1*
      (13:ℚ)^(groupPowers 183).2.2.1*(5:ℚ)^(groupPowers 183).2.2.2 := by
  simp only [show gridGroupRate 183=((25/2):ℚ) from rfl,
      show groupPowers 183=(-1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_184 :
    gridGroupRate 184=(2:ℚ)^(groupPowers 184).1*(3:ℚ)^(groupPowers 184).2.1*
      (13:ℚ)^(groupPowers 184).2.2.1*(5:ℚ)^(groupPowers 184).2.2.2 := by
  simp only [show gridGroupRate 184=((25/8):ℚ) from rfl,
      show groupPowers 184=(-3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_185 :
    gridGroupRate 185=(2:ℚ)^(groupPowers 185).1*(3:ℚ)^(groupPowers 185).2.1*
      (13:ℚ)^(groupPowers 185).2.2.1*(5:ℚ)^(groupPowers 185).2.2.2 := by
  simp only [show gridGroupRate 185=((25/18):ℚ) from rfl,
      show groupPowers 185=(-1, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_186 :
    gridGroupRate 186=(2:ℚ)^(groupPowers 186).1*(3:ℚ)^(groupPowers 186).2.1*
      (13:ℚ)^(groupPowers 186).2.2.1*(5:ℚ)^(groupPowers 186).2.2.2 := by
  simp only [show gridGroupRate 186=((9/8):ℚ) from rfl,
      show groupPowers 186=(-3, 2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_187 :
    gridGroupRate 187=(2:ℚ)^(groupPowers 187).1*(3:ℚ)^(groupPowers 187).2.1*
      (13:ℚ)^(groupPowers 187).2.2.1*(5:ℚ)^(groupPowers 187).2.2.2 := by
  simp only [show gridGroupRate 187=((25/72):ℚ) from rfl,
      show groupPowers 187=(-3, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_188 :
    gridGroupRate 188=(2:ℚ)^(groupPowers 188).1*(3:ℚ)^(groupPowers 188).2.1*
      (13:ℚ)^(groupPowers 188).2.2.1*(5:ℚ)^(groupPowers 188).2.2.2 := by
  simp only [show gridGroupRate 188=((2/9):ℚ) from rfl,
      show groupPowers 188=(1, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_189 :
    gridGroupRate 189=(2:ℚ)^(groupPowers 189).1*(3:ℚ)^(groupPowers 189).2.1*
      (13:ℚ)^(groupPowers 189).2.2.1*(5:ℚ)^(groupPowers 189).2.2.2 := by
  simp only [show gridGroupRate 189=((9/50):ℚ) from rfl,
      show groupPowers 189=(-1, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_190 :
    gridGroupRate 190=(2:ℚ)^(groupPowers 190).1*(3:ℚ)^(groupPowers 190).2.1*
      (13:ℚ)^(groupPowers 190).2.2.1*(5:ℚ)^(groupPowers 190).2.2.2 := by
  simp only [show gridGroupRate 190=((9/200):ℚ) from rfl,
      show groupPowers 190=(-3, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_191 :
    gridGroupRate 191=(2:ℚ)^(groupPowers 191).1*(3:ℚ)^(groupPowers 191).2.1*
      (13:ℚ)^(groupPowers 191).2.2.1*(5:ℚ)^(groupPowers 191).2.2.2 := by
  simp only [show gridGroupRate 191=((8/225):ℚ) from rfl,
      show groupPowers 191=(3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_192 :
    gridGroupRate 192=(2:ℚ)^(groupPowers 192).1*(3:ℚ)^(groupPowers 192).2.1*
      (13:ℚ)^(groupPowers 192).2.2.1*(5:ℚ)^(groupPowers 192).2.2.2 := by
  simp only [show gridGroupRate 192=((1/50):ℚ) from rfl,
      show groupPowers 192=(-1, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_193 :
    gridGroupRate 193=(2:ℚ)^(groupPowers 193).1*(3:ℚ)^(groupPowers 193).2.1*
      (13:ℚ)^(groupPowers 193).2.2.1*(5:ℚ)^(groupPowers 193).2.2.2 := by
  simp only [show gridGroupRate 193=((1/72):ℚ) from rfl,
      show groupPowers 193=(-3, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_194 :
    gridGroupRate 194=(2:ℚ)^(groupPowers 194).1*(3:ℚ)^(groupPowers 194).2.1*
      (13:ℚ)^(groupPowers 194).2.2.1*(5:ℚ)^(groupPowers 194).2.2.2 := by
  simp only [show gridGroupRate 194=((2/225):ℚ) from rfl,
      show groupPowers 194=(1, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_195 :
    gridGroupRate 195=(2:ℚ)^(groupPowers 195).1*(3:ℚ)^(groupPowers 195).2.1*
      (13:ℚ)^(groupPowers 195).2.2.1*(5:ℚ)^(groupPowers 195).2.2.2 := by
  simp only [show gridGroupRate 195=((1/200):ℚ) from rfl,
      show groupPowers 195=(-3, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_196 :
    gridGroupRate 196=(2:ℚ)^(groupPowers 196).1*(3:ℚ)^(groupPowers 196).2.1*
      (13:ℚ)^(groupPowers 196).2.2.1*(5:ℚ)^(groupPowers 196).2.2.2 := by
  simp only [show gridGroupRate 196=((1/450):ℚ) from rfl,
      show groupPowers 196=(-1, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_197 :
    gridGroupRate 197=(2:ℚ)^(groupPowers 197).1*(3:ℚ)^(groupPowers 197).2.1*
      (13:ℚ)^(groupPowers 197).2.2.1*(5:ℚ)^(groupPowers 197).2.2.2 := by
  simp only [show gridGroupRate 197=((1/1800):ℚ) from rfl,
      show groupPowers 197=(-3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_198 :
    gridGroupRate 198=(2:ℚ)^(groupPowers 198).1*(3:ℚ)^(groupPowers 198).2.1*
      (13:ℚ)^(groupPowers 198).2.2.1*(5:ℚ)^(groupPowers 198).2.2.2 := by
  simp only [show gridGroupRate 198=((1/1800):ℚ) from rfl,
      show groupPowers 198=(-3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_199 :
    gridGroupRate 199=(2:ℚ)^(groupPowers 199).1*(3:ℚ)^(groupPowers 199).2.1*
      (13:ℚ)^(groupPowers 199).2.2.1*(5:ℚ)^(groupPowers 199).2.2.2 := by
  simp only [show gridGroupRate 199=((1/450):ℚ) from rfl,
      show groupPowers 199=(-1, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_200 :
    gridGroupRate 200=(2:ℚ)^(groupPowers 200).1*(3:ℚ)^(groupPowers 200).2.1*
      (13:ℚ)^(groupPowers 200).2.2.1*(5:ℚ)^(groupPowers 200).2.2.2 := by
  simp only [show gridGroupRate 200=((1/200):ℚ) from rfl,
      show groupPowers 200=(-3, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_201 :
    gridGroupRate 201=(2:ℚ)^(groupPowers 201).1*(3:ℚ)^(groupPowers 201).2.1*
      (13:ℚ)^(groupPowers 201).2.2.1*(5:ℚ)^(groupPowers 201).2.2.2 := by
  simp only [show gridGroupRate 201=((2/225):ℚ) from rfl,
      show groupPowers 201=(1, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_202 :
    gridGroupRate 202=(2:ℚ)^(groupPowers 202).1*(3:ℚ)^(groupPowers 202).2.1*
      (13:ℚ)^(groupPowers 202).2.2.1*(5:ℚ)^(groupPowers 202).2.2.2 := by
  simp only [show gridGroupRate 202=((1/72):ℚ) from rfl,
      show groupPowers 202=(-3, -2, 0, 0) from rfl]
  norm_num

theorem groupRate_factor_203 :
    gridGroupRate 203=(2:ℚ)^(groupPowers 203).1*(3:ℚ)^(groupPowers 203).2.1*
      (13:ℚ)^(groupPowers 203).2.2.1*(5:ℚ)^(groupPowers 203).2.2.2 := by
  simp only [show gridGroupRate 203=((1/50):ℚ) from rfl,
      show groupPowers 203=(-1, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_204 :
    gridGroupRate 204=(2:ℚ)^(groupPowers 204).1*(3:ℚ)^(groupPowers 204).2.1*
      (13:ℚ)^(groupPowers 204).2.2.1*(5:ℚ)^(groupPowers 204).2.2.2 := by
  simp only [show gridGroupRate 204=((8/225):ℚ) from rfl,
      show groupPowers 204=(3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_205 :
    gridGroupRate 205=(2:ℚ)^(groupPowers 205).1*(3:ℚ)^(groupPowers 205).2.1*
      (13:ℚ)^(groupPowers 205).2.2.1*(5:ℚ)^(groupPowers 205).2.2.2 := by
  simp only [show gridGroupRate 205=((9/200):ℚ) from rfl,
      show groupPowers 205=(-3, 2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_206 :
    gridGroupRate 206=(2:ℚ)^(groupPowers 206).1*(3:ℚ)^(groupPowers 206).2.1*
      (13:ℚ)^(groupPowers 206).2.2.1*(5:ℚ)^(groupPowers 206).2.2.2 := by
  simp only [show gridGroupRate 206=((25/72):ℚ) from rfl,
      show groupPowers 206=(-3, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_207 :
    gridGroupRate 207=(2:ℚ)^(groupPowers 207).1*(3:ℚ)^(groupPowers 207).2.1*
      (13:ℚ)^(groupPowers 207).2.2.1*(5:ℚ)^(groupPowers 207).2.2.2 := by
  simp only [show gridGroupRate 207=((200/9):ℚ) from rfl,
      show groupPowers 207=(3, -2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_208 :
    gridGroupRate 208=(2:ℚ)^(groupPowers 208).1*(3:ℚ)^(groupPowers 208).2.1*
      (13:ℚ)^(groupPowers 208).2.2.1*(5:ℚ)^(groupPowers 208).2.2.2 := by
  simp only [show gridGroupRate 208=(50:ℚ) from rfl,
      show groupPowers 208=(1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_209 :
    gridGroupRate 209=(2:ℚ)^(groupPowers 209).1*(3:ℚ)^(groupPowers 209).2.1*
      (13:ℚ)^(groupPowers 209).2.2.1*(5:ℚ)^(groupPowers 209).2.2.2 := by
  simp only [show gridGroupRate 209=(50:ℚ) from rfl,
      show groupPowers 209=(1, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_210 :
    gridGroupRate 210=(2:ℚ)^(groupPowers 210).1*(3:ℚ)^(groupPowers 210).2.1*
      (13:ℚ)^(groupPowers 210).2.2.1*(5:ℚ)^(groupPowers 210).2.2.2 := by
  simp only [show gridGroupRate 210=((2/25):ℚ) from rfl,
      show groupPowers 210=(1, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_211 :
    gridGroupRate 211=(2:ℚ)^(groupPowers 211).1*(3:ℚ)^(groupPowers 211).2.1*
      (13:ℚ)^(groupPowers 211).2.2.1*(5:ℚ)^(groupPowers 211).2.2.2 := by
  simp only [show gridGroupRate 211=((1/200):ℚ) from rfl,
      show groupPowers 211=(-3, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_212 :
    gridGroupRate 212=(2:ℚ)^(groupPowers 212).1*(3:ℚ)^(groupPowers 212).2.1*
      (13:ℚ)^(groupPowers 212).2.2.1*(5:ℚ)^(groupPowers 212).2.2.2 := by
  simp only [show gridGroupRate 212=((1/200):ℚ) from rfl,
      show groupPowers 212=(-3, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_213 :
    gridGroupRate 213=(2:ℚ)^(groupPowers 213).1*(3:ℚ)^(groupPowers 213).2.1*
      (13:ℚ)^(groupPowers 213).2.2.1*(5:ℚ)^(groupPowers 213).2.2.2 := by
  simp only [show gridGroupRate 213=((1/50):ℚ) from rfl,
      show groupPowers 213=(-1, 0, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_214 :
    gridGroupRate 214=(2:ℚ)^(groupPowers 214).1*(3:ℚ)^(groupPowers 214).2.1*
      (13:ℚ)^(groupPowers 214).2.2.1*(5:ℚ)^(groupPowers 214).2.2.2 := by
  simp only [show gridGroupRate 214=(200:ℚ) from rfl,
      show groupPowers 214=(3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_215 :
    gridGroupRate 215=(2:ℚ)^(groupPowers 215).1*(3:ℚ)^(groupPowers 215).2.1*
      (13:ℚ)^(groupPowers 215).2.2.1*(5:ℚ)^(groupPowers 215).2.2.2 := by
  simp only [show gridGroupRate 215=((225/2):ℚ) from rfl,
      show groupPowers 215=(-1, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_216 :
    gridGroupRate 216=(2:ℚ)^(groupPowers 216).1*(3:ℚ)^(groupPowers 216).2.1*
      (13:ℚ)^(groupPowers 216).2.2.1*(5:ℚ)^(groupPowers 216).2.2.2 := by
  simp only [show gridGroupRate 216=(200:ℚ) from rfl,
      show groupPowers 216=(3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_217 :
    gridGroupRate 217=(2:ℚ)^(groupPowers 217).1*(3:ℚ)^(groupPowers 217).2.1*
      (13:ℚ)^(groupPowers 217).2.2.1*(5:ℚ)^(groupPowers 217).2.2.2 := by
  simp only [show gridGroupRate 217=(450:ℚ) from rfl,
      show groupPowers 217=(1, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_218 :
    gridGroupRate 218=(2:ℚ)^(groupPowers 218).1*(3:ℚ)^(groupPowers 218).2.1*
      (13:ℚ)^(groupPowers 218).2.2.1*(5:ℚ)^(groupPowers 218).2.2.2 := by
  simp only [show gridGroupRate 218=((225/2):ℚ) from rfl,
      show groupPowers 218=(-1, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_219 :
    gridGroupRate 219=(2:ℚ)^(groupPowers 219).1*(3:ℚ)^(groupPowers 219).2.1*
      (13:ℚ)^(groupPowers 219).2.2.1*(5:ℚ)^(groupPowers 219).2.2.2 := by
  simp only [show gridGroupRate 219=(200:ℚ) from rfl,
      show groupPowers 219=(3, 0, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_220 :
    gridGroupRate 220=(2:ℚ)^(groupPowers 220).1*(3:ℚ)^(groupPowers 220).2.1*
      (13:ℚ)^(groupPowers 220).2.2.1*(5:ℚ)^(groupPowers 220).2.2.2 := by
  simp only [show gridGroupRate 220=(450:ℚ) from rfl,
      show groupPowers 220=(1, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_221 :
    gridGroupRate 221=(2:ℚ)^(groupPowers 221).1*(3:ℚ)^(groupPowers 221).2.1*
      (13:ℚ)^(groupPowers 221).2.2.1*(5:ℚ)^(groupPowers 221).2.2.2 := by
  simp only [show gridGroupRate 221=(1800:ℚ) from rfl,
      show groupPowers 221=(3, 2, 0, 2) from rfl]
  norm_num

theorem groupRate_factor_222 :
    gridGroupRate 222=(2:ℚ)^(groupPowers 222).1*(3:ℚ)^(groupPowers 222).2.1*
      (13:ℚ)^(groupPowers 222).2.2.1*(5:ℚ)^(groupPowers 222).2.2.2 := by
  simp only [show gridGroupRate 222=((1/1800):ℚ) from rfl,
      show groupPowers 222=(-3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_223 :
    gridGroupRate 223=(2:ℚ)^(groupPowers 223).1*(3:ℚ)^(groupPowers 223).2.1*
      (13:ℚ)^(groupPowers 223).2.2.1*(5:ℚ)^(groupPowers 223).2.2.2 := by
  simp only [show gridGroupRate 223=((1/1800):ℚ) from rfl,
      show groupPowers 223=(-3, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_224 :
    gridGroupRate 224=(2:ℚ)^(groupPowers 224).1*(3:ℚ)^(groupPowers 224).2.1*
      (13:ℚ)^(groupPowers 224).2.2.1*(5:ℚ)^(groupPowers 224).2.2.2 := by
  simp only [show gridGroupRate 224=((900/13):ℚ) from rfl,
      show groupPowers 224=(2, 2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_225 :
    gridGroupRate 225=(2:ℚ)^(groupPowers 225).1*(3:ℚ)^(groupPowers 225).2.1*
      (13:ℚ)^(groupPowers 225).2.2.1*(5:ℚ)^(groupPowers 225).2.2.2 := by
  simp only [show gridGroupRate 225=((225/52):ℚ) from rfl,
      show groupPowers 225=(-2, 2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_226 :
    gridGroupRate 226=(2:ℚ)^(groupPowers 226).1*(3:ℚ)^(groupPowers 226).2.1*
      (13:ℚ)^(groupPowers 226).2.2.1*(5:ℚ)^(groupPowers 226).2.2.2 := by
  simp only [show gridGroupRate 226=((117/100):ℚ) from rfl,
      show groupPowers 226=(-2, 2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_227 :
    gridGroupRate 227=(2:ℚ)^(groupPowers 227).1*(3:ℚ)^(groupPowers 227).2.1*
      (13:ℚ)^(groupPowers 227).2.2.1*(5:ℚ)^(groupPowers 227).2.2.2 := by
  simp only [show gridGroupRate 227=((100/117):ℚ) from rfl,
      show groupPowers 227=(2, -2, -1, 2) from rfl]
  norm_num

theorem groupRate_factor_228 :
    gridGroupRate 228=(2:ℚ)^(groupPowers 228).1*(3:ℚ)^(groupPowers 228).2.1*
      (13:ℚ)^(groupPowers 228).2.2.1*(5:ℚ)^(groupPowers 228).2.2.2 := by
  simp only [show gridGroupRate 228=((52/225):ℚ) from rfl,
      show groupPowers 228=(2, -2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_229 :
    gridGroupRate 229=(2:ℚ)^(groupPowers 229).1*(3:ℚ)^(groupPowers 229).2.1*
      (13:ℚ)^(groupPowers 229).2.2.1*(5:ℚ)^(groupPowers 229).2.2.2 := by
  simp only [show gridGroupRate 229=((13/900):ℚ) from rfl,
      show groupPowers 229=(-2, -2, 1, -2) from rfl]
  norm_num

theorem groupRate_factor_230 :
    gridGroupRate 230=(2:ℚ)^(groupPowers 230).1*(3:ℚ)^(groupPowers 230).2.1*
      (13:ℚ)^(groupPowers 230).2.2.1*(5:ℚ)^(groupPowers 230).2.2.2 := by
  simp only [show gridGroupRate 230=((4/2925):ℚ) from rfl,
      show groupPowers 230=(2, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_231 :
    gridGroupRate 231=(2:ℚ)^(groupPowers 231).1*(3:ℚ)^(groupPowers 231).2.1*
      (13:ℚ)^(groupPowers 231).2.2.1*(5:ℚ)^(groupPowers 231).2.2.2 := by
  simp only [show gridGroupRate 231=((1/11700):ℚ) from rfl,
      show groupPowers 231=(-2, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_232 :
    gridGroupRate 232=(2:ℚ)^(groupPowers 232).1*(3:ℚ)^(groupPowers 232).2.1*
      (13:ℚ)^(groupPowers 232).2.2.1*(5:ℚ)^(groupPowers 232).2.2.2 := by
  simp only [show gridGroupRate 232=((1/11700):ℚ) from rfl,
      show groupPowers 232=(-2, -2, -1, -2) from rfl]
  norm_num

theorem groupRate_factor_233 :
    gridGroupRate 233=(2:ℚ)^(groupPowers 233).1*(3:ℚ)^(groupPowers 233).2.1*
      (13:ℚ)^(groupPowers 233).2.2.1*(5:ℚ)^(groupPowers 233).2.2.2 := by
  simp only [show gridGroupRate 233=((1/225):ℚ) from rfl,
      show groupPowers 233=(0, -2, 0, -2) from rfl]
  norm_num

theorem groupRate_factor_234 :
    gridGroupRate 234=(2:ℚ)^(groupPowers 234).1*(3:ℚ)^(groupPowers 234).2.1*
      (13:ℚ)^(groupPowers 234).2.2.1*(5:ℚ)^(groupPowers 234).2.2.2 := by
  simp only [show gridGroupRate 234=(225:ℚ) from rfl,
      show groupPowers 234=(0, 2, 0, 2) from rfl]
  norm_num

end SmallLevelTwentySixGrid
