module
public import SmallLevelTwentySixGridGeometryDataV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixGrid
open Matrix SmallLevelAdditive

theorem gridGroup_geometry_0 : GridGroupGeometry 0 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 0=(23:Fin 27) from rfl,
    show gridGroupIndex 0=(0:Fin 780) from rfl,
    show gridGroupPartner 0=(-15:ℤ) from rfl,
    show gridGroupRate 0=(104:ℚ) from rfl,
    show gridGroupDerivative 0=(52:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![0,1;-26,-52] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_1 : GridGroupGeometry 1 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 1=(23:Fin 27) from rfl,
    show gridGroupIndex 1=(240:Fin 780) from rfl,
    show gridGroupPartner 1=(-13:ℤ) from rfl,
    show gridGroupRate 1=((1800/13):ℚ) from rfl,
    show gridGroupDerivative 1=(60:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![0,1;-26,-52] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_2 : GridGroupGeometry 2 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 2=(23:Fin 27) from rfl,
    show gridGroupIndex 2=(390:Fin 780) from rfl,
    show gridGroupPartner 2=(-12:ℤ) from rfl,
    show gridGroupRate 2=((325/2):ℚ) from rfl,
    show gridGroupDerivative 2=(65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 23=!![0,1;-26,-52] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_3 : GridGroupGeometry 3 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 3=(22:Fin 27) from rfl,
    show gridGroupIndex 3=(0:Fin 780) from rfl,
    show gridGroupPartner 3=(-30:ℤ) from rfl,
    show gridGroupRate 3=(26:ℚ) from rfl,
    show gridGroupDerivative 3=(26:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 22=!![0,1;-26,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_4 : GridGroupGeometry 4 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 4=(22:Fin 27) from rfl,
    show gridGroupIndex 4=(120:Fin 780) from rfl,
    show gridGroupPartner 4=(-26:ℤ) from rfl,
    show gridGroupRate 4=((450/13):ℚ) from rfl,
    show gridGroupDerivative 4=(30:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 22=!![0,1;-26,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_5 : GridGroupGeometry 5 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 5=(22:Fin 27) from rfl,
    show gridGroupIndex 5=(156:Fin 780) from rfl,
    show gridGroupPartner 5=(-25:ℤ) from rfl,
    show gridGroupRate 5=((936/25):ℚ) from rfl,
    show gridGroupDerivative 5=((156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 22=!![0,1;-26,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_6 : GridGroupGeometry 6 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 6=(22:Fin 27) from rfl,
    show gridGroupIndex 6=(195:Fin 780) from rfl,
    show gridGroupPartner 6=(-24:ℤ) from rfl,
    show gridGroupRate 6=((325/8):ℚ) from rfl,
    show gridGroupDerivative 6=((65/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 22=!![0,1;-26,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_7 : GridGroupGeometry 7 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 7=(22:Fin 27) from rfl,
    show gridGroupIndex 7=(390:Fin 780) from rfl,
    show gridGroupPartner 7=(-20:ℤ) from rfl,
    show gridGroupRate 7=((117/2):ℚ) from rfl,
    show gridGroupDerivative 7=(39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 22=!![0,1;-26,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_8 : GridGroupGeometry 8 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 8=(22:Fin 27) from rfl,
    show gridGroupIndex 8=(520:Fin 780) from rfl,
    show gridGroupPartner 8=(-18:ℤ) from rfl,
    show gridGroupRate 8=((650/9):ℚ) from rfl,
    show gridGroupDerivative 8=((130/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 22=!![0,1;-26,-26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_9 : GridGroupGeometry 9 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 9=(21:Fin 27) from rfl,
    show gridGroupIndex 9=(1:Fin 780) from rfl,
    show gridGroupPartner 9=(-23400:ℤ) from rfl,
    show gridGroupRate 9=((1/23400):ℚ) from rfl,
    show gridGroupDerivative 9=((1/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_10 : GridGroupGeometry 10 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 10=(21:Fin 27) from rfl,
    show gridGroupIndex 10=(2:Fin 780) from rfl,
    show gridGroupPartner 10=(-11700:ℤ) from rfl,
    show gridGroupRate 10=((1/5850):ℚ) from rfl,
    show gridGroupDerivative 10=((1/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_11 : GridGroupGeometry 11 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 11=(21:Fin 27) from rfl,
    show gridGroupIndex 11=(3:Fin 780) from rfl,
    show gridGroupPartner 11=(-7800:ℤ) from rfl,
    show gridGroupRate 11=((1/2600):ℚ) from rfl,
    show gridGroupDerivative 11=((1/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_12 : GridGroupGeometry 12 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 12=(21:Fin 27) from rfl,
    show gridGroupIndex 12=(4:Fin 780) from rfl,
    show gridGroupPartner 12=(-5850:ℤ) from rfl,
    show gridGroupRate 12=((2/2925):ℚ) from rfl,
    show gridGroupDerivative 12=((2/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_13 : GridGroupGeometry 13 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 13=(21:Fin 27) from rfl,
    show gridGroupIndex 13=(5:Fin 780) from rfl,
    show gridGroupPartner 13=(-4680:ℤ) from rfl,
    show gridGroupRate 13=((1/936):ℚ) from rfl,
    show gridGroupDerivative 13=((1/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_14 : GridGroupGeometry 14 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 14=(21:Fin 27) from rfl,
    show gridGroupIndex 14=(6:Fin 780) from rfl,
    show gridGroupPartner 14=(-3900:ℤ) from rfl,
    show gridGroupRate 14=((1/650):ℚ) from rfl,
    show gridGroupDerivative 14=((1/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_15 : GridGroupGeometry 15 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 15=(21:Fin 27) from rfl,
    show gridGroupIndex 15=(8:Fin 780) from rfl,
    show gridGroupPartner 15=(-2925:ℤ) from rfl,
    show gridGroupRate 15=((8/2925):ℚ) from rfl,
    show gridGroupDerivative 15=((4/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_16 : GridGroupGeometry 16 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 16=(21:Fin 27) from rfl,
    show gridGroupIndex 16=(9:Fin 780) from rfl,
    show gridGroupPartner 16=(-2600:ℤ) from rfl,
    show gridGroupRate 16=((9/2600):ℚ) from rfl,
    show gridGroupDerivative 16=((3/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_17 : GridGroupGeometry 17 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 17=(21:Fin 27) from rfl,
    show gridGroupIndex 17=(10:Fin 780) from rfl,
    show gridGroupPartner 17=(-2340:ℤ) from rfl,
    show gridGroupRate 17=((1/234):ℚ) from rfl,
    show gridGroupDerivative 17=((1/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_18 : GridGroupGeometry 18 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 18=(21:Fin 27) from rfl,
    show gridGroupIndex 18=(12:Fin 780) from rfl,
    show gridGroupPartner 18=(-1950:ℤ) from rfl,
    show gridGroupRate 18=((2/325):ℚ) from rfl,
    show gridGroupDerivative 18=((2/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_19 : GridGroupGeometry 19 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 19=(21:Fin 27) from rfl,
    show gridGroupIndex 19=(13:Fin 780) from rfl,
    show gridGroupPartner 19=(-1800:ℤ) from rfl,
    show gridGroupRate 19=((13/1800):ℚ) from rfl,
    show gridGroupDerivative 19=((13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_20 : GridGroupGeometry 20 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 20=(21:Fin 27) from rfl,
    show gridGroupIndex 20=(15:Fin 780) from rfl,
    show gridGroupPartner 20=(-1560:ℤ) from rfl,
    show gridGroupRate 20=((1/104):ℚ) from rfl,
    show gridGroupDerivative 20=((1/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_21 : GridGroupGeometry 21 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 21=(21:Fin 27) from rfl,
    show gridGroupIndex 21=(18:Fin 780) from rfl,
    show gridGroupPartner 21=(-1300:ℤ) from rfl,
    show gridGroupRate 21=((9/650):ℚ) from rfl,
    show gridGroupDerivative 21=((3/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_22 : GridGroupGeometry 22 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 22=(21:Fin 27) from rfl,
    show gridGroupIndex 22=(20:Fin 780) from rfl,
    show gridGroupPartner 22=(-1170:ℤ) from rfl,
    show gridGroupRate 22=((2/117):ℚ) from rfl,
    show gridGroupDerivative 22=((2/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_23 : GridGroupGeometry 23 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 23=(21:Fin 27) from rfl,
    show gridGroupIndex 23=(24:Fin 780) from rfl,
    show gridGroupPartner 23=(-975:ℤ) from rfl,
    show gridGroupRate 23=((8/325):ℚ) from rfl,
    show gridGroupDerivative 23=((4/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_24 : GridGroupGeometry 24 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 24=(21:Fin 27) from rfl,
    show gridGroupIndex 24=(25:Fin 780) from rfl,
    show gridGroupPartner 24=(-936:ℤ) from rfl,
    show gridGroupRate 24=((25/936):ℚ) from rfl,
    show gridGroupDerivative 24=((5/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_25 : GridGroupGeometry 25 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 25=(21:Fin 27) from rfl,
    show gridGroupIndex 25=(26:Fin 780) from rfl,
    show gridGroupPartner 25=(-900:ℤ) from rfl,
    show gridGroupRate 25=((13/450):ℚ) from rfl,
    show gridGroupDerivative 25=((13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_26 : GridGroupGeometry 26 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 26=(21:Fin 27) from rfl,
    show gridGroupIndex 26=(30:Fin 780) from rfl,
    show gridGroupPartner 26=(-780:ℤ) from rfl,
    show gridGroupRate 26=((1/26):ℚ) from rfl,
    show gridGroupDerivative 26=(1:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_27 : GridGroupGeometry 27 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 27=(21:Fin 27) from rfl,
    show gridGroupIndex 27=(36:Fin 780) from rfl,
    show gridGroupPartner 27=(-650:ℤ) from rfl,
    show gridGroupRate 27=((18/325):ℚ) from rfl,
    show gridGroupDerivative 27=((6/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_28 : GridGroupGeometry 28 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 28=(21:Fin 27) from rfl,
    show gridGroupIndex 28=(39:Fin 780) from rfl,
    show gridGroupPartner 28=(-600:ℤ) from rfl,
    show gridGroupRate 28=((13/200):ℚ) from rfl,
    show gridGroupDerivative 28=((13/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_29 : GridGroupGeometry 29 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 29=(21:Fin 27) from rfl,
    show gridGroupIndex 29=(40:Fin 780) from rfl,
    show gridGroupPartner 29=(-585:ℤ) from rfl,
    show gridGroupRate 29=((8/117):ℚ) from rfl,
    show gridGroupDerivative 29=((4/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_30 : GridGroupGeometry 30 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 30=(21:Fin 27) from rfl,
    show gridGroupIndex 30=(45:Fin 780) from rfl,
    show gridGroupPartner 30=(-520:ℤ) from rfl,
    show gridGroupRate 30=((9/104):ℚ) from rfl,
    show gridGroupDerivative 30=((3/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_31 : GridGroupGeometry 31 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 31=(21:Fin 27) from rfl,
    show gridGroupIndex 31=(50:Fin 780) from rfl,
    show gridGroupPartner 31=(-468:ℤ) from rfl,
    show gridGroupRate 31=((25/234):ℚ) from rfl,
    show gridGroupDerivative 31=((5/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_32 : GridGroupGeometry 32 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 32=(21:Fin 27) from rfl,
    show gridGroupIndex 32=(52:Fin 780) from rfl,
    show gridGroupPartner 32=(-450:ℤ) from rfl,
    show gridGroupRate 32=((26/225):ℚ) from rfl,
    show gridGroupDerivative 32=((26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_33 : GridGroupGeometry 33 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 33=(21:Fin 27) from rfl,
    show gridGroupIndex 33=(60:Fin 780) from rfl,
    show gridGroupPartner 33=(-390:ℤ) from rfl,
    show gridGroupRate 33=((2/13):ℚ) from rfl,
    show gridGroupDerivative 33=(2:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_34 : GridGroupGeometry 34 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 34=(21:Fin 27) from rfl,
    show gridGroupIndex 34=(65:Fin 780) from rfl,
    show gridGroupPartner 34=(-360:ℤ) from rfl,
    show gridGroupRate 34=((13/72):ℚ) from rfl,
    show gridGroupDerivative 34=((13/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_35 : GridGroupGeometry 35 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 35=(21:Fin 27) from rfl,
    show gridGroupIndex 35=(72:Fin 780) from rfl,
    show gridGroupPartner 35=(-325:ℤ) from rfl,
    show gridGroupRate 35=((72/325):ℚ) from rfl,
    show gridGroupDerivative 35=((12/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_36 : GridGroupGeometry 36 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 36=(21:Fin 27) from rfl,
    show gridGroupIndex 36=(75:Fin 780) from rfl,
    show gridGroupPartner 36=(-312:ℤ) from rfl,
    show gridGroupRate 36=((25/104):ℚ) from rfl,
    show gridGroupDerivative 36=((5/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_37 : GridGroupGeometry 37 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 37=(21:Fin 27) from rfl,
    show gridGroupIndex 37=(78:Fin 780) from rfl,
    show gridGroupPartner 37=(-300:ℤ) from rfl,
    show gridGroupRate 37=((13/50):ℚ) from rfl,
    show gridGroupDerivative 37=((13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_38 : GridGroupGeometry 38 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 38=(21:Fin 27) from rfl,
    show gridGroupIndex 38=(90:Fin 780) from rfl,
    show gridGroupPartner 38=(-260:ℤ) from rfl,
    show gridGroupRate 38=((9/26):ℚ) from rfl,
    show gridGroupDerivative 38=(3:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_39 : GridGroupGeometry 39 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 39=(21:Fin 27) from rfl,
    show gridGroupIndex 39=(100:Fin 780) from rfl,
    show gridGroupPartner 39=(-234:ℤ) from rfl,
    show gridGroupRate 39=((50/117):ℚ) from rfl,
    show gridGroupDerivative 39=((10/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_40 : GridGroupGeometry 40 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 40=(21:Fin 27) from rfl,
    show gridGroupIndex 40=(104:Fin 780) from rfl,
    show gridGroupPartner 40=(-225:ℤ) from rfl,
    show gridGroupRate 40=((104/225):ℚ) from rfl,
    show gridGroupDerivative 40=((52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_41 : GridGroupGeometry 41 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 41=(21:Fin 27) from rfl,
    show gridGroupIndex 41=(117:Fin 780) from rfl,
    show gridGroupPartner 41=(-200:ℤ) from rfl,
    show gridGroupRate 41=((117/200):ℚ) from rfl,
    show gridGroupDerivative 41=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_42 : GridGroupGeometry 42 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 42=(21:Fin 27) from rfl,
    show gridGroupIndex 42=(120:Fin 780) from rfl,
    show gridGroupPartner 42=(-195:ℤ) from rfl,
    show gridGroupRate 42=((8/13):ℚ) from rfl,
    show gridGroupDerivative 42=(4:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_43 : GridGroupGeometry 43 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 43=(21:Fin 27) from rfl,
    show gridGroupIndex 43=(130:Fin 780) from rfl,
    show gridGroupPartner 43=(-180:ℤ) from rfl,
    show gridGroupRate 43=((13/18):ℚ) from rfl,
    show gridGroupDerivative 43=((13/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_44 : GridGroupGeometry 44 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 44=(21:Fin 27) from rfl,
    show gridGroupIndex 44=(150:Fin 780) from rfl,
    show gridGroupPartner 44=(-156:ℤ) from rfl,
    show gridGroupRate 44=((25/26):ℚ) from rfl,
    show gridGroupDerivative 44=(5:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_45 : GridGroupGeometry 45 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 45=(21:Fin 27) from rfl,
    show gridGroupIndex 45=(156:Fin 780) from rfl,
    show gridGroupPartner 45=(-150:ℤ) from rfl,
    show gridGroupRate 45=((26/25):ℚ) from rfl,
    show gridGroupDerivative 45=((26/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_46 : GridGroupGeometry 46 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 46=(21:Fin 27) from rfl,
    show gridGroupIndex 46=(180:Fin 780) from rfl,
    show gridGroupPartner 46=(-130:ℤ) from rfl,
    show gridGroupRate 46=((18/13):ℚ) from rfl,
    show gridGroupDerivative 46=(6:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_47 : GridGroupGeometry 47 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 47=(21:Fin 27) from rfl,
    show gridGroupIndex 47=(195:Fin 780) from rfl,
    show gridGroupPartner 47=(-120:ℤ) from rfl,
    show gridGroupRate 47=((13/8):ℚ) from rfl,
    show gridGroupDerivative 47=((13/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_48 : GridGroupGeometry 48 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 48=(21:Fin 27) from rfl,
    show gridGroupIndex 48=(200:Fin 780) from rfl,
    show gridGroupPartner 48=(-117:ℤ) from rfl,
    show gridGroupRate 48=((200/117):ℚ) from rfl,
    show gridGroupDerivative 48=((20/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_49 : GridGroupGeometry 49 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 49=(21:Fin 27) from rfl,
    show gridGroupIndex 49=(225:Fin 780) from rfl,
    show gridGroupPartner 49=(-104:ℤ) from rfl,
    show gridGroupRate 49=((225/104):ℚ) from rfl,
    show gridGroupDerivative 49=((15/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_50 : GridGroupGeometry 50 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 50=(21:Fin 27) from rfl,
    show gridGroupIndex 50=(234:Fin 780) from rfl,
    show gridGroupPartner 50=(-100:ℤ) from rfl,
    show gridGroupRate 50=((117/50):ℚ) from rfl,
    show gridGroupDerivative 50=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_51 : GridGroupGeometry 51 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 51=(21:Fin 27) from rfl,
    show gridGroupIndex 51=(260:Fin 780) from rfl,
    show gridGroupPartner 51=(-90:ℤ) from rfl,
    show gridGroupRate 51=((26/9):ℚ) from rfl,
    show gridGroupDerivative 51=((26/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_52 : GridGroupGeometry 52 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 52=(21:Fin 27) from rfl,
    show gridGroupIndex 52=(300:Fin 780) from rfl,
    show gridGroupPartner 52=(-78:ℤ) from rfl,
    show gridGroupRate 52=((50/13):ℚ) from rfl,
    show gridGroupDerivative 52=(10:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_53 : GridGroupGeometry 53 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 53=(21:Fin 27) from rfl,
    show gridGroupIndex 53=(312:Fin 780) from rfl,
    show gridGroupPartner 53=(-75:ℤ) from rfl,
    show gridGroupRate 53=((104/25):ℚ) from rfl,
    show gridGroupDerivative 53=((52/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_54 : GridGroupGeometry 54 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 54=(21:Fin 27) from rfl,
    show gridGroupIndex 54=(325:Fin 780) from rfl,
    show gridGroupPartner 54=(-72:ℤ) from rfl,
    show gridGroupRate 54=((325/72):ℚ) from rfl,
    show gridGroupDerivative 54=((65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_55 : GridGroupGeometry 55 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 55=(21:Fin 27) from rfl,
    show gridGroupIndex 55=(360:Fin 780) from rfl,
    show gridGroupPartner 55=(-65:ℤ) from rfl,
    show gridGroupRate 55=((72/13):ℚ) from rfl,
    show gridGroupDerivative 55=(12:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_56 : GridGroupGeometry 56 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 56=(21:Fin 27) from rfl,
    show gridGroupIndex 56=(390:Fin 780) from rfl,
    show gridGroupPartner 56=(-60:ℤ) from rfl,
    show gridGroupRate 56=((13/2):ℚ) from rfl,
    show gridGroupDerivative 56=(13:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_57 : GridGroupGeometry 57 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 57=(21:Fin 27) from rfl,
    show gridGroupIndex 57=(450:Fin 780) from rfl,
    show gridGroupPartner 57=(-52:ℤ) from rfl,
    show gridGroupRate 57=((225/26):ℚ) from rfl,
    show gridGroupDerivative 57=(15:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_58 : GridGroupGeometry 58 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 58=(21:Fin 27) from rfl,
    show gridGroupIndex 58=(468:Fin 780) from rfl,
    show gridGroupPartner 58=(-50:ℤ) from rfl,
    show gridGroupRate 58=((234/25):ℚ) from rfl,
    show gridGroupDerivative 58=((78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_59 : GridGroupGeometry 59 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 59=(21:Fin 27) from rfl,
    show gridGroupIndex 59=(520:Fin 780) from rfl,
    show gridGroupPartner 59=(-45:ℤ) from rfl,
    show gridGroupRate 59=((104/9):ℚ) from rfl,
    show gridGroupDerivative 59=((52/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_60 : GridGroupGeometry 60 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 60=(21:Fin 27) from rfl,
    show gridGroupIndex 60=(585:Fin 780) from rfl,
    show gridGroupPartner 60=(-40:ℤ) from rfl,
    show gridGroupRate 60=((117/8):ℚ) from rfl,
    show gridGroupDerivative 60=((39/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_61 : GridGroupGeometry 61 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 61=(21:Fin 27) from rfl,
    show gridGroupIndex 61=(600:Fin 780) from rfl,
    show gridGroupPartner 61=(-39:ℤ) from rfl,
    show gridGroupRate 61=((200/13):ℚ) from rfl,
    show gridGroupDerivative 61=(20:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_62 : GridGroupGeometry 62 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 62=(21:Fin 27) from rfl,
    show gridGroupIndex 62=(650:Fin 780) from rfl,
    show gridGroupPartner 62=(-36:ℤ) from rfl,
    show gridGroupRate 62=((325/18):ℚ) from rfl,
    show gridGroupDerivative 62=((65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 21=!![0,1;-26,0] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_63 : GridGroupGeometry 63 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 63=(24:Fin 27) from rfl,
    show gridGroupIndex 63=(770:Fin 780) from rfl,
    show gridGroupPartner 63=(2340:ℤ) from rfl,
    show gridGroupRate 63=((1/234):ℚ) from rfl,
    show gridGroupDerivative 63=((-1/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_64 : GridGroupGeometry 64 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 64=(24:Fin 27) from rfl,
    show gridGroupIndex 64=(771:Fin 780) from rfl,
    show gridGroupPartner 64=(2600:ℤ) from rfl,
    show gridGroupRate 64=((9/2600):ℚ) from rfl,
    show gridGroupDerivative 64=((-3/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_65 : GridGroupGeometry 65 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 65=(24:Fin 27) from rfl,
    show gridGroupIndex 65=(772:Fin 780) from rfl,
    show gridGroupPartner 65=(2925:ℤ) from rfl,
    show gridGroupRate 65=((8/2925):ℚ) from rfl,
    show gridGroupDerivative 65=((-4/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_66 : GridGroupGeometry 66 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 66=(24:Fin 27) from rfl,
    show gridGroupIndex 66=(774:Fin 780) from rfl,
    show gridGroupPartner 66=(3900:ℤ) from rfl,
    show gridGroupRate 66=((1/650):ℚ) from rfl,
    show gridGroupDerivative 66=((-1/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_67 : GridGroupGeometry 67 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 67=(24:Fin 27) from rfl,
    show gridGroupIndex 67=(775:Fin 780) from rfl,
    show gridGroupPartner 67=(4680:ℤ) from rfl,
    show gridGroupRate 67=((1/936):ℚ) from rfl,
    show gridGroupDerivative 67=((-1/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_68 : GridGroupGeometry 68 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 68=(24:Fin 27) from rfl,
    show gridGroupIndex 68=(776:Fin 780) from rfl,
    show gridGroupPartner 68=(5850:ℤ) from rfl,
    show gridGroupRate 68=((2/2925):ℚ) from rfl,
    show gridGroupDerivative 68=((-2/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_69 : GridGroupGeometry 69 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 69=(24:Fin 27) from rfl,
    show gridGroupIndex 69=(777:Fin 780) from rfl,
    show gridGroupPartner 69=(7800:ℤ) from rfl,
    show gridGroupRate 69=((1/2600):ℚ) from rfl,
    show gridGroupDerivative 69=((-1/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_70 : GridGroupGeometry 70 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 70=(24:Fin 27) from rfl,
    show gridGroupIndex 70=(778:Fin 780) from rfl,
    show gridGroupPartner 70=(11700:ℤ) from rfl,
    show gridGroupRate 70=((1/5850):ℚ) from rfl,
    show gridGroupDerivative 70=((-1/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_71 : GridGroupGeometry 71 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 71=(24:Fin 27) from rfl,
    show gridGroupIndex 71=(779:Fin 780) from rfl,
    show gridGroupPartner 71=(23400:ℤ) from rfl,
    show gridGroupRate 71=((1/23400):ℚ) from rfl,
    show gridGroupDerivative 71=((-1/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 24=!![0,1;-26,26] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_72 : GridGroupGeometry 72 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 72=(9:Fin 27) from rfl,
    show gridGroupIndex 72=(690:Fin 780) from rfl,
    show gridGroupPartner 72=(-29:ℤ) from rfl,
    show gridGroupRate 72=(900:ℚ) from rfl,
    show gridGroupDerivative 72=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 9=!![1,-2;-26,53] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_73 : GridGroupGeometry 73 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 73=(1:Fin 27) from rfl,
    show gridGroupIndex 73=(630:Fin 780) from rfl,
    show gridGroupPartner 73=(31:ℤ) from rfl,
    show gridGroupRate 73=(900:ℚ) from rfl,
    show gridGroupDerivative 73=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 1=!![1,-2;26,-51] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_74 : GridGroupGeometry 74 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 74=(10:Fin 27) from rfl,
    show gridGroupIndex 74=(570:Fin 780) from rfl,
    show gridGroupPartner 74=(-14:ℤ) from rfl,
    show gridGroupRate 74=(225:ℚ) from rfl,
    show gridGroupDerivative 74=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 10=!![1,-1;-52,53] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_75 : GridGroupGeometry 75 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 75=(8:Fin 27) from rfl,
    show gridGroupIndex 75=(360:Fin 780) from rfl,
    show gridGroupPartner 75=(-28:ℤ) from rfl,
    show gridGroupRate 75=(225:ℚ) from rfl,
    show gridGroupDerivative 75=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![1,-1;-26,27] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_76 : GridGroupGeometry 76 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 76=(8:Fin 27) from rfl,
    show gridGroupIndex 76=(510:Fin 780) from rfl,
    show gridGroupPartner 76=(-27:ℤ) from rfl,
    show gridGroupRate 76=(100:ℚ) from rfl,
    show gridGroupDerivative 76=(-260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![1,-1;-26,27] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_77 : GridGroupGeometry 77 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 77=(8:Fin 27) from rfl,
    show gridGroupIndex 77=(710:Fin 780) from rfl,
    show gridGroupPartner 77=(-21:ℤ) from rfl,
    show gridGroupRate 77=((100/9):ℚ) from rfl,
    show gridGroupDerivative 77=((-260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 8=!![1,-1;-26,27] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_78 : GridGroupGeometry 78 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 78=(0:Fin 27) from rfl,
    show gridGroupIndex 78=(300:Fin 780) from rfl,
    show gridGroupPartner 78=(32:ℤ) from rfl,
    show gridGroupRate 78=(225:ℚ) from rfl,
    show gridGroupDerivative 78=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_79 : GridGroupGeometry 79 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 79=(0:Fin 27) from rfl,
    show gridGroupIndex 79=(450:Fin 780) from rfl,
    show gridGroupPartner 79=(33:ℤ) from rfl,
    show gridGroupRate 79=(100:ℚ) from rfl,
    show gridGroupDerivative 79=(-260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_80 : GridGroupGeometry 80 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 80=(0:Fin 27) from rfl,
    show gridGroupIndex 80=(570:Fin 780) from rfl,
    show gridGroupPartner 80=(35:ℤ) from rfl,
    show gridGroupRate 80=(36:ℚ) from rfl,
    show gridGroupDerivative 80=(-156:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_81 : GridGroupGeometry 81 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 81=(0:Fin 27) from rfl,
    show gridGroupIndex 81=(675:Fin 780) from rfl,
    show gridGroupPartner 81=(42:ℤ) from rfl,
    show gridGroupRate 81=((25/4):ℚ) from rfl,
    show gridGroupDerivative 81=(-65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_82 : GridGroupGeometry 82 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 82=(0:Fin 27) from rfl,
    show gridGroupIndex 82=(700:Fin 780) from rfl,
    show gridGroupPartner 82=(48:ℤ) from rfl,
    show gridGroupRate 82=((25/9):ℚ) from rfl,
    show gridGroupDerivative 82=((-130/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_83 : GridGroupGeometry 83 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 83=(0:Fin 27) from rfl,
    show gridGroupIndex 83=(714:Fin 780) from rfl,
    show gridGroupPartner 83=(55:ℤ) from rfl,
    show gridGroupRate 83=((36/25):ℚ) from rfl,
    show gridGroupDerivative 83=((-156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_84 : GridGroupGeometry 84 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 84=(0:Fin 27) from rfl,
    show gridGroupIndex 84=(725:Fin 780) from rfl,
    show gridGroupPartner 84=(66:ℤ) from rfl,
    show gridGroupRate 84=((25/36):ℚ) from rfl,
    show gridGroupDerivative 84=((-65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_85 : GridGroupGeometry 85 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 85=(0:Fin 27) from rfl,
    show gridGroupIndex 85=(732:Fin 780) from rfl,
    show gridGroupPartner 85=(80:ℤ) from rfl,
    show gridGroupRate 85=((9/25):ℚ) from rfl,
    show gridGroupDerivative 85=((-78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_86 : GridGroupGeometry 86 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 86=(0:Fin 27) from rfl,
    show gridGroupIndex 86=(738:Fin 780) from rfl,
    show gridGroupPartner 86=(105:ℤ) from rfl,
    show gridGroupRate 86=((4/25):ℚ) from rfl,
    show gridGroupDerivative 86=((-52/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_87 : GridGroupGeometry 87 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 87=(0:Fin 27) from rfl,
    show gridGroupIndex 87=(745:Fin 780) from rfl,
    show gridGroupPartner 87=(210:ℤ) from rfl,
    show gridGroupRate 87=((1/36):ℚ) from rfl,
    show gridGroupDerivative 87=((-13/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_88 : GridGroupGeometry 88 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 88=(0:Fin 27) from rfl,
    show gridGroupIndex 88=(747:Fin 780) from rfl,
    show gridGroupPartner 88=(330:ℤ) from rfl,
    show gridGroupRate 88=((1/100):ℚ) from rfl,
    show gridGroupDerivative 88=((-13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_89 : GridGroupGeometry 89 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 89=(0:Fin 27) from rfl,
    show gridGroupIndex 89=(748:Fin 780) from rfl,
    show gridGroupPartner 89=(480:ℤ) from rfl,
    show gridGroupRate 89=((1/225):ℚ) from rfl,
    show gridGroupDerivative 89=((-26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_90 : GridGroupGeometry 90 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 90=(0:Fin 27) from rfl,
    show gridGroupIndex 90=(749:Fin 780) from rfl,
    show gridGroupPartner 90=(930:ℤ) from rfl,
    show gridGroupRate 90=((1/900):ℚ) from rfl,
    show gridGroupDerivative 90=((-13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 0=!![1,-1;26,-25] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_91 : GridGroupGeometry 91 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 91=(2:Fin 27) from rfl,
    show gridGroupIndex 91=(540:Fin 780) from rfl,
    show gridGroupPartner 91=(16:ℤ) from rfl,
    show gridGroupRate 91=(225:ℚ) from rfl,
    show gridGroupDerivative 91=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![1,-1;52,-51] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_92 : GridGroupGeometry 92 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 92=(2:Fin 27) from rfl,
    show gridGroupIndex 92=(764:Fin 780) from rfl,
    show gridGroupPartner 92=(240:ℤ) from rfl,
    show gridGroupRate 92=((1/225):ℚ) from rfl,
    show gridGroupDerivative 92=((-52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 2=!![1,-1;52,-51] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_93 : GridGroupGeometry 93 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 93=(11:Fin 27) from rfl,
    show gridGroupIndex 93=(11:Fin 780) from rfl,
    show gridGroupPartner 93=(-110:ℤ) from rfl,
    show gridGroupRate 93=((1/100):ℚ) from rfl,
    show gridGroupDerivative 93=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 11=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_94 : GridGroupGeometry 94 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 94=(11:Fin 27) from rfl,
    show gridGroupIndex 94=(14:Fin 780) from rfl,
    show gridGroupPartner 94=(-35:ℤ) from rfl,
    show gridGroupRate 94=((4/25):ℚ) from rfl,
    show gridGroupDerivative 94=((156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 11=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_95 : GridGroupGeometry 95 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 95=(11:Fin 27) from rfl,
    show gridGroupIndex 95=(110:Fin 780) from rfl,
    show gridGroupPartner 95=(-11:ℤ) from rfl,
    show gridGroupRate 95=(100:ℚ) from rfl,
    show gridGroupDerivative 95=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 11=!![1,0;-78,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_96 : GridGroupGeometry 96 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 96=(7:Fin 27) from rfl,
    show gridGroupIndex 96=(21:Fin 780) from rfl,
    show gridGroupPartner 96=(70:ℤ) from rfl,
    show gridGroupRate 96=((9/100):ℚ) from rfl,
    show gridGroupDerivative 96=((-39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 7=!![1,0;-26,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_97 : GridGroupGeometry 97 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 97=(7:Fin 27) from rfl,
    show gridGroupIndex 97=(27:Fin 780) from rfl,
    show gridGroupPartner 97=(270:ℤ) from rfl,
    show gridGroupRate 97=((1/100):ℚ) from rfl,
    show gridGroupDerivative 97=((-13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 7=!![1,0;-26,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_98 : GridGroupGeometry 98 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 98=(7:Fin 27) from rfl,
    show gridGroupIndex 98=(28:Fin 780) from rfl,
    show gridGroupPartner 98=(420:ℤ) from rfl,
    show gridGroupRate 98=((1/225):ℚ) from rfl,
    show gridGroupDerivative 98=((-26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 7=!![1,0;-26,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_99 : GridGroupGeometry 99 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 99=(7:Fin 27) from rfl,
    show gridGroupIndex 99=(29:Fin 780) from rfl,
    show gridGroupPartner 99=(870:ℤ) from rfl,
    show gridGroupRate 99=((1/900):ℚ) from rfl,
    show gridGroupDerivative 99=((-13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 7=!![1,0;-26,1] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_100 : GridGroupGeometry 100 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 100=(18:Fin 27) from rfl,
    show gridGroupIndex 100=(180:Fin 780) from rfl,
    show gridGroupPartner 100=(-59:ℤ) from rfl,
    show gridGroupRate 100=(1800:ℚ) from rfl,
    show gridGroupDerivative 100=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 18=!![2,-5;-26,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_101 : GridGroupGeometry 101 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 101=(17:Fin 27) from rfl,
    show gridGroupIndex 101=(300:Fin 780) from rfl,
    show gridGroupPartner 101=(-58:ℤ) from rfl,
    show gridGroupRate 101=(450:ℚ) from rfl,
    show gridGroupDerivative 101=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 17=!![2,-3;-26,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_102 : GridGroupGeometry 102 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 102=(17:Fin 27) from rfl,
    show gridGroupIndex 102=(600:Fin 780) from rfl,
    show gridGroupPartner 102=(-57:ℤ) from rfl,
    show gridGroupRate 102=(200:ℚ) from rfl,
    show gridGroupDerivative 102=(-260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 17=!![2,-3;-26,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_103 : GridGroupGeometry 103 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 103=(17:Fin 27) from rfl,
    show gridGroupIndex 103=(750:Fin 780) from rfl,
    show gridGroupPartner 103=(-56:ℤ) from rfl,
    show gridGroupRate 103=((225/2):ℚ) from rfl,
    show gridGroupDerivative 103=(-195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 17=!![2,-3;-26,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_104 : GridGroupGeometry 104 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 104=(6:Fin 27) from rfl,
    show gridGroupIndex 104=(240:Fin 780) from rfl,
    show gridGroupPartner 104=(62:ℤ) from rfl,
    show gridGroupRate 104=(450:ℚ) from rfl,
    show gridGroupDerivative 104=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 6=!![2,-3;26,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_105 : GridGroupGeometry 105 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 105=(6:Fin 27) from rfl,
    show gridGroupIndex 105=(540:Fin 780) from rfl,
    show gridGroupPartner 105=(63:ℤ) from rfl,
    show gridGroupRate 105=(200:ℚ) from rfl,
    show gridGroupDerivative 105=(-260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 6=!![2,-3;26,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_106 : GridGroupGeometry 106 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 106=(6:Fin 27) from rfl,
    show gridGroupIndex 106=(690:Fin 780) from rfl,
    show gridGroupPartner 106=(64:ℤ) from rfl,
    show gridGroupRate 106=((225/2):ℚ) from rfl,
    show gridGroupDerivative 106=(-195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 6=!![2,-3;26,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_107 : GridGroupGeometry 107 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 107=(12:Fin 27) from rfl,
    show gridGroupIndex 107=(324:Fin 780) from rfl,
    show gridGroupPartner 107=(-11:ℤ) from rfl,
    show gridGroupRate 107=(72:ℚ) from rfl,
    show gridGroupDerivative 107=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_108 : GridGroupGeometry 108 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 108=(12:Fin 27) from rfl,
    show gridGroupIndex 108=(360:Fin 780) from rfl,
    show gridGroupPartner 108=(-10:ℤ) from rfl,
    show gridGroupRate 108=(18:ℚ) from rfl,
    show gridGroupDerivative 108=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_109 : GridGroupGeometry 109 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 109=(12:Fin 27) from rfl,
    show gridGroupIndex 109=(372:Fin 780) from rfl,
    show gridGroupPartner 109=(-9:ℤ) from rfl,
    show gridGroupRate 109=(8:ℚ) from rfl,
    show gridGroupDerivative 109=(-260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_110 : GridGroupGeometry 110 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 110=(12:Fin 27) from rfl,
    show gridGroupIndex 110=(378:Fin 780) from rfl,
    show gridGroupPartner 110=(-8:ℤ) from rfl,
    show gridGroupRate 110=((9/2):ℚ) from rfl,
    show gridGroupDerivative 110=(-195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_111 : GridGroupGeometry 111 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 111=(12:Fin 27) from rfl,
    show gridGroupIndex 111=(384:Fin 780) from rfl,
    show gridGroupPartner 111=(-6:ℤ) from rfl,
    show gridGroupRate 111=(2:ℚ) from rfl,
    show gridGroupDerivative 111=(-130:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_112 : GridGroupGeometry 112 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 112=(12:Fin 27) from rfl,
    show gridGroupIndex 112=(387:Fin 780) from rfl,
    show gridGroupPartner 112=(-4:ℤ) from rfl,
    show gridGroupRate 112=((9/8):ℚ) from rfl,
    show gridGroupDerivative 112=((-195/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_113 : GridGroupGeometry 113 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 113=(12:Fin 27) from rfl,
    show gridGroupIndex 113=(388:Fin 780) from rfl,
    show gridGroupPartner 113=(-3:ℤ) from rfl,
    show gridGroupRate 113=((8/9):ℚ) from rfl,
    show gridGroupDerivative 113=((-260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_114 : GridGroupGeometry 114 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 114=(12:Fin 27) from rfl,
    show gridGroupIndex 114=(390:Fin 780) from rfl,
    show gridGroupPartner 114=(0:ℤ) from rfl,
    show gridGroupRate 114=((1/2):ℚ) from rfl,
    show gridGroupDerivative 114=(-65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_115 : GridGroupGeometry 115 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 115=(12:Fin 27) from rfl,
    show gridGroupIndex 115=(392:Fin 780) from rfl,
    show gridGroupPartner 115=(6:ℤ) from rfl,
    show gridGroupRate 115=((2/9):ℚ) from rfl,
    show gridGroupDerivative 115=((-130/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_116 : GridGroupGeometry 116 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 116=(12:Fin 27) from rfl,
    show gridGroupIndex 116=(393:Fin 780) from rfl,
    show gridGroupPartner 116=(12:ℤ) from rfl,
    show gridGroupRate 116=((1/8):ℚ) from rfl,
    show gridGroupDerivative 116=((-65/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_117 : GridGroupGeometry 117 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 117=(12:Fin 27) from rfl,
    show gridGroupIndex 117=(394:Fin 780) from rfl,
    show gridGroupPartner 117=(24:ℤ) from rfl,
    show gridGroupRate 117=((1/18):ℚ) from rfl,
    show gridGroupDerivative 117=((-65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_118 : GridGroupGeometry 118 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 118=(12:Fin 27) from rfl,
    show gridGroupIndex 118=(395:Fin 780) from rfl,
    show gridGroupPartner 118=(60:ℤ) from rfl,
    show gridGroupRate 118=((1/72):ℚ) from rfl,
    show gridGroupDerivative 118=((-65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_119 : GridGroupGeometry 119 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 119=(12:Fin 27) from rfl,
    show gridGroupIndex 119=(397:Fin 780) from rfl,
    show gridGroupPartner 119=(-84:ℤ) from rfl,
    show gridGroupRate 119=((1/72):ℚ) from rfl,
    show gridGroupDerivative 119=((65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_120 : GridGroupGeometry 120 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 120=(12:Fin 27) from rfl,
    show gridGroupIndex 120=(398:Fin 780) from rfl,
    show gridGroupPartner 120=(-48:ℤ) from rfl,
    show gridGroupRate 120=((1/18):ℚ) from rfl,
    show gridGroupDerivative 120=((65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_121 : GridGroupGeometry 121 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 121=(12:Fin 27) from rfl,
    show gridGroupIndex 121=(399:Fin 780) from rfl,
    show gridGroupPartner 121=(-36:ℤ) from rfl,
    show gridGroupRate 121=((1/8):ℚ) from rfl,
    show gridGroupDerivative 121=((65/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_122 : GridGroupGeometry 122 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 122=(12:Fin 27) from rfl,
    show gridGroupIndex 122=(400:Fin 780) from rfl,
    show gridGroupPartner 122=(-30:ℤ) from rfl,
    show gridGroupRate 122=((2/9):ℚ) from rfl,
    show gridGroupDerivative 122=((130/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_123 : GridGroupGeometry 123 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 123=(12:Fin 27) from rfl,
    show gridGroupIndex 123=(402:Fin 780) from rfl,
    show gridGroupPartner 123=(-24:ℤ) from rfl,
    show gridGroupRate 123=((1/2):ℚ) from rfl,
    show gridGroupDerivative 123=(65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_124 : GridGroupGeometry 124 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 124=(12:Fin 27) from rfl,
    show gridGroupIndex 124=(404:Fin 780) from rfl,
    show gridGroupPartner 124=(-21:ℤ) from rfl,
    show gridGroupRate 124=((8/9):ℚ) from rfl,
    show gridGroupDerivative 124=((260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_125 : GridGroupGeometry 125 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 125=(12:Fin 27) from rfl,
    show gridGroupIndex 125=(405:Fin 780) from rfl,
    show gridGroupPartner 125=(-20:ℤ) from rfl,
    show gridGroupRate 125=((9/8):ℚ) from rfl,
    show gridGroupDerivative 125=((195/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_126 : GridGroupGeometry 126 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 126=(12:Fin 27) from rfl,
    show gridGroupIndex 126=(408:Fin 780) from rfl,
    show gridGroupPartner 126=(-18:ℤ) from rfl,
    show gridGroupRate 126=(2:ℚ) from rfl,
    show gridGroupDerivative 126=(130:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_127 : GridGroupGeometry 127 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 127=(12:Fin 27) from rfl,
    show gridGroupIndex 127=(414:Fin 780) from rfl,
    show gridGroupPartner 127=(-16:ℤ) from rfl,
    show gridGroupRate 127=((9/2):ℚ) from rfl,
    show gridGroupDerivative 127=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_128 : GridGroupGeometry 128 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 128=(12:Fin 27) from rfl,
    show gridGroupIndex 128=(420:Fin 780) from rfl,
    show gridGroupPartner 128=(-15:ℤ) from rfl,
    show gridGroupRate 128=(8:ℚ) from rfl,
    show gridGroupDerivative 128=(260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_129 : GridGroupGeometry 129 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 129=(12:Fin 27) from rfl,
    show gridGroupIndex 129=(432:Fin 780) from rfl,
    show gridGroupPartner 129=(-14:ℤ) from rfl,
    show gridGroupRate 129=(18:ℚ) from rfl,
    show gridGroupDerivative 129=(390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_130 : GridGroupGeometry 130 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 130=(12:Fin 27) from rfl,
    show gridGroupIndex 130=(468:Fin 780) from rfl,
    show gridGroupPartner 130=(-13:ℤ) from rfl,
    show gridGroupRate 130=(72:ℚ) from rfl,
    show gridGroupDerivative 130=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 12=!![2,-1;-130,66] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_131 : GridGroupGeometry 131 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 131=(13:Fin 27) from rfl,
    show gridGroupIndex 131=(200:Fin 780) from rfl,
    show gridGroupPartner 131=(-19:ℤ) from rfl,
    show gridGroupRate 131=(200:ℚ) from rfl,
    show gridGroupDerivative 131=(-780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_132 : GridGroupGeometry 132 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 132=(13:Fin 27) from rfl,
    show gridGroupIndex 132=(300:Fin 780) from rfl,
    show gridGroupPartner 132=(-18:ℤ) from rfl,
    show gridGroupRate 132=(50:ℚ) from rfl,
    show gridGroupDerivative 132=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_133 : GridGroupGeometry 133 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 133=(13:Fin 27) from rfl,
    show gridGroupIndex 133=(350:Fin 780) from rfl,
    show gridGroupPartner 133=(-16:ℤ) from rfl,
    show gridGroupRate 133=((25/2):ℚ) from rfl,
    show gridGroupDerivative 133=(-195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_134 : GridGroupGeometry 134 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 134=(13:Fin 27) from rfl,
    show gridGroupIndex 134=(375:Fin 780) from rfl,
    show gridGroupPartner 134=(-12:ℤ) from rfl,
    show gridGroupRate 134=((25/8):ℚ) from rfl,
    show gridGroupDerivative 134=((-195/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_135 : GridGroupGeometry 135 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 135=(13:Fin 27) from rfl,
    show gridGroupIndex 135=(380:Fin 780) from rfl,
    show gridGroupPartner 135=(-10:ℤ) from rfl,
    show gridGroupRate 135=(2:ℚ) from rfl,
    show gridGroupDerivative 135=(-78:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_136 : GridGroupGeometry 136 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 136=(13:Fin 27) from rfl,
    show gridGroupIndex 136=(401:Fin 780) from rfl,
    show gridGroupPartner 136=(-220:ℤ) from rfl,
    show gridGroupRate 136=((1/200):ℚ) from rfl,
    show gridGroupDerivative 136=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_137 : GridGroupGeometry 137 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 137=(13:Fin 27) from rfl,
    show gridGroupIndex 137=(410:Fin 780) from rfl,
    show gridGroupPartner 137=(-40:ℤ) from rfl,
    show gridGroupRate 137=((1/2):ℚ) from rfl,
    show gridGroupDerivative 137=(39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_138 : GridGroupGeometry 138 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 138=(13:Fin 27) from rfl,
    show gridGroupIndex 138=(425:Fin 780) from rfl,
    show gridGroupPartner 138=(-28:ℤ) from rfl,
    show gridGroupRate 138=((25/8):ℚ) from rfl,
    show gridGroupDerivative 138=((195/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_139 : GridGroupGeometry 139 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 139=(13:Fin 27) from rfl,
    show gridGroupIndex 139=(440:Fin 780) from rfl,
    show gridGroupPartner 139=(-25:ℤ) from rfl,
    show gridGroupRate 139=(8:ℚ) from rfl,
    show gridGroupDerivative 139=(156:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_140 : GridGroupGeometry 140 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 140=(13:Fin 27) from rfl,
    show gridGroupIndex 140=(450:Fin 780) from rfl,
    show gridGroupPartner 140=(-24:ℤ) from rfl,
    show gridGroupRate 140=((25/2):ℚ) from rfl,
    show gridGroupDerivative 140=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_141 : GridGroupGeometry 141 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 141=(13:Fin 27) from rfl,
    show gridGroupIndex 141=(500:Fin 780) from rfl,
    show gridGroupPartner 141=(-22:ℤ) from rfl,
    show gridGroupRate 141=(50:ℚ) from rfl,
    show gridGroupDerivative 141=(390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_142 : GridGroupGeometry 142 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 142=(13:Fin 27) from rfl,
    show gridGroupIndex 142=(600:Fin 780) from rfl,
    show gridGroupPartner 142=(-21:ℤ) from rfl,
    show gridGroupRate 142=(200:ℚ) from rfl,
    show gridGroupDerivative 142=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 13=!![2,-1;-78,40] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_143 : GridGroupGeometry 143 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 143=(14:Fin 27) from rfl,
    show gridGroupIndex 143=(60:Fin 780) from rfl,
    show gridGroupPartner 143=(-55:ℤ) from rfl,
    show gridGroupRate 143=(72:ℚ) from rfl,
    show gridGroupDerivative 143=(-156:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_144 : GridGroupGeometry 144 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 144=(14:Fin 27) from rfl,
    show gridGroupIndex 144=(120:Fin 780) from rfl,
    show gridGroupPartner 144=(-54:ℤ) from rfl,
    show gridGroupRate 144=(50:ℚ) from rfl,
    show gridGroupDerivative 144=(-130:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_145 : GridGroupGeometry 145 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 145=(14:Fin 27) from rfl,
    show gridGroupIndex 145=(220:Fin 780) from rfl,
    show gridGroupPartner 145=(-51:ℤ) from rfl,
    show gridGroupRate 145=((200/9):ℚ) from rfl,
    show gridGroupDerivative 145=((-260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_146 : GridGroupGeometry 146 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 146=(14:Fin 27) from rfl,
    show gridGroupIndex 146=(270:Fin 780) from rfl,
    show gridGroupPartner 146=(-48:ℤ) from rfl,
    show gridGroupRate 146=((25/2):ℚ) from rfl,
    show gridGroupDerivative 146=(-65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_147 : GridGroupGeometry 147 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 147=(14:Fin 27) from rfl,
    show gridGroupIndex 147=(320:Fin 780) from rfl,
    show gridGroupPartner 147=(-42:ℤ) from rfl,
    show gridGroupRate 147=((50/9):ℚ) from rfl,
    show gridGroupDerivative 147=((-130/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_148 : GridGroupGeometry 148 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 148=(14:Fin 27) from rfl,
    show gridGroupIndex 148=(330:Fin 780) from rfl,
    show gridGroupPartner 148=(-40:ℤ) from rfl,
    show gridGroupRate 148=((9/2):ℚ) from rfl,
    show gridGroupDerivative 148=(-39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_149 : GridGroupGeometry 149 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 149=(14:Fin 27) from rfl,
    show gridGroupIndex 149=(345:Fin 780) from rfl,
    show gridGroupPartner 149=(-36:ℤ) from rfl,
    show gridGroupRate 149=((25/8):ℚ) from rfl,
    show gridGroupDerivative 149=((-65/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_150 : GridGroupGeometry 150 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 150=(14:Fin 27) from rfl,
    show gridGroupIndex 150=(348:Fin 780) from rfl,
    show gridGroupPartner 150=(-35:ℤ) from rfl,
    show gridGroupRate 150=((72/25):ℚ) from rfl,
    show gridGroupDerivative 150=((-156/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_151 : GridGroupGeometry 151 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 151=(14:Fin 27) from rfl,
    show gridGroupIndex 151=(370:Fin 780) from rfl,
    show gridGroupPartner 151=(-24:ℤ) from rfl,
    show gridGroupRate 151=((25/18):ℚ) from rfl,
    show gridGroupDerivative 151=((-65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_152 : GridGroupGeometry 152 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 152=(14:Fin 27) from rfl,
    show gridGroupIndex 152=(411:Fin 780) from rfl,
    show gridGroupPartner 152=(140:ℤ) from rfl,
    show gridGroupRate 152=((9/200):ℚ) from rfl,
    show gridGroupDerivative 152=((-39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_153 : GridGroupGeometry 153 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 153=(14:Fin 27) from rfl,
    show gridGroupIndex 153=(412:Fin 780) from rfl,
    show gridGroupPartner 153=(165:ℤ) from rfl,
    show gridGroupRate 153=((8/225):ℚ) from rfl,
    show gridGroupDerivative 153=((-52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_154 : GridGroupGeometry 154 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 154=(14:Fin 27) from rfl,
    show gridGroupIndex 154=(415:Fin 780) from rfl,
    show gridGroupPartner 154=(300:ℤ) from rfl,
    show gridGroupRate 154=((1/72):ℚ) from rfl,
    show gridGroupDerivative 154=((-13/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_155 : GridGroupGeometry 155 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 155=(14:Fin 27) from rfl,
    show gridGroupIndex 155=(416:Fin 780) from rfl,
    show gridGroupPartner 155=(390:ℤ) from rfl,
    show gridGroupRate 155=((2/225):ℚ) from rfl,
    show gridGroupDerivative 155=((-26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_156 : GridGroupGeometry 156 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 156=(14:Fin 27) from rfl,
    show gridGroupIndex 156=(417:Fin 780) from rfl,
    show gridGroupPartner 156=(540:ℤ) from rfl,
    show gridGroupRate 156=((1/200):ℚ) from rfl,
    show gridGroupDerivative 156=((-13/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_157 : GridGroupGeometry 157 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 157=(14:Fin 27) from rfl,
    show gridGroupIndex 157=(418:Fin 780) from rfl,
    show gridGroupPartner 157=(840:ℤ) from rfl,
    show gridGroupRate 157=((1/450):ℚ) from rfl,
    show gridGroupDerivative 157=((-13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_158 : GridGroupGeometry 158 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 158=(14:Fin 27) from rfl,
    show gridGroupIndex 158=(419:Fin 780) from rfl,
    show gridGroupPartner 158=(1740:ℤ) from rfl,
    show gridGroupRate 158=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 158=((-13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_159 : GridGroupGeometry 159 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 159=(14:Fin 27) from rfl,
    show gridGroupIndex 159=(421:Fin 780) from rfl,
    show gridGroupPartner 159=(-1860:ℤ) from rfl,
    show gridGroupRate 159=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 159=((13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_160 : GridGroupGeometry 160 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 160=(14:Fin 27) from rfl,
    show gridGroupIndex 160=(422:Fin 780) from rfl,
    show gridGroupPartner 160=(-960:ℤ) from rfl,
    show gridGroupRate 160=((1/450):ℚ) from rfl,
    show gridGroupDerivative 160=((13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_161 : GridGroupGeometry 161 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 161=(14:Fin 27) from rfl,
    show gridGroupIndex 161=(423:Fin 780) from rfl,
    show gridGroupPartner 161=(-660:ℤ) from rfl,
    show gridGroupRate 161=((1/200):ℚ) from rfl,
    show gridGroupDerivative 161=((13/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_162 : GridGroupGeometry 162 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 162=(14:Fin 27) from rfl,
    show gridGroupIndex 162=(424:Fin 780) from rfl,
    show gridGroupPartner 162=(-510:ℤ) from rfl,
    show gridGroupRate 162=((2/225):ℚ) from rfl,
    show gridGroupDerivative 162=((26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_163 : GridGroupGeometry 163 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 163=(14:Fin 27) from rfl,
    show gridGroupIndex 163=(426:Fin 780) from rfl,
    show gridGroupPartner 163=(-360:ℤ) from rfl,
    show gridGroupRate 163=((1/50):ℚ) from rfl,
    show gridGroupDerivative 163=((13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_164 : GridGroupGeometry 164 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 164=(14:Fin 27) from rfl,
    show gridGroupIndex 164=(428:Fin 780) from rfl,
    show gridGroupPartner 164=(-285:ℤ) from rfl,
    show gridGroupRate 164=((8/225):ℚ) from rfl,
    show gridGroupDerivative 164=((52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_165 : GridGroupGeometry 165 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 165=(14:Fin 27) from rfl,
    show gridGroupIndex 165=(429:Fin 780) from rfl,
    show gridGroupPartner 165=(-260:ℤ) from rfl,
    show gridGroupRate 165=((9/200):ℚ) from rfl,
    show gridGroupDerivative 165=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_166 : GridGroupGeometry 166 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 166=(14:Fin 27) from rfl,
    show gridGroupIndex 166=(430:Fin 780) from rfl,
    show gridGroupPartner 166=(-240:ℤ) from rfl,
    show gridGroupRate 166=((1/18):ℚ) from rfl,
    show gridGroupDerivative 166=((13/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_167 : GridGroupGeometry 167 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 167=(14:Fin 27) from rfl,
    show gridGroupIndex 167=(435:Fin 780) from rfl,
    show gridGroupPartner 167=(-180:ℤ) from rfl,
    show gridGroupRate 167=((1/8):ℚ) from rfl,
    show gridGroupDerivative 167=((13/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_168 : GridGroupGeometry 168 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 168=(14:Fin 27) from rfl,
    show gridGroupIndex 168=(438:Fin 780) from rfl,
    show gridGroupPartner 168=(-160:ℤ) from rfl,
    show gridGroupRate 168=((9/50):ℚ) from rfl,
    show gridGroupDerivative 168=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_169 : GridGroupGeometry 169 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 169=(14:Fin 27) from rfl,
    show gridGroupIndex 169=(445:Fin 780) from rfl,
    show gridGroupPartner 169=(-132:ℤ) from rfl,
    show gridGroupRate 169=((25/72):ℚ) from rfl,
    show gridGroupDerivative 169=((65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_170 : GridGroupGeometry 170 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 170=(14:Fin 27) from rfl,
    show gridGroupIndex 170=(456:Fin 780) from rfl,
    show gridGroupPartner 170=(-110:ℤ) from rfl,
    show gridGroupRate 170=((18/25):ℚ) from rfl,
    show gridGroupDerivative 170=((78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_171 : GridGroupGeometry 171 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 171=(14:Fin 27) from rfl,
    show gridGroupIndex 171=(460:Fin 780) from rfl,
    show gridGroupPartner 171=(-105:ℤ) from rfl,
    show gridGroupRate 171=((8/9):ℚ) from rfl,
    show gridGroupDerivative 171=((52/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_172 : GridGroupGeometry 172 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 172=(14:Fin 27) from rfl,
    show gridGroupIndex 172=(465:Fin 780) from rfl,
    show gridGroupPartner 172=(-100:ℤ) from rfl,
    show gridGroupRate 172=((9/8):ℚ) from rfl,
    show gridGroupDerivative 172=((39/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_173 : GridGroupGeometry 173 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 173=(14:Fin 27) from rfl,
    show gridGroupIndex 173=(470:Fin 780) from rfl,
    show gridGroupPartner 173=(-96:ℤ) from rfl,
    show gridGroupRate 173=((25/18):ℚ) from rfl,
    show gridGroupDerivative 173=((65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_174 : GridGroupGeometry 174 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 174=(14:Fin 27) from rfl,
    show gridGroupIndex 174=(480:Fin 780) from rfl,
    show gridGroupPartner 174=(-90:ℤ) from rfl,
    show gridGroupRate 174=(2:ℚ) from rfl,
    show gridGroupDerivative 174=(26:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_175 : GridGroupGeometry 175 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 175=(14:Fin 27) from rfl,
    show gridGroupIndex 175=(495:Fin 780) from rfl,
    show gridGroupPartner 175=(-84:ℤ) from rfl,
    show gridGroupRate 175=((25/8):ℚ) from rfl,
    show gridGroupDerivative 175=((65/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_176 : GridGroupGeometry 176 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 176=(14:Fin 27) from rfl,
    show gridGroupIndex 176=(510:Fin 780) from rfl,
    show gridGroupPartner 176=(-80:ℤ) from rfl,
    show gridGroupRate 176=((9/2):ℚ) from rfl,
    show gridGroupDerivative 176=(39:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_177 : GridGroupGeometry 177 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 177=(14:Fin 27) from rfl,
    show gridGroupIndex 177=(540:Fin 780) from rfl,
    show gridGroupPartner 177=(-75:ℤ) from rfl,
    show gridGroupRate 177=(8:ℚ) from rfl,
    show gridGroupDerivative 177=(52:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_178 : GridGroupGeometry 178 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 178=(14:Fin 27) from rfl,
    show gridGroupIndex 178=(570:Fin 780) from rfl,
    show gridGroupPartner 178=(-72:ℤ) from rfl,
    show gridGroupRate 178=((25/2):ℚ) from rfl,
    show gridGroupDerivative 178=(65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_179 : GridGroupGeometry 179 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 179=(14:Fin 27) from rfl,
    show gridGroupIndex 179=(620:Fin 780) from rfl,
    show gridGroupPartner 179=(-69:ℤ) from rfl,
    show gridGroupRate 179=((200/9):ℚ) from rfl,
    show gridGroupDerivative 179=((260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_180 : GridGroupGeometry 180 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 180=(14:Fin 27) from rfl,
    show gridGroupIndex 180=(720:Fin 780) from rfl,
    show gridGroupPartner 180=(-66:ℤ) from rfl,
    show gridGroupRate 180=(50:ℚ) from rfl,
    show gridGroupDerivative 180=(130:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 14=!![2,-1;-26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_181 : GridGroupGeometry 181 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 181=(4:Fin 27) from rfl,
    show gridGroupIndex 181=(160:Fin 780) from rfl,
    show gridGroupPartner 181=(69:ℤ) from rfl,
    show gridGroupRate 181=((200/9):ℚ) from rfl,
    show gridGroupDerivative 181=((-260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_182 : GridGroupGeometry 182 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 182=(4:Fin 27) from rfl,
    show gridGroupIndex 182=(180:Fin 780) from rfl,
    show gridGroupPartner 182=(70:ℤ) from rfl,
    show gridGroupRate 182=(18:ℚ) from rfl,
    show gridGroupDerivative 182=(-78:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_183 : GridGroupGeometry 183 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 183=(4:Fin 27) from rfl,
    show gridGroupIndex 183=(210:Fin 780) from rfl,
    show gridGroupPartner 183=(72:ℤ) from rfl,
    show gridGroupRate 183=((25/2):ℚ) from rfl,
    show gridGroupDerivative 183=(-65:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_184 : GridGroupGeometry 184 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 184=(4:Fin 27) from rfl,
    show gridGroupIndex 184=(285:Fin 780) from rfl,
    show gridGroupPartner 184=(84:ℤ) from rfl,
    show gridGroupRate 184=((25/8):ℚ) from rfl,
    show gridGroupDerivative 184=((-65/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_185 : GridGroupGeometry 185 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 185=(4:Fin 27) from rfl,
    show gridGroupIndex 185=(310:Fin 780) from rfl,
    show gridGroupPartner 185=(96:ℤ) from rfl,
    show gridGroupRate 185=((25/18):ℚ) from rfl,
    show gridGroupDerivative 185=((-65/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_186 : GridGroupGeometry 186 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 186=(4:Fin 27) from rfl,
    show gridGroupIndex 186=(315:Fin 780) from rfl,
    show gridGroupPartner 186=(100:ℤ) from rfl,
    show gridGroupRate 186=((9/8):ℚ) from rfl,
    show gridGroupDerivative 186=((-39/2):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_187 : GridGroupGeometry 187 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 187=(4:Fin 27) from rfl,
    show gridGroupIndex 187=(335:Fin 780) from rfl,
    show gridGroupPartner 187=(132:ℤ) from rfl,
    show gridGroupRate 187=((25/72):ℚ) from rfl,
    show gridGroupDerivative 187=((-65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_188 : GridGroupGeometry 188 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 188=(4:Fin 27) from rfl,
    show gridGroupIndex 188=(340:Fin 780) from rfl,
    show gridGroupPartner 188=(150:ℤ) from rfl,
    show gridGroupRate 188=((2/9):ℚ) from rfl,
    show gridGroupDerivative 188=((-26/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_189 : GridGroupGeometry 189 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 189=(4:Fin 27) from rfl,
    show gridGroupIndex 189=(342:Fin 780) from rfl,
    show gridGroupPartner 189=(160:ℤ) from rfl,
    show gridGroupRate 189=((9/50):ℚ) from rfl,
    show gridGroupDerivative 189=((-39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_190 : GridGroupGeometry 190 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 190=(4:Fin 27) from rfl,
    show gridGroupIndex 190=(351:Fin 780) from rfl,
    show gridGroupPartner 190=(260:ℤ) from rfl,
    show gridGroupRate 190=((9/200):ℚ) from rfl,
    show gridGroupDerivative 190=((-39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_191 : GridGroupGeometry 191 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 191=(4:Fin 27) from rfl,
    show gridGroupIndex 191=(352:Fin 780) from rfl,
    show gridGroupPartner 191=(285:ℤ) from rfl,
    show gridGroupRate 191=((8/225):ℚ) from rfl,
    show gridGroupDerivative 191=((-52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_192 : GridGroupGeometry 192 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 192=(4:Fin 27) from rfl,
    show gridGroupIndex 192=(354:Fin 780) from rfl,
    show gridGroupPartner 192=(360:ℤ) from rfl,
    show gridGroupRate 192=((1/50):ℚ) from rfl,
    show gridGroupDerivative 192=((-13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_193 : GridGroupGeometry 193 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 193=(4:Fin 27) from rfl,
    show gridGroupIndex 193=(355:Fin 780) from rfl,
    show gridGroupPartner 193=(420:ℤ) from rfl,
    show gridGroupRate 193=((1/72):ℚ) from rfl,
    show gridGroupDerivative 193=((-13/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_194 : GridGroupGeometry 194 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 194=(4:Fin 27) from rfl,
    show gridGroupIndex 194=(356:Fin 780) from rfl,
    show gridGroupPartner 194=(510:ℤ) from rfl,
    show gridGroupRate 194=((2/225):ℚ) from rfl,
    show gridGroupDerivative 194=((-26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_195 : GridGroupGeometry 195 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 195=(4:Fin 27) from rfl,
    show gridGroupIndex 195=(357:Fin 780) from rfl,
    show gridGroupPartner 195=(660:ℤ) from rfl,
    show gridGroupRate 195=((1/200):ℚ) from rfl,
    show gridGroupDerivative 195=((-13/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_196 : GridGroupGeometry 196 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 196=(4:Fin 27) from rfl,
    show gridGroupIndex 196=(358:Fin 780) from rfl,
    show gridGroupPartner 196=(960:ℤ) from rfl,
    show gridGroupRate 196=((1/450):ℚ) from rfl,
    show gridGroupDerivative 196=((-13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_197 : GridGroupGeometry 197 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 197=(4:Fin 27) from rfl,
    show gridGroupIndex 197=(359:Fin 780) from rfl,
    show gridGroupPartner 197=(1860:ℤ) from rfl,
    show gridGroupRate 197=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 197=((-13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_198 : GridGroupGeometry 198 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 198=(4:Fin 27) from rfl,
    show gridGroupIndex 198=(361:Fin 780) from rfl,
    show gridGroupPartner 198=(-1740:ℤ) from rfl,
    show gridGroupRate 198=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 198=((13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_199 : GridGroupGeometry 199 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 199=(4:Fin 27) from rfl,
    show gridGroupIndex 199=(362:Fin 780) from rfl,
    show gridGroupPartner 199=(-840:ℤ) from rfl,
    show gridGroupRate 199=((1/450):ℚ) from rfl,
    show gridGroupDerivative 199=((13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_200 : GridGroupGeometry 200 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 200=(4:Fin 27) from rfl,
    show gridGroupIndex 200=(363:Fin 780) from rfl,
    show gridGroupPartner 200=(-540:ℤ) from rfl,
    show gridGroupRate 200=((1/200):ℚ) from rfl,
    show gridGroupDerivative 200=((13/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_201 : GridGroupGeometry 201 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 201=(4:Fin 27) from rfl,
    show gridGroupIndex 201=(364:Fin 780) from rfl,
    show gridGroupPartner 201=(-390:ℤ) from rfl,
    show gridGroupRate 201=((2/225):ℚ) from rfl,
    show gridGroupDerivative 201=((26/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_202 : GridGroupGeometry 202 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 202=(4:Fin 27) from rfl,
    show gridGroupIndex 202=(365:Fin 780) from rfl,
    show gridGroupPartner 202=(-300:ℤ) from rfl,
    show gridGroupRate 202=((1/72):ℚ) from rfl,
    show gridGroupDerivative 202=((13/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_203 : GridGroupGeometry 203 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 203=(4:Fin 27) from rfl,
    show gridGroupIndex 203=(366:Fin 780) from rfl,
    show gridGroupPartner 203=(-240:ℤ) from rfl,
    show gridGroupRate 203=((1/50):ℚ) from rfl,
    show gridGroupDerivative 203=((13/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_204 : GridGroupGeometry 204 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 204=(4:Fin 27) from rfl,
    show gridGroupIndex 204=(368:Fin 780) from rfl,
    show gridGroupPartner 204=(-165:ℤ) from rfl,
    show gridGroupRate 204=((8/225):ℚ) from rfl,
    show gridGroupDerivative 204=((52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_205 : GridGroupGeometry 205 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 205=(4:Fin 27) from rfl,
    show gridGroupIndex 205=(369:Fin 780) from rfl,
    show gridGroupPartner 205=(-140:ℤ) from rfl,
    show gridGroupRate 205=((9/200):ℚ) from rfl,
    show gridGroupDerivative 205=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_206 : GridGroupGeometry 206 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 206=(4:Fin 27) from rfl,
    show gridGroupIndex 206=(385:Fin 780) from rfl,
    show gridGroupPartner 206=(-12:ℤ) from rfl,
    show gridGroupRate 206=((25/72):ℚ) from rfl,
    show gridGroupDerivative 206=((65/6):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_207 : GridGroupGeometry 207 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 207=(4:Fin 27) from rfl,
    show gridGroupIndex 207=(560:Fin 780) from rfl,
    show gridGroupPartner 207=(51:ℤ) from rfl,
    show gridGroupRate 207=((200/9):ℚ) from rfl,
    show gridGroupDerivative 207=((260/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_208 : GridGroupGeometry 208 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 208=(4:Fin 27) from rfl,
    show gridGroupIndex 208=(660:Fin 780) from rfl,
    show gridGroupPartner 208=(54:ℤ) from rfl,
    show gridGroupRate 208=(50:ℚ) from rfl,
    show gridGroupDerivative 208=(130:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 4=!![2,-1;26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_209 : GridGroupGeometry 209 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 209=(3:Fin 27) from rfl,
    show gridGroupIndex 209=(280:Fin 780) from rfl,
    show gridGroupPartner 209=(22:ℤ) from rfl,
    show gridGroupRate 209=(50:ℚ) from rfl,
    show gridGroupDerivative 209=(-390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 3=!![2,-1;78,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_210 : GridGroupGeometry 210 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 210=(3:Fin 27) from rfl,
    show gridGroupIndex 210=(376:Fin 780) from rfl,
    show gridGroupPartner 210=(70:ℤ) from rfl,
    show gridGroupRate 210=((2/25):ℚ) from rfl,
    show gridGroupDerivative 210=((-78/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 3=!![2,-1;78,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_211 : GridGroupGeometry 211 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 211=(3:Fin 27) from rfl,
    show gridGroupIndex 211=(379:Fin 780) from rfl,
    show gridGroupPartner 211=(220:ℤ) from rfl,
    show gridGroupRate 211=((1/200):ℚ) from rfl,
    show gridGroupDerivative 211=((-39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 3=!![2,-1;78,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_212 : GridGroupGeometry 212 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 212=(3:Fin 27) from rfl,
    show gridGroupIndex 212=(381:Fin 780) from rfl,
    show gridGroupPartner 212=(-180:ℤ) from rfl,
    show gridGroupRate 212=((1/200):ℚ) from rfl,
    show gridGroupDerivative 212=((39/10):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 3=!![2,-1;78,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_213 : GridGroupGeometry 213 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 213=(3:Fin 27) from rfl,
    show gridGroupIndex 213=(382:Fin 780) from rfl,
    show gridGroupPartner 213=(-80:ℤ) from rfl,
    show gridGroupRate 213=((1/50):ℚ) from rfl,
    show gridGroupDerivative 213=((39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 3=!![2,-1;78,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_214 : GridGroupGeometry 214 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 214=(3:Fin 27) from rfl,
    show gridGroupIndex 214=(580:Fin 780) from rfl,
    show gridGroupPartner 214=(19:ℤ) from rfl,
    show gridGroupRate 214=(200:ℚ) from rfl,
    show gridGroupDerivative 214=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 3=!![2,-1;78,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_215 : GridGroupGeometry 215 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 215=(15:Fin 27) from rfl,
    show gridGroupIndex 215=(90:Fin 780) from rfl,
    show gridGroupPartner 215=(-64:ℤ) from rfl,
    show gridGroupRate 215=((225/2):ℚ) from rfl,
    show gridGroupDerivative 215=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![2,1;-26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_216 : GridGroupGeometry 216 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 216=(15:Fin 27) from rfl,
    show gridGroupIndex 216=(240:Fin 780) from rfl,
    show gridGroupPartner 216=(-63:ℤ) from rfl,
    show gridGroupRate 216=(200:ℚ) from rfl,
    show gridGroupDerivative 216=(260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![2,1;-26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_217 : GridGroupGeometry 217 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 217=(15:Fin 27) from rfl,
    show gridGroupIndex 217=(540:Fin 780) from rfl,
    show gridGroupPartner 217=(-62:ℤ) from rfl,
    show gridGroupRate 217=(450:ℚ) from rfl,
    show gridGroupDerivative 217=(390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 15=!![2,1;-26,-12] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_218 : GridGroupGeometry 218 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 218=(5:Fin 27) from rfl,
    show gridGroupIndex 218=(30:Fin 780) from rfl,
    show gridGroupPartner 218=(56:ℤ) from rfl,
    show gridGroupRate 218=((225/2):ℚ) from rfl,
    show gridGroupDerivative 218=(195:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![2,1;26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_219 : GridGroupGeometry 219 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 219=(5:Fin 27) from rfl,
    show gridGroupIndex 219=(180:Fin 780) from rfl,
    show gridGroupPartner 219=(57:ℤ) from rfl,
    show gridGroupRate 219=(200:ℚ) from rfl,
    show gridGroupDerivative 219=(260:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![2,1;26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_220 : GridGroupGeometry 220 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 220=(5:Fin 27) from rfl,
    show gridGroupIndex 220=(480:Fin 780) from rfl,
    show gridGroupPartner 220=(58:ℤ) from rfl,
    show gridGroupRate 220=(450:ℚ) from rfl,
    show gridGroupDerivative 220=(390:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 5=!![2,1;26,14] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_221 : GridGroupGeometry 221 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 221=(16:Fin 27) from rfl,
    show gridGroupIndex 221=(660:Fin 780) from rfl,
    show gridGroupPartner 221=(-61:ℤ) from rfl,
    show gridGroupRate 221=(1800:ℚ) from rfl,
    show gridGroupDerivative 221=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 16=!![2,3;-26,-38] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_222 : GridGroupGeometry 222 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 222=(19:Fin 27) from rfl,
    show gridGroupIndex 222=(59:Fin 780) from rfl,
    show gridGroupPartner 222=(2160:ℤ) from rfl,
    show gridGroupRate 222=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 222=((-13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 19=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_223 : GridGroupGeometry 223 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 223=(19:Fin 27) from rfl,
    show gridGroupIndex 223=(61:Fin 780) from rfl,
    show gridGroupPartner 223=(-1440:ℤ) from rfl,
    show gridGroupRate 223=((1/1800):ℚ) from rfl,
    show gridGroupDerivative 223=((13/30):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 19=!![12,-1;26,-2] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_224 : GridGroupGeometry 224 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 224=(26:Fin 27) from rfl,
    show gridGroupIndex 224=(270:Fin 780) from rfl,
    show gridGroupPartner 224=(403:ℤ) from rfl,
    show gridGroupRate 224=((900/13):ℚ) from rfl,
    show gridGroupDerivative 224=(-60:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 26=!![13,-20;26,-39] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_225 : GridGroupGeometry 225 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 225=(25:Fin 27) from rfl,
    show gridGroupIndex 225=(165:Fin 780) from rfl,
    show gridGroupPartner 225=(442:ℤ) from rfl,
    show gridGroupRate 225=((225/52):ℚ) from rfl,
    show gridGroupDerivative 225=(-15:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![13,-7;26,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_226 : GridGroupGeometry 226 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 226=(25:Fin 27) from rfl,
    show gridGroupIndex 226=(273:Fin 780) from rfl,
    show gridGroupPartner 226=(490:ℤ) from rfl,
    show gridGroupRate 226=((117/100):ℚ) from rfl,
    show gridGroupDerivative 226=((-39/5):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![13,-7;26,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_227 : GridGroupGeometry 227 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 227=(25:Fin 27) from rfl,
    show gridGroupIndex 227=(290:Fin 780) from rfl,
    show gridGroupPartner 227=(507:ℤ) from rfl,
    show gridGroupRate 227=((100/117):ℚ) from rfl,
    show gridGroupDerivative 227=((-20/3):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![13,-7;26,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_228 : GridGroupGeometry 228 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 228=(25:Fin 27) from rfl,
    show gridGroupIndex 228=(338:Fin 780) from rfl,
    show gridGroupPartner 228=(615:ℤ) from rfl,
    show gridGroupRate 228=((52/225):ℚ) from rfl,
    show gridGroupDerivative 228=((-52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![13,-7;26,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_229 : GridGroupGeometry 229 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 229=(25:Fin 27) from rfl,
    show gridGroupIndex 229=(377:Fin 780) from rfl,
    show gridGroupPartner 229=(1290:ℤ) from rfl,
    show gridGroupRate 229=((13/900):ℚ) from rfl,
    show gridGroupDerivative 229=((-13/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![13,-7;26,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_230 : GridGroupGeometry 230 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 230=(25:Fin 27) from rfl,
    show gridGroupIndex 230=(386:Fin 780) from rfl,
    show gridGroupPartner 230=(3315:ℤ) from rfl,
    show gridGroupRate 230=((4/2925):ℚ) from rfl,
    show gridGroupDerivative 230=((-4/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![13,-7;26,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_231 : GridGroupGeometry 231 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 231=(25:Fin 27) from rfl,
    show gridGroupIndex 231=(389:Fin 780) from rfl,
    show gridGroupPartner 231=(12090:ℤ) from rfl,
    show gridGroupRate 231=((1/11700):ℚ) from rfl,
    show gridGroupDerivative 231=((-1/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![13,-7;26,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_232 : GridGroupGeometry 232 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 232=(25:Fin 27) from rfl,
    show gridGroupIndex 232=(391:Fin 780) from rfl,
    show gridGroupPartner 232=(-11310:ℤ) from rfl,
    show gridGroupRate 232=((1/11700):ℚ) from rfl,
    show gridGroupDerivative 232=((1/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 25=!![13,-7;26,-13] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_233 : GridGroupGeometry 233 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 233=(20:Fin 27) from rfl,
    show gridGroupIndex 233=(406:Fin 780) from rfl,
    show gridGroupPartner 233=(150:ℤ) from rfl,
    show gridGroupRate 233=((1/225):ℚ) from rfl,
    show gridGroupDerivative 233=((52/15):ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 20=!![25,-13;52,-27] from rfl]
  norm_num [Matrix.det_fin_two]

theorem gridGroup_geometry_234 : GridGroupGeometry 234 := by
  simp only [GridGroupGeometry,
    show gridGroupSource 234=(20:Fin 27) from rfl,
    show gridGroupIndex 234=(630:Fin 780) from rfl,
    show gridGroupPartner 234=(374:ℤ) from rfl,
    show gridGroupRate 234=(225:ℚ) from rfl,
    show gridGroupDerivative 234=(780:ℚ) from rfl,
    sourcePartner,sourceRate,sourceDerivative,
    show sourceRaw 20=!![25,-13;52,-27] from rfl]
  norm_num [Matrix.det_fin_two]

end SmallLevelTwentySixGrid
