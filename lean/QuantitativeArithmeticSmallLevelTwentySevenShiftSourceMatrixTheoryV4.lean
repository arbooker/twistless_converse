module

public import QuantitativeArithmeticSmallLevelTwentySevenMatrixSourceTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenShiftSampleV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenMatrixShiftBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix
open QuantitativeArithmeticRationalRows
open QuantitativeArithmeticSmallLevelTwentySevenObservation (observation)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource
open QuantitativeArithmeticSmallLevelTwentySevenMatrixSource

def obs0 : Fin 553 := ⟨26,by decide⟩
theorem observed0 (v : ℕ → ℂ) : eval v (observation obs0)=v spec0.right := by
  have h : observation obs0=[(1,spec0.right)] := by decide +kernel
  rw [h]
  simp
def obs1 : Fin 553 := ⟨53,by decide⟩
theorem observed1 (v : ℕ → ℂ) : eval v (observation obs1)=v spec1.right := by
  have h : observation obs1=[(1,spec1.right)] := by decide +kernel
  rw [h]
  simp
def obs2 : Fin 553 := ⟨52,by decide⟩
theorem observed2 (v : ℕ → ℂ) : eval v (observation obs2)=v spec2.right := by
  have h : observation obs2=[(1,spec2.right)] := by decide +kernel
  rw [h]
  simp
def obs3 : Fin 553 := ⟨52,by decide⟩
theorem observed3 (v : ℕ → ℂ) : eval v (observation obs3)=v spec3.right := by
  have h : observation obs3=[(1,spec3.right)] := by decide +kernel
  rw [h]
  simp
def obs4 : Fin 553 := ⟨2,by decide⟩
theorem observed4 (v : ℕ → ℂ) : eval v (observation obs4)=v spec4.right := by
  have h : observation obs4=[(1,spec4.right)] := by decide +kernel
  rw [h]
  simp
def obs5 : Fin 553 := ⟨1,by decide⟩
theorem observed5 (v : ℕ → ℂ) : eval v (observation obs5)=v spec5.right := by
  have h : observation obs5=[(1,spec5.right)] := by decide +kernel
  rw [h]
  simp
def obs6 : Fin 553 := ⟨54,by decide⟩
theorem observed6 (v : ℕ → ℂ) : eval v (observation obs6)=v spec6.right := by
  have h : observation obs6=[(1,spec6.right)] := by decide +kernel
  rw [h]
  simp
def obs7 : Fin 553 := ⟨50,by decide⟩
theorem observed7 (v : ℕ → ℂ) : eval v (observation obs7)=v spec7.right := by
  have h : observation obs7=[(1,spec7.right)] := by decide +kernel
  rw [h]
  simp
def obs8 : Fin 553 := ⟨4,by decide⟩
theorem observed8 (v : ℕ → ℂ) : eval v (observation obs8)=v spec8.right := by
  have h : observation obs8=[(1,spec8.right)] := by decide +kernel
  rw [h]
  simp
def obs9 : Fin 553 := ⟨1,by decide⟩
theorem observed9 (v : ℕ → ℂ) : eval v (observation obs9)=v spec9.right := by
  have h : observation obs9=[(1,spec9.right)] := by decide +kernel
  rw [h]
  simp
def obs10 : Fin 553 := ⟨78,by decide⟩
theorem observed10 (v : ℕ → ℂ) : eval v (observation obs10)=v spec10.right := by
  have h : observation obs10=[(1,spec10.right)] := by decide +kernel
  rw [h]
  simp
def obs11 : Fin 553 := ⟨91,by decide⟩
theorem observed11 (v : ℕ → ℂ) : eval v (observation obs11)=v spec11.right := by
  have h : observation obs11=[(1,spec11.right)] := by decide +kernel
  rw [h]
  simp

def obs12 : Fin 553 := ⟨27,by decide⟩
theorem observed12 (v : ℕ → ℂ) : eval v (observation obs12)=v spec12.right := by
  have h : observation obs12=[(1,spec12.right)] := by decide +kernel
  rw [h]
  simp
def obs13 : Fin 553 := ⟨0,by decide⟩
theorem observed13 (v : ℕ → ℂ) : eval v (observation obs13)=v spec13.right := by
  have h : observation obs13=[(1,spec13.right)] := by decide +kernel
  rw [h]
  simp
def obs14 : Fin 553 := ⟨313,by decide⟩
theorem observed14 (v : ℕ → ℂ) : eval v (observation obs14)=v spec14.right := by
  have h : observation obs14=[(1,spec14.right)] := by decide +kernel
  rw [h]
  simp
def obs15 : Fin 553 := ⟨323,by decide⟩
theorem observed15 (v : ℕ → ℂ) : eval v (observation obs15)=v spec15.right := by
  have h : observation obs15=[(1,spec15.right)] := by decide +kernel
  rw [h]
  simp
def obs16 : Fin 553 := ⟨28,by decide⟩
theorem observed16 (v : ℕ → ℂ) : eval v (observation obs16)=v spec16.right := by
  have h : observation obs16=[(1,spec16.right)] := by decide +kernel
  rw [h]
  simp
def obs17 : Fin 553 := ⟨53,by decide⟩
theorem observed17 (v : ℕ → ℂ) : eval v (observation obs17)=v spec17.right := by
  have h : observation obs17=[(1,spec17.right)] := by decide +kernel
  rw [h]
  simp
def obs18 : Fin 553 := ⟨4,by decide⟩
theorem observed18 (v : ℕ → ℂ) : eval v (observation obs18)=v spec18.right := by
  have h : observation obs18=[(1,spec18.right)] := by decide +kernel
  rw [h]
  simp
def obs19 : Fin 553 := ⟨1,by decide⟩
theorem observed19 (v : ℕ → ℂ) : eval v (observation obs19)=v spec19.right := by
  have h : observation obs19=[(1,spec19.right)] := by decide +kernel
  rw [h]
  simp
def obs20 : Fin 553 := ⟨26,by decide⟩
theorem observed20 (v : ℕ → ℂ) : eval v (observation obs20)=v spec20.right := by
  have h : observation obs20=[(1,spec20.right)] := by decide +kernel
  rw [h]
  simp
def obs21 : Fin 553 := ⟨0,by decide⟩
theorem observed21 (v : ℕ → ℂ) : eval v (observation obs21)=v spec21.right := by
  have h : observation obs21=[(1,spec21.right)] := by decide +kernel
  rw [h]
  simp
def obs22 : Fin 553 := ⟨28,by decide⟩
theorem observed22 (v : ℕ → ℂ) : eval v (observation obs22)=v spec22.right := by
  have h : observation obs22=[(1,spec22.right)] := by decide +kernel
  rw [h]
  simp
def obs23 : Fin 553 := ⟨55,by decide⟩
theorem observed23 (v : ℕ → ℂ) : eval v (observation obs23)=v spec23.right := by
  have h : observation obs23=[(1,spec23.right)] := by decide +kernel
  rw [h]
  simp

def obs24 : Fin 553 := ⟨56,by decide⟩
theorem observed24 (v : ℕ → ℂ) : eval v (observation obs24)=v spec24.right := by
  have h : observation obs24=[(1,spec24.right)] := by decide +kernel
  rw [h]
  simp
def obs25 : Fin 553 := ⟨57,by decide⟩
theorem observed25 (v : ℕ → ℂ) : eval v (observation obs25)=v spec25.right := by
  have h : observation obs25=[(1,spec25.right)] := by decide +kernel
  rw [h]
  simp
def obs26 : Fin 553 := ⟨58,by decide⟩
theorem observed26 (v : ℕ → ℂ) : eval v (observation obs26)=v spec26.right := by
  have h : observation obs26=[(1,spec26.right)] := by decide +kernel
  rw [h]
  simp
def obs27 : Fin 553 := ⟨59,by decide⟩
theorem observed27 (v : ℕ → ℂ) : eval v (observation obs27)=v spec27.right := by
  have h : observation obs27=[(1,spec27.right)] := by decide +kernel
  rw [h]
  simp
def obs28 : Fin 553 := ⟨5,by decide⟩
theorem observed28 (v : ℕ → ℂ) : eval v (observation obs28)=v spec28.right := by
  have h : observation obs28=[(1,spec28.right)] := by decide +kernel
  rw [h]
  simp
def obs29 : Fin 553 := ⟨6,by decide⟩
theorem observed29 (v : ℕ → ℂ) : eval v (observation obs29)=v spec29.right := by
  have h : observation obs29=[(1,spec29.right)] := by decide +kernel
  rw [h]
  simp
def obs30 : Fin 553 := ⟨8,by decide⟩
theorem observed30 (v : ℕ → ℂ) : eval v (observation obs30)=v spec30.right := by
  have h : observation obs30=[(1,spec30.right)] := by decide +kernel
  rw [h]
  simp
def obs31 : Fin 553 := ⟨9,by decide⟩
theorem observed31 (v : ℕ → ℂ) : eval v (observation obs31)=v spec31.right := by
  have h : observation obs31=[(1,spec31.right)] := by decide +kernel
  rw [h]
  simp
def obs32 : Fin 553 := ⟨14,by decide⟩
theorem observed32 (v : ℕ → ℂ) : eval v (observation obs32)=v spec32.right := by
  have h : observation obs32=[(1,spec32.right)] := by decide +kernel
  rw [h]
  simp
def obs33 : Fin 553 := ⟨24,by decide⟩
theorem observed33 (v : ℕ → ℂ) : eval v (observation obs33)=v spec33.right := by
  have h : observation obs33=[(1,spec33.right)] := by decide +kernel
  rw [h]
  simp
def obs34 : Fin 553 := ⟨38,by decide⟩
theorem observed34 (v : ℕ → ℂ) : eval v (observation obs34)=v spec34.right := by
  have h : observation obs34=[(1,spec34.right)] := by decide +kernel
  rw [h]
  simp
def obs35 : Fin 553 := ⟨48,by decide⟩
theorem observed35 (v : ℕ → ℂ) : eval v (observation obs35)=v spec35.right := by
  have h : observation obs35=[(1,spec35.right)] := by decide +kernel
  rw [h]
  simp

def obs36 : Fin 553 := ⟨3,by decide⟩
theorem observed36 (v : ℕ → ℂ) : eval v (observation obs36)=v spec36.right := by
  have h : observation obs36=[(1,spec36.right)] := by decide +kernel
  rw [h]
  simp
def obs37 : Fin 553 := ⟨60,by decide⟩
theorem observed37 (v : ℕ → ℂ) : eval v (observation obs37)=v spec37.right := by
  have h : observation obs37=[(1,spec37.right)] := by decide +kernel
  rw [h]
  simp
def obs38 : Fin 553 := ⟨61,by decide⟩
theorem observed38 (v : ℕ → ℂ) : eval v (observation obs38)=v spec38.right := by
  have h : observation obs38=[(1,spec38.right)] := by decide +kernel
  rw [h]
  simp
def obs39 : Fin 553 := ⟨62,by decide⟩
theorem observed39 (v : ℕ → ℂ) : eval v (observation obs39)=v spec39.right := by
  have h : observation obs39=[(1,spec39.right)] := by decide +kernel
  rw [h]
  simp
def obs40 : Fin 553 := ⟨63,by decide⟩
theorem observed40 (v : ℕ → ℂ) : eval v (observation obs40)=v spec40.right := by
  have h : observation obs40=[(1,spec40.right)] := by decide +kernel
  rw [h]
  simp
def obs41 : Fin 553 := ⟨55,by decide⟩
theorem observed41 (v : ℕ → ℂ) : eval v (observation obs41)=v spec41.right := by
  have h : observation obs41=[(1,spec41.right)] := by decide +kernel
  rw [h]
  simp
def obs42 : Fin 553 := ⟨29,by decide⟩
theorem observed42 (v : ℕ → ℂ) : eval v (observation obs42)=v spec42.right := by
  have h : observation obs42=[(1,spec42.right)] := by decide +kernel
  rw [h]
  simp
def obs43 : Fin 553 := ⟨34,by decide⟩
theorem observed43 (v : ℕ → ℂ) : eval v (observation obs43)=v spec43.right := by
  have h : observation obs43=[(1,spec43.right)] := by decide +kernel
  rw [h]
  simp
def obs44 : Fin 553 := ⟨24,by decide⟩
theorem observed44 (v : ℕ → ℂ) : eval v (observation obs44)=v spec44.right := by
  have h : observation obs44=[(1,spec44.right)] := by decide +kernel
  rw [h]
  simp
def obs45 : Fin 553 := ⟨64,by decide⟩
theorem observed45 (v : ℕ → ℂ) : eval v (observation obs45)=v spec45.right := by
  have h : observation obs45=[(1,spec45.right)] := by decide +kernel
  rw [h]
  simp
def obs46 : Fin 553 := ⟨65,by decide⟩
theorem observed46 (v : ℕ → ℂ) : eval v (observation obs46)=v spec46.right := by
  have h : observation obs46=[(1,spec46.right)] := by decide +kernel
  rw [h]
  simp
def obs47 : Fin 553 := ⟨66,by decide⟩
theorem observed47 (v : ℕ → ℂ) : eval v (observation obs47)=v spec47.right := by
  have h : observation obs47=[(1,spec47.right)] := by decide +kernel
  rw [h]
  simp

def obs48 : Fin 553 := ⟨67,by decide⟩
theorem observed48 (v : ℕ → ℂ) : eval v (observation obs48)=v spec48.right := by
  have h : observation obs48=[(1,spec48.right)] := by decide +kernel
  rw [h]
  simp
def obs49 : Fin 553 := ⟨68,by decide⟩
theorem observed49 (v : ℕ → ℂ) : eval v (observation obs49)=v spec49.right := by
  have h : observation obs49=[(1,spec49.right)] := by decide +kernel
  rw [h]
  simp
def obs50 : Fin 553 := ⟨69,by decide⟩
theorem observed50 (v : ℕ → ℂ) : eval v (observation obs50)=v spec50.right := by
  have h : observation obs50=[(1,spec50.right)] := by decide +kernel
  rw [h]
  simp
def obs51 : Fin 553 := ⟨29,by decide⟩
theorem observed51 (v : ℕ → ℂ) : eval v (observation obs51)=v spec51.right := by
  have h : observation obs51=[(1,spec51.right)] := by decide +kernel
  rw [h]
  simp
def obs52 : Fin 553 := ⟨30,by decide⟩
theorem observed52 (v : ℕ → ℂ) : eval v (observation obs52)=v spec52.right := by
  have h : observation obs52=[(1,spec52.right)] := by decide +kernel
  rw [h]
  simp
def obs53 : Fin 553 := ⟨32,by decide⟩
theorem observed53 (v : ℕ → ℂ) : eval v (observation obs53)=v spec53.right := by
  have h : observation obs53=[(1,spec53.right)] := by decide +kernel
  rw [h]
  simp
def obs54 : Fin 553 := ⟨33,by decide⟩
theorem observed54 (v : ℕ → ℂ) : eval v (observation obs54)=v spec54.right := by
  have h : observation obs54=[(1,spec54.right)] := by decide +kernel
  rw [h]
  simp
def obs55 : Fin 553 := ⟨38,by decide⟩
theorem observed55 (v : ℕ → ℂ) : eval v (observation obs55)=v spec55.right := by
  have h : observation obs55=[(1,spec55.right)] := by decide +kernel
  rw [h]
  simp
def obs56 : Fin 553 := ⟨48,by decide⟩
theorem observed56 (v : ℕ → ℂ) : eval v (observation obs56)=v spec56.right := by
  have h : observation obs56=[(1,spec56.right)] := by decide +kernel
  rw [h]
  simp
def obs57 : Fin 553 := ⟨8,by decide⟩
theorem observed57 (v : ℕ → ℂ) : eval v (observation obs57)=v spec57.right := by
  have h : observation obs57=[(1,spec57.right)] := by decide +kernel
  rw [h]
  simp
def obs58 : Fin 553 := ⟨18,by decide⟩
theorem observed58 (v : ℕ → ℂ) : eval v (observation obs58)=v spec58.right := by
  have h : observation obs58=[(1,spec58.right)] := by decide +kernel
  rw [h]
  simp
def obs59 : Fin 553 := ⟨23,by decide⟩
theorem observed59 (v : ℕ → ℂ) : eval v (observation obs59)=v spec59.right := by
  have h : observation obs59=[(1,spec59.right)] := by decide +kernel
  rw [h]
  simp

def obs60 : Fin 553 := ⟨32,by decide⟩
theorem observed60 (v : ℕ → ℂ) : eval v (observation obs60)=v spec60.right := by
  have h : observation obs60=[(1,spec60.right)] := by decide +kernel
  rw [h]
  simp
def obs61 : Fin 553 := ⟨42,by decide⟩
theorem observed61 (v : ℕ → ℂ) : eval v (observation obs61)=v spec61.right := by
  have h : observation obs61=[(1,spec61.right)] := by decide +kernel
  rw [h]
  simp
def obs62 : Fin 553 := ⟨47,by decide⟩
theorem observed62 (v : ℕ → ℂ) : eval v (observation obs62)=v spec62.right := by
  have h : observation obs62=[(1,spec62.right)] := by decide +kernel
  rw [h]
  simp
def obs63 : Fin 553 := ⟨70,by decide⟩
theorem observed63 (v : ℕ → ℂ) : eval v (observation obs63)=v spec63.right := by
  have h : observation obs63=[(1,spec63.right)] := by decide +kernel
  rw [h]
  simp
def obs64 : Fin 553 := ⟨71,by decide⟩
theorem observed64 (v : ℕ → ℂ) : eval v (observation obs64)=v spec64.right := by
  have h : observation obs64=[(1,spec64.right)] := by decide +kernel
  rw [h]
  simp
def obs65 : Fin 553 := ⟨72,by decide⟩
theorem observed65 (v : ℕ → ℂ) : eval v (observation obs65)=v spec65.right := by
  have h : observation obs65=[(1,spec65.right)] := by decide +kernel
  rw [h]
  simp
def obs66 : Fin 553 := ⟨36,by decide⟩
theorem observed66 (v : ℕ → ℂ) : eval v (observation obs66)=v spec66.right := by
  have h : observation obs66=[(1,spec66.right)] := by decide +kernel
  rw [h]
  simp
def obs67 : Fin 553 := ⟨77,by decide⟩
theorem observed67 (v : ℕ → ℂ) : eval v (observation obs67)=v spec67.right := by
  have h : observation obs67=[(1,spec67.right)] := by decide +kernel
  rw [h]
  simp
def obs68 : Fin 553 := ⟨8,by decide⟩
theorem observed68 (v : ℕ → ℂ) : eval v (observation obs68)=v spec68.right := by
  have h : observation obs68=[(1,spec68.right)] := by decide +kernel
  rw [h]
  simp
def obs69 : Fin 553 := ⟨6,by decide⟩
theorem observed69 (v : ℕ → ℂ) : eval v (observation obs69)=v spec69.right := by
  have h : observation obs69=[(1,spec69.right)] := by decide +kernel
  rw [h]
  simp
def obs70 : Fin 553 := ⟨90,by decide⟩
theorem observed70 (v : ℕ → ℂ) : eval v (observation obs70)=v spec70.right := by
  have h : observation obs70=[(1,spec70.right)] := by decide +kernel
  rw [h]
  simp
def obs71 : Fin 553 := ⟨312,by decide⟩
theorem observed71 (v : ℕ → ℂ) : eval v (observation obs71)=v spec71.right := by
  have h : observation obs71=[(1,spec71.right)] := by decide +kernel
  rw [h]
  simp

def obs72 : Fin 553 := ⟨314,by decide⟩
theorem observed72 (v : ℕ → ℂ) : eval v (observation obs72)=v spec72.right := by
  have h : observation obs72=[(1,spec72.right)] := by decide +kernel
  rw [h]
  simp
def obs73 : Fin 553 := ⟨315,by decide⟩
theorem observed73 (v : ℕ → ℂ) : eval v (observation obs73)=v spec73.right := by
  have h : observation obs73=[(1,spec73.right)] := by decide +kernel
  rw [h]
  simp
def obs74 : Fin 553 := ⟨316,by decide⟩
theorem observed74 (v : ℕ → ℂ) : eval v (observation obs74)=v spec74.right := by
  have h : observation obs74=[(1,spec74.right)] := by decide +kernel
  rw [h]
  simp
def obs75 : Fin 553 := ⟨317,by decide⟩
theorem observed75 (v : ℕ → ℂ) : eval v (observation obs75)=v spec75.right := by
  have h : observation obs75=[(1,spec75.right)] := by decide +kernel
  rw [h]
  simp
def obs76 : Fin 553 := ⟨318,by decide⟩
theorem observed76 (v : ℕ → ℂ) : eval v (observation obs76)=v spec76.right := by
  have h : observation obs76=[(1,spec76.right)] := by decide +kernel
  rw [h]
  simp
def obs77 : Fin 553 := ⟨11,by decide⟩
theorem observed77 (v : ℕ → ℂ) : eval v (observation obs77)=v spec77.right := by
  have h : observation obs77=[(1,spec77.right)] := by decide +kernel
  rw [h]
  simp
def obs78 : Fin 553 := ⟨18,by decide⟩
theorem observed78 (v : ℕ → ℂ) : eval v (observation obs78)=v spec78.right := by
  have h : observation obs78=[(1,spec78.right)] := by decide +kernel
  rw [h]
  simp
def obs79 : Fin 553 := ⟨32,by decide⟩
theorem observed79 (v : ℕ → ℂ) : eval v (observation obs79)=v spec79.right := by
  have h : observation obs79=[(1,spec79.right)] := by decide +kernel
  rw [h]
  simp
def obs80 : Fin 553 := ⟨30,by decide⟩
theorem observed80 (v : ℕ → ℂ) : eval v (observation obs80)=v spec80.right := by
  have h : observation obs80=[(1,spec80.right)] := by decide +kernel
  rw [h]
  simp
def obs81 : Fin 553 := ⟨44,by decide⟩
theorem observed81 (v : ℕ → ℂ) : eval v (observation obs81)=v spec81.right := by
  have h : observation obs81=[(1,spec81.right)] := by decide +kernel
  rw [h]
  simp
def obs82 : Fin 553 := ⟨51,by decide⟩
theorem observed82 (v : ℕ → ℂ) : eval v (observation obs82)=v spec82.right := by
  have h : observation obs82=[(1,spec82.right)] := by decide +kernel
  rw [h]
  simp
def obs83 : Fin 553 := ⟨319,by decide⟩
theorem observed83 (v : ℕ → ℂ) : eval v (observation obs83)=v spec83.right := by
  have h : observation obs83=[(1,spec83.right)] := by decide +kernel
  rw [h]
  simp

def obs84 : Fin 553 := ⟨320,by decide⟩
theorem observed84 (v : ℕ → ℂ) : eval v (observation obs84)=v spec84.right := by
  have h : observation obs84=[(1,spec84.right)] := by decide +kernel
  rw [h]
  simp
def obs85 : Fin 553 := ⟨32,by decide⟩
theorem observed85 (v : ℕ → ℂ) : eval v (observation obs85)=v spec85.right := by
  have h : observation obs85=[(1,spec85.right)] := by decide +kernel
  rw [h]
  simp
def obs86 : Fin 553 := ⟨18,by decide⟩
theorem observed86 (v : ℕ → ℂ) : eval v (observation obs86)=v spec86.right := by
  have h : observation obs86=[(1,spec86.right)] := by decide +kernel
  rw [h]
  simp
def obs87 : Fin 553 := ⟨25,by decide⟩
theorem observed87 (v : ℕ → ℂ) : eval v (observation obs87)=v spec87.right := by
  have h : observation obs87=[(1,spec87.right)] := by decide +kernel
  rw [h]
  simp
def obs88 : Fin 553 := ⟨321,by decide⟩
theorem observed88 (v : ℕ → ℂ) : eval v (observation obs88)=v spec88.right := by
  have h : observation obs88=[(1,spec88.right)] := by decide +kernel
  rw [h]
  simp
def obs89 : Fin 553 := ⟨322,by decide⟩
theorem observed89 (v : ℕ → ℂ) : eval v (observation obs89)=v spec89.right := by
  have h : observation obs89=[(1,spec89.right)] := by decide +kernel
  rw [h]
  simp
def obs90 : Fin 553 := ⟨324,by decide⟩
theorem observed90 (v : ℕ → ℂ) : eval v (observation obs90)=v spec90.right := by
  have h : observation obs90=[(1,spec90.right)] := by decide +kernel
  rw [h]
  simp
def obs91 : Fin 553 := ⟨325,by decide⟩
theorem observed91 (v : ℕ → ℂ) : eval v (observation obs91)=v spec91.right := by
  have h : observation obs91=[(1,spec91.right)] := by decide +kernel
  rw [h]
  simp
def obs92 : Fin 553 := ⟨326,by decide⟩
theorem observed92 (v : ℕ → ℂ) : eval v (observation obs92)=v spec92.right := by
  have h : observation obs92=[(1,spec92.right)] := by decide +kernel
  rw [h]
  simp
def obs93 : Fin 553 := ⟨35,by decide⟩
theorem observed93 (v : ℕ → ℂ) : eval v (observation obs93)=v spec93.right := by
  have h : observation obs93=[(1,spec93.right)] := by decide +kernel
  rw [h]
  simp
def obs94 : Fin 553 := ⟨42,by decide⟩
theorem observed94 (v : ℕ → ℂ) : eval v (observation obs94)=v spec94.right := by
  have h : observation obs94=[(1,spec94.right)] := by decide +kernel
  rw [h]
  simp
def obs95 : Fin 553 := ⟨14,by decide⟩
theorem observed95 (v : ℕ → ℂ) : eval v (observation obs95)=v spec95.right := by
  have h : observation obs95=[(1,spec95.right)] := by decide +kernel
  rw [h]
  simp

def obs96 : Fin 553 := ⟨21,by decide⟩
theorem observed96 (v : ℕ → ℂ) : eval v (observation obs96)=v spec96.right := by
  have h : observation obs96=[(1,spec96.right)] := by decide +kernel
  rw [h]
  simp
def obs97 : Fin 553 := ⟨316,by decide⟩
theorem observed97 (v : ℕ → ℂ) : eval v (observation obs97)=v spec97.right := by
  have h : observation obs97=[(1,spec97.right)] := by decide +kernel
  rw [h]
  simp
def obs98 : Fin 553 := ⟨38,by decide⟩
theorem observed98 (v : ℕ → ℂ) : eval v (observation obs98)=v spec98.right := by
  have h : observation obs98=[(1,spec98.right)] := by decide +kernel
  rw [h]
  simp
def obs99 : Fin 553 := ⟨45,by decide⟩
theorem observed99 (v : ℕ → ℂ) : eval v (observation obs99)=v spec99.right := by
  have h : observation obs99=[(1,spec99.right)] := by decide +kernel
  rw [h]
  simp
def obs100 : Fin 553 := ⟨328,by decide⟩
theorem observed100 (v : ℕ → ℂ) : eval v (observation obs100)=v spec100.right := by
  have h : observation obs100=[(1,spec100.right)] := by decide +kernel
  rw [h]
  simp
def obs101 : Fin 553 := ⟨329,by decide⟩
theorem observed101 (v : ℕ → ℂ) : eval v (observation obs101)=v spec101.right := by
  have h : observation obs101=[(1,spec101.right)] := by decide +kernel
  rw [h]
  simp
def obs102 : Fin 553 := ⟨6,by decide⟩
theorem observed102 (v : ℕ → ℂ) : eval v (observation obs102)=v spec102.right := by
  have h : observation obs102=[(1,spec102.right)] := by decide +kernel
  rw [h]
  simp
def obs103 : Fin 553 := ⟨46,by decide⟩
theorem observed103 (v : ℕ → ℂ) : eval v (observation obs103)=v spec103.right := by
  have h : observation obs103=[(1,spec103.right)] := by decide +kernel
  rw [h]
  simp
def obs104 : Fin 553 := ⟨42,by decide⟩
theorem observed104 (v : ℕ → ℂ) : eval v (observation obs104)=v spec104.right := by
  have h : observation obs104=[(1,spec104.right)] := by decide +kernel
  rw [h]
  simp
def obs105 : Fin 553 := ⟨46,by decide⟩
theorem observed105 (v : ℕ → ℂ) : eval v (observation obs105)=v spec105.right := by
  have h : observation obs105=[(1,spec105.right)] := by decide +kernel
  rw [h]
  simp
def obs106 : Fin 553 := ⟨335,by decide⟩
theorem observed106 (v : ℕ → ℂ) : eval v (observation obs106)=v spec106.right := by
  have h : observation obs106=[(1,spec106.right)] := by decide +kernel
  rw [h]
  simp
def obs107 : Fin 553 := ⟨44,by decide⟩
theorem observed107 (v : ℕ → ℂ) : eval v (observation obs107)=v spec107.right := by
  have h : observation obs107=[(1,spec107.right)] := by decide +kernel
  rw [h]
  simp

def obs108 : Fin 553 := ⟨336,by decide⟩
theorem observed108 (v : ℕ → ℂ) : eval v (observation obs108)=v spec108.right := by
  have h : observation obs108=[(1,spec108.right)] := by decide +kernel
  rw [h]
  simp
def obs109 : Fin 553 := ⟨337,by decide⟩
theorem observed109 (v : ℕ → ℂ) : eval v (observation obs109)=v spec109.right := by
  have h : observation obs109=[(1,spec109.right)] := by decide +kernel
  rw [h]
  simp
def obs110 : Fin 553 := ⟨8,by decide⟩
theorem observed110 (v : ℕ → ℂ) : eval v (observation obs110)=v spec110.right := by
  have h : observation obs110=[(1,spec110.right)] := by decide +kernel
  rw [h]
  simp
def obs111 : Fin 553 := ⟨23,by decide⟩
theorem observed111 (v : ℕ → ℂ) : eval v (observation obs111)=v spec111.right := by
  have h : observation obs111=[(1,spec111.right)] := by decide +kernel
  rw [h]
  simp
def obs112 : Fin 553 := ⟨357,by decide⟩
theorem observed112 (v : ℕ → ℂ) : eval v (observation obs112)=v spec112.right := by
  have h : observation obs112=[(1,spec112.right)] := by decide +kernel
  rw [h]
  simp
def obs113 : Fin 553 := ⟨14,by decide⟩
theorem observed113 (v : ℕ → ℂ) : eval v (observation obs113)=v spec113.right := by
  have h : observation obs113=[(1,spec113.right)] := by decide +kernel
  rw [h]
  simp
def obs114 : Fin 553 := ⟨34,by decide⟩
theorem observed114 (v : ℕ → ℂ) : eval v (observation obs114)=v spec114.right := by
  have h : observation obs114=[(1,spec114.right)] := by decide +kernel
  rw [h]
  simp
def obs115 : Fin 553 := ⟨30,by decide⟩
theorem observed115 (v : ℕ → ℂ) : eval v (observation obs115)=v spec115.right := by
  have h : observation obs115=[(1,spec115.right)] := by decide +kernel
  rw [h]
  simp
def obs116 : Fin 553 := ⟨544,by decide⟩
theorem observed116 (v : ℕ → ℂ) : eval v (observation obs116)=v spec116.right := by
  have h : observation obs116=[(1,spec116.right)] := by decide +kernel
  rw [h]
  simp
def obs117 : Fin 553 := ⟨59,by decide⟩
theorem observed117 (v : ℕ → ℂ) : eval v (observation obs117)=v spec117.right := by
  have h : observation obs117=[(1,spec117.right)] := by decide +kernel
  rw [h]
  simp
def obs118 : Fin 553 := ⟨7,by decide⟩
theorem observed118 (v : ℕ → ℂ) : eval v (observation obs118)=v spec118.right := by
  have h : observation obs118=[(1,spec118.right)] := by decide +kernel
  rw [h]
  simp

end QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenMatrixShiftsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix
open QuantitativeArithmeticRationalRows
open QuantitativeArithmeticSmallLevelTwentySevenObservation (observation)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource
def selected (i : Fin 119) : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec :=
  QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.selected ⟨i.val,by rw [QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.specs_length]; exact i.isLt⟩
def obs : Fin 119 → Fin 553
  | 0 => obs0
  | 1 => obs1
  | 2 => obs2
  | 3 => obs3
  | 4 => obs4
  | 5 => obs5
  | 6 => obs6
  | 7 => obs7
  | 8 => obs8
  | 9 => obs9
  | 10 => obs10
  | 11 => obs11
  | 12 => obs12
  | 13 => obs13
  | 14 => obs14
  | 15 => obs15
  | 16 => obs16
  | 17 => obs17
  | 18 => obs18
  | 19 => obs19
  | 20 => obs20
  | 21 => obs21
  | 22 => obs22
  | 23 => obs23
  | 24 => obs24
  | 25 => obs25
  | 26 => obs26
  | 27 => obs27
  | 28 => obs28
  | 29 => obs29
  | 30 => obs30
  | 31 => obs31
  | 32 => obs32
  | 33 => obs33
  | 34 => obs34
  | 35 => obs35
  | 36 => obs36
  | 37 => obs37
  | 38 => obs38
  | 39 => obs39
  | 40 => obs40
  | 41 => obs41
  | 42 => obs42
  | 43 => obs43
  | 44 => obs44
  | 45 => obs45
  | 46 => obs46
  | 47 => obs47
  | 48 => obs48
  | 49 => obs49
  | 50 => obs50
  | 51 => obs51
  | 52 => obs52
  | 53 => obs53
  | 54 => obs54
  | 55 => obs55
  | 56 => obs56
  | 57 => obs57
  | 58 => obs58
  | 59 => obs59
  | 60 => obs60
  | 61 => obs61
  | 62 => obs62
  | 63 => obs63
  | 64 => obs64
  | 65 => obs65
  | 66 => obs66
  | 67 => obs67
  | 68 => obs68
  | 69 => obs69
  | 70 => obs70
  | 71 => obs71
  | 72 => obs72
  | 73 => obs73
  | 74 => obs74
  | 75 => obs75
  | 76 => obs76
  | 77 => obs77
  | 78 => obs78
  | 79 => obs79
  | 80 => obs80
  | 81 => obs81
  | 82 => obs82
  | 83 => obs83
  | 84 => obs84
  | 85 => obs85
  | 86 => obs86
  | 87 => obs87
  | 88 => obs88
  | 89 => obs89
  | 90 => obs90
  | 91 => obs91
  | 92 => obs92
  | 93 => obs93
  | 94 => obs94
  | 95 => obs95
  | 96 => obs96
  | 97 => obs97
  | 98 => obs98
  | 99 => obs99
  | 100 => obs100
  | 101 => obs101
  | 102 => obs102
  | 103 => obs103
  | 104 => obs104
  | 105 => obs105
  | 106 => obs106
  | 107 => obs107
  | 108 => obs108
  | 109 => obs109
  | 110 => obs110
  | 111 => obs111
  | 112 => obs112
  | 113 => obs113
  | 114 => obs114
  | 115 => obs115
  | 116 => obs116
  | 117 => obs117
  | _ => obs118
theorem all_observed (v : ℕ → ℂ) (i : Fin 119) :
    eval v (observation (obs i))=v (selected i).right := by
  fin_cases i
  · exact observed0 v
  · exact observed1 v
  · exact observed2 v
  · exact observed3 v
  · exact observed4 v
  · exact observed5 v
  · exact observed6 v
  · exact observed7 v
  · exact observed8 v
  · exact observed9 v
  · exact observed10 v
  · exact observed11 v
  · exact observed12 v
  · exact observed13 v
  · exact observed14 v
  · exact observed15 v
  · exact observed16 v
  · exact observed17 v
  · exact observed18 v
  · exact observed19 v
  · exact observed20 v
  · exact observed21 v
  · exact observed22 v
  · exact observed23 v
  · exact observed24 v
  · exact observed25 v
  · exact observed26 v
  · exact observed27 v
  · exact observed28 v
  · exact observed29 v
  · exact observed30 v
  · exact observed31 v
  · exact observed32 v
  · exact observed33 v
  · exact observed34 v
  · exact observed35 v
  · exact observed36 v
  · exact observed37 v
  · exact observed38 v
  · exact observed39 v
  · exact observed40 v
  · exact observed41 v
  · exact observed42 v
  · exact observed43 v
  · exact observed44 v
  · exact observed45 v
  · exact observed46 v
  · exact observed47 v
  · exact observed48 v
  · exact observed49 v
  · exact observed50 v
  · exact observed51 v
  · exact observed52 v
  · exact observed53 v
  · exact observed54 v
  · exact observed55 v
  · exact observed56 v
  · exact observed57 v
  · exact observed58 v
  · exact observed59 v
  · exact observed60 v
  · exact observed61 v
  · exact observed62 v
  · exact observed63 v
  · exact observed64 v
  · exact observed65 v
  · exact observed66 v
  · exact observed67 v
  · exact observed68 v
  · exact observed69 v
  · exact observed70 v
  · exact observed71 v
  · exact observed72 v
  · exact observed73 v
  · exact observed74 v
  · exact observed75 v
  · exact observed76 v
  · exact observed77 v
  · exact observed78 v
  · exact observed79 v
  · exact observed80 v
  · exact observed81 v
  · exact observed82 v
  · exact observed83 v
  · exact observed84 v
  · exact observed85 v
  · exact observed86 v
  · exact observed87 v
  · exact observed88 v
  · exact observed89 v
  · exact observed90 v
  · exact observed91 v
  · exact observed92 v
  · exact observed93 v
  · exact observed94 v
  · exact observed95 v
  · exact observed96 v
  · exact observed97 v
  · exact observed98 v
  · exact observed99 v
  · exact observed100 v
  · exact observed101 v
  · exact observed102 v
  · exact observed103 v
  · exact observed104 v
  · exact observed105 v
  · exact observed106 v
  · exact observed107 v
  · exact observed108 v
  · exact observed109 v
  · exact observed110 v
  · exact observed111 v
  · exact observed112 v
  · exact observed113 v
  · exact observed114 v
  · exact observed115 v
  · exact observed116 v
  · exact observed117 v
  · exact observed118 v
#print axioms all_observed
end QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix
end
end
