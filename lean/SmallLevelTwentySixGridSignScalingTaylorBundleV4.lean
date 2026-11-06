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

theorem taylor_scale_sign_0 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 0 then -c else 1)*(-1))*u^(taylorPowers 0).1*v^(taylorPowers 0).2.2.1=
      ((if 2∣gridTaylorQ 0 then u else 1)*(if 13∣gridTaylorQ 0 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 0=3 from rfl,show taylorPowers 0=(-1, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_1 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 1 then -c else 1)*(-1))*u^(taylorPowers 1).1*v^(taylorPowers 1).2.2.1=
      ((if 2∣gridTaylorQ 1 then u else 1)*(if 13∣gridTaylorQ 1 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 1=3 from rfl,show taylorPowers 1=(-3, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_2 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 2 then -c else 1)*(-1))*u^(taylorPowers 2).1*v^(taylorPowers 2).2.2.1=
      ((if 2∣gridTaylorQ 2 then u else 1)*(if 13∣gridTaylorQ 2 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 2=3 from rfl,show taylorPowers 2=(-1, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_3 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 3 then -c else 1)*(-1))*u^(taylorPowers 3).1*v^(taylorPowers 3).2.2.1=
      ((if 2∣gridTaylorQ 3 then u else 1)*(if 13∣gridTaylorQ 3 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 3=3 from rfl,show taylorPowers 3=(3, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_4 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 4 then -c else 1)*(-1))*u^(taylorPowers 4).1*v^(taylorPowers 4).2.2.1=
      ((if 2∣gridTaylorQ 4 then u else 1)*(if 13∣gridTaylorQ 4 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 4=3 from rfl,show taylorPowers 4=(-1, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_5 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 5 then -c else 1)*(-1))*u^(taylorPowers 5).1*v^(taylorPowers 5).2.2.1=
      ((if 2∣gridTaylorQ 5 then u else 1)*(if 13∣gridTaylorQ 5 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 5=3 from rfl,show taylorPowers 5=(-3, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_6 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 6 then -c else 1)*(-1))*u^(taylorPowers 6).1*v^(taylorPowers 6).2.2.1=
      ((if 2∣gridTaylorQ 6 then u else 1)*(if 13∣gridTaylorQ 6 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 6=3 from rfl,show taylorPowers 6=(1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_7 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 7 then -c else 1)*(-1))*u^(taylorPowers 7).1*v^(taylorPowers 7).2.2.1=
      ((if 2∣gridTaylorQ 7 then u else 1)*(if 13∣gridTaylorQ 7 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 7=3 from rfl,show taylorPowers 7=(-3, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_8 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 8 then -c else 1)*(-1))*u^(taylorPowers 8).1*v^(taylorPowers 8).2.2.1=
      ((if 2∣gridTaylorQ 8 then u else 1)*(if 13∣gridTaylorQ 8 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 8=3 from rfl,show taylorPowers 8=(-1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_9 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 9 then -c else 1)*(-1))*u^(taylorPowers 9).1*v^(taylorPowers 9).2.2.1=
      ((if 2∣gridTaylorQ 9 then u else 1)*(if 13∣gridTaylorQ 9 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 9=3 from rfl,show taylorPowers 9=(-1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_10 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 10 then -c else 1)*(-1))*u^(taylorPowers 10).1*v^(taylorPowers 10).2.2.1=
      ((if 2∣gridTaylorQ 10 then u else 1)*(if 13∣gridTaylorQ 10 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 10=3 from rfl,show taylorPowers 10=(-3, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_11 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 11 then -c else 1)*(-1))*u^(taylorPowers 11).1*v^(taylorPowers 11).2.2.1=
      ((if 2∣gridTaylorQ 11 then u else 1)*(if 13∣gridTaylorQ 11 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 11=3 from rfl,show taylorPowers 11=(1, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_12 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 12 then -c else 1)*(-1))*u^(taylorPowers 12).1*v^(taylorPowers 12).2.2.1=
      ((if 2∣gridTaylorQ 12 then u else 1)*(if 13∣gridTaylorQ 12 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 12=3 from rfl,show taylorPowers 12=(-3, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_13 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 13 then -c else 1)*(-1))*u^(taylorPowers 13).1*v^(taylorPowers 13).2.2.1=
      ((if 2∣gridTaylorQ 13 then u else 1)*(if 13∣gridTaylorQ 13 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 13=3 from rfl,show taylorPowers 13=(-1, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_14 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 14 then -c else 1)*(-1))*u^(taylorPowers 14).1*v^(taylorPowers 14).2.2.1=
      ((if 2∣gridTaylorQ 14 then u else 1)*(if 13∣gridTaylorQ 14 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 14=3 from rfl,show taylorPowers 14=(3, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_15 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 15 then -c else 1)*(-1))*u^(taylorPowers 15).1*v^(taylorPowers 15).2.2.1=
      ((if 2∣gridTaylorQ 15 then u else 1)*(if 13∣gridTaylorQ 15 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 15=3 from rfl,show taylorPowers 15=(-1, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_16 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 16 then -c else 1)*(-1))*u^(taylorPowers 16).1*v^(taylorPowers 16).2.2.1=
      ((if 2∣gridTaylorQ 16 then u else 1)*(if 13∣gridTaylorQ 16 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 16=3 from rfl,show taylorPowers 16=(-3, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_17 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 17 then -c else 1)*(-1))*u^(taylorPowers 17).1*v^(taylorPowers 17).2.2.1=
      ((if 2∣gridTaylorQ 17 then u else 1)*(if 13∣gridTaylorQ 17 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 17=3 from rfl,show taylorPowers 17=(-1, 0, 1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_18 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 18 then -c else 1)*(-1))*u^(taylorPowers 18).1*v^(taylorPowers 18).2.2.1=
      ((if 2∣gridTaylorQ 18 then u else 1)*(if 13∣gridTaylorQ 18 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 18=4 from rfl,show taylorPowers 18=(0, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_19 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 19 then -c else 1)*(-1))*u^(taylorPowers 19).1*v^(taylorPowers 19).2.2.1=
      ((if 2∣gridTaylorQ 19 then u else 1)*(if 13∣gridTaylorQ 19 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 19=4 from rfl,show taylorPowers 19=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_20 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 20 then -c else 1)*(-1))*u^(taylorPowers 20).1*v^(taylorPowers 20).2.2.1=
      ((if 2∣gridTaylorQ 20 then u else 1)*(if 13∣gridTaylorQ 20 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 20=4 from rfl,show taylorPowers 20=(0, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_21 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 21 then -c else 1)*(-1))*u^(taylorPowers 21).1*v^(taylorPowers 21).2.2.1=
      ((if 2∣gridTaylorQ 21 then u else 1)*(if 13∣gridTaylorQ 21 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 21=4 from rfl,show taylorPowers 21=(0, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_22 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 22 then -c else 1)*(-1))*u^(taylorPowers 22).1*v^(taylorPowers 22).2.2.1=
      ((if 2∣gridTaylorQ 22 then u else 1)*(if 13∣gridTaylorQ 22 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 22=4 from rfl,show taylorPowers 22=(0, -2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_23 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 23 then -c else 1)*(-1))*u^(taylorPowers 23).1*v^(taylorPowers 23).2.2.1=
      ((if 2∣gridTaylorQ 23 then u else 1)*(if 13∣gridTaylorQ 23 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 23=4 from rfl,show taylorPowers 23=(0, -2, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_24 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 24 then -c else 1)*(-1))*u^(taylorPowers 24).1*v^(taylorPowers 24).2.2.1=
      ((if 2∣gridTaylorQ 24 then u else 1)*(if 13∣gridTaylorQ 24 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 24=4 from rfl,show taylorPowers 24=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_25 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 25 then -c else 1)*(-1))*u^(taylorPowers 25).1*v^(taylorPowers 25).2.2.1=
      ((if 2∣gridTaylorQ 25 then u else 1)*(if 13∣gridTaylorQ 25 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 25=4 from rfl,show taylorPowers 25=(0, -2, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_26 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 26 then -c else 1)*(-1))*u^(taylorPowers 26).1*v^(taylorPowers 26).2.2.1=
      ((if 2∣gridTaylorQ 26 then u else 1)*(if 13∣gridTaylorQ 26 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 26=4 from rfl,show taylorPowers 26=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_27 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 27 then -c else 1)*(-1))*u^(taylorPowers 27).1*v^(taylorPowers 27).2.2.1=
      ((if 2∣gridTaylorQ 27 then u else 1)*(if 13∣gridTaylorQ 27 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 27=4 from rfl,show taylorPowers 27=(0, 2, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_28 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 28 then -c else 1)*(-1))*u^(taylorPowers 28).1*v^(taylorPowers 28).2.2.1=
      ((if 2∣gridTaylorQ 28 then u else 1)*(if 13∣gridTaylorQ 28 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 28=6 from rfl,show taylorPowers 28=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_29 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 29 then -c else 1)*(-1))*u^(taylorPowers 29).1*v^(taylorPowers 29).2.2.1=
      ((if 2∣gridTaylorQ 29 then u else 1)*(if 13∣gridTaylorQ 29 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 29=6 from rfl,show taylorPowers 29=(-2, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_30 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 30 then -c else 1)*(-1))*u^(taylorPowers 30).1*v^(taylorPowers 30).2.2.1=
      ((if 2∣gridTaylorQ 30 then u else 1)*(if 13∣gridTaylorQ 30 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 30=6 from rfl,show taylorPowers 30=(2, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_31 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 31 then -c else 1)*(-1))*u^(taylorPowers 31).1*v^(taylorPowers 31).2.2.1=
      ((if 2∣gridTaylorQ 31 then u else 1)*(if 13∣gridTaylorQ 31 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 31=6 from rfl,show taylorPowers 31=(-2, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_32 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 32 then -c else 1)*(-1))*u^(taylorPowers 32).1*v^(taylorPowers 32).2.2.1=
      ((if 2∣gridTaylorQ 32 then u else 1)*(if 13∣gridTaylorQ 32 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 32=6 from rfl,show taylorPowers 32=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_33 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 33 then -c else 1)*(-1))*u^(taylorPowers 33).1*v^(taylorPowers 33).2.2.1=
      ((if 2∣gridTaylorQ 33 then u else 1)*(if 13∣gridTaylorQ 33 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 33=6 from rfl,show taylorPowers 33=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_34 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 34 then -c else 1)*(-1))*u^(taylorPowers 34).1*v^(taylorPowers 34).2.2.1=
      ((if 2∣gridTaylorQ 34 then u else 1)*(if 13∣gridTaylorQ 34 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 34=6 from rfl,show taylorPowers 34=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_35 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 35 then -c else 1)*(-1))*u^(taylorPowers 35).1*v^(taylorPowers 35).2.2.1=
      ((if 2∣gridTaylorQ 35 then u else 1)*(if 13∣gridTaylorQ 35 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 35=6 from rfl,show taylorPowers 35=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_36 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 36 then -c else 1)*(-1))*u^(taylorPowers 36).1*v^(taylorPowers 36).2.2.1=
      ((if 2∣gridTaylorQ 36 then u else 1)*(if 13∣gridTaylorQ 36 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 36=6 from rfl,show taylorPowers 36=(-2, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_37 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 37 then -c else 1)*(-1))*u^(taylorPowers 37).1*v^(taylorPowers 37).2.2.1=
      ((if 2∣gridTaylorQ 37 then u else 1)*(if 13∣gridTaylorQ 37 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 37=6 from rfl,show taylorPowers 37=(2, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_38 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 38 then -c else 1)*(-1))*u^(taylorPowers 38).1*v^(taylorPowers 38).2.2.1=
      ((if 2∣gridTaylorQ 38 then u else 1)*(if 13∣gridTaylorQ 38 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 38=6 from rfl,show taylorPowers 38=(-2, 0, -1, 2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_39 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 39 then -c else 1)*(-1))*u^(taylorPowers 39).1*v^(taylorPowers 39).2.2.1=
      ((if 2∣gridTaylorQ 39 then u else 1)*(if 13∣gridTaylorQ 39 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 39=6 from rfl,show taylorPowers 39=(0, 0, 1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_40 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 40 then -c else 1)*(-1))*u^(taylorPowers 40).1*v^(taylorPowers 40).2.2.1=
      ((if 2∣gridTaylorQ 40 then u else 1)*(if 13∣gridTaylorQ 40 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 40=10 from rfl,show taylorPowers 40=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_41 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 41 then -c else 1)*(-1))*u^(taylorPowers 41).1*v^(taylorPowers 41).2.2.1=
      ((if 2∣gridTaylorQ 41 then u else 1)*(if 13∣gridTaylorQ 41 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 41=10 from rfl,show taylorPowers 41=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_42 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 42 then -c else 1)*(-1))*u^(taylorPowers 42).1*v^(taylorPowers 42).2.2.1=
      ((if 2∣gridTaylorQ 42 then u else 1)*(if 13∣gridTaylorQ 42 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 42=12 from rfl,show taylorPowers 42=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_43 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 43 then -c else 1)*(-1))*u^(taylorPowers 43).1*v^(taylorPowers 43).2.2.1=
      ((if 2∣gridTaylorQ 43 then u else 1)*(if 13∣gridTaylorQ 43 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 43=12 from rfl,show taylorPowers 43=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_44 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 44 then -c else 1)*(-1))*u^(taylorPowers 44).1*v^(taylorPowers 44).2.2.1=
      ((if 2∣gridTaylorQ 44 then u else 1)*(if 13∣gridTaylorQ 44 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 44=12 from rfl,show taylorPowers 44=(0, 0, -1, -2) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_45 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 45 then -c else 1)*(-1))*u^(taylorPowers 45).1*v^(taylorPowers 45).2.2.1=
      ((if 2∣gridTaylorQ 45 then u else 1)*(if 13∣gridTaylorQ 45 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 45=12 from rfl,show taylorPowers 45=(0, 0, -1, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_46 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 46 then -c else 1)*(-1))*u^(taylorPowers 46).1*v^(taylorPowers 46).2.2.1=
      ((if 2∣gridTaylorQ 46 then u else 1)*(if 13∣gridTaylorQ 46 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 46=13 from rfl,show taylorPowers 46=(1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_47 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 47 then -c else 1)*(-1))*u^(taylorPowers 47).1*v^(taylorPowers 47).2.2.1=
      ((if 2∣gridTaylorQ 47 then u else 1)*(if 13∣gridTaylorQ 47 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 47=13 from rfl,show taylorPowers 47=(-1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_48 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 48 then -c else 1)*(-1))*u^(taylorPowers 48).1*v^(taylorPowers 48).2.2.1=
      ((if 2∣gridTaylorQ 48 then u else 1)*(if 13∣gridTaylorQ 48 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 48=13 from rfl,show taylorPowers 48=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_49 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 49 then -c else 1)*(-1))*u^(taylorPowers 49).1*v^(taylorPowers 49).2.2.1=
      ((if 2∣gridTaylorQ 49 then u else 1)*(if 13∣gridTaylorQ 49 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 49=13 from rfl,show taylorPowers 49=(-1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_50 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 50 then -c else 1)*(-1))*u^(taylorPowers 50).1*v^(taylorPowers 50).2.2.1=
      ((if 2∣gridTaylorQ 50 then u else 1)*(if 13∣gridTaylorQ 50 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 50=13 from rfl,show taylorPowers 50=(-1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_51 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 51 then -c else 1)*(-1))*u^(taylorPowers 51).1*v^(taylorPowers 51).2.2.1=
      ((if 2∣gridTaylorQ 51 then u else 1)*(if 13∣gridTaylorQ 51 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 51=13 from rfl,show taylorPowers 51=(1, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_52 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 52 then -c else 1)*(-1))*u^(taylorPowers 52).1*v^(taylorPowers 52).2.2.1=
      ((if 2∣gridTaylorQ 52 then u else 1)*(if 13∣gridTaylorQ 52 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 52=13 from rfl,show taylorPowers 52=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_53 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 53 then -c else 1)*(-1))*u^(taylorPowers 53).1*v^(taylorPowers 53).2.2.1=
      ((if 2∣gridTaylorQ 53 then u else 1)*(if 13∣gridTaylorQ 53 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 53=13 from rfl,show taylorPowers 53=(-1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_54 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 54 then -c else 1)*(-1))*u^(taylorPowers 54).1*v^(taylorPowers 54).2.2.1=
      ((if 2∣gridTaylorQ 54 then u else 1)*(if 13∣gridTaylorQ 54 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 54=13 from rfl,show taylorPowers 54=(1, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_55 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 55 then -c else 1)*(-1))*u^(taylorPowers 55).1*v^(taylorPowers 55).2.2.1=
      ((if 2∣gridTaylorQ 55 then u else 1)*(if 13∣gridTaylorQ 55 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 55=26 from rfl,show taylorPowers 55=(0, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_56 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 56 then -c else 1)*(-1))*u^(taylorPowers 56).1*v^(taylorPowers 56).2.2.1=
      ((if 2∣gridTaylorQ 56 then u else 1)*(if 13∣gridTaylorQ 56 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 56=26 from rfl,show taylorPowers 56=(0, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_57 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 57 then -c else 1)*(-1))*u^(taylorPowers 57).1*v^(taylorPowers 57).2.2.1=
      ((if 2∣gridTaylorQ 57 then u else 1)*(if 13∣gridTaylorQ 57 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 57=26 from rfl,show taylorPowers 57=(0, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_58 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 58 then -c else 1)*(-1))*u^(taylorPowers 58).1*v^(taylorPowers 58).2.2.1=
      ((if 2∣gridTaylorQ 58 then u else 1)*(if 13∣gridTaylorQ 58 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 58=26 from rfl,show taylorPowers 58=(0, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_59 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 59 then -c else 1)*(-1))*u^(taylorPowers 59).1*v^(taylorPowers 59).2.2.1=
      ((if 2∣gridTaylorQ 59 then u else 1)*(if 13∣gridTaylorQ 59 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 59=39 from rfl,show taylorPowers 59=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_60 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 60 then -c else 1)*(-1))*u^(taylorPowers 60).1*v^(taylorPowers 60).2.2.1=
      ((if 2∣gridTaylorQ 60 then u else 1)*(if 13∣gridTaylorQ 60 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 60=39 from rfl,show taylorPowers 60=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_61 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 61 then -c else 1)*(-1))*u^(taylorPowers 61).1*v^(taylorPowers 61).2.2.1=
      ((if 2∣gridTaylorQ 61 then u else 1)*(if 13∣gridTaylorQ 61 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 61=39 from rfl,show taylorPowers 61=(-1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_62 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 62 then -c else 1)*(-1))*u^(taylorPowers 62).1*v^(taylorPowers 62).2.2.1=
      ((if 2∣gridTaylorQ 62 then u else 1)*(if 13∣gridTaylorQ 62 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 62=39 from rfl,show taylorPowers 62=(1, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_63 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 63 then -c else 1)*(-1))*u^(taylorPowers 63).1*v^(taylorPowers 63).2.2.1=
      ((if 2∣gridTaylorQ 63 then u else 1)*(if 13∣gridTaylorQ 63 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 63=52 from rfl,show taylorPowers 63=(0, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_64 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 64 then -c else 1)*(-1))*u^(taylorPowers 64).1*v^(taylorPowers 64).2.2.1=
      ((if 2∣gridTaylorQ 64 then u else 1)*(if 13∣gridTaylorQ 64 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 64=52 from rfl,show taylorPowers 64=(0, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_65 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 65 then -c else 1)*(-1))*u^(taylorPowers 65).1*v^(taylorPowers 65).2.2.1=
      ((if 2∣gridTaylorQ 65 then u else 1)*(if 13∣gridTaylorQ 65 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 65=52 from rfl,show taylorPowers 65=(0, -2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_66 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 66 then -c else 1)*(-1))*u^(taylorPowers 66).1*v^(taylorPowers 66).2.2.1=
      ((if 2∣gridTaylorQ 66 then u else 1)*(if 13∣gridTaylorQ 66 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 66=52 from rfl,show taylorPowers 66=(0, 2, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_67 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 67 then -c else 1)*(-1))*u^(taylorPowers 67).1*v^(taylorPowers 67).2.2.1=
      ((if 2∣gridTaylorQ 67 then u else 1)*(if 13∣gridTaylorQ 67 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 67=78 from rfl,show taylorPowers 67=(0, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_68 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 68 then -c else 1)*(-1))*u^(taylorPowers 68).1*v^(taylorPowers 68).2.2.1=
      ((if 2∣gridTaylorQ 68 then u else 1)*(if 13∣gridTaylorQ 68 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 68=78 from rfl,show taylorPowers 68=(0, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_69 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 69 then -c else 1)*(-1))*u^(taylorPowers 69).1*v^(taylorPowers 69).2.2.1=
      ((if 2∣gridTaylorQ 69 then u else 1)*(if 13∣gridTaylorQ 69 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 69=156 from rfl,show taylorPowers 69=(0, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

theorem taylor_scale_sign_70 (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ 70 then -c else 1)*(-1))*u^(taylorPowers 70).1*v^(taylorPowers 70).2.2.1=
      ((if 2∣gridTaylorQ 70 then u else 1)*(if 13∣gridTaylorQ 70 then -(c*v) else 1))*(-u*v) := by
  simp only [show gridTaylorQ 70=156 from rfl,show taylorPowers 70=(0, 0, 0, 0) from rfl]
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> norm_num <;> ring

end SmallLevelTwentySixGrid
