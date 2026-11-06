module
public import SmallLevelLeadingCoordinateDetectionV1
public import SmallLevelTwentySixUnitMMMFreeKernelTheoryV4
public import SmallLevelTwentySixGridPoleSystemV1
public import SmallLevelTwentySixUnitMMMTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 7000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Matrix SmallLevelPrimeRates SmallLevelFiniteGridSupport QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixUnitMMM (support support_injective)

def replayTopIndex : Fin 2→Fin 320 := ![110,222]

theorem PoleSystem.leading_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (i : GridSource) :
    HasAnalyticGerm (fun z => ∑ j,fullLeadingMatrix m f ε z i j*S.G z j) x := by
  exact leading_taylor_germ S.G x S.meromorphic hshift S.B
    (fun z j => fullLeadingMatrix m f ε z i j)
    (fun n z j => fullShiftMatrix m f ε n z i j) (fun n z => S.E n z i)
    (fun n j => fullShiftMatrix_analytic m f ε n i j x)
    (fun n hn => S.error n i x hn)
    (fun n hn => S.continued_rows n i x hn)

/-- In the four MMM-related sign cases, any highest pole of the full
original grid is detected in coordinate300 or540. -/
theorem PoleSystem.pole_in_replay_top {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0) :
    ∃ i : Fin 2,meromorphicOrderAt (fun z => S.G z (replayTopIndex i)) x<0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  apply SmallLevelLeadingCoordinateDetection.pole_in_detecting_coordinates S.G x replayTopIndex
    (fullLeadingMatrix m f ε) (fun j => S.meromorphic j x) hpole
    (fun i j => fullLeadingMatrix_analytic m f ε i j x) (S.leading_germ x hshift)
  intro w hw hcoords
  let V : Fin 780→ℂ := extension support w
  have hmatrix : fullLeadingMatrix m f ε x *ᵥ w=gridLeadingRows m f ε x V := by
    rw [fullLeadingMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
    rfl
  have hsource : ∀ i,SmallLevelTwentySixUnitMMM.sourceRows
      (u*parameter 2 m x) (parameter 3 m x) (v*parameter 13 m x) (parameter 5 m x)
      (badParameter f 3) (badParameter f 5) V i=0 := by
    intro i
    rw [SmallLevelTwentySixUnitMMM.scaled_sourceRows_actual m f ε u v x hu hv hη hs2 hs13]
    rw [←hmatrix]
    exact hw (SmallLevelTwentySixUnitMMM.selectedSource i)
  have h300 : V 300=0 := by
    change extend support w (support 110)=0
    rw [extend_at support support_injective]
    exact hcoords 0
  have h540 : V 540=0 := by
    change extend support w (support 222)=0
    rw [extend_at support support_injective]
    exact hcoords 1
  have hz := SmallLevelTwentySixUnitMMM.FreeKernel.source_zero_of_replay_free
    (u*parameter 2 m x) (parameter 3 m x) (v*parameter 13 m x) (parameter 5 m x)
    (badParameter f 3) (badParameter f 5)
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x))
    (parameter_ne_zero 3 m (by decide) x)
    (mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) x))
    (parameter_ne_zero 5 m (by decide) x) V hsource h300 h540
  funext j
  have hj := hz j
  change extend support w (support j)=0 at hj
  simpa only [extend_at support support_injective,Pi.zero_apply] using hj

#print axioms PoleSystem.leading_germ
#print axioms PoleSystem.pole_in_replay_top
end SmallLevelTwentySixGrid
