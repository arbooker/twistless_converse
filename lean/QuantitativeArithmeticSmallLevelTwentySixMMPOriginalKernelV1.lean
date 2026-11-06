module
public import QuantitativeArithmeticSmallLevelTwentySixMMPTopPoleV1
public import SmallLevelTwentySixGermSourcesTheoryV4
public import SmallLevelTwentySixGermDAGOriginalGermsV1
public import SmallLevelLaurentTwoCoordinateGermsV1
set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPOriginalKernel
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermSources SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelTwentySixGermDAG (replayVector)
open SmallLevelTwentySixGrid (phase badParameter replayTopIndex)
open SmallLevelTwentySixUnitMMM (support support_injective)

theorem replay_top (m : ℕ) (G : ℂ → Fin 320 → ℂ) (z : ℂ) (i : Fin 2) :
    replayVector m G z i = G z (replayTopIndex i) := by
  fin_cases i
  · change extend support (G z) (support 110) = G z 110
    exact extend_at support support_injective (G z) 110
  · change extend support (G z) (support 222) = G z 222
    exact extend_at support support_injective (G z) 222

/-- Any collection of polynomial syzygies supported on the two top
coordinates shares a single nonzero leading vector at an original pole.
Analyticity of the syzygies must be proved before applying this lemma;
no restriction is imposed on pole orders of the eliminated lower layers. -/
theorem original_leading_kernel {ρ : Type*} {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (s u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0)
    (rows : ρ → Poly)
    (hsupport : ∀ i t,t∈rows i → t.2.1=0 ∨ t.2.1=1)
    (hgerms : ∀ i,HasAnalyticGerm (fun z => eval
      (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) (rows i)) s) :
    ∃ w : Fin 2 → ℂ,w≠0 ∧ ∀ i,eval
      (u*parameter 2 m s) ((parameter 3 m s)^2)
      (v*parameter 13 m s) ((parameter 5 m s)^2)
      (badParameter f 3*parameter 3 m s) (badParameter f 5*parameter 5 m s)
      1 (fun j => if j=0 then w 0 else w 1) (rows i)=0 := by
  have hG := S.grid_G_eq T
  have htshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => T.G z j) (s+n) := by
    simpa only [hG] using hshift
  have htpole : ∃ j,meromorphicOrderAt (fun z => T.G z j) s<0 := by
    simpa only [hG] using hpole
  have htop := QuantitativeArithmeticSmallLevelTwentySixMMPTopPole.PoleSystem.pole_in_replay_top
    T s u v hu hv htshift hη hs2 hs13 htpole
  have hstop : ∃ i : Fin 2,meromorphicOrderAt (fun z => S.G z (replayTopIndex i)) s<0 := by
    simpa only [hG] using htop
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  apply SmallLevelLaurentTwoCoordinateGerms.leading_kernel
    (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
    (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
    (fun z => badParameter f 3*parameter 3 m z)
    (fun z => badParameter f 5*parameter 5 m z) (fun _ => 1)
    (fun i z => S.G z (replayTopIndex i)) rows s
    (analyticAt_const.mul (parameter_analytic 2 m (by decide) s))
    ((parameter_analytic 3 m (by decide) s).pow 2)
    (analyticAt_const.mul (parameter_analytic 13 m (by decide) s))
    ((parameter_analytic 5 m (by decide) s).pow 2)
    (analyticAt_const.mul (parameter_analytic 3 m (by decide) s))
    (analyticAt_const.mul (parameter_analytic 5 m (by decide) s)) analyticAt_const
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s))
    (pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) s))
    (mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) s))
    (pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) s))
    (fun i => (S.meromorphic (replayTopIndex i) s).meromorphicAt)
    hstop hsupport
  intro i
  apply (hgerms i).congr
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [SmallLevelLaurentTwoCoordinateGerms.eval_two_coordinates _ _ _ _ _ _ _ _ _ (hsupport i),
      SmallLevelLaurentTwoCoordinateGerms.eval_two_coordinates _ _ _ _ _ _ _ _ _ (hsupport i)]
  have h0 : replayVector m S.G z 0 = S.G z (replayTopIndex 0) := by
    simpa using replay_top m S.G z (0 : Fin 2)
  have h1 : replayVector m S.G z 1 = S.G z (replayTopIndex 1) := by
    simpa using replay_top m S.G z (1 : Fin 2)
  rw [h0,h1]
  simp

#print axioms replay_top
#print axioms original_leading_kernel
end QuantitativeArithmeticSmallLevelTwentySixMMPOriginalKernel
