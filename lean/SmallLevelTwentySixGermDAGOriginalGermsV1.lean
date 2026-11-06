module
public import SmallLevelTwentySixGermDAGCoordinatesV1
public import SmallLevelTwentySixGermSourcesTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelTwentySixUnitMMM SmallLevelFiniteGridSupport
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm

theorem leadingRows_congr_support (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (v w : Fin 780→ℂ) (he : ∀ j : Fin 320,v (support j)=w (support j)) (i : GridSource) :
    gridLeadingRows m f ε s v i=gridLeadingRows m f ε s w i := by
  rw [←leadingRows_restrict m f ε s v i,←leadingRows_restrict m f ε s w i]
  rw [funext he]

theorem slopeRows_restrict (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 780→ℂ) (i : GridSource) :
    slopeRows m f ε n s (extension support (fun j => v (support j))) i=
      slopeRows m f ε n s v i := by
  cases i <;> simp only [slopeRows,groupTarget_restrict,taylorTarget_restrict]

theorem slopeRows_congr_support (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v w : Fin 780→ℂ) (he : ∀ j : Fin 320,v (support j)=w (support j)) (i : GridSource) :
    slopeRows m f ε n s v i=slopeRows m f ε n s w i := by
  rw [←slopeRows_restrict m f ε n s v i,←slopeRows_restrict m f ε n s w i]
  rw [funext he]

theorem physical_jet_congr_support (m n : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (v w : ℕ→Fin 780→ℂ)
    (he : ∀ h,h≤n → ∀ j : Fin 320,v h (support j)=w h (support j)) (i : GridSource) :
    laurentJetRow n (parameter 2 m s) (parameter 3 m s) (parameter 13 m s)
      (parameter 5 m s) (phase m ε) (badParameter f 2) (badParameter f 13)
      (badParameter f 3) (badParameter f 5) v i =
    laurentJetRow n (parameter 2 m s) (parameter 3 m s) (parameter 13 m s)
      (parameter 5 m s) (phase m ε) (badParameter f 2) (badParameter f 13)
      (badParameter f 3) (badParameter f 5) w i := by
  simp only [laurentJetRow_physical]
  apply congrArg₂ (fun p q : ℂ => p-q)
  · exact leadingRows_congr_support m f ε _ (v n) (w n) (he n le_rfl) i
  · apply Finset.sum_congr rfl
    intro h hh
    rw [slopeRows_congr_support m f ε (n-h) _ (v h) (w h)
      (he h (Nat.le_of_lt (Finset.mem_range.mp hh))) i]

def replayVector (m : ℕ) (G : ℂ→Fin 320→ℂ) (z : ℂ) : ℕ→ℂ :=
  encodedVector (fun h => extension support (normalizedLayer m G z h))

/-- The actual three-layer continuation supplies the functions used in
the MMM replay. These sign equalities specify this chart; no pole-order
or row-elimination conclusion is assumed. -/
theorem original_replayJetRow_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -1) (hs2 : badParameter f 2= -1) (hs13 : badParameter f 13= -1)
    (n : Fin 3) (i : Fin 397) :
    HasAnalyticGerm (fun z => replayJetRow n.val (parameter 2 m z) (parameter 3 m z)
      (parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
      (replayVector m S.G z) i) x := by
  have hh := S.laurent_jet_germ x hshift hx hx1 n (selectedSource i)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  have he := physical_jet_congr_support m n.val f ε z
    (fun h => extension support (normalizedLayer m S.G z h))
    (fun h j => replayVector m S.G z (sourceCoordinate h j))
    (fun h hh j => (encodedVector_support
      (fun h => extension support (normalizedLayer m S.G z h)) h
      (lt_of_le_of_lt hh n.isLt) j).symm) (selectedSource i)
  simpa only [hη,hs2,hs13,replayJetRow] using he

#print axioms physical_jet_congr_support
#print axioms original_replayJetRow_germ
end SmallLevelTwentySixGermDAG
