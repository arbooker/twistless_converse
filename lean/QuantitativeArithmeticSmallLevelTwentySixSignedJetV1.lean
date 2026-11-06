module
public import SmallLevelTwentySixGermDAGOriginalGermsV1
public import SmallLevelTwentySixGermSourcesTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixSignedJet
open SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelTwentySixUnitMMM SmallLevelFiniteGridSupport
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm

/-- A common encoded Taylor row for either base sign at13. -/
def signedReplayJetRow (c : ℂ) (n : ℕ) (X Y Z W a b : ℂ)
    (v : ℕ→ℂ) (i : Fin 397) : ℂ :=
  laurentJetRow n X Y Z W (-1) (-1) c a b
    (fun h j => v (sourceCoordinate h j)) (selectedSource i)

/-- The three-layer germ relations retain the base sign c. In particular c=1
supplies the MMP family directly from the original continuation, with no
comparison between pole orders at distinct points. -/
theorem signed_original_replayJetRow_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v c : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= c*v)
    (n : Fin 3) (i : Fin 397) :
    HasAnalyticGerm (fun z => signedReplayJetRow c n.val (u*parameter 2 m z) (parameter 3 m z)
      (v*parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
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
  have hs := laurentJetRow_sign_scale n.val
    (parameter 2 m z) (parameter 3 m z) (parameter 13 m z) (parameter 5 m z)
    c (badParameter f 3) (badParameter f 5) u v hu hv
    (fun h j => replayVector m S.G z (sourceCoordinate h j)) (selectedSource i)
  rw [hη,hs2,hs13] at he
  simpa only [hη,hs2,hs13,signedReplayJetRow] using he.trans hs.symm

#print axioms signed_original_replayJetRow_germ
end QuantitativeArithmeticSmallLevelTwentySixSignedJet
