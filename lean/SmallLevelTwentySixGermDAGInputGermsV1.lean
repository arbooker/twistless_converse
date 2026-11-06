module
public import SmallLevelTwentySixGermDAGOriginalGermsV1
public import SmallLevelTwentySixGermDAGSourceMatchAllV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGermDAG
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation

theorem original_input_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -1) (hs2 : badParameter f 2= -1) (hs13 : badParameter f 13= -1)
    (i : ℕ) (hi : i<1191) :
    HasAnalyticGerm (fun z => eval (parameter 2 m z) (parameter 3 m z)
      (parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
      1 (replayVector m S.G z) (sourceRows i)) x := by
  let n : Fin 3 := ⟨i/397,by omega⟩
  let j : Fin 397 := ⟨i%397,Nat.mod_lt _ (by decide)⟩
  have hij : n.val*397+j.val=i := by dsimp [n,j]; omega
  have hh := original_replayJetRow_germ S x hshift hx hx1 hη hs2 hs13 n j
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  have he := source_rows_match (parameter 2 m z) (parameter 3 m z)
    (parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
    (parameter_ne_zero 2 m (by decide) z) (parameter_ne_zero 3 m (by decide) z)
    (parameter_ne_zero 13 m (by decide) z) (parameter_ne_zero 5 m (by decide) z)
    (replayVector m S.G z) n j
  rw [hij] at he
  exact he.symm

/-- A checked finite derivation acts on the actual three-layer functions.
Concrete raw-row certificates are instantiated in the next module. -/
theorem original_derived_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ} {p : Poly}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -1) (hs2 : badParameter f 2= -1) (hs13 : badParameter f 13= -1)
    (hp : Derived sourceRows 1191 p) :
    HasAnalyticGerm (fun z => eval (parameter 2 m z) (parameter 3 m z)
      (parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
      1 (replayVector m S.G z) p) x := by
  apply hp.germ (parameter 2 m) (parameter 3 m) (parameter 13 m) (parameter 5 m)
    (badParameter f 3) (badParameter f 5) 1 x (replayVector m S.G)
  · exact parameter_analytic 2 m (by decide) x
  · exact parameter_analytic 3 m (by decide) x
  · exact parameter_analytic 13 m (by decide) x
  · exact parameter_analytic 5 m (by decide) x
  · exact parameter_ne_zero 2 m (by decide)
  · exact parameter_ne_zero 3 m (by decide)
  · exact parameter_ne_zero 13 m (by decide)
  · exact parameter_ne_zero 5 m (by decide)
  · exact original_input_germ S x hshift hx hx1 hη hs2 hs13

#print axioms original_input_germ
#print axioms original_derived_germ
end SmallLevelTwentySixGermDAG
