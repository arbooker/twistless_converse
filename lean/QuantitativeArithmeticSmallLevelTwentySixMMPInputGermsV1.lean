module
public import QuantitativeArithmeticSmallLevelTwentySixMMPSourceReuseV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPInputGerms
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermDAG (replayVector)
open QuantitativeArithmeticSmallLevelTwentySixSignedJet
open QuantitativeArithmeticSmallLevelTwentySixMMPSourceReuse (source source_match)
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation

def sourceRows (i : ℕ) : Poly := source (i/397) ⟨i%397,Nat.mod_lt _ (by decide)⟩

theorem signed_original_input_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= v)
    (i : ℕ) (hi : i < 1191) :
    HasAnalyticGerm (fun z => eval (u*parameter 2 m z) (parameter 3 m z)
      (v*parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
      1 (replayVector m S.G z) (sourceRows i)) x := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  let n : Fin 3 := ⟨i/397,by omega⟩
  let j : Fin 397 := ⟨i%397,Nat.mod_lt _ (by decide)⟩
  have hh := signed_original_replayJetRow_germ S x u v 1 hu hv hshift hx hx1 hη hs2 (by simpa using hs13) n j
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  have he := source_match n j (u*parameter 2 m z) (parameter 3 m z)
    (v*parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) z)) (parameter_ne_zero 3 m (by decide) z)
    (mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) z)) (parameter_ne_zero 5 m (by decide) z)
    (replayVector m S.G z)
  exact he.symm

/-- A checked finite derivation acts on the actual three-layer functions.
Concrete raw-row certificates are instantiated in the next module. -/
theorem signed_original_derived_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ} {p : Poly}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= v)
    (hp : Derived sourceRows 1191 p) :
    HasAnalyticGerm (fun z => eval (u*parameter 2 m z) (parameter 3 m z)
      (v*parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
      1 (replayVector m S.G z) p) x := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  apply hp.germ (fun z => u*parameter 2 m z) (parameter 3 m)
    (fun z => v*parameter 13 m z) (parameter 5 m)
    (badParameter f 3) (badParameter f 5) 1 x (replayVector m S.G)
  · exact analyticAt_const.mul (parameter_analytic 2 m (by decide) x)
  · exact parameter_analytic 3 m (by decide) x
  · exact analyticAt_const.mul (parameter_analytic 13 m (by decide) x)
  · exact parameter_analytic 5 m (by decide) x
  · exact fun z => mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) z)
  · exact parameter_ne_zero 3 m (by decide)
  · exact fun z => mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) z)
  · exact parameter_ne_zero 5 m (by decide)
  · exact signed_original_input_germ S x u v hu hv hshift hx hx1 hη hs2 hs13

#print axioms signed_original_input_germ
#print axioms signed_original_derived_germ
end QuantitativeArithmeticSmallLevelTwentySixMMPInputGerms
