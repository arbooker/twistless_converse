module
public import QuantitativeArithmeticSmallLevelTwentySixMMPSourceDataV1
public import QuantitativeArithmeticSmallLevelTwentySixMMPNormalizedInputV1
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPDataGerms
open QuantitativeArithmeticSmallLevelTwentySixMMPSourceData
open SmallLevelTwentySixGermSources SmallLevelPrimeRates QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixGermDAG (replayVector)
open QuantitativeArithmeticSevenLaurentRows SmallLevelLaurentDerivation

theorem data_binding : normalizedSourceRows =
    QuantitativeArithmeticSmallLevelTwentySixMMPNormalizedInput.sourceRows := rfl

theorem signed_original_derived_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ} {p : Poly}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13= v)
    (hp : Derived normalizedSourceRows 1191 p) :
    HasAnalyticGerm (fun z => eval (u*parameter 2 m z) (parameter 3 m z)
      (v*parameter 13 m z) (parameter 5 m z) (badParameter f 3) (badParameter f 5)
      1 (replayVector m S.G z) p) x := by
  rw [data_binding] at hp
  exact QuantitativeArithmeticSmallLevelTwentySixMMPNormalizedInput.signed_original_derived_germ
    S x u v hu hv hshift hx hx1 hη hs2 hs13 hp

#print axioms signed_original_derived_germ
end QuantitativeArithmeticSmallLevelTwentySixMMPDataGerms
