module

public import QuantitativeArithmeticSmallLevelThirtyFiveSixRowDataV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

def lowerFricke (m : ℕ) (G : ℂ → Fin 210 → ℂ) (s : ℂ) : ℂ :=
  G s 42+primeParameter 7 m s/primeParameter 5 m s*G s 180

def lowerSeven (m : ℕ) (G : ℂ → Fin 210 → ℂ) (s : ℂ) : ℂ :=
  sampleSum 7 (-30) (G s)+primeParameter 5 m s*sampleSum 7 6 (G s)

def lowerCombination (m : ℕ) (G : ℂ → Fin 210 → ℂ) (s : ℂ) : ℂ :=
  primeParameter 5 m s/primeParameter 7 m s*lowerFricke m G s+lowerSeven m G s

theorem source_zero_and_six_germs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) (x : ℂ) :
    HasAnalyticGerm (fun z => G z 0) x ∧ HasAnalyticGerm (fun z => G z 6) x := by
  have h0 := integer_word_infinity_germ hm hf BG G hG hGF (.generator 4)
    (by norm_num [integerRaw,integerSeed]) 0
    (by norm_num [integerDen,integerRaw,integerSeed])
  have h6 := integer_word_infinity_germ hm hf BG G hG hGF (.inv (.generator 1))
    (by norm_num [integerRaw,integerSeed,Matrix.adjugate_fin_two]) 6
    (by norm_num [integerDen,integerRaw,integerSeed,Matrix.adjugate_fin_two])
  constructor
  · refine ⟨_,h0.1 x,?_⟩
    simpa only [show gridIndex 0=0 by decide] using h0.2 x
  · refine ⟨_,h6.1 x,?_⟩
    simpa only [show gridIndex 6=6 by decide] using h6.2 x

theorem lowerCombination_identity {m : ℕ} {f : ℕ → ℂ} (h7 : badSeven f= -1)
    (G : ℂ → Fin 210 → ℂ) (s : ℂ) : lowerCombination m G s=
      G s 0-primeParameter 5 m s*G s 6+sampleSum 7 0 (G s)+
        primeParameter 5 m s*fullHeckeRow m f 7 6 s (G s) := by
  rw [seven_hecke_row h7]
  simp only [lowerCombination,lowerFricke,lowerSeven,sampleSeven_zero,
    sampleSeven_source,sampleSeven_target,sevenTargetSum]
  field_simp [primeParameter_ne_zero 5 m (by decide) s,
    primeParameter_ne_zero 7 m (by decide) s]
  ring

/-- The exact lower row combination has an analytic germ, derived from
the two source-to-infinity rows, the entire Ramanujan sum, and U_7. -/
theorem lowerCombination_analytic_germ {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) (x : ℂ) :
    HasAnalyticGerm (lowerCombination m G) x := by
  obtain ⟨h0,h6⟩ := source_zero_and_six_germs hm hf BG G hG hGF x
  obtain ⟨hR,heR⟩ := original_full_entire_germs hm hf BG G hG hGF
    (q:=7) (by decide) (by decide)
  have hr : HasAnalyticGerm (fun z => sampleSum 7 0 (G z)) x := ⟨_,hR x,heR x⟩
  have hh : HasAnalyticGerm (fun z => fullHeckeRow m f 7 6 z (G z)) x :=
    ⟨fun _ => 0,analyticAt_const,original_full_hecke_germs hm hf BG G hG hGF
      (p:=7) (by decide) (by decide) 6 x⟩
  have hZ := primeParameter_analytic 5 m (by decide) x
  apply ((h0.sub (h6.mul_analytic hZ)).add hr |>.add (hh.mul_analytic hZ)).congr
  exact Filter.Eventually.of_forall (fun z => (lowerCombination_identity h7 G z).symm)

#print axioms source_zero_and_six_germs
#print axioms lowerCombination_analytic_germ
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
