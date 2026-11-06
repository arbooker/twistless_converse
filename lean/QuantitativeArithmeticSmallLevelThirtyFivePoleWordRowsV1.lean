module

public import QuantitativeArithmeticUniversalPoleVectorV1
public import QuantitativeArithmeticSmallLevelThirtyFiveWordLaurentV1
public import QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

/-- Every closed word gives a constraint on the same principal-part vector.
The integer certificate is enough; no additive continuation is assumed. -/
theorem pole_word_constraint {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (r : ClosedWordRow) :
    v (gridIndex r.source)-rationalWordCoefficient m (ε*I^(2*m)) r.word r.source 0 x*
      v (gridIndex r.target)=0 := by
  obtain ⟨B,H,hrow⟩ := integer_word_grid_germs hm hf ε hε hlaw BG G hG hGF
    r.word r.nonaffine r.source r.target r.denominator r.closed
  have he := hv.taylor hG hshift B (wordLeadingRow m (ε*I^(2*m)) r)
    (wordShiftRow m (ε*I^(2*m)) r) H
    (wordLeadingRow_analytic m (ε*I^(2*m)) r x)
    (fun n j => wordShiftRow_analytic m (ε*I^(2*m)) r n x j)
    (fun n z hz => (hrow n).1 z hz)
    (fun n hn => by
      simpa only [wordLeadingRow_apply,wordShiftRow_apply] using (hrow n).2 x hn)
  simpa only [wordLeadingRow_apply] using he

theorem sampleSum_three (v : Fin 210 → ℂ) : sampleSum 3 0 v=v 70+v 140 := by
  norm_num [sampleSum,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]

/-- The primitive denominator-three sum is entire, so it annihilates every
universal principal-part vector independently of its pole order. -/
theorem pole_ramanujan_three {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G x v) : v 70+v 140=0 := by
  obtain ⟨hE,he⟩ := original_full_entire_germs hm hf BG G hG hGF
    (q:=3) (by decide) (by decide)
  let A : ℂ → Fin 210 → ℂ := fun _ j => (if j=70 then 1 else 0)+(if j=140 then 1 else 0)
  have hA (z : ℂ) (u : Fin 210 → ℂ) : (∑ j, A z j*u j)=u 70+u 140 := by
    simp [A,add_mul,Finset.sum_add_distrib]
  have hrow : (fun z => ∑ j, A z j*G z j)=ᶠ[𝓝[≠] x]
      SmallLevelTaylor.ramanujanEntire 35 (2*m) f 3 := by
    simpa only [hA,sampleSum_three] using he x
  have hh := hv.2 A _ (fun _ => analyticAt_const) (hE x) hrow
  simpa only [hA] using hh

#print axioms pole_word_constraint
#print axioms pole_ramanujan_three
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
