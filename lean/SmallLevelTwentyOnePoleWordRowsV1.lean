module

public import SmallLevelTwentyOneWordInfinityGermsV1
public import QuantitativeArithmeticUniversalPoleVectorV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Filter Set SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- A closed word contributes a row to the SAME principal-part vector as
every other analytic equation. No assumption on a common pole order is made. -/
theorem pole_word_constraint {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (w : Word) (hC : coordC w≠0) (t u : ℤ) (ht : wordDen w t≠0)
    (hu : (coordA w*((t:ℝ)/42)+coordB w)/wordDen w t=(u:ℝ)/42) :
    v (gridIndex t)-wordCoefficient m (ε*I^(2*m)) w t 0 x*v (gridIndex u)=0 := by
  classical
  obtain ⟨B,H,hrow⟩ := word_grid_germs_of_law hf ε hε hlaw BG G hG hGF w hC t u ht hu
  let A : ℂ → Fin 42 → ℂ := fun s j =>
    (if j=gridIndex t then 1 else 0)-
      (if j=gridIndex u then wordCoefficient m (ε*I^(2*m)) w t 0 s else 0)
  let C : ℕ → ℂ → Fin 42 → ℂ := fun n s j =>
    if j=gridIndex u then wordCoefficient m (ε*I^(2*m)) w t (n+1) s else 0
  have hA (s : ℂ) (a : Fin 42 → ℂ) :
      (∑ j, A s j*a j)=a (gridIndex t)-wordCoefficient m (ε*I^(2*m)) w t 0 s*a (gridIndex u) := by
    simp [A,sub_mul,Finset.sum_sub_distrib,ite_mul]
  have hCsum (n : ℕ) (s : ℂ) (a : Fin 42 → ℂ) :
      (∑ j, C n s j*a j)=wordCoefficient m (ε*I^(2*m)) w t (n+1) s*a (gridIndex u) := by
    simp [C,ite_mul]
  have hAa (j : Fin 42) : AnalyticAt ℂ (fun s => A s j) x := by
    have hc := wordCoefficient_analytic m (ε*I^(2*m)) w t ht 0 x
    dsimp only [A]
    split_ifs <;> fun_prop
  have hCa (n : ℕ) (j : Fin 42) : AnalyticAt ℂ (fun s => C n s j) x := by
    dsimp only [C]
    split_ifs
    · exact wordCoefficient_analytic m _ w t ht (n+1) x
    · exact analyticAt_const
  have he := hv.taylor hG hshift B A C H hAa hCa
    (fun n z hz => (hrow n).1 z hz)
    (fun n hn => by simpa only [hA,hCsum] using (hrow n).2 x hn)
  simpa only [hA] using he

/-- A source mapped to infinity has zero coordinate in every universal
principal-part vector, because its Mellin transform is entire. -/
theorem pole_infinity_constraint {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (w : Word) (hC : coordC w≠0) (t : ℤ) (ht : wordDen w t=0) :
    v (gridIndex t)=0 := by
  classical
  obtain ⟨hE,he⟩ := original_word_infinity_germ hm hf BG G hG hGF w hC t ht
  let A : ℂ → Fin 42 → ℂ := fun _ j => if j=gridIndex t then 1 else 0
  have hA (s : ℂ) (a : Fin 42 → ℂ) : (∑ j, A s j*a j)=a (gridIndex t) := by simp [A]
  have hh := hv.2 A (sourceEntire (2*m) f t) (fun _ => analyticAt_const) (hE x)
    (by simpa only [hA] using he x)
  simpa only [hA] using hh

#print axioms pole_word_constraint
#print axioms pole_infinity_constraint
end SmallLevelTwentyOneKnownWords
