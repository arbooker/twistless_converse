module
public import SmallLevelPrimeGridRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Set SmallLevelAdditive SmallLevelPrimeRates

def gridHeckeSpecs : Fin 61→ℕ×ℤ :=
  ![(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),(2,17),(2,18),(2,19),(2,20),(2,21),(2,22),(2,23),(2,24),(2,25),(2,26),(2,27),(2,28),(2,29),(2,30),(2,31),(2,32),(3,0),(3,1),(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(3,13),(3,14),(3,15),(3,16),(3,17),(3,18),(3,19),(3,20),(3,21),(11,0),(11,1),(11,2),(11,3),(11,4),(11,5)]
def gridHeckeP (i : Fin 61) : ℕ := (gridHeckeSpecs i).1
def gridHeckeT (i : Fin 61) : ℤ := (gridHeckeSpecs i).2

theorem gridHeckeSpecs_valid (i : Fin 61) :
    (gridHeckeP i).Prime ∧ gridHeckeP i∣66 := by
  fin_cases i <;> decide

def gridHeckeRow (m : ℕ) (f : ℕ→ℂ) (i : Fin 61) (s : ℂ) : ℂ :=
  (∑ j∈Finset.range (gridHeckeP i),grid (2*m) f 66
    (gridHeckeT i+(j:ℤ)*(66/gridHeckeP i:ℕ)) s)-
    ((Real.sqrt (gridHeckeP i):ℂ)*f (gridHeckeP i))*(parameter (gridHeckeP i) m s)⁻¹*
      grid (2*m) f 66 ((gridHeckeP i:ℤ)*gridHeckeT i) s+
    (if gridHeckeP i∣33 then 0 else ((parameter (gridHeckeP i) m s)⁻¹)^2*
      grid (2*m) f 66 ((gridHeckeP i:ℤ)^2*gridHeckeT i) s)

/-- All 61 prime equations at 2, 3 and 11, including the two ramified primes. -/
theorem original_grid_hecke_row (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (i : Fin 61) :
    ∃ B : ℝ,∀ s : ℂ,B<s.re → gridHeckeRow m f i s=0 := by
  have hv:=gridHeckeSpecs_valid i
  by_cases hb : gridHeckeP i∣33
  · obtain ⟨B,hB⟩:=SmallLevelPrimeGrid.original_ramified_rows hf hm hv.1 hb
      (by decide : 0<66) hv.2
    exact ⟨B,fun s hs => by simpa only [gridHeckeRow,ite_eq_left hb,add_zero] using hB (gridHeckeT i) s hs⟩
  · obtain ⟨B,hB⟩:=SmallLevelPrimeGrid.original_good_rows hf hv.1 hb
      (by decide : 0<66) hv.2
    exact ⟨B,fun s hs => by simpa only [gridHeckeRow,ite_eq_right hb] using hB (gridHeckeT i) s hs⟩

theorem original_grid_hecke_system (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ B : ℝ,∀ i : Fin 61,∀ s : ℂ,B<s.re → gridHeckeRow m f i s=0 := by
  choose b hb using original_grid_hecke_row m hm hf
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 61) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  exact ⟨B,fun i s hs => hb i s (lt_of_le_of_lt (hbB i) hs)⟩

#print axioms original_grid_hecke_system
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
