module
public import SmallLevelPrimeGridRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Set SmallLevelAdditive SmallLevelPrimeRates

def gridHeckeSpecs : Fin 51→ℕ×ℤ :=
  ![(2, 7),(2, 8),(2, 9),(2, 11),(2, 22),(2, 42),(2, 52),(2, 55),(2, 66),(2, 95),(2, 100),(2, 104),(2, 105),(2, 110),(2, 140),(2, 143),(2, 162),(2, 185),(2, 205),(2, 225),(2, 228),(2, 250),(2, 295),(2, 368),(3, 13),(3, 20),(3, 25),(3, 26),(3, 35),(3, 40),(3, 55),(3, 65),(3, 75),(3, 95),(3, 110),(3, 150),(3, 185),(3, 195),(3, 205),(3, 220),(3, 240),(5, 26),(5, 39),(5, 52),(5, 104),(5, 117),(5, 130),(13, 10),(13, 20),(13, 40),(13, 50)]
def gridHeckeP (i : Fin 51) : ℕ := (gridHeckeSpecs i).1
def gridHeckeT (i : Fin 51) : ℤ := (gridHeckeSpecs i).2

theorem gridHeckeSpecs_valid (i : Fin 51) :
    (gridHeckeP i).Prime ∧ gridHeckeP i∣780 := by
  fin_cases i <;> decide

def gridHeckeRow (m : ℕ) (f : ℕ→ℂ) (i : Fin 51) (s : ℂ) : ℂ :=
  (∑ j∈Finset.range (gridHeckeP i),grid (2*m) f 780
    (gridHeckeT i+(j:ℤ)*(780/gridHeckeP i:ℕ)) s)-
    ((Real.sqrt (gridHeckeP i):ℂ)*f (gridHeckeP i))*(parameter (gridHeckeP i) m s)⁻¹*
      grid (2*m) f 780 ((gridHeckeP i:ℤ)*gridHeckeT i) s+
    (if gridHeckeP i∣26 then 0 else ((parameter (gridHeckeP i) m s)⁻¹)^2*
      grid (2*m) f 780 ((gridHeckeP i:ℤ)^2*gridHeckeT i) s)

/-- All51 prime equations, including both ramified and both good primes. -/
theorem original_grid_hecke_row (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (i : Fin 51) :
    ∃ B : ℝ,∀ s : ℂ,B<s.re → gridHeckeRow m f i s=0 := by
  have hv:=gridHeckeSpecs_valid i
  by_cases hb : gridHeckeP i∣26
  · obtain ⟨B,hB⟩:=SmallLevelPrimeGrid.original_ramified_rows hf hm hv.1 hb
      (by decide : 0<780) hv.2
    exact ⟨B,fun s hs => by simpa only [gridHeckeRow,ite_eq_left hb,add_zero] using hB (gridHeckeT i) s hs⟩
  · obtain ⟨B,hB⟩:=SmallLevelPrimeGrid.original_good_rows hf hv.1 hb
      (by decide : 0<780) hv.2
    exact ⟨B,fun s hs => by simpa only [gridHeckeRow,ite_eq_right hb] using hB (gridHeckeT i) s hs⟩

theorem original_grid_hecke_system (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ B : ℝ,∀ i : Fin 51,∀ s : ℂ,B<s.re → gridHeckeRow m f i s=0 := by
  choose b hb using original_grid_hecke_row m hm hf
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 51) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  exact ⟨B,fun i s hs => hb i s (lt_of_le_of_lt (hbB i) hs)⟩

#print axioms original_grid_hecke_system
end SmallLevelTwentySixGrid
