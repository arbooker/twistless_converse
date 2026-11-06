module

public import SmallLevelTwentyOneTaylorGridV1
public import SmallLevelTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive

def entireSpecs : Fin 4 → ℕ := ![1,2,3,6]
def heckeSpecs : Fin 10 → ℤ := ![2,3,4,5,6,8,9,10,11,16]

theorem entireSpecs_valid : ∀ i : Fin 4, 0<entireSpecs i ∧ entireSpecs i∣42 := by decide

/-- The four Ramanujan rows selected by the 42-grid determinant certificate
have actual entire extensions from the original hypotheses. -/
theorem original_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 k f) :
    (∀ i : Fin 4, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 21 k f (entireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 4, ∀ s : ℂ, B<s.re →
        ramanujanEntire 21 k f (entireSpecs i) s=gridSum k f 42 (entireSpecs i) 0 s := by
  have hh (i : Fin 4) := original_ramanujan_entire (by decide : 0<21) hk hf (entireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
    rw [hb i s (lt_of_le_of_lt hbi hs)]
    have hg := ramanujanAdditive_grid k f (by decide : 0<42)
      (entireSpecs_valid i).1 (entireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

/-- The exact Hecke equation on the 42-grid, for every integer row index. -/
theorem original_hecke_grid {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re →
      grid (2*m) f 42 j s+grid (2*m) f 42 (j+21) s-
        ((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s)*grid (2*m) f 42 (2*j) s+
        ((2:ℂ)^((m:ℂ)-s))^2*grid (2*m) f 42 (4*j) s=0 := by
  obtain ⟨B,hB⟩ := normalized_additive_hecke hf (by decide : Nat.Prime 2) (by decide : ¬2∣21)
  refine ⟨B,?_⟩
  intro j s hs
  have hh := hB ((j:ℝ)/42) s hs
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    Nat.cast_one,Nat.cast_ofNat,zero_div,add_zero] at hh
  have h1 : (j:ℝ)/42+1/2=((j+21:ℤ):ℝ)/42 := by push_cast; ring
  have h2 : 2*((j:ℝ)/42)=((2*j:ℤ):ℝ)/42 := by push_cast; ring
  have h4 : (4:ℝ)*((j:ℝ)/42)=((4*j:ℤ):ℝ)/42 := by push_cast; ring
  rw [h1,h2,h4] at hh
  exact hh

/-- In particular, all ten Hecke rows used by the written determinant
certificate hold simultaneously in one half-plane. -/
theorem original_selected_hecke_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ B : ℝ, ∀ i : Fin 10, ∀ s : ℂ, B<s.re →
      grid (2*m) f 42 (heckeSpecs i) s+grid (2*m) f 42 (heckeSpecs i+21) s-
        ((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s)*grid (2*m) f 42 (2*heckeSpecs i) s+
        ((2:ℂ)^((m:ℂ)-s))^2*grid (2*m) f 42 (4*heckeSpecs i) s=0 := by
  obtain ⟨B,hB⟩ := original_hecke_grid hf
  exact ⟨B,fun i s hs => hB (heckeSpecs i) s hs⟩

#print axioms original_entire_rows
#print axioms original_hecke_grid
#print axioms original_selected_hecke_rows
end SmallLevelTwentyOne
