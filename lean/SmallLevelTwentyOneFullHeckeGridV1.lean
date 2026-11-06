module

public import SmallLevelTwentyOneMatrixSystemV1
public import QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneFullHecke
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive

def heckeLeading (m : ℕ) (f : ℕ→ℂ) (p : ℕ) (j : ℤ) (s : ℂ) : ℂ :=
  (∑ a∈Finset.range p, grid (2*m) f 42 (j+(a:ℤ)*(42/p:ℕ)) s)-
    ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*grid (2*m) f 42 ((p:ℤ)*j) s+
    if p∣21 then 0 else
      ((p:ℂ)^((m:ℂ)-s))^2*grid (2*m) f 42 ((p:ℤ)^2*j) s

theorem original_hecke_grid {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    {p : ℕ} (hp : p.Prime) (hpQ : p∣42) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re → heckeLeading m f p j s=0 := by
  have hsum (j : ℤ) (s : ℂ) :
      (∑ a∈Finset.range p, original (2*m) f ((j:ℝ)/42+(a:ℝ)/p) s)=
      ∑ a∈Finset.range p, grid (2*m) f 42 (j+(a:ℤ)*(42/p:ℕ)) s := by
    apply Finset.sum_congr rfl
    intro a _
    unfold grid
    congr 1
    simpa only [Nat.cast_ofNat] using
      (grid_translation (by decide : 0<42) hp.pos hpQ (t := j) (j := a))
  have h1 (j : ℤ) : (p:ℝ)*((j:ℝ)/42)=(((p:ℤ)*j:ℤ):ℝ)/42 := by
    push_cast
    ring
  have h2 (j : ℤ) : (p:ℝ)^2*((j:ℝ)/42)=(((p:ℤ)^2*j:ℤ):ℝ)/42 := by
    push_cast
    ring
  by_cases hb : p∣21
  · obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.normalized_additive_bad_hecke hm hf hp hb
    refine ⟨B,?_⟩
    intro j s hs
    have hh := hB ((j:ℝ)/42) s hs
    rw [hsum,h1] at hh
    simpa only [heckeLeading,ite_eq_left hb,add_zero,grid,Nat.cast_ofNat] using hh
  · obtain ⟨B,hB⟩ := normalized_additive_hecke hf hp hb
    refine ⟨B,?_⟩
    intro j s hs
    have hh := hB ((j:ℝ)/42) s hs
    rw [hsum,h1,h2] at hh
    simpa only [heckeLeading,ite_eq_right hb,grid,Nat.cast_ofNat] using hh


#print axioms original_hecke_grid
end SmallLevelTwentyOneFullHecke
