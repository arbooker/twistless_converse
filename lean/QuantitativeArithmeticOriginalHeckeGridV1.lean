module
public import SmallLevelTaylorTheoryV4
public import SmallLevelAdditiveTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticOriginalHeckeGrid
open Complex SmallLevelTaylor SmallLevelAdditive
variable (N Q : ℕ) (hQ : 0<Q)

def heckeLeading (m : ℕ) (f : ℕ→ℂ) (p : ℕ) (j : ℤ) (s : ℂ) : ℂ :=
  (∑ a∈Finset.range p, grid (2*m) f Q (j+(a:ℤ)*(Q/p:ℕ)) s)-
    ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*grid (2*m) f Q ((p:ℤ)*j) s+
    if p∣N then 0 else
      ((p:ℂ)^((m:ℂ)-s))^2*grid (2*m) f Q ((p:ℤ)^2*j) s

include hQ in
theorem original_hecke_grid {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f)
    {p : ℕ} (hp : p.Prime) (hpQ : p∣Q) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re → heckeLeading N Q m f p j s=0 := by
  have hsum (j : ℤ) (s : ℂ) :
      (∑ a∈Finset.range p, original (2*m) f ((j:ℝ)/Q+(a:ℝ)/p) s)=
      ∑ a∈Finset.range p, grid (2*m) f Q (j+(a:ℤ)*(Q/p:ℕ)) s := by
    apply Finset.sum_congr rfl
    intro a _
    unfold grid
    congr 1
    simpa only [Nat.cast_ofNat] using
      (grid_translation hQ hp.pos hpQ (t := j) (j := a))
  have h1 (j : ℤ) : (p:ℝ)*((j:ℝ)/Q)=(((p:ℤ)*j:ℤ):ℝ)/Q := by
    push_cast
    ring
  have h2 (j : ℤ) : (p:ℝ)^2*((j:ℝ)/Q)=(((p:ℤ)^2*j:ℤ):ℝ)/Q := by
    push_cast
    ring
  by_cases hb : p∣N
  · obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.normalized_additive_bad_hecke hm hf hp hb
    refine ⟨B,?_⟩
    intro j s hs
    have hh := hB ((j:ℝ)/Q) s hs
    rw [hsum,h1] at hh
    simpa only [heckeLeading,ite_eq_left hb,add_zero,grid,Nat.cast_ofNat] using hh
  · obtain ⟨B,hB⟩ := normalized_additive_hecke hf hp hb
    refine ⟨B,?_⟩
    intro j s hs
    have hh := hB ((j:ℝ)/Q) s hs
    rw [hsum,h1,h2] at hh
    simpa only [heckeLeading,ite_eq_right hb,grid,Nat.cast_ofNat] using hh


#print axioms original_hecke_grid
end QuantitativeArithmeticOriginalHeckeGrid
