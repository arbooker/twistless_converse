module

/- A separately decreasing two-prime dimension array stabilizes in a quadrant. -/
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace SpanningStationaryDimensions

theorem horizontal_le (f : ℕ → ℕ → ℕ) (hx : ∀a b,f (a+1) b≤f a b)
    (a b i : ℕ) : f (a+i) b≤f a b := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact Nat.le_trans (hx (a+i) b) ih

theorem vertical_le (f : ℕ → ℕ → ℕ) (hy : ∀a b,f a (b+1)≤f a b)
    (a b j : ℕ) : f a (b+j)≤f a b := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact Nat.le_trans (hy a (b+j)) ih

theorem stable_quadrant (f : ℕ → ℕ → ℕ)
    (hx : ∀a b,f (a+1) b≤f a b) (hy : ∀a b,f a (b+1)≤f a b) :
    ∃a b, ∀i j, f (a+i) (b+j)=f a b := by
  classical
  have hex : ∃n,∃a b,f a b=n := ⟨f 0 0,0,0,rfl⟩
  obtain ⟨a,b,hab⟩ := Nat.find_spec hex
  refine ⟨a,b,fun i j => le_antisymm ?_ ?_⟩
  · exact Nat.le_trans (vertical_le f hy (a+i) b j) (horizontal_le f hx a b i)
  · rw [hab]
    exact Nat.find_min' hex ⟨a+i,b+j,rfl⟩

#print axioms stable_quadrant

end SpanningStationaryDimensions
