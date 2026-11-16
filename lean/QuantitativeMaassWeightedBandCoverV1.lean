module

public import QuantitativeMaassUnitBandCoverV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeMaass

/-- Nonnegative weights can be summed over an overlapping finite cover. -/
theorem finite_cover_weight_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : κ→ι→Prop) [∀ j i,Decidable (P j i)] (hcover : ∀ i,∃ j,P j i)
    (w : ι→ℝ) (hw : ∀ i,0≤w i) :
    ∑ i,w i≤∑ j,∑ i : {i // P j i},w i := by
  classical
  calc
    _ ≤ ∑ i,∑ j,if P j i then w i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨j,hj⟩ := hcover i
      have hh := Finset.single_le_sum
        (f:=fun j => if P j i then w i else (0:ℝ))
        (s:=Finset.univ) (fun j _ => by split_ifs; exact hw i; exact le_rfl) (Finset.mem_univ j)
      simpa only [ite_eq_left hj] using hh
    _ = ∑ j,∑ i,if P j i then w i else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [←Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) w

#print axioms finite_cover_weight_le
end QuantitativeMaass
