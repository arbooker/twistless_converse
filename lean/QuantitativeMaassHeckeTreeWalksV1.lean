module

public import QuantitativeMaassHeckeTreeIntegralV1
public import QuantitativeMaassTreeOperatorV1

set_option autoImplicit false
@[expose] public section

open scoped BigOperators

namespace QuantitativeMaass
namespace HeckeUpper

def root : HeckeUpper := ⟨1,0,1⟩

theorem root_det : root.det = 1 := rfl

theorem root_primitive (p : ℕ) [Fact p.Prime] : primitive p root := by
  have hp : ¬ (p : ℤ) ∣ 1 := by exact_mod_cast (Fact.out : p.Prime).not_dvd_one
  rintro ⟨ha, _, _⟩
  exact hp ha

/-- A literal finite sum over all sequences of the p+1 normalized integral
Hecke branches, testing determinant one at the endpoint. -/
noncomputable def walks (p : ℕ) [Fact p.Prime] : ℕ → HeckeUpper → ℕ
  | 0, M => if M.det = 1 then 1 else 0
  | n + 1, M => ∑ j : Option (ZMod p), walks p n (next p j M)

/-- The arithmetic cancellation theorem yields the tree radial recurrence
for actual matrix-word endpoint counts. -/
theorem walks_eq_tree (p : ℕ) [Fact p.Prime] (n k : ℕ) (M : HeckeUpper)
    (hM : primitive p M) (hdet : M.det = (p : ℤ)^k) :
    walks p n M = treeWalkCount (p + 1) n k := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : ¬ (p : ℤ) ∣ 1 := by exact_mod_cast (Fact.out : p.Prime).not_dvd_one
  induction n generalizing M k with
  | zero =>
    cases k with
    | zero => simp [walks, treeWalkCount, hdet]
    | succ k =>
      have hn : M.det ≠ 1 := by
        intro he
        apply hp1
        rw [← he, hdet, pow_succ']
        exact dvd_mul_right _ _
      simp [walks, treeWalkCount, hn]
  | succ n ih =>
    cases k with
    | zero =>
      have hnot (j : Option (ZMod p)) : ¬ cancels p j M :=
        no_cancel p M (by simpa only [hdet, pow_zero] using hp1) j
      have hn (j : Option (ZMod p)) : (next p j M).det = (p : ℤ)^1 := by
        rw [next_det_forward p j M (hnot j), hdet]
        simp
      have hpoint (j : Option (ZMod p)) : walks p n (next p j M) = treeWalkCount (p+1) n 1 :=
        ih 1 _ (next_primitive p hpne j M hM) (hn j)
      simp only [walks, treeWalkCount]
      simp_rw [hpoint]
      simp
    | succ k =>
      have hd : (p : ℤ) ∣ M.det := by
        rw [hdet, pow_succ']
        exact dvd_mul_right _ _
      obtain ⟨back, hback, hunique⟩ := unique_cancel p M hM hd
      have hpoint (j : Option (ZMod p)) : walks p n (next p j M) =
          if j = back then treeWalkCount (p+1) n k else treeWalkCount (p+1) n (k+2) := by
        by_cases hj : j = back
        · subst j
          rw [ite_eq_left rfl]
          apply ih k _ (next_primitive p hpne back M hM)
          apply mul_left_cancel₀ hpne
          rw [next_det_cancel p hpne back M hback, hdet, pow_succ']
        · rw [ite_eq_right hj]
          have hnc : ¬ cancels p j M := fun h => hj (hunique j h)
          apply ih (k+2) _ (next_primitive p hpne j M hM)
          rw [next_det_forward p j M hnc, hdet]
          simp only [pow_succ']
      rw [walks, treeWalkCount]
      simp_rw [hpoint]
      rw [Finset.sum_ite]
      have heq : Finset.univ.filter (fun j : Option (ZMod p) => j = back) = {back} := by
        ext j
        simp
      rw [heq]
      simp [Finset.filter_ne', Finset.card_erase_of_mem]

/-- The normalized integral representatives and actual colored-tree
adjacency have exactly the same unnormalized return coefficient. -/
theorem walks_root_eq_tree (p n : ℕ) [Fact p.Prime] :
    walks p n root = treeWalkCount (p+1) n 0 :=
  walks_eq_tree p n 0 root (root_primitive p) (by simp [root_det])

#print axioms walks_eq_tree
#print axioms walks_root_eq_tree

end HeckeUpper
end QuantitativeMaass
