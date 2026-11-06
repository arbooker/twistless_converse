module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.List.Chain
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

open scoped BigOperators lp

namespace QuantitativeMaass

/-- Pullback by a permutation, constructed directly on the actual l² space. -/
noncomputable def l2Permutation {V : Type*} (e : V ≃ V) :
    ℓ²(V, ℂ) ≃ₗᵢ[ℂ] ℓ²(V, ℂ) where
  toFun f := ⟨fun v => f (e v), memℓp_gen ((e.summable_iff).mpr
    ((lp.memℓp f).summable (by norm_num)))⟩
  invFun f := ⟨fun v => f (e.symm v), memℓp_gen ((e.symm.summable_iff).mpr
    ((lp.memℓp f).summable (by norm_num)))⟩
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun v => ‖f v‖ ^ (2 : ENNReal).toReal)

@[simp] theorem l2Permutation_apply {V : Type*} (e : V ≃ V)
    (f : ℓ²(V, ℂ)) (v : V) : l2Permutation e f v = f (e v) := rfl

/-- A vertex is a word with no repeated adjacent colors. Adding a color
cancels the first letter precisely when the two colors coincide. -/
abbrev TreeWord (α : Type*) := {w : List α // w.IsChain (· ≠ ·)}

namespace TreeWord

variable {α : Type*} [DecidableEq α]

def root : TreeWord α := ⟨[], by simp⟩

def stepList (a : α) : List α → List α
  | [] => [a]
  | b :: w => if a = b then w else a :: b :: w

theorem stepList_reduced (a : α) (w : List α) (hw : w.IsChain (· ≠ ·)) :
    (stepList a w).IsChain (· ≠ ·) := by
  cases w with
  | nil => simp [stepList]
  | cons b w =>
    by_cases hab : a = b
    · simpa [stepList, hab] using hw.tail
    · simpa [stepList, hab, List.isChain_cons_cons] using And.intro hab hw

def step (a : α) (w : TreeWord α) : TreeWord α :=
  ⟨stepList a w.val, stepList_reduced a w.val w.property⟩

theorem step_involutive (a : α) : Function.Involutive (step a) := by
  rintro ⟨w, hw⟩
  apply Subtype.ext
  change stepList a (stepList a w) = w
  cases w with
  | nil => simp [stepList]
  | cons b w =>
    by_cases hab : a = b
    · subst b
      cases w with
      | nil => simp [stepList]
      | cons c w =>
        have hac : a ≠ c := (List.isChain_cons_cons.mp hw).1
        simp [stepList, hac]
    · simp [stepList, hab]

def edgeEquiv (a : α) : TreeWord α ≃ TreeWord α :=
  (step_involutive a).toPerm

@[simp] theorem edgeEquiv_apply (a : α) (w : TreeWord α) :
    edgeEquiv a w = step a w := rfl

theorem edgeEquiv_symm (a : α) : (edgeEquiv a).symm = edgeEquiv a := rfl

end TreeWord

variable {α : Type*} [DecidableEq α]

noncomputable def treeEdge (a : α) : ℓ²(TreeWord α, ℂ) →L[ℂ] ℓ²(TreeWord α, ℂ) :=
  (l2Permutation (TreeWord.edgeEquiv a)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem treeEdge_apply (a : α) (f : ℓ²(TreeWord α, ℂ)) (v : TreeWord α) :
    treeEdge a f v = f (TreeWord.step a v) := rfl

theorem treeEdge_selfAdjoint (a : α) : IsSelfAdjoint (treeEdge a) := by
  change (treeEdge a).adjoint = treeEdge a
  rw [treeEdge, LinearIsometryEquiv.adjoint_eq_symm]
  ext f v
  rfl

theorem treeEdge_norm (a : α) (f : ℓ²(TreeWord α, ℂ)) : ‖treeEdge a f‖ = ‖f‖ :=
  (l2Permutation (TreeWord.edgeEquiv a)).norm_map f

/-- The adjacency operator of the edge-colored regular tree. In the
application the color set has p+1 elements, and normalization divides
this operator by sqrt p. -/
noncomputable def treeAdjacency [Fintype α] :
    ℓ²(TreeWord α, ℂ) →L[ℂ] ℓ²(TreeWord α, ℂ) := ∑ a : α, treeEdge a

theorem treeAdjacency_selfAdjoint [Fintype α] :
    IsSelfAdjoint (treeAdjacency (α := α)) := by
  unfold treeAdjacency
  exact isSelfAdjoint_sum Finset.univ (x := treeEdge (α := α))
    (fun a _ => treeEdge_selfAdjoint a)

theorem treeAdjacency_norm_le [Fintype α] :
    ‖treeAdjacency (α := α)‖ ≤ Fintype.card α := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖(∑ a : α, treeEdge a) f‖ ≤ _
  rw [sum_apply]
  calc
    ‖∑ a : α, treeEdge a f‖ ≤ ∑ a : α, ‖treeEdge a f‖ := norm_sum_le _ _
    _ = (Fintype.card α : ℝ) * ‖f‖ := by simp [treeEdge_norm]

theorem treeAdjacency_apply [Fintype α] (f : ℓ²(TreeWord α, ℂ)) (v : TreeWord α) :
    treeAdjacency f v = ∑ a : α, f (TreeWord.step a v) := by
  simp only [treeAdjacency, sum_apply, lp.coeFn_sum, Finset.sum_apply, treeEdge_apply]

theorem tree_radial_sum_root [Fintype α] (u : ℕ → ℂ) :
    (∑ a : α, u (TreeWord.step a TreeWord.root).val.length) =
      (Fintype.card α : ℂ) * u 1 := by
  simp [TreeWord.step, TreeWord.stepList, TreeWord.root]

theorem tree_radial_sum_cons [Fintype α] (u : ℕ → ℂ) (b : α) (w : List α)
    (hw : (b :: w).IsChain (· ≠ ·)) :
    (∑ a : α, u (TreeWord.step a ⟨b :: w, hw⟩).val.length) =
      u w.length + ((Fintype.card α - 1 : ℕ) : ℂ) * u (w.length + 2) := by
  have hpoint (a : α) : u (TreeWord.step a ⟨b :: w, hw⟩).val.length =
      if a = b then u w.length else u (w.length + 2) := by
    by_cases hab : a = b <;> simp [TreeWord.step, TreeWord.stepList, hab]
  simp_rw [hpoint]
  rw [Finset.sum_ite]
  have heq : Finset.univ.filter (fun a : α => a = b) = {b} := by
    ext a
    simp
  rw [heq]
  simp [Finset.filter_ne', Finset.card_erase_of_mem]

/-- Exact radial walk-count recurrence, including the distinct degree at
the root. The parameter d is the number of edge colors. -/
def treeWalkCount (d : ℕ) : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => d * treeWalkCount d n 1
  | n + 1, k + 1 => treeWalkCount d n k + (d - 1) * treeWalkCount d n (k + 2)

noncomputable def treeRootVector : ℓ²(TreeWord α, ℂ) :=
  lp.single 2 TreeWord.root 1

theorem treeRootVector_norm : ‖treeRootVector (α := α)‖ = 1 := by
  rw [treeRootVector, lp.norm_single (by norm_num)]
  norm_num

theorem treeAdjacency_power_root [Fintype α] (n : ℕ) (v : TreeWord α) :
    ((treeAdjacency (α := α)) ^ n) treeRootVector v =
      (treeWalkCount (Fintype.card α) n v.val.length : ℂ) := by
  induction n generalizing v with
  | zero =>
    rcases v with ⟨w, hw⟩
    cases w with
    | nil => simp [treeWalkCount, treeRootVector, TreeWord.root]
    | cons b w =>
      have hn : (⟨b :: w, hw⟩ : TreeWord α) ≠ TreeWord.root := by
        intro h
        have := congrArg Subtype.val h
        simp [TreeWord.root] at this
      simp [treeWalkCount, treeRootVector, Pi.single_eq_of_ne hn]
  | succ n ih =>
    rw [pow_succ']
    change treeAdjacency ((treeAdjacency ^ n) treeRootVector) v = _
    rw [treeAdjacency_apply]
    simp_rw [ih]
    rcases v with ⟨w, hw⟩
    cases w with
    | nil =>
      rw [show (⟨[], hw⟩ : TreeWord α) = TreeWord.root from rfl,
        tree_radial_sum_root (fun k => (treeWalkCount (Fintype.card α) n k : ℂ))]
      simp [treeWalkCount, TreeWord.root]
    | cons b w =>
      rw [tree_radial_sum_cons (fun k => (treeWalkCount (Fintype.card α) n k : ℂ)) b w hw]
      simp [treeWalkCount]

#print axioms l2Permutation
#print axioms TreeWord.step_involutive
#print axioms treeAdjacency_selfAdjoint
#print axioms treeAdjacency_norm_le
#print axioms treeAdjacency_power_root

end QuantitativeMaass
