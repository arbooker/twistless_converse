module

public import AsymptoticIntegralSubgroupV1
public import AsymptoticRegularBranchFamilyV1
public import AsymptoticStackSubgroupSupportV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSubgroupSupport

open AsymptoticRegularTrace ContinuousLinearMap
open scoped lp

variable {G α ι : Type*} [Group G]

theorem supported_finsetSum (S : Subgroup G) (s : Finset ι)
    (B : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hB : ∀ i∈s,Supported S (B i)) :
    Supported S (∑ i∈s,B i) := by
  intro g h hh
  change matrixCLM g h (∑ i∈s,B i)=0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hB i hi g h hh)

theorem supported_diagonal (S : Subgroup G) (c : G → ℂ) {C : ℝ} (hC : 0≤C)
    (hc : ∀ g,‖c g‖≤C) : Supported S (AsymptoticOrbitDiagonal.operator c hC hc) := by
  intro g h hh
  rw [AsymptoticOrbitDiagonal.operator_matrix]
  have hne : g≠h := by
    intro he
    apply hh
    rw [he,mul_inv_cancel]
    exact S.one_mem
  simp only [hne,ite_false]

variable [MulAction G α]

theorem supported_weighted_branch (S : Subgroup G) (a : G) (ha : a∈S) (c : α → ℂ)
    {C : ℝ} (hC : 0≤C) (hc : ∀ x,‖c x‖≤C) (x : α) :
    Supported S (AsymptoticOrbitBranch.operator a c hC hc x) := by
  intro g h hh
  rw [AsymptoticOrbitBranch.operator_matrix]
  have hne : a*g≠h := by
    intro he
    apply hh
    rw [← he]
    simpa [mul_assoc] using S.inv_mem ha
  simp only [hne,ite_false]

theorem supported_corner (S : Subgroup G) (s : Set α) (x : α) :
    Supported S (AsymptoticOrbitDiagonal.corner s x) :=
  supported_diagonal S _ _ _

#print axioms supported_finsetSum
#print axioms supported_diagonal
#print axioms supported_weighted_branch
#print axioms supported_corner

end AsymptoticSubgroupSupport

namespace AsymptoticIntegralSubgroup

open AsymptoticSubgroupSupport AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch AsymptoticRegularBranchFamily UpperHalfPlane
open AsymptoticCompactBranch (Data)

variable (q : ℕ) [Fact q.Prime]

theorem compactFold_mem (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    (hi : g∈integralGL q) (n : ℤ) : compactFold g hg n∈integralGroup q := by
  apply ofMatrix_mem
  exact (integralGL q).mul_mem (translation_integer_integral q (-n)) hi

/-- The actual compact folded counting branch is q-integral when its
rational matrix is. Integer folds and the strip projection preserve
integrality. -/
theorem compact_operator_supported (g : GL (Fin 2) ℚ) (hg : 0<(realMatrix g).det.val)
    (hi : g∈integralGL q) {s : Set ℍ} {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (D : Data (realMatrix g) s ε t) (x : ℍ) :
    Supported (integralGroup q) (AsymptoticRegularCompactBranch.operator g hg hε t D x) := by
  apply supported_comp
  · exact supported_finsetSum _ _ _ (fun n _ =>
      supported_weighted_branch _ _ (compactFold_mem q g hg hi n) _ _ _ x)
  · exact supported_corner _ _ _

theorem compact_family_supported {ι : Type*} [Fintype ι] (b : ι → Branch) (c : ι → ℂ)
    (hi : ∀ i,(b i).matrix∈integralGL q) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    Supported (integralGroup q) (family b c hs hε t x) := by
  apply supported_sum
  intro i
  exact supported_smul _ _
    (compact_operator_supported q (b i).matrix (b i).positive (hi i) hε t _ x) (c i)

#print axioms compactFold_mem
#print axioms compact_operator_supported
#print axioms compact_family_supported

end AsymptoticIntegralSubgroup
