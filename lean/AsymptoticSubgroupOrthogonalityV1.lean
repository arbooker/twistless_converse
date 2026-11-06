module

public import AsymptoticPolarSubgroupSupportV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSubgroupSupport

open AsymptoticRegularTrace AsymptoticOrbitBranch ContinuousLinearMap InnerProductSpace
open scoped lp InnerProduct

variable {G ι : Type*} [Group G]

noncomputable def translation (a : G) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  (reindex (Equiv.mulLeft a)).toContinuousLinearMap

theorem translation_apply (a : G) (v : ℓ²(G,ℂ)) (g : G) : translation a v g=v (a*g) := rfl

theorem translation_one (v : ℓ²(G,ℂ)) : translation (1:G) v=v := by
  apply lp.ext
  funext g
  simp only [translation_apply,one_mul]

/-- A translation outside the supporting subgroup makes two columns
orthogonal. The statement holds at every counting root. -/
theorem translated_columns_orthogonal (S : Subgroup G)
    (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hB : Supported S B) (hC : Supported S C)
    (a : G) (ha : a∉S) (h : G) :
    ⟪B (delta h),translation a (C (delta h))⟫_ℂ=0 := by
  rw [lp.inner_eq_tsum]
  suffices hz : ∀ g,⟪B (delta h) g,translation a (C (delta h)) g⟫_ℂ=0 by
    simp only [hz,tsum_zero]
  intro g
  by_cases hg : g*h⁻¹∈S
  · have hag : (a*g)*h⁻¹∉S := by
      intro hh
      have he := S.mul_mem hh (S.inv_mem hg)
      exact ha (by simpa [mul_assoc] using he)
    have hc : translation a (C (delta h)) g=0 := hC (a*g) h hag
    rw [hc,inner_zero_right]
  · have hb : B (delta h) g=0 := hB g h hg
    rw [hb,inner_zero_left]

/-- The rooted cross coefficient vanishes, including arbitrary infinite
columns of the original bounded operators. -/
theorem translated_cross_root_zero (S : Subgroup G)
    (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hB : Supported S B) (hC : Supported S C)
    (a : G) (ha : a∉S) (h : G) :
    matrix (B.adjoint.comp ((translation a).comp C)) h h=0 := by
  rw [matrix_cross]
  exact translated_columns_orthogonal S B C hB hC a ha h

/-- In the fresh-prime mixing matrix, subgroup separation removes all
off-diagonal translated terms. The diagonal is exactly the original
sum of column energies, independently of the number of nonzero entries. -/
theorem translated_root_energy [Fintype ι] (S : Subgroup G)
    (V : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hV : ∀ i,Supported S (V i))
    (a : ι → ι → G) (hdiag : ∀ i,a i i=1) (hoff : ∀ i j,i≠j → a i j∉S) (h : G) :
    (∑ i,∑ j,⟪V i (delta h),translation (a i j) (V j (delta h))⟫_ℂ)=
      ∑ i,((‖V i (delta h)‖^2:ℝ):ℂ) := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [hdiag,translation_one,inner_self_eq_norm_sq_to_K]
    exact (Complex.ofReal_pow _ _).symm
  · intro j hj hji
    exact translated_columns_orthogonal S (V i) (V j) (hV i) (hV j) (a i j) (hoff i j hji.symm) h
  · simp

#print axioms translation_apply
#print axioms translation_one
#print axioms translated_columns_orthogonal
#print axioms translated_cross_root_zero
#print axioms translated_root_energy

end AsymptoticSubgroupSupport
