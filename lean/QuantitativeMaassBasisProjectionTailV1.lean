module

public import QuantitativeMaassFiniteSpectralSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Set

namespace QuantitativeMaass

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An omitted basis vector is orthogonal to the whole selected span. -/
theorem hilbertBasis_omitted_inner_span (b : HilbertBasis ι ℂ H) (S : Set ι)
    (i : ι) (hi : i∉S) (x : H)
    (hx : x∈Submodule.span ℂ (Set.range (fun j : S => b j.val))) :
    inner ℂ (b i) x=0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    have hij : i≠j.val := by intro h; exact hi (h ▸ j.property)
    exact b.orthonormal.inner_eq_zero hij
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right,hx,hy,add_zero]
  | smul a x _ hx => rw [inner_smul_right,hx,mul_zero]

/-- Parseval for the actual orthogonal projection onto a selected basis
span. No assumption about the vector's spectral support is made. -/
theorem hilbertBasis_projection_tail (b : HilbertBasis ι ℂ H) (S : Set ι)
    [(Submodule.span ℂ (Set.range (fun j : S => b j.val))).HasOrthogonalProjection]
    (x : H) :
    ‖x-(Submodule.span ℂ (Set.range (fun j : S => b j.val))).starProjection x‖^2=
      ∑' i : {i // i∉S},‖inner ℂ (b i.val) x‖^2 := by
  classical
  let W := Submodule.span ℂ (Set.range (fun j : S => b j.val))
  let y := x-W.starProjection x
  have hzero (i : ι) (hi : i∈S) : inner ℂ (b i) y=0 := by
    apply inner_eq_zero_symm.mp
    exact W.starProjection_inner_eq_zero x (b i)
      (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩)
  have hout (i : {i // i∉S}) : inner ℂ (b i.val) y=inner ℂ (b i.val) x := by
    dsimp [y]
    rw [inner_sub_right,hilbertBasis_omitted_inner_span b S i.val i.property
      (W.starProjection x) (W.starProjection_apply_mem x),sub_zero]
  have hs : Function.support (fun i => ‖inner ℂ (b i) y‖^2)⊆Sᶜ := by
    intro i hi
    by_contra h
    have hmem : i∈S := by simpa using h
    exact hi (by simp [hzero i hmem])
  have hp : (∑' i,‖inner ℂ (b i) y‖^2)=‖y‖^2 := by
    simpa only [norm_inner_symm] using (hasSum_inner_norm_sq b y).tsum_eq
  change ‖y‖^2=_
  rw [←hp,←tsum_subtype_eq_of_support_subset hs]
  exact tsum_congr (fun i => by rw [hout i])

#print axioms hilbertBasis_omitted_inner_span
#print axioms hilbertBasis_projection_tail

end QuantitativeMaass
