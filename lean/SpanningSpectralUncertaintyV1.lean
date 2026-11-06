module

public import SpanningVandermondeV1
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace SpanningSpectralUncertainty

open SpanningVandermonde

variable {K I : Type*} [Field K] [Fintype I]

/-- A vector with L consecutive zero moments cannot have a nonzero
polynomial annihilator of degree <=L in any injective spectral labelling.
The two labellings may differ, as for different generators of a cyclic
shift group. Their relation to literal cyclic shifts is a later bridge. -/
theorem no_small_polynomial_annihilator {z w a : I → K}
    (hz : Function.Injective z) (hz0 : ∀i,z i≠0) (hw : Function.Injective w)
    {L : ℕ} (s : ℕ) (ha : a≠0)
    (hmom : ∀j:ℕ,j<L → ∑i:I,a i*z i^(s+j)=0)
    (p : Polynomial K) (hdeg : p.natDegree≤L)
    (hann : ∀i,a i*p.eval (w i)=0) : p=0 := by
  classical
  by_contra hp
  let S := Finset.univ.filter (fun i:I => p.eval (w i)=0)
  have hroot : ∀i:S,p.eval (w i.val)=0 := fun i => (Finset.mem_filter.mp i.property).2
  have hcard : S.card≤p.natDegree := by
    by_contra! hc
    apply hp
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (hw.comp (Subtype.val_injective (p:=fun i => i∈S))) hroot
    simpa only [Fintype.card_coe] using hc
  have hsupp : ∀i,i∉S → a i=0 := by
    intro i hi
    have hwi : p.eval (w i)≠0 := by simpa [S] using hi
    exact (mul_eq_zero.mp (hann i)).resolve_right hwi
  exact ha (sparse_moments_zero hz hz0 S (hcard.trans hdeg) hsupp s hmom)

#print axioms no_small_polynomial_annihilator

end SpanningSpectralUncertainty
