module

public import SpanningCoordinateDefectsV1
public import SpanningKernelDifferencesV1

@[expose] public section

namespace SpanningFineDefects

open SpanningKernelDefects SpanningKernelDifferences SpanningActualKernel
  SpanningTraceAlgebra SpanningLinearKernels

variable {K : Type} [Field K]

theorem mem_coordinateDefects {N Q P j : ℕ} {L : Set ℕ} :
    j∈coordinateDefects (K:=K) N L Q P ↔ j<Q ∧
      ∃f:ℤ → K,Augmented N L Q f ∧ f j≠f (j+P:ℕ) := by
  classical
  simp only [coordinateDefects,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hj,f,hf⟩
    exact ⟨hj,f.val,f.property,hf⟩
  · rintro ⟨hj,f,hf,hd⟩
    exact ⟨hj,⟨f,hf⟩,hd⟩

theorem restriction_defect {N Q r P n : ℕ} {L : Set ℕ} (hr : 0<r)
    (hdiv : ∀ell∈L,ell∣Q) {f : ℤ → K} (hf : Augmented N L (r*Q) f)
    (hn : n<r*Q) (hd : difference (r*P) f n≠0) :
    n/r∈coordinateDefects (K:=K) N L Q P := by
  apply mem_coordinateDefects.mpr
  have hj : n/r<Q := (Nat.div_lt_iff_lt_mul hr).mpr (by nlinarith [hn])
  let g := restrict r (n%r) f
  refine ⟨hj,g,augmented_restrict hdiv hf (Nat.mod_lt n hr),?_⟩
  intro he
  have hdecomp := Nat.div_add_mod n r
  have he1 : g (n/r:ℕ)=f n := by
    dsimp [g,restrict]
    congr 1
    exact_mod_cast hdecomp
  have he2 : g (n/r+P:ℕ)=f (n+r*P:ℕ) := by
    dsimp [g,restrict]
    congr 1
    have hh : (r:ℤ)*(n/r:ℕ)+(n%r:ℕ)=n := by exact_mod_cast hdecomp
    nlinarith
  rw [he1,he2] at he
  apply hd
  unfold difference
  push_cast at he
  exact sub_eq_zero.mpr he.symm

theorem normalized_quotient_error {r Q : ℕ} (hr : 0<r) (hQ : 0<Q) (n : ℕ) :
    |(n:ℝ)/((r:ℝ)*Q)-((n/r:ℕ):ℝ)/Q|<(1:ℝ)/Q := by
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have he : (r:ℝ)*((n/r:ℕ):ℝ)+((n%r:ℕ):ℝ)=n := by exact_mod_cast Nat.div_add_mod n r
  have hm : ((n%r:ℕ):ℝ)<r := by exact_mod_cast Nat.mod_lt n hr
  have heq : (n:ℝ)/((r:ℝ)*Q)-((n/r:ℕ):ℝ)/Q=((n%r:ℕ):ℝ)/((r:ℝ)*Q) := by
    apply (eq_div_iff (ne_of_gt (mul_pos hr' hQ'))).mpr
    field_simp
    nlinarith [he]
  rw [heq,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (mul_pos hr' hQ').le)]
  apply (div_lt_div_iff₀ (mul_pos hr' hQ') hQ').mpr
  nlinarith

theorem fine_defects_near {N Q r P : ℕ} {L : Set ℕ} (hr : 0<r) (hQ : 0<Q)
    (hdiv : ∀ell∈L,ell∣Q) {E : Finset ℚ} {ε : ℝ}
    (hconc : ∀j∈coordinateDefects (K:=K) N L Q P,∃x∈E,|(j:ℝ)/(Q:ℝ)-(x:ℝ)|<ε)
    {f : ℤ → K} (hf : Augmented N L (r*Q) f) (n : Fin (r*Q))
    (hd : difference (r*P) f n.val≠0) :
    ∃x∈E,|(n.val:ℝ)/((r:ℝ)*Q)-(x:ℝ)|<ε+(1:ℝ)/Q := by
  obtain ⟨x,hx,hnear⟩ := hconc _ (restriction_defect hr hdiv hf n.isLt hd)
  refine ⟨x,hx,?_⟩
  have htriangle := abs_sub_le ((n.val:ℝ)/((r:ℝ)*Q)) (((n.val/r:ℕ):ℝ)/Q) (x:ℝ)
  have he := normalized_quotient_error hr hQ n.val
  linarith

#print axioms fine_defects_near

end SpanningFineDefects
