module

public import AsymptoticOrbitBranchV1
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped lp ComplexConjugate

variable {G α ι : Type*} [Group G]

noncomputable def matrixCLM (g h : G) : (ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : G => ℂ) 2 g).comp (ContinuousLinearMap.apply ℂ ℓ²(G,ℂ) (delta h))

omit [Group G] in
theorem matrixCLM_apply (g h : G) (B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    matrixCLM g h B=matrix B g h := rfl

omit [Group G] in
theorem matrix_comp (B C : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (g h : G) :
    matrix (B.comp C) g h=∑' i,matrix B g i*matrix C i h := by
  rw [matrix,← delta_inner,comp_apply,← adjoint_inner_left,lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [RCLike.inner_apply]
  change matrix C i h*conj (matrix B.adjoint i g)=_
  rw [matrix_adjoint]
  simp only [starRingEnd_apply,star_star]
  ring

omit [Group G] in
theorem matrix_tsum (B : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hB : Summable B) (g h : G) :
    matrix (∑' i,B i) g h=∑' i,matrix (B i) g h :=
  (matrixCLM g h).map_tsum hB

omit [Group G] in
theorem tsum_apply_coordinate (B : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hB : Summable B)
    (f : ℓ²(G,ℂ)) (g : G) : (∑' i,B i) f g=∑' i,B i f g :=
  ((lp.evalCLM ℂ (fun _ : G => ℂ) 2 g).comp (ContinuousLinearMap.apply ℂ ℓ²(G,ℂ) f)).map_tsum hB

variable [MulAction G α]

theorem covariant_comp (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Covariant B) (hC : Covariant C) : Covariant (fun x => (B x).comp (C x)) := by
  intro x a g h
  simp only [matrix_comp,hB x a,hC x a]
  exact (Equiv.mulRight a).tsum_eq (fun i => matrix (B x) (g*a) i*matrix (C x) i (h*a))

theorem covariant_tsum (B : ι → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hs : ∀ x,Summable (fun i => B i x)) (hc : ∀ i,Covariant (B i)) :
    Covariant (fun x => ∑' i,B i x) := by
  intro x a g h
  rw [matrix_tsum _ (hs (a • x)),matrix_tsum _ (hs x)]
  exact tsum_congr (fun i => hc i x a g h)

theorem covariant_finsetSum (s : Finset ι) (B : ι → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hc : ∀ i∈s,Covariant (B i)) : Covariant (fun x => ∑ i∈s,B i x) := by
  intro x a g h
  change matrixCLM g h (∑ i∈s,B i (a • x))=matrixCLM (g*a) (h*a) (∑ i∈s,B i x)
  rw [map_sum,map_sum]
  exact Finset.sum_congr rfl (fun i hi => hc i hi x a g h)

theorem covariant_smul (c : ℂ) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hc : Covariant B) : Covariant (fun x => c • B x) := by
  intro x a g h
  change matrixCLM g h (c • B (a • x))=matrixCLM (g*a) (h*a) (c • B x)
  rw [map_smul,map_smul]
  exact congrArg (fun z : ℂ => c • z) (hc x a g h)

theorem covariant_add (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : Covariant B) (hC : Covariant C) : Covariant (fun x => B x+C x) := by
  intro x a g h
  change matrixCLM g h (B (a • x)+C (a • x))=matrixCLM (g*a) (h*a) (B x+C x)
  rw [map_add,map_add]
  exact congrArg₂ (·+·) (hB x a g h) (hC x a g h)

theorem covariant_one : Covariant (fun _ : α => (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))) := by
  classical
  intro x a g h
  simp [matrix,delta,Pi.single_apply]

theorem covariant_pow (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hB : Covariant B) (n : ℕ) :
    Covariant (fun x => B x^n) := by
  induction n with
  | zero => simpa only [pow_zero] using (covariant_one (G:=G) (α:=α))
  | succ n ih =>
    simp only [pow_succ]
    exact covariant_comp _ _ ih hB

variable [MeasurableSpace α]

omit [Group G] [MulAction G α] in
theorem matrix_comp_measurable [Countable G]
    (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hC : ∀ g h,Measurable (fun x => matrix (C x) g h)) (g h : G) :
    Measurable (fun x => matrix ((B x).comp (C x)) g h) := by
  simp only [matrix_comp]
  exact Measurable.tsum (fun i => (hB g i).mul (hC i h))

omit [Group G] [MulAction G α] in
theorem matrix_tsum_measurable [Countable ι]
    (B : ι → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hs : ∀ x,Summable (fun i => B i x))
    (hB : ∀ i g h,Measurable (fun x => matrix (B i x) g h)) (g h : G) :
    Measurable (fun x => matrix (∑' i,B i x) g h) := by
  simp only [matrix_tsum _ (hs _)]
  exact Measurable.tsum (fun i => hB i g h)

omit [Group G] [MulAction G α] in
theorem matrix_finsetSum_measurable (s : Finset ι)
    (B : ι → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ i∈s,∀ g h,Measurable (fun x => matrix (B i x) g h)) (g h : G) :
    Measurable (fun x => matrix (∑ i∈s,B i x) g h) := by
  have he (x : α) : matrix (∑ i∈s,B i x) g h=∑ i∈s,matrix (B i x) g h :=
    map_sum (matrixCLM g h) _ _
  simp only [he]
  exact Finset.measurable_sum s (fun i hi => hB i hi g h)

omit [Group G] [MulAction G α] in
theorem matrix_smul_measurable (c : ℂ) (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h)) (g h : G) :
    Measurable (fun x => matrix (c • B x) g h) := by
  have he (x : α) : matrix (c • B x) g h=c*matrix (B x) g h :=
    (matrixCLM g h).map_smul c (B x)
  simp only [he]
  exact measurable_const.mul (hB g h)

omit [Group G] [MulAction G α] in
theorem matrix_pow_measurable [Countable G]
    (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h)) (n : ℕ) (g h : G) :
    Measurable (fun x => matrix (B x^n) g h) := by
  induction n generalizing g h with
  | zero => simpa only [pow_zero] using (measurable_const : Measurable (fun _ : α => matrix 1 g h))
  | succ n ih =>
    simp only [pow_succ]
    exact matrix_comp_measurable _ _ ih hB g h

omit [Group G] [MulAction G α] in
theorem matrix_add_measurable (B C : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hC : ∀ g h,Measurable (fun x => matrix (C x) g h)) (g h : G) :
    Measurable (fun x => matrix (B x+C x) g h) := by
  have he (x : α) : matrix (B x+C x) g h=matrix (B x) g h+matrix (C x) g h :=
    map_add (matrixCLM g h) (B x) (C x)
  simp only [he]
  exact (hB g h).add (hC g h)

#print axioms matrix_comp
#print axioms covariant_comp
#print axioms covariant_tsum
#print axioms matrix_comp_measurable
#print axioms matrix_tsum_measurable

end AsymptoticRegularTrace
