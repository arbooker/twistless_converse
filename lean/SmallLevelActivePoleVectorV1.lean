module
public import SmallLevelPoleGridTheoryV4
public import QuantitativeArithmeticUniversalPoleVectorV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelActivePoleVector
open Complex Filter QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- Multiplication by the weight factor precisely removes the permitted
simple pole, and no other pole. -/
theorem weighted_order_nonneg_iff (g : ℂ→ℂ) (k x : ℂ) (hg : MeromorphicAt g x) :
    0≤meromorphicOrderAt (fun z => (z-k)*g z) x ↔
      0≤meromorphicOrderAt g x ∨ (x=k ∧ (-1:WithTop ℤ)≤meromorphicOrderAt g x) := by
  have hc : AnalyticAt ℂ (fun z : ℂ => z-k) x := analyticAt_id.sub analyticAt_const
  change 0≤meromorphicOrderAt ((fun z : ℂ => z-k)*g) x ↔ _
  rw [meromorphicOrderAt_mul hc.meromorphicAt hg]
  by_cases hx : x=k
  · subst k
    rw [meromorphicOrderAt_id_sub_const]
    cases ho : meromorphicOrderAt g x with
    | top => simp
    | coe n =>
      norm_cast
      rw [←WithTop.coe_one,←WithTop.LinearOrderedAddCommGroup.coe_neg,WithTop.coe_le_coe]
      simp only [true_and]
      omega
  · have hc0 : meromorphicOrderAt (fun z : ℂ => z-k) x=0 :=
      (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hc.meromorphicAt).mp
        ⟨x-k,sub_ne_zero.mpr hx,hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
    simp only [hc0,zero_add,hx,false_and,or_false]

/-- Select one rightmost active point and one common pole vector. Higher
poles at the weight are included; a simple pole there is harmless. -/
theorem exists_rightmost_active_vector {ι : Type*} [Fintype ι]
    (G : ℂ→ι→ℂ) (k x : ℂ) (hx : x≠k)
    (hG : ∀ i z,MeromorphicAt (fun s => G s i) z)
    (hpole : ∃ i,meromorphicOrderAt (fun z => G z i) x<0)
    (B : ℝ) (hhalf : ∀ i z,B<z.re → AnalyticAt ℂ (fun s => G s i) z) :
    ∃ n : ℕ,∃ v : ι→ℂ,
      IsLeadingVector (fun z j => (z-k)*G z j) (x+n) v ∧
      ∀ a : ℕ,0<a → ∀ j,
        0≤meromorphicOrderAt (fun z => G z j) (x+n+a) ∨
        (x+n+a=k ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) (x+n+a)) := by
  have hp : ∃ i,meromorphicOrderAt (fun z => (z-k)*G z i) x<0 := by
    obtain ⟨i,hi⟩:=hpole
    refine ⟨i,lt_of_not_ge ?_⟩
    intro hn
    have hh:=(weighted_order_nonneg_iff (fun z => G z i) k x (hG i x)).mp hn
    exact (not_le_of_gt hi) (by simpa only [hx,false_and,or_false] using hh)
  obtain ⟨n,hn,hs⟩:=SmallLevelPoleGrid.rightmost_pole
    (fun i z => (z-k)*G z i) hp B
    (fun i z hz => (analyticAt_id.sub analyticAt_const).mul (hhalf i z hz))
  obtain ⟨v,hv⟩:=exists_leading_vector (fun z i => (z-k)*G z i) (x+n)
    (fun i => ((analyticAt_id.sub analyticAt_const).meromorphicAt).mul (hG i (x+n))) hn
  refine ⟨n,v,hv,?_⟩
  intro a ha j
  exact (weighted_order_nonneg_iff (fun z => G z j) k (x+n+a) (hG j _)).mp (hs a ha j)

#print axioms weighted_order_nonneg_iff
#print axioms exists_rightmost_active_vector
end SmallLevelActivePoleVector
