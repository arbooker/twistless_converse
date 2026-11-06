module

public import Mathlib.Analysis.Analytic.Order
public import SmallLevelContinuationTheoryV4
public import SmallLevelSimplePoleCancellationV1

/-! Consolidated chapter: QuantitativeArithmeticAnalyticGerm. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticAnalyticGermFirstShiftV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex Filter Set
open scoped Topology

/-- An analytic representative of a punctured germ; no assertion about an
arbitrarily assigned value at the puncture is built into this definition. -/
def HasAnalyticGerm (F : ℂ → ℂ) (x : ℂ) : Prop :=
  ∃ H : ℂ → ℂ, AnalyticAt ℂ H x ∧ F=ᶠ[𝓝[≠] x] H

theorem HasAnalyticGerm.of_analytic {F : ℂ → ℂ} {x : ℂ} (h : AnalyticAt ℂ F x) :
    HasAnalyticGerm F x := ⟨F,h,Filter.EventuallyEq.rfl⟩

theorem HasAnalyticGerm.congr {F G : ℂ → ℂ} {x : ℂ}
    (h : HasAnalyticGerm F x) (he : F=ᶠ[𝓝[≠] x] G) : HasAnalyticGerm G x := by
  obtain ⟨H,hH,hFH⟩ := h
  exact ⟨H,hH,he.symm.trans hFH⟩

theorem HasAnalyticGerm.add {F G : ℂ → ℂ} {x : ℂ}
    (hF : HasAnalyticGerm F x) (hG : HasAnalyticGerm G x) :
    HasAnalyticGerm (fun z => F z+G z) x := by
  obtain ⟨A,hA,heA⟩ := hF
  obtain ⟨B,hB,heB⟩ := hG
  exact ⟨fun z => A z+B z,hA.add hB,heA.add heB⟩

theorem HasAnalyticGerm.sub {F G : ℂ → ℂ} {x : ℂ}
    (hF : HasAnalyticGerm F x) (hG : HasAnalyticGerm G x) :
    HasAnalyticGerm (fun z => F z-G z) x := by
  obtain ⟨A,hA,heA⟩ := hF
  obtain ⟨B,hB,heB⟩ := hG
  exact ⟨fun z => A z-B z,hA.sub hB,heA.sub heB⟩

theorem HasAnalyticGerm.mul_analytic {F C : ℂ → ℂ} {x : ℂ}
    (hF : HasAnalyticGerm F x) (hC : AnalyticAt ℂ C x) :
    HasAnalyticGerm (fun z => C z*F z) x := by
  obtain ⟨H,hH,he⟩ := hF
  exact ⟨fun z => C z*H z,hC.mul hH,Filter.EventuallyEq.rfl.mul he⟩

theorem HasAnalyticGerm.shift {F : ℂ → ℂ} {x d : ℂ}
    (h : HasAnalyticGerm F (x+d)) : HasAnalyticGerm (fun z => F (z+d)) x := by
  obtain ⟨H,hH,he⟩ := h
  have ht : Tendsto (fun z : ℂ => z+d) (𝓝[≠] x) (𝓝[≠] (x+d)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.add continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,add_left_inj] using hz
  exact ⟨fun z => H (z+d),hH.comp (f:=fun z : ℂ => z+d)
    (analyticAt_id.add analyticAt_const),he.comp_tendsto ht⟩

/-- Isolate the first positive Taylor shift at one point. All higher shifts
are absorbed in a genuine analytic germ, regardless of the pole order of
the unshifted source A. -/
theorem first_shift (B : ℝ) (A F : ℂ → ℂ) (C H : ℕ → ℂ → ℂ) (x : ℂ)
    (hC : ∀ n, AnalyticAt ℂ (C n) x)
    (hH : ∀ (n : ℕ) z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (H n) z)
    (hshift : ∀ j : ℕ, 2≤j → AnalyticAt ℂ F (x+j))
    (hrow : ∀ n : ℕ, B-((n:ℝ)+1)<x.re →
      A=ᶠ[𝓝[≠] x] (fun z => H n z+∑ a∈Finset.range n, C a z*F (z+((a:ℂ)+1)))) :
    HasAnalyticGerm (fun z => A z-C 0 z*F (z+1)) x := by
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-(((n+1:ℕ):ℝ)+1)<x.re := by push_cast; linarith
  let R : ℂ → ℂ := fun z => H (n+1) z+
    ∑ a∈Finset.range n, C (a+1) z*F (z+(((a+1:ℕ):ℂ)+1))
  refine ⟨R,?_,?_⟩
  · apply (hH (n+1) x hx).add
    apply Finset.analyticAt_fun_sum
    intro a _
    have hs : AnalyticAt ℂ F (x+(((a+1:ℕ):ℂ)+1)) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1+1) (by omega)
    exact (hC (a+1)).mul (hs.comp (f:=fun z : ℂ => z+(((a+1:ℕ):ℂ)+1))
      (analyticAt_id.add analyticAt_const))
  · filter_upwards [hrow (n+1) hx] with z hz
    rw [Finset.sum_range_succ'] at hz
    simp only [Nat.cast_zero,zero_add] at hz
    dsimp only [R]
    linear_combination hz

#print axioms HasAnalyticGerm.shift
#print axioms first_shift
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticAnalyticGermRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex Filter Set
open scoped Topology

/-- Analytic punctured germs have nonnegative meromorphic order. -/
theorem HasAnalyticGerm.order_nonneg {F : ℂ → ℂ} {x : ℂ}
    (h : HasAnalyticGerm F x) : 0≤meromorphicOrderAt F x := by
  obtain ⟨H,hH,he⟩ := h
  rw [meromorphicOrderAt_congr he]
  exact hH.meromorphicOrderAt_nonneg

theorem HasAnalyticGerm.analyticAt {F : ℂ → ℂ} {x : ℂ}
    (h : HasAnalyticGerm F x) (hF : MeromorphicNFAt F x) : AnalyticAt ℂ F x :=
  hF.meromorphicOrderAt_nonneg_iff_analyticAt.mp h.order_nonneg

/-- Exact analytic row operations act on all Laurent coefficients. -/
theorem HasAnalyticGerm.combine {F G C D : ℂ → ℂ} {x : ℂ}
    (hF : HasAnalyticGerm F x) (hG : HasAnalyticGerm G x)
    (hC : AnalyticAt ℂ C x) (hD : AnalyticAt ℂ D x) :
    HasAnalyticGerm (fun z => C z*F z+D z*G z) x :=
  (hF.mul_analytic hC).add (hG.mul_analytic hD)

/-- When every positive translate is regular, the complete leading Taylor
row is an analytic germ, not only an equation on a maximal Laurent vector. -/
theorem leading_taylor_germ {ι : Type*} [Fintype ι]
    (G : ℂ → ι → ℂ) (x : ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun s => G s j) z)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (B : ℝ) (A : ℂ → ι → ℂ) (C : ℕ → ℂ → ι → ℂ) (H : ℕ → ℂ → ℂ)
    (hC : ∀ n j, AnalyticAt ℂ (fun z => C n z j) x)
    (hH : ∀ n : ℕ, B-((n:ℝ)+1)<x.re → AnalyticAt ℂ (H n) x)
    (hrow : ∀ n : ℕ, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j, A z j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z+∑ a∈Finset.range n, ∑ j, C a z j*G (z+((a:ℂ)+1)) j)) :
    HasAnalyticGerm (fun z => ∑ j, A z j*G z j) x := by
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  refine ⟨_,?_,hrow n hx⟩
  apply (hH n hx).add
  apply Finset.analyticAt_fun_sum
  intro a _
  apply Finset.analyticAt_fun_sum
  intro j _
  have hs : AnalyticAt ℂ (fun z => G z j) (x+((a:ℂ)+1)) := by
    apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1) (by omega) j
  exact (hC a j).mul (hs.comp (f:=fun z : ℂ => z+((a:ℂ)+1))
    (analyticAt_id.add analyticAt_const))

#print axioms HasAnalyticGerm.order_nonneg
#print axioms HasAnalyticGerm.analyticAt
#print axioms HasAnalyticGerm.combine
#print axioms leading_taylor_germ
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticAnalyticGermFiniteSumV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex Filter Set
open scoped Topology

theorem HasAnalyticGerm.sum {ι : Type*} [Fintype ι] (F : ι → ℂ → ℂ) (x : ℂ)
    (h : ∀ i, HasAnalyticGerm (F i) x) :
    HasAnalyticGerm (fun z => ∑ i, F i z) x := by
  choose H hH he using h
  refine ⟨fun z => ∑ i, H i z,?_,?_⟩
  · apply Finset.analyticAt_fun_sum
    intro i _
    exact hH i
  · filter_upwards [Filter.eventually_all.mpr he] with z hz
    exact Finset.sum_congr rfl (fun i _ => hz i)

#print axioms HasAnalyticGerm.sum
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticAnalyticGermOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex Filter Set
open scoped Topology

/-- An analytic error and an analytic unit preserve any nonpositive lower
bound on meromorphic order. No normal-form assumption is needed. -/
theorem order_lower_of_unit_relation {F G C : ℂ → ℂ} {x : ℂ} {b : WithTop ℤ}
    (hF : MeromorphicAt F x) (hC : AnalyticAt ℂ C x) (hC0 : C x≠0)
    (hrel : HasAnalyticGerm (fun z => F z-C z*G z) x)
    (hb : b≤0) (hbound : b≤meromorphicOrderAt F x) :
    b≤meromorphicOrderAt G x := by
  obtain ⟨H,hH,he⟩ := hrel
  have heq : (C*G)=ᶠ[𝓝[≠] x] (F+(-H)) := by
    filter_upwards [he] with z hz
    change C z*G z=F z+-H z
    linear_combination -hz
  rw [←meromorphicOrderAt_mul_of_ne_zero hC hC0,meromorphicOrderAt_congr heq]
  exact (le_min hbound (hb.trans hH.neg.meromorphicOrderAt_nonneg)).trans
    (meromorphicOrderAt_add hF hH.neg.meromorphicAt)

#print axioms order_lower_of_unit_relation
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticAnalyticGermOrderBoundsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex Filter Set
open scoped Topology

theorem analytic_multiplier_order_lower {C G : ℂ → ℂ} {x : ℂ} {b : WithTop ℤ}
    (hC : AnalyticAt ℂ C x) (hG : MeromorphicAt G x)
    (hb : b≤meromorphicOrderAt G x) :
    b≤meromorphicOrderAt (fun z => C z*G z) x := by
  change b≤meromorphicOrderAt (C*G) x
  rw [meromorphicOrderAt_mul hC.meromorphicAt hG]
  exact hb.trans (le_add_of_nonneg_left hC.meromorphicOrderAt_nonneg)

/-- Dividing by an analytic coefficient of zero multiplicity at most n
can worsen a pole-order bound by at most n. -/
theorem order_lower_of_analytic_factor {C G : ℂ → ℂ} {x : ℂ}
    (b : ℤ) (n : ℕ) (hC : AnalyticAt ℂ C x) (hG : MeromorphicAt G x)
    (hCn : analyticOrderAt C x≤n)
    (hb : (b:WithTop ℤ)≤meromorphicOrderAt (fun z => C z*G z) x) :
    ((b-(n:ℤ):ℤ):WithTop ℤ)≤meromorphicOrderAt G x := by
  have hfinite : analyticOrderAt C x≠⊤ := by
    intro htop
    rw [htop] at hCn
    exact (not_le_of_gt (ENat.natCast_lt_top n)) hCn
  obtain ⟨r,hr⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hrn : r≤n := by exact_mod_cast (hr ▸ hCn)
  change (b:WithTop ℤ)≤meromorphicOrderAt (C*G) x at hb
  rw [meromorphicOrderAt_mul hC.meromorphicAt hG,hC.meromorphicOrderAt_eq,←hr] at hb
  simp only [ENat.map_natCast] at hb
  cases he : meromorphicOrderAt G x with
  | top => exact le_top
  | coe t =>
    rw [he] at hb
    have hi : b≤(r:ℤ)+t := by exact_mod_cast hb
    exact WithTop.coe_le_coe.mpr (by omega)

/-- In an analytic two-coordinate row, the second term has no worse
pole order than the first coordinate, up to analytic coefficients. -/
theorem two_row_order_lower {A C F G : ℂ → ℂ} {x : ℂ} {b : WithTop ℤ}
    (hA : AnalyticAt ℂ A x) (hF : MeromorphicAt F x)
    (hrow : HasAnalyticGerm (fun z => A z*F z+C z*G z) x)
    (hb0 : b≤0) (hb : b≤meromorphicOrderAt F x) :
    b≤meromorphicOrderAt (fun z => C z*G z) x := by
  have hrel : HasAnalyticGerm (fun z => (-A z)*F z-1*(C z*G z)) x := by
    apply (hrow.mul_analytic (C:=fun _ => (-1:ℂ)) analyticAt_const).congr
    exact Filter.Eventually.of_forall (fun z => by ring)
  exact order_lower_of_unit_relation (hA.neg.meromorphicAt.mul hF)
    (C:=fun _ => (1:ℂ)) analyticAt_const (by norm_num) hrel hb0
    (analytic_multiplier_order_lower hA.neg hF hb)

#print axioms analytic_multiplier_order_lower
#print axioms order_lower_of_analytic_factor
#print axioms two_row_order_lower
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticAnalyticGermFourRowV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex Filter Set
open scoped Topology

theorem order_lower_add {F G : ℂ → ℂ} {x : ℂ} {b : WithTop ℤ}
    (hF : MeromorphicAt F x) (hG : MeromorphicAt G x)
    (hbF : b≤meromorphicOrderAt F x) (hbG : b≤meromorphicOrderAt G x) :
    b≤meromorphicOrderAt (fun z => F z+G z) x :=
  (le_min hbF hbG).trans (meromorphicOrderAt_add hF hG)

/-- A four-coordinate row with an analytic unit in its first coordinate
transfers a common nonpositive pole-order bound from the other three. -/
theorem four_row_order_lower {C D E J F G H I : ℂ → ℂ} {x : ℂ} {b : WithTop ℤ}
    (hC : AnalyticAt ℂ C x) (hD : AnalyticAt ℂ D x)
    (hE : AnalyticAt ℂ E x) (hJ : AnalyticAt ℂ J x) (hC0 : C x≠0)
    (hG : MeromorphicAt G x) (hH : MeromorphicAt H x) (hI : MeromorphicAt I x)
    (hb0 : b≤0) (hbG : b≤meromorphicOrderAt G x)
    (hbH : b≤meromorphicOrderAt H x) (hbI : b≤meromorphicOrderAt I x)
    (hrow : HasAnalyticGerm (fun z => C z*F z+D z*G z+E z*H z+J z*I z) x) :
    b≤meromorphicOrderAt F x := by
  let R : ℂ → ℂ := fun z => D z*G z+E z*H z+J z*I z
  have hR : MeromorphicAt R x :=
    ((hD.meromorphicAt.mul hG).add (hE.meromorphicAt.mul hH)).add (hJ.meromorphicAt.mul hI)
  have hbR : b≤meromorphicOrderAt R x :=
    order_lower_add ((hD.meromorphicAt.mul hG).add (hE.meromorphicAt.mul hH))
      (hJ.meromorphicAt.mul hI)
      (order_lower_add (hD.meromorphicAt.mul hG) (hE.meromorphicAt.mul hH)
        (analytic_multiplier_order_lower hD hG hbG) (analytic_multiplier_order_lower hE hH hbH))
      (analytic_multiplier_order_lower hJ hI hbI)
  have hr : HasAnalyticGerm (fun z => 1*R z+C z*F z) x := by
    apply hrow.congr
    exact Filter.Eventually.of_forall (fun z => by dsimp [R]; ring)
  have hh := two_row_order_lower (A:=fun _ => (1:ℂ)) analyticAt_const hR hr hb0 hbR
  change b≤meromorphicOrderAt (C*F) x at hh
  rwa [meromorphicOrderAt_mul_of_ne_zero hC hC0] at hh

#print axioms order_lower_add
#print axioms four_row_order_lower
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticAnalyticGermPoleMultiplierV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Filter
open scoped Topology

theorem multiplier_zero_at_pole {F C : ℂ → ℂ} {x : ℂ}
    (hC : AnalyticAt ℂ C x)
    (hCF : HasAnalyticGerm (fun z => C z*F z) x)
    (hF : meromorphicOrderAt F x<0) : C x=0 := by
  by_contra hcx
  have hn : ∀ᶠ z in 𝓝[≠] x, C z≠0 :=
    (hC.continuousAt.eventually (eventually_ne_nhds hcx)).filter_mono nhdsWithin_le_nhds
  have hh : HasAnalyticGerm F x := by
    apply (hCF.mul_analytic (hC.inv hcx)).congr
    filter_upwards [hn] with z hz
    simp only [Pi.inv_apply,← mul_assoc,inv_mul_cancel₀ hz,one_mul]
  exact not_lt_of_ge hh.order_nonneg hF
#print axioms multiplier_zero_at_pole
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticAnalyticGermSimplePoleFreezeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex Filter Set
open scoped Topology

/-- A vanishing analytic multiplier removes an at-most-simple pole, as a
punctured germ. The assigned value at the puncture is irrelevant. -/
theorem vanishing_mul_simple_pole {A F : ℂ → ℂ} {x : ℂ}
    (hA : AnalyticAt ℂ A x) (hAx : A x=0) (hF : MeromorphicAt F x)
    (horder : (-1:WithTop ℤ)≤meromorphicOrderAt F x) :
    HasAnalyticGerm (fun z => A z*F z) x := by
  apply (hA.meromorphicAt.mul hF).meromorphicOrderAt_nonneg_iff.mp
  rw [meromorphicOrderAt_mul hA.meromorphicAt hF,hA.meromorphicOrderAt_eq]
  have hne : analyticOrderAt A x≠0 := hA.analyticOrderAt_ne_zero.mpr hAx
  cases ha : analyticOrderAt A x with
  | top => simp
  | coe n =>
    have hn : 1≤n := by
      have hn0 : n≠0 := by intro hn; apply hne; simp [ha,hn]
      omega
    simp only [ENat.map_natCast]
    cases hf : meromorphicOrderAt F x with
    | top => simp
    | coe m =>
      rw [hf] at horder
      change ((-1:ℤ):WithTop ℤ)≤(m:WithTop ℤ) at horder
      have hm : (-1:ℤ)≤m := WithTop.coe_le_coe.mp horder
      have hnm : (0:ℤ)≤(n:ℤ)+m := by omega
      exact_mod_cast hnm

/-- At a simple pole an analytic coefficient may be replaced by its value
at the pole, modulo analytic germs. -/
theorem freeze_simple_pole_coefficient {A F : ℂ → ℂ} {x : ℂ}
    (hA : AnalyticAt ℂ A x) (hF : MeromorphicAt F x)
    (horder : (-1:WithTop ℤ)≤meromorphicOrderAt F x) :
    HasAnalyticGerm (fun z => (A z-A x)*F z) x :=
  vanishing_mul_simple_pole (hA.sub analyticAt_const) (sub_self _) hF horder

/-- An analytic anchor relation gives the constant residue profile, without
asserting equality of the meromorphic functions themselves. -/
theorem freeze_simple_pole_anchor {G F A : ℂ → ℂ} {x : ℂ}
    (hrel : HasAnalyticGerm (fun z => G z-A z*F z) x)
    (hA : AnalyticAt ℂ A x) (hF : MeromorphicAt F x)
    (horder : (-1:WithTop ℤ)≤meromorphicOrderAt F x) :
    HasAnalyticGerm (fun z => G z-A x*F z) x := by
  apply (hrel.add (freeze_simple_pole_coefficient hA hF horder)).congr
  exact Filter.Eventually.of_forall (fun z => by ring)

#print axioms vanishing_mul_simple_pole
#print axioms freeze_simple_pole_coefficient
#print axioms freeze_simple_pole_anchor
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticAnalyticGermProfileRowV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Filter
open scoped Topology

/-- A top-row scalar need only match the polar profile at the pole. This
permits the denominator rescalings in the finite certificate without
continuing any unobserved individual coordinate. -/
theorem profile_row_germ {ι : Type*} [Fintype ι]
    (G C : ℂ→ι→ℂ) (q : ι→ℂ) (F D : ℂ→ℂ) (x : ℂ)
    (hprofile : ∀ i, HasAnalyticGerm (fun z => G z i-q i*F z) x)
    (hC : ∀ i, AnalyticAt ℂ (fun z => C z i) x)
    (hD : AnalyticAt ℂ D x) (hF : MeromorphicAt F x)
    (horder : (-1:WithTop ℤ)≤meromorphicOrderAt F x)
    (hmatch : D x=∑ i, C x i*q i) :
    HasAnalyticGerm (fun z => (∑ i, C z i*G z i)-D z*F z) x := by
  classical
  have hR := HasAnalyticGerm.sum (fun i z => C z i*(G z i-q i*F z)) x
    (fun i => (hprofile i).mul_analytic (hC i))
  have hA : AnalyticAt ℂ (fun z => (∑ i, C z i*q i)-D z) x := by
    apply AnalyticAt.sub _ hD
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (hC i).mul analyticAt_const
  have hz : (∑ i, C x i*q i)-D x=0 := by rw [hmatch,sub_self]
  have hV := vanishing_mul_simple_pole hA hz hF horder
  apply (hR.add hV).congr
  exact Filter.Eventually.of_forall (fun z => by
    simp only [mul_sub,Finset.sum_sub_distrib,←mul_assoc,←Finset.sum_mul]
    ring)

#print axioms profile_row_germ
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticRegularizedOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex

theorem regularized_order {F : ℂ → ℂ} {x : ℂ} (hF : MeromorphicAt F x) :
    meromorphicOrderAt (fun z => (z-x)*F z) x=1+meromorphicOrderAt F x := by
  have hlin : MeromorphicAt (fun z : ℂ => z-x) x :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  change meromorphicOrderAt ((fun z : ℂ => z-x)*F) x=_
  rw [meromorphicOrderAt_mul hlin hF,meromorphicOrderAt_id_sub_const]

theorem regularized_order_nonneg_iff {F : ℂ → ℂ} {x : ℂ} (hF : MeromorphicAt F x) :
    0≤meromorphicOrderAt (fun z => (z-x)*F z) x ↔
      (-1:WithTop ℤ)≤meromorphicOrderAt F x := by
  rw [regularized_order hF]
  cases h : meromorphicOrderAt F x with
  | top => simp
  | coe n =>
    change ((0:ℤ):WithTop ℤ)≤((1:ℤ):WithTop ℤ)+(n:WithTop ℤ) ↔
      ((-1:ℤ):WithTop ℤ)≤(n:WithTop ℤ)
    rw [← WithTop.coe_add,WithTop.coe_le_coe,WithTop.coe_le_coe]
    omega

theorem regularized_order_ge_neg_one {F : ℂ → ℂ} {x : ℂ} (hF : MeromorphicAt F x)
    (hb : (-2:WithTop ℤ)≤meromorphicOrderAt F x) :
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => (z-x)*F z) x := by
  rw [regularized_order hF]
  cases h : meromorphicOrderAt F x with
  | top => simp
  | coe n =>
    rw [h] at hb
    have hn : -2≤n := WithTop.coe_le_coe.mp hb
    change ((-1:ℤ):WithTop ℤ)≤((1:ℤ):WithTop ℤ)+(n:WithTop ℤ)
    rw [← WithTop.coe_add,WithTop.coe_le_coe]
    omega

#print axioms regularized_order
#print axioms regularized_order_nonneg_iff
#print axioms regularized_order_ge_neg_one
end QuantitativeArithmeticAnalyticGerm
end
end

/-! ## QuantitativeArithmeticSimplePoleResidueV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticAnalyticGerm
open Complex Filter Set
open scoped Topology

theorem simple_residue_zero_iff {F R : ℂ → ℂ} {x : ℂ}
    (hF : MeromorphicAt F x) (hR : AnalyticAt ℂ R x)
    (he : (fun z => (z-x)*F z)=ᶠ[𝓝[≠] x] R) :
    R x=0 ↔ 0≤meromorphicOrderAt F x := by
  have hord := meromorphicOrderAt_congr he
  change meromorphicOrderAt ((fun z : ℂ => z-x)*F) x=meromorphicOrderAt R x at hord
  have hlin : MeromorphicAt (fun z : ℂ => z-x) x :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  rw [meromorphicOrderAt_mul hlin hF,
    meromorphicOrderAt_id_sub_const] at hord
  have hzero : R x=0 ↔ 0<meromorphicOrderAt R x := by
    constructor
    · intro hz
      apply (tendsto_zero_iff_meromorphicOrderAt_pos hR.meromorphicAt).mp
      simpa only [hz] using hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · intro hp
      exact tendsto_nhds_unique
        (hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        ((tendsto_zero_iff_meromorphicOrderAt_pos hR.meromorphicAt).mpr hp)
  rw [hzero,← hord]
  cases h : meromorphicOrderAt F x with
  | top => simp
  | coe n =>
    change (0:WithTop ℤ)<((1:ℤ):WithTop ℤ)+(n:WithTop ℤ) ↔
      ((0:ℤ):WithTop ℤ)≤(n:WithTop ℤ)
    rw [← WithTop.coe_add]
    change ((0:ℤ):WithTop ℤ)<((1+n:ℤ):WithTop ℤ) ↔ ((0:ℤ):WithTop ℤ)≤(n:WithTop ℤ)
    rw [WithTop.coe_lt_coe,WithTop.coe_le_coe]
    omega

/-- Residues of a finite family with at most simple poles simultaneously
satisfy every analytic-germ row. Vanishing detects removability coordinatewise. -/
theorem exists_simple_residue_vector {ι : Type*} [Fintype ι]
    (G : ℂ → ι → ℂ) (x : ℂ)
    (hG : ∀ j, MeromorphicAt (fun z => G z j) x)
    (hbound : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) x) :
    ∃ v : ι → ℂ,
      (∀ j, v j=0 ↔ 0≤meromorphicOrderAt (fun z => G z j) x) ∧
      ∀ A : ℂ → ι → ℂ,
        (∀ j, AnalyticAt ℂ (fun z => A z j) x) →
        HasAnalyticGerm (fun z => ∑ j, A z j*G z j) x →
        ∑ j, A x j*v j=0 := by
  classical
  have hlocal (j : ι) : ∃ R : ℂ → ℂ, AnalyticAt ℂ R x ∧
      (fun z => (z-x)*G z j)=ᶠ[𝓝[≠] x] R :=
    SmallLevelFiniteShift.simple_pole_cancellation (fun z => z-x) (fun z => G z j) x
      (analyticAt_id.sub analyticAt_const) (sub_self x) (hG j) (hbound j)
  choose R hR he using hlocal
  refine ⟨fun j => R j x,fun j => simple_residue_zero_iff (hG j) (hR j) (he j),?_⟩
  intro A hA hrow
  obtain ⟨H,hH,hrow⟩ := hrow
  have hleft : AnalyticAt ℂ (fun z => ∑ j, A z j*R j z) x :=
    Finset.analyticAt_fun_sum _ (fun j _ => (hA j).mul (hR j))
  have hright : AnalyticAt ℂ (fun z => (z-x)*H z) x :=
    (analyticAt_id.sub analyticAt_const).mul hH
  have heall : ∀ᶠ z in 𝓝[≠] x, ∀ j, (z-x)*G z j=R j z :=
    Filter.eventually_all.mpr he
  have hsum : (fun z => ∑ j, A z j*R j z)=ᶠ[𝓝[≠] x] (fun z => (z-x)*H z) := by
    filter_upwards [heall,hrow] with z hz hzr
    calc
      (∑ j, A z j*R j z) = ∑ j, A z j*((z-x)*G z j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hz j]
      _ = (z-x)*(∑ j, A z j*G z j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (z-x)*H z := by rw [hzr]
  have hfull := (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hleft.continuousAt hright.continuousAt).mp hsum
  simpa using hfull.eq_of_nhds

#print axioms simple_residue_zero_iff
#print axioms exists_simple_residue_vector
end QuantitativeArithmeticAnalyticGerm
end
end
