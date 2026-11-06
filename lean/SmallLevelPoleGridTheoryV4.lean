module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic

/-! Consolidated chapter: SmallLevelPoleGrid. Original declarations and local scopes are retained. -/

/-! ## SmallLevelMeromorphicGridV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- A finite grid of scalar meromorphic germs is one meromorphic vector germ. -/
theorem meromorphic_vector {ι : Type*} [Fintype ι] {F : ι → ℂ → ℂ} {x : ℂ}
    (hF : ∀ i, MeromorphicAt (F i) x) : MeromorphicAt (fun z i => F i z) x := by
  classical
  choose n hn using hF
  let m := Finset.univ.sup n
  refine ⟨m, ?_⟩
  apply AnalyticAt.pi
  intro i
  have hni : n i≤m := Finset.le_sup (f:=n) (Finset.mem_univ i)
  have hp : AnalyticAt ℂ (fun z : ℂ => (z-x)^(m-n i)) x :=
    (analyticAt_id.sub analyticAt_const).pow _
  have h := hp.smul (hn i)
  convert h using 1
  funext z
  change (z-x)^m*F i z=(z-x)^(m-n i)*((z-x)^n i*F i z)
  rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hni]

/-- A pole in any coordinate forces a pole of the full vector. -/
theorem vector_order_neg {ι : Type*} [Fintype ι] {F : ι → ℂ → ℂ} {x : ℂ}
    (hF : ∀ i, MeromorphicAt (F i) x)
    (hpole : ∃ i, meromorphicOrderAt (F i) x<0) :
    meromorphicOrderAt (fun z i => F i z) x<0 := by
  by_contra! h
  obtain ⟨g,hg,he⟩ := (meromorphic_vector hF).meromorphicOrderAt_nonneg_iff.mp h
  obtain ⟨i,hi⟩ := hpole
  have he' : F i=ᶠ[𝓝[≠] x] fun z => g z i := by
    filter_upwards [he] with z hz
    exact congrFun hz i
  have ha : AnalyticAt ℂ (fun z => g z i) x := analyticAt_pi_iff.mp hg i
  rw [meromorphicOrderAt_congr he'] at hi
  exact (not_lt_of_ge ha.meromorphicOrderAt_nonneg) hi

/-- Multiplying the whole grid by one positive power removes its highest pole,
and the resulting analytic vector has a nonzero value at the pole. -/
theorem leading_vector {ι : Type*} [Fintype ι] {F : ι → ℂ → ℂ} {x : ℂ}
    (hF : ∀ i, MeromorphicAt (F i) x)
    (hpole : ∃ i, meromorphicOrderAt (F i) x<0) :
    ∃ (u : ℕ) (g : ℂ → (ι → ℂ)), 0<u ∧ AnalyticAt ℂ g x ∧ g x≠0 ∧
      ∀ᶠ z in 𝓝[≠] x, (z-x)^u • (fun i => F i z)=g z := by
  have hv := meromorphic_vector hF
  have ho := vector_order_neg hF hpole
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  have hn0 : n<0 := by simpa [← hn] using ho
  obtain ⟨g,hg,hg0,he⟩ := (meromorphicOrderAt_eq_int_iff hv).mp hn.symm
  refine ⟨(-n).toNat,g,by omega,hg,hg0,?_⟩
  have hu : (((-n).toNat:ℕ):ℤ)= -n := Int.toNat_of_nonneg (by omega)
  filter_upwards [he,self_mem_nhdsWithin] with z hz hzx
  have hne : z-x≠0 := sub_ne_zero.mpr hzx
  rw [hz,← mul_smul,← zpow_natCast,hu,← zpow_add₀ hne]
  simp

#print axioms meromorphic_vector
#print axioms vector_order_neg
#print axioms leading_vector

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleRightmostV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- A common right half-plane gives a rightmost grid pole in any nonnegative
integer translation class containing a pole. The selected coordinate need
not be the coordinate that supplied the original pole. -/
theorem rightmost_pole {ι : Type*} (F : ι → ℂ → ℂ) {x : ℂ}
    (hpole : ∃ i, meromorphicOrderAt (F i) x<0)
    (σ : ℝ) (hhalf : ∀ i z, σ<z.re → AnalyticAt ℂ (F i) z) :
    ∃ n : ℕ, (∃ i, meromorphicOrderAt (F i) (x+n)<0) ∧
      ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (F i) (x+n+j) := by
  classical
  obtain ⟨B,hB⟩ := exists_nat_gt (σ-x.re)
  let P : ℕ → Prop := fun n => ∃ i, meromorphicOrderAt (F i) (x+n)<0
  have hlim (n : ℕ) (hn : B≤n) : ¬P n := by
    rintro ⟨i,hi⟩
    have hn' : (B:ℝ)≤n := by exact_mod_cast hn
    have hr : σ<(x+(n:ℂ)).re := by
      simp only [Complex.add_re,Complex.natCast_re]
      linarith
    exact (not_lt_of_ge (hhalf i _ hr).meromorphicOrderAt_nonneg) hi
  let n := Nat.findGreatest P B
  have hn : P n := Nat.findGreatest_spec (Nat.zero_le B) (by simpa [P] using hpole)
  refine ⟨n,hn,?_⟩
  intro j hj i
  by_contra! hi
  have hp : P (n+j) := ⟨i,by simpa only [Nat.cast_add,add_assoc] using hi⟩
  by_cases hb : B≤n+j
  · exact hlim _ hb hp
  · exact Nat.findGreatest_is_greatest (by dsimp [n]; omega)
      (by omega : n+j≤B) hp

#print axioms rightmost_pole

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleReflectionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- An analytic nonvanishing functional-equation multiplier preserves pole
orders under reflection, without assuming that either side is entire. -/
theorem reflected_order {F a : ℂ → ℂ} {x K : ℂ}
    (ha : AnalyticAt ℂ a x) (ha0 : a x≠0)
    (he : ∀ᶠ z in 𝓝[≠] x, F z=a z*F (K-z)) :
    meromorphicOrderAt F x=meromorphicOrderAt F (K-x) := by
  rw [meromorphicOrderAt_congr he]
  change meromorphicOrderAt (a*(F ∘ (fun z => K-z))) x=_
  rw [meromorphicOrderAt_mul_of_ne_zero ha ha0]
  apply meromorphicOrderAt_comp_of_deriv_ne_zero
  · exact analyticAt_const.sub analyticAt_id
  · have hd : HasDerivAt (fun z : ℂ => K-z) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub K
    rw [hd.deriv]
    norm_num

/-- Reflection lets any pole be chosen on or to the right of the central
line. The reflected point is an actual pole, not a new analytic premise. -/
theorem pole_on_right {F a : ℂ → ℂ} (K : ℝ)
    (ha : ∀ x, AnalyticAt ℂ a x) (ha0 : ∀ x, a x≠0)
    (he : ∀ z, F z=a z*F ((K:ℂ)-z))
    (hpole : ∃ x, meromorphicOrderAt F x<0) :
    ∃ x, K/2≤x.re ∧ meromorphicOrderAt F x<0 := by
  obtain ⟨x,hx⟩ := hpole
  by_cases hr : K/2≤x.re
  · exact ⟨x,hr,hx⟩
  · refine ⟨(K:ℂ)-x,?_,?_⟩
    · simp only [Complex.sub_re,Complex.ofReal_re]
      linarith
    · have ho := reflected_order (ha x) (ha0 x) (Filter.Eventually.of_forall he)
      rw [← ho]
      exact hx

/-- A nonzero constant times an exponential is an everywhere analytic unit,
as required for the completed-twist functional-equation multipliers. -/
theorem exponential_multiplier (ε α β : ℂ) (hε : ε≠0) (x : ℂ) :
    AnalyticAt ℂ (fun z => ε*Complex.exp (α*z+β)) x ∧
      ε*Complex.exp (α*x+β)≠0 := by
  constructor
  · fun_prop
  · exact mul_ne_zero hε (Complex.exp_ne_zero _)

#print axioms reflected_order
#print axioms pole_on_right
#print axioms exponential_multiplier

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleCombinationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- Analytic coefficients preserve analytic extension of a finite combination
of removable meromorphic germs. -/
theorem combination_extension {ι : Type*} [Fintype ι]
    (F : ι → ℂ → ℂ) (w : ℂ → ι → ℂ) {x : ℂ}
    (hF : ∀ i, MeromorphicAt (F i) x)
    (ho : ∀ i, 0≤meromorphicOrderAt (F i) x)
    (hw : ∀ i, AnalyticAt ℂ (fun z => w z i) x) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G x ∧
      (fun z => ∑ i, w z i*F i z)=ᶠ[𝓝[≠] x] G := by
  classical
  choose g hg he using fun i => (hF i).meromorphicOrderAt_nonneg_iff.mp (ho i)
  refine ⟨fun z => ∑ i, w z i*g i z,?_,?_⟩
  · exact Finset.analyticAt_fun_sum _ (fun i _ => (hw i).mul (hg i))
  · filter_upwards [Filter.eventually_all.mpr he] with z hz
    apply Finset.sum_congr rfl
    intro i _
    rw [hz i]

/-- A pole of a character-twist combination must come from some grid
coordinate; no specified coordinate is assumed to carry the top pole. -/
theorem combination_pole {ι : Type*} [Fintype ι]
    (F : ι → ℂ → ℂ) (w : ℂ → ι → ℂ) {x : ℂ}
    (hF : ∀ i, MeromorphicAt (F i) x)
    (hw : ∀ i, AnalyticAt ℂ (fun z => w z i) x)
    (hpole : meromorphicOrderAt (fun z => ∑ i, w z i*F i z) x<0) :
    ∃ i, meromorphicOrderAt (F i) x<0 := by
  by_contra! ho
  obtain ⟨G,hG,he⟩ := combination_extension F w hF ho hw
  rw [meromorphicOrderAt_congr he] at hpole
  exact (not_lt_of_ge hG.meromorphicOrderAt_nonneg) hpole

#print axioms combination_extension
#print axioms combination_pole

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleLeadingSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- A genuine pole of a finite meromorphic grid supplies a nonzero vector in
the kernel of every analytic leading row whose right hand side is analytic. -/
theorem leading_kernel {ι ρ : Type*} [Fintype ι]
    {F : ι → ℂ → ℂ} {x : ℂ}
    (hF : ∀ i, MeromorphicAt (F i) x)
    (hpole : ∃ i, meromorphicOrderAt (F i) x<0)
    (A : ℂ → ρ → ι → ℂ) (H : ρ → ℂ → ℂ)
    (hA : ∀ r i, AnalyticAt ℂ (fun z => A z r i) x)
    (hH : ∀ r, AnalyticAt ℂ (H r) x)
    (he : ∀ r, ∀ᶠ z in 𝓝[≠] x, ∑ i, A z r i*F i z=H r z) :
    ∃ v : ι → ℂ, v≠0 ∧ ∀ r, ∑ i, A x r i*v i=0 := by
  classical
  obtain ⟨u,g,hu,hg,hg0,hfg⟩ := leading_vector hF hpole
  refine ⟨g x,hg0,?_⟩
  intro r
  have hl : AnalyticAt ℂ (fun z => ∑ i, A z r i*g z i) x :=
    Finset.analyticAt_fun_sum _ (fun i _ => (hA r i).mul (analyticAt_pi_iff.mp hg i))
  have hp : AnalyticAt ℂ (fun z : ℂ => (z-x)^u) x :=
    (analyticAt_id.sub analyticAt_const).pow _
  have hr := hp.mul (hH r)
  have hh : (fun z => ∑ i, A z r i*g z i)=ᶠ[𝓝[≠] x]
      (fun z => (z-x)^u*H r z) := by
    filter_upwards [hfg,he r] with z hz hez
    calc
      _ = ∑ i, A z r i*((z-x)^u*F i z) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← congrFun hz i]
        rfl
      _ = (z-x)^u*(∑ i, A z r i*F i z) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hez]
  have hfull := (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hl.continuousAt hr.continuousAt).mp hh
  have hx := hfull.eq_of_nhds
  simpa [zero_pow hu.ne'] using hx

/-- An explicit injective leading matrix rules out every grid pole. This is
an analytic bridge for finite certificates, not an assumption of modularity. -/
theorem no_poles_of_leading_kernel {ι ρ : Type*} [Fintype ι]
    {F : ι → ℂ → ℂ} {x : ℂ} (hF : ∀ i, MeromorphicAt (F i) x)
    (A : ℂ → ρ → ι → ℂ) (H : ρ → ℂ → ℂ)
    (hA : ∀ r i, AnalyticAt ℂ (fun z => A z r i) x)
    (hH : ∀ r, AnalyticAt ℂ (H r) x)
    (he : ∀ r, ∀ᶠ z in 𝓝[≠] x, ∑ i, A z r i*F i z=H r z)
    (hker : ∀ v : ι → ℂ, (∀ r, ∑ i, A x r i*v i=0) → v=0) :
    ∀ i, 0≤meromorphicOrderAt (F i) x := by
  intro i
  by_contra! hp
  obtain ⟨v,hv,hAv⟩ := leading_kernel hF ⟨i,hp⟩ A H hA hH he
  exact hv (hker v hAv)

#print axioms leading_kernel
#print axioms no_poles_of_leading_kernel

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleRowSpanV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- An analytic row-span certificate removes every Laurent order of its
target combination, including when the full leading matrix is singular. -/
theorem target_extension_of_row_span {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (F : ι → ℂ → ℂ) (A : ℂ → ρ → ι → ℂ) (H : ρ → ℂ → ℂ)
    (b : ℂ → ρ → ℂ) (w : ℂ → ι → ℂ) {x : ℂ}
    (hb : ∀ r, AnalyticAt ℂ (fun z => b z r) x)
    (hH : ∀ r, AnalyticAt ℂ (H r) x)
    (hw : ∀ᶠ z in 𝓝[≠] x, ∀ i, w z i=∑ r, b z r*A z r i)
    (he : ∀ r, ∀ᶠ z in 𝓝[≠] x, ∑ i, A z r i*F i z=H r z) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G x ∧
      (fun z => ∑ i, w z i*F i z)=ᶠ[𝓝[≠] x] G := by
  classical
  refine ⟨fun z => ∑ r, b z r*H r z,?_,?_⟩
  · exact Finset.analyticAt_fun_sum _ (fun r _ => (hb r).mul (hH r))
  · filter_upwards [hw,Filter.eventually_all.mpr he] with z hwz hez
    calc
      _ = ∑ i, (∑ r, b z r*A z r i)*F i z := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hwz i]
      _ = ∑ r, b z r*(∑ i, A z r i*F i z) := by
        simp_rw [Finset.sum_mul,Finset.mul_sum,mul_assoc]
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hez r]

theorem target_order_nonneg_of_row_span {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (F : ι → ℂ → ℂ) (A : ℂ → ρ → ι → ℂ) (H : ρ → ℂ → ℂ)
    (b : ℂ → ρ → ℂ) (w : ℂ → ι → ℂ) {x : ℂ}
    (hb : ∀ r, AnalyticAt ℂ (fun z => b z r) x)
    (hH : ∀ r, AnalyticAt ℂ (H r) x)
    (hw : ∀ᶠ z in 𝓝[≠] x, ∀ i, w z i=∑ r, b z r*A z r i)
    (he : ∀ r, ∀ᶠ z in 𝓝[≠] x, ∑ i, A z r i*F i z=H r z) :
    0≤meromorphicOrderAt (fun z => ∑ i, w z i*F i z) x := by
  obtain ⟨G,hG,hFG⟩ := target_extension_of_row_span F A H b w hb hH hw he
  rw [meromorphicOrderAt_congr hFG]
  exact hG.meromorphicOrderAt_nonneg

#print axioms target_extension_of_row_span
#print axioms target_order_nonneg_of_row_span

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleTaylorRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- At a rightmost grid pole, a finite Taylor source involving only positive
integer shifts and an analytic remainder has an analytic extension as a germ.
The values assigned at removable singularities are irrelevant. -/
theorem shifted_source_extension {ι κ : Type*} [Fintype κ]
    (F : ι → ℂ → ℂ) {x : ℂ}
    (hF : ∀ i (j : ℕ), MeromorphicAt (F i) (x+(j:ℕ)))
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (F i) (x+j))
    (index : κ → ι) (shift : κ → ℕ) (hpos : ∀ j, 0<shift j)
    (b : κ → ℂ → ℂ) (R : ℂ → ℂ)
    (hb : ∀ j, AnalyticAt ℂ (b j) x) (hR : AnalyticAt ℂ R x) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G x ∧
      (fun z => R z+∑ j, b j z*F (index j) (z+shift j))=ᶠ[𝓝[≠] x] G := by
  classical
  have hm (j : κ) : MeromorphicAt (fun z => F (index j) (z+shift j)) x :=
    meromorphicAt_comp_add_const_iff_meromorphicAt.mpr (hF (index j) (shift j))
  have ho (j : κ) : 0≤meromorphicOrderAt (fun z => F (index j) (z+shift j)) x := by
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
    exact hshift (shift j) (hpos j) (index j)
  choose G hG he using fun j => (hm j).meromorphicOrderAt_nonneg_iff.mp (ho j)
  refine ⟨fun z => R z+∑ j, b j z*G j z,?_,?_⟩
  · exact hR.add (Finset.analyticAt_fun_sum _ (fun j _ => (hb j).mul (hG j)))
  · filter_upwards [Filter.eventually_all.mpr he] with z hz
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hz j]

/-- Leading rows with positive-shift Taylor corrections annihilate an actual
nonzero leading Laurent vector at a rightmost pole. -/
theorem leading_kernel_of_shifted_rows {ι ρ κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → ℂ → ℂ) {x : ℂ}
    (hF : ∀ i (j : ℕ), MeromorphicAt (F i) (x+j))
    (hpole : ∃ i, meromorphicOrderAt (F i) x<0)
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (F i) (x+j))
    (A : ℂ → ρ → ι → ℂ) (index : ρ → κ → ι) (shift : ρ → κ → ℕ)
    (b : ρ → κ → ℂ → ℂ) (R : ρ → ℂ → ℂ)
    (hA : ∀ r i, AnalyticAt ℂ (fun z => A z r i) x)
    (hpos : ∀ r j, 0<shift r j)
    (hb : ∀ r j, AnalyticAt ℂ (b r j) x) (hR : ∀ r, AnalyticAt ℂ (R r) x)
    (he : ∀ r, ∀ᶠ z in 𝓝[≠] x,
      ∑ i, A z r i*F i z=R r z+∑ j, b r j z*F (index r j) (z+shift r j)) :
    ∃ v : ι → ℂ, v≠0 ∧ ∀ r, ∑ i, A x r i*v i=0 := by
  classical
  choose H hH hsource using fun r => shifted_source_extension F hF hshift
    (index r) (shift r) (hpos r) (b r) (R r) (hb r) (hR r)
  apply leading_kernel (fun i => by simpa using hF i 0) hpole A H hA hH
  intro r
  filter_upwards [he r,hsource r] with z hz hs
  exact hz.trans hs

#print axioms shifted_source_extension
#print axioms leading_kernel_of_shifted_rows

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleCentralCriterionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- The pole-removal pattern used for a character-twist target. A finite
leading certificate confines rightmost grid poles to the central line; an
analytic row-span certificate removes the target germ there. All analytic
continuation, row identities and finite certificates remain explicit inputs. -/
theorem target_no_poles_of_central_rows {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (F : ι → ℂ → ℂ) (w : ι → ℂ) (a : ℂ → ℂ) (K σ : ℝ)
    (hF : ∀ i x, MeromorphicAt (F i) x)
    (hhalf : ∀ i z, σ<z.re → AnalyticAt ℂ (F i) z)
    (ha : ∀ x, AnalyticAt ℂ a x) (ha0 : ∀ x, a x≠0)
    (hfe : ∀ z, (∑ i, w i*F i z)=a z*(∑ i, w i*F i ((K:ℂ)-z)))
    (A : ℂ → ρ → ι → ℂ) (H : ρ → ℂ → ℂ)
    (hA : ∀ x r i, AnalyticAt ℂ (fun z => A z r i) x)
    (hrows : ∀ x r, ∀ᶠ z in 𝓝[≠] x, ∑ i, A z r i*F i z=H r z)
    (hsource : ∀ x, (∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (F i) (x+j)) →
      ∀ r, ∃ G : ℂ → ℂ, AnalyticAt ℂ G x ∧ H r=ᶠ[𝓝[≠] x] G)
    (hcentral : ∀ x (v : ι → ℂ), v≠0 → (∀ r, ∑ i, A x r i*v i=0) → x.re=K/2)
    (helim : ∀ x, x.re=K/2 → ∃ b : ℂ → ρ → ℂ,
      (∀ r, AnalyticAt ℂ (fun z => b z r) x) ∧
      ∀ᶠ z in 𝓝[≠] x, ∀ i, w i=∑ r, b z r*A z r i) :
    ∀ x, 0≤meromorphicOrderAt (fun z => ∑ i, w i*F i z) x := by
  classical
  intro y
  by_contra! hy
  let C : ℂ → ℂ := fun z => ∑ i, w i*F i z
  obtain ⟨x,hxr,hxp⟩ := pole_on_right (F:=C) K ha ha0 hfe ⟨y,hy⟩
  have hpgrid := combination_pole F (fun _ i => w i) (fun i => hF i x)
    (fun _ => analyticAt_const) hxp
  obtain ⟨n,hpn,hshift⟩ := rightmost_pole F hpgrid σ hhalf
  choose G hG hHG using hsource (x+n) hshift
  have he (r : ρ) : ∀ᶠ z in 𝓝[≠] (x+n), ∑ i, A z r i*F i z=G r z := by
    filter_upwards [hrows (x+n) r,hHG r] with z hz hs
    exact hz.trans hs
  obtain ⟨v,hv,hAv⟩ := leading_kernel (fun i => hF i (x+n)) hpn A G (hA (x+n)) hG he
  have hc := hcentral (x+n) v hv hAv
  have hn0 : n=0 := by
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    have hr : x.re+(n:ℝ)=K/2 := by simpa only [Complex.add_re,Complex.natCast_re] using hc
    have hn' : (n:ℝ)=0 := by linarith
    exact_mod_cast hn'
  subst n
  simp only [Nat.cast_zero,add_zero] at hc hG hHG he
  obtain ⟨b,hb,hw⟩ := helim x hc
  have hn := target_order_nonneg_of_row_span F A G b (fun _ i => w i) hb hG hw he
  exact (not_lt_of_ge hn) hxp

/-- An exponential residual with a unit-modulus right hand side confines its
zero set to the central vertical line. This applies to the residual
35^(s-k/2) = sigma5*sigma7 in the level-35 leading certificate. -/
theorem exponential_zero_central {x : ℂ} {c α : ℝ} {s : ℂ}
    (hα : α≠0) (hs : ‖s‖=1)
    (he : Complex.exp ((α:ℂ)*(x-c))=s) : x.re=c := by
  have hn := congrArg norm he
  rw [Complex.norm_exp,hs] at hn
  have hz := (Real.exp_eq_one_iff _).mp hn
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.sub_re,zero_mul,sub_zero] at hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hα)

#print axioms target_no_poles_of_central_rows
#print axioms exponential_zero_central

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleEntireExtensionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- Nonnegative meromorphic orders give a genuine entire representative,
with the same punctured germs and unchanged values wherever the original
function was already analytic. -/
theorem entire_extension_of_no_poles (F : ℂ → ℂ)
    (hF : ∀ x, MeromorphicAt F x) (ho : ∀ x, 0≤meromorphicOrderAt F x) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ x, G=ᶠ[𝓝[≠] x] F) ∧ (∀ x, AnalyticAt ℂ F x → G x=F x) := by
  let G := toMeromorphicNFOn F Set.univ
  have hm : MeromorphicOn F Set.univ := fun x _ => hF x
  have ha (x : ℂ) : AnalyticAt ℂ G x := by
    apply ((meromorphicNFOn_toMeromorphicNFOn F Set.univ) (Set.mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (Set.mem_univ x)]
    exact ho x
  refine ⟨G,(fun x => (ha x).differentiableAt),?_,?_⟩
  · intro x
    exact hm.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ x)
  · intro x hx
    change toMeromorphicNFOn F Set.univ x=F x
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (Set.mem_univ x),
      toMeromorphicNFAt_eq_self.mpr hx.meromorphicNFAt]

/-- The entire representative of a pole-free character combination agrees
with its original grid sum throughout the common right half-plane. -/
theorem combination_entire_extension {ι : Type*} [Fintype ι]
    (F : ι → ℂ → ℂ) (w : ι → ℂ) (σ : ℝ)
    (hF : ∀ i x, MeromorphicAt (F i) x)
    (hhalf : ∀ i z, σ<z.re → AnalyticAt ℂ (F i) z)
    (ho : ∀ x, 0≤meromorphicOrderAt (fun z => ∑ i, w i*F i z) x) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun z => ∑ i, w i*F i z)) ∧
      ∀ z, σ<z.re → G z=∑ i, w i*F i z := by
  classical
  have hm (x : ℂ) : MeromorphicAt (fun z => ∑ i, w i*F i z) x :=
    MeromorphicAt.fun_sum (fun i _ => (MeromorphicAt.const (w i) x).mul (hF i x))
  obtain ⟨G,hG,hgerm,hvalue⟩ := entire_extension_of_no_poles _ hm ho
  refine ⟨G,hG,hgerm,?_⟩
  intro z hz
  apply hvalue z
  exact Finset.analyticAt_fun_sum _ (fun i _ => analyticAt_const.mul (hhalf i z hz))

/-- Passing to the entire representative preserves a reflected functional
equation initially known as an equality of punctured germs. -/
theorem entire_reflection (F G a : ℂ → ℂ) (K : ℂ)
    (hG : Differentiable ℂ G) (ha : ∀ x, AnalyticAt ℂ a x)
    (hgerm : ∀ x, G=ᶠ[𝓝[≠] x] F)
    (he : ∀ x, ∀ᶠ z in 𝓝[≠] x, F z=a z*F (K-z)) :
    ∀ x, G x=a x*G (K-x) := by
  intro x
  have hd : HasDerivAt (fun z : ℂ => K-z) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub K
  have href := hd.tendsto_nhdsNE (by norm_num : (-1:ℂ)≠0)
  have hh : G=ᶠ[𝓝[≠] x] (fun z => a z*G (K-z)) := by
    filter_upwards [hgerm x,he x,(hgerm (K-x)).comp_tendsto href] with z hz hfe hr
    change G (K-z)=F (K-z) at hr
    rw [hz,hfe,hr]
  have hc : ContinuousAt (fun z => a z*G (K-z)) x :=
    (ha x).continuousAt.mul (hG.continuous.continuousAt.comp hd.continuousAt)
  exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hG.continuous.continuousAt hc).mp hh).eq_of_nhds

#print axioms entire_reflection

#print axioms entire_extension_of_no_poles
#print axioms combination_entire_extension

end SmallLevelPoleGrid
end
end

/-! ## SmallLevelPoleRightmostAwayV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelPoleGrid

open Complex Filter Set
open scoped Topology

/-- A common right half-plane gives a rightmost grid pole in any nonnegative
integer translation class containing a pole. The selected coordinate need
not be the coordinate that supplied the original pole. -/
theorem rightmost_pole_away {ι : Type*} (F : ι → ℂ → ℂ) {x : ℂ} (k : ℂ) (hx : x≠k)
    (hpole : ∃ i, meromorphicOrderAt (F i) x<0)
    (σ : ℝ) (hhalf : ∀ i z, σ<z.re → AnalyticAt ℂ (F i) z) :
    ∃ n : ℕ, x+n≠k ∧ (∃ i, meromorphicOrderAt (F i) (x+n)<0) ∧
      ∀ j : ℕ, 0<j → x+n+j≠k → ∀ i, 0≤meromorphicOrderAt (F i) (x+n+j) := by
  classical
  obtain ⟨B,hB⟩ := exists_nat_gt (σ-x.re)
  let P : ℕ → Prop := fun n => x+n≠k ∧ ∃ i, meromorphicOrderAt (F i) (x+n)<0
  have hlim (n : ℕ) (hn : B≤n) : ¬P n := by
    rintro ⟨_,i,hi⟩
    have hn' : (B:ℝ)≤n := by exact_mod_cast hn
    have hr : σ<(x+(n:ℂ)).re := by
      simp only [Complex.add_re,Complex.natCast_re]
      linarith
    exact (not_lt_of_ge (hhalf i _ hr).meromorphicOrderAt_nonneg) hi
  let n := Nat.findGreatest P B
  have hn : P n := Nat.findGreatest_spec (Nat.zero_le B) (by simpa [P] using And.intro hx hpole)
  refine ⟨n,hn.1,hn.2,?_⟩
  intro j hj hne i
  by_contra! hi
  have hp : P (n+j) := ⟨by simpa only [Nat.cast_add,add_assoc] using hne,
      i,by simpa only [Nat.cast_add,add_assoc] using hi⟩
  by_cases hb : B≤n+j
  · exact hlim _ hb hp
  · exact Nat.findGreatest_is_greatest (by dsimp [n]; omega)
      (by omega : n+j≤B) hp

#print axioms rightmost_pole_away

end SmallLevelPoleGrid
end
end
