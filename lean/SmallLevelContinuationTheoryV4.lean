module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.MellinTransform
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import SmallLevelPoleGridTheoryV4

/-! Consolidated chapter: SmallLevelContinuation. Original declarations and local scopes are retained. -/

/-! ## SmallLevelMeromorphicIdentityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelContinuation

open Complex Filter Set
open scoped Topology

/-- Meromorphic normal-form representatives agreeing as germs at one point
agree throughout a preconnected domain. Values at poles are included. -/
theorem normalForm_identity {F G : ℂ → ℂ} {U : Set ℂ} {x : ℂ}
    (hF : MeromorphicNFOn F U) (hG : MeromorphicNFOn G U)
    (hU : IsPreconnected U) (hx : x∈U) (he : F=ᶠ[𝓝[≠] x] G) : EqOn F G U := by
  have hsub : MeromorphicOn (fun z => F z-G z) U :=
    hF.meromorphicOn.sub hG.meromorphicOn
  have htop : meromorphicOrderAt (fun z => F z-G z) x=⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [he] with z hz
    simp only [hz,sub_self]
  intro y hy
  have hyorder := hsub.meromorphicOrderAt_eq_top_of_isPreconnected hU hx hy htop
  have hzero := meromorphicOrderAt_eq_top_iff.mp hyorder
  have he' : F=ᶠ[𝓝[≠] y] G := by
    filter_upwards [hzero] with z hz
    exact sub_eq_zero.mp hz
  exact (((hF hy).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hG hy)).mp he').eq_of_nhds

/-- Two continuations on a half-plane are identical if they agree on any
further right half-plane. No pointwise invertibility at determinant zeros is
needed for this uniqueness statement. -/
theorem halfplane_unique {F G : ℂ → ℂ} (b c : ℝ)
    (hF : MeromorphicNFOn F {z : ℂ | b<z.re})
    (hG : MeromorphicNFOn G {z : ℂ | b<z.re})
    (he : EqOn F G {z : ℂ | c<z.re}) : EqOn F G {z : ℂ | b<z.re} := by
  let x : ℂ := ((max b c+1:ℝ):ℂ)
  have hxb : b<x.re := by dsimp [x]; linarith [le_max_left b c]
  have hxc : c<x.re := by dsimp [x]; linarith [le_max_right b c]
  apply normalForm_identity hF hG (convex_halfSpace_re_gt b).isPreconnected hxb
  have hn : ∀ᶠ z in 𝓝 x, c<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hxc
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with z hz
  exact he hz

#print axioms normalForm_identity
#print axioms halfplane_unique

end SmallLevelContinuation
end
end

/-! ## SmallLevelMeromorphicMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelContinuation

open Complex Filter Set Matrix
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem determinant_analytic {A : ℂ → Matrix ι ι ℂ} {x : ℂ}
    (hA : ∀ i j, AnalyticAt ℂ (fun z => A z i j) x) :
    AnalyticAt ℂ (fun z => (A z).det) x := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ => hA (σ i) i))

theorem adjugate_analytic {A : ℂ → Matrix ι ι ℂ} {x : ℂ}
    (hA : ∀ i j, AnalyticAt ℂ (fun z => A z i j) x) (i j : ι) :
    AnalyticAt ℂ (fun z => (A z).adjugate i j) x := by
  simp_rw [Matrix.adjugate_apply]
  apply determinant_analytic
  intro p q
  by_cases hp : p=j
  · subst p
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simpa [Matrix.updateRow,Function.update_of_ne hp] using hA p q

/-- Adjugate division is meromorphic even where the leading matrix is
singular. Agreement with a previously known solution is proved separately. -/
def matrixSolve (A : ℂ → Matrix ι ι ℂ) (H : ℂ → ι → ℂ) (z : ℂ) : ι → ℂ :=
  (A z).det⁻¹ • ((A z).adjugate *ᵥ H z)

theorem matrixSolve_meromorphic {A : ℂ → Matrix ι ι ℂ} {H : ℂ → ι → ℂ} {x : ℂ}
    (hA : ∀ i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hH : ∀ i, MeromorphicAt (fun z => H z i) x) (i : ι) :
    MeromorphicAt (fun z => matrixSolve A H z i) x := by
  change MeromorphicAt (fun z => (A z).det⁻¹ * ∑ j, (A z).adjugate i j * H z j) x
  apply (determinant_analytic hA).meromorphicAt.inv.mul
  exact MeromorphicAt.fun_sum (fun j _ => (adjugate_analytic hA i j).meromorphicAt.mul (hH j))

theorem matrixSolve_eq {A : ℂ → Matrix ι ι ℂ} {H V : ℂ → ι → ℂ} {z : ℂ}
    (hd : (A z).det≠0) (he : A z *ᵥ V z=H z) : matrixSolve A H z=V z := by
  rw [matrixSolve,← he,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
    Matrix.smul_mulVec,Matrix.one_mulVec,smul_smul,inv_mul_cancel₀ hd,one_smul]

theorem matrixSolve_eq_germ {A : ℂ → Matrix ι ι ℂ} {H V : ℂ → ι → ℂ} {x : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] x, (A z).det≠0)
    (he : ∀ᶠ z in 𝓝[≠] x, A z *ᵥ V z=H z) (i : ι) :
    (fun z => matrixSolve A H z i)=ᶠ[𝓝[≠] x] (fun z => V z i) := by
  filter_upwards [hd,he] with z hz hez
  exact congrFun (matrixSolve_eq hz hez) i

#print axioms determinant_analytic
#print axioms adjugate_analytic
#print axioms matrixSolve_meromorphic
#print axioms matrixSolve_eq
#print axioms matrixSolve_eq_germ

end SmallLevelContinuation
end
end

/-! ## SmallLevelContinuationStepV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelContinuation

open Complex Filter Set Matrix
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A single nonzero value of an entire determinant excludes a zero germ at
every point, including points where the determinant itself vanishes. -/
theorem determinant_nonzero_germ {A : ℂ → Matrix ι ι ℂ}
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hd : ∃ y, (A y).det≠0) (x : ℂ) :
    ∀ᶠ z in 𝓝[≠] x, (A z).det≠0 := by
  rcases (determinant_analytic (hA x)).eventually_eq_zero_or_eventually_ne_zero with hz|hz
  · obtain ⟨y,hy⟩ := hd
    have han : AnalyticOnNhd ℂ (fun z => (A z).det) Set.univ :=
      fun z _ => determinant_analytic (hA z)
    exact False.elim (hy (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ x) hz (Set.mem_univ y)))
  · exact hz

/-- A meromorphic matrix right side on a larger half-plane gives a unique
extension of the previous solution. The equations need only hold in a common
far right half-plane. The extension includes determinant zeros in normal form. -/
theorem matrix_halfplane_extension (a b c : ℝ) (hab : a≤b)
    (A : ℂ → Matrix ι ι ℂ) (H V : ℂ → ι → ℂ)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hd : ∃ y, (A y).det≠0)
    (hH : ∀ i, MeromorphicOn (fun z => H z i) {z : ℂ | a<z.re})
    (hV : ∀ i, MeromorphicNFOn (fun z => V z i) {z : ℂ | b<z.re})
    (he : ∀ z : ℂ, c<z.re → A z *ᵥ V z=H z) :
    ∃ W : ℂ → ι → ℂ,
      (∀ i, MeromorphicNFOn (fun z => W z i) {z : ℂ | a<z.re}) ∧
      (∀ z : ℂ, b<z.re → W z=V z) ∧
      ∀ i x, a<x.re → (fun z => W z i)=ᶠ[𝓝[≠] x]
        (fun z => matrixSolve A H z i) := by
  let S (i : ι) : ℂ → ℂ := fun z => matrixSolve A H z i
  have hS (i : ι) : MeromorphicOn (S i) {z : ℂ | a<z.re} :=
    fun x hx => matrixSolve_meromorphic (hA x) (fun j => hH j x hx) i
  let W : ℂ → ι → ℂ := fun z i => toMeromorphicNFOn (S i) {z : ℂ | a<z.re} z
  have hW (i : ι) : MeromorphicNFOn (fun z => W z i) {z : ℂ | a<z.re} :=
    meromorphicNFOn_toMeromorphicNFOn (S i) _
  have hgerm (i : ι) (x : ℂ) (hx : a<x.re) :
      (fun z => W z i)=ᶠ[𝓝[≠] x] S i :=
    (hS i).toMeromorphicNFOn_eq_self_on_nhdsNE hx
  refine ⟨W,hW,?_,hgerm⟩
  intro z hz
  funext i
  let x : ℂ := ((max b c+1:ℝ):ℂ)
  have hxb : b<x.re := by dsimp [x]; linarith [le_max_left b c]
  have hxc : c<x.re := by dsimp [x]; linarith [le_max_right b c]
  have hxa : a<x.re := lt_of_le_of_lt hab hxb
  have hWb : MeromorphicNFOn (fun z => W z i) {z : ℂ | b<z.re} :=
    fun y hy => hW i (lt_of_le_of_lt hab hy)
  apply normalForm_identity hWb (hV i) (convex_halfSpace_re_gt b).isPreconnected hxb _ hz
  apply (hgerm i x hxa).trans
  apply matrixSolve_eq_germ (determinant_nonzero_germ hA hd x)
  have hn : ∀ᶠ y in 𝓝 x, c<y.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hxc
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
  exact he y hy

#print axioms determinant_nonzero_germ
#print axioms matrix_halfplane_extension

end SmallLevelContinuation
end
end

/-! ## SmallLevelHalfplaneGluingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelContinuation

open Complex Filter Set
open scoped Topology

/-- Normal-form continuations to arbitrarily far left half-planes glue to
one global meromorphic function. Pairwise compatibility follows from the
identity theorem and agreement with the same initial function. -/
theorem halfplane_glue (B : ℝ) (F : ℂ → ℂ)
    (h : ∀ n : ℕ, ∃ G : ℂ → ℂ,
      MeromorphicNFOn G {z : ℂ | B-(n:ℝ)<z.re} ∧
      EqOn G F {z : ℂ | B<z.re}) :
    ∃ G : ℂ → ℂ, (∀ x, MeromorphicNFAt G x) ∧ EqOn G F {z : ℂ | B<z.re} := by
  choose V hV he using h
  have hcover (x : ℂ) : ∃ n : ℕ, B-(n:ℝ)<x.re := by
    obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
    exact ⟨n,by linarith⟩
  choose depth hdepth using hcover
  let G : ℂ → ℂ := fun x => V (depth x) x
  have hagree (n m : ℕ) (x : ℂ) (hn : B-(n:ℝ)<x.re) (hm : B-(m:ℝ)<x.re) :
      V n x=V m x := by
    have hnm : EqOn (V n) (V m) {z : ℂ | max (B-(n:ℝ)) (B-(m:ℝ))<z.re} := by
      apply halfplane_unique (max (B-(n:ℝ)) (B-(m:ℝ))) B
      · intro z hz
        exact hV n (lt_of_le_of_lt (le_max_left (B-(n:ℝ)) (B-(m:ℝ))) hz)
      · intro z hz
        exact hV m (lt_of_le_of_lt (le_max_right (B-(n:ℝ)) (B-(m:ℝ))) hz)
      · intro z hz
        exact (he n hz).trans (he m hz).symm
    exact hnm (max_lt hn hm)
  have hlocal (n : ℕ) (x : ℂ) (hx : B-(n:ℝ)<x.re) : G=ᶠ[𝓝 x] V n := by
    have hn : ∀ᶠ y in 𝓝 x, B-(n:ℝ)<y.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx
    filter_upwards [hn] with y hy
    exact hagree (depth y) n y (hdepth y) hy
  refine ⟨G,?_,?_⟩
  · intro x
    exact (meromorphicNFAt_congr (hlocal (depth x) x (hdepth x))).mpr (hV (depth x) (hdepth x))
  · intro x hx
    exact he (depth x) hx

#print axioms halfplane_glue

end SmallLevelContinuation
end
end

/-! ## SmallLevelClosedContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelContinuation

open Complex Filter Set Matrix
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Closed-system continuation from finite Taylor rows. Here `C m` is the
coefficient of the positive shift `m+1`, and `H n` is the remainder after
retaining shifts 1 through n. The actual Taylor--Fricke estimates and finite
determinant certificate are explicit hypotheses, not asserted by this lemma. -/
theorem closed_system_continuation (B : ℝ) (F : ℂ → ι → ℂ)
    (A : ℂ → Matrix ι ι ℂ) (C : ℕ → ℂ → Matrix ι ι ℂ)
    (H : ℕ → ℂ → ι → ℂ)
    (hF : ∀ i z, B<z.re → AnalyticAt ℂ (fun w => F w i) z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hd : ∃ y, (A y).det≠0)
    (hC : ∀ m x i j, AnalyticAt ℂ (fun z => C m z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re → ∀ i,
      ∑ j, A z i j*F z j=H n z i+
        ∑ m ∈ Finset.range n, ∑ j, C m z i j*F (z+((m:ℂ)+1)) j) :
    ∃ G : ℂ → ι → ℂ, (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=F z := by
  have stages : ∀ n : ℕ, ∃ V : ℂ → ι → ℂ,
      (∀ i, MeromorphicNFOn (fun z => V z i) {z : ℂ | B-(n:ℝ)<z.re}) ∧
      ∀ z, B<z.re → V z=F z := by
    intro n
    induction n with
    | zero =>
      refine ⟨F,?_,fun _ _ => rfl⟩
      intro i z hz
      exact (hF i z (by simpa using hz)).meromorphicNFAt
    | succ n ih =>
      obtain ⟨V,hV,heV⟩ := ih
      let R : ℂ → ι → ℂ := fun z i => H n z i+
        ∑ m ∈ Finset.range n, ∑ j, C m z i j*V (z+((m:ℂ)+1)) j
      have hR (i : ι) : MeromorphicOn (fun z => R z i)
          {z : ℂ | B-((n:ℝ)+1)<z.re} := by
        intro x hx
        apply (hH n i x hx).meromorphicAt.add
        apply MeromorphicAt.fun_sum
        intro m _
        apply MeromorphicAt.fun_sum
        intro j _
        apply (hC m x i j).meromorphicAt.mul
        have hshift : B-(n:ℝ)<(x+((m:ℂ)+1)).re := by
          simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
          change B-((n:ℝ)+1)<x.re at hx
          linarith [Nat.cast_nonneg (α:=ℝ) m]
        exact ((hV j hshift).meromorphicAt).comp_analyticAt
          (g := fun z : ℂ => z+((m:ℂ)+1)) (by fun_prop)
      have he : ∀ z, B<z.re → A z *ᵥ V z=R z := by
        intro z hz
        funext i
        change (∑ j, A z i j*V z j)=_
        rw [heV z hz,hrow n z hz i]
        change H n z i+_=H n z i+_
        congr 1
        apply Finset.sum_congr rfl
        intro m _
        have hs : B<(z+((m:ℂ)+1)).re := by
          simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
          linarith [Nat.cast_nonneg (α:=ℝ) m]
        rw [heV _ hs]
      obtain ⟨W,hW,heW,_⟩ := matrix_halfplane_extension
        (B-((n:ℝ)+1)) (B-(n:ℝ)) B (by linarith) A R V hA hd hR hV he
      refine ⟨W,?_,?_⟩
      · simpa only [Nat.cast_succ] using hW
      · intro z hz
        exact (heW z (by linarith [Nat.cast_nonneg (α:=ℝ) n])).trans (heV z hz)
  have hcoord (i : ι) : ∃ G : ℂ → ℂ, (∀ x, MeromorphicNFAt G x) ∧
      EqOn G (fun z => F z i) {z : ℂ | B<z.re} := by
    apply halfplane_glue B (fun z => F z i)
    intro n
    obtain ⟨V,hV,heV⟩ := stages n
    exact ⟨fun z => V z i,hV i,fun z hz => congrFun (heV z hz) i⟩
  choose G hG heG using hcoord
  refine ⟨fun z i => G i z,hG,?_⟩
  intro z hz
  funext i
  exact heG i hz

#print axioms closed_system_continuation

end SmallLevelContinuation
end
end

/-! ## SmallLevelContinuedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace SmallLevelContinuation
open Complex Filter Set Matrix
open scoped Topology

/-- Meromorphic equations continue as punctured germs throughout a
half-plane, without requiring normal-form representatives of their sums. -/
theorem halfplane_germ_identity {F G : ℂ → ℂ} (b c : ℝ)
    (hF : MeromorphicOn F {z : ℂ | b<z.re})
    (hG : MeromorphicOn G {z : ℂ | b<z.re})
    (he : EqOn F G {z : ℂ | c<z.re}) (x : ℂ) (hx : b<x.re) :
    F=ᶠ[𝓝[≠] x] G := by
  let y : ℂ := ((max b c+1:ℝ):ℂ)
  have hyb : b<y.re := by dsimp [y]; linarith [le_max_left b c]
  have hyc : c<y.re := by dsimp [y]; linarith [le_max_right b c]
  have hn : ∀ᶠ z in 𝓝 y, c<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hyc
  have htop : meromorphicOrderAt (fun z => F z-G z) y=⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with z hz
    exact sub_eq_zero.mpr (he hz)
  have hxorder := (hF.sub hG).meromorphicOrderAt_eq_top_of_isPreconnected
    (convex_halfSpace_re_gt b).isPreconnected hyb hx htop
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hxorder] with z hz
  exact sub_eq_zero.mp hz

variable {ι : Type*} [Fintype ι]

/-- The full Taylor recurrence holds as a germ wherever its remainder is
analytic, after any global meromorphic continuation agreeing on the initial
half-plane. This includes every retained positive shift. -/
theorem continued_rows (B : ℝ) (F G : ℂ → ι → ℂ)
    (A : ℂ → Matrix ι ι ℂ) (C : ℕ → ℂ → Matrix ι ι ℂ)
    (H : ℕ → ℂ → ι → ℂ)
    (hG : ∀ i x, MeromorphicAt (fun z => G z i) x)
    (hGF : ∀ z, B<z.re → G z=F z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re →
      A z *ᵥ F z=H n z+∑ m∈Finset.range n, C m z *ᵥ F (z+((m:ℂ)+1)))
    (n : ℕ) (i : ι) (x : ℂ) (hx : B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
      (fun z => H n z i+∑ m∈Finset.range n, ∑ j, C m z i j*G (z+((m:ℂ)+1)) j) := by
  apply halfplane_germ_identity (B-((n:ℝ)+1)) B _ _ _ x hx
  · intro z _
    exact MeromorphicAt.fun_sum (fun j _ => (hA z i j).meromorphicAt.mul (hG j z))
  · intro z hz
    apply (hH n i z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro m _
    apply MeromorphicAt.fun_sum
    intro j _
    exact (hC m z i j).meromorphicAt.mul
      ((hG j (z+((m:ℂ)+1))).comp_analyticAt (g:=fun w : ℂ => w+((m:ℂ)+1)) (by fun_prop))
  · intro z hz
    dsimp only
    change B<z.re at hz
    have he := congrFun (hrow n z hz) i
    simp only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] at he
    rw [hGF z hz]
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    have hs : B<(z+((m:ℂ)+1)).re := by
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) m]
    rw [hGF _ hs]

#print axioms halfplane_germ_identity
#print axioms continued_rows
end SmallLevelContinuation
end
end

/-! ## SmallLevelContinuedPoleKernelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section

namespace SmallLevelContinuation
open Complex Filter Set Matrix
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- At a rightmost pole of a continued Taylor system, its leading matrix
has a genuine nonzero kernel vector. The truncation is chosen far enough
to make the actual remainder analytic at that pole. -/
theorem continued_leading_kernel (B : ℝ) (G : ℂ → ι → ℂ)
    (A : ℂ → Matrix ι ι ℂ) (C : ℕ → ℂ → Matrix ι ι ℂ)
    (H : ℕ → ℂ → ι → ℂ)
    (hG : ∀ i x, MeromorphicNFAt (fun z => G z i) x)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j, A z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ m∈Finset.range n, ∑ j, C m z i j*G (z+((m:ℂ)+1)) j))
    (x : ℂ) (hpole : ∃ i, meromorphicOrderAt (fun z => G z i) x<0)
    (hshift : ∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+j)) :
    ∃ v : ι → ℂ, v≠0 ∧ A x *ᵥ v=0 := by
  classical
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  let R : ι → ℂ → ℂ := fun i z => H n z i+
    ∑ m∈Finset.range n, ∑ j, C m z i j*G (z+((m:ℂ)+1)) j
  have hR (i : ι) : AnalyticAt ℂ (R i) x := by
    apply (hH n i x hx).add
    apply Finset.analyticAt_fun_sum
    intro m _
    apply Finset.analyticAt_fun_sum
    intro j _
    have hs : AnalyticAt ℂ (fun z => G z j) (x+((m:ℂ)+1)) := by
      apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      simpa only [Nat.cast_add,Nat.cast_one] using hshift (m+1) (by omega) j
    exact (hC m x i j).mul (hs.comp (f:=fun z : ℂ => z+((m:ℂ)+1))
      (analyticAt_id.add analyticAt_const))
  obtain ⟨v,hv,hAv⟩ := SmallLevelPoleGrid.leading_kernel
    (fun i => (hG i x).meromorphicAt) hpole A R (hA x) hR (fun i => hrow n i x hx)
  refine ⟨v,hv,?_⟩
  funext i
  exact hAv i

/-- A nonzero leading Laurent vector forces determinant zero. -/
theorem det_zero_of_kernel [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hker : ∃ v : ι → ℂ, v≠0 ∧ A *ᵥ v=0) : A.det=0 := by
  by_contra hdet
  have hu : IsUnit A := A.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hu
  obtain ⟨v,hv,hAv⟩ := hker
  apply hv
  apply hi
  simpa using hAv

#print axioms continued_leading_kernel
#print axioms det_zero_of_kernel
end SmallLevelContinuation
end
end

/-! ## SmallLevelEntireHalfplaneModelsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelContinuation
open Complex Filter Set
open scoped Topology

/-- Arbitrarily far-left analytic half-plane representatives remove every
pole of a normal-form meromorphic continuation agreeing initially with F. -/
theorem entire_of_halfplane_models (F G : ℂ → ℂ) (BG B : ℝ)
    (hG : ∀ s, MeromorphicNFAt G s)
    (hGF : ∀ s, BG<s.re → G s=F s)
    (H : ℕ → ℂ → ℂ)
    (hH : ∀ (n : ℕ) s, B-(n:ℝ)<s.re → AnalyticAt ℂ (H n) s)
    (hHF : ∀ (n : ℕ) s, B<s.re → H n s=F s) : Differentiable ℂ G := by
  intro s
  obtain ⟨n,hn⟩ := exists_nat_gt (B-s.re)
  have hs : B-(n:ℝ)<s.re := by linarith
  have he : G=ᶠ[𝓝[≠] s] H n := by
    apply halfplane_germ_identity (B-(n:ℝ)) (max BG B)
    · exact fun z _ => (hG z).meromorphicAt
    · exact fun z hz => (hH n z hz).meromorphicAt
    · intro z hz
      exact (hGF z (lt_of_le_of_lt (le_max_left _ _) hz)).trans
        (hHF n z (lt_of_le_of_lt (le_max_right _ _) hz)).symm
    · exact hs
  have ha := hH n s hs
  have he' := ((hG s).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds ha.meromorphicNFAt).mp he
  exact ((analyticAt_congr he').mpr ha).differentiableAt

#print axioms entire_of_halfplane_models
end SmallLevelContinuation
end
end

/-! ## SmallLevelMellinRemainderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelContinuation

open Complex Filter Set Asymptotics MeasureTheory Matrix
open scoped Topology

/-- A local remainder of order t^(-b), with exponential decay at infinity,
has an analytic Mellin transform in Re(s)>b. Local integrability is retained
explicitly, so a cutoff or a discontinuity cannot silently be ignored. -/
theorem mellin_remainder_analytic {R : ℝ → ℂ} {a b : ℝ} (ha : 0<a)
    (hlocal : LocallyIntegrableOn R (Ioi 0))
    (htop : R=O[atTop] (fun t : ℝ => Real.exp (-a*t)))
    (hzero : R=O[𝓝[>] 0] (fun t : ℝ => t^(-b))) :
    AnalyticOnNhd ℂ (mellin R) {z : ℂ | b<z.re} := by
  have hd : DifferentiableOn ℂ (mellin R) {z : ℂ | b<z.re} := by
    intro z hz
    exact (mellin_differentiableAt_of_isBigO_rpow_exp ha hlocal htop hzero hz).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- The closed-grid theorem with its holomorphic remainder hypothesis
discharged by explicit local Taylor bounds and Mellin integrals. This does
not supply those bounds for a particular Fourier transformation. -/
theorem closed_system_of_mellin_remainders {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℝ) (F : ℂ → ι → ℂ)
    (A : ℂ → Matrix ι ι ℂ) (C : ℕ → ℂ → Matrix ι ι ℂ)
    (R : ℕ → ι → ℝ → ℂ) (a : ℕ → ι → ℝ)
    (hF : ∀ i z, B<z.re → AnalyticAt ℂ (fun w => F w i) z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hd : ∃ y, (A y).det≠0)
    (hC : ∀ m x i j, AnalyticAt ℂ (fun z => C m z i j) x)
    (ha : ∀ n i, 0<a n i)
    (hlocal : ∀ n i, LocallyIntegrableOn (R n i) (Ioi 0))
    (htop : ∀ n i, R n i=O[atTop] (fun t : ℝ => Real.exp (-a n i*t)))
    (hzero : ∀ (n : ℕ) i, R n i=O[𝓝[>] 0] (fun t : ℝ => t^((n:ℝ)+1-B)))
    (hrow : ∀ n z, B<z.re → ∀ i,
      ∑ j, A z i j*F z j=mellin (R n i) z+
        ∑ m ∈ Finset.range n, ∑ j, C m z i j*F (z+((m:ℂ)+1)) j) :
    ∃ G : ℂ → ι → ℂ, (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=F z := by
  apply closed_system_continuation B F A C (fun n z i => mellin (R n i) z)
    hF hA hd hC _ hrow
  intro n i z hz
  apply mellin_remainder_analytic (ha n i) (hlocal n i) (htop n i) _ z hz
  simpa only [neg_sub] using hzero n i

#print axioms mellin_remainder_analytic
#print axioms closed_system_of_mellin_remainders

end SmallLevelContinuation
end
end

/-! ## SmallLevelMeromorphicSourceContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelContinuation

open Complex Filter Set Matrix
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Closed-system continuation allowing meromorphic source terms. This
permits an enlarged grid to use a previously continued smaller grid in its
source rows; no entireness of that smaller grid is required. -/
theorem closed_system_meromorphic_source (B : ℝ) (F : ℂ → ι → ℂ)
    (A : ℂ → Matrix ι ι ℂ) (C : ℕ → ℂ → Matrix ι ι ℂ)
    (H : ℕ → ℂ → ι → ℂ)
    (hF : ∀ i z, B<z.re → AnalyticAt ℂ (fun w => F w i) z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hd : ∃ y, (A y).det≠0)
    (hC : ∀ m x i j, AnalyticAt ℂ (fun z => C m z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → MeromorphicAt (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re → ∀ i,
      ∑ j, A z i j*F z j=H n z i+
        ∑ m ∈ Finset.range n, ∑ j, C m z i j*F (z+((m:ℂ)+1)) j) :
    ∃ G : ℂ → ι → ℂ, (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=F z := by
  have stages : ∀ n : ℕ, ∃ V : ℂ → ι → ℂ,
      (∀ i, MeromorphicNFOn (fun z => V z i) {z : ℂ | B-(n:ℝ)<z.re}) ∧
      ∀ z, B<z.re → V z=F z := by
    intro n
    induction n with
    | zero =>
      refine ⟨F,?_,fun _ _ => rfl⟩
      intro i z hz
      exact (hF i z (by simpa using hz)).meromorphicNFAt
    | succ n ih =>
      obtain ⟨V,hV,heV⟩ := ih
      let R : ℂ → ι → ℂ := fun z i => H n z i+
        ∑ m ∈ Finset.range n, ∑ j, C m z i j*V (z+((m:ℂ)+1)) j
      have hR (i : ι) : MeromorphicOn (fun z => R z i)
          {z : ℂ | B-((n:ℝ)+1)<z.re} := by
        intro x hx
        apply (hH n i x hx).add
        apply MeromorphicAt.fun_sum
        intro m _
        apply MeromorphicAt.fun_sum
        intro j _
        apply (hC m x i j).meromorphicAt.mul
        have hshift : B-(n:ℝ)<(x+((m:ℂ)+1)).re := by
          simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
          change B-((n:ℝ)+1)<x.re at hx
          linarith [Nat.cast_nonneg (α:=ℝ) m]
        exact ((hV j hshift).meromorphicAt).comp_analyticAt
          (g := fun z : ℂ => z+((m:ℂ)+1)) (by fun_prop)
      have he : ∀ z, B<z.re → A z *ᵥ V z=R z := by
        intro z hz
        funext i
        change (∑ j, A z i j*V z j)=_
        rw [heV z hz,hrow n z hz i]
        change H n z i+_=H n z i+_
        congr 1
        apply Finset.sum_congr rfl
        intro m _
        have hs : B<(z+((m:ℂ)+1)).re := by
          simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
          linarith [Nat.cast_nonneg (α:=ℝ) m]
        rw [heV _ hs]
      obtain ⟨W,hW,heW,_⟩ := matrix_halfplane_extension
        (B-((n:ℝ)+1)) (B-(n:ℝ)) B (by linarith) A R V hA hd hR hV he
      refine ⟨W,?_,?_⟩
      · simpa only [Nat.cast_succ] using hW
      · intro z hz
        exact (heW z (by linarith [Nat.cast_nonneg (α:=ℝ) n])).trans (heV z hz)
  have hcoord (i : ι) : ∃ G : ℂ → ℂ, (∀ x, MeromorphicNFAt G x) ∧
      EqOn G (fun z => F z i) {z : ℂ | B<z.re} := by
    apply halfplane_glue B (fun z => F z i)
    intro n
    obtain ⟨V,hV,heV⟩ := stages n
    exact ⟨fun z => V z i,hV i,fun z hz => congrFun (heV z hz) i⟩
  choose G hG heG using hcoord
  refine ⟨fun z i => G i z,hG,?_⟩
  intro z hz
  funext i
  exact heG i hz

#print axioms closed_system_meromorphic_source

end SmallLevelContinuation
end
end

/-! ## SmallLevelRectangularContinuedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelContinuation
open Complex Filter Set Matrix
open scoped Topology
variable {ι ρ : Type*} [Fintype ι]

/-- A rectangular family of original Taylor equations continues as germs.
The row index need not have the same size as the additive grid. -/
theorem rectangular_continued_rows (B : ℝ) (F G : ℂ→ι→ℂ)
    (A : ℂ→Matrix ρ ι ℂ) (C : ℕ→ℂ→Matrix ρ ι ℂ) (H : ℕ→ℂ→ρ→ℂ)
    (hG : ∀ i x,MeromorphicAt (fun z => G z i) x)
    (hGF : ∀ z,B<z.re → G z=F z)
    (hA : ∀ x i j,AnalyticAt ℂ (fun z => A z i j) x)
    (hC : ∀ n x i j,AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z,B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hrow : ∀ n z,B<z.re →
      A z *ᵥ F z=H n z+∑ m∈Finset.range n,C m z *ᵥ F (z+((m:ℂ)+1)))
    (n : ℕ) (i : ρ) (x : ℂ) (hx : B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j,A z i j*G z j)=ᶠ[𝓝[≠] x]
      (fun z => H n z i+∑ m∈Finset.range n,∑ j,C m z i j*G (z+((m:ℂ)+1)) j) := by
  apply halfplane_germ_identity (B-((n:ℝ)+1)) B _ _ _ x hx
  · intro z _
    exact MeromorphicAt.fun_sum (fun j _ => (hA z i j).meromorphicAt.mul (hG j z))
  · intro z hz
    apply (hH n i z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro m _
    apply MeromorphicAt.fun_sum
    intro j _
    exact (hC m z i j).meromorphicAt.mul
      ((hG j (z+((m:ℂ)+1))).comp_analyticAt (g:=fun w : ℂ => w+((m:ℂ)+1)) (by fun_prop))
  · intro z hz
    dsimp only
    change B<z.re at hz
    have he:=congrFun (hrow n z hz) i
    simp only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] at he
    rw [hGF z hz,he]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    have hs : B<(z+((m:ℂ)+1)).re := by
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) m]
    rw [hGF _ hs]

#print axioms rectangular_continued_rows
end SmallLevelContinuation
end
end
