module

public import SmallLevelContinuationTheoryV4
public import SmallLevelSimplePoleCancellationV1
public import SmallLevelTaylorRowCoefficientsV1
public import SmallLevelTaylorRowNormalizationV1

/-! Consolidated chapter: SmallLevelSimplePoleTaylor. Original declarations and local scopes are retained. -/

/-! ## SmallLevelSimplePoleTaylorGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelSimplePoleTaylor
open Complex Filter Set SmallLevelTaylor
open scoped Topology

/-- Positive Taylor terms cancel a permitted simple weight pole. The
zero-order term is regular whenever the base point differs from the weight. -/
theorem term_extension (k n : ℕ) (G : ℂ → ℂ)
    (hG : ∀ z, MeromorphicAt G z)
    (hGa : ∀ z, z≠(k:ℂ) → AnalyticAt ℂ G z)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (x : ℂ) (hx : x≠(k:ℂ)) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R x ∧
      (fun z => Ring.choose (z+(n:ℂ)-(k:ℂ)) n*G (z+n))=ᶠ[𝓝[≠] x] R := by
  have hc := binomial_shift_analytic k n x
  by_cases hs : x+(n:ℂ)=(k:ℂ)
  · have hn : 0<n := by
      by_contra hn
      have hn0 : n=0 := by omega
      simp only [hn0,Nat.cast_zero,add_zero] at hs
      exact hx hs
    apply SmallLevelFiniteShift.simple_pole_cancellation _ _ x hc
    · rw [hs,sub_self,Ring.choose_zero_pos ℂ hn]
    · exact (hG (x+n)).comp_analyticAt (g:=fun z : ℂ => z+n) (analyticAt_id.add analyticAt_const)
    · change (-1:WithTop ℤ)≤meromorphicOrderAt (G ∘ (fun z : ℂ => z+n)) x
      rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt,hs]
      exact hGo
  · exact ⟨_,hc.mul ((hGa _ hs).comp (f:=fun z : ℂ => z+n)
      (analyticAt_id.add analyticAt_const)),Filter.EventuallyEq.rfl⟩

/-- A meromorphic half-plane model with a removable germ at one point
transfers that regularity to a normal-form continuation. -/
theorem analyticAt_of_model (F G H R : ℂ → ℂ) (BG B b : ℝ) (x : ℂ)
    (hG : ∀ z, MeromorphicNFAt G z)
    (hGF : ∀ z, BG<z.re → G z=F z)
    (hH : ∀ z, b<z.re → MeromorphicAt H z)
    (hHF : ∀ z, B<z.re → H z=F z) (hx : b<x.re)
    (hR : AnalyticAt ℂ R x) (he : H=ᶠ[𝓝[≠] x] R) : AnalyticAt ℂ G x := by
  have hGH : G=ᶠ[𝓝[≠] x] H := by
    apply SmallLevelContinuation.halfplane_germ_identity b (max BG B)
    · exact fun z _ => (hG z).meromorphicAt
    · exact hH
    · intro z hz
      exact (hGF z (lt_of_le_of_lt (le_max_left _ _) hz)).trans
        (hHF z (lt_of_le_of_lt (le_max_right _ _) hz)).symm
    · exact hx
  have heq := ((hG x).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hR.meromorphicNFAt).mp (hGH.trans he)
  exact (analyticAt_congr heq).mpr hR

#print axioms term_extension
#print axioms analyticAt_of_model
end SmallLevelSimplePoleTaylor
end
end

/-! ## SmallLevelHalfplaneGermRegularityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelSimplePoleTaylor
open Complex Filter Set
open scoped Topology

/-- Removable germs in successively larger half-plane models transfer to
an initially equal normal-form continuation. -/
theorem analyticAt_of_halfplane_germs (F G : ℂ→ℂ) (BG B : ℝ)
    (H : ℕ→ℂ→ℂ) (x : ℂ) (hG : ∀ s, MeromorphicNFAt G s)
    (hGF : ∀ s, BG<s.re → G s=F s)
    (hH : ∀ (M : ℕ) s, B-(M:ℝ)<s.re → MeromorphicAt (H M) s)
    (hHF : ∀ (M : ℕ) s, B<s.re → H M s=F s)
    (hHR : ∀ M : ℕ, B-(M:ℝ)<x.re →
      ∃ R : ℂ→ℂ, AnalyticAt ℂ R x ∧ H M=ᶠ[𝓝[≠] x] R) :
    AnalyticAt ℂ G x := by
  obtain ⟨M,hM⟩:=exists_nat_gt (B-x.re)
  have hx : B-(M:ℝ)<x.re := by linarith
  obtain ⟨R,hR,he⟩:=hHR M hx
  exact analyticAt_of_model F G (H M) R BG B (B-(M:ℝ)) x
    hG hGF (hH M) (hHF M) hx hR he

#print axioms analyticAt_of_halfplane_germs
end SmallLevelSimplePoleTaylor
end
end

/-! ## SmallLevelSimplePolePartnerModelsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelSimplePoleTaylor
open Complex Set Filter MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

/-- A Fricke partner with at most a simple pole at the weight gives
meromorphic half-plane models, each with a removable germ away from that weight. -/
theorem partner_models {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) (hk : Even k) {a : ℕ→ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (χ : ℂ) (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z)))
    (BG : ℝ) (G : ℂ→ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (hGF : ∀ s, BG<s.re → G s=transform a (-1/(L*r)) s) :
    ∃ (B : ℝ) (H : ℕ→ℂ→ℂ),
      (∀ (M : ℕ) (s : ℂ), B-(M:ℝ)<s.re → MeromorphicAt (H M) s) ∧
      (∀ (M : ℕ) (s : ℂ), B<s.re → H M s=transform a r s) ∧
      (∀ (M : ℕ) (s : ℂ), B-(M:ℝ)<s.re → s≠(k:ℂ) →
        ∃ R : ℂ→ℂ, AnalyticAt ℂ R s ∧ H M=ᶠ[𝓝[≠] s] R) := by
  obtain ⟨B,hB⟩:=normalized_taylor_mellin_rows hL hr k hk ha ha0 χ hF
  let V : ℕ→ℂ→ℂ := fun M s => ∑ n∈Finset.range M,
    (I*(L:ℂ)*(r:ℂ))^n*Ring.choose (s+(n:ℂ)-(k:ℂ)) n*G (s+n)
  let P : ℂ→ℂ := fun s => χ*((L*r^2:ℝ):ℂ)^(s-(k:ℂ)/2)
  have hP (s : ℂ) : AnalyticAt ℂ P s := by
    have hn : ((L*r^2:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (mul_ne_zero hL.ne' (pow_ne_zero 2 hr))
    dsimp [P]
    simp_rw [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  have hV (M : ℕ) (s : ℂ) : MeromorphicAt (V M) s := by
    apply MeromorphicAt.fun_sum
    intro n _
    exact ((analyticAt_const.mul (binomial_shift_analytic k n s)).meromorphicAt).mul
      ((hG (s+n)).comp_analyticAt (g:=fun z : ℂ => z+n) (analyticAt_id.add analyticAt_const))
  have hVR (M : ℕ) (s : ℂ) (hs : s≠(k:ℂ)) :
      ∃ R : ℂ→ℂ, AnalyticAt ℂ R s ∧ V M=ᶠ[𝓝[≠] s] R := by
    induction M with
    | zero =>
      refine ⟨fun _ => 0,analyticAt_const,?_⟩
      filter_upwards with z
      simp [V]
    | succ M ih =>
      obtain ⟨R,hR,he⟩:=ih
      obtain ⟨T,hT,ht⟩:=term_extension k M G hG hGa hGo s hs
      refine ⟨fun z => R z+(I*(L:ℂ)*(r:ℂ))^M*T z,hR.add (analyticAt_const.mul hT),?_⟩
      filter_upwards [he,ht] with z hz hz'
      dsimp only [V] at hz ⊢
      rw [Finset.sum_range_succ,hz,mul_assoc,hz']
  have hVF (M : ℕ) (s : ℂ) (hs : BG<s.re) :
      V M s=normalizedTaylorSum k a L r M s := by
    unfold V normalizedTaylorSum
    apply Finset.sum_congr rfl
    intro n _
    have hn : BG<(s+(n:ℂ)).re := by
      simp only [Complex.add_re,Complex.natCast_re]
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [hGF _ hn]
  let H : ℕ→ℂ→ℂ := fun M s => mellin (frickeError k a L r χ M) s+P s*V M s
  refine ⟨max B BG,H,?_,?_,?_⟩
  · intro M s hs
    have hb : B-(M:ℝ)<s.re := by linarith [le_max_left B BG]
    exact (((hB M).1 s hb).meromorphicAt).add ((hP s).meromorphicAt.mul (hV M s))
  · intro M s hs
    dsimp [H]
    rw [hVF M s (lt_of_le_of_lt (le_max_right _ _) hs)]
    have he := (hB M).2 s (lt_of_le_of_lt (le_max_left _ _) hs)
    dsimp [P]
    exact (sub_eq_iff_eq_add.mp he).symm
  · intro M s hs hsk
    obtain ⟨R,hR,he⟩:=hVR M s hsk
    have hb : B-(M:ℝ)<s.re := by linarith [le_max_left B BG]
    refine ⟨fun z => mellin (frickeError k a L r χ M) z+P z*R z,
      ((hB M).1 s hb).add ((hP s).mul hR),?_⟩
    filter_upwards [he] with z hz
    dsimp [H]
    rw [hz]

#print axioms partner_models
end SmallLevelSimplePoleTaylor
end
end
