module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.MellinTransform
public import SmallLevelAdditiveMellinV1
public import SmallLevelContinuationTheoryV4
public import SmallLevelTranslatedRayDecayV1

/-! Consolidated chapter: SmallLevelMellinEndpoint. Original declarations and local scopes are retained. -/

/-! ## SmallLevelMellinEndpointResidueV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelMellinEndpoint
open Complex Filter Asymptotics Set MeasureTheory
open scoped Topology

def step (L : ℂ) : ℝ→ℂ := (Ioc 0 1).indicator (fun _ => L)
def remainder (g : ℝ→ℂ) (L : ℂ) (t : ℝ) : ℂ := g t-step L t

theorem step_mellin (L : ℂ) {s : ℂ} (hs : 0<s.re) : HasMellin (step L) s (L/s) := by
  have hh:=hasMellin_one_Ioc hs
  have he : step L=(fun t : ℝ => L • (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) t) := by
    funext t
    simp only [step,Set.indicator]
    split_ifs <;> simp
  rw [he]
  simpa only [hh.2,smul_eq_mul,mul_one_div] using hasMellin_const_smul hh.1 L

/-- Subtracting the constant endpoint isolates its simple Mellin pole.
The hypotheses are estimates on the explicit remainder, not pole claims. -/
theorem mellin_decomposition (g : ℝ→ℂ) (L : ℂ)
    (hlocal : LocallyIntegrableOn (remainder g L) (Ioi 0))
    (htop : remainder g L =O[atTop] (fun t : ℝ => t^(-1:ℝ)))
    (hzero : remainder g L =O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)))
    {s : ℂ} (hs0 : 0<s.re) (hs1 : s.re<1) :
    mellin g s=L/s+mellin (remainder g L) s := by
  have hr : MellinConvergent (remainder g L) s :=
    mellinConvergent_of_isBigO_rpow hlocal htop hs1
      (by simpa only [neg_neg] using hzero) (by linarith : (-1:ℝ)<s.re)
  have hl:=step_mellin L hs0
  have he : (fun t => step L t+remainder g L t)=g := by
    funext t
    simp [remainder]
  have hh:=(hasMellin_add hl.1 hr).2
  rw [he,hl.2] at hh
  exact hh

theorem remainder_continuous (g : ℝ→ℂ) (L : ℂ)
    (hlocal : LocallyIntegrableOn (remainder g L) (Ioi 0))
    (htop : remainder g L =O[atTop] (fun t : ℝ => t^(-1:ℝ)))
    (hzero : remainder g L =O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ))) :
    ContinuousAt (mellin (remainder g L)) 0 := by
  apply DifferentiableAt.continuousAt (𝕜:=ℂ)
  exact mellin_differentiableAt_of_isBigO_rpow hlocal htop (by norm_num : (0:ℂ).re<1)
    (by simpa only [neg_neg] using hzero) (by norm_num : (-1:ℝ)<(0:ℂ).re)

/-- A continuation regular at zero forces a constant endpoint to vanish,
once the explicit remainder has one positive power of decay at zero. -/
theorem endpoint_zero_of_regular (g : ℝ→ℂ) (L : ℂ) (A : ℂ→ℂ)
    (hlocal : LocallyIntegrableOn (remainder g L) (Ioi 0))
    (htop : remainder g L =O[atTop] (fun t : ℝ => t^(-1:ℝ)))
    (hzero : remainder g L =O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)))
    (hA : ContinuousAt A 0)
    (hagrees : ∀ s : ℂ, 0<s.re → s.re<1 → A s=mellin g s) : L=0 := by
  have hr:=remainder_continuous g L hlocal htop hzero
  have hpath : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun t : ℝ => (t:ℂ)*(A t-mellin (remainder g L) t))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def,zero_mul] using hpath.mul ((hA.tendsto.comp hpath).sub (hr.tendsto.comp hpath))
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, (t:ℂ)*(A t-mellin (remainder g L) t)=L := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono
      nhdsWithin_le_nhds] with t ht0 ht1
    have ht0' : 0<t:=ht0
    rw [hagrees t (by simpa using ht0') (by simpa using ht1),
      mellin_decomposition g L hlocal htop hzero (by simpa using ht0') (by simpa using ht1)]
    have hn : (t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ht0'.ne'
    field_simp [hn]
    ring
  exact (tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds).symm

#print axioms mellin_decomposition
#print axioms endpoint_zero_of_regular
end SmallLevelMellinEndpoint
end
end

/-! ## SmallLevelMellinEndpointContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelMellinEndpoint
open Complex Filter Asymptotics Set MeasureTheory
open scoped Topology

theorem remainder_analytic (g : ℝ→ℂ) (L : ℂ)
    (hlocal : LocallyIntegrableOn (remainder g L) (Ioi 0))
    (htop : ∀ r : ℝ,remainder g L =O[atTop] (fun t : ℝ => t^r))
    (hzero : remainder g L =O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ))) :
    AnalyticOnNhd ℂ (mellin (remainder g L)) {s : ℂ | -1<s.re} := by
  have hd : DifferentiableOn ℂ (mellin (remainder g L)) {s : ℂ | -1<s.re} := by
    intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow hlocal (htop (-(s.re+1))) (by linarith)
      (by simpa only [neg_neg] using hzero) hs).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem decomposition_rapid (g : ℝ→ℂ) (L : ℂ)
    (hlocal : LocallyIntegrableOn (remainder g L) (Ioi 0))
    (htop : ∀ r : ℝ,remainder g L =O[atTop] (fun t : ℝ => t^r))
    (hzero : remainder g L =O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)))
    {s : ℂ} (hs : 0<s.re) : mellin g s=L/s+mellin (remainder g L) s := by
  have hr : MellinConvergent (remainder g L) s :=
    mellinConvergent_of_isBigO_rpow hlocal (htop (-(s.re+1))) (by linarith)
      (by simpa only [neg_neg] using hzero) (by linarith : (-1:ℝ)<s.re)
  have hl:=step_mellin L hs
  have he : (fun t => step L t+remainder g L t)=g := by funext t; simp [remainder]
  have hh:=(hasMellin_add hl.1 hr).2
  rw [he,hl.2] at hh
  exact hh

/-- Initial half-plane agreement suffices: meromorphic uniqueness transports
the endpoint residue to zero. No agreement near zero is assumed. -/
theorem endpoint_zero_of_continuation (g : ℝ→ℂ) (L : ℂ) (A : ℂ→ℂ) (B : ℝ)
    (hlocal : LocallyIntegrableOn (remainder g L) (Ioi 0))
    (htop : ∀ r : ℝ,remainder g L =O[atTop] (fun t : ℝ => t^r))
    (hzero : remainder g L =O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)))
    (hmer : ∀ s,MeromorphicAt A s) (hA : ContinuousAt A 0)
    (hagrees : ∀ s : ℂ,B<s.re → A s=mellin g s) : L=0 := by
  have hR:=remainder_analytic g L hlocal htop hzero
  have he : (fun s : ℂ => s*A s)=ᶠ[𝓝[≠] 0]
      (fun s : ℂ => L+s*mellin (remainder g L) s) := by
    apply SmallLevelContinuation.halfplane_germ_identity (-1) (max B 0)
    · intro s _
      exact (analyticAt_id.meromorphicAt).mul (hmer s)
    · intro s hs
      exact (analyticAt_const.add (analyticAt_id.mul (hR s hs))).meromorphicAt
    · intro s hs
      dsimp only
      have hs0 : 0<s.re:=(le_max_right B 0).trans_lt hs
      rw [hagrees s ((le_max_left B 0).trans_lt hs),decomposition_rapid g L hlocal htop hzero hs0]
      have hn : s≠0:=by intro h; simp [h] at hs0
      field_simp [hn]
    · norm_num
  have hleft : ContinuousAt (fun s : ℂ => s*A s) 0:=continuousAt_id.mul hA
  have hright : ContinuousAt (fun s : ℂ => L+s*mellin (remainder g L) s) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hR 0 (by norm_num)).continuousAt)
  have hh:=tendsto_nhds_unique
    ((hleft.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
    (hright.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [zero_mul,add_zero] using hh.symm

#print axioms endpoint_zero_of_continuation
end SmallLevelMellinEndpoint
end
end

/-! ## SmallLevelMellinFourierEndpointV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelMellinEndpoint
open Complex Filter Asymptotics Set MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

def ray (a : ℕ→ℂ) (r : ℝ) (t : ℝ) : ℂ := fourier a ((r:ℂ)+(t:ℂ)*Complex.I)

theorem ray_local {a : ℕ→ℂ} (ha : PolynomialBound a) (r : ℝ) :
    LocallyIntegrableOn (ray a r) (Ioi 0) := by
  have hc : ContinuousOn (ray a r) (Ioi 0) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact (FinitenessFourierConstruction.holomorphic ha (by simpa using ht)).continuousAt.comp
      (by fun_prop)
  exact hc.locallyIntegrableOn measurableSet_Ioi

theorem step_integrable (L : ℂ) : Integrable (step L) := by
  rw [step,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by simp [Real.volume_Ioc])

theorem ray_remainder_local {a : ℕ→ℂ} (ha : PolynomialBound a) (r : ℝ) (L : ℂ) :
    LocallyIntegrableOn (remainder (ray a r) L) (Ioi 0) :=
  (ray_local ha r).sub ((step_integrable L).locallyIntegrable.locallyIntegrableOn (Ioi 0))

theorem ray_remainder_rapid {a : ℕ→ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (r : ℝ) (L : ℂ) (s : ℝ) : remainder (ray a r) L =O[atTop] (fun t : ℝ => t^s) := by
  have hh:=SmallLevelTranslatedRay.weighted_rapid ha ha0 0 r s
  simp only [pow_zero,one_mul] at hh
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2:ℝ)] with t ht
  have hn : t∉Ioc (0:ℝ) 1:=by intro h; linarith [h.2]
  simp only [remainder,step,indicator_of_notMem hn,sub_zero,ray]

theorem remainder_first_order {g : ℝ→ℂ} {L : ℂ}
    (h : (fun t => g t-L)=O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ))) :
    remainder g L =O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)) := by
  apply h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht0 ht1
  have ht : t∈Ioc (0:ℝ) 1:=⟨ht0,ht1.le⟩
  simp only [remainder,step,indicator_of_mem ht]

/-- For a polynomially bounded Fourier sequence, regularity at zero of an
initially equal additive continuation excludes a nonzero constant endpoint. -/
theorem fourier_endpoint_zero {a : ℕ→ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (r : ℝ) (L : ℂ) (A : ℂ→ℂ) (B : ℝ)
    (hzero : (fun t => ray a r t-L)=O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)))
    (hmer : ∀ s,MeromorphicAt A s) (hA : ContinuousAt A 0)
    (hagrees : ∀ s : ℂ,B<s.re → A s=SmallLevelAdditive.transform a r s) : L=0 := by
  obtain ⟨C,hC⟩:=SmallLevelAdditive.common_halfplane ha ha0
  apply endpoint_zero_of_continuation (ray a r) L A (max B C)
    (ray_remainder_local ha r L) (ray_remainder_rapid ha ha0 r L)
    (remainder_first_order hzero) hmer hA
  intro s hs
  rw [hagrees s ((le_max_left B C).trans_lt hs)]
  exact ((hC r s ((le_max_right B C).trans_lt hs)).2).symm

#print axioms ray_remainder_local
#print axioms fourier_endpoint_zero
end SmallLevelMellinEndpoint
end
end
