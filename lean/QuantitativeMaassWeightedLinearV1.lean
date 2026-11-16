module

public import QuantitativeMaassSmoothEigenSpaceV1
public import QuantitativeMaassEulerL2InjectiveV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

/-- Literal multiplication by the fixed capped weight and restriction to the
translation strip, before passage to almost-everywhere classes. -/
def weightedStripMap (ε : ℝ) (t : ℕ) : ((ℝ×ℝ) → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := AsymptoticMassTransport.strip.indicator
    (fun z : ℍ => (((min (z.im/ε) 1)^t:ℝ):ℂ)*f (z.re,z.im))
  map_add' f g := by
    funext z
    classical
    by_cases hz : z∈AsymptoticMassTransport.strip <;> simp [hz,mul_add]
  map_smul' c f := by
    funext z
    classical
    by_cases hz : z∈AsymptoticMassTransport.strip <;> simp [hz,mul_left_comm]

theorem weightedStripMap_eq_section (ε : ℝ) (t : ℕ) (f : (ℝ×ℝ) → ℂ) :
    weightedStripMap ε t f=AsymptoticWeightedBranches.stripSection ε t 0 (fun z => f (z.re,z.im)) := by
  funext z
  change AsymptoticMassTransport.strip.indicator
    (fun z : ℍ => (((min (z.im/ε) 1)^t:ℝ):ℂ)*f (z.re,z.im)) z=
      AsymptoticMassTransport.strip.indicator
        (AsymptoticWeightedBranches.weighted ε t 0 (fun z => f (z.re,z.im))) z
  classical
  by_cases hz : z∈AsymptoticMassTransport.strip
  · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz]
    simp only [AsymptoticWeightedBranches.weighted,pow_zero,mul_one]
    rfl
  · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]

/-- The actual smooth, horizontally analytic functions for which the fixed
weighted strip square norm is finite form a vector space. -/
def weightedAnalyticSpace (ε : ℝ) (t : ℕ) : Submodule ℂ ((ℝ×ℝ) → ℂ) where
  carrier := {f | f∈smoothUpperSpace ∧
    (∀ y : ℝ,0<y → AnalyticOnNhd ℝ (fun x => f (x,y)) univ) ∧
    MemLp (weightedStripMap ε t f) 2 volume}
  zero_mem' := ⟨smoothUpperSpace.zero_mem,fun _ _ => analyticOnNhd_const,by simp⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨smoothUpperSpace.add_mem hf.1 hg.1,fun y hy => (hf.2.1 y hy).add (hg.2.1 y hy),?_⟩
    rw [map_add]
    exact hf.2.2.add hg.2.2
  smul_mem' := by
    intro c f hf
    refine ⟨smoothUpperSpace.smul_mem c hf.1,?_,?_⟩
    · intro y hy
      change AnalyticOnNhd ℝ (fun x => c*f (x,y)) univ
      exact analyticOnNhd_const.mul (hf.2.1 y hy)
    · rw [map_smul]
      exact hf.2.2.const_smul c

def weightedAnalyticForget (ε : ℝ) (t : ℕ) : weightedAnalyticSpace ε t →ₗ[ℂ] smoothUpperSpace where
  toFun f := ⟨f.val,f.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal weighted Hilbert embedding, with its linearity proved on the
actual analytic function domain. -/
def weightedAnalyticLp (ε : ℝ) (t : ℕ) : weightedAnalyticSpace ε t →ₗ[ℂ] AsymptoticHyperbolicSlash.Space where
  toFun f := f.property.2.2.toLp (weightedStripMap ε t f.val)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (f+g).property.2.2,MemLp.coeFn_toLp f.property.2.2,
      MemLp.coeFn_toLp g.property.2.2,Lp.coeFn_add (f.property.2.2.toLp _) (g.property.2.2.toLp _)] with z hfg hf hg ha
    rw [hfg,ha]
    change weightedStripMap ε t (f+g).val z=
      f.property.2.2.toLp _ z+g.property.2.2.toLp _ z
    rw [hf,hg]
    exact congrFun (map_add (weightedStripMap ε t) f.val g.val) z
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (c•f).property.2.2,MemLp.coeFn_toLp f.property.2.2,
      Lp.coeFn_smul c (f.property.2.2.toLp _)] with z hcf hf hs
    simp only [RingHom.id_apply]
    rw [hcf,hs]
    change weightedStripMap ε t (c•f).val z=c*(f.property.2.2.toLp _ z)
    rw [hf]
    exact congrFun (map_smul (weightedStripMap ε t) c f.val) z

theorem weightedAnalyticLp_coeFn (ε : ℝ) (t : ℕ) (f : weightedAnalyticSpace ε t) :
    weightedAnalyticLp ε t f =ᵐ[volume] weightedStripMap ε t f.val := MemLp.coeFn_toLp f.property.2.2

/-- No linearly independent analytic waves are lost in the fixed weighted
Hilbert realization. This applies uniformly across different eigenvalues. -/
theorem weightedAnalyticLp_injective (ε : ℝ) (hε : 0<ε) (t : ℕ) :
    Function.Injective (weightedAnalyticLp ε t) := by
  intro f g he
  have hae := (weightedAnalyticLp_coeFn ε t f).symm.trans (he ▸ weightedAnalyticLp_coeFn ε t g)
  rw [weightedStripMap_eq_section,weightedStripMap_eq_section] at hae
  have hfc : Continuous (fun z : ℍ => f.val (z.re,z.im)) :=
    f.property.1.1.continuousOn.comp_continuous (continuous_re.prodMk continuous_im) (fun z => z.im_pos)
  have hgc : Continuous (fun z : ℍ => g.val (z.re,z.im)) :=
    g.property.1.1.continuousOn.comp_continuous (continuous_re.prodMk continuous_im) (fun z => z.im_pos)
  have hstrip := weighted_strip_ae_eq_open ε hε t _ _ hfc hgc hae
  apply Subtype.ext
  funext z
  by_cases hz : 0<z.2
  · have hlocal : (fun x : ℝ => f.val (x,z.2)) =ᶠ[𝓝 (1/2:ℝ)] (fun x => g.val (x,z.2)) := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)] with x hx
      exact hstrip ⟨⟨x,z.2⟩,hz⟩ hx.1 hx.2
    exact congrFun ((f.property.2.1 z.2 hz).eq_of_eventuallyEq (g.property.2.1 z.2 hz) hlocal) z.1
  · rw [f.property.1.2 z (le_of_not_gt hz),g.property.1.2 z (le_of_not_gt hz)]

#print axioms weightedStripMap
#print axioms weightedAnalyticSpace
#print axioms weightedAnalyticLp
#print axioms weightedAnalyticLp_injective

end QuantitativeMaass
