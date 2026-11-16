module

public import QuantitativeMaassWeightedLinearV1
public import AsymptoticClassicalPeterssonMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology

namespace QuantitativeMaass

def upperFunctionLinear : ((ℝ×ℝ) → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun := upperFunction
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Smooth horizontally analytic functions with finite actual quotient norm. -/
def quotientAnalyticSpace (N : ℕ) : Submodule ℂ ((ℝ×ℝ) → ℂ) where
  carrier := {f | f∈smoothUpperSpace ∧
    (∀ y : ℝ,0<y → AnalyticOnNhd ℝ (fun x => f (x,y)) univ) ∧
    MemLp (upperFunctionLinear f) 2 (AsymptoticClassicalPetersson.quotientMeasure N)}
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

def quotientAnalyticForget (N : ℕ) : quotientAnalyticSpace N →ₗ[ℂ] smoothUpperSpace where
  toFun f := ⟨f.val,f.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal quotient Hilbert embedding on the analytic function domain. -/
def quotientAnalyticLp (N : ℕ) : quotientAnalyticSpace N →ₗ[ℂ] Lp ℂ 2 (AsymptoticClassicalPetersson.quotientMeasure N) where
  toFun f := f.property.2.2.toLp (upperFunctionLinear f.val)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (f+g).property.2.2,MemLp.coeFn_toLp f.property.2.2,
      MemLp.coeFn_toLp g.property.2.2,Lp.coeFn_add (f.property.2.2.toLp _) (g.property.2.2.toLp _)] with z hfg hf hg ha
    rw [hfg,ha]
    change upperFunctionLinear (f+g).val z=
      f.property.2.2.toLp _ z+g.property.2.2.toLp _ z
    rw [hf,hg]
    exact congrFun (map_add (upperFunctionLinear) f.val g.val) z
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (c•f).property.2.2,MemLp.coeFn_toLp f.property.2.2,
      Lp.coeFn_smul c (f.property.2.2.toLp _)] with z hcf hf hs
    simp only [RingHom.id_apply]
    rw [hcf,hs]
    change upperFunctionLinear (c•f).val z=c*(f.property.2.2.toLp _ z)
    rw [hf]
    exact congrFun (map_smul (upperFunctionLinear) c f.val) z

theorem quotientAnalyticLp_coeFn (N : ℕ) (f : quotientAnalyticSpace N) :
    quotientAnalyticLp N f =ᵐ[AsymptoticClassicalPetersson.quotientMeasure N] upperFunctionLinear f.val := MemLp.coeFn_toLp f.property.2.2

/-- Positive orbit density on the open strip and horizontal analyticity
make the actual quotient embedding injective, including across eigenvalues. -/
theorem quotientAnalyticLp_injective (N : ℕ) : Function.Injective (quotientAnalyticLp N) := by
  intro f g he
  have hae := (quotientAnalyticLp_coeFn N f).symm.trans (he ▸ quotientAnalyticLp_coeFn N g)
  have hstripae := AsymptoticClassicalPetersson.ae_strip_of_ae N hae
  have hweighted : AsymptoticWeightedBranches.stripSection 1 0 0 (fun z => f.val (z.re,z.im)) =ᵐ[volume]
      AsymptoticWeightedBranches.stripSection 1 0 0 (fun z => g.val (z.re,z.im)) := by
    filter_upwards [hstripae] with z hz
    classical
    by_cases hs : z∈AsymptoticMassTransport.strip
    · simpa only [AsymptoticWeightedBranches.stripSection,Set.indicator_of_mem hs,
        AsymptoticWeightedBranches.weighted,pow_zero,Complex.ofReal_one,one_mul,
        upperFunctionLinear,LinearMap.coe_mk,AddHom.coe_mk,upperFunction,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] using hz hs
    · simp only [AsymptoticWeightedBranches.stripSection,Set.indicator_of_notMem hs]
  have hfc : Continuous (fun z : ℍ => f.val (z.re,z.im)) :=
    f.property.1.1.continuousOn.comp_continuous (continuous_re.prodMk continuous_im) (fun z => z.im_pos)
  have hgc : Continuous (fun z : ℍ => g.val (z.re,z.im)) :=
    g.property.1.1.continuousOn.comp_continuous (continuous_re.prodMk continuous_im) (fun z => z.im_pos)
  have hstrip := weighted_strip_ae_eq_open 1 (by norm_num) 0 _ _ hfc hgc hweighted
  apply Subtype.ext
  funext z
  by_cases hz : 0<z.2
  · have hlocal : (fun x : ℝ => f.val (x,z.2)) =ᶠ[𝓝 (1/2:ℝ)] (fun x => g.val (x,z.2)) := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)] with x hx
      exact hstrip ⟨⟨x,z.2⟩,hz⟩ hx.1 hx.2
    exact congrFun ((f.property.2.1 z.2 hz).eq_of_eventuallyEq (g.property.2.1 z.2 hz) hlocal) z.1
  · rw [f.property.1.2 z (le_of_not_gt hz),g.property.1.2 z (le_of_not_gt hz)]

#print axioms upperFunctionLinear
#print axioms quotientAnalyticSpace
#print axioms quotientAnalyticLp
#print axioms quotientAnalyticLp_injective

end QuantitativeMaass
