module

public import QuantitativeMaassCuspLogConstantV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

theorem localHalfDensity_map_complex_smul (w A B : ℝ) (hw : 0<w) (z : ℂ)
    (f : Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B)))) :
    localHalfDensity w A B hw (z • f)=z • localHalfDensity w A B hw f := by
  have hz : ((z • f : Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B)))) : ℝ → ℂ)
      =ᵐ[heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B))]
      fun y => z*f y := by
    filter_upwards [Lp.coeFn_smul z f] with y hy
    exact hy
  have h := localHalfDensity_representative_ae w A B hw (z • f) (fun y => z*f y) hz
  apply Lp.ext
  filter_upwards [h,localHalfDensity_ae w A B hw f,
    Lp.coeFn_smul z (localHalfDensity w A B hw f)] with x h1 h2 h3
  rw [h1,h3,Pi.smul_apply,h2,smul_eq_mul]
  ring

/-- The constructed half-density map is complex-linear; the underlying
bounded real map arose only from Mathlib's change-of-measure interface. -/
def localHalfDensityComplex (w A B : ℝ) (hw : 0<w) :
    Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B))) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Icc A B)) where
  toFun := localHalfDensity w A B hw
  map_add' := (localHalfDensity w A B hw).map_add
  map_smul' z f := localHalfDensity_map_complex_smul w A B hw z f
  cont := (localHalfDensity w A B hw).continuous

/-- The actual local cusp constant-term map, as a bounded complex-linear operator. -/
def cuspLogConstantComplex (N : ℕ) (hN : 0<N) (s : SL(2,ℤ)) (A B : ℝ) :
    AutomorphicSpace N →L[ℂ] Lp ℂ 2 (volume.restrict (Icc A B)) :=
  (localHalfDensityComplex N A B (Nat.cast_pos.mpr hN)).comp
    (cuspConstantLocal N s (Real.exp A) (Real.exp B) (Real.exp_pos A))

theorem cuspLogConstantComplex_apply (N : ℕ) (hN : 0<N) (s : SL(2,ℤ)) (A B : ℝ)
    (f : AutomorphicSpace N) :
    cuspLogConstantComplex N hN s A B f=cuspLogConstant N hN s A B f := rfl

/-- The actual geometric all-cusp kernel in the quotient Hilbert space. -/
def localCuspidalSpace (N : ℕ) (hN : 0<N) : Submodule ℂ (AutomorphicSpace N) :=
  ⨅ s : SL(2,ℤ), ⨅ A : ℝ, ⨅ B : ℝ, (cuspLogConstantComplex N hN s A B).ker

theorem mem_localCuspidalSpace (N : ℕ) (hN : 0<N) (f : AutomorphicSpace N) :
    f∈localCuspidalSpace N hN ↔ ∀ s : SL(2,ℤ), ∀ A B : ℝ, cuspLogConstant N hN s A B f=0 := by
  simp only [localCuspidalSpace,Submodule.mem_iInf,LinearMap.mem_ker]
  rfl

theorem localCuspidalSpace_closed (N : ℕ) (hN : 0<N) :
    IsClosed (localCuspidalSpace N hN : Set (AutomorphicSpace N)) := by
  simp only [localCuspidalSpace,Submodule.coe_iInf]
  exact isClosed_iInter (fun s => isClosed_iInter (fun A => isClosed_iInter
    (fun B => (cuspLogConstantComplex N hN s A B).isClosed_ker)))

#print axioms localHalfDensity_map_complex_smul
#print axioms localCuspidalSpace_closed

end QuantitativeMaass
