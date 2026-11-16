module

public import QuantitativeMaassLVCuspidalRangeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

theorem localHalfDensity_eq_zero_iff (w A B : ℝ) (hw : 0<w)
    (f : Lp ℂ 2 (heightMeasure (upperRectangle 0 w (Real.exp A) (Real.exp B)))) :
    localHalfDensity w A B hw f=0 ↔ f=0 := by
  constructor
  · intro h
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    rw [localHalfDensity_inner w A B hw f f,h,inner_zero_left,mul_zero]
  · rintro rfl
    exact map_zero _

/-- The LV range has zero ACTUAL height-average on every positive compact
height band, not just after a change of coordinates. -/
theorem actualLVFilter_cuspConstantLocal_zero (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ)
    (s : SL(2,ℤ)) (y₁ y₂ : ℝ) (hy₁ : 0<y₁) (hy₂ : 0<y₂) (f : AutomorphicSpace N) :
    cuspConstantLocal N s y₁ y₂ hy₁ (actualLVFilter N p hN hpN a b hab d f)=0 := by
  have h := (localHalfDensity_eq_zero_iff N (Real.log y₁) (Real.log y₂) (Nat.cast_pos.mpr hN)
    (cuspConstantLocal N s (Real.exp (Real.log y₁)) (Real.exp (Real.log y₂))
      (Real.exp_pos _) (actualLVFilter N p hN hpN a b hab d f))).mp
    (actualLVFilter_cuspLogConstant_zero N p hN hpN hNp hpres a b hab d s
      (Real.log y₁) (Real.log y₂) f)
  have transfer : ∀ (u v : ℝ) (hu : 0<u), u=y₁ → v=y₂ →
      cuspConstantLocal N s u v hu (actualLVFilter N p hN hpN a b hab d f)=0 →
      cuspConstantLocal N s y₁ y₂ hy₁ (actualLVFilter N p hN hpN a b hab d f)=0 := by
    intro u v hu he₁ he₂ hz
    subst u
    subst v
    exact hz
  exact transfer _ _ _ (Real.exp_log hy₁) (Real.exp_log hy₂) h

/-- The actual free-wave intertwining proves invariance of the geometric
closed cuspidal subspace under the quotient wave. -/
theorem shiftedQuotientWave_mem_localCuspidalSpace (N : ℕ) (hN : 0<N)
    (f : AutomorphicSpace N) (hf : f∈localCuspidalSpace N hN) (t : ℝ) :
    Wave.shiftedQuotientWave N t f∈localCuspidalSpace N hN := by
  rw [mem_localCuspidalSpace] at hf ⊢
  intro s A B
  rw [Wave.cuspLogConstant_wave_eq_free,Wave.cuspLogFreeWave,hf,hf,map_zero,map_zero,
    add_zero,smul_zero]

/-- The actual Hecke operator preserves the same closed geometric kernel
for the arithmetic progression used by the all-cusp correspondence. -/
theorem hecke_mem_localCuspidalSpace (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : AutomorphicSpace N) (hf : f∈localCuspidalSpace N hN) :
    HeckeL2.operator N p hN hpN a b hab f∈localCuspidalSpace N hN := by
  rw [mem_localCuspidalSpace] at hf ⊢
  intro s A B
  rw [cuspLogConstant_hecke N p hN hpN hNp hpres a b hab,hf,hf,map_zero,map_zero,add_zero]

#print axioms actualLVFilter_cuspConstantLocal_zero
#print axioms shiftedQuotientWave_mem_localCuspidalSpace
#print axioms hecke_mem_localCuspidalSpace

end QuantitativeMaass
