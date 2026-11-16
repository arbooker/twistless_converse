module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import QuantitativeMaassShiftedWaveContinuityV1
public import QuantitativeMaassShiftedWaveScalarODEV1
public import QuantitativeMaassWaveSpectrumV1
public import QuantitativeMaassWaveTimePrimitiveV1

/-! Consolidated chapter: QuantitativeArithmeticMaassWave. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticMaassWaveCoreCalculusV1 -/
section
/- Adapted from Min's paused draft of QuantitativeMaassShiftedWaveCoreCalculusV1.
The original file is preserved; this variant is checked independently. -/






set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeArithmeticMaassWave

open QuantitativeMaass QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def corePositionScalar (A : H →L[ℂ] H) (t : ℝ) : C(spectrum ℝ A,ℝ) :=
  ⟨fun s => shiftedDampedCosine t s*s,
    ((shiftedDampedCosine_continuous t).comp continuous_subtype_val).mul continuous_subtype_val⟩

def coreAccelerationScalar (A : H →L[ℂ] H) (t : ℝ) : C(spectrum ℝ A,ℝ) :=
  ⟨fun s => shiftedDampedCosine t s*((5/4)*s-1),
    ((shiftedDampedCosine_continuous t).comp continuous_subtype_val).mul
      ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩

omit [CompleteSpace H] in
theorem coreAccelerationScalar_continuous (A : H →L[ℂ] H) :
    Continuous (coreAccelerationScalar A) := by
  have hp : Continuous (fun p : ℝ × spectrum ℝ A => (p.1, (p.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  let F : C(ℝ × spectrum ℝ A,ℝ) := ⟨fun p =>
    shiftedDampedCosine p.1 p.2*((5/4)*p.2-1),
    (shiftedDampedCosine_jointlyContinuous.comp hp).mul
      ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const)⟩
  exact F.curry.continuous

/-- Strong reconstruction on the twice-resolvent core, proved by scalar FTC on
both energy branches and continuous functional calculus on the compact spectrum. -/
theorem corePositionScalar_integral (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (t : ℝ) :
    corePositionScalar A t=corePositionScalar A 0+
      timePrimitive (timePrimitive (coreAccelerationScalar A)) t := by
  apply continuousMap_doublePrimitive _ _
    (fun u (s : spectrum ℝ A) => (s:ℝ)^2*signedVelocity u ((s:ℝ)⁻¹-1-1/4))
    (coreAccelerationScalar_continuous A)
  · intro s u
    have hs := positiveContraction_spectrum_bound A hp hn s.property
    exact twiceShiftedDamped_hasDerivAt u hs.1 hs.2
  · intro s u
    have hs := positiveContraction_spectrum_bound A hp hn s.property
    exact twiceShiftedVelocity_hasDerivAt u hs.1 hs.2
  · intro s
    simp only [signedVelocity_zero,mul_zero]

theorem corePositionScalar_hasDerivAt (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (t : ℝ) :
    HasDerivAt (corePositionScalar A) (timePrimitive (coreAccelerationScalar A) t) t := by
  have he : corePositionScalar A=fun u => corePositionScalar A 0+
      timePrimitive (timePrimitive (coreAccelerationScalar A)) u :=
    funext (corePositionScalar_integral A hp hn)
  rw [he]
  exact (timePrimitive_hasDerivAt (timePrimitive_continuous
    (coreAccelerationScalar_continuous A)) t).const_add _

/-- The functional calculus as a bounded real-linear map. -/
def spectralRealMap (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    C(spectrum ℝ A,ℝ) →L[ℝ] (H →L[ℂ] H) :=
  ⟨(cfcHom hA).toLinearMap,cfcHom_continuous hA⟩

def coreWaveVelocity (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) : H →L[ℂ] H :=
  spectralRealMap A hA (timePrimitive (coreAccelerationScalar A) t)

theorem spectralRealMap_position (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    spectralRealMap A hA (corePositionScalar A t)=shiftedDampedOperator A t*A := by
  have h := cfc_apply (fun s => shiftedDampedCosine t s*s) A hA
    ((shiftedDampedCosine_continuous t).mul continuous_id).continuousOn
  change cfcHom hA (corePositionScalar A t)=cfc (shiftedDampedCosine t) A*A
  trans cfc (fun s => shiftedDampedCosine t s*s) A
  · exact h.symm
  rw [cfc_mul (shiftedDampedCosine t) (fun s : ℝ => s) A
    (shiftedDampedCosine_continuous t).continuousOn continuous_id.continuousOn,cfc_id' ℝ A hA]

theorem spectralRealMap_acceleration (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    spectralRealMap A hA (coreAccelerationScalar A t)=
      shiftedDampedOperator A t*((5/4 : ℝ) • A-1) := by
  have h := cfc_apply (fun s => shiftedDampedCosine t s*((5/4)*s-1)) A hA
    ((shiftedDampedCosine_continuous t).mul
      ((continuous_const.mul continuous_id).sub continuous_const)).continuousOn
  change cfcHom hA (coreAccelerationScalar A t)=cfc (shiftedDampedCosine t) A*((5/4 : ℝ) • A-1)
  trans cfc (fun s => shiftedDampedCosine t s*((5/4)*s-1)) A
  · exact h.symm
  rw [cfc_mul (shiftedDampedCosine t) (fun s : ℝ => (5/4)*s-1) A
      (shiftedDampedCosine_continuous t).continuousOn
      ((continuous_const.mul continuous_id).sub continuous_const).continuousOn,
    cfc_sub (fun s : ℝ => (5/4)*s) (fun _ : ℝ => 1) A
      (continuous_const.mul continuous_id).continuousOn continuous_const.continuousOn,
    cfc_const_mul_id (5/4 : ℝ) A hA,cfc_const_one ℝ A]

theorem coreWave_hasDerivAt (A : H →L[ℂ] H) (hp : A.IsPositive) (hn : ‖A‖≤1) (t : ℝ) :
    HasDerivAt (fun u => shiftedDampedOperator A u*A) (coreWaveVelocity A hp.isSelfAdjoint t) t := by
  have h := (spectralRealMap A hp.isSelfAdjoint).hasFDerivAt.comp_hasDerivAt t
    (corePositionScalar_hasDerivAt A hp hn t)
  simpa only [Function.comp_def,spectralRealMap_position,coreWaveVelocity] using h

theorem coreWaveVelocity_hasDerivAt (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    HasDerivAt (coreWaveVelocity A hA)
      (shiftedDampedOperator A t*((5/4 : ℝ) • A-1)) t := by
  have h := (spectralRealMap A hA).hasFDerivAt.comp_hasDerivAt t
    (timePrimitive_hasDerivAt (coreAccelerationScalar_continuous A) t)
  exact h.congr_deriv (spectralRealMap_acceleration A hA t)

#print axioms coreWave_hasDerivAt
#print axioms coreWaveVelocity_hasDerivAt

end QuantitativeArithmeticMaassWave
end
end

/-! ## QuantitativeArithmeticMaassWaveStrongPrimitiveV1 -/
section
/- Adapted from Min's paused draft of QuantitativeMaassWaveStrongPrimitiveV1.
The original file is preserved; this variant is checked independently. -/




set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace QuantitativeArithmeticMaassWave

open QuantitativeMaass QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def doublePrimitiveLinear (T : ℝ → H →L[ℂ] H)
    (hT : ∀ z, Continuous (fun u => T u z)) (t : ℝ) : H →ₗ[ℂ] H where
  toFun z := timePrimitive (timePrimitive (fun u => T u z)) t
  map_add' z w := by
    simp only [timePrimitive,map_add]
    simp_rw [intervalIntegral.integral_add ((hT z).intervalIntegrable 0 _)
      ((hT w).intervalIntegrable 0 _)]
    exact intervalIntegral.integral_add
      ((timePrimitive_continuous (hT z)).intervalIntegrable 0 t)
      ((timePrimitive_continuous (hT w)).intervalIntegrable 0 t)
  map_smul' c z := by
    simp only [timePrimitive,map_smul,intervalIntegral.integral_smul,RingHom.id_apply]

theorem abs_le_of_mem_zero_uIoc {u t : ℝ} (hu : u∈Ι (0:ℝ) t) : |u|≤|t| := by
  have h := abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hu)
  simpa only [sub_zero] using h

omit [CompleteSpace H] in
/-- Strong integrals remain bounded in the initial vector without assuming
operator-norm measurability or operator-norm continuity of the wave family. -/
theorem doublePrimitive_norm_le (T : ℝ → H →L[ℂ] H) {C t : ℝ} (hC : 0≤C)
    (hb : ∀ u, |u|≤|t| → ‖T u‖≤C) (z : H) :
    ‖timePrimitive (timePrimitive (fun u => T u z)) t‖≤(C*|t|^2)*‖z‖ := by
  have hi : ∀ u, |u|≤|t| → ‖timePrimitive (fun v => T v z) u‖≤C*‖z‖*|t| := by
    intro u hu
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := u)
      (f := fun v => T v z) (C := C*‖z‖) (fun v hv =>
        ((T v).le_opNorm z).trans (mul_le_mul_of_nonneg_right
          (hb v ((abs_le_of_mem_zero_uIoc hv).trans hu)) (norm_nonneg z)))
    simp only [sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left hu (mul_nonneg hC (norm_nonneg z)))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := timePrimitive (fun u => T u z)) (C := C*‖z‖*|t|)
    (fun u hu => hi u (abs_le_of_mem_zero_uIoc hu))
  simp only [sub_zero] at h
  change ‖timePrimitive (timePrimitive (fun u => T u z)) t‖≤_ at h
  convert h using 1
  ring

theorem doublePrimitive_continuous_apply (T : ℝ → H →L[ℂ] H)
    (hT : ∀ z, Continuous (fun u => T u z)) {C t : ℝ} (hC : 0≤C)
    (hb : ∀ u, |u|≤|t| → ‖T u‖≤C) :
    Continuous (fun z => timePrimitive (timePrimitive (fun u => T u z)) t) :=
  ((doublePrimitiveLinear T hT t).mkContinuous (C*|t|^2)
    (doublePrimitive_norm_le T hC hb)).continuous

#print axioms doublePrimitive_continuous_apply

end QuantitativeArithmeticMaassWave
end
end

/-! ## QuantitativeArithmeticMaassWaveStrongEquationV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeArithmeticMaassWave

open QuantitativeMaass QuantitativeMaass.Wave

theorem map_timePrimitive {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (f : ℝ → E) (hf : Continuous f) (t : ℝ) :
    L (timePrimitive f t)=timePrimitive (fun u => L (f u)) t :=
  (L.intervalIntegral_comp_comm (μ := volume) (hf.intervalIntegrable 0 t)).symm

theorem map_doublePrimitive {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (f : ℝ → E) (hf : Continuous f) (t : ℝ) :
    L (timePrimitive (timePrimitive f) t)=
      timePrimitive (timePrimitive (fun u => L (f u))) t := by
  rw [map_timePrimitive L _ (timePrimitive_continuous hf)]
  congr 1
  funext u
  exact map_timePrimitive L f hf u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem core_wave_integral (A : H →L[ℂ] H) (hp : A.IsPositive) (hn : ‖A‖≤1)
    (hd : DenseRange A) (z : H) (t : ℝ) :
    shiftedRangeCosine A t (A (A z))=A (A z)+
      timePrimitive (timePrimitive (fun u =>
        shiftedRangeCosine A u ((5/4 : ℝ) • A (A z)-A z))) t := by
  let L : C(spectrum ℝ A,ℝ) →L[ℝ] H :=
    ((ContinuousLinearMap.apply ℂ H z).restrictScalars ℝ).comp
      (spectralRealMap A hp.isSelfAdjoint)
  have hpos (u : ℝ) : L (corePositionScalar A u)=shiftedRangeCosine A u (A (A z)) := by
    change (spectralRealMap A hp.isSelfAdjoint (corePositionScalar A u)) z=_
    rw [spectralRealMap_position,shiftedRangeCosine_range A hp.isSelfAdjoint hd]
    rfl
  have hacc (u : ℝ) : L (coreAccelerationScalar A u)=
      shiftedRangeCosine A u ((5/4 : ℝ) • A (A z)-A z) := by
    change (spectralRealMap A hp.isSelfAdjoint (coreAccelerationScalar A u)) z=_
    rw [spectralRealMap_acceleration]
    change shiftedDampedOperator A u ((5/4 : ℝ) • A z-z)=_
    rw [shiftedDampedOperator,← shiftedRangeCosine_range A hp.isSelfAdjoint hd,map_sub,
      show A ((5/4 : ℝ) • A z)=(5/4 : ℝ) • A (A z) from
        (A.restrictScalars ℝ).map_smul (5/4 : ℝ) (A z)]
  have he := congrArg L (corePositionScalar_integral A hp hn t)
  rw [map_add,map_doublePrimitive L _ (coreAccelerationScalar_continuous A),hpos,
    hpos,shiftedRangeCosine_zero A hp.isSelfAdjoint hd] at he
  simpa only [ContinuousLinearMap.id_apply,hacc] using he

/-- Extension of the strong integral equation from the twice-resolvent core
to the full resolvent range. Only strong continuity is needed for the wave. -/
theorem range_wave_integral (A : H →L[ℂ] H) (hp : A.IsPositive) (hn : ‖A‖≤1)
    (hd : DenseRange A) (z : H) (t : ℝ) :
    shiftedRangeCosine A t (A z)=A z+
      timePrimitive (timePrimitive (fun u =>
        shiftedRangeCosine A u ((5/4 : ℝ) • A z-z))) t := by
  have hW := shiftedRangeCosine_stronglyContinuous A hp.isSelfAdjoint hd
  have hbound (u : ℝ) (hu : |u|≤|t|) :
      ‖shiftedRangeCosine A u‖≤Real.cosh (|t|/2) := by
    apply (shiftedRangeCosine_norm_le A hp.isSelfAdjoint hd u).trans
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0≤|u|/2),abs_of_nonneg (by positivity : 0≤|t|/2)]
    linarith
  have hI := doublePrimitive_continuous_apply (shiftedRangeCosine A) hW
    (Real.cosh_pos (|t|/2)).le hbound
  have hc : Continuous (fun v : H => A v+
      timePrimitive (timePrimitive (fun u => shiftedRangeCosine A u ((5/4 : ℝ) • A v-v))) t) :=
    A.continuous.add (hI.comp ((A.continuous.const_smul (5/4 : ℝ)).sub continuous_id))
  exact congrFun (hd.equalizer ((shiftedRangeCosine A t).continuous.comp A.continuous)
    hc (funext fun v => core_wave_integral A hp hn hd v t)) z

theorem range_wave_hasDerivAt (A : H →L[ℂ] H) (hp : A.IsPositive) (hn : ‖A‖≤1)
    (hd : DenseRange A) (z : H) (t : ℝ) :
    HasDerivAt (fun u => shiftedRangeCosine A u (A z))
      (timePrimitive (fun u => shiftedRangeCosine A u ((5/4 : ℝ) • A z-z)) t) t := by
  have he : (fun u => shiftedRangeCosine A u (A z))=fun u => A z+
      timePrimitive (timePrimitive (fun v => shiftedRangeCosine A v ((5/4 : ℝ) • A z-z))) u :=
    funext (range_wave_integral A hp hn hd z)
  rw [he]
  exact (timePrimitive_hasDerivAt (timePrimitive_continuous
    (shiftedRangeCosine_stronglyContinuous A hp.isSelfAdjoint hd _)) t).const_add _

#print axioms range_wave_integral
#print axioms range_wave_hasDerivAt

end QuantitativeArithmeticMaassWave
end
end
