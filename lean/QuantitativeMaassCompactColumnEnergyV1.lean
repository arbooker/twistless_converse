module

public import QuantitativeMaassCylinderCompactPhysicalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped SchwartzMap
namespace QuantitativeMaass

/-- The global energy of the actual compact-input columns is exactly the
compact diagonal energy. The interchange uses the proved self-adjoint packet
and finite-energy trace identities, not a formal cyclic trace rule. -/
theorem compact_input_column_energy {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {a : ℝ} (ha : 0<a) (b : ℝ) :
    let S := upperRectangle 0 1 a b
    let hS := upperRectangle_compact 0 1 a b ha
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) S hS.measurableSet
    (∫ z,‖P (cylinderTimeColumn f hc he R hR hs z)‖^2 ∂quotientMeasure 0)=
      ∫ z in S,‖cylinderTimeColumn f hc he R hR hs z‖^2 := by
  intro S hS P
  let W := cylinderTimePacket f (f.smooth ⊤) hc
  have hcyc := compact_input_column_trace_cyclic f hc he hr R hR hs basis ha b
    (1 : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
  have hnorm (x : Lp ℂ 2 (quotientMeasure 0)) : (inner ℂ x x).re=‖x‖^2 :=
    (norm_sq_eq_re_inner (𝕜:=ℂ) x).symm
  simp only [columnLinearTrace,one_def,id_apply,hnorm] at hcyc
  have heq (i : ι) : ‖P (W (basis i))‖=
      ‖cylinderCompactColumnPacket f hc he R hR hs S hS (basis i)‖ := by
    have hh := congrArg norm (compact_column_zeroExtension f hc he hr R hR hs ha b (basis i))
    simpa only [LinearIsometry.norm_map] using hh.symm
  have hsum := finiteEnergyColumn_input_real_energy (volume.restrict S)
    (cylinderTimeColumn f hc he R hR hs)
    (compact_column_memLp _ (cylinderAbelColumn_continuous _ _ R hR _) S hS) basis
    (1 : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
  simp only [one_def,adjoint_id,id_apply] at hsum
  calc
    _ = ∑' i,‖P (W (basis i))‖^2 := hcyc
    _ = ∑' i,‖cylinderCompactColumnPacket f hc he R hR hs S hS (basis i)‖^2 := by simp_rw [heq]
    _ = _ := hsum

/-- Norm approximation of the retained operator costs only the actual
compact diagonal packet energy. No sign is imposed on the approximant. -/
theorem compact_input_column_trace_approx {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)
    {a : ℝ} (ha : 0<a) (b : ℝ)
    (T U : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0))
    {δ : ℝ} (hδ : ‖T-U‖≤δ) :
    let S := upperRectangle 0 1 a b
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) S
      (upperRectangle_compact 0 1 a b ha).measurableSet
    |columnLinearTrace (quotientMeasure 0) (fun z => P (cylinderTimeColumn f hc he R hR hs z)) T-
      columnLinearTrace (quotientMeasure 0) (fun z => P (cylinderTimeColumn f hc he R hR hs z)) U|≤
      δ*(∫ z in S,‖cylinderTimeColumn f hc he R hR hs z‖^2) := by
  intro S P
  have hh := columnLinearTrace_approx (quotientMeasure 0)
    (fun z => P (cylinderTimeColumn f hc he R hR hs z))
    (cylinderTimeColumn_compact_input_memLp f hc he R hR hs ha b) T U hδ
  rwa [compact_input_column_energy basis f hc he hr R hR hs ha b] at hh

#print axioms compact_input_column_energy
#print axioms compact_input_column_trace_approx
end QuantitativeMaass
