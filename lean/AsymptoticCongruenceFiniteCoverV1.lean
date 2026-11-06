module

public import AsymptoticCongruenceStripV1
public import AsymptoticHyperbolicAreaV1
public import Mathlib.NumberTheory.Modular

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceCover

open Matrix UpperHalfPlane MeasureTheory Set
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticHyperbolicArea
open scoped MatrixGroups ENNReal Pointwise

theorem modular_orbit_meets_terminal (z : ℍ) :
    ∃ g : SL(2,ℤ),g • z∈terminal (1/4) := by
  obtain ⟨g,hg⟩ := ModularGroup.exists_one_half_le_im_smul z
  refine ⟨ModularGroup.T^(-Int.floor (g • z).re)*g,?_⟩
  change (0≤(_ • z).re ∧ (_ • z).re<1) ∧ (1:ℝ)/4<(_ • z).im
  simp only [mul_smul,ModularGroup.re_T_zpow_smul,ModularGroup.im_T_zpow_smul,Int.cast_neg]
  have h0 := Int.floor_le (g • z).re
  have h1 := Int.lt_floor_add_one (g • z).re
  exact ⟨⟨by linarith,by linarith⟩,by linarith⟩

/-- A finite union of translates of a terminal translation strip,
using the actual integral congruence cosets. -/
noncomputable def cover (N : ℕ) : Set ℍ :=
  ⋃ q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    (integralLabel q.out)⁻¹ • terminal (1/4)

theorem cover_measurable (N : ℕ) (hN : 0<N) : MeasurableSet (cover N) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply MeasurableSet.iUnion
  intro q
  rw [← preimage_smul_inv]
  exact (terminal_measurable (1/4)).preimage
    (AsymptoticRationalGroup.measurePreserving (integralLabel q.out)).measurable

theorem orbit_meets_cover (N : ℕ) (z : ℍ) : ∃ h : gamma N,h.val • z∈cover N := by
  obtain ⟨g,hg⟩ := modular_orbit_meets_terminal z
  let q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N := QuotientGroup.mk g
  have hmem : q.out⁻¹*g∈CongruenceSubgroup.Gamma0 N :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  refine ⟨⟨integralLabel (q.out⁻¹*g),Subgroup.mem_map.mpr ⟨_,hmem,rfl⟩⟩,?_⟩
  apply mem_iUnion.mpr
  refine ⟨q,?_⟩
  refine ⟨g • z,hg,?_⟩
  simp only [map_mul,map_inv,mul_smul,integralLabel_action]

theorem cover_volume_finite (N : ℕ) (hN : 0<N) : (volume : Measure ℍ) (cover N)<∞ := by
  let : NeZero N := ⟨hN.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  apply (measure_iUnion_le _).trans_lt
  rw [tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro q _
  have he : (volume : Measure ℍ) ((integralLabel q.out)⁻¹ • terminal (1/4))=
      volume (terminal (1/4)) := by
    rw [← preimage_smul_inv]
    exact (AsymptoticRationalGroup.measurePreserving (integralLabel q.out)).measure_preimage
      (terminal_measurable (1/4)).nullMeasurableSet
  rw [he,terminal_area (by norm_num : (0:ℝ)<1/4)]
  exact ENNReal.ofReal_lt_top

#print axioms modular_orbit_meets_terminal
#print axioms cover_measurable
#print axioms orbit_meets_cover
#print axioms cover_volume_finite

end AsymptoticCongruenceCover
