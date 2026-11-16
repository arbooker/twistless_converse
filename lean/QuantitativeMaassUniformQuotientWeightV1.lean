module

public import QuantitativeMaassCappedRowMajorantV1
public import QuantitativeMaassWeightedQuotientEnergyV1
public import AsymptoticModularFundamentalV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticCompactBranch
open AsymptoticMassTransport AsymptoticCongruenceLabels AsymptoticClassicalPetersson
open scoped MatrixGroups Modular ENNReal

namespace QuantitativeMaass

def quotientWeightBound (ε : ℝ) : ℝ := ∑' a : ℤ × ℤ,cappedRowMajorant ε a

theorem quotientWeightBound_nonneg (ε : ℝ) : 0≤quotientWeightBound ε :=
  tsum_nonneg (cappedRowMajorant_nonneg ε)

/-- Bound the convergent strip orbit sum by its injective primitive lower
rows. This bound is uniform in the height throughout the standard cusp. -/
theorem quotientWeight_standard_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (z : ℍ) (hx : |z.re|≤1/2) (hy : 1/2≤z.im) :
    weight N ε v z≤quotientWeightBound ε := by
  let row : Strip N z → ℤ × ℤ := fun g => (bottom g 0,bottom g 1)
  have hr : Function.Injective row := by
    intro g h he
    apply bottom_injective N z
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  have he : weight N ε v z=∑' g : Strip N z,cap ε v (g.val.val • z)^2 := by
    unfold weight
    exact (tsum_subtype {g : gamma N | g.val • z∈strip}
      (fun g => cap ε v (g.val • z)^2)).symm
  rw [he]
  calc
    _≤∑' g : Strip N z,cappedRowMajorant ε (row g) := by
      apply (strip_summable N hε hv z).tsum_le_tsum _
        ((cappedRowMajorant_summable ε).comp_injective hr)
      intro g
      have hh := cap_sq_le_cappedRowMajorant hε hv (representative g.val) z hx hy
      simpa only [Function.comp_def,←integralLabel_action,representative_label,row,bottom] using hh
    _≤quotientWeightBound ε := tsum_comp_le_tsum_of_inj (cappedRowMajorant_summable ε)
      (cappedRowMajorant_nonneg ε) hr

theorem quotientWeight_le_level_one (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (z : ℍ) : weight N ε v z≤weight 1 ε v z := by
  let incl : gamma N → gamma 1 := fun g => ⟨g.val,gamma_le_of_dvd (one_dvd N) g.property⟩
  have hi : Function.Injective incl := by
    intro g h he
    apply Subtype.ext
    exact congrArg (fun a : gamma 1 => a.val) he
  exact tsum_comp_le_tsum_of_inj (weight_summable 1 hε hv z)
    (fun g => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _) hi

/-- A global uniform upper bound on the actual cap orbit weight. It holds
at every level; no newspace equation or Laplace parameter is involved. -/
theorem quotientWeight_uniform_bound (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (z : ℍ) : weight N ε v z≤quotientWeightBound ε := by
  apply (quotientWeight_le_level_one N hε hv z).trans
  obtain ⟨g,hg⟩ := AsymptoticModularDomain.gamma_one_orbit_meets z
  rw [←weight_invariant 1 ε v g z]
  apply quotientWeight_standard_bound 1 hε hv (g.val • z) hg.2
  have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
  nlinarith [(g.val • z).im_pos]

/-- The concrete weighted quotient embedding has a uniform upper energy
bound, with the comparison constant constructed from a summable lattice
majorant. Only the lower bound on the new/sign target remains separate. -/
theorem weighted_quotient_energy_uniform (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (f : ℍ → ℂ) (hf : Measurable f)
    (hinv : ∀ g : gamma N,∀ z,f (g.val • z)=f z) :
    (∫⁻ z,ENNReal.ofReal (‖(cap ε v z:ℂ)*f z‖^2) ∂quotientMeasure 0)≤
      ENNReal.ofReal (quotientWeightBound ε)*
        ∫⁻ z,ENNReal.ofReal (‖f z‖^2) ∂quotientMeasure N :=
  weighted_quotient_energy_le N hε hv (quotientWeightBound ε)
    (quotientWeight_uniform_bound N hε hv) f hf hinv

#print axioms quotientWeightBound_nonneg
#print axioms quotientWeight_standard_bound
#print axioms quotientWeight_le_level_one
#print axioms quotientWeight_uniform_bound
#print axioms weighted_quotient_energy_uniform

end QuantitativeMaass
