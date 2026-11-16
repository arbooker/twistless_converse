module

public import QuantitativeMaassCuspCoreGeometryV1
public import QuantitativeArithmeticMaassOverlapEnergyV1
public import QuantitativeArithmeticMaassCuspLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open QuantitativeSpectralObservability QuantitativeArithmeticMaassOverlap
open QuantitativeArithmeticMaassCuspBand
open scoped ENNReal MatrixGroups ContDiff

namespace QuantitativeMaass

/-- Integrate the explicit radial row bound against the raw compact-core
measure used by the cusp estimate. -/
theorem radialKernel_core_energy_explicit (N : ℕ) (hN : 0<N)
    (Y L R : ℝ) (hR : 0≤R)
    (hL : wideCompactCover N Y ⊆ Metric.closedBall I L)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hs : Function.support g ⊆ Iic (Real.cosh R)) :
    (∫⁻ x in wideCompactCover N Y, ∫⁻ y,
      ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2) ∂quotientMeasure N) ≤
      ((energyMultiplicity I L R:ℝ≥0∞)*
        ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2))*
        ((Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ≥0∞)*40) := by
  let : NeZero N := ⟨hN.ne'⟩
  calc
    _ ≤ ∫⁻ _x in wideCompactCover N Y,
        (energyMultiplicity I L R:ℝ≥0∞)*
          ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2) := by
      apply setLIntegral_mono' (wideCompactCover_compact N hN Y).measurableSet
      intro x hx
      rw [←radialKernel_row_lintegral N g hg R hR hs x,
        ←radialKernel_row_energy N g hg R hR hs x]
      exact radialKernel_compact_energy_explicit N I L R hR g hg hs x (hL hx)
    _ = ((energyMultiplicity I L R:ℝ≥0∞)*
        ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2))*
        (volume : Measure ℍ) (wideCompactCover N Y) := by
      rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := mul_le_mul_of_nonneg_left (wideCompactCover_area_uniform N hN Y) zero_le

/-- An explicit cardinal estimate for every finite subset of a cuspidal
orthonormal packet eigenfamily. The core mass is derived from the form energy. -/
theorem cuspidal_packet_finset_card {ι : Type*} (N : ℕ) (hN : 0<N)
    (u : ι → QuotientEnergySpace N)
    (hv : Orthonormal ℂ (fun i => energyInclusion N (u i)))
    (hu : ∀ i, energyInclusion N (u i)∈localCuspidalSpace N hN)
    (E Y L : ℝ) (hY : 2≤Y)
    (hsize : 8*(Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*N^2*(N+1)*E≤Y^2)
    (henergy : ∀ i, (quotientClosedEnergy N (u i) (u i)).re≤E*‖energyInclusion N (u i)‖^2)
    (hL : wideCompactCover N Y ⊆ Metric.closedBall I L)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hr : ∀ q,star (g q)=g q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (eigenvalue : ι → ℂ) (b : ℝ) (hb : 0<b)
    (heigenvalue : ∀ i,b≤‖eigenvalue i‖)
    (hpacket : letI : NeZero N := ⟨hN.ne'⟩; ∀ i,
      radialKernelOperator N g hg R hR hs (energyInclusion N (u i))=
        eigenvalue i • energyInclusion N (u i)) (s : Finset ι) :
    (s.card:ℝ)*(b^2/2) ≤ (energyMultiplicity I L R:ℝ)*
      ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2)*
      ((Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*40) := by
  let : NeZero N := ⟨hN.ne'⟩
  let K := wideCompactCover N Y
  have hK := wideCompactCover_compact N hN Y
  let A := quotientRestriction N K hK hK.measurableSet
  have hlower (i : ι) : b^2/2 ≤
      ‖A (radialKernelOperator N g hg R hR hs (energyInclusion N (u i)))‖^2 := by
    rw [hpacket i,map_smul,norm_smul,mul_pow]
    have hc := cuspidal_bounded_energy_core N hN E Y hY hsize (u i) (hu i) (henergy i)
    rw [hv.norm_eq_one i,one_pow] at hc
    have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg ‖eigenvalue i‖)
    have hl : b^2≤‖eigenvalue i‖^2 := by nlinarith [heigenvalue i,norm_nonneg (eigenvalue i)]
    change 1≤2*‖A (energyInclusion N (u i))‖^2 at hc
    change ‖eigenvalue i‖^2*1≤‖eigenvalue i‖^2*(2*‖A (energyInclusion N (u i))‖^2) at hm
    nlinarith
  have hbound : (s.card:ℝ≥0∞)*ENNReal.ofReal (b^2/2) ≤
      ((energyMultiplicity I L R:ℝ≥0∞)*
        ENNReal.ofReal ((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2))*
        ((Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ≥0∞)*40) := by
    calc
      _ = ∑ _i∈s,ENNReal.ofReal (b^2/2) := by simp
      _ ≤ ∑ i∈s,ENNReal.ofReal
          (‖A (radialKernelOperator N g hg R hR hs (energyInclusion N (u i)))‖^2) :=
        Finset.sum_le_sum (fun i _ => ENNReal.ofReal_le_ofReal (hlower i))
      _ ≤ ∑' i,ENNReal.ofReal
          (‖A (radialKernelOperator N g hg R hR hs (energyInclusion N (u i)))‖^2) :=
        ENNReal.sum_le_tsum s
      _ ≤ _ := (radialKernel_raw_compact_bessel N (fun i => energyInclusion N (u i))
        hv g hg hr R hR hs K hK).trans
        (radialKernel_core_energy_explicit N hN Y L R hR hL g hg hs)
  have hnonneg : 0≤(2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2 :=
    mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg s.card)]
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hnonneg),
    ENNReal.ofReal_mul (Nat.cast_nonneg (energyMultiplicity I L R)),
    ENNReal.ofReal_mul (Nat.cast_nonneg (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)))]
  simpa only [ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat] using hbound

/-- The explicit lattice overlap on the logarithmic core ball is bounded
by a polynomial in cusp height, uniformly for all short packet radii. -/
theorem cuspCore_overlap_polynomial (N : ℕ) (hN : 0<N) :
    ∃ C D : ℝ,1≤C ∧ 0<D ∧ ∀ Y : ℝ,2≤Y →
      wideCompactCover N Y ⊆ Metric.closedBall I (Real.log (C*(Y+3)^2)) ∧
      ∀ R : ℝ,0≤R → R≤1 →
        (energyMultiplicity I (Real.log (C*(Y+3)^2)) R:ℝ)≤D*(Y+3)^8 := by
  obtain ⟨C,hC,hcore⟩ := wideCompactCover_log_radius N hN
  refine ⟨C,(2*Real.exp 2*C+3)^4,hC,by positivity,?_⟩
  intro Y hY
  refine ⟨hcore Y hY,?_⟩
  intro R hR hR1
  have hp : 0<C*(Y+3)^2 := by positivity
  have he : Real.exp (R+Real.log (C*(Y+3)^2)+1+dist (I:ℍ) I) ≤
      Real.exp 2*C*(Y+3)^2 := by
    calc
      _ ≤ Real.exp (2+Real.log (C*(Y+3)^2)) := Real.exp_le_exp.mpr (by simp only [dist_self]; linarith)
      _ = _ := by rw [Real.exp_add,Real.exp_log hp]; ring
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos
    (R+Real.log (C*(Y+3)^2)+1+dist (I:ℍ) I)).le).le
  have hbase : (2*⌈Real.exp (R+Real.log (C*(Y+3)^2)+1+dist (I:ℍ) I)⌉₊+1:ℝ) ≤
      (2*Real.exp 2*C+3)*(Y+3)^2 := by
    nlinarith [sq_nonneg (Y+3)]
  unfold energyMultiplicity
  push_cast
  apply (pow_le_pow_left₀ (by positivity) hbase 4).trans_eq
  ring

#print axioms radialKernel_core_energy_explicit
#print axioms cuspidal_packet_finset_card
#print axioms cuspCore_overlap_polynomial

end QuantitativeMaass
