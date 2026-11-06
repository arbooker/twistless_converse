module

public import QuantitativeArithmeticRetainedCommonSectorScaleV1
public import QuantitativeArithmeticRetainedActualCommonFilterV1
public import QuantitativeEulerEndpointHorizonEndpointV1
public import AsymptoticTotalNewTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedIteration
open AsymptoticSectorSigns QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight QuantitativeHolomorphic
open QuantitativeHolomorphic.Schedule QuantitativeEulerEndpointPrepared
open QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeArithmeticRetainedHorizonScale
open Polynomial AsymptoticFiniteBranch
open scoped Classical MatrixGroups

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

def sectorLeadingCoefficient (e : Sector N) : ℝ :=
  (AsymptoticRegularTrace.trace MeasureTheory.volume
    (fun x => (AsymptoticQuotientIncidence.space N (NeZero.pos N) P.epsilon_pos
      (by omega : 1≤QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) e x).starProjection)).toReal/(4*Real.pi)

theorem sectorLeadingCoefficient_nonneg (e : Sector N) : 0≤sectorLeadingCoefficient A P e :=
  div_nonneg ENNReal.toReal_nonneg (by positivity)

/-- All filter, recurrence, original-equation and trace-comparison premises
are discharged. Only explicit scalar horizon/weight inequalities remain. -/
theorem exists_actual_sector_scale (hR₀ : ∀p∈R₀,p.Prime) (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (hN2 : 2≤N) (e : Sector N) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (H₀ : ℝ) (hH₀ : max P.ε⁻¹ 4≤H₀)
    (hdata : ∀ i,sectorFamilyB N (NeZero.pos N) e S hS i≤H₀) :
    ∃ C D : ℝ,0≤C ∧ 0≤D ∧ ∀ n h : ℕ,∀ c : ℝ,0<h →
      1≤Real.log (observationScale c (h+1)) →
      32≤Real.log (Real.log (h+1:ℝ)) →
      (4:ℝ)^n≤(Real.log (observationScale c (h+1)))^2 → D*c^2≤1/2 →
      (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
        sectorLeadingCoefficient A P e+C/(4:ℝ)^n+3*Real.exp (-Real.log (h+1:ℝ)/4) := by
  let excluded := reconstructionExclusions N Q ∪ R₀
  let G := generatorTransportConstant (QuantitativeEulerEndpointPrepared.prepared N hN2 excluded threshold)
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,C₀,hC₀,Kobs,hKobs,hfilters⟩ :=
    exists_actual_common_filter A P hR₀ hdiv hbad hN2 e threshold S hS
  obtain ⟨Ka,Kc,hKa,hKc,hall⟩ := hfilters H₀ hH₀ hdata
  obtain ⟨Ce,De,hCe,hDe,hscale⟩ := exists_common_sector_scale A P hR₀ (NeZero.pos N) hdiv hbad hKa hKc
  let E := Real.exp ((8:ℝ)/3+8)*(P.ε⁻¹+4*(1+P.ε⁻¹*Real.log 2))
  let tail := sectorTailConstant N (NeZero.pos N) e S hS
  let C := Ce+((tail+1)/H₀+E)/(4*Real.pi)
  have hH0 : 0<H₀ := lt_of_lt_of_le (by norm_num : (0:ℝ)<4) ((le_max_right _ _).trans hH₀)
  have htail : 0≤tail := sectorTailConstant_nonneg N (NeZero.pos N) e S hS
  have hε : 0<P.ε := P.epsilon_pos
  have hE : 0≤E := by dsimp only [E]; positivity
  have hC : 0≤C := by dsimp only [C]; positivity
  refine ⟨C,De,hC,hDe,?_⟩
  intro n h c hh hs hlog hn hsc
  obtain ⟨F,z,hi,hvalid,hrec,hfix,htrace,hmass,hmatrix,happrox,hphysical⟩ := hall n
  let T := actualFiniteExpression A P hR₀ e hN2 excluded threshold S hS W Bobs Bg D H₀ G C₀ Kobs
    n (Real.exp ((Ka+1)*(4:ℝ)^n)) z
  have hreg (x) : 0≤regularSum T x ∧ regularSum T x≤1 := by
    have hr := actualFiniteExpression_regular_order A P hR₀ e hN2 excluded threshold S hS W Bobs Bg D H₀ G C₀ Kobs
      n (Real.exp ((Ka+1)*(4:ℝ)^n)) z (fun j hj => (hrec j hj).1.scalar) x
    exact hr
  have hp := hphysical h
  have hb := hscale n h c hh hs hlog hn hsc e (F n)
    ⟨(hvalid n le_rfl).nonneg,(hvalid n le_rfl).le_one⟩ T hmass hmatrix hreg happrox
    ⟨hp.1.1,hp.1.2.1⟩ hp.2
  have ht := div_le_div_of_nonneg_right htrace (by positivity : 0≤4*Real.pi)
  have hid : (sectorTraceTarget N (NeZero.pos N) e S hS (H₀*(4:ℝ)^n) P.epsilon_pos
      (by omega : 1≤QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)+(H₀*(4:ℝ)^n)⁻¹+E/(4:ℝ)^n)/(4*Real.pi)+Ce/(4:ℝ)^n=
      sectorLeadingCoefficient A P e+C/(4:ℝ)^n := by
    dsimp only [sectorTraceTarget,sectorLeadingCoefficient,C,tail]
    rw [mul_inv_rev]
    ring
  dsimp only [E] at hid
  linarith only [hb,ht,hid]

#print axioms sectorLeadingCoefficient_nonneg
#print axioms exists_actual_sector_scale
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open AsymptoticSectorSigns QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight QuantitativeHolomorphic
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointHorizon QuantitativeEulerDensityGenerators
open Filter
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

/-- The actual original-equation sector has endpoint excess over its
incidence leading coefficient. No filter or analytic hypothesis remains. -/
theorem actual_sector_endpoint (hR₀ : ∀p∈R₀,p.Prime) (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (hN2 : 2≤N) (e : Sector N) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ h : ℕ in atTop,
      (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h
        (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
      sectorLeadingCoefficient A P e+B/Real.log (Real.log (h+1:ℝ)) := by
  let S := observedGenerators N
  have hS := observedGenerators_closure N
  let H₀ := max (max P.ε⁻¹ 4)
    (∑ i,abs (sectorFamilyB N (NeZero.pos N) e S hS i))
  have hdata (i) : sectorFamilyB N (NeZero.pos N) e S hS i≤H₀ := by
    apply (le_abs_self _).trans
    apply le_trans (Finset.single_le_sum (fun j _ => abs_nonneg (sectorFamilyB N (NeZero.pos N) e S hS j)) (Finset.mem_univ i))
    exact le_max_right _ _
  obtain ⟨C,D,hC,hD,hbound⟩ := exists_actual_sector_scale A P hR₀ hdiv hbad hN2 e 0 S hS H₀ (le_max_left _ _) hdata
  apply eventual_endpoint_of_horizon_bound _ _ C D (sectorLeadingCoefficient_nonneg A P e) hC hD
  intro n h c hh hs hlog hn hscale
  simpa only [mul_div_assoc] using hbound n h c hh hs hlog hn hscale

/-- The sum of sector leading coefficients is bounded by the actual
arithmetic local-new coefficient, without sectorwise classical identification. -/
theorem sum_sectorLeadingCoefficient_le :
    (∑ e : Sector N,sectorLeadingCoefficient A P e)≤AsymptoticTotalNewCorner.coefficient N (NeZero.pos N) := by
  have hh := AsymptoticTotalNewCorner.totalTrace_le_coefficient N (NeZero.pos N) P.epsilon_pos
    (by omega : 1≤QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)
  simp only [sectorLeadingCoefficient,←Finset.sum_div]
  apply (div_le_iff₀ (by positivity : 0<4*Real.pi)).mpr
  simpa only [AsymptoticQuotientIncidence.totalTrace,mul_comm] using hh

/-- Endpoint control of the sum of actual original-equation sector dimensions.
The leading coefficient is unchanged and the error is inverse log-log. -/
theorem actual_total_sector_endpoint (hR₀ : ∀p∈R₀,p.Prime) (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (hN2 : 2≤N) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ h : ℕ in atTop,
      (∑ e : Sector N,(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h
        (h+1+P.s) e):ℝ))/(2*h+2:ℝ)≤
      AsymptoticTotalNewCorner.coefficient N (NeZero.pos N)+B/Real.log (Real.log (h+1:ℝ)) := by
  choose B hB hb using fun e : Sector N => actual_sector_endpoint A P hR₀ hdiv hbad hN2 e
  refine ⟨∑ e,B e,Finset.sum_nonneg (fun e _ => hB e),?_⟩
  have hall := Filter.eventually_all.mpr hb
  filter_upwards [hall] with h hh
  have hs := Finset.sum_le_sum (fun e (_ : e∈(Finset.univ : Finset (Sector N))) => hh e)
  simp only [Finset.sum_add_distrib,←Finset.sum_div] at hs
  exact hs.trans (add_le_add (sum_sectorLeadingCoefficient_le A P) le_rfl)

#print axioms actual_sector_endpoint
#print axioms sum_sectorLeadingCoefficient_le
#print axioms actual_total_sector_endpoint
end QuantitativeArithmeticRetainedIteration
