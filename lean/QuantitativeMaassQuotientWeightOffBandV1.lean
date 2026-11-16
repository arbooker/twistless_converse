module

public import QuantitativeMaassQuotientWeightFluxVectorsV1
public import QuantitativeMaassSeparatedFluxV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeMaass

/-- Multiplication by the literal nonsmooth orbit weight has uniformly small
mass at separated shifted spectral frequencies. This is an estimate for the
actual multiplier on actual Friedrichs eigenvectors, not an assumption of
spectral-band preservation. -/
theorem quotientWeight_separated_mass {ι : Type*} [Fintype ι]
    (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (r : ι → ℝ) (μ : ℝ)
    (f : ι → AutomorphicSpace N) (g : AutomorphicSpace N)
    (hf : Orthonormal ℂ f) (hr : ∀ i,0≤r i) (hμ : 0≤μ)
    (hgraph : ∀ i,FriedrichsGraph N (f i) ((r i:ℂ) • f i))
    (hg : FriedrichsGraph N g ((μ:ℂ) • g)) (L : ℝ) (hL : 0<L)
    (hsep : ∀ i,L≤|Real.sqrt (1+r i)-Real.sqrt (1+μ)|) :
    ∑ i,‖inner ℂ (f i).val (quotientWeightMultiplier N hε ht g.val)‖^2≤
      16*(4*quotientWeightBound ε*(2*t:ℝ))^2*‖g‖^2/L^2 := by
  let u := fun i => ((Real.sqrt (1+r i))⁻¹:ℂ) • eigenEnergyLift N (r i) (f i)
  let A := quotientWeightFluxEnergyVector N hε ht g.val
  let B := quotientWeightFluxAmbientVector N hε ht (eigenEnergyLift N μ g)
  have hu : Orthonormal ℂ u := eigenEnergyLift_orthonormal N r f hf hr hgraph
  have hv : Orthonormal ℂ (fun i => (f i).val) :=
    hf.comp_linearIsometry (AutomorphicSpace N).subtypeₗᵢ
  have hsμ : 0<Real.sqrt (1+μ) := Real.sqrt_pos.2 (by linarith)
  have hflux (i : ι) :
      (((Real.sqrt (1+r i))^2-(Real.sqrt (1+μ))^2:ℝ):ℂ)*
          inner ℂ (f i).val (quotientWeightMultiplier N hε ht g.val)=
        (Real.sqrt (1+r i):ℂ)*inner ℂ (u i) A-inner ℂ (f i).val B := by
    rw [Real.sq_sqrt (show 0≤1+r i by linarith [hr i]),
      Real.sq_sqrt (show 0≤1+μ by linarith)]
    have he : ((1+r i-(1+μ):ℝ):ℂ)=((r i-μ:ℝ):ℂ) := by congr 1; ring
    rw [he,eigen_quotientWeight_flux_vectors N hε ht (r i) μ (f i) g (hgraph i) hg]
    change inner ℂ (eigenEnergyLift N (r i) (f i)) A-inner ℂ (f i).val B=_
    congr 1
    change inner ℂ (eigenEnergyLift N (r i) (f i)) A=
      (Real.sqrt (1+r i):ℂ)*inner ℂ
        (((Real.sqrt (1+r i))⁻¹:ℂ) • eigenEnergyLift N (r i) (f i)) A
    rw [_root_.inner_smul_left]
    have hs : Real.sqrt (1+r i)≠0 := ne_of_gt (Real.sqrt_pos.2 (by linarith [hr i]))
    have hc : (starRingEnd ℂ) (((Real.sqrt (1+r i))⁻¹:ℝ):ℂ)=
        (((Real.sqrt (1+r i))⁻¹:ℝ):ℂ) := Complex.conj_ofReal _
    simp only [Complex.ofReal_inv] at hc
    rw [hc]
    field_simp [Complex.ofReal_ne_zero.mpr hs]
  have hh := separated_flux_bessel u (fun i => (f i).val) hu hv A B
    (fun i => Real.sqrt (1+r i)) (Real.sqrt (1+μ)) L
    (fun _ => Real.sqrt_nonneg _) hsμ hL hsep
    (fun i => inner ℂ (f i).val (quotientWeightMultiplier N hε ht g.val)) hflux
  apply hh.trans
  have hA := pow_le_pow_left₀ (norm_nonneg A) (quotientWeightFluxEnergyVector_norm N hε ht g.val) 2
  have hB := pow_le_pow_left₀ (norm_nonneg B)
    (quotientWeightFluxAmbientVector_norm N hε ht (eigenEnergyLift N μ g)) 2
  change ‖A‖^2≤(2*|(4*quotientWeightBound ε*(2*t:ℝ))| *‖g‖)^2 at hA
  change ‖B‖^2≤(2*|(4*quotientWeightBound ε*(2*t:ℝ))| *‖eigenEnergyLift N μ g‖)^2 at hB
  rw [mul_pow,mul_pow,sq_abs,eigenEnergyLift_norm_sq N μ g hg] at hB
  rw [mul_pow,mul_pow,sq_abs] at hA
  rw [Real.sq_sqrt (show 0≤1+μ by linarith)]
  have hdiv : ‖B‖^2/(1+μ)≤4*(4*quotientWeightBound ε*(2*t:ℝ))^2*‖g‖^2 := by
    apply (div_le_iff₀ (show 0<1+μ by linarith)).mpr
    nlinarith only [hB]
  have htotal : ‖A‖^2+‖B‖^2/(1+μ)≤8*(4*quotientWeightBound ε*(2*t:ℝ))^2*‖g‖^2 := by
    nlinarith only [hA,hdiv]
  calc
    _ ≤ (2/L^2)*(8*(4*quotientWeightBound ε*(2*t:ℝ))^2*‖g‖^2) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    _ = _ := by ring

#print axioms quotientWeight_separated_mass

end QuantitativeMaass
