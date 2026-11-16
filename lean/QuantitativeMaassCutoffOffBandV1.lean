module

public import QuantitativeMaassEigenFluxVectorsV1
public import QuantitativeMaassSeparatedFluxV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeMaass.Weighted

/-- Multiplication by a smooth invariant real cutoff has uniformly small
mass at separated shifted spectral frequencies. This is an estimate for the
actual multiplier on actual Friedrichs eigenvectors, not an assumption of
spectral-band preservation. -/
theorem smooth_cutoff_separated_mass {ι : Type*} [Fintype ι]
    (N : ℕ) (b : Cutoff N) (r : ι → ℝ) (μ : ℝ)
    (f : ι → AutomorphicSpace N) (g : AutomorphicSpace N)
    (hf : Orthonormal ℂ f) (hr : ∀ i,0≤r i) (hμ : 0≤μ)
    (hgraph : ∀ i,FriedrichsGraph N (f i) ((r i:ℂ) • f i))
    (hg : FriedrichsGraph N g ((μ:ℂ) • g)) (L : ℝ) (hL : 0<L)
    (hsep : ∀ i,L≤|Real.sqrt (1+r i)-Real.sqrt (1+μ)|) :
    ∑ i,‖inner ℂ (f i).val (multiplier N b g.val)‖^2≤
      16*b.gradientBound^2*‖g‖^2/L^2 := by
  let u := fun i => ((Real.sqrt (1+r i))⁻¹:ℂ) • eigenEnergyLift N (r i) (f i)
  let A := cutoffFluxEnergyVector N b g.val
  let B := cutoffFluxAmbientVector N b (eigenEnergyLift N μ g)
  have hu : Orthonormal ℂ u := eigenEnergyLift_orthonormal N r f hf hr hgraph
  have hv : Orthonormal ℂ (fun i => (f i).val) :=
    hf.comp_linearIsometry (AutomorphicSpace N).subtypeₗᵢ
  have hsμ : 0<Real.sqrt (1+μ) := Real.sqrt_pos.2 (by linarith)
  have hflux (i : ι) :
      (((Real.sqrt (1+r i))^2-(Real.sqrt (1+μ))^2:ℝ):ℂ)*
          inner ℂ (f i).val (multiplier N b g.val)=
        (Real.sqrt (1+r i):ℂ)*inner ℂ (u i) A-inner ℂ (f i).val B := by
    rw [Real.sq_sqrt (show 0≤1+r i by linarith [hr i]),
      Real.sq_sqrt (show 0≤1+μ by linarith)]
    have he : ((1+r i-(1+μ):ℝ):ℂ)=((r i-μ:ℝ):ℂ) := by congr 1; ring
    rw [he,eigen_cutoff_flux_vectors N b (r i) μ (f i) g (hgraph i) hg]
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
    (fun i => inner ℂ (f i).val (multiplier N b g.val)) hflux
  apply hh.trans
  have hA := pow_le_pow_left₀ (norm_nonneg A) (cutoffFluxEnergyVector_norm N b g.val) 2
  have hB := pow_le_pow_left₀ (norm_nonneg B)
    (cutoffFluxAmbientVector_norm N b (eigenEnergyLift N μ g)) 2
  change ‖A‖^2≤(2*|b.gradientBound| *‖g‖)^2 at hA
  change ‖B‖^2≤(2*|b.gradientBound| *‖eigenEnergyLift N μ g‖)^2 at hB
  rw [mul_pow,mul_pow,sq_abs,eigenEnergyLift_norm_sq N μ g hg] at hB
  rw [mul_pow,mul_pow,sq_abs] at hA
  rw [Real.sq_sqrt (show 0≤1+μ by linarith)]
  have hdiv : ‖B‖^2/(1+μ)≤4*b.gradientBound^2*‖g‖^2 := by
    apply (div_le_iff₀ (show 0<1+μ by linarith)).mpr
    nlinarith only [hB]
  have ht : ‖A‖^2+‖B‖^2/(1+μ)≤8*b.gradientBound^2*‖g‖^2 := by
    nlinarith only [hA,hdiv]
  calc
    _ ≤ (2/L^2)*(8*b.gradientBound^2*‖g‖^2) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

#print axioms smooth_cutoff_separated_mass

end QuantitativeMaass.Weighted
