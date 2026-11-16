module

public import QuantitativeMaassWeightedCutoffV1
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open scoped InnerProductSpace

namespace QuantitativeMaass

/-- The canonical form-domain lift of an actual Friedrichs eigenvector. -/
def eigenEnergyLift (N : ℕ) (r : ℝ) (f : AutomorphicSpace N) :
    QuotientEnergySpace N :=
  (energyInclusion N).adjoint (f+(r:ℂ) • f)

theorem eigenEnergyLift_inclusion (N : ℕ) (r : ℝ) (f : AutomorphicSpace N)
    (hf : FriedrichsGraph N f ((r:ℂ) • f)) :
    energyInclusion N (eigenEnergyLift N r f)=f := hf

theorem eigenEnergyLift_pairing (N : ℕ) (r : ℝ) (f : AutomorphicSpace N)
    (u : QuotientEnergySpace N) :
    inner ℂ u (eigenEnergyLift N r f)=
      (1+(r:ℂ))*inner ℂ (energyInclusion N u) f := by
  unfold eigenEnergyLift
  rw [(energyInclusion N).adjoint_inner_right,inner_add_right]
  have hs : inner ℂ (energyInclusion N u) ((r:ℂ) • f)=
      (r:ℂ)*inner ℂ (energyInclusion N u) f :=
    _root_.inner_smul_right (𝕜 := ℂ) (energyInclusion N u) f (r:ℂ)
  rw [hs]
  ring

theorem eigenEnergyLift_form (N : ℕ) (r : ℝ) (f : AutomorphicSpace N)
    (hf : FriedrichsGraph N f ((r:ℂ) • f)) (u : QuotientEnergySpace N) :
    quotientClosedEnergy N u (eigenEnergyLift N r f)=
      (r:ℂ)*inner ℂ (energyInclusion N u) f := by
  rw [quotientClosedEnergy,eigenEnergyLift_pairing,eigenEnergyLift_inclusion N r f hf]
  ring

theorem eigenEnergyLift_norm_sq (N : ℕ) (r : ℝ) (f : AutomorphicSpace N)
    (hf : FriedrichsGraph N f ((r:ℂ) • f)) :
    ‖eigenEnergyLift N r f‖^2=(1+r)*‖f‖^2 := by
  have hh := congrArg Complex.re (eigenEnergyLift_pairing N r f (eigenEnergyLift N r f))
  rw [eigenEnergyLift_inclusion N r f hf] at hh
  have h₁ : (inner ℂ (eigenEnergyLift N r f) (eigenEnergyLift N r f)).re=
      ‖eigenEnergyLift N r f‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h₂ : (inner ℂ f f).re=‖f‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  simpa only [Complex.mul_re,Complex.add_re,Complex.one_re,Complex.ofReal_re,
    Complex.add_im,Complex.one_im,Complex.ofReal_im,zero_add,zero_mul,sub_zero,
    h₁,h₂] using hh

/-- Normalizing in the actual form norm gives another orthonormal family.
This supplies Bessel estimates for cutoff fluxes without a spectral-band
invariance assumption for the cutoff. -/
theorem eigenEnergyLift_orthonormal {ι : Type*} (N : ℕ) (r : ι → ℝ)
    (f : ι → AutomorphicSpace N) (hf : Orthonormal ℂ f)
    (hr : ∀ i,0≤r i) (hg : ∀ i,FriedrichsGraph N (f i) ((r i:ℂ) • f i)) :
    Orthonormal ℂ (fun i => ((Real.sqrt (1+r i))⁻¹:ℂ) • eigenEnergyLift N (r i) (f i)) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [_root_.inner_smul_left,_root_.inner_smul_right,eigenEnergyLift_pairing,
    eigenEnergyLift_inclusion N (r i) (f i) (hg i),orthonormal_iff_ite.mp hf i j]
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    have hs : Real.sqrt (1+r i)≠0 := ne_of_gt (Real.sqrt_pos.2 (by linarith [hr i]))
    have he : ((Real.sqrt (1+r i):ℂ))^2=1+(r i:ℂ) := by
      exact_mod_cast Real.sq_sqrt (show 0≤1+r i by linarith [hr i])
    rw [←he]
    field_simp
    rw [map_div₀,map_one]
    rw [show (starRingEnd ℂ) (Real.sqrt (1+r i):ℂ)=(Real.sqrt (1+r i):ℂ)
      from Complex.conj_ofReal _]
    field_simp
    exact div_self (Complex.ofReal_ne_zero.mpr hs)
  · simp [hij]

#print axioms eigenEnergyLift_inclusion
#print axioms eigenEnergyLift_pairing
#print axioms eigenEnergyLift_form
#print axioms eigenEnergyLift_norm_sq
#print axioms eigenEnergyLift_orthonormal

end QuantitativeMaass
