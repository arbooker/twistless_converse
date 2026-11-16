module

public import QuantitativeMaassAbelSpectralIdentificationV1
public import QuantitativeMaassHilbertSchmidtV1
public import QuantitativeMaassRadialKernelPairingV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace BigOperators

namespace QuantitativeMaass

/-- Exact square energy of a literal periodized radial kernel row. -/
theorem radialKernel_row_energy (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ) :
    ‖poincareSeedVector N (radialSeed g hg x R hR hs)‖^2=
      ∫ y,‖radialPoincareKernel N g x y‖^2 ∂quotientMeasure N := by
  change ‖(poincareSeedVector N (radialSeed g hg x R hR hs)).val‖^2=_
  rw [← inner_self_eq_norm_sq (𝕜:=ℝ),L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [poincareSeedVector_coeFn N (radialSeed g hg x R hR hs)] with y hy
  rw [hy]
  rfl

/-- Pointwise Parseval for the actual radial integral output on a full
quotient Hilbert basis. In particular its square sum is genuinely summable. -/
theorem radialKernel_output_parseval {ι : Type*} (N : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hr : ∀ q,star (g q)=g q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ) :
    HasSum (fun i => ‖(radialKernelData N g hg R hR hs).output (b i).val x‖^2)
      (∫ y,‖radialPoincareKernel N g x y‖^2 ∂quotientMeasure N) := by
  have h := hasSum_inner_norm_sq b (poincareSeedVector N (radialSeed g hg x R hR hs))
  simp_rw [radialKernel_column_inner N g hg R hR hs hr x] at h
  rw [radialKernel_row_energy] at h
  exact h

/-- Finite Bessel bound on literal radial-kernel outputs. This does not
assume a discrete spectral basis or a trace-class statement. -/
theorem radialKernel_output_bessel {ι : Type*} (N : ℕ) (v : ι → AutomorphicSpace N)
    (hv : Orthonormal ℂ v) (s : Finset ι)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hr : ∀ q,star (g q)=g q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ) :
    (∑ i∈s,‖(radialKernelData N g hg R hR hs).output (v i).val x‖^2)≤
      ∫ y,‖radialPoincareKernel N g x y‖^2 ∂quotientMeasure N := by
  have h := hv.sum_inner_products_le (s:=s) (poincareSeedVector N (radialSeed g hg x R hR hs))
  simp_rw [norm_inner_symm (v _) _,radialKernel_column_inner N g hg R hR hs hr x] at h
  rw [radialKernel_row_energy] at h
  exact h

/-- Actual spectral packet values have the literal geometric integral
representative, now that Abel identification is proved. -/
theorem coshWavePacket_coeFn (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) (f : AutomorphicSpace N) :
    (coshWavePacket N F hF R hR hs f).val=ᵐ[quotientMeasure N]
      (radialKernelData N (abelProfile F) (abelProfile_smooth F hF hc)
        R hR (abelProfile_support F _ hs)).output f.val := by
  rw [← abelKernelOperator_eq_coshWavePacket N F hF hc hr R hR hs]
  exact radialKernelOperator_coeFn N (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hs) f

/-- A local squared-kernel pretrace identity for the actual spectral
packet. This is an almost-everywhere identity; a global trace estimate and
an eigenbasis/counting interpretation remain separate steps. -/
theorem coshWavePacket_pretrace {ι : Type*} [Countable ι] (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    ∀ᵐ x ∂quotientMeasure N,
      HasSum (fun i => ‖(coshWavePacket N F hF R hR hs (b i)).val x‖^2)
        (∫ y,‖radialPoincareKernel N (abelProfile F) x y‖^2 ∂quotientMeasure N) := by
  have he : ∀ᵐ x ∂quotientMeasure N,∀ i,
      (coshWavePacket N F hF R hR hs (b i)).val x=
        (radialKernelData N (abelProfile F) (abelProfile_smooth F hF hc)
          R hR (abelProfile_support F _ hs)).output (b i).val x :=
    ae_all_iff.mpr (fun i => coshWavePacket_coeFn N F hF hc hr R hR hs (b i))
  filter_upwards [he] with x hx
  simp_rw [hx]
  exact radialKernel_output_parseval N b (abelProfile F) (abelProfile_smooth F hF hc)
    (abelProfile_real F hr) R hR (abelProfile_support F _ hs) x

#print axioms radialKernel_row_energy
#print axioms radialKernel_output_parseval
#print axioms radialKernel_output_bessel
#print axioms coshWavePacket_coeFn
#print axioms coshWavePacket_pretrace

end QuantitativeMaass
