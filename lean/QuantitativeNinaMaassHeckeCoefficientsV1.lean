module

public import QuantitativeNinaMaassPhysicalCoefficientsV1
public import QuantitativeNinaMaassFourierTransportV1
public import QuantitativeMaassHeckeStandardV1
public import QuantitativeMaassHeckeHalfDensityV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology

/-!
The coefficient relation for the actual normalized good-prime Hecke
operator. Coefficients are literal horocycle integrals, not abstract
functionals. The first-mode identity is established for actual continuous
Hilbert eigenvectors. Bessel amplitudes and the ramified operators remain
separate obligations.
-/

namespace QuantitativeNinaMaass

def horocycleFourier (f : ℍ → ℂ) (n : ℤ) (y : {y : ℝ // 0 < y}) : ℂ :=
  unitLineFourierCoeff (fun x => f (horocyclePoint x y.val y.property)) n

theorem horocycleFourier_const_mul (f : ℍ → ℂ) (c : ℂ) (n : ℤ)
    (y : {y : ℝ // 0 < y}) :
    horocycleFourier (fun z => c * f z) n y = c * horocycleFourier f n y :=
  unitLineFourierCoeff_const_mul _ c n

/-- The physical representative has the normalized p+1 branches in the
unscaled coordinate of the cusp at infinity. -/
theorem heckeRepresentative_horocycle (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hNp : (N : ZMod p) ≠ 0)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (x y : ℝ) (hy : 0 < y) :
    (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val (horocyclePoint x y hy) =
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
        (f.val (horocyclePoint ((p : ℝ) * x) ((p : ℝ) * y)
          (mul_pos (by exact_mod_cast (Fact.out : p.Prime).pos) hy)) +
        ∑ a ∈ Finset.range p, f.val (horocyclePoint ((x + a) / p) (y / p)
          (div_pos hy (by exact_mod_cast (Fact.out : p.Prime).pos)))) := by
  rw [← normalizedCuspHecke_eq_representative N p hN hpN hNp A B hAB f]
  rw [normalizedCuspHecke, cuspHeckeSum_eq_one N p hNp f.val f.property.2.1,
    cuspHeckeSum, Fintype.sum_option, Complex.real_smul]
  simp only [cuspBranchGL_none_point, cuspBranchGL_some_point, Nat.cast_one, one_mul]
  congr 2
  exact sum_zmod_val p (fun a => f.val (horocyclePoint ((x + a) / p) (y / p)
    (div_pos hy (by exact_mod_cast (Fact.out : p.Prime).pos))))

/-- The exact good-prime Fourier relation, including its height changes
and normalization, follows from the actual finite-cover operator. -/
theorem horocycleFourier_hecke (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hNp : (N : ZMod p) ≠ 0)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (n : ℤ) (y : {y : ℝ // 0 < y}) :
    horocycleFourier (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val n y =
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
        ((if (p : ℤ) ∣ n then horocycleFourier f.val (n / p)
          ⟨p * y.val, mul_pos (by exact_mod_cast (Fact.out : p.Prime).pos) y.property⟩ else 0) +
        (p : ℂ) * horocycleFourier f.val ((p : ℤ) * n)
          ⟨y.val / p, div_pos y.property (by exact_mod_cast (Fact.out : p.Prime).pos)⟩) := by
  have hp : p.Prime := Fact.out
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  let F : ℝ → ℂ := fun x => f.val (horocyclePoint x (p * y.val) (mul_pos hpR y.property))
  let G : ℝ → ℂ := fun x => f.val (horocyclePoint x (y.val / p) (div_pos y.property hpR))
  have hF : Continuous F := hf.comp (horocyclePoint_continuous _ _)
  have hG : Continuous G := hf.comp (horocyclePoint_continuous _ _)
  have hFp : Function.Periodic F 1 := representative_unit_periodic N f _ _
  have hshape : (fun x => (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val
      (horocyclePoint x y.val y.property)) =
      fun x => (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
        (F ((p : ℝ) * x) + ∑ a ∈ Finset.range p, G ((x + a) / p)) := by
    funext x
    exact heckeRepresentative_horocycle N p hN hpN hNp A B hAB f x y.val y.property
  unfold horocycleFourier
  rw [hshape, unitLineFourierCoeff_const_mul,
    unitLineFourierCoeff_add (fun x => F ((p : ℝ) * x))
      (fun x => ∑ a ∈ Finset.range p, G ((x + a) / p)) (hF.comp (by fun_prop))
      (by exact continuous_finsetSum _ (fun a _ => hG.comp (by fun_prop)))]
  rw [unitLineFourierCoeff_inverse_branch_sum G hG p hp.pos n]
  have hd := unitLineFourierCoeff_dilate F hF hFp (p : ℤ) n (by exact_mod_cast hp.ne_zero)
  simp only [Int.cast_natCast] at hd
  rw [hd]

/-- A Hilbert-space Hecke eigenvector has the same pointwise eigenrelation
on its unique continuous representative. -/
theorem hecke_eigen_representative (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hNp : (N : ZMod p) ≠ 0)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (ell : ℂ)
    (he : HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
      ell • AutomorphicL2.denseEmbedding _ _ f) :
    HeckeL2.heckeRepresentative N p hN hpN A B hAB f = ell • f := by
  apply continuous_representative_unique N _ (ell • f)
  · exact heckeRepresentative_continuous N p hN hpN hNp A B hAB f hf
  · exact continuous_const.mul hf
  · rw [← HeckeL2.operator_on_representatives, map_smul]
    exact he

theorem horocycleFourier_hecke_eigen (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hNp : (N : ZMod p) ≠ 0)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (ell : ℂ)
    (he : HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
      ell • AutomorphicL2.denseEmbedding _ _ f) (n : ℤ) (y : {y : ℝ // 0 < y}) :
    horocycleFourier (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val n y =
      ell * horocycleFourier f.val n y := by
  rw [hecke_eigen_representative N p hN hpN hNp A B hAB f hf ell he]
  exact horocycleFourier_const_mul f.val ell n y

/-- The first Fourier mode determines the p-th mode of an actual
good-prime eigenvector, with the precise square-root normalization. -/
theorem hecke_first_mode (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hNp : (N : ZMod p) ≠ 0)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (ell : ℂ)
    (he : HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) =
      ell • AutomorphicL2.denseEmbedding _ _ f) (y : {y : ℝ // 0 < y}) :
    ell * horocycleFourier f.val 1 y = (Real.sqrt (p : ℝ) : ℂ) *
      horocycleFourier f.val (p : ℤ)
        ⟨y.val / p, div_pos y.property (by exact_mod_cast (Fact.out : p.Prime).pos)⟩ := by
  have hp : p.Prime := Fact.out
  have hn : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have hd : p ∣ 1 := by exact_mod_cast h
    exact hp.not_dvd_one hd
  have hh := horocycleFourier_hecke N p hN hpN hNp A B hAB f hf 1 y
  rw [horocycleFourier_hecke_eigen N p hN hpN hNp A B hAB f hf ell he,
    ite_eq_right hn, zero_add, mul_one] at hh
  rw [hh, ← mul_assoc]
  congr 1
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hs : (Real.sqrt (p : ℝ))⁻¹ * (p : ℝ) = Real.sqrt (p : ℝ) := by
    calc
      _ = (Real.sqrt (p : ℝ))⁻¹ * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) :=
        congrArg (fun x : ℝ => (Real.sqrt (p : ℝ))⁻¹ * x) (Real.mul_self_sqrt hpR.le).symm
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr hpR).ne', one_mul]
  exact_mod_cast hs

#print axioms horocycleFourier_const_mul
#print axioms heckeRepresentative_horocycle
#print axioms horocycleFourier_hecke
#print axioms hecke_eigen_representative
#print axioms horocycleFourier_hecke_eigen
#print axioms hecke_first_mode

end QuantitativeNinaMaass
