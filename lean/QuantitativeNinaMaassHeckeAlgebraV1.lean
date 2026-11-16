module

public import QuantitativeNinaMaassHeckeCoefficientsV1
public import QuantitativeMaassReflectionHeckeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson

/-!
The commuting algebra of the literal height-dependent Fourier action.
Both the index and the height are transported; no Bessel expansion or
height-independent coefficient recurrence is assumed.
-/

namespace QuantitativeNinaMaass

abbrev PositiveHeight := {y : ℝ // 0 < y}

def multiplyHeight (p : ℕ) (hp : 0 < p) (y : PositiveHeight) : PositiveHeight :=
  ⟨(p : ℝ) * y.val, mul_pos (by exact_mod_cast hp) y.property⟩

def divideHeight (p : ℕ) (hp : 0 < p) (y : PositiveHeight) : PositiveHeight :=
  ⟨y.val / p, div_pos y.property (by exact_mod_cast hp)⟩

theorem multiplyHeight_mul (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (y : PositiveHeight) :
    multiplyHeight q hq (multiplyHeight p hp y) = multiplyHeight (p * q) (Nat.mul_pos hp hq) y := by
  apply Subtype.ext
  simp only [multiplyHeight, Nat.cast_mul]
  ring

theorem divideHeight_comm (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (y : PositiveHeight) :
    divideHeight q hq (divideHeight p hp y) = divideHeight p hp (divideHeight q hq y) := by
  apply Subtype.ext
  simp only [divideHeight]
  ring

theorem multiply_divide_height (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (y : PositiveHeight) :
    divideHeight q hq (multiplyHeight p hp y) = multiplyHeight p hp (divideHeight q hq y) := by
  apply Subtype.ext
  simp only [divideHeight, multiplyHeight]
  ring

abbrev HeightCoefficients := ℕ → PositiveHeight → ℂ

def heightUp (p : ℕ) (hp : 0 < p) : Module.End ℂ HeightCoefficients where
  toFun c n y := c (p * n) (divideHeight p hp y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def heightDown (p : ℕ) (hp : 0 < p) : Module.End ℂ HeightCoefficients where
  toFun c n y := if p ∣ n then c (n / p) (multiplyHeight p hp y) else 0
  map_add' c d := by
    funext n y
    by_cases hn : p ∣ n <;> simp [hn]
  map_smul' z c := by
    funext n y
    by_cases hn : p ∣ n <;> simp [hn]

theorem heightUp_up (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (c : HeightCoefficients) :
    heightUp p hp (heightUp q hq c) = heightUp q hq (heightUp p hp c) := by
  funext n y
  change c (q * (p * n)) (divideHeight q hq (divideHeight p hp y)) =
    c (p * (q * n)) (divideHeight p hp (divideHeight q hq y))
  rw [Nat.mul_left_comm q p n, divideHeight_comm]

theorem heightDown_up (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : p.Coprime q)
    (c : HeightCoefficients) :
    heightDown p hp (heightUp q hq c) = heightUp q hq (heightDown p hp c) := by
  funext n y
  change (if p ∣ n then c (q * (n / p)) (divideHeight q hq (multiplyHeight p hp y)) else 0) =
    if p ∣ q * n then c (q * n / p) (multiplyHeight p hp (divideHeight q hq y)) else 0
  simp only [hc.dvd_mul_left]
  split_ifs with hn
  · rw [Nat.mul_div_assoc q hn, multiply_divide_height]
  · rfl

theorem heightDown_down_product (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (c : HeightCoefficients) :
    heightDown p hp (heightDown q hq c) = heightDown (p * q) (Nat.mul_pos hp hq) c := by
  funext n y
  change (if p ∣ n then
      (if q ∣ n / p then c (n / p / q) (multiplyHeight q hq (multiplyHeight p hp y)) else 0)
      else 0) =
    if p * q ∣ n then c (n / (p * q)) (multiplyHeight (p * q) (Nat.mul_pos hp hq) y) else 0
  by_cases hpn : p ∣ n
  · have he : q ∣ n / p ↔ p * q ∣ n := by
      simpa only [Nat.mul_comm q p] using Nat.dvd_div_iff_mul_dvd hpn
    simp only [hpn, ite_eq_left, he]
    split_ifs
    · rw [Nat.div_div_eq_div_mul, multiplyHeight_mul]
    · rfl
  · have hn : ¬ p * q ∣ n := fun h => hpn (dvd_trans (Nat.dvd_mul_right p q) h)
    simp only [hpn, hn, ite_false]

theorem heightDown_down (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (c : HeightCoefficients) :
    heightDown p hp (heightDown q hq c) = heightDown q hq (heightDown p hp c) := by
  rw [heightDown_down_product, heightDown_down_product]
  congr 2
  exact Nat.mul_comm p q

/-- The exact normalized p+1 Fourier action, with coefficients still
depending on the positive height. -/
def heightHecke (p : ℕ) (hp : 0 < p) : Module.End ℂ HeightCoefficients :=
  ((((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) * (p : ℂ)) • heightUp p hp +
    (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) • heightDown p hp

theorem heightHecke_commute (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : p.Coprime q) :
    Commute (heightHecke p hp) (heightHecke q hq) := by
  apply LinearMap.ext
  intro c
  change heightHecke p hp (heightHecke q hq c) = heightHecke q hq (heightHecke p hp c)
  simp only [heightHecke, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  rw [heightUp_up p q hp hq, heightDown_up p q hp hq hc,
    ← heightDown_up q p hq hp hc.symm, heightDown_down p q hp hq]
  module

def actualHeightCoefficients (f : UpperHalfPlane → ℂ) : HeightCoefficients :=
  fun n y => horocycleFourier f (n : ℤ) y

/-- Identification with the actual finite-cover Hecke operator. -/
theorem actualHeightCoefficients_hecke (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hNp : (N : ZMod p) ≠ 0)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    actualHeightCoefficients (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val =
      heightHecke p (Fact.out : p.Prime).pos (actualHeightCoefficients f.val) := by
  funext n y
  change horocycleFourier (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val (n : ℤ) y = _
  rw [horocycleFourier_hecke N p hN hpN hNp A B hAB f hf]
  simp only [heightHecke, LinearMap.add_apply, LinearMap.smul_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, heightUp, heightDown, LinearMap.coe_mk, AddHom.coe_mk,
    actualHeightCoefficients, multiplyHeight, divideHeight]
  by_cases hn : p ∣ n
  · have hnZ : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
    simp only [hn, hnZ, ite_eq_left, Int.natCast_ediv, Nat.cast_mul]
    ring
  · have hnZ : ¬ (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
    simp only [hn, hnZ, ite_false, mul_zero, zero_add, add_zero, Nat.cast_mul]
    ring

/-- All nonnegative horocycle integrals determine an actual continuous
representative of fixed reflection parity, including its constant term. -/
theorem actualHeightCoefficients_separate (N : ℕ)
    (f g : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hg : Continuous g.val) (s : ℂ)
    (hsf : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f)
    (hsg : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ g) =
      s • AutomorphicL2.denseEmbedding _ _ g)
    (he : actualHeightCoefficients f.val = actualHeightCoefficients g.val) : f = g := by
  apply Subtype.ext
  funext z
  have hh := continuous_periodic_eq_of_nonnegative_fourier
    (fun x => f.val (horocyclePoint x z.im z.im_pos))
    (fun x => g.val (horocyclePoint x z.im z.im_pos))
    (hf.comp (horocyclePoint_continuous z.im z.im_pos))
    (hg.comp (horocyclePoint_continuous z.im z.im_pos))
    (representative_unit_periodic N f z.im z.im_pos)
    (representative_unit_periodic N g z.im z.im_pos) s
    (fun x => representative_pointwise_parity N f hf s hsf x z.im z.im_pos)
    (fun x => representative_pointwise_parity N g hg s hsg x z.im z.im_pos)
    (fun n => congrFun (congrFun he n) ⟨z.im, z.im_pos⟩)
  exact congrFun hh z.re

theorem heckeRepresentative_reflection_eigen (N p : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hNp : (N : ZMod p) ≠ 0)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) (s : ℂ)
    (hs : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f) :
    reflectionIsometry N (AutomorphicL2.denseEmbedding _ _
      (HeckeL2.heckeRepresentative N p hN hpN A B hAB f)) =
        s • AutomorphicL2.denseEmbedding _ _ (HeckeL2.heckeRepresentative N p hN hpN A B hAB f) := by
  simp only [← HeckeL2.operator_on_representatives]
  have hh := DFunLike.congr_fun (reflectionIsometry_hecke_commute N p hN hpN hNp A B hAB)
    (AutomorphicL2.denseEmbedding _ _ f)
  change reflectionIsometry N (HeckeL2.operator N p hN hpN A B hAB
      (AutomorphicL2.denseEmbedding _ _ f)) =
    HeckeL2.operator N p hN hpN A B hAB (reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f)) at hh
  rw [hh, hs, map_smul]

/-- Coprime good-prime correspondences commute on actual continuous
automorphic representatives of fixed reflection parity. The proof uses
the literal Fourier action and the proved uniqueness theorem. -/
theorem heckeRepresentatives_commute_parity (N p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (hqN : ¬ q ∣ N)
    (hNp : (N : ZMod p) ≠ 0) (hNq : (N : ZMod q) ≠ 0) (hpq : p.Coprime q)
    (A B C D : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (hCD : (q : ℤ) * C + (N : ℤ) * D = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (s : ℂ)
    (hs : reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ f) =
      s • AutomorphicL2.denseEmbedding _ _ f) :
    HeckeL2.heckeRepresentative N p hN hpN A B hAB
      (HeckeL2.heckeRepresentative N q hN hqN C D hCD f) =
    HeckeL2.heckeRepresentative N q hN hqN C D hCD
      (HeckeL2.heckeRepresentative N p hN hpN A B hAB f) := by
  have hpcont := heckeRepresentative_continuous N p hN hpN hNp A B hAB f hf
  have hqcont := heckeRepresentative_continuous N q hN hqN hNq C D hCD f hf
  have hpse := heckeRepresentative_reflection_eigen N p hN hpN hNp A B hAB f s hs
  have hqse := heckeRepresentative_reflection_eigen N q hN hqN hNq C D hCD f s hs
  apply actualHeightCoefficients_separate N _ _
    (heckeRepresentative_continuous N p hN hpN hNp A B hAB _ hqcont)
    (heckeRepresentative_continuous N q hN hqN hNq C D hCD _ hpcont) s
    (heckeRepresentative_reflection_eigen N p hN hpN hNp A B hAB _ s hqse)
    (heckeRepresentative_reflection_eigen N q hN hqN hNq C D hCD _ s hpse)
  rw [actualHeightCoefficients_hecke N p hN hpN hNp A B hAB _ hqcont,
    actualHeightCoefficients_hecke N q hN hqN hNq C D hCD f hf,
    actualHeightCoefficients_hecke N q hN hqN hNq C D hCD _ hpcont,
    actualHeightCoefficients_hecke N p hN hpN hNp A B hAB f hf]
  exact DFunLike.congr_fun
    (heightHecke_commute p q (Fact.out : p.Prime).pos (Fact.out : q.Prime).pos hpq)
      (actualHeightCoefficients f.val)

#print axioms multiplyHeight_mul
#print axioms divideHeight_comm
#print axioms multiply_divide_height
#print axioms heightUp_up
#print axioms heightDown_up
#print axioms heightDown_down_product
#print axioms heightDown_down
#print axioms heightHecke_commute
#print axioms actualHeightCoefficients_hecke
#print axioms actualHeightCoefficients_separate
#print axioms heckeRepresentative_reflection_eigen
#print axioms heckeRepresentatives_commute_parity

end QuantitativeNinaMaass
