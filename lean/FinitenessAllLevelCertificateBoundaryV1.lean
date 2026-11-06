module

public import FinitenessAllLevelBoundaryGeometryV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCertificateBoundary

open Complex Metric Set MeasureTheory FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelCauchyOperator
  QuantitativeArithmeticRetainedCertificate SpanningIntegerRows
  FinitenessAllLevelReconstruction FinitenessAllLevelGoodTrace

variable {N Q p : ℕ} {hQ : 0 < Q}

def lift {r : ℝ} (f : space r) (z : ℂ) : ℂ :=
  extend f.val (Function.Periodic.qParam 1 z)

def shift (Q : ℕ) (j : Fin Q) (u : ℤ) : ℝ := ((u : ℝ) - (j.val : ℝ)) / Q

theorem line_shift (Q : ℕ) (j : Fin Q) (u : ℤ) (x b : ℝ) :
    line (x + shift Q j u) b = line x b + ((u : ℂ) - (j.val : ℂ)) / Q := by
  unfold line shift
  push_cast
  ring

theorem row_level_pos (hN : 0 < N) (hQ : 0 < Q) (i : RowIndex N Q) :
    (0 : ℝ) < Nat.lcm N (i.val.1 ^ 2) := by
  exact_mod_cast Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos i.property.1 hQ) 2)

/-- The eigenvalue-free part of one certificate row: primitive Fricke
samples, or the negative second dilation for a retained row. -/
def row₀ (hN : 0 < N) (A : Certificate N {p} Q hQ)
    (r : ℝ) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 < b)
    (cell : Set ℂ) (hc : MeasurableSet cell) (x : ℂ → ℝ) (hx : Measurable x)
    (χ : ℕ → ℂ) (m : ℕ) (j : Fin Q) :
    AugIndex N (({p} : Finset ℕ) : Set ℕ) Q → BoundaryOperator (space r) R
  | Sum.inl i => FinitenessAllLevelBoundarySampling.sum
      ((Finset.range i.val.1).filter (fun a => Nat.Coprime a i.val.1))
      (fun a => frickeCell r hR (row_level_pos hN hQ i) hb cell hc
        (shift Q j i.val.2) ((a : ℝ) / i.val.1) x hx
        ((A.coeff j (Sum.inl i) : ℂ) * χ i.val.1) (2 * m))
  | Sum.inr i => dilationCell r hR cell hc ((i.1.val : ℝ) ^ 2) b
      (shift Q j i.2) x hx (-(A.coeff j (Sum.inr i) : ℂ) * (i.1.val : ℂ) ^ (2 * m))

/-- The coefficient of the one retained eigenvalue in a certificate row. -/
def row₁ (A : Certificate N {p} Q hQ) (r : ℝ) {R : ℝ} (hR : 0 ≤ R) (b : ℝ)
    (cell : Set ℂ) (hc : MeasurableSet cell) (x : ℂ → ℝ) (hx : Measurable x)
    (m : ℕ) (j : Fin Q) : AugIndex N (({p} : Finset ℕ) : Set ℕ) Q → BoundaryOperator (space r) R
  | Sum.inl _ => FinitenessAllLevelBoundarySampling.zero (space r) R
  | Sum.inr i => dilationCell r hR cell hc (i.1.val : ℝ) b (shift Q j i.2) x hx
      ((A.coeff j (Sum.inr i) : ℂ) * (i.1.val : ℂ) ^ m * (Real.sqrt i.1.val : ℂ))

/-- On its chosen cell, the two bounded boundary operators are precisely
the actual two-dilation reconstruction row, with the eigenvalue separated. -/
theorem row_formula (hN : 0 < N) (A : Certificate N {p} Q hQ)
    (r : ℝ) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 < b)
    (cell : Set ℂ) (hc : MeasurableSet cell) (x : ℂ → ℝ) (hx : Measurable x)
    (χ : ℕ → ℂ) (m : ℕ) (j : Fin Q) (i : AugIndex N (({p} : Finset ℕ) : Set ℕ) Q)
    (f : space r) (lam w : ℂ) (hw : w ∈ cell) :
    (row₀ hN A r hR hb cell hc x hx χ m j i).data f w +
        lam * (row₁ A r hR b cell hc x hx m j i).data f w =
      (A.coeff j i : ℂ) * twoDilationRow (lift f) (2 * m) χ
        (firstMultiplier (fun _ => lam) m) (fun q => (q : ℂ) ^ (2 * m)) j (line (x w) b) i := by
  cases i with
  | inl i =>
    simp only [row₀, row₁, FinitenessAllLevelBoundarySampling.zero,
      LinearMap.zero_apply, Pi.zero_apply, mul_zero, add_zero,
      FinitenessAllLevelBoundarySampling.sum_apply, frickeCell,
      FinitenessAllLevelBoundarySampling.cellSample_apply, indicator_of_mem hw,
      frickeWeight, frickeSource, line_shift, twoDilationRow,
      QuantitativeArithmeticRetainedReconstruction.frickeRow,
      FinitenessAnalyticReconstruction.twist, lift, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    ring
  | inr i =>
    simp only [row₀, row₁, dilationCell, FinitenessAllLevelBoundarySampling.cellSample_apply,
      indicator_of_mem hw, dilationSource, line_shift, twoDilationRow, firstMultiplier, lift]
    push_cast
    ring

theorem row_outside (hN : 0 < N) (A : Certificate N {p} Q hQ)
    (r : ℝ) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 < b)
    (cell : Set ℂ) (hc : MeasurableSet cell) (x : ℂ → ℝ) (hx : Measurable x)
    (χ : ℕ → ℂ) (m : ℕ) (j : Fin Q) (i : AugIndex N (({p} : Finset ℕ) : Set ℕ) Q)
    (f : space r) (w : ℂ) (hw : w ∉ cell) :
    (row₀ hN A r hR hb cell hc x hx χ m j i).data f w = 0 ∧
      (row₁ A r hR b cell hc x hx m j i).data f w = 0 := by
  cases i <;> simp [row₀, row₁, frickeCell, dilationCell,
    FinitenessAllLevelBoundarySampling.sum_apply,
    FinitenessAllLevelBoundarySampling.cellSample_apply,
    FinitenessAllLevelBoundarySampling.zero, indicator_of_notMem hw]

def cell₀ (hN : 0 < N) (A : Certificate N {p} Q hQ)
    (r : ℝ) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 < b)
    (cell : Set ℂ) (hc : MeasurableSet cell) (x : ℂ → ℝ) (hx : Measurable x)
    (χ : ℕ → ℂ) (m : ℕ) (j : Fin Q) : BoundaryOperator (space r) R :=
  FinitenessAllLevelBoundarySampling.sum (A.coeff j).support
    (row₀ hN A r hR hb cell hc x hx χ m j)

def cell₁ (A : Certificate N {p} Q hQ) (r : ℝ) {R : ℝ} (hR : 0 ≤ R) (b : ℝ)
    (cell : Set ℂ) (hc : MeasurableSet cell) (x : ℂ → ℝ) (hx : Measurable x)
    (m : ℕ) (j : Fin Q) : BoundaryOperator (space r) R :=
  FinitenessAllLevelBoundarySampling.sum (A.coeff j).support (row₁ A r hR b cell hc x hx m j)

theorem cell_formula (hN : 0 < N) (A : Certificate N {p} Q hQ)
    (r : ℝ) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 < b)
    (cell : Set ℂ) (hc : MeasurableSet cell) (x : ℂ → ℝ) (hx : Measurable x)
    (χ : ℕ → ℂ) (m : ℕ) (j : Fin Q) (f : space r) (lam w : ℂ) (hw : w ∈ cell) :
    (cell₀ hN A r hR hb cell hc x hx χ m j).data f w +
        lam * (cell₁ A r hR b cell hc x hx m j).data f w =
      ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) *
        twoDilationRow (lift f) (2 * m) χ (firstMultiplier (fun _ => lam) m)
          (fun q => (q : ℂ) ^ (2 * m)) j (line (x w) b) i := by
  simp only [cell₀, cell₁, FinitenessAllLevelBoundarySampling.sum_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => row_formula hN A r hR hb cell hc x hx χ m j i f lam w hw)

theorem cell_outside (hN : 0 < N) (A : Certificate N {p} Q hQ)
    (r : ℝ) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 < b)
    (cell : Set ℂ) (hc : MeasurableSet cell) (x : ℂ → ℝ) (hx : Measurable x)
    (χ : ℕ → ℂ) (m : ℕ) (j : Fin Q) (f : space r) (w : ℂ) (hw : w ∉ cell) :
    (cell₀ hN A r hR hb cell hc x hx χ m j).data f w = 0 ∧
      (cell₁ A r hR b cell hc x hx m j).data f w = 0 := by
  simp only [cell₀, cell₁, FinitenessAllLevelBoundarySampling.sum_apply]
  constructor
  · exact Finset.sum_eq_zero (fun i _ =>
      (row_outside hN A r hR hb cell hc x hx χ m j i f w hw).1)
  · exact Finset.sum_eq_zero (fun i _ =>
      (row_outside hN A r hR hb cell hc x hx χ m j i f w hw).2)

#print axioms row_formula
#print axioms row_outside
#print axioms cell_formula

end FinitenessAllLevelCertificateBoundary
