module

public import QuantitativeNinaMaassNewParityEnergyBandsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeMaass AsymptoticClassicalPetersson
open scoped ENNReal InnerProductSpace

namespace QuantitativeNinaMaass

/-- Group a nonnegative spectral sum by its actual principal parameter.
The finite fibers are the literal sharp spectral windows, including their
multiplicities; no ordering or enumeration of the eigenvalues is assumed. -/
theorem principalWeight_tsum_fibers {ι : Type*} (e w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ r, (principalWindowIndices e r r).Finite)
    (F : ℝ → ℝ≥0∞) :
    (∑' i : {i // 1 / 4 ≤ e i}, F (Real.sqrt (e i.val - 1 / 4)) * ENNReal.ofReal (w i.val)) =
      ∑' r, F r * ENNReal.ofReal (principalWindowWeight e w r r) := by
  let g := fun i : {i // 1 / 4 ≤ e i} => Real.sqrt (e i.val - 1 / 4)
  rw [← ENNReal.tsum_fiberwise _ g]
  apply tsum_congr
  intro r
  let E : (g ⁻¹' {r}) ≃ principalWindowIndices e r r :=
    { toFun := fun i => ⟨i.val.val, i.val.property, le_of_eq i.property.symm, le_of_eq i.property⟩
      invFun := fun i => ⟨⟨i.val, i.property.1⟩, le_antisymm i.property.2.2 i.property.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hg (i : g ⁻¹' {r}) : g i.val = r := i.property
  change (∑' i : g ⁻¹' {r}, F (g i.val) * ENNReal.ofReal (w i.val.val)) = _
  simp_rw [hg]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have heq := E.tsum_eq (fun i : principalWindowIndices e r r => ENNReal.ofReal (w i.val))
  change (∑' i : g ⁻¹' {r}, ENNReal.ofReal (w i.val.val)) =
    ∑' i : principalWindowIndices e r r, ENNReal.ofReal (w i.val) at heq
  change (∑' i : g ⁻¹' {r}, ENNReal.ofReal (w i.val.val)) = _
  rw [heq]
  let : Fintype (principalWindowIndices e r r) := (hf r).fintype
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun i : principalWindowIndices e r r => hw i.val) Summable.of_finite).symm

/-- Nonnegative weighted singleton dimensions of the actual partial-new
parity bands. Extended sums allow the exact recurrence to be proved before
trace finiteness, without subtracting divergent real series. -/
def partialParityEnergyMass (N : ℕ) (P : Set ℕ) (η : ℝ) (F : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' r, F r * (partialParityCount N P r r η : ℝ≥0∞)

/-- The already proved physical two-old-image dimension recurrence lifts
to every nonnegative spectral multiplier with coefficient two. -/
theorem partialParityEnergyMass_simple (M p : ℕ) (hM : 0 < M) (hp : p.Prime)
    (hcp : p.Coprime M) (P : Set ℕ) (hpP : p ∉ P) (η : ℝ) (F : ℝ → ℝ≥0∞) :
    partialParityEnergyMass (p * M) (insert p P) η F +
      2 * partialParityEnergyMass M P η F = partialParityEnergyMass (p * M) P η F := by
  unfold partialParityEnergyMass
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply tsum_congr
  intro r
  have hh : (partialParityCount (p * M) (insert p P) r r η : ℝ≥0∞) +
      2 * (partialParityCount M P r r η : ℝ≥0∞) =
        (partialParityCount (p * M) P r r η : ℝ≥0∞) := by
    exact_mod_cast partialParityCount_simple M p hM hp hcp P hpP r r η
  calc
    _ = F r * ((partialParityCount (p * M) (insert p P) r r η : ℝ≥0∞) +
      2 * (partialParityCount M P r r η : ℝ≥0∞)) := by ring
    _ = _ := by rw [hh]

theorem partialParityEnergyMass_covers (N : ℕ) (hN : 0 < N) (P : Set ℕ)
    (hP : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ P) (η : ℝ) (F : ℝ → ℝ≥0∞) :
    partialParityEnergyMass N P η F = partialParityEnergyMass N univ η F := by
  simp only [partialParityEnergyMass, partialParityCount_covers N hN P hP]

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- With no trace equations, the actual partial-new dimension is the
whole physical parity-band dimension. -/
theorem partialParityCount_empty_eq (N : ℕ) [NeZero N] (hN : 0 < N) (a b η : ℝ) :
    partialParityCount N ∅ a b η =
      Module.finrank ℂ ((geometricCuspSpectrum N hN).parityBand a b η) := by
  rw [partialParityCount_eq N hN]
  exact ((LinearEquiv.ofEq _ _
    ((geometricCuspSpectrum N hN).partialParityBand_empty a b η)).trans
      Submodule.topEquiv).finrank_eq

/-- The repeated-prime base keeps the actual common old image. This is
the exact finite-band identity at every level divisible by four. -/
theorem partialParityCount_repeated_two (L : ℕ) (hL : 0 < L)
    (a b η : ℝ) (hη : η ^ 2 = 1) :
    partialParityCount (2 * (2 * L)) {2} a b η +
      2 * partialParityCount (2 * L) ∅ a b η =
        partialParityCount (2 * (2 * L)) ∅ a b η + partialParityCount L ∅ a b η := by
  let : NeZero L := ⟨hL.ne'⟩
  have h2 : 0 < 2 * L := Nat.mul_pos (by decide) hL
  have h4 : 0 < 2 * (2 * L) := Nat.mul_pos (by decide) h2
  let S := geometricCuspSpectrum L hL
  let T := geometricCuspSpectrum (2 * L) h2
  let V := geometricCuspSpectrum (2 * (2 * L)) h4
  have hcount : partialParityCount (2 * (2 * L)) {2} a b η =
      Module.finrank ℂ (T.traceNewParityBand V (Nat.dvd_mul_left (2 * L) 2) a b η) := by
    rw [partialParityCount_eq _ h4]
    apply LinearEquiv.finrank_eq
    apply LinearEquiv.ofEq
    change V.partialParityBand a b η {2} = _
    rw [show ({2} : Set ℕ) = insert 2 ∅ by ext p; simp,
      CuspEnergySpectrum.partialParityBand_insert (2 * L) 2 h2 Nat.prime_two T V a b η ∅,
      CuspEnergySpectrum.partialParityBand_empty, inf_top_eq]
  rw [hcount, partialParityCount_empty_eq (2 * L) h2,
    partialParityCount_empty_eq (2 * (2 * L)) h4, partialParityCount_empty_eq L hL]
  exact CuspEnergySpectrum.repeated_traceNewParityBand_finrank L 2 hL Nat.prime_two
    (two_level_relIndex_prime L hL) S T V a b η hη

/-- The actual overlap recurrence persists for arbitrary nonnegative
spectral weights, including the compact-window multipliers. -/
theorem partialParityEnergyMass_repeated_two (L : ℕ) (hL : 0 < L)
    (η : ℝ) (hη : η ^ 2 = 1) (F : ℝ → ℝ≥0∞) :
    partialParityEnergyMass (2 * (2 * L)) {2} η F +
      2 * partialParityEnergyMass (2 * L) ∅ η F =
        partialParityEnergyMass (2 * (2 * L)) ∅ η F + partialParityEnergyMass L ∅ η F := by
  unfold partialParityEnergyMass
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply tsum_congr
  intro r
  have hh : (partialParityCount (2 * (2 * L)) {2} r r η : ℝ≥0∞) +
      2 * (partialParityCount (2 * L) ∅ r r η : ℝ≥0∞) =
        (partialParityCount (2 * (2 * L)) ∅ r r η : ℝ≥0∞) +
          (partialParityCount L ∅ r r η : ℝ≥0∞) := by
    exact_mod_cast partialParityCount_repeated_two L hL r r η hη
  calc
    _ = F r * ((partialParityCount (2 * (2 * L)) {2} r r η : ℝ≥0∞) +
      2 * (partialParityCount (2 * L) ∅ r r η : ℝ≥0∞)) := by ring
    _ = _ := by rw [hh]; ring

/-- The singleton-mass notation is exactly the actual new-parity
projection-weighted principal spectral sum, not an auxiliary count model. -/
theorem partialParityEnergyMass_univ_eq (N : ℕ) [NeZero N] (hN : 0 < N)
    (η : ℝ) (hη : η ^ 2 = 1) (F : ℝ → ℝ≥0∞) :
    partialParityEnergyMass N univ η F =
      ∑' i : {i // 1 / 4 ≤ (geometricCuspSpectrum N hN).energy i},
        F (Real.sqrt ((geometricCuspSpectrum N hN).energy i.val - 1 / 4)) *
          ENNReal.ofReal (newParitySpectralWeight (geometricCuspSpectrum N hN) η i.val) := by
  let S := geometricCuspSpectrum N hN
  have ho := S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  have hf (r : ℝ) : (principalWindowIndices S.energy r r).Finite :=
    principalWindowIndices_finite N hN _ ho (fun j => (S.basis j).property)
      S.energy S.energy_nonneg S.graph r r
  rw [principalWeight_tsum_fibers S.energy (newParitySpectralWeight S η)
    (fun i => (newParitySpectralWeight_bounds S η i).1) hf F]
  unfold partialParityEnergyMass
  apply tsum_congr
  intro r
  rw [sharp_newParity_weight_eq_dimension S r r η hη, partialParityCount_eq N hN]
  simp only [ENNReal.ofReal_natCast]
  rfl

/-- The empty partial-new mass is the genuine geometric parity-weighted
principal spectrum. This is the base for weighted old/new recurrence. -/
theorem partialParityEnergyMass_empty_eq (N : ℕ) [NeZero N] (hN : 0 < N)
    (η : ℝ) (hη : η ^ 2 = 1) (F : ℝ → ℝ≥0∞) :
    partialParityEnergyMass N ∅ η F =
      ∑' i : {i // 1 / 4 ≤ (geometricCuspSpectrum N hN).energy i},
        F (Real.sqrt ((geometricCuspSpectrum N hN).energy i.val - 1 / 4)) *
          ENNReal.ofReal (‖parityProjection N η
            ((geometricCuspSpectrum N hN).basis i.val : AutomorphicSpace N)‖ ^ 2) := by
  let S := geometricCuspSpectrum N hN
  have ho := S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  have hf (r : ℝ) : (principalWindowIndices S.energy r r).Finite :=
    principalWindowIndices_finite N hN _ ho (fun j => (S.basis j).property)
      S.energy S.energy_nonneg S.graph r r
  rw [principalWeight_tsum_fibers S.energy
    (fun i => ‖parityProjection N η (S.basis i : AutomorphicSpace N)‖ ^ 2)
    (fun _ => sq_nonneg _) hf F]
  unfold partialParityEnergyMass
  apply tsum_congr
  intro r
  rw [sharp_parity_weight_eq_dimension N hN S.basis S.energy S.energy_nonneg S.graph r r η hη,
    partialParityCount_empty_eq N hN]
  simp only [ENNReal.ofReal_natCast]
  rfl

/-- Adding actual trace equations decreases the finite band dimension. -/
theorem partialParityCount_le_empty (N : ℕ) (hN : 0 < N) (P : Set ℕ) (a b η : ℝ) :
    partialParityCount N P a b η ≤ partialParityCount N ∅ a b η := by
  let : NeZero N := ⟨hN.ne'⟩
  let S := geometricCuspSpectrum N hN
  let := S.band_finiteDimensional a b
  rw [partialParityCount_eq N hN, partialParityCount_empty_eq N hN]
  exact Submodule.finrank_le _

/-- All partial masses are controlled by the actual full-cusp parity
mass, supplying finiteness once the physical packet energy is finite. -/
theorem partialParityEnergyMass_le_empty (N : ℕ) (hN : 0 < N) (P : Set ℕ)
    (η : ℝ) (F : ℝ → ℝ≥0∞) :
    partialParityEnergyMass N P η F ≤ partialParityEnergyMass N ∅ η F := by
  apply ENNReal.tsum_le_tsum
  intro r
  gcongr
  exact_mod_cast partialParityCount_le_empty N hN P r r η

#print axioms principalWeight_tsum_fibers
#print axioms partialParityEnergyMass_simple
#print axioms partialParityEnergyMass_covers
#print axioms partialParityCount_empty_eq
#print axioms partialParityCount_repeated_two
#print axioms partialParityEnergyMass_repeated_two
#print axioms partialParityEnergyMass_univ_eq
#print axioms partialParityEnergyMass_empty_eq
#print axioms partialParityCount_le_empty
#print axioms partialParityEnergyMass_le_empty

end QuantitativeNinaMaass
