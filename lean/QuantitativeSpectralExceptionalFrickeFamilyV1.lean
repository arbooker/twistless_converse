module

public import QuantitativeSpectralExceptionalFrickeDataV1
public import QuantitativeSpectralObservabilityOldFamilyControlV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalFricke

open UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip AsymptoticRegularBranchFamily
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows
open scoped MatrixGroups lp

variable {F : Type*} [Fintype F] {I : F → Type} [∀ i, Fintype (I i)]

def familyIndices (I : F → Type) : Option F → Type
  | none => Bool
  | some i => I i

instance familyIndices_fintype (i : Option F) : Fintype (familyIndices I i) := by
  cases i with
  | none => exact inferInstanceAs (Fintype Bool)
  | some i => exact inferInstanceAs (Fintype (I i))

def familyBranches (N : ℕ) (hN : 0<N) (J : F → Subgroup OrbitGroup) (r : ∀ i, I i → J i) :
    ∀ j : Option F, familyIndices I j → Branch
  | none => branches N hN
  | some i => oldBranches (r i)

def familyCoefficients (N : ℕ) (sign : ℝ) (J : F → Subgroup OrbitGroup) :
    ∀ j : Option F, familyIndices I j → ℂ
  | none => coefficients sign
  | some i => oldCoefficients N (J i)

variable (N : ℕ) (hN : 0<N) (sign : ℝ) (S : Finset SL(2,ℤ))
  (J : F → Subgroup OrbitGroup) (hJ : ∀ i, gamma N≤J i)
  [∀ i, Finite (J i ⧸ (gamma N).subgroupOf (J i))]
  (r : ∀ i, I i → J i) (d : ∀ i, OldResidualData N hN S (J i) (hJ i) (r i))
  (df : ResidualData N hN sign S)

def familyPieces : Option F → Type
  | none => Fin df.n
  | some i => Fin (d i).n

instance familyPieces_fintype (i : Option F) : Fintype (familyPieces N hN sign S J hJ r d df i) := by
  cases i with
  | none => exact inferInstanceAs (Fintype (Fin df.n))
  | some i => exact inferInstanceAs (Fintype (Fin (d i).n))

def familyWords : ∀ j : Option F,
    familyPieces N hN sign S J hJ r d df j → familyIndices I j → List SL(2,ℤ)
  | none => df.w
  | some i => (d i).w

def familyRegions (Y : ℝ) : Option F → Set ℍ
  | none => wideCompactCover N (Y/df.C)
  | some i => wideCompactCover N (Y/(d i).C)

omit [Fintype F] in
theorem familyRegions_compact (Y : ℝ) (i : Option F) :
    IsCompact (familyRegions N hN sign S J hJ r d df Y i) := by
  cases i with
  | none => exact wideCompactCover_compact N hN _
  | some i => exact wideCompactCover_compact N hN _

def familyCost (Y ε : ℝ) (t : ℕ) : ℝ :=
  (∑ i, ((d i).L*(1+ε*(d i).K*(Y/(d i).C+3)^2)^(2*t))^2)+(df.cost Y ε t)^2

/-- Old and signed Fricke rows use one literal enlarged detector. The two
tail-kernel conditions are the intersection of their actual error kernels. -/
theorem family_energy_le_detector {Y : ℝ} (hY : ∀ i, (d i).B≤Y) (hfY : df.B≤Y)
    {u : Set ℍ} (hu : IsCompact u) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (x : ℍ) (v : ℓ²(OrbitGroup,ℂ))
    (hv : oldTailStack N hN J hJ Y (fun i => Y/(d i).C) hε ht x v=0)
    (hvf : tailRow N hN sign Y (Y/df.C) hε ht x v=0) :
    let b := familyBranches N hN J r
    let c := familyCoefficients (I:=I) N sign J
    let w := familyWords N hN sign S J hJ r d df
    let hs := familyRegions_compact N hN sign S J hJ r d df Y
    let hu' := enlargedRegion_compact b w (familyRegions N hN sign S J hJ r d df Y) hs hu
    (∑ i, ‖oldSampledRow N hN (J i) (hJ i) Y hε ht x v‖^2)+
      ‖sampledRow N hN sign Y hε ht x v‖^2 ≤
      familyCost N hN sign S J hJ r d df Y ε t*
        ‖enlargedDetector (signedGenerators S) b c hu' hε t x v‖^2 := by
  dsimp only
  rw [enlargedDetector_norm_apply]
  let b := familyBranches N hN J r
  let c := familyCoefficients (I:=I) N sign J
  let w := familyWords N hN sign S J hJ r d df
  let sr := familyRegions N hN sign S J hJ r d df Y
  let hs := familyRegions_compact N hN sign S J hJ r d df Y
  let D := AsymptoticObservationStack.stack
    (enlargedRows (signedGenerators S) b c (enlargedRegion_compact b w sr hs hu) hε t x)
  have hold : (∑ i, ‖oldSampledRow N hN (J i) (hJ i) Y hε ht x v‖^2)≤
      (∑ i, ((d i).L*(1+ε*(d i).K*(Y/(d i).C+3)^2)^(2*t))^2)*‖D v‖^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hz := (oldTailStack_eq_zero_iff N hN J hJ Y (fun i => Y/(d i).C) hε ht x v).mp hv i
    have hn := (d i).old_norm_le (hY i) hε ht x v hz
    have hd := commonResidualStack_norm_le_enlarged (signedGenerators S) b w c sr hs hu hε t x (some i) v
    have hcost : 0≤(d i).L*(1+ε*(d i).K*(Y/(d i).C+3)^2)^(2*t) := by
      have hL := zero_le_one.trans (d i).L_ge_one
      rw [Nat.mul_comm 2 t,pow_mul]
      exact mul_nonneg hL (sq_nonneg _)
    have he := hn.trans (mul_le_mul_of_nonneg_left hd hcost)
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) he 2
  have hfr : ‖sampledRow N hN sign Y hε ht x v‖^2≤(df.cost Y ε t)^2*‖D v‖^2 := by
    have hn := df.norm_le hfY hε ht x v hvf
    have hd := commonResidualStack_norm_le_enlarged (signedGenerators S) b w c sr hs hu hε t x none v
    have he := hn.trans (mul_le_mul_of_nonneg_left hd (df.cost_nonneg Y ε t))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) he 2
  exact (add_le_add hold hfr).trans_eq (by rw [← add_mul]; rfl)

#print axioms family_energy_le_detector

end QuantitativeSpectralExceptionalFricke
