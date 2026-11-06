module

public import QuantitativeEulerEndpointSectorSignRowsV1
public import QuantitativeEulerEndpointSectorWeightedBridgeV1
public import QuantitativeEulerEndpointQuotientRowResidualV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane ContinuousLinearMap QuantitativeEulerDiamondDecode
open AsymptoticSectorSigns AsymptoticCongruenceStrip AsymptoticRegularBranchFamily
open AsymptoticCongruenceQuotient QuantitativeSpectralObservability QuantitativeNewGap
open QuantitativeSpectralFiniteReduction QuantitativeSpectralExceptionalReducedRows
open AsymptoticRegularCompactBranch (Space)
open scoped Classical lp

def sectorSignBranches (N : ℕ) (hN : 0<N) (i : SectorSignIndex N) : Fin 2 → Branch :=
  fun j => if j=0 then projectiveBranch (sectorLabel N hN i) else projectiveBranch 1

def sectorSignCoefficients {N : ℕ} (sector : Sector N) (i : SectorSignIndex N) : Fin 2 → ℂ :=
  fun j => if j=0 then 1 else -(sectorNormalizerSign sector i:ℂ)

theorem compactAction_sectorSignRingRow (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (sectorSignRingRow N hN sector i)=
      AsymptoticRegularBranchFamily.family (sectorSignBranches N hN i)
        (sectorSignCoefficients sector i) hs hε t x := by
  have he (g : OrbitGroup) : compactAction hs hε t x (symbol g)=
      AsymptoticRegularBranchFamily.compact (projectiveBranch g) hs hε t x := by
    have h := compactAction_branch hs hε t x (projectiveBranch g)
    rw [show AsymptoticRationalBranches.ofMatrix (projectiveBranch g).matrix
      (projectiveBranch g).positive=g from projectiveBranch_label g] at h
    exact h
  have hid : compactAction hs hε t x 1=
      AsymptoticRegularBranchFamily.compact (projectiveBranch 1) hs hε t x := by
    simpa only [map_one] using he 1
  rw [sectorSignRingRow,map_sub,map_smul,he,hid]
  simp [AsymptoticRegularBranchFamily.family,sectorSignBranches,sectorSignCoefficients,
    Fin.sum_univ_two,sub_eq_add_neg]
  exact (_root_.neg_smul _ _).symm

theorem weightedSectorSignRow_range (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (v : Space) :
    weightedSectorSignRow N hN sector i hε ht x v∈quotientSpace N hε ht x := by
  exact ⟨_,rfl⟩

theorem weightedSectorSignRow_coordinate (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (v : Space)
    (hv : v∈quotientSpace N hε ht x) (g : OrbitGroup) :
    coordinate N ε t x g (weightedSectorSignRow N hN sector i hε ht x v)=
      ∑ j,sectorSignCoefficients sector i j*
        coordinate N ε t x (label (sectorSignBranches N hN i j)*g) v := by
  obtain ⟨f,rfl⟩ := hv
  simp only [LinearIsometry.coe_toLinearMap]
  rw [weightedSectorSignRow_induction]
  simp only [Fin.sum_univ_two,sectorSignCoefficients,sectorSignBranches,
    ite_true,show ¬(1:Fin 2)=0 by decide,ite_false,projectiveBranch_label,one_mul,coordinate_induction]
  simp only [neg_mul,←sub_eq_add_neg]
  cases i <;> rfl

#print axioms compactAction_sectorSignRingRow
#print axioms weightedSectorSignRow_coordinate
end QuantitativeEulerEndpointPrepared
