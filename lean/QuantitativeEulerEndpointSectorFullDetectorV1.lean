module

public import QuantitativeEulerEndpointSectorSourceV1
public import QuantitativeEulerEndpointSectorUniformV1
public import QuantitativeEulerEndpointNewDetectorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticRegularBranchFamily AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticSectorSigns
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReducedRows QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

def sectorRegion (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (ε H : ℝ) : Set ℍ :=
  enlargedRegion (sectorFamilyBranches N hN) (sectorFamilyWords N hN sector S hS)
    (fun i => wideCompactCover N (H/sectorFamilyC N hN sector S hS i)) (wordRegion W ε H)

theorem sectorRegion_compact (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) {ε : ℝ} (hε : 0<ε) (H : ℝ) :
    IsCompact (sectorRegion N hN sector S hS W ε H) :=
  enlargedRegion_compact (sectorFamilyBranches N hN) (sectorFamilyWords N hN sector S hS)
    (fun i => wideCompactCover N (H/sectorFamilyC N hN sector S hS i))
    (fun i => wideCompactCover_compact N hN (H/sectorFamilyC N hN sector S hS i))
    (wordRegion_compact W hε H)

def sectorDetector (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (H : ℝ) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  enlargedDetector (signedGenerators S) (sectorFamilyBranches N hN) (sectorFamilyCoefficients N hN sector)
    (sectorRegion_compact N hN sector S hS W hε H) hε t x

/-- Every row of the actual total-new detector is controlled by original
observations. Both old directions, all ramified primes, and all sectors are
covered with constants fixed before the geometry and fresh prime. -/
theorem sectorDetector_full_original_energy {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold) (hN2 : 2≤N) (sector : Sector N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) :
    ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (ε : ℝ) (hε : 0<ε) (H : ℝ), 0≤H → ∀ (C : ℝ), B≤C →
      ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (t : ℕ) (x : ℍ) (v : Space),
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖sectorDetector N (NeZero.pos N) sector S hS W H hε t x v‖^2≤
        K*((wideDistortion L R R)^t)^2*
          primeOldOriginalEnergy sector q hqN (wideFreshRegion_compact L R R hZ) hε t x v := by
  obtain ⟨Bg,hBg,D,hD,hgeo⟩ := enlarged_new_region_geometry N W
    (sectorFamilyBranches N (NeZero.pos N))
    (sectorFamilyWords N (NeZero.pos N) sector S hS)
    (sectorFamilyC N (NeZero.pos N) sector S hS)
  obtain ⟨B₁,hB₁,K₁,hK₁,hrows⟩ := wide_primeOld_rows_original_bound P
  obtain ⟨B₂,_hB₂,K₂,hK₂,hsign⟩ := wide_sectorSign_rows_original_bound P hN2
  obtain ⟨B₃,_hB₃,K₃,hK₃,hgamma⟩ := wide_gamma0_stack_bound P (signedGenerators S)
    (signedGenerator_mem_gamma N S hS)
  let n : ℝ := Fintype.card (SectorFamilyIndex N)
  refine ⟨Bg,hBg,D,hD,max B₁ (max B₂ B₃),hB₁.trans (le_max_left _ _),n*(K₁+K₂)+K₃,
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hK₁ hK₂)) hK₃,?_⟩
  intro ε hε H hH C hBC q hqPrime hqGood
  obtain ⟨hqN,hrow⟩ := hrows C ((le_max_left _ _).trans hBC) q hqGood
  obtain ⟨_hqN,hsig⟩ := hsign C ((le_max_left _ _).trans ((le_max_right _ _).trans hBC)) q hqGood
  obtain ⟨_hqN,hgam⟩ := hgamma C ((le_max_right _ _).trans ((le_max_right _ _).trans hBC)) q hqGood
  refine ⟨hqN,?_⟩
  intro t x v
  let R := Bg*(D*H+2+1)/min 1 (min ε (1/4))
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  have hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let hs := sectorRegion_compact N (NeZero.pos N) sector S hS W hε H
  have hregion := hgeo ε hε H hH
  have hre : ∀ z∈sectorRegion N (NeZero.pos N) sector S hS W ε H, |z.re|≤R :=
    fun z hz => (hregion hz).1
  have hlo : ∀ z∈sectorRegion N (NeZero.pos N) sector S hS W ε H,
      min ε (1/4)/wideDistortion Bg 2 (D*H)≤z.im := fun z hz => (hregion hz).2.1
  have him : ∀ z∈sectorRegion N (NeZero.pos N) sector S hS W ε H, z.im≤R :=
    fun z hz => (hregion hz).2.2
  have hrow' (i : SectorFamilyIndex N) :
      ‖AsymptoticRegularBranchFamily.family (sectorFamilyBranches N (NeZero.pos N) i)
        (sectorFamilyCoefficients N (NeZero.pos N) sector i) hs hε t x v‖^2≤
      (K₁+K₂)*((wideDistortion L R R)^t)^2*
        primeOldOriginalEnergy sector q hqN (wideFreshRegion_compact L R R hZ) hε t x v := by
    cases i with
    | inl i =>
      exact (hrow sector i hs hε hZ hre hlo him t x v).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK₂) (sq_nonneg _))
          (primeOldOriginalEnergy_nonneg sector q hqN _ hε t x v))
    | inr i =>
      exact (hsig sector i hs hε hZ hre hlo him t x v).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK₁) (sq_nonneg _))
          (primeOldOriginalEnergy_nonneg sector q hqN _ hε t x v))
  have hsum := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (SectorFamilyIndex N))) => hrow' i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hg := hgam (sign sector.1) (by simpa only [pow_two] using sign_sq sector.1)
    hs hε hZ hre hlo him t x v
  have henergy :
      (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one (sign sector.1)
          (wideFreshRegion_compact L R R hZ) hε t x v‖^2+
        ‖fixedPrimeStack N (sign sector.1) (wideFreshRegion_compact L R R hZ) hε t x v‖^2+
        ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN (sign sector.1)
          (wideFreshRegion_compact L R R hZ) hε t i x) v‖^2)≤
      primeOldOriginalEnergy sector q hqN (wideFreshRegion_compact L R R hZ) hε t x v :=
    le_add_of_nonneg_right (by positivity)
  have hg' := hg.trans (mul_le_mul_of_nonneg_left henergy (mul_nonneg hK₃ (sq_nonneg _)))
  change ‖enlargedDetector (signedGenerators S)
    (sectorFamilyBranches N (NeZero.pos N))
    (sectorFamilyCoefficients N (NeZero.pos N) sector) hs hε t x v‖^2≤_
  rw [enlarged_detector_energy]
  exact (add_le_add hsum hg').trans_eq (by dsimp only [n]; ring)

#print axioms sectorDetector_full_original_energy
end QuantitativeEulerEndpointPrepared
