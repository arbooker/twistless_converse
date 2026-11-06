module

public import QuantitativeEulerEndpointNewDetectorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDensityGenerators
open AsymptoticRegularObservationRows AsymptoticObservationStack
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction QuantitativeNewGap
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- Actual total-new source observability after replacing every congruence
row by the proved original Euler observations. The literal old-row energy
and the actual old-tail kernel remain explicit obligations. -/
theorem exists_new_source_original_observability {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), max ε⁻¹ 4≤H →
      (∀ i, (primeOldData N (NeZero.pos N) S hS i).B≤H) →
      ∀ (w : ℂ), w*w=1 → ∀ (t : ℕ) (ht : 1≤t) (x : ℍ), fundamentalGood N x →
      ∀ (v : Space), v∈AsymptoticOrbitRegion.Space
        (AsymptoticHyperbolicArea.terminal ε\AsymptoticHyperbolicArea.terminal H) x →
      oldTailStack N (NeZero.pos N) (primeOldGroup N (NeZero.pos N)) (primeOld_le N (NeZero.pos N)) H
        (fun i => H/(primeOldData N (NeZero.pos N) S hS i).C) hε ht x v=0 →
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min hε (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      ‖v‖^2≤newObservationCost N (NeZero.pos N) S hS W Bobs H ε t*
        (primeOldRowsEnergy N (NeZero.pos N) S hS W H hε t x v+
          K*((wideDistortion L R R)^t)^2*
            (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w hs hε t x v‖^2+
              ‖fixedPrimeStack N w hs hε t x v‖^2+
              ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
                hs hε t i x) v‖^2)+
          ‖newSampling N (NeZero.pos N) H hε ht x v‖^2) := by
  obtain ⟨W,Bobs,hBobs,hobs⟩ := exists_new_source_observability N (NeZero.pos N) S hS hε
  obtain ⟨Bg,hBg,D,hD,B,hB,K,hK,hdet⟩ := primeOldDetector_original_energy P S hS W
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro H hH hdata w hw t ht x hx v hv htail
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  obtain ⟨_hqN,hbound⟩ := hdet ε hε H hH0 C hBC q hqGood
  have hd := hbound w hw t x v
  have ho := hobs H hH hdata t ht x hx v hv htail
  change ‖v‖^2≤newObservationCost N (NeZero.pos N) S hS W Bobs H ε t*
    (‖primeOldDetector N (NeZero.pos N) S hS W H hε t x v‖^2+
      ‖newSampling N (NeZero.pos N) H hε ht x v‖^2) at ho
  dsimp only at hd ⊢
  exact ho.trans (mul_le_mul_of_nonneg_left (add_le_add hd le_rfl)
    (newObservationCost_nonneg N (NeZero.pos N) S hS W Bobs H ε t))

#print axioms exists_new_source_original_observability
end QuantitativeEulerEndpointPrepared
