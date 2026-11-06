module

public import QuantitativeEulerEndpointPreparedBoundedIterationV1
public import QuantitativeEulerEndpointCertificateExclusionsV1
public import QuantitativeEulerEndpointPrimeBlocksV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open FinitenessCertificate FinitenessGlobalHeight AsymptoticRegularReconstruction QuantitativeHolomorphic
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBlocks
open scoped Classical MatrixGroups ENNReal
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q}

/-- Actual positive polynomial filters on the entire normalized terminal
source attain O(4^-n) regular trace excess. The arithmetic blocks, explicit
row normalization, defect schedule, support propagation and fixed solutions
are all instantiated. The finite-weight comparison is a separate task. -/
theorem exists_bounded_prime_block_iteration
    (A : Certificate N Q hQ) (P : Parameters A)
    (hN2 : 2≤N) (sector : Sector N) (threshold : ℕ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let excluded := reconstructionExclusions N Q
    let D₀ := QuantitativeEulerEndpointPrepared.prepared N hN2 excluded threshold
    let P' := AsymptoticReconstructedCount.parameters A P
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (n : ℕ) (C : ℕ → ℝ), (∀ j,j<n → B≤C j) →
      ∀ H : ℝ,max P'.ε⁻¹ 4≤H →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN2 excluded threshold
      let Y := min P'.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P'.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := fun j => (2*generatorTransportConstant D₀*C j)*(X j)^4
      let hs := fun j => wideFreshRegion_compact (L j) R R hZ
      let J := fun j => (countReconstructionBound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P'.ε (P'.s+4)*
        (K*((wideDistortion (L j) R R)^(P'.s+4))^2)
      let c := fun j => Real.sqrt ((2*(1+2*J j))⁻¹)
      let Z := Y/wideDistortion Bg 2 (D*H)
      let height := fun j => L j*(R+R+1)/min 1 Z
      let low := fun j => Z/wideDistortion (L j) R R
      let l := QuantitativeEulerEndpointPrimeBlocks.primes N hN2 excluded threshold
      let b : ℕ → Block A P sector := fun j => ⟨_,hs j,l j,c j,
        wideCombinedBound A P sector (height j+1) (low j) (height j) (l j),
        combined_rows_wide_norm A P sector (hs j)
          (div_pos hZ (wideDistortion_pos (L j) R R))
          (fun _ hz => hz.1) (fun _ hz => hz.2.1) (fun _ hz => hz.2.2) (l j)⟩
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P'.epsilon_pos (by omega : 1≤P'.s+4)+H⁻¹
      ∃ (F : ℕ → Algebra A P) (z : ℕ → ℝ[X]),F 0=1 ∧
        (∀ j,j≤n → Valid A P sector n b j (F j)) ∧
        (∀ j,j<n → Step A P sector n b target j (F j) (z j) ∧
          F (j+1)=nextAt A P sector n b j (F j) (z j)) ∧
        (∀ E : Algebra A P,
          (∀ j,j<n → ∀ i : Fin ((l j).length+1),∀ x,
            normalizedCombinedRows A P sector (hs j) (l j) i x*rep A P E x=0) →
          ∀ j,j≤n → F j*E=E) ∧
        tr A P (F n)≤target+Real.exp ((8:ℝ)/3+8)*
          (P'.ε⁻¹+4*(1+P'.ε⁻¹*Real.log 2))/(4:ℝ)^n := by
  intro excluded D₀ P'
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_prepared_bounded_iteration A P D₀ hN2 sector
      (baseline_subset_reconstructionExclusions N Q) S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro n C hC H hH hdata X Y R hZ L hs J c Z height low l b target
  have hgood (j : ℕ) (_hj : j<n) (p : EligiblePrime N) (hp : p∈l j) :
      D₀.Good p.val ∧ (p.val:ℝ)≤X j ∧ ¬p.val∣Q := by
    have hh := QuantitativeEulerEndpointPrimeBlocks.primes_good_bound N hN2 excluded threshold j p hp
    exact ⟨hh.1,hh.2,good_prime_avoids_certificate hQ D₀
      (certificate_subset_reconstructionExclusions N Q) p.val hh.1⟩
  exact hbound n C X hC H hH hdata l
    (fun j _ => QuantitativeEulerEndpointPrimeBlocks.primes_nodup N hN2 excluded threshold j)
    hgood (fun i j hij _ => QuantitativeEulerEndpointPrimeBlocks.primes_disjoint N hN2 excluded threshold i j hij)
    (fun j => 2/(4:ℝ)^j) (8/3) (fun _ => by positivity)
    (QuantitativeEulerEndpointPrimeBlocks.crossing_loss_sum n)
    (fun j _ => QuantitativeEulerEndpointPrimeBlocks.primes_contraction N hN2 excluded threshold j)

#print axioms exists_bounded_prime_block_iteration
end QuantitativeEulerEndpointBoundedIteration
