module

public import QuantitativeArithmeticRetainedIterationV1
public import QuantitativeEulerEndpointNormalizedThresholdV1
public import QuantitativeEulerEndpointWideBaselineBoundsV1
public import QuantitativeEulerEndpointCertificateExclusionsV1
public import QuantitativeEulerEndpointPrimeBlocksV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedPacket
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedFilterExpression
open AsymptoticRegularCompactBranch

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)

def wideCombinedBound (R Y H : ℝ) (l : List (EligiblePrime N)) : ℕ → ℝ
  | 0 => wideDetectorBound N e R Y H (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)
  | j+1 => wideSequenceBound N (sign e.1) R Y H (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) l j

theorem combined_rows_wide_norm {s : Set UpperHalfPlane} (hs : IsCompact s)
    {R Y H : ℝ} (hY : 0<Y)
    (hre : ∀ z∈s,|z.re|≤R) (hlo : ∀ z∈s,Y≤z.im) (hhi : ∀ z∈s,z.im≤H)
    (l : List (EligiblePrime N)) (i : ℕ) (x : UpperHalfPlane) :
    ‖rows A P hR₀ e hs l i x‖≤wideCombinedBound A P e R Y H l i := by
  have hu := regularAmbient_norm A P hR₀ (NeZero.pos N) e x
  cases i with
  | zero =>
    apply (norm_mul_le_of_le
      (newBaselineDetector_wide_norm hs P.epsilon_pos
        hY hre hlo hhi N e (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) x) hu).trans_eq
    exact mul_one _
  | succ i =>
    apply (norm_mul_le_of_le
      (packet_sequence_wide_norm N (NeZero.pos N) (sign e.1) hs
        P.epsilon_pos hY hre hlo hhi
        (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) l i x) hu).trans_eq
    exact mul_one _

#print axioms combined_rows_wide_norm
end QuantitativeArithmeticRetainedPacket

namespace QuantitativeArithmeticRetainedIteration
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticRegularReconstruction QuantitativeHolomorphic
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra Polynomial
open QuantitativeArithmeticRetainedPreparedReconstruction QuantitativeArithmeticRetainedPacket
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBlocks
open scoped Classical MatrixGroups ENNReal
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}

/-- Construct the actual normalized terminal polynomial sequence from identity.
All hard contractions, scalar schedules, propagated defects, future-prime
supports and exact solution invariants are discharged. The normalization uses explicit geometric row bounds. The prime-product
budget is the remaining arithmetic input to this interface. -/
theorem exists_prepared_bounded_iteration
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (sector : Sector N) (hex : baselineDenominators N⊆excluded)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (n : ℕ) (C X : ℕ → ℝ), (∀ j,j<n → B≤C j) →
      ∀ H : ℝ,max P.ε⁻¹ 4≤H →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let Y := min P.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := fun j => (2*generatorTransportConstant D₀*C j)*(X j)^4
      let hs := fun j => wideFreshRegion_compact (L j) R R hZ
      let J := fun j => (bound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)*
        (K*((wideDistortion (L j) R R)^(exponent A P+4))^2)
      let c := fun j => Real.sqrt ((2*(1+2*J j))⁻¹)
      let Z := Y/wideDistortion Bg 2 (D*H)
      let height := fun j => L j*(R+R+1)/min 1 Z
      let low := fun j => Z/wideDistortion (L j) R R
      ∀ l : ℕ → List (EligiblePrime N),
      let b : ℕ → Block A P hR₀ sector := fun j => ⟨_,hs j,l j,c j,
        QuantitativeArithmeticRetainedPacket.wideCombinedBound A P sector (height j+1) (low j) (height j) (l j),
        QuantitativeArithmeticRetainedPacket.combined_rows_wide_norm A P hR₀ sector (hs j)
          (div_pos hZ (wideDistortion_pos (L j) R R))
          (fun _ hz => hz.1) (fun _ hz => hz.2.1) (fun _ hz => hz.2.2) (l j)⟩
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤exponent A P+4)+H⁻¹
      (∀ j,j<n → (l j).Nodup) →
      (∀ j,j<n → ∀ p∈l j,D₀.Good p.val ∧ (p.val:ℝ)≤X j ∧ ¬p.val∣Q ∧ ∀r∈R₀,¬p.val∣r) →
      (∀ i j,i<j → j<n → ∀ r∈l j,r∉l i) →
      ∀ (bad : ℕ → ℝ) (Cbad : ℝ), (∀ j,0≤bad j) →
      (∑ j∈Finset.range n,bad j)≤Cbad →
      (∀ j,j<n → ((l j).map primeFactor).prod≤Real.exp (bad j)/4) →
      ∃ (F : ℕ → Algebra A P) (z : ℕ → ℝ[X]),F 0=1 ∧
        (∀ j,j≤n → Valid A P hR₀ sector n b j (F j)) ∧
        (∀ j,j<n → Step A P hR₀ sector n b target j (F j) (z j) ∧
          F (j+1)=nextAt A P hR₀ sector n b j (F j) (z j)) ∧
        (∀ E : Algebra A P,
          (∀ j,j<n → ∀ i : Fin ((l j).length+1),∀ x,
            QuantitativeArithmeticRetainedPacket.rows A P hR₀ sector (hs j) (l j) i x*rep A P E x=0) →
          ∀ j,j≤n → F j*E=E) ∧
        tr A P (F n)≤target+Real.exp (Cbad+8)*
          (P.ε⁻¹+4*(1+P.ε⁻¹*Real.log 2))/(4:ℝ)^n := by
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    QuantitativeArithmeticRetainedPacket.exists_packet_contraction (Q := Q)
      A P hR₀ D₀ hN2 sector hex S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro n C X hC H hH hdata Y R hZ L hs J c Z height low l b target hnodup hgood hdisjoint bad Cbad hbad hbudget hprime
  have hprimes : ∀ j,j<n → ∀ r∈(b j).primes,
      ¬r.val∣Q ∧ (∀p∈R₀,¬r.val∣p) ∧ ∀ a : UnitResidue N,¬r.val∣(primeLift N a).q := by
    intro j hj r hr
    exact ⟨(hgood j hj r hr).2.2.1,(hgood j hj r hr).2.2.2,good_prime_avoids_baseline D₀ hex r.val (hgood j hj r hr).1⟩
  have hstep (j : ℕ) (hj : j<n) (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1)
      (hsF : ∀ r∈(b j).primes,∀ x,Supported (integralGroup r.val) (rep A P F x))
      (hdef : tr A P (F-F^2)≤4*P.ε⁻¹/(sharpnessAt A P hR₀ sector n b j:ℝ)) :
      ∃ z,Step A P hR₀ sector n b target j F z := by
    have hJ : 0≤J j := mul_nonneg
      (mul_nonneg (sq_nonneg _) (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)))
      (mul_nonneg hK (sq_nonneg _))
    have hc : 0<(b j).cutoff := QuantitativeEulerEndpointNormalizedThreshold.threshold_pos hJ
    have hu := (QuantitativeEulerEndpointNormalizedThreshold.normalized_range
      (b j).bound ((b j).primes.length+1) hJ).2
    have hregular := half_regular A P F (IsSelfAdjoint.of_nonneg hF0)
    have hsupport : ∀ p∈l j,∀ x,Supported (integralGroup p.val) (half A P F x).toSubmodule.starProjection := by
      intro p hp x
      exact half_supported A P F (IsSelfAdjoint.of_nonneg hF0) (integralGroup p.val) (hsF p hp) x
    have hchain := hbound (C j) (hC j hj) (X j) H hH hdata (half A P F)
      hregular.1 hregular.2 (half_le_terminal A P F hF0 hF1)
      (l j) (hnodup j hj) (hgood j hj) hsupport
    exact exists_step A P hR₀ sector n b j hj.le F hF0 hF1 target hc hu hchain hdef
  obtain ⟨F,z,hzero,hvalid,hsteps,hfixed⟩ :=
    exists_iteration A P hR₀ sector n b hprimes hdisjoint target hstep
  refine ⟨F,z,hzero,hvalid,hsteps,hfixed,?_⟩
  have hH0 : 0≤H := (by norm_num : (0:ℝ)≤4).trans ((le_max_right _ _).trans hH)
  have htarget : 0≤target := add_nonneg
    (sectorTraceTarget_nonneg N (NeZero.pos N) sector S hS hH0 P.epsilon_pos (by omega))
    (inv_nonneg.mpr hH0)
  exact finite_trace_bound A P hR₀ sector n b target F z hzero htarget hsteps bad hbad hbudget hprime

#print axioms exists_prepared_bounded_iteration
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace AsymptoticSectorSigns
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticRegularReconstruction QuantitativeHolomorphic
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators QuantitativeSpectralObservability QuantitativeNewGap
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra Polynomial
open QuantitativeArithmeticRetainedPreparedReconstruction QuantitativeArithmeticRetainedPacket
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBlocks
open scoped Classical MatrixGroups ENNReal
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}

/-- Actual positive polynomial filters on the entire normalized terminal
source attain O(4^-n) regular trace excess. The arithmetic blocks, explicit
row normalization, defect schedule, support propagation and fixed solutions
are all instantiated. The finite-weight comparison is a separate task. -/
theorem exists_bounded_prime_block_iteration
    (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
    (hN2 : 2≤N) (sector : Sector N) (threshold : ℕ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let excluded := reconstructionExclusions N Q ∪ R₀
    let D₀ := QuantitativeEulerEndpointPrepared.prepared N hN2 excluded threshold
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ), 1≤Bobs ∧
      ∃ Bg : ℝ, 1≤Bg ∧ ∃ D : ℝ, 1≤D ∧ ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (n : ℕ) (C : ℕ → ℝ), (∀ j,j<n → B≤C j) →
      ∀ H : ℝ,max P.ε⁻¹ 4≤H →
      (∀ i,sectorFamilyB N (NeZero.pos N) sector S hS i≤H) →
      let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN2 excluded threshold
      let Y := min P.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := fun j => (2*generatorTransportConstant D₀*C j)*(X j)^4
      let hs := fun j => wideFreshRegion_compact (L j) R R hZ
      let J := fun j => (bound A P)^2*
        sectorObservationCost N (NeZero.pos N) sector S hS W Bobs H P.ε (exponent A P+4)*
        (K*((wideDistortion (L j) R R)^(exponent A P+4))^2)
      let c := fun j => Real.sqrt ((2*(1+2*J j))⁻¹)
      let Z := Y/wideDistortion Bg 2 (D*H)
      let height := fun j => L j*(R+R+1)/min 1 Z
      let low := fun j => Z/wideDistortion (L j) R R
      let l := QuantitativeEulerEndpointPrimeBlocks.primes N hN2 excluded threshold
      let b : ℕ → Block A P hR₀ sector := fun j => ⟨_,hs j,l j,c j,
        QuantitativeArithmeticRetainedPacket.wideCombinedBound A P sector (height j+1) (low j) (height j) (l j),
        QuantitativeArithmeticRetainedPacket.combined_rows_wide_norm A P hR₀ sector (hs j)
          (div_pos hZ (wideDistortion_pos (L j) R R))
          (fun _ hz => hz.1) (fun _ hz => hz.2.1) (fun _ hz => hz.2.2) (l j)⟩
      let target := sectorTraceTarget N (NeZero.pos N) sector S hS H P.epsilon_pos (by omega : 1≤exponent A P+4)+H⁻¹
      ∃ (F : ℕ → Algebra A P) (z : ℕ → ℝ[X]),F 0=1 ∧
        (∀ j,j≤n → Valid A P hR₀ sector n b j (F j)) ∧
        (∀ j,j<n → Step A P hR₀ sector n b target j (F j) (z j) ∧
          F (j+1)=nextAt A P hR₀ sector n b j (F j) (z j)) ∧
        (∀ E : Algebra A P,
          (∀ j,j<n → ∀ i : Fin ((l j).length+1),∀ x,
            QuantitativeArithmeticRetainedPacket.rows A P hR₀ sector (hs j) (l j) i x*rep A P E x=0) →
          ∀ j,j≤n → F j*E=E) ∧
        tr A P (F n)≤target+Real.exp ((8:ℝ)/3+8)*
          (P.ε⁻¹+4*(1+P.ε⁻¹*Real.log 2))/(4:ℝ)^n := by
  intro excluded D₀
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hbound⟩ :=
    exists_prepared_bounded_iteration A P hR₀ D₀ hN2 sector
      ((baseline_subset_reconstructionExclusions N Q).trans Finset.subset_union_left) S hS
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro n C hC H hH hdata X Y R hZ L hs J c Z height low l b target
  have hgood (j : ℕ) (_hj : j<n) (p : EligiblePrime N) (hp : p∈l j) :
      D₀.Good p.val ∧ (p.val:ℝ)≤X j ∧ ¬p.val∣Q ∧ ∀r∈R₀,¬p.val∣r := by
    have hh := QuantitativeEulerEndpointPrimeBlocks.primes_good_bound N hN2 excluded threshold j p hp
    refine ⟨hh.1,hh.2,good_prime_avoids_certificate hQ D₀
      ((certificate_subset_reconstructionExclusions N Q).trans Finset.subset_union_left) p.val hh.1,?_⟩
    intro r hr hdiv
    have heq : p.val=r := (Nat.prime_dvd_prime_iff_eq p.property.1 (hR₀ r hr)).mp hdiv
    exact (D₀.prime_data p.val p.property.1 hh.1).1 (Finset.mem_union_right _ (heq.symm ▸ hr))
  exact hbound n C X hC H hH hdata l
    (fun j _ => QuantitativeEulerEndpointPrimeBlocks.primes_nodup N hN2 excluded threshold j)
    hgood (fun i j hij _ => QuantitativeEulerEndpointPrimeBlocks.primes_disjoint N hN2 excluded threshold i j hij)
    (fun j => 2/(4:ℝ)^j) (8/3) (fun _ => by positivity)
    (QuantitativeEulerEndpointPrimeBlocks.crossing_loss_sum n)
    (fun j _ => QuantitativeEulerEndpointPrimeBlocks.primes_contraction N hN2 excluded threshold j)

#print axioms exists_bounded_prime_block_iteration
end QuantitativeArithmeticRetainedIteration
