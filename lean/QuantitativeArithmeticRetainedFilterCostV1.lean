module

public import QuantitativeArithmeticRetainedPreparedIterationV1
public import QuantitativeEulerEndpointActualCombinedEffortV1
public import QuantitativeHolomorphicFilterStabilityV1

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra
open QuantitativeEulerEndpointNormalizedThreshold QuantitativeHolomorphic
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open scoped Classical MatrixGroups

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
  (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
  (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
  (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The exact explicitly normalized block in the constructed iteration,
with one fixed transport constant and common terminal height H0*4^n. -/
def actualBlock (n j : ℕ) : Block A P hR₀ sector :=
  let H := H₀*(4:ℝ)^n
  let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN excluded threshold₀ j
  let Y := min P.ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  let Z := Y/wideDistortion Bg 2 (D*H)
  let hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
  let L := (2*G*C)*X^4
  let hs := wideFreshRegion_compact L R R hZ
  let cost := (bound A P)^2*
    sectorObservationCost N (NeZero.pos N) sector S hS W B H P.ε (exponent A P+4)*
      (Kobs*((wideDistortion L R R)^(exponent A P+4))^2)
  let l := QuantitativeEulerEndpointPrimeBlocks.primes N hN excluded threshold₀ j
  let height := L*(R+R+1)/min 1 Z
  let low := Z/wideDistortion L R R
  ⟨_,hs,l,threshold cost,QuantitativeArithmeticRetainedPacket.wideCombinedBound A P sector (height+1) low height l,
    QuantitativeArithmeticRetainedPacket.combined_rows_wide_norm A P hR₀ sector hs (div_pos hZ (wideDistortion_pos L R R))
      (fun _ hz => hz.1) (fun _ hz => hz.2.1) (fun _ hz => hz.2.2) l⟩

theorem actualBlock_range (hK0 : 0≤Kobs) (n j : ℕ) :
    let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    0<b.cutoff ∧ QuantitativeEulerEndpointBlockNormalization.factor
      b.bound (b.primes.length+1)*b.cutoff≤1 := by
  have hcost (H L R : ℝ) : 0≤(bound A P)^2*
      sectorObservationCost N (NeZero.pos N) sector S hS W B H P.ε (exponent A P+4)*
        (Kobs*((wideDistortion L R R)^(exponent A P+4))^2) :=
    mul_nonneg (mul_nonneg (sq_nonneg _)
      (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W B H P.ε (exponent A P+4)))
      (mul_nonneg hK0 (sq_nonneg _))
  dsimp only [actualBlock]
  exact ⟨threshold_pos (hcost _ _ _),(normalized_range _ _ (hcost _ _ _)).2⟩

theorem actualBlock_effort_pos (hK0 : 0≤Kobs) (n j : ℕ) :
    0<effortAt A P hR₀ sector n
      (actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) j := by
  have hr := actualBlock_range A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs hK0 n j
  exact QuantitativeEulerEndpointLocalEffort.effort_pos n j
    (QuantitativeArithmeticRetainedPolynomial.logCost_nonneg _ _ hr.1 hr.2)

theorem actualBlock_logCost (n j : ℕ) :
    let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    QuantitativeArithmeticRetainedPolynomial.logCost b.bound (b.primes.length+1) b.cutoff=
      actualCombinedLog N hN excluded threshold₀ sector S hS W B Bg D H₀ G C
        ((bound A P)^2*Kobs) P.ε (exponent A P+4) n j := by
  dsimp only [actualBlock,QuantitativeArithmeticRetainedPolynomial.logCost,actualCombinedLog]
  have he : ∀ R Y H : ℝ,∀ l : List (EligiblePrime N),QuantitativeArithmeticRetainedPacket.wideCombinedBound A P sector R Y H l=
      prepend (wideDetectorBound N sector R Y H (exponent A P+4))
        (wideSequenceBound N (sign sector.1) R Y H (exponent A P+4) l) := by
    intro R Y H l
    funext i
    cases i <;> rfl
  rw [he]
  congr 4
  ring

theorem actualBlock_effort (n j : ℕ) :
    effortAt A P hR₀ sector n (actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) j=
      QuantitativeEulerEndpointLocalEffort.effort n j
        (actualCombinedLog N hN excluded threshold₀ sector S hS W B Bg D H₀ G C
          ((bound A P)^2*Kobs) P.ε (exponent A P+4) n j) := by
  unfold effortAt QuantitativeArithmeticRetainedPolynomial.effort
  rw [actualBlock_logCost]

/-- All logarithmic effort of the actual bounded iteration, including
its final next-block sharpening, is O(4^n). -/
theorem exists_actual_total_effort (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) :
    ∃ K : ℝ,0≤K ∧ ∀ n : ℕ,
      (∑ j∈Finset.range n,effortAt A P hR₀ sector n
        (actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) j)+
      effortAt A P hR₀ sector n
        (actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n) n≤K*(4:ℝ)^n := by
  obtain ⟨K,hK,hbound⟩ := exists_actual_combined_total_effort N hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C ((bound A P)^2*Kobs) P.ε (exponent A P+4)
    hBg0 hD0 hH₀ hG0 hC0 (mul_nonneg (sq_nonneg _) hK0) P.epsilon_pos
  refine ⟨K,hK,?_⟩
  intro n
  simpa only [actualBlock_effort] using hbound n

#print axioms actualBlock_logCost
#print axioms actualBlock_range
#print axioms actualBlock_effort_pos
#print axioms actualBlock_effort
#print axioms exists_actual_total_effort
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedPacket
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open AsymptoticRegularCompactBranch ContinuousLinearMap
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedFilterExpression
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeEulerEndpointBlockNormalization QuantitativeArithmeticRetainedTerminalAlgebra

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))

/-- The actual packet before applying normalized reconstruction. -/
def uncomposedCombinedRows : ℕ → UpperHalfPlane → Space →L[ℂ] Space
  | 0,x => newBaselineDetector N e hs P.epsilon_pos
      (exponent A P+4) x
  | j+1,x => packetSequence N (NeZero.pos N) (sign e.1) hs
      P.epsilon_pos
      (exponent A P+4) l j x

theorem combined_rows_comp (i : ℕ) (x : UpperHalfPlane) :
    rows A P hR₀ e hs l i x=uncomposedCombinedRows A P e hs l i x*
      regularAmbient A P hR₀ (NeZero.pos N) e x := by
  cases i <;> rfl

theorem uncomposed_combined_rows_wide_norm {R Y H : ℝ} (hY : 0<Y)
    (hre : ∀ z∈s,|z.re|≤R) (hlo : ∀ z∈s,Y≤z.im) (hhi : ∀ z∈s,z.im≤H)
    (i : ℕ) (x : UpperHalfPlane) :
    ‖uncomposedCombinedRows A P e hs l i x‖≤wideCombinedBound A P e R Y H l i := by
  cases i with
  | zero =>
    exact newBaselineDetector_wide_norm hs P.epsilon_pos
      hY hre hlo hhi N e (exponent A P+4) x
  | succ i =>
    exact packet_sequence_wide_norm N (NeZero.pos N) (sign e.1) hs
      P.epsilon_pos hY hre hlo hhi
      (exponent A P+4) l i x

/-- Reconstruction may be replaced while keeping exactly the coefficients
and original observation rows of the actual bounded Gram. -/
def replacementGram (C : ℕ → ℝ) (x : UpperHalfPlane) (U : Space →L[ℂ] Space) :=
  finiteRowGram Finset.univ (fun i : Fin (l.length+1) =>
    ((factor C (l.length+1):ℝ):ℂ) • uncomposedCombinedRows A P e hs l i x) U

theorem replacementGram_exact (C : ℕ → ℝ)
    (hC : ∀ i x,‖rows A P hR₀ e hs l i x‖≤C i) (x : UpperHalfPlane) :
    rep A P (gram A P hR₀ e hs l C hC) x=
      replacementGram A P e hs l C x (regularAmbient A P hR₀ (NeZero.pos N) e x) := by
  rw [rep_gram]
  unfold replacementGram finiteRowGram
  apply Finset.sum_congr rfl
  intro i _
  rw [scaledRows,combined_rows_comp]
  rw [smul_comp]
  rfl

theorem replacementGram_difference (C : ℕ → ℝ) (x : UpperHalfPlane)
    (hC : ∀ i,‖uncomposedCombinedRows A P e hs l i x‖≤C i)
    (U V : Space →L[ℂ] Space) (hU : ‖U‖≤1) (hV : ‖V‖≤1) :
    ‖replacementGram A P e hs l C x V-replacementGram A P e hs l C x U‖≤2*‖V-U‖ := by
  let r := factor C (l.length+1)
  have hrows (i : Fin (l.length+1)) : ‖(r:ℂ) • uncomposedCombinedRows A P e hs l i x‖≤r*C i := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (factor_pos C (l.length+1))]
    exact mul_le_mul_of_nonneg_left (hC i) (factor_pos C (l.length+1)).le
  have hh := finiteRowGram_difference Finset.univ
    (fun i : Fin (l.length+1) => (r:ℂ) • uncomposedCombinedRows A P e hs l i x)
    (fun i => r*C i) hrows U V hU hV
  have hs := normalized_square_sum C (l.length+1)
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hs (norm_nonneg (V-U))])

theorem replacementGram_order (C : ℕ → ℝ) (x : UpperHalfPlane)
    (hC : ∀ i,‖uncomposedCombinedRows A P e hs l i x‖≤C i)
    (U : Space →L[ℂ] Space) (hU : ‖U‖≤1) :
    0≤replacementGram A P e hs l C x U ∧ replacementGram A P e hs l C x U≤1 := by
  let r := factor C (l.length+1)
  let B := fun i : Fin (l.length+1) => ((r:ℂ) • uncomposedCombinedRows A P e hs l i x).comp U
  have hrows (i : Fin (l.length+1)) : ‖B i‖≤r*C i := by
    apply (opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left hU (norm_nonneg _)).trans
    rw [mul_one,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (factor_pos C (l.length+1))]
    exact mul_le_mul_of_nonneg_left (hC i) (factor_pos C (l.length+1)).le
  have hpos : 0≤replacementGram A P e hs l C x U := by
    change 0≤∑ i : Fin (l.length+1),star (B i)*B i
    exact Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
  have hn : ‖replacementGram A P e hs l C x U‖≤1 := by
    change ‖∑ i : Fin (l.length+1),(B i).adjoint.comp (B i)‖≤1
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i (_hi : i∈Finset.univ) => ?_)).trans (normalized_square_sum C (l.length+1))
    have hp : ‖(B i).adjoint.comp (B i)‖≤‖B i‖^2 := by
      simpa only [adjoint.norm_map,pow_two] using opNorm_comp_le (B i).adjoint (B i)
    exact hp.trans (pow_le_pow_left₀ (norm_nonneg _) (hrows i) 2)
  exact ⟨hpos,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hn⟩

#print axioms uncomposed_combined_rows_wide_norm
#print axioms replacementGram_exact
#print axioms replacementGram_difference
#print axioms replacementGram_order
end QuantitativeArithmeticRetainedPacket

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeHolomorphic
open AsymptoticRegularCompactBranch AsymptoticFiniteBranch
open QuantitativeArithmeticRetainedPacket QuantitativeArithmeticRetainedFilterExpression
open scoped Classical MatrixGroups

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime)
  (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
  (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
  (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

/-- The explicit block bounds control the original rows before either
exact or finite reconstruction is composed with them. -/
theorem actualBlock_uncomposed_norm (n j i : ℕ) (x : UpperHalfPlane) :
    let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    ‖uncomposedCombinedRows A P sector b.compact b.primes i x‖≤b.bound i := by
  dsimp only [actualBlock]
  apply uncomposed_combined_rows_wide_norm
  · exact div_pos (div_pos
      (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4))
      (wideDistortion_pos _ _ _)) (wideDistortion_pos _ _ _)
  · intro z hz
    exact hz.1
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact hz.2.2

/-- Replacing reconstruction in any actual block keeps the Gram a positive
contraction and changes it by at most twice the reconstruction error. -/
theorem actualBlock_replacement (n j : ℕ) (x : UpperHalfPlane)
    (V : Space →L[ℂ] Space) (hV : ‖V‖≤1) :
    let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    let T := replacementGram A P sector b.compact b.primes b.bound x V
    0≤T ∧ T≤1 ∧
      ‖T-rep A P (gram A P hR₀ sector
        b.compact b.primes b.bound b.norm_bound) x‖≤
        2*‖V-regularAmbient A P hR₀ (NeZero.pos N) sector x‖ := by
  intro b T
  have hraw := actualBlock_uncomposed_norm A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
  have hord := replacementGram_order A P sector b.compact b.primes b.bound x (fun i => hraw i x) V hV
  refine ⟨hord.1,hord.2,?_⟩
  rw [replacementGram_exact]
  exact replacementGram_difference A P sector b.compact b.primes b.bound x (fun i => hraw i x)
    _ V (regularAmbient_norm A P hR₀ (NeZero.pos N) sector x) hV

/-- The common reconstruction's paid error transfers directly to the exact
actual Gram, retaining its normalization and with no row-count loss. -/
theorem actualBlock_paid_replacement (n j : ℕ) (E : Expression)
    (hE : ∀ x,‖regularSum E x‖≤1) {M : ℝ} (hM : 0≤M)
    (hpaid : ∀ x,M*‖regularSum E x-regularAmbient A P hR₀ (NeZero.pos N) sector x‖≤1/(4:ℝ)^n)
    (x : UpperHalfPlane) :
    let b := actualBlock A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs n j
    M*‖replacementGram A P sector b.compact b.primes b.bound x (regularSum E x)-
      rep A P (gram A P hR₀ sector
        b.compact b.primes b.bound b.norm_bound) x‖≤2/(4:ℝ)^n := by
  have hh := (actualBlock_replacement A P hR₀ hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs
    n j x (regularSum E x) (hE x)).2.2
  have hm := mul_le_mul_of_nonneg_left hh hM
  have hp := hpaid x
  dsimp only
  rw [show (2:ℝ)/(4:ℝ)^n=2*(1/(4:ℝ)^n) by ring]
  nlinarith only [hm,hp]

#print axioms actualBlock_uncomposed_norm
#print axioms actualBlock_replacement
#print axioms actualBlock_paid_replacement
end QuantitativeArithmeticRetainedIteration
