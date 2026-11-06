module

public import QuantitativeArithmeticRetainedFourierMajorantV1
public import QuantitativeHolomorphicSectorFilterTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedFilterTrace
open ContinuousLinearMap InnerProductSpace AsymptoticSectorSigns AsymptoticCylinder
open AsymptoticCompactObservationCount AsymptoticObservation AsymptoticDiagonalTrace
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedSectorReconstruction
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedCylinderNormalization
open QuantitativeArithmeticRetainedFourierMajorant QuantitativeHolomorphic
open scoped InnerProduct

section General
variable {G H K ι : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
/-- The common positive filter fixes every vector whose reconstructed
image satisfies the selected rows. This does not depend on the certificate. -/
theorem filter_fixes (qs : Finset ι) (L : ι → H →L[ℂ] K) (b : ι → ℝ)
    (V : G →L[ℂ] H) (v : G) (hv : ∀i∈qs,L i (V v)=0) (d : ℕ) :
    finiteRowFilter qs L b V d v=v := by
  have hg : finiteRowGram qs L V v=0 := by
    rw [finiteRowGram,_root_.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    change ((L i).comp V).adjoint (L i (V v))=0
    rw [hv i hi,map_zero]
  have hs : (1-(finiteRowBound qs b)⁻¹ • finiteRowGram qs L V) v=v := by
    simp only [sub_apply,smul_apply,hg,smul_zero,sub_zero]
    rfl
  induction d with
  | zero => rfl
  | succ d ih =>
    change ((1-(finiteRowBound qs b)⁻¹ • finiteRowGram qs L V)^(d+1)) v=v
    rw [pow_succ',mul_apply_eq_comp]
    exact (congrArg (fun w : G => (1-(finiteRowBound qs b)⁻¹ • finiteRowGram qs L V) w) ih).trans hs
end General

/-- Compact observations vanish on the original coefficient sector for
any integrable cylinder weight, not just the primitive spanning parameters. -/
theorem row_annihilates {N : ℕ} (hN : 0<N) (h d t : ℕ)
    {ε : ℝ} (hε : 0<ε) (hd : 2*d+4≤2*h+2*t+1) (e : Sector N)
    (r : Row N) {s : Set UpperHalfPlane} (hs : IsCompact s)
    (a : AsymptoticRamifiedSectors.sector N h d e) :
    rowOperator hN r e hs hε t (h+1)
      (AsymptoticRamifiedSectors.cylinderMap N h d t e hε hd a:Space)=0 := by
  cases r with
  | twist q hq =>
    have hFE := AsymptoticSectorReconstruction.coefficientSector_laws hN hq
      (multiplier e) (h+1) d a.val (a.property.1 q hq)
    exact AsymptoticTwistObservation.residual_eq_zero N q hN hq hs hε t (h+1) (multiplier e q)
      (FinitenessFourierConstruction.fourier a.val.val) (FinitenessFourierConstruction.periodic a.val.val)
      (hFE q (dvd_refl q)) _ (AsymptoticCylinderLift.lift_fourierMap h t d hε hd a.val)
  | ramified p hp hpN =>
    exact AsymptoticRamifiedObservation.residual_eq_zero p hp.pos hs hε t h
      (AsymptoticCylinderRamified.eigenvalue e p) a.val.val
      (AsymptoticCylinder.coefficientSpace_polynomial _ a.val)
      (AsymptoticCylinderRamified.coefficient_row e p hp hpN a) _
      (AsymptoticCylinderLift.lift_fourierMap h t d hε hd a.val)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime) (hN : 0<N) (P : Parameters A)

def reconstruction (h : ℕ) (e : Sector N) :=
  normalized A hS hN P (multiplier e) (ramifiedParameter e) (by omega : 2≤exponent A P+3) (h+1)

theorem reconstruction_norm (h : ℕ) (e : Sector N) :
    ‖reconstruction A hS hN P h e‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change ‖normalized A hS hN P (multiplier e) (ramifiedParameter e)
    (by omega : 2≤exponent A P+3) (h+1) v‖≤1*‖v‖
  rw [one_mul]
  exact (normalized_norm A hS hN P
    (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
    (fun p _ => ramifiedParameter_norm e p) (by omega : 2≤exponent A P+3) (h+1)
    (physical_contraction A P hS hN e (h+1)) v).le

variable {ι : Type*}

def observationFilter (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ) :=
  finiteRowFilter qs (fun i => rowOperator hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) (h+1))
    (fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4))
    (reconstruction A hS hN P h e) d

theorem observationFilter_order (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    0≤observationFilter A hS hN P h e qs r s hs d ∧
      observationFilter A hS hN P h e qs r s hs d≤1 ∧
      ‖observationFilter A hS hN P h e qs r s hs d‖≤1 :=
  finiteRowFilter_order _ _ _ (fun i => rowOperator_norm_le hN (r i) e (hs i)
    P.epsilon_pos (exponent A P+4) (h+1)) _ (reconstruction_norm A hS hN P h e) d

def holomorphicFilter (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ) :=
  compressedSandwich (reconstruction A hS hN P h e)
    (observationFilter A hS hN P h e qs r s hs d)
    (holomorphicSpace (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)

/-- Dimension of the original mixed sector is bounded by the actual
positive Fourier trace, with the row equations and reconstruction discharged. -/
theorem sector_finrank_le_trace (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    (Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)≤
      trace (fourierBasis (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
        (holomorphicFilter A hS hN P h e qs r s hs d) := by
  let W := holomorphicSpace (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos
  let fb := fourierBasis (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos
  let U := reconstruction A hS hN P h e
  let F := observationFilter A hS hN P h e qs r s hs d
  have hd := degree_bound A P h
  let C := AsymptoticRamifiedSectors.cylinderMap N h (h+1+P.s) (exponent A P+4) e P.epsilon_pos (by omega)
  let V := QuantitativeArithmeticRetainedSectorProjection.coordinates A hS hN P h (h+1+P.s)
    (exponent A P+3) (by omega) hd e
  have hv (a) : U (V a)=(C a:Space) :=
    QuantitativeArithmeticRetainedSectorProjection.coordinates_reconstruct A hS hN P h (h+1+P.s)
      (exponent A P+3) (by omega) hd e hdiv hbad (physical_contraction A P hS hN e (h+1)) a
  have hfix (a) : F (V a)=V a := by
    apply filter_fixes
    intro i _
    rw [hv]
    exact row_annihilates hN h (h+1+P.s) (exponent A P+4) P.epsilon_pos (by omega) e (r i) (hs i) a
  have hp : (compressedSandwich U F W).IsPositive := by
    have hp := (nonneg_iff_isPositive.mp (observationFilter_order A hS hN P h e qs r s hs d).1).adjoint_conj
      (U.adjoint.comp W.subtypeL)
    simpa only [compressedSandwich,adjoint_comp,adjoint_adjoint,comp_assoc] using hp
  have hsum := compressedSandwich_summable U F W fb (2*h) (exponent A P+4)
    (by positivity : 0<4*Real.pi) P.epsilon_pos (normalized_fourier_gram A hS hN P h e)
  have hfixed : ∀w∈LinearMap.range C,compressedSandwich U F W w=w := by
    rintro w ⟨a,rfl⟩
    change W.subtypeL.adjoint (U (F (V a)))=C a
    rw [hfix,hv,W.adjoint_subtypeL]
    exact W.orthogonalProjectionOnto_mem_subspace_eq_self (C a)
  let _ := sector_finiteDimensional A hS hN P hdiv hbad h (h+1+P.s) e
  have hf := finrank_le_trace fb (compressedSandwich U F W) hp (LinearMap.range C) hfixed hsum
  rw [AsymptoticRamifiedSectors.cylinderMap_finrank] at hf
  exact hf

theorem original_count_le_trace (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (h : ℕ) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    ((FinitenessOriginalInput.S N (2*(h+1))).ncard:ℝ)≤∑e : Sector N,
      trace (fourierBasis (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
        (holomorphicFilter A hS hN P h e qs r s hs d) := by
  have hc := (original_count A P hS hN hdiv hbad h).2
  have hc' : ((FinitenessOriginalInput.S N (2*(h+1))).ncard:ℝ)≤
      ∑e : Sector N,(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ) := by
    exact_mod_cast hc
  exact hc'.trans (Finset.sum_le_sum (fun e _ => sector_finrank_le_trace A hS hN P hdiv hbad h e qs r s hs d))

/-- The same observation filter with any contraction reconstruction. -/
def filteredCompression (h : ℕ) (e : Sector N) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i))
    (V : AsymptoticCylinderTerminal.Space P.ε →L[ℂ] Space) (d : ℕ) :=
  compressedSandwich V
    (finiteRowFilter qs
      (fun i => rowOperator hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) (h+1))
      (fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)) V d)
    (holomorphicSpace (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)

def finiteFilter (δ Y : ℝ) (h : ℕ) (e : Sector N) (n : ℕ) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ) :=
  filteredCompression A hN P h e qs r s hs
    (polynomialNormalizedReconstruction
      (QuantitativeArithmeticRetainedFiniteNormalization.physicalScaled A P hS hN δ Y e (h+1)) n) d

def traceMajorant (n : ℕ) : ℝ := max (((Real.sqrt (gramLower A P))⁻¹)^2) (((3/2:ℝ)^n)^2)

def traceError (δ Y : ℝ) (n d : ℕ) : ℝ :=
  (2*d+2:ℝ)*QuantitativeArithmeticRetainedFiniteNormalization.normalizedError A P δ Y n

/-- The quantitative comparison uses the actual finite mixed expression;
no primitive certificate or unproved trace estimate is supplied as input. -/
theorem finite_trace_error {δ Y : ℝ} (hδ : 0<δ) (hY : 0≤Y)
    (h : ℕ) (e : Sector N) (n : ℕ) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ)
    (hD : 0<traceError A P δ Y n d) (hD1 : traceError A P δ Y n d≤1) :
    let fb := fourierBasis (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos
    ‖trace fb (finiteFilter A hS hN P δ Y h e n qs r s hs d)-
      trace fb (holomorphicFilter A hS hN P h e qs r s hs d)‖/(4*h+2:ℝ)≤
      (2+2*traceMajorant A P n*AsymptoticFourierNorm.majorantConstant (exponent A P+4) (4*Real.pi) P.ε)*
        Real.sqrt (traceError A P δ Y n d) := by
  let W := holomorphicSpace (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos
  let fb := fourierBasis (2*h) (exponent A P+4) (by positivity : 0<4*Real.pi) P.epsilon_pos
  let U := reconstruction A hS hN P h e
  let V := polynomialNormalizedReconstruction
    (QuantitativeArithmeticRetainedFiniteNormalization.physicalScaled A P hS hN δ Y e (h+1)) n
  let L := fun i => rowOperator hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) (h+1)
  let b := fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)
  have hL : ∀i,‖L i‖≤b i := fun i => rowOperator_norm_le hN (r i) e (hs i) _ _ _
  have hU : ‖U‖≤1 := reconstruction_norm A hS hN P h e
  have hV : ‖V‖≤1 := polynomialNormalizedReconstruction_norm_le _
    (QuantitativeArithmeticRetainedFiniteNormalization.physicalScaled_norm A P hS hN δ Y e (h+1)) n
  have hC : 0≤traceMajorant A P n := (sq_nonneg _).trans (le_max_left _ _)
  have hbU (l : ℕ) : ‖(⟪filteredCompression A hN P h e qs r s hs U d (fb l),fb l⟫_ℂ).re‖≤
      traceMajorant A P n*AsymptoticFourierNorm.modeRatio (2*h) (exponent A P+4) (4*Real.pi) P.ε (l+1) := by
    apply (finiteRowFilter_diagonal_bound qs L b hL U hU d W (fb l)).trans
    apply (normalized_fourier_gram A hS hN P h e l).trans
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (AsymptoticFourierNorm.modeRatio_nonneg _ _ _ _ P.epsilon_pos)
  have hbV (l : ℕ) : ‖(⟪filteredCompression A hN P h e qs r s hs V d (fb l),fb l⟫_ℂ).re‖≤
      traceMajorant A P n*AsymptoticFourierNorm.modeRatio (2*h) (exponent A P+4) (4*Real.pi) P.ε (l+1) := by
    apply (finiteRowFilter_diagonal_bound qs L b hL V hV d W (fb l)).trans
    apply (finite_fourier_gram A hS hN P δ Y h e n l).trans
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (AsymptoticFourierNorm.modeRatio_nonneg _ _ _ _ P.epsilon_pos)
  have herr : ‖filteredCompression A hN P h e qs r s hs V d-
      filteredCompression A hN P h e qs r s hs U d‖≤traceError A P δ Y n d := by
    apply (orthogonalCompression_sub_norm_le W _ _).trans
    apply (finiteRowFilter_sandwich_difference qs L b hL U V hU hV d).trans
    exact mul_le_mul_of_nonneg_left
      (QuantitativeArithmeticRetainedFiniteNormalization.physical_normalized_error A P hS hN hδ hY e (h+1) n)
      (by positivity)
  have ht := normalized_trace_sub_le_sqrt_of_absolute_majorants fb _ _ (2*h) (exponent A P+4)
    (by positivity : 0<4*Real.pi) P.epsilon_pos hC hD hD1 herr hbV hbU
  dsimp only [finiteFilter,holomorphicFilter,observationFilter,filteredCompression,U,V,fb] at ht ⊢
  convert ht using 1
  push_cast
  ring

#print axioms finite_trace_error

#print axioms filter_fixes
#print axioms row_annihilates
#print axioms observationFilter_order
#print axioms sector_finrank_le_trace
#print axioms original_count_le_trace
end QuantitativeArithmeticRetainedFilterTrace
