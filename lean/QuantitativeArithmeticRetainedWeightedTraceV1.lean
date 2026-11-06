module

public import QuantitativeArithmeticRetainedPhysicalSectorV1
public import QuantitativeEulerEndpointApproximateTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedWeightedTrace
open ContinuousLinearMap AsymptoticSectorSigns AsymptoticCylinder
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedPhysicalSector QuantitativeArithmeticRetainedSectorReconstruction

variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N)

def coordinates (h : ℕ) (e : Sector N) :=
  QuantitativeArithmeticRetainedSectorProjection.coordinates A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e

theorem reconstruct_coordinates (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N)
    (h : ℕ) (e : Sector N) (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e (coordinates A P hR₀ hN h e a)=
      (AsymptoticRamifiedSectors.cylinderMap N h (h+1+P.s) (exponent A P+4) e P.epsilon_pos
        (by have := exponent_ge A P; omega) a : Space) :=
  QuantitativeArithmeticRetainedSectorProjection.coordinates_reconstruct A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad
    (physical_contraction A P hR₀ hN e (h+1)) a

theorem reconstruction_isometry (h : ℕ) (e : Sector N) (v : AsymptoticCylinderTerminal.Space P.ε) :
    ‖QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e v‖=‖v‖ :=
  QuantitativeArithmeticRetainedCylinderNormalization.normalized_norm A hR₀ hN P
    (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
    (fun p _ => ramifiedParameter_norm e p) (by omega : 2≤exponent A P+3) (h+1)
    (physical_contraction A P hR₀ hN e (h+1)) v

theorem normalizedPhysicalSector_finiteDimensional (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N)
    (h : ℕ) (e : Sector N) :
    FiniteDimensional ℂ (LinearMap.range (normalizedPhysicalSectorMap A P hR₀ hN h e)) :=
  QuantitativeArithmeticRetainedSectorProjection.physicalMap_finiteDimensional A hR₀ hN P h (h+1+P.s)
    (exponent A P+3) (by omega) (degree_bound A P h) e hdiv hbad
end QuantitativeArithmeticRetainedWeightedTrace

namespace QuantitativeArithmeticRetainedWeightedTrace
open ContinuousLinearMap QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace InnerProductSpace QuantitativeHolomorphic
open scoped InnerProduct
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (hR₀ : ∀p∈R₀,p.Prime)

/-- The actual full coefficient-sector rank is controlled by the weighted
holomorphic trace. Positivity and summability are proved from reconstruction;
the only residual premise concerns actual normalized sector vectors. -/
theorem sector_finrank_mul_le_trace (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (F : AsymptoticCylinderTerminal.Space P.ε →L[ℂ]
      AsymptoticCylinderTerminal.Space P.ε)
    (hF : 0≤F) (δ : ℝ)
    (herr : ∀ a,‖F (coordinates A P hR₀ hN h e a)-coordinates A P hR₀ hN h e a‖≤
      δ*‖coordinates A P hR₀ hN h e a‖) :
    let W := holomorphicSpace (2*h) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) (by positivity : 0<4*Real.pi) P.epsilon_pos
    let fb := fourierBasis (2*h) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) (by positivity : 0<4*Real.pi) P.epsilon_pos
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)≤
      trace fb (compressedSandwich (QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e) F W) := by
  intro W fb
  let U := QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e
  let C := AsymptoticRamifiedSectors.cylinderMap N h (h+1+P.s) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) e P.epsilon_pos (by have := QuantitativeArithmeticRetainedPreparedReconstruction.exponent_ge A P; omega)
  let T := compressedSandwich U F W
  have ht : 0≤T := by
    apply nonneg_iff_isPositive.mpr
    have hh := (nonneg_iff_isPositive.mp hF).adjoint_conj (U.adjoint.comp W.subtypeL)
    simpa only [T,compressedSandwich,adjoint_comp,adjoint_adjoint,ContinuousLinearMap.comp_assoc] using hh
  have hs : Summable (fun l => (⟪T (fb l),fb l⟫_ℂ).re) :=
    compressedSandwich_summable U F W fb (2*h) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4))
      (by positivity : 0<4*Real.pi) P.epsilon_pos
      (QuantitativeArithmeticRetainedFourierMajorant.normalized_fourier_gram A hR₀ hN P h e)
  have he : ∀ w∈LinearMap.range C,‖T w-w‖≤δ*‖w‖ := by
    rintro w ⟨a,rfl⟩
    let v := coordinates A P hR₀ hN h e a
    have hu : U v=(C a:Space) := reconstruct_coordinates A P hR₀ hN hdiv hbad h e a
    have hx : W.subtypeL.adjoint (U v)=C a := by
      rw [hu,W.adjoint_subtypeL]
      exact W.orthogonalProjectionOnto_mem_subspace_eq_self (C a)
    have hn : ‖v‖=‖C a‖ := by
      rw [←reconstruction_isometry A P hR₀ hN h e v]
      exact congrArg norm hu
    have hp : ‖W.subtypeL.adjoint‖≤1 := by
      rw [adjoint.norm_map]
      apply opNorm_le_bound _ zero_le_one
      intro w
      simp
    calc
      ‖T (C a)-C a‖=‖W.subtypeL.adjoint (U (F v-v))‖ := by
        rw [map_sub,map_sub,hx]
        rfl
      _ ≤ ‖U (F v-v)‖ := (W.subtypeL.adjoint.le_opNorm _).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      _ = ‖F v-v‖ := reconstruction_isometry A P hR₀ hN h e _
      _ ≤ δ*‖v‖ := herr a
      _ = δ*‖C a‖ := by rw [hn]
  let := QuantitativeArithmeticRetainedSectorReconstruction.sector_finiteDimensional A hR₀ hN P hdiv hbad h (h+1+P.s) e
  have hh := QuantitativeEulerEndpointApproximateTrace.finrank_mul_le_trace fb T ht (LinearMap.range C) δ he hs
  rw [AsymptoticRamifiedSectors.cylinderMap_finrank] at hh
  exact hh

#print axioms sector_finrank_mul_le_trace
end QuantitativeArithmeticRetainedWeightedTrace

namespace QuantitativeArithmeticRetainedWeightedTrace
open ContinuousLinearMap QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticObservation AsymptoticCompactObservationCount
open AsymptoticDiagonalTrace InnerProductSpace QuantitativeHolomorphic
open QuantitativeArithmeticRetainedPhysicalSector
open scoped InnerProduct
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (hR₀ : ∀p∈R₀,p.Prime) (P : Parameters A)

def terminalCompression (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) :=
  let S := AsymptoticCylinderTerminal.ambientLift P.ε
  S.adjoint.comp (F.comp S)

theorem ambient_sector_residual (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (hN : 0<N) (h : ℕ) (e : Sector N)
    (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) (δ : ℝ)
    (herr : ‖F*normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad-normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad‖≤δ)
    (a : AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :
    ‖terminalCompression A P F (coordinates A P hR₀ hN h e a)-coordinates A P hR₀ hN h e a‖≤
      δ*‖coordinates A P hR₀ hN h e a‖ := by
  let S := AsymptoticCylinderTerminal.ambientLift P.ε
  let v := coordinates A P hR₀ hN h e a
  let E := normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad
  have hiso : ∀ v,‖S v‖=‖v‖ := (norm_map_iff_adjoint_comp_self S).mpr
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)
  have hSn : ‖S.adjoint‖≤1 := by
    rw [adjoint.norm_map]
    apply opNorm_le_bound _ zero_le_one
    intro v
    rw [hiso,one_mul]
  have hSv : S.adjoint (S v)=v := congrArg (fun T => T v)
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)
  have hEv : E (S v)=S v := by
    let _ := normalizedPhysicalSector_finiteDimensional A P hR₀ hN hdiv hbad h e
    exact (LinearMap.range (normalizedPhysicalSectorMap A P hR₀ hN h e)).starProjection_eq_self_iff.mpr ⟨a,rfl⟩
  have he : (F*E-E) (S v)=F (S v)-S v := by
    change F (E (S v))-E (S v)=_
    rw [hEv]
  calc
    ‖terminalCompression A P F v-v‖=‖S.adjoint ((F*E-E) (S v))‖ := by
      rw [he,map_sub,hSv]
      rfl
    _ ≤ ‖(F*E-E) (S v)‖ := (S.adjoint.le_opNorm _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hSn (norm_nonneg _))
    _ ≤ ‖F*E-E‖*‖S v‖ := (F*E-E).le_opNorm _
    _ ≤ δ*‖S v‖ := mul_le_mul_of_nonneg_right herr (norm_nonneg _)
    _ = δ*‖v‖ := by rw [hiso]

/-- Actual ambient sector preservation yields an actual summable weighted
holomorphic trace bound for the original coefficient-sector dimension. -/
theorem ambient_sector_finrank_mul_le_trace (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (hN : 0<N) (h : ℕ) (e : Sector N)
    (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) (hF : 0≤F) (δ : ℝ)
    (herr : ‖F*normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad-normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad‖≤δ) :
    let W := holomorphicSpace (2*h) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) (by positivity : 0<4*Real.pi) P.epsilon_pos
    let fb := fourierBasis (2*h) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) (by positivity : 0<4*Real.pi) P.epsilon_pos
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)≤
      trace fb (AsymptoticObservation.compressedSandwich (QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ hN P h e) (terminalCompression A P F) W) := by
  refine sector_finrank_mul_le_trace A hR₀ hdiv hbad hN P h e (terminalCompression A P F) ?_ δ ?_
  · exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hF).adjoint_conj
      (AsymptoticCylinderTerminal.ambientLift P.ε))
  · exact ambient_sector_residual A hR₀ P hdiv hbad hN h e F δ herr

#print axioms ambient_sector_residual
#print axioms ambient_sector_finrank_mul_le_trace
end QuantitativeArithmeticRetainedWeightedTrace

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns Polynomial
open QuantitativeEulerEndpointPrepared QuantitativeHolomorphic AsymptoticFiniteBranch
open QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointExponentialParameters
open QuantitativeEulerEndpointNestedPerturbation QuantitativeArithmeticRetainedWeightedTrace
open AsymptoticCylinder AsymptoticFourierNorm AsymptoticDiagonalTrace
open scoped Classical MatrixGroups
variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (hR₀ : ∀p∈R₀,p.Prime) (P : Parameters A)
    (e : Sector N) (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs : ℝ)

theorem actualFiniteExpression_sector_trace (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N) (n h : ℕ) {K : ℝ} (hK : 0≤K) (q : ℕ → ℝ[X])
    (hq : ∀ j<n,ScalarSharpening (q j))
    (hbudget : comparisonBudget (fun j => power (effortAt A P hR₀ e n
      (actualBlock A P hR₀ hN excluded threshold e S hS W B Bg D H₀ G C Kobs n) j)) q n≤Real.exp (Real.exp (K*(4:ℝ)^n))) :
    let V := holomorphicSpace (2*h) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) (by positivity : 0<4*Real.pi) P.epsilon_pos
    let fb := fourierBasis (2*h) ((QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4)) (by positivity : 0<4*Real.pi) P.epsilon_pos
    let F := holomorphicSum (actualFiniteExpression A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n (Real.exp ((K+1)*(4:ℝ)^n)) q) (h+1)
    (1-2/(4:ℝ)^n)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)≤
      trace fb (AsymptoticObservation.compressedSandwich (QuantitativeArithmeticRetainedFilterTrace.reconstruction A hR₀ (NeZero.pos N) P h e) (terminalCompression A P F) V) := by
  apply ambient_sector_finrank_mul_le_trace A hR₀ P hdiv hbad (NeZero.pos N) h e
  · exact (actualFiniteExpression_physical_order A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      n h (Real.exp ((K+1)*(4:ℝ)^n)) q hq).1
  · exact actualFiniteExpression_sector_paid A P hR₀ e hN excluded threshold S hS W B Bg D H₀ G C Kobs
      hdiv hbad n h hK q hq hbudget

#print axioms actualFiniteExpression_sector_trace
end QuantitativeArithmeticRetainedIteration
