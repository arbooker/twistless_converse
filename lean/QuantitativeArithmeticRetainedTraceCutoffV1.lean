module

public import QuantitativeArithmeticRetainedFilterTraceV1
public import QuantitativeHolomorphicFilterCutoffV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedTraceCutoff
open ContinuousLinearMap AsymptoticSectorSigns AsymptoticCylinder AsymptoticFourierNorm
open AsymptoticCylinderModeComparison AsymptoticFiniteBranch
open AsymptoticObservation AsymptoticCompactObservationCount AsymptoticDiagonalTrace
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedPreparedReconstruction QuantitativeHolomorphic
open QuantitativeArithmeticRetainedFiniteNormalization QuantitativeArithmeticRetainedFourierMajorant

private theorem retained_sandwich {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (V : G →L[ℂ] Space) (F : G →L[ℂ] G) (Y H : ℝ)
    (hV : (upperProjection Y).comp V=V) (W : Submodule ℂ Space) [CompleteSpace W] :
    compressedSandwich (retainedProjection Y H) (V.comp (F.comp V.adjoint)) W=
      compressedSandwich (removePart (upperProjection H) V) F W := by
  have hp : (retainedProjection Y H).comp V=removePart (upperProjection H) V := by
    rw [retainedProjection,comp_assoc,hV]
    ext1 x
    simp [removePart]
  rw [←hp]
  simp only [compressedSandwich,adjoint_comp,retainedProjection_adjoint,comp_assoc]

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime) (hN : 0<N) (P : Parameters A)

theorem finite_left_height (δ Y : ℝ) (e : Sector N) (m n : ℕ) :
    (upperProjection Y).comp (polynomialNormalizedReconstruction (physicalScaled A P hS hN δ Y e m) n)=
      polynomialNormalizedReconstruction (physicalScaled A P hS hN δ Y e m) n := by
  have hp : (AsymptoticCylinderTerminal.projection Y).comp (AsymptoticCylinderTerminal.projection Y)=
      AsymptoticCylinderTerminal.projection Y := AsymptoticCylinderTerminal.projection_comp_of_le le_rfl
  rw [polynomialNormalizedReconstruction,←comp_assoc]
  have hv : (upperProjection Y).comp (physicalScaled A P hS hN δ Y e m)=physicalScaled A P hS hN δ Y e m := by
    rw [physicalScaled,comp_smul,upperProjection_eq_terminal,←comp_assoc,hp]
  rw [hv]

variable {ι : Type*}

def cylinderFilter (δ Y : ℝ) (h : ℕ) (e : Sector N) (n : ℕ) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ) :=
  let V := polynomialNormalizedReconstruction (physicalScaled A P hS hN δ Y e (h+1)) n
  V.comp ((finiteRowFilter qs
    (fun i => rowOperator hN (r i) e (hs i) P.epsilon_pos (exponent A P+4) (h+1))
    (fun i => rowBound hN (r i) (hs i) P.epsilon_pos (exponent A P+4)) V d).comp V.adjoint)

def retainedTrace (δ Y H : ℝ) (h : ℕ) (e : Sector N) (n : ℕ) (qs : Finset ι) (r : ι → Row N)
    (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d t : ℕ) : ℝ :=
  trace (fourierBasis (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (compressedSandwich (retainedProjection Y H) (cylinderFilter A hS hN P δ Y h e n qs r s hs d)
      (holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos))

/-- Upper-cusp removal for the actual finite mixed filter, with the sharp
Newton majorant and the explicit Fourier mass bound. -/
theorem upper_cut_error (δ Y H : ℝ) (hH : 0<H) (h : ℕ) (e : Sector N) (n : ℕ)
    (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane) (hs : ∀i,IsCompact (s i)) (d : ℕ) :
    let t := exponent A P+4
    let fb := fourierBasis (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos
    let B := (3/2:ℝ)^n
    ‖trace fb (QuantitativeArithmeticRetainedFilterTrace.finiteFilter A hS hN P δ Y h e n qs r s hs d)-
      retainedTrace A hS hN P δ Y H h e n qs r s hs d t‖/(2*h+2:ℝ)≤
      upperCutError (B^2*(1+majorantConstant t (4*Real.pi) P.ε)) B 1
        (massBound (2*h) t (4*Real.pi) H/(2*h+2:ℝ)) := by
  dsimp only
  let t := exponent A P+4
  let W := holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos
  let fb := fourierBasis (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos
  let V := polynomialNormalizedReconstruction (physicalScaled A P hS hN δ Y e (h+1)) n
  let R := finiteWeighted A hS hN P δ Y e (h+1) n
  let L := fun i => rowOperator hN (r i) e (hs i) P.epsilon_pos t (h+1)
  let b := fun i => rowBound hN (r i) (hs i) P.epsilon_pos t
  let F := finiteRowFilter qs L b V d
  have hV : ‖V‖≤1 := polynomialNormalizedReconstruction_norm_le _ (physicalScaled_norm A P hS hN δ Y e (h+1)) n
  have hF : ‖F‖≤1 := (finiteRowFilter_order qs L b
    (fun i => rowOperator_norm_le hN (r i) e (hs i) _ _ _) V hV d).2.2
  have ht := factored_upperCut_trace_bound R F (finiteWeighted_norm A hS hN P δ Y e (h+1) n)
    hF (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos hH
  have hv : (inclusion P.epsilon_pos).comp R=V := (finite_weighted A hS hN P δ Y e (h+1) n).symm
  rw [hv] at ht
  have he : retainedTrace A hS hN P δ Y H h e n qs r s hs d t=
      upperCutTrace V F (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos H :=
    congrArg (trace fb) (retained_sandwich V F Y H (finite_left_height A hS hN P δ Y e (h+1) n) W)
  rw [he]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at ht
  apply ht.trans
  have hm := div_le_div_of_nonneg_right
    (upperCompression_trace_le_massBound (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos hH)
    (by positivity : (0:ℝ)≤2*h+2)
  unfold upperCutError
  gcongr

#print axioms finite_left_height
#print axioms upper_cut_error
end QuantitativeArithmeticRetainedTraceCutoff
