module

public import QuantitativeMaassAmbientNewBandFilterV1
public import QuantitativeMaassOldFilterContractionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open ContinuousLinearMap QuantitativeNinaMaass
namespace QuantitativeMaass

/-- The normalized cover-range projection is orthogonal on the full
Hilbert space, without a cusp or finite-dimensional restriction. -/
theorem scaled_cover_projection {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : E→L[ℂ]H) (q : ℝ) (hq : 0<q)
    (hC : ∀ x,C.adjoint (C x)=(q:ℂ) • x) :
    let P := ((q⁻¹:ℝ):ℂ) • C.comp C.adjoint
    IsSelfAdjoint P ∧ IsIdempotentElem P := by
  intro P
  have hc : ((q⁻¹:ℝ):ℂ)*(q:ℂ)=1 := by
    rw [Complex.ofReal_inv,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hq.ne')]
  constructor
  · change P.adjoint=P
    dsimp only [P]
    rw [map_smulₛₗ,adjoint_comp,adjoint_adjoint]
    congr 1
    exact Complex.conj_ofReal (q⁻¹)
  · apply ContinuousLinearMap.ext
    intro x
    change ((q⁻¹:ℝ):ℂ) • C (C.adjoint (((q⁻¹:ℝ):ℂ) • C (C.adjoint x)))=
      ((q⁻¹:ℝ):ℂ) • C (C.adjoint x)
    rw [map_smul,hC,map_smul,map_smul,smul_smul,smul_smul]
    rw [mul_assoc,hc,mul_one]

/-- Orthogonal old projections conjugate through the actual Fricke
involution. No commutation of the two old projections is required. -/
theorem conjugate_orthogonal_projection {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P W : H→L[ℂ]H) (hP : IsSelfAdjoint P) (hPP : IsIdempotentElem P)
    (hW : IsSelfAdjoint W) (hWW : Function.Involutive W) :
    IsSelfAdjoint (W.comp (P.comp W)) ∧ IsIdempotentElem (W.comp (P.comp W)) := by
  constructor
  · change (W.comp (P.comp W)).adjoint=W.comp (P.comp W)
    simp only [adjoint_comp,hW.adjoint_eq,hP.adjoint_eq,comp_assoc]
  · apply ContinuousLinearMap.ext
    intro x
    change W (P (W (W (P (W x)))))=W (P (W x))
    rw [hWW]
    have hp : P (P (W x))=P (W x) := DFunLike.congr_fun hPP (W x)
    rw [hp]

theorem ambientSimpleNewFilter_norm (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) [NeZero (p*M)] (m : ℕ) :
    ‖ambientSimpleNewFilter (Nat.mul_pos (Fact.out : p.Prime).pos hM)
      (Nat.dvd_mul_left M p) p m‖≤1 := by
  let hN := Nat.mul_pos (Fact.out : p.Prime).pos hM
  let C := levelCover (Nat.dvd_mul_left M p)
  let W := (frickeIsometry (p*M) hN).toContinuousLinearMap
  let c : ℂ := (((((p:ℝ)+1)⁻¹:ℝ):ℂ))
  let P := c • C.comp C.adjoint
  let Q := W.comp (P.comp W)
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have huv : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    rw [←Nat.gcd_eq_gcd_ab,hcop.gcd_eq_one,Int.natCast_one]
  have hCC (x : AutomorphicSpace M) : C.adjoint (C x)=Complex.ofReal ((p:ℝ)+1) • x := by
    change levelTrace (Nat.dvd_mul_left M p) (levelCover (Nat.dvd_mul_left M p) x)=_
    rw [levelTrace_cover]
    have hi := HeckeL2.cover_index M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) huv
    change Nat.card (AsymptoticCongruenceStrip.gamma M ⧸
      (AsymptoticCongruenceStrip.gamma (p*M)).subgroupOf (AsymptoticCongruenceStrip.gamma M))=p+1 at hi
    rw [hi]
    simp only [Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]
  have hp := scaled_cover_projection C ((p:ℝ)+1) (by positivity) hCC
  change IsSelfAdjoint P ∧ IsIdempotentElem P at hp
  have hq := conjugate_orthogonal_projection P W hp.1 hp.2
    (frickeIsometry_selfAdjoint (p*M) hN) (frickeIsometry_involutive (p*M) hN)
  have he : c • ambientDivisorOldPair hN (Nat.dvd_mul_left M p)=P+Q := by
    apply ContinuousLinearMap.ext
    intro x
    change c • (C (C.adjoint x)+W (C (C.adjoint (W x))))=
      c • C (C.adjoint x)+W (c • C (C.adjoint (W x)))
    rw [smul_add,map_smul]
  apply opNorm_le_bound _ zero_le_one
  intro x
  have hPP : IsIdempotentElem P.toLinearMap := by
    apply LinearMap.ext
    intro y
    exact DFunLike.congr_fun hp.2 y
  have hQQ : IsIdempotentElem Q.toLinearMap := by
    apply LinearMap.ext
    intro y
    exact DFunLike.congr_fun hq.2 y
  have hh := two_projection_filter_pointwise P.toLinearMap Q.toLinearMap
    hp.1.isSymmetric hq.1.isSymmetric hPP hQQ m x
  change ‖(ambientSimpleNewFilter hN (Nat.dvd_mul_left M p) p m) x‖≤1*‖x‖
  rw [one_mul,ambientSimpleNewFilter,he]
  have hu : (1-(1/2:ℂ) • (P+Q)).toLinearMap=
      1-(1/2:ℂ) • (P.toLinearMap+Q.toLinearMap) := rfl
  rw [←hu,←toLinearMap_pow] at hh
  exact hh

#print axioms scaled_cover_projection
#print axioms conjugate_orthogonal_projection
#print axioms ambientSimpleNewFilter_norm
end QuantitativeMaass
