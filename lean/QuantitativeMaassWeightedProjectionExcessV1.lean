module

public import QuantitativeMaassPositiveTracialBoundV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- A supported error pays the finite projection trace, not the trace of the
ambient identity. -/
theorem tracial_right_supported_bound (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (B X E : 𝔄) (hE : IsStarProjection E) (hX : X*E=X) :
    |τ (B*X)|≤‖B‖*‖X‖*τ E := by
  have hte : 0≤τ E := by simpa only [map_zero] using hm hE.nonneg
  have hh := positive_tracial_mul_bound τ hm hc hs (B*X) E hE.nonneg
  rw [mul_assoc,hX] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (norm_mul_le B X) hte)

/-- Approximate fixing and an unweighted trace excess control every bounded
weight. The error is proportional to the finite canonical projection trace. -/
theorem weighted_projection_excess (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (B F E : 𝔄) (hF : 0≤F) (hE : IsStarProjection E)
    {δ : ℝ} (hfix : ‖F*E-E‖≤δ) :
    |τ (B*(F-E))|≤‖B‖*(τ F-τ E+4*δ*τ E) := by
  let X := F*E-E
  let G := (1-E)*F*(1-E)
  have hEE : E*E=E := hE.isIdempotentElem.eq
  have hEs : star E=E := hE.isSelfAdjoint.star_eq
  have hFs : star F=F := (IsSelfAdjoint.of_nonneg hF).star_eq
  have hXE : X*E=X := by dsimp only [X]; rw [sub_mul,mul_assoc,hEE]
  have hEXs : E*star X=star X := by
    have hh := congrArg star hXE
    simpa only [star_mul,hEs] using hh
  have hnE : ‖E‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg E hE.nonneg).mpr hE.le_one
  have hnX : ‖X‖≤δ := hfix
  have hte : 0≤τ E := by simpa only [map_zero] using hm hE.nonneg
  have htx : |τ X|≤δ*τ E := by
    have hh := positive_tracial_mul_bound τ hm hc hs X E hE.nonneg
    rw [hXE] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hnX hte)
  have hG : 0≤G := by
    have hh := star_left_conjugate_nonneg hF (1-E)
    simpa only [star_sub,star_one,hEs] using hh
  have htG : τ G=τ F-τ E-τ X := by
    have he : G=F-F*E-E*F+E*F*E := by dsimp only [G]; noncomm_ring
    have hef : τ (E*F)=τ (F*E) := hc E F
    have hefe : τ (E*F*E)=τ (F*E) := by
      rw [hc (E*F) E,←mul_assoc,hEE,hc E F]
    rw [he,map_add,map_sub,map_sub,hef,hefe]
    dsimp only [X]
    rw [map_sub]
    ring
  have hgt : τ G≤τ F-τ E+δ*τ E := by
    rw [htG]
    linarith [(abs_le.mp htx).1]
  have hbX : |τ (B*X)|≤‖B‖*δ*τ E :=
    (tracial_right_supported_bound τ hm hc hs B X E hE hXE).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnX (norm_nonneg B)) hte)
  have hbXs : |τ (B*star X)|≤‖B‖*δ*τ E := by
    have hh := positive_tracial_mul_bound τ hm hc hs (star X*B) E hE.nonneg
    have he : τ ((star X*B)*E)=τ (B*star X) := by
      rw [hc (star X*B) E,←mul_assoc,hEXs,hc (star X) B]
    rw [he] at hh
    have hn : ‖star X*B‖≤‖B‖*δ := by
      calc
        _≤‖star X‖*‖B‖ := norm_mul_le _ _
        _=‖B‖*‖X‖ := by rw [norm_star,mul_comm]
        _≤‖B‖*δ := mul_le_mul_of_nonneg_left hnX (norm_nonneg _)
    exact hh.trans (mul_le_mul_of_nonneg_right hn hte)
  have hbEX : |τ (B*(E*X))|≤‖B‖*δ*τ E := by
    have hsup : (E*X)*E=E*X := by rw [mul_assoc,hXE]
    have hn : ‖E*X‖≤δ := (norm_mul_le E X).trans
      ((mul_le_mul hnE hnX (norm_nonneg X) zero_le_one).trans_eq (one_mul δ))
    exact (tracial_right_supported_bound τ hm hc hs B (E*X) E hE hsup).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (norm_nonneg B)) hte)
  have he : F-E=G+X+star X-E*X := by
    dsimp only [G,X]
    rw [star_sub,star_mul,hEs,hFs]
    noncomm_ring
    rw [hEE]
    abel
  have hbG := positive_tracial_mul_bound τ hm hc hs B G hG
  have hmain : |τ (B*(F-E))|≤|τ (B*G)|+|τ (B*X)|+|τ (B*star X)|+|τ (B*(E*X))| := by
    rw [he,mul_sub,mul_add,mul_add,map_sub,map_add,map_add]
    exact (abs_sub _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  have hh := hmain.trans (add_le_add
    (add_le_add (add_le_add hbG hbX) hbXs) hbEX)
  have hhG := mul_le_mul_of_nonneg_left hgt (norm_nonneg B)
  nlinarith

/-- Inverse-metric pullback multiplies only the trace excess and fixing
error; the canonical trace is subtracted before this bound is applied. -/
theorem pullback_projection_excess (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (D F E : 𝔄) (hF : 0≤F) (hE : IsStarProjection E)
    {δ η : ℝ} (hfix : ‖F*E-E‖≤δ) (htrace : τ F≤τ E+η) :
    |τ (D*(F-E)*star D)|≤‖D‖^2*(η+4*δ*τ E) := by
  have he : τ (D*(F-E)*star D)=τ ((star D*D)*(F-E)) := by
    rw [hc (D*(F-E)) (star D),←mul_assoc]
  rw [he]
  have hh := weighted_projection_excess τ hm hc hs (star D*D) F E hF hE hfix
  rw [CStarRing.norm_star_mul_self,←pow_two] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg ‖D‖))

#print axioms pullback_projection_excess
#print axioms tracial_right_supported_bound
#print axioms weighted_projection_excess
end QuantitativeMaass
