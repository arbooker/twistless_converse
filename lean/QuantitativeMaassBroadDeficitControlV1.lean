module

public import QuantitativeMaassLVDeficitOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)

include hNp hpres

/-- The unfiltered LV deficit controls the entire noncuspidal part.
This is an estimate on the full quotient, including continuous spectrum. -/
theorem actualLVDeficit_noncuspidal_norm (d : ℕ) (x : AutomorphicSpace N) :
    ‖x-localCuspidalProjection N hN x‖ ≤
      ‖actualLVDeficit N p hN hpN a b hab d x‖ := by
  have he := congrArg (fun T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => T x)
    (localCuspidalProjection_actualLVFilter N p hN hpN hNp hpres a b hab d)
  change localCuspidalProjection N hN (actualLVFilter N p hN hpN a b hab d x)=
    actualLVFilter N p hN hpN a b hab d x at he
  have hb := (localCuspidalSpace N hN)ᗮ.norm_starProjection_apply_le
    (actualLVDeficit N p hN hpN a b hab d x)
  rw [Submodule.starProjection_orthogonal] at hb
  change ‖actualLVDeficit N p hN hpN a b hab d x-
    localCuspidalProjection N hN (actualLVDeficit N p hN hpN a b hab d x)‖ ≤ _ at hb
  have hid : actualLVDeficit N p hN hpN a b hab d x-
      localCuspidalProjection N hN (actualLVDeficit N p hN hpN a b hab d x)=
      x-localCuspidalProjection N hN x := by
    change (x-actualLVFilter N p hN hpN a b hab d x)-
      localCuspidalProjection N hN (x-actualLVFilter N p hN hpN a b hab d x)=_
    rw [map_sub,he]
    module
  rwa [hid] at hb

/-- A broad approximation can be inserted before measuring the LV
deficit. No commutation between the packet, cutoff or sector filter
is assumed. -/
theorem packet_noncuspidal_error_sq (d : ℕ)
    (Q : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (x : AutomorphicSpace N) :
    ‖x-localCuspidalProjection N hN x‖^2 ≤
      2*‖actualLVDeficit N p hN hpN a b hab d (Q x)‖^2+2*‖Q x-x‖^2 := by
  let D := actualLVDeficit N p hN hpN a b hab d
  have hD : ‖D (x-Q x)‖ ≤ ‖x-Q x‖ :=
    (D.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (actualLVDeficit_order N p hN hpN a b hab d).2.2)
  have he : D x=D (Q x)+D (x-Q x) := by
    rw [← map_add]
    congr 1
    module
  have hh := actualLVDeficit_noncuspidal_norm N p hN hpN hNp hpres a b hab d x
  change ‖x-localCuspidalProjection N hN x‖ ≤ ‖D x‖ at hh
  rw [he] at hh
  have hb := hh.trans ((norm_add_le _ _).trans (add_le_add le_rfl hD))
  rw [norm_sub_rev x (Q x)] at hb
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
  nlinarith [sq_nonneg (‖D (Q x)‖-‖Q x-x‖)]

/-- An arbitrary bounded ambient filter is applied only after removing
the noncuspidal error. Its norm, rather than its polynomial coefficient
mass inside the LV trace, is the sole additional cost. -/
theorem filtered_packet_noncuspidal_error_sq (d : ℕ)
    (Q F : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (x : AutomorphicSpace N) :
    ‖F x-F (localCuspidalProjection N hN x)‖^2 ≤ ‖F‖^2*
      (2*‖actualLVDeficit N p hN hpN a b hab d (Q x)‖^2+2*‖Q x-x‖^2) := by
  rw [← map_sub]
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (F.le_opNorm (x-localCuspidalProjection N hN x))
  rw [mul_pow] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (packet_noncuspidal_error_sq N p hN hpN hNp hpres a b hab d Q x) (sq_nonneg _))

#print axioms actualLVDeficit_noncuspidal_norm
#print axioms packet_noncuspidal_error_sq
#print axioms filtered_packet_noncuspidal_error_sq

end QuantitativeMaass
