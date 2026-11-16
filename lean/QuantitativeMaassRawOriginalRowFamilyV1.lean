module

public import QuantitativeMaassEulerCoherentRowsV1
public import QuantitativeEulerEndpointSectorRowsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawPrepared
open UpperHalfPlane AsymptoticSectorSigns AsymptoticFiniteBranch ContinuousLinearMap
open QuantitativeEulerEndpointPrepared AsymptoticCompactObservationCount QuantitativeEulerDensityGenerators

variable {N : ℕ} [NeZero N] (e : Sector N) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (u : AsymptoticHyperbolicSlash.Space)
    (hu : ∀ (row : Row N) (s : Set ℍ) (hs : IsCompact s),
      holomorphicSum (rowExpression (NeZero.pos N) row e hs hε t) 0 u=0)

include hu in
theorem baseline_zero_of_original_rows {s : Set ℍ} (hs : IsCompact s)
    (i : NewBaselineIndex N) :
    holomorphicSum (originalBaselineExpression N e hs hε t i) 0 u=0 := by
  cases i with
  | inl i =>
    cases i with
    | none =>
      simpa only [originalBaselineExpression,rowExpression,multiplier_one] using
        hu (.twist 1 Nat.zero_lt_one) s hs
    | some a =>
      have hf : ¬(primeLift N a).q∣N := fun hd =>
        (not_le_of_gt (primeLift N a).large) (Nat.le_of_dvd (NeZero.pos N) hd)
      simpa only [originalBaselineExpression,rowExpression,
        multiplier_fresh e (primeLift N a).prime hf] using
          hu (.twist (primeLift N a).q (primeLift N a).prime.pos) s hs
  | inr p =>
    simpa only [originalBaselineExpression,rowExpression] using
      hu (.ramified p.val (Nat.mem_primeFactors.mp p.property).1
        (Nat.mem_primeFactors.mp p.property).2.1) s hs

include hu in
theorem packet_zero_of_original_rows {s : Set ℍ} (hs : IsCompact s)
    (l : List (EligiblePrime N)) (i : Fin l.length) :
    holomorphicSum (originalPacketSequenceExpression hs hε N (NeZero.pos N) (sign e.1) t l i) 0 u=0 := by
  have hz := hu (.twist l[i.val].val l[i.val].property.1.pos) s hs
  rw [rowExpression,multiplier_fresh e l[i.val].property.1 l[i.val].property.2] at hz
  rw [originalPacketSequenceExpression,originalPacketExpression,holomorphicSum_scale,smul_apply,hz,smul_zero]

#print axioms baseline_zero_of_original_rows
#print axioms packet_zero_of_original_rows
end QuantitativeMaass.RawPrepared
