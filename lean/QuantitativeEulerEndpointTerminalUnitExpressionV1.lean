module

public import QuantitativeEulerEndpointCornerAmbientV1
public import QuantitativeEulerEndpointNestedFiniteV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointTerminalExpression
open FinitenessCertificate FinitenessGlobalHeight AsymptoticFiniteBranch QuantitativeHolomorphic
open QuantitativeEulerEndpointTerminalAlgebra Polynomial MeasureTheory

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The finite branch identity on the ENTIRE terminal source. -/
def unit : Expression := [AsymptoticFiniteBranch.corner (terminalRegion A P) (terminal_measurable A P)]

theorem unit_mass : expressionBound (unit A P)=1 := by
  simp [unit,expressionBound,AsymptoticFiniteBranch.corner]

theorem unit_matrix : ExpressionMatrixBound (unit A P) 1 := by
  intro b hb
  have hb' : b=AsymptoticFiniteBranch.corner (terminalRegion A P) (terminal_measurable A P) := by
    simpa only [unit,List.mem_singleton] using hb
  subst b
  refine ⟨1,integerAction_one,?_⟩
  intro i j
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem unit_regular (x : UpperHalfPlane) : regularSum (unit A P) x=rep A P 1 x := by
  simp only [unit,regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,regular_corner]
  rfl

theorem unit_physical (m : ℕ) : holomorphicSum (unit A P) m=
    AsymptoticRegionL2.projection (volume : Measure UpperHalfPlane) (terminalRegion A P) (terminal_measurable A P) := by
  simp only [unit,holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,holomorphic_corner]

theorem unit_regular_projection (x : UpperHalfPlane) : IsStarProjection (regularSum (unit A P) x) := by
  rw [unit_regular,rep_one]
  exact isStarProjection_starProjection

theorem unit_physical_projection (m : ℕ) : IsStarProjection (holomorphicSum (unit A P) m) := by
  constructor
  · change holomorphicSum (unit A P) m*holomorphicSum (unit A P) m=holomorphicSum (unit A P) m
    rw [unit_physical]
    apply ContinuousLinearMap.ext
    exact AsymptoticRegionL2.projection_idempotent _ _ _
  · change star (holomorphicSum (unit A P) m)=holomorphicSum (unit A P) m
    rw [unit_physical]
    exact AsymptoticRegionL2.projection_adjoint _ _ _

theorem unit_regular_order (x : UpperHalfPlane) :
    0≤regularSum (unit A P) x ∧ regularSum (unit A P) x≤1 := by
  have hp := unit_regular_projection A P x
  have hn : ‖regularSum (unit A P) x‖≤1 := (regularSum_norm_le _ _).trans (unit_mass A P).le
  have hz := star_mul_self_nonneg (regularSum (unit A P) x)
  rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at hz
  exact ⟨hz,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hz).mp hn⟩

theorem unit_physical_order (m : ℕ) :
    0≤holomorphicSum (unit A P) m ∧ holomorphicSum (unit A P) m≤1 := by
  have hp := unit_physical_projection A P m
  have hn : ‖holomorphicSum (unit A P) m‖≤1 := (holomorphicSum_norm_le _ _).trans (unit_mass A P).le
  have hz := star_mul_self_nonneg (holomorphicSum (unit A P) m)
  rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at hz
  exact ⟨hz,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hz).mp hn⟩

theorem rep_support (a : Algebra A P) (x : UpperHalfPlane) :
    rep A P 1 x*rep A P a x=rep A P a x ∧ rep A P a x*rep A P 1 x=rep A P a x := by
  change rep A P (1*a) x=rep A P a x ∧ rep A P (a*1) x=rep A P a x
  simp only [one_mul,mul_one,and_self]

theorem rep_order (a : Algebra A P) (ha : 0≤a ∧ a≤1) (x : UpperHalfPlane) :
    0≤rep A P a x ∧ rep A P a x≤1 := by
  have h0 := (QuantitativeSpectralRegularOrder.pointwise_le_iff _ _ _ 0 a).mpr ha.1 x
  have h1 := (QuantitativeSpectralRegularOrder.pointwise_le_iff _ _ _ a 1).mpr ha.2 x
  change 0≤rep A P a x at h0
  change rep A P a x≤rep A P 1 x at h1
  have hu := (unit_regular_order A P x).2
  rw [unit_regular] at hu
  exact ⟨h0,h1.trans hu⟩

theorem rep_sharpened_ambient (a g : Algebra A P) (d : ℕ) (q : ℝ[X]) (hq : q.eval 0=0)
    (x : UpperHalfPlane) :
    rep A P (aeval (QuantitativeEulerEndpointSoftUpdate.update a (a*g*a) d) q) x=
      aeval (QuantitativeEulerEndpointSoftUpdate.update (rep A P a x)
        (rep A P a x*rep A P g x*rep A P a x) d) q := by
  rw [rep_aeval,rep_update]
  have hp : IsStarProjection (rep A P 1 x) := by simpa only [unit_regular] using unit_regular_projection A P x
  exact QuantitativeEulerEndpointCornerAmbient.corner_sharpened_eq _ _ _ hp.isIdempotentElem.eq
    (rep_support A P a x).1 (rep_support A P a x).2 d q hq

#print axioms unit_matrix
#print axioms unit_regular_projection
#print axioms unit_physical_projection
#print axioms rep_order
#print axioms rep_sharpened_ambient
end QuantitativeEulerEndpointTerminalExpression
