module

public import QuantitativeEulerOldProjectionEnergyV1
public import AsymptoticSlashGaugeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionCocycle

open AsymptoticNestedQuotients QuantitativeEulerOldProjectionPhysical
open scoped lp

variable {G α : Type*} [Group G] [MulAction G α]

/-- A genuine unitary multiplier cocycle, including the actual even-weight
projective slash phase. Its axioms are algebraic, not spectral-gap premises. -/
structure Phase where
  value : G → α → ℂ
  one : ∀ x, value 1 x = 1
  mul : ∀ g h x, value (g*h) x = value g (h • x) * value h x
  norm : ∀ g x, ‖value g x‖ = 1

def slashPhase (S : Subgroup AsymptoticRationalGroup.Group) (m : ℕ) :
    Phase (G := S) (α := UpperHalfPlane) where
  value g x := AsymptoticSlashGauge.phase g.val m x
  one := AsymptoticSlashGauge.phase_one m
  mul g h x := AsymptoticSlashGauge.phase_mul g.val h.val m x
  norm g x := AsymptoticSlashGauge.phase_norm g.val m x

variable (c : Phase (G := G) (α := α)) (H : Subgroup G)
    (f : α → ℂ) (hf : ∀ h : H, ∀ x, c.value h.val x * f (h.val • x) = f x)

/-- Gauge the values at one orbit root before passing to finite cosets. -/
def rooted (x : α) (g : G) : ℂ := c.value g x * f (g • x)

include hf in
theorem rooted_invariant (x : α) (h : H) (g : G) :
    rooted c f x (h.val * g) = rooted c f x g := by
  rw [rooted, c.mul, mul_smul]
  calc
    _ = c.value g x * (c.value h.val (g • x) * f (h.val • (g • x))) := by ring
    _ = _ := by rw [hf]; rfl

theorem rooted_norm (x : α) (g : G) : ‖rooted c f x g‖ = ‖f (g • x)‖ := by
  rw [rooted, norm_mul, c.norm, one_mul]

include hf in
theorem norm_invariant (h : H) (x : α) : ‖f (h.val • x)‖ = ‖f x‖ := by
  have he := congrArg norm (hf h x)
  simpa only [norm_mul, c.norm, one_mul] using he

variable [H.FiniteIndex]

local instance : Finite (Classes H) := Finite.of_equiv (G ⧸ H)
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
local instance : Fintype (Classes H) := Fintype.ofFinite _
local instance : Fintype (G ⧸ H) := Fintype.ofFinite _

/-- The finite phase-corrected orbit vector. The finite-index hypothesis
makes every vector genuine ℓ², without sampling an infinite orbit. -/
def vector (x : α) : ℓ²(Classes H,ℂ) :=
  orbitVector H (rooted c f x) (rooted_invariant c H f hf x) 1

theorem vector_classOf (x : α) (g : G) :
    vector c H f hf x (classOf H g) = c.value g x * f (g • x) := by
  rw [vector, orbitVector_classOf]
  change rooted c f x (g*1) = _
  rw [mul_one]
  rfl

/-- The unit cocycle contributes no energy factor, uniformly in the weight. -/
theorem vector_norm_sq (x : α) :
    ‖vector c H f hf x‖^2 = ∑ q : G ⧸ H, ‖f (q.out⁻¹ • x)‖^2 := by
  rw [vector, orbitVector_norm_sq]
  apply Finset.sum_congr rfl
  intro q _
  change ‖rooted c f x (q.out⁻¹*1)‖^2 = _
  rw [mul_one, rooted_norm]

/-- Re-rooting has exactly one scalar unit phase, with no weight growth. -/
theorem vector_translate (g : G) (x : α) (q : Classes H) :
    c.value g x * vector c H f hf (g • x) q =
      vector c H f hf x (AsymptoticNestedQuotients.rightMulEquiv H g q) := by
  induction q using Quotient.inductionOn with
  | h a =>
    change c.value g x * vector c H f hf (g • x) (classOf H a) =
      vector c H f hf x (AsymptoticNestedQuotients.rightMulEquiv H g (classOf H a))
    rw [AsymptoticNestedQuotients.rightMulEquiv_classOf,
      vector_classOf, vector_classOf, c.mul, mul_smul]
    ring

#print axioms slashPhase
#print axioms vector_norm_sq
#print axioms vector_translate
end QuantitativeEulerOldProjectionCocycle
