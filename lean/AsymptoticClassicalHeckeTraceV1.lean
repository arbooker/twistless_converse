module

public import AsymptoticClassicalDegeneracyV1
public import AsymptoticClassicalTraceAdjointV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct ComplexConjugate

variable (N : ℕ) [NeZero N] (p : ℕ) (hp : 0 < p) (k : ℤ)

/-- The actual trace of the slash translate by diag(p,1). At a prime
 coprime to N, this is the usual unnormalized classical Hecke operator. -/
def dilationTrace : CuspForm (level N) k →ₗ[ℂ] CuspForm (level N) k := by
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  exact (p : ℂ) ^ (k - 1) •
    (arithmeticTrace (level (p * N)) (level N) k).comp (degeneracy N p hp k)

@[simp] theorem dilationTrace_apply (f : CuspForm (level N) k) :
    dilationTrace N p hp k f = (p : ℂ) ^ (k - 1) •
      (by
        let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
        exact arithmeticTrace (level (p * N)) (level N) k (degeneracy N p hp k f)) := rfl

/-- Unfolding the Petersson pairing converts the Hecke correspondence
 into the two genuine degeneracy directions at level p*N. -/
theorem dilationTrace_inner (f g : CuspForm (level N) k) :
    inner ℂ (dilationTrace N p hp k f) g =
      (p : ℂ) ^ (k - 1) *
        (by
          let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
          exact inner ℂ (degeneracy N p hp k f)
            (restrict k (level_antitone (show N ∣ p * N from dvd_mul_left N p)) g)) := by
  let : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne N)⟩
  rw [dilationTrace_apply, inner_smul_left,
    trace_adjoint (p * N) N k (dvd_mul_left N p)]
  simp

#print axioms dilationTrace_apply
#print axioms dilationTrace_inner

end AsymptoticClassicalCusp
