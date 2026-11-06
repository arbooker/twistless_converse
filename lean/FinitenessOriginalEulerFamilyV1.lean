module

public import FinitenessEulerFamilyV1
public import FinitenessEulerIdentificationV1

set_option autoImplicit false

public section

namespace FinitenessOriginalEulerFamily

open FinitenessOriginalInput

/-- Independence of the literal original solution sequences, derived from
their infinite Euler products rather than assuming Hecke relations. -/
theorem independent (N k : ℕ) :
    LinearIndependent ℂ (fun f : S N k => f.val) := by
  classical
  apply FinitenessEulerFamily.independent _ (fun p => if p ∣ N then 0 else 1)
  · intro f
    exact f.property.zero
  · intro f
    exact (FinitenessEulerIdentification.solution_arithmetic f.property).1
  · intro f a b hc
    exact (FinitenessEulerIdentification.solution_arithmetic f.property).2.1 a b hc
  · intro f p hp j
    exact (FinitenessEulerIdentification.solution_arithmetic f.property).2.2 p hp j
  · intro f g he
    exact Subtype.ext he

#print axioms independent

end FinitenessOriginalEulerFamily
