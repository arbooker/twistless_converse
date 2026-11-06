module

public import AsymptoticRamifiedOldBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRamifiedTwistedLaw

open AsymptoticRationalGroup AsymptoticIntegralSubgroup AsymptoticCongruenceLabels
open AsymptoticFreshMatrices AsymptoticOrbitDecode

/-- The full finite translation sum, before deleting the zero residue. -/
noncomputable def residueSum (p : ℕ) (F : AsymptoticRationalGroup.Group → ℂ)
    (g : AsymptoticRationalGroup.Group) : ℂ :=
  ∑ a : Fin p,F (translationLabel ((a.val:ℚ)/p)*g)

/-- At prime p this is the Ramanujan translation operator C_p. -/
noncomputable def puncturedSum (p : ℕ) (F : AsymptoticRationalGroup.Group → ℂ)
    (g : AsymptoticRationalGroup.Group) : ℂ := residueSum p F g-F g

theorem residueSum_of_ramified (p : ℕ) (hp : 0<p) (F : AsymptoticRationalGroup.Group → ℂ)
    (δ : ℂ) (hU : ∀ g,∑ a : Fin p,F (ramifiedLabel p hp a*g)=δ*F g)
    (g : AsymptoticRationalGroup.Group) : residueSum p F g=δ*F (dilationLabel p hp*g) := by
  simpa only [residueSum,← mul_assoc,ramifiedLabel_mul_dilation] using hU (dilationLabel p hp*g)

theorem dilation_mul_fricke (N p : ℕ) (hN : 0<N) (hp : 0<p) :
    dilationLabel p hp*frickeLabel (p*N) (Nat.mul_pos hp hN)=frickeLabel N hN := by
  rw [← inv_dilation_mul_fricke N p hN hp,mul_inv_cancel_left]

theorem reverse_fricke_equation (N : ℕ) (hN : 0<N) (F : AsymptoticRationalGroup.Group → ℂ)
    (w : ℂ) (hW : ∀ g,w*F (frickeLabel N hN*g)=F g)
    (g : AsymptoticRationalGroup.Group) : F (frickeLabel N hN*g)=w*F g := by
  have he := hW (frickeLabel N hN*g)
  simpa only [← mul_assoc,frickeLabel_mul_self,one_mul] using he.symm

/-- The ramified twisted Fricke relation follows from the two original
incidence equations. No extra twist observation is assumed. -/
theorem punctured_fricke (N p : ℕ) (hN : 0<N) (hp : 0<p)
    (F : AsymptoticRationalGroup.Group → ℂ) (w δ : ℂ) (hδ : δ^2=1)
    (hW : ∀ g,w*F (frickeLabel N hN*g)=F g)
    (hU : ∀ g,∑ a : Fin p,F (ramifiedLabel p hp a*g)=δ*F g)
    (g : AsymptoticRationalGroup.Group) :
    puncturedSum p F (frickeLabel (p*N) (Nat.mul_pos hp hN)*g)=
      (-w*δ)*puncturedSum p F g := by
  rw [puncturedSum,puncturedSum,residueSum_of_ramified p hp F δ hU,
    residueSum_of_ramified p hp F δ hU,← mul_assoc,dilation_mul_fricke N p hN hp,
    ← fricke_mul_dilation N p hN hp,mul_assoc]
  rw [reverse_fricke_equation N hN F w hW,reverse_fricke_equation N hN F w hW]
  linear_combination w*F (dilationLabel p hp*g)*hδ

#print axioms residueSum_of_ramified
#print axioms dilation_mul_fricke
#print axioms reverse_fricke_equation
#print axioms punctured_fricke

end AsymptoticRamifiedTwistedLaw
