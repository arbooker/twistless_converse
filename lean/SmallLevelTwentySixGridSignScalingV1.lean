module
public import SmallLevelTwentySixGridSignScalingParityV1
public import SmallLevelTwentySixGridLaurentRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex

theorem monomial_scale (e : ℤ×ℤ×ℤ×ℤ) (X Y Z W u v : ℂ) :
    SmallLevelFourPrimeRates.monomial e (u*X) Y (v*Z) W=
      (u^e.1*v^e.2.2.1)*SmallLevelFourPrimeRates.monomial e X Y Z W := by
  simp only [SmallLevelFourPrimeRates.monomial,mul_zpow]
  ring

theorem hecke_scale_sign (X Y Z W c a b u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (w : Fin 780→ℂ) (i : Fin 51) :
    laurentHecke (u*X) Y (v*Z) W (-1) c a b w i=
      laurentHecke X Y Z W (-u) (c*v) a b w i := by
  have hp : gridHeckeP i=2 ∨ gridHeckeP i=3 ∨ gridHeckeP i=13 ∨ gridHeckeP i=5 := by
    fin_cases i <;> decide
  rcases hp with hp|hp|hp|hp <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    simp [laurentHecke,hp,primeParameter,primeEigenvalue] <;> ring_nf <;> simp_all

/-- All original leading-row types respect the same sign rescaling.
Taking c=-1 or c=1 reduces the eight physical sign choices to two bases. -/
theorem laurentRows_sign_scale (X Y Z W c a b u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (w : Fin 780→ℂ) (i : GridSource) :
    laurentRows (u*X) Y (v*Z) W (-1) (-1) c a b w i=
      laurentRows X Y Z W (-u*v) (-u) (c*v) a b w i := by
  cases i with
  | word i =>
    simp only [laurentRows,neg_neg,monomial_scale]
    rw [←word_scale_sign i u v hu hv]
    ring
  | taylor i =>
    simp only [laurentRows,neg_neg,ite_self,one_mul,monomial_scale]
    rw [←taylor_scale_sign i c u v hu hv]
    ring
  | entire i => rfl
  | infinity i => rfl
  | hecke i => exact hecke_scale_sign X Y Z W c a b u v hu hv w i

#print axioms laurentRows_sign_scale
end SmallLevelTwentySixGrid
