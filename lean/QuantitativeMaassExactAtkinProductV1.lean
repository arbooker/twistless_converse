module

public import QuantitativeMaassExactAtkinChoiceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticRationalGroup AsymptoticRationalFreeness
open scoped MatrixGroups

namespace QuantitativeMaass

/-- Products at disjoint exact divisors have the exact matrix shape
of their product divisor, modulo a congruence transformation. -/
theorem exactAtkin_product_mod_gamma (D P Q : ℕ) (hP : 0<P) (hQ : 0<Q)
    (A B C E U V : ℤ)
    (hAB : (P:ℤ)*A+((Q*D:ℕ):ℤ)*B=1)
    (hCE : (Q:ℤ)*C+((P*D:ℕ):ℤ)*E=1)
    (hUV : ((P*Q:ℕ):ℤ)*U+(D:ℤ)*V=1) :
    ∃ a : gamma ((P*Q)*D),
      exactAtkinLabel (Q*D) P hP A B hAB*exactAtkinLabel (P*D) Q hQ C E hCE=
        a.val*exactAtkinLabel D (P*Q) (Nat.mul_pos hP hQ) U V hUV := by
  let x : ℤ := 1-(D:ℤ)*B
  let y : ℤ := (P:ℤ)*E+B*(Q:ℤ)*C
  let z : ℤ := -((Q:ℤ)+(P:ℤ)*A)
  let w : ℤ := A*C-(D:ℤ)*E
  have hxy : ((P*Q:ℕ):ℤ)*x*w-(D:ℤ)*y*z=1 := by
    calc
      _ = ((P:ℤ)*A+((Q*D:ℕ):ℤ)*B)*((Q:ℤ)*C+((P*D:ℕ):ℤ)*E) := by
        dsimp only [x,y,z,w]
        simp only [Nat.cast_mul]
        ring
      _ = 1 := by rw [hAB,hCE,one_mul]
  let a := exactAtkinComparison D (P*Q) U V x y z w hUV hxy
  have ha : a∈CongruenceSubgroup.Gamma0 ((P*Q)*D) :=
    exactAtkinComparison_mem D (P*Q) U V x y z w hUV hxy
  have hm : a.val*exactAtkinMatrix D (P*Q) U V=
      exactAtkinMatrix (Q*D) P A B*exactAtkinMatrix (P*D) Q C E := by
    rw [show a.val*exactAtkinMatrix D (P*Q) U V=
      !![((P*Q:ℕ):ℤ)*x,y;((P*Q:ℕ):ℤ)*D*z,((P*Q:ℕ):ℤ)*w] from
        exactAtkinComparison_mul D (P*Q) U V x y z w hUV hxy]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [exactAtkinMatrix,Matrix.mul_apply,Fin.sum_univ_two,x,y,z,w]
    all_goals ring
  refine ⟨⟨integralLabel a,⟨a,ha,rfl⟩⟩,?_⟩
  symm
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (rationalGL a)*rationalMap (exactAtkinGL D (P*Q) (Nat.mul_pos hP hQ) U V hUV)=
    rationalMap (exactAtkinGL (Q*D) P hP A B hAB)*rationalMap (exactAtkinGL (P*D) Q hQ C E hCE)
  rw [←map_mul,←map_mul]
  apply congrArg rationalMap
  apply Units.ext
  change (a.val.map (fun n : ℤ => (n:ℚ)))*
    ((exactAtkinMatrix D (P*Q) U V).map (fun n : ℤ => (n:ℚ)))=
      ((exactAtkinMatrix (Q*D) P A B).map (fun n : ℤ => (n:ℚ)))*
      ((exactAtkinMatrix (P*D) Q C E).map (fun n : ℤ => (n:ℚ)))
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => (M i j:ℚ)) hm
  simpa only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map_apply,Int.cast_add,Int.cast_mul] using hh

#print axioms exactAtkin_product_mod_gamma

end QuantitativeMaass
