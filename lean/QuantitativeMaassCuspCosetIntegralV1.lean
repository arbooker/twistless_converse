module

public import QuantitativeMaassCuspCosetReductionV1
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix
open scoped Matrix MatrixGroups

namespace QuantitativeMaass

/-- Integral unramified representatives whose reductions modulo N are all
identity when p is 1 modulo N. -/
def cuspBranch (N p : ℕ) (j : Option (ZMod p)) : Matrix (Fin 2) (Fin 2) ℤ :=
  match j with
  | none => !![(p:ℤ),0;0,1]
  | some u => !![1,(N:ℤ)*u.val;0,(p:ℤ)]

theorem cuspBranch_det (N p : ℕ) (j : Option (ZMod p)) : (cuspBranch N p j).det = p := by
  cases j <;> simp [cuspBranch, Matrix.det_fin_two]

theorem cuspBranch_adjugate_mod (N p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) :
    (cuspBranch N p j).adjugate.map (Int.castRingHom (ZMod p)) = cuspAdjMod (N : ZMod p) j := by
  cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [cuspBranch,cuspAdjMod,Matrix.adjugate_fin_two,Matrix.map_apply]

theorem cuspBranch_mod_level (N p : ℕ) (hpN : (p : ZMod N)=1) (j : Option (ZMod p)) :
    (cuspBranch N p j).map (Int.castRingHom (ZMod N)) = 1 := by
  cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [cuspBranch,Matrix.map_apply,hpN]

/-- Division of the adjugate product produces an actual integral
unimodular left quotient; this is not a prescribed coset relation. -/
theorem exists_integral_left_quotient (p : ℕ) (hp : p≠0)
    (M C : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det=p) (hC : C.det=p)
    (hdiv : ∀ i j, (p:ℤ) ∣ (M*C.adjugate) i j) :
    ∃ γ : SL(2,ℤ), M=γ.val*C ∧ (p:ℤ) • γ.val=M*C.adjugate := by
  let Q : Matrix (Fin 2) (Fin 2) ℤ := (M*C.adjugate).map (fun x => x/(p:ℤ))
  have hpZ : (p:ℤ)≠0 := by exact_mod_cast hp
  have he : (p:ℤ) • Q=M*C.adjugate := by
    ext i j
    change (p:ℤ) * ((M*C.adjugate) i j / (p:ℤ)) = (M*C.adjugate) i j
    exact Int.mul_ediv_cancel' (hdiv i j)
  have hQ : Q.det=1 := by
    have hd := congrArg Matrix.det he
    rw [Matrix.det_smul,Matrix.det_mul,Matrix.det_adjugate,hM,hC] at hd
    simp only [Fintype.card_fin, Nat.add_one_sub_one, pow_one] at hd
    apply mul_left_cancel₀ (pow_ne_zero 2 hpZ)
    linear_combination hd
  refine ⟨⟨Q,hQ⟩,?_,he⟩
  have hm := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A*C) he
  rw [smul_mul_assoc,mul_assoc,Matrix.adjugate_mul,hC,mul_smul_comm,mul_one] at hm
  ext i j
  have hij := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A i j) hm
  exact (mul_left_cancel₀ hpZ hij).symm

/-- The quotient is also the identity modulo N whenever both original
matrices and p have that reduction. -/
theorem left_quotient_mod_level (N p : ℕ) (hpN : (p : ZMod N)=1)
    (M C : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.map (Int.castRingHom (ZMod N))=1)
    (hC : C.map (Int.castRingHom (ZMod N))=1) (γ : SL(2,ℤ))
    (he : (p:ℤ) • γ.val=M*C.adjugate) :
    γ.val.map (Int.castRingHom (ZMod N))=1 := by
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (Int.castRingHom (ZMod N))) he
  have hs : ((p:ℤ) • γ.val).map (Int.castRingHom (ZMod N)) =
      (p : ZMod N) • γ.val.map (Int.castRingHom (ZMod N)) := by
    ext i j
    change (((p:ℤ) * γ.val i j : ℤ) : ZMod N) =
      (p:ZMod N) * (γ.val i j : ZMod N)
    simp
  have ha : C.adjugate.map (Int.castRingHom (ZMod N)) =
      (C.map (Int.castRingHom (ZMod N))).adjugate := (Int.castRingHom (ZMod N)).map_adjugate C
  rw [hs,Matrix.map_mul,ha,hM,hC] at hh
  simpa [hpN] using hh

#print axioms exists_integral_left_quotient
#print axioms left_quotient_mod_level

end QuantitativeMaass
