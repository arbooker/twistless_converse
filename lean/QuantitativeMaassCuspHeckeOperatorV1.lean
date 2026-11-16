module

public import QuantitativeMaassAllCuspConstantV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix UpperHalfPlane
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticClassicalCusp AsymptoticClassicalDiscriminant AsymptoticClassicalPetersson
open scoped MatrixGroups BigOperators

namespace QuantitativeMaass

theorem cuspBranchGL_none_dilation (N p : ℕ) [Fact p.Prime] :
    cuspBranchGL N p none=dilationReal p (Fact.out : p.Prime).pos := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspBranchGL,cuspBranch,dilationReal,dilationGL,GeneralLinearGroup.map]

theorem cuspBranchGL_some_triangular (p : ℕ) [Fact p.Prime] (u : ZMod p) :
    cuspBranchGL 1 p (some u)=triangularGL 1 u.val p (by norm_num)
      (by exact_mod_cast (Fact.out : p.Prime).pos) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspBranchGL,cuspBranch,triangularGL]

/-- Reducing N*j modulo p changes the corresponding upper-triangular branch
only by an actual integral translation. -/
theorem cuspBranchGL_translate (N p : ℕ) [Fact p.Prime] (u : ZMod p) :
    cuspBranchGL N p (some u) =
      SpecialLinearGroup.mapGL ℝ (upperSL ((N*u.val/p : ℕ):ℤ)) *
        cuspBranchGL 1 p (some ((N:ZMod p)*u)) := by
  have hv : ((N:ZMod p)*u).val=(N*u.val)%p := by
    calc
      ((N:ZMod p)*u).val = (((N*u.val:ℕ):ZMod p)).val := by
        rw [Nat.cast_mul,ZMod.natCast_zmod_val]
      _ = _ := ZMod.val_natCast p (N*u.val)
  apply Units.ext
  change (cuspBranch N p (some u)).map (Int.castRingHom ℝ) =
    (upperSL ((N*u.val/p : ℕ):ℤ)).val.map (Int.castRingHom ℝ) *
      (cuspBranch 1 p (some ((N:ZMod p)*u))).map (Int.castRingHom ℝ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspBranch,upperSL,AsymptoticFreshCRT.upper,Matrix.mul_apply,Fin.sum_univ_two,hv]
  have hd := congrArg (fun t : ℤ => (t:ℝ))
    (Int.emod_add_mul_ediv ((N:ℤ)*(u.val:ℤ)) (p:ℤ))
  simpa [mul_comm] using hd.symm

/-- The modified branch sum equals the ordinary p+1 Hecke sum on every
actual level-N automorphic function; the residues are permuted, not counted
with a formal density assumption. -/
theorem cuspHeckeSum_eq_standard (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (f : ℍ → ℂ)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z)=f z) (z : ℍ) :
    cuspHeckeSum N p f z = f (dilationLabel p (Fact.out : p.Prime).pos • z) +
      ∑ a : Fin p, f (triangularGL 1 a.val p (by norm_num)
        (by exact_mod_cast (Fact.out : p.Prime).pos) • z) := by
  rw [cuspHeckeSum,Fintype.sum_option,cuspBranchGL_none_dilation]
  congr 1
  have ht (u : ZMod p) : f (cuspBranchGL N p (some u) • z)=
      f (cuspBranchGL 1 p (some ((N:ZMod p)*u)) • z) := by
    rw [cuspBranchGL_translate,mul_smul]
    have hmem : upperSL ((N*u.val/p:ℕ):ℤ) ∈ CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [upperSL,AsymptoticFreshCRT.upper]
    have hi := hinv ⟨integralLabel (upperSL ((N*u.val/p:ℕ):ℤ)),
      ⟨upperSL ((N*u.val/p:ℕ):ℤ),hmem,rfl⟩⟩
      (cuspBranchGL 1 p (some ((N:ZMod p)*u)) • z)
    rw [integralLabel_action] at hi
    exact hi
  simp_rw [ht]
  have he := Equiv.sum_comp (Equiv.mulLeft₀ (N:ZMod p) hNp)
    (fun u => f (cuspBranchGL 1 p (some u) • z))
  change (∑ u : ZMod p, f (cuspBranchGL 1 p (some ((N:ZMod p)*u)) • z)) =
    ∑ u : ZMod p, f (cuspBranchGL 1 p (some u) • z) at he
  rw [he]
  simp_rw [cuspBranchGL_some_triangular]
  rw [sum_zmod_val p (fun a => f (triangularGL 1 a p (by norm_num)
    (by exact_mod_cast (Fact.out : p.Prime).pos) • z))]
  exact (Fin.sum_univ_eq_sum_range (fun a => f (triangularGL 1 a p (by norm_num)
    (by exact_mod_cast (Fact.out : p.Prime).pos) • z)) p).symm

/-- The all-cusp correspondence is exactly the already constructed bounded
self-adjoint Hecke operator on every measurable automorphic L² representative. -/
theorem normalizedCuspHecke_eq_representative (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    normalizedCuspHecke N p f.val = (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val := by
  funext z
  rw [normalizedCuspHecke,cuspHeckeSum_eq_standard N p hNp f.val f.property.2.1,
    HeckeL2.heckeRepresentative_apply]
  rfl

#print axioms normalizedCuspHecke_eq_representative

end QuantitativeMaass
