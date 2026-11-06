module

public import Mathlib.GroupTheory.OrderOfElement
public import QuantitativeArithmeticSmallLevelCircBadSemisimpleV1
public import QuantitativeArithmeticSmallLevelCircCuspSemisimpleV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelCirc.SpectralAlgebra. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelCircPermutationV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.SpectralAlgebra

/-- Pullback of functions by an actual finite permutation. -/
def permutationOperator {X : Type*} (P : Equiv.Perm X) : Module.End ℂ (X → ℂ) where
  toFun f x := f (P x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem permutationOperator_pow {X : Type*} (P : Equiv.Perm X) (n : ℕ)
    (f : X → ℂ) (x : X) : (permutationOperator P ^ n) f x = f ((P ^ n) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (permutationOperator P ^ n) f (P x) = _
    rw [ih, pow_succ]
    rfl

theorem permutationOperator_isSemisimple {X : Type*} [Finite X] (P : Equiv.Perm X) :
    Module.End.IsSemisimple (permutationOperator P) := by
  classical
  let n := orderOf P
  have hn : 0 < n := orderOf_pos P
  have hpow : permutationOperator P ^ n = 1 := by
    apply LinearMap.ext
    intro f
    funext x
    rw [permutationOperator_pow]
    change f ((P ^ orderOf P) x) = f x
    rw [pow_orderOf_eq_one]
    rfl
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((Polynomial.separable_X_pow_sub_C (n := n) (1 : ℂ)
      (by exact_mod_cast hn.ne') one_ne_zero).squarefree)
  simp only [map_sub, map_pow, Polynomial.aeval_X,
    map_one, hpow, sub_self]

/-- The boundary Hecke model is semisimple even for arbitrary complex
weights: both summands are commuting finite-order permutation operators. -/
theorem permutation_sum_isSemisimple {X : Type*} [Finite X]
    (P : Equiv.Perm X) (c : ℂ) :
    Module.End.IsSemisimple (permutationOperator P + c • permutationOperator P.symm) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  apply Module.End.IsSemisimple.add_of_commute
  · apply LinearMap.ext
    intro f
    funext x
    change c * f (P.symm (P x)) = c * f (P (P.symm x))
    simp
  · exact permutationOperator_isSemisimple P
  · exact Module.End.IsSemisimple_smul c (permutationOperator_isSemisimple P.symm)

#print axioms permutationOperator_isSemisimple
#print axioms permutation_sum_isSemisimple
end QuantitativeArithmeticSmallLevelCirc.SpectralAlgebra
end
end

/-! ## QuantitativeArithmeticSmallLevelCircSpectralGlueV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.SpectralAlgebra

variable {E F G : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]

/-- An actual intertwining map respects the polynomial module structures. -/
def intertwiningPolynomialMap (T : Module.End ℂ E) (S : Module.End ℂ F)
    (L : E →ₗ[ℂ] F) (hL : ∀ x, L (T x) = S (L x)) :
    Module.AEval' T →ₗ[Polynomial ℂ] Module.AEval' S :=
  LinearMap.ofAEval T ((Module.AEval.of ℂ F S).toLinearMap.comp L) (fun x => by
    change Module.AEval.of ℂ F S (L (T x)) =
      Polynomial.X • Module.AEval.of ℂ F S (L x)
    rw [Module.AEval.X_smul_of]
    exact congrArg (Module.AEval.of ℂ F S) (hL x))

/-- Semisimplicity descends to a subspace through an injective intertwiner. -/
theorem semisimple_of_injective_intertwiner (T : Module.End ℂ E)
    (S : Module.End ℂ F) (L : E →ₗ[ℂ] F)
    (hL : ∀ x, L (T x) = S (L x)) (hLI : Function.Injective L)
    (hS : Module.End.IsSemisimple S) : Module.End.IsSemisimple T := by
  let : IsSemisimpleModule (Polynomial ℂ) (Module.AEval' S) := hS
  exact IsSemisimpleModule.of_injective (intertwiningPolynomialMap T S L hL) hLI

/-- Two invariant semisimple images spanning the space suffice. No
orthogonality or choice of their eigenbases is required. -/
theorem semisimple_of_spanning_images (T : Module.End ℂ E)
    (S : Module.End ℂ F) (U : Module.End ℂ G)
    (L : F →ₗ[ℂ] E) (J : G →ₗ[ℂ] E)
    (hL : ∀ x, L (S x) = T (L x)) (hJ : ∀ x, J (U x) = T (J x))
    (hspan : ∀ v, ∃ x y, L x + J y = v)
    (hS : Module.End.IsSemisimple S) (hU : Module.End.IsSemisimple U) :
    Module.End.IsSemisimple T := by
  let : IsSemisimpleModule (Polynomial ℂ) (Module.AEval' S) := hS
  let : IsSemisimpleModule (Polynomial ℂ) (Module.AEval' U) := hU
  let l := intertwiningPolynomialMap S T L hL
  let j := intertwiningPolynomialMap U T J hJ
  have htop : l.range ⊔ j.range = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨x,y,hxy⟩ := hspan ((Module.AEval.of ℂ E T).symm v)
    have he : l (Module.AEval.of ℂ F S x) + j (Module.AEval.of ℂ G U y) = v := hxy
    rw [← he]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self l _)
      (LinearMap.mem_range_self j _)
  have hh := (IsSemisimpleModule.range l).sup (IsSemisimpleModule.range j)
  rw [htop] at hh
  let := hh
  exact IsSemisimpleModule.congr (Submodule.topEquiv.symm)

#print axioms semisimple_of_injective_intertwiner
#print axioms semisimple_of_spanning_images
end QuantitativeArithmeticSmallLevelCirc.SpectralAlgebra
end
end
