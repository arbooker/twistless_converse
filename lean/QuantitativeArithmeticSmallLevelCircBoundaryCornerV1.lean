module

public import QuantitativeArithmeticSmallLevelCircSpectralAlgebraTheoryV4
public import QuantitativeArithmeticSmallLevelEisensteinTheoryV4
public import QuantitativeArithmeticSmallLevelEisensteinBoundaryFiniteV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.CuspSpectral
open UpperHalfPlane AsymptoticClassicalCusp
open QuantitativeArithmeticSmallLevelEisenstein

/-- The actual boundary spectral summand, inside full Mcirc. -/
def boundaryCorner (N m : ℕ) [NeZero N] (hN : 0 < N) (p : Nat.Primes) :
    Submodule ℂ (space N hN (2 * m)) :=
  Module.End.eigenspace (allHecke N (2 * m) hN (even_two_mul m) p)
    (1 + (p.val : ℂ)^(2 * m - 1))

theorem boundaryCorner_eigen (N m : ℕ) [NeZero N] (hN : 0 < N)
    (p : Nat.Primes) (hpN : ¬ p.val ∣ N) (E : boundaryCorner N m hN p) :
    ModularHecke.dilationTrace N p.val p.property.pos ((2 * m : ℕ) : ℤ) E.val.val =
      (1 + (p.val : ℂ)^(2 * m - 1)) • E.val.val := by
  have he := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp E.property)
  change ModularHecke.primeHecke N p.val p.property _ E.val.val = _ at he
  simpa only [ModularHecke.primeHecke, hpN, ite_false, Submodule.coe_smul] using he

theorem boundaryCorner_invariant (N m : ℕ) [NeZero N] (hN : 0 < N)
    (p q : Nat.Primes) :
    boundaryCorner N m hN p ∈
      Module.End.invtSubmodule (allHecke N (2 * m) hN (even_two_mul m) q) := by
  intro E hE
  apply Module.End.mem_eigenspace_iff.mpr
  change allHecke N (2 * m) hN (even_two_mul m) p
    (allHecke N (2 * m) hN (even_two_mul m) q E) = _
  rw [allHecke_commute N (2 * m) hN (even_two_mul m) p q,
    Module.End.mem_eigenspace_iff.mp hE, map_smul]

def boundaryCornerHecke (N m : ℕ) [NeZero N] (hN : 0 < N)
    (p q : Nat.Primes) : Module.End ℂ (boundaryCorner N m hN p) :=
  (allHecke N (2 * m) hN (even_two_mul m) q).restrict
    (boundaryCorner_invariant N m hN p q)

def boundaryCornerMap (N m : ℕ) [NeZero N] (hN : 0 < N) (p : Nat.Primes) :
    boundaryCorner N m hN p →ₗ[ℂ] (boundaryLabels N → ℂ) :=
  ((finiteCuspBoundary (level N) ((2 * m : ℕ) : ℤ) N).comp
    (space N hN (2 * m)).subtype).comp (boundaryCorner N m hN p).subtype

/-- The boundary restriction on the spectral complement is injective,
including weight two, by the actual cusp spectral exclusion. -/
theorem boundaryCornerMap_injective (N m : ℕ) [NeZero N] (hN : 0 < N)
    (p : Nat.Primes) (hpN : ¬ p.val ∣ N) (hm : 0 < m) :
    Function.Injective (boundaryCornerMap N m hN p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro E hE
  have hzero : finiteCuspBoundary (level N) ((2 * m : ℕ) : ℤ) N E.val.val = 0 := hE
  have hc : E.val.val ∈ ModularForm.cuspFormSubmodule (level N) ((2 * m : ℕ) : ℤ) := by
    rw [← finiteCuspBoundary_ker (level N) ((2 * m : ℕ) : ℤ) N
      (level_contains_principal N)]
    exact hzero
  obtain ⟨G,hG⟩ := hc
  have he := boundaryCorner_eigen N m hN p hpN E
  rw [← hG, dilationTrace_toModular] at he
  have hg : dilationTrace N p.val p.property.pos ((2 * m : ℕ) : ℤ) G =
      (1 + (p.val : ℂ)^(2 * m - 1)) • G := by
    apply DFunLike.coe_injective
    exact congrArg (fun H : ModularForm (level N) ((2 * m : ℕ) : ℤ) => (H : ℍ → ℂ)) he
  have hz := boundary_eigen_zero N p.val m hN p.property hpN hm G hg
  apply Subtype.ext
  apply Subtype.ext
  rw [← hG, hz, map_zero]
  rfl

theorem cusp_boundary_spanning (N m : ℕ) [NeZero N] (hN : 0 < N)
    (p : Nat.Primes) (hpN : ¬ p.val ∣ N) (hpmod : (p.val : ZMod N) = 1)
    (hm : 0 < m) (F : space N hN (2 * m)) :
    ∃ G : cuspCorner N (2 * m) hN, ∃ E : boundaryCorner N m hN p,
      cuspCornerInclusion N (2 * m) hN G + E.val = F := by
  obtain ⟨G,E,hGE,hE⟩ := circ_boundary_split N p.val m hN p.property hpN hpmod hm F
  have he : E ∈ boundaryCorner N m hN p := by
    apply Module.End.mem_eigenspace_iff.mpr
    apply Subtype.ext
    change ModularHecke.primeHecke N p.val p.property _ E.val = _
    simpa only [ModularHecke.primeHecke, hpN, ite_false, Submodule.coe_smul] using hE
  exact ⟨G,⟨E,he⟩,Subtype.ext hGE.symm⟩

#print axioms boundaryCorner_invariant
#print axioms boundaryCornerMap_injective
#print axioms cusp_boundary_spanning
end QuantitativeArithmeticSmallLevelCirc.CuspSpectral
