module

public import QuantitativeArithmeticSmallLevelCircBoundarySplitV1
public import QuantitativeArithmeticSmallLevelCircJointBasisV1
public import AsymptoticClassicalHeckeSymmetryV1
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.CuspSpectral
open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalPetersson
open scoped InnerProduct

/-- Petersson symmetry gives invariant orthogonal complements and hence
algebraic semisimplicity, without choosing an eigenbasis. -/
theorem symmetric_isSemisimple {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : Module.End ℂ E) (hT : T.IsSymmetric) : Module.End.IsSemisimple T := by
  apply Module.End.isSemisimple_iff.mpr
  intro P hP
  refine ⟨Pᗮ, ?_, P.isCompl_orthogonal⟩
  intro v hv
  change T v ∈ Pᗮ
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro w hw
  rw [← hT]
  exact hv _ (hP hw)

theorem cusp_goodHecke_isSemisimple (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) (k : ℤ) :
    Module.End.IsSemisimple (dilationTrace N p hp.pos k) := by
  have hc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
  have hAB : (p : ℤ) * Nat.gcdA p N + (N : ℤ) * Nat.gcdB p N = 1 := by
    have hh := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one, Nat.cast_one] at hh
    exact hh.symm
  exact symmetric_isSemisimple _
    (dilationTrace_isSymmetric N p hp.pos k (Nat.gcdA p N) (Nat.gcdB p N) hAB)

theorem cuspCorner_goodHecke_invariant (N p k : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    cuspCorner N k hN ∈ Module.End.invtSubmodule (dilationTrace N p hp.pos (k : ℤ)) := by
  intro f hf
  change CuspForm.toModularFormₗ (dilationTrace N p hp.pos (k : ℤ) f) ∈ space N hN k
  rw [← dilationTrace_toModular]
  have ht := primeHecke_mem_space N p k hN hp hpN (CuspForm.toModularFormₗ f) hf
  simpa only [ModularHecke.primeHecke, hpN, ite_false] using ht

/-- Actual good Hecke operator on the cuspidal corner of full Mcirc. -/
def cuspCornerHecke (N p k : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Module.End ℂ (cuspCorner N k hN) :=
  (dilationTrace N p hp.pos (k : ℤ)).restrict
    (cuspCorner_goodHecke_invariant N p k hN hp hpN)

theorem cuspCornerHecke_isSemisimple (N p k : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Module.End.IsSemisimple (cuspCornerHecke N p k hN hp hpN) :=
  (cusp_goodHecke_isSemisimple N p hp hpN (k : ℤ)).restrict
    (cuspCorner_goodHecke_invariant N p k hN hp hpN)

def cuspCornerInclusion (N k : ℕ) [NeZero N] (hN : 0 < N) :
    cuspCorner N k hN →ₗ[ℂ] space N hN k :=
  (CuspForm.toModularFormₗ.comp (cuspCorner N k hN).subtype).codRestrict
    (space N hN k) (fun f => f.property)

theorem cuspCornerInclusion_injective (N k : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Injective (cuspCornerInclusion N k hN) := by
  intro f g h
  apply Subtype.ext
  apply DFunLike.coe_injective
  exact congrArg (fun F : space N hN k => (F.val : ℍ → ℂ)) h

theorem cuspCornerInclusion_intertwine (N k : ℕ) [NeZero N] (hN : 0 < N)
    (hk : Even k) (p : Nat.Primes) (hpN : ¬ p.val ∣ N)
    (f : cuspCorner N k hN) :
    allHecke N k hN hk p (cuspCornerInclusion N k hN f) =
      cuspCornerInclusion N k hN (cuspCornerHecke N p.val k hN p.property hpN f) := by
  apply Subtype.ext
  change ModularHecke.primeHecke N p.val p.property (k : ℤ)
    (CuspForm.toModularFormₗ f.val) = _
  simp only [ModularHecke.primeHecke, hpN, ite_false]
  exact dilationTrace_toModular N p.val p.property.pos (k : ℤ) f.val

#print axioms symmetric_isSemisimple
#print axioms cuspCornerHecke_isSemisimple
#print axioms cuspCornerInclusion_intertwine
end QuantitativeArithmeticSmallLevelCirc.CuspSpectral
