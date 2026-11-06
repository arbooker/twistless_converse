module

public import AsymptoticClassicalCuspSplitV1
public import AsymptoticReconstructionBranchV1
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix ConjAct
open scoped ModularForm MatrixGroups Pointwise

/-- The honest real-matrix congruence group used by Mathlib cusp forms. -/
abbrev level (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

/-- Arithmetic groups have finite relative index, so their classical trace
 requires no additional finiteness input. -/
def arithmeticTrace (G H : Subgroup (GL (Fin 2) ℝ))
    [G.HasDetOne] [H.HasDetOne] [G.IsArithmetic] [H.IsArithmetic] (k : ℤ) :
    CuspForm G k →ₗ[ℂ] CuspForm H k := by
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  exact trace k

/-- The rational Fricke matrix; its conjugation determines the second old
 direction. No slash-action normalisation is used in this definition. -/
def fricke (N : ℕ) (hN : 0 < N) : GL (Fin 2) ℚ :=
  AsymptoticReconstructionBranch.branch (N : ℚ) 0 0 (by exact_mod_cast hN.ne')

def frickeOldLevel (N M : ℕ) (hN : 0 < N) : Subgroup (GL (Fin 2) ℝ) :=
  toConjAct ((fricke N hN).map (Rat.castHom ℝ)) • level M

instance frickeOldLevel_det (N M : ℕ) (hN : 0 < N) :
    (frickeOldLevel N M hN).HasDetOne := inferInstanceAs
      (toConjAct ((fricke N hN).map (Rat.castHom ℝ)) • level M).HasDetOne

instance frickeOldLevel_arithmetic (N M : ℕ) (hN : 0 < N) [NeZero M] :
    (frickeOldLevel N M hN).IsArithmetic :=
  Subgroup.IsArithmetic.conj (level M) (fricke N hN)

/-- The two actual lower-level trace equations for a prime divisor. -/
def primeTraceKernel (N : ℕ) (hN : 0 < N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) : Submodule ℂ (CuspForm (level N) k) := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero (N / p.val) := ⟨(Nat.div_pos (Nat.le_of_dvd hN p.property.2)
    p.property.1.pos).ne'⟩
  exact LinearMap.ker (arithmeticTrace (level N) (level (N / p.val)) k) ⊓
    LinearMap.ker (arithmeticTrace (level N) (frickeOldLevel N (N / p.val) hN) k)

/-- A concrete classical cusp subspace defined by all old-trace equations.
 Finite dimensionality is proved in AsymptoticClassicalFiniteDimensionV1.
 Identification with the Petersson orthogonal complement of the two old
 directions is proved in AsymptoticClassicalNewOrthogonalV1. Its general
 dimension asymptotic and the newform eigenbasis remain to be proved. -/
def newSpace (N : ℕ) (hN : 0 < N) (k : ℤ) : Submodule ℂ (CuspForm (level N) k) :=
  ⨅ p : {p : ℕ // p.Prime ∧ p ∣ N}, primeTraceKernel N hN k p

theorem mem_newSpace (N : ℕ) (hN : 0 < N) (k : ℤ) (f : CuspForm (level N) k) :
    f ∈ newSpace N hN k ↔
      ∀ p : {p : ℕ // p.Prime ∧ p ∣ N}, f ∈ primeTraceKernel N hN k p := by
  simp [newSpace]

/-- With no bad primes, the trace conditions impose no restriction. -/
theorem newSpace_one (k : ℤ) : newSpace 1 (by decide) k = ⊤ := by
  apply top_unique
  intro f _
  rw [mem_newSpace]
  intro p
  exact False.elim (p.property.1.not_dvd_one p.property.2)

#print axioms frickeOldLevel_arithmetic
#print axioms mem_newSpace
#print axioms newSpace_one

end AsymptoticClassicalCusp
