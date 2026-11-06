module

public import QuantitativeArithmeticSmallLevelCircBadSemisimpleV1
public import QuantitativeArithmeticSmallLevelCircOriginalEigenV1
public import Mathlib.LinearAlgebra.Eigenspace.Pi

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalEigenbasis Module

/-- Standard simultaneous diagonalization for an arbitrary, possibly
infinite, commuting family of semisimple complex endomorphisms. -/
theorem semisimple_joint_family {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (T : ι → Module.End ℂ E)
    (hT : ∀ i, Module.End.IsSemisimple (T i))
    (hcomm : Pairwise fun i j => Commute (T i) (T j)) :
    ∃ b : Fin (finrank ℂ E) → E, LinearIndependent ℂ b ∧
      ∀ j, ∃ e : ι → ℂ, ∀ i, T i (b j) = e i • b j := by
  classical
  let s : Set E := {v | ∃ e : ι → ℂ, ∀ i, T i v = e i • v}
  have hjoint : (⨆ e : ι → ℂ, ⨅ i, Module.End.eigenspace (T i) (e i)) = ⊤ := by
    have hh := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      T hcomm (fun i => Module.End.iSup_maxGenEigenspace_eq_top (T i))
    simpa only [(fun i e => (hT i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace e)] using hh
  have hspan : Submodule.span ℂ s = ⊤ := by
    apply top_unique
    rw [← hjoint]
    refine iSup_le fun e => ?_
    intro v hv
    apply Submodule.subset_span
    refine ⟨e, fun i => ?_⟩
    exact Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf (fun i => Module.End.eigenspace (T i) (e i))).mp hv i)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℂ s
  have hdim : finrank ℂ (Submodule.span ℂ s) = finrank ℂ E := by rw [hspan, finrank_top]
  rw [hdim] at hex
  obtain ⟨b, hb, _, hli⟩ := hex
  exact ⟨b, hli, hb⟩

/-- This isolates precisely the remaining analytic input: semisimplicity
at good primes. Ramified semisimplicity, invariance, commutation,
normalization, and spanning are all proved here or in checked predecessors.
This conditional bridge is not asserted as the completed eigenbasis theorem. -/
theorem normalized_joint_basis_of_good_semisimple (N k : ℕ) [NeZero N]
    (hN : 0 < N) (hk : Even k)
    (hgood : ∀ p : Nat.Primes, ¬ p.val ∣ N → Module.End.IsSemisimple (allHecke N k hN hk p)) :
    ∃ b : Fin (finrank ℂ (space N hN k)) → space N hN k,
      LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ ∧
      (∀ j, coefficient N hN k 1 (b j) = 1) ∧
      ∀ j, ∃ e : Nat.Primes → ℂ, ∀ p : Nat.Primes,
        ModularHecke.primeHecke N p.val p.property (k : ℤ) (b j).val = e p • (b j).val := by
  classical
  let T := allHecke N k hN hk
  have hT (p : Nat.Primes) : Module.End.IsSemisimple (T p) := by
    by_cases hpN : p.val ∣ N
    · exact allHecke_bad_isSemisimple N k hN hk p hpN
    · exact hgood p hpN
  have hcomm : Pairwise (fun p q => Commute (T p) (T q)) := by
    intro p q _
    exact LinearMap.ext (allHecke_commute N k hN hk p q)
  obtain ⟨b, hb, he⟩ := semisimple_joint_family T hT hcomm
  let first := coefficient N hN k 1
  have hfirst (j) : first (b j) ≠ 0 := by
    obtain ⟨e, he⟩ := he j
    intro hz
    exact hb.ne_zero j ((recurrence_of_prime_eigen (b j) e
      (fun p => congrArg Subtype.val (he p))).first_kernel hz)
  let b' := fun j => normalizedVector first (b j)
  have hli : LinearIndependent ℂ b' := by
    exact hb.units_smul (fun j => Units.mk0 ((first (b j))⁻¹) (inv_ne_zero (hfirst j)))
  refine ⟨b', hli, hli.span_eq_top_of_card_eq_finrank' (by simp), ?_, ?_⟩
  · intro j
    exact first_normalizedVector first (hfirst j)
  · intro j
    obtain ⟨e, he⟩ := he j
    exact ⟨e, fun p => congrArg Subtype.val (normalizedVector_eigen T first he p)⟩

#print axioms semisimple_joint_family
#print axioms normalized_joint_basis_of_good_semisimple
end QuantitativeArithmeticSmallLevelCirc
