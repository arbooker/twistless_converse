module

public import Mathlib.NumberTheory.PrimesCongruentOne
public import QuantitativeArithmeticSmallLevelCircBoundaryCornerV1
public import QuantitativeArithmeticSmallLevelEisensteinTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelCirc. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelCircGoodSemisimpleV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp
open CuspSpectral SpectralAlgebra QuantitativeArithmeticSmallLevelEisenstein

/-- Actual good Hecke action on the boundary spectral corner is
semisimple, via its injective finite cusp-constant map. -/
theorem boundaryCornerHecke_isSemisimple (N m : ℕ) [NeZero N]
    (hN : 0 < N) (p q : Nat.Primes) (hpN : ¬ p.val ∣ N)
    (hqN : ¬ q.val ∣ N) (hm : 0 < m) :
    Module.End.IsSemisimple (boundaryCornerHecke N m hN p q) := by
  let P := boundaryPrimePerm N q.val q.property (q.property.coprime_iff_not_dvd.mpr hqN)
  let c : ℂ := (q.val : ℂ)^(((2*m : ℕ) : ℤ)-1)
  let B := permutationOperator P + c • permutationOperator P.symm
  apply semisimple_of_injective_intertwiner _ B (boundaryCornerMap N m hN p)
  · intro E
    funext v
    change finiteCuspBoundary (level N) ((2*m : ℕ) : ℤ) N
      (ModularHecke.primeHecke N q.val q.property ((2*m : ℕ) : ℤ) E.val.val) v = _
    simp only [ModularHecke.primeHecke, hqN, ite_false]
    exact finiteCuspBoundary_goodHecke N q.val q.property hqN ((2*m : ℕ) : ℤ) E.val.val v
  · exact boundaryCornerMap_injective N m hN p hpN hm
  · exact permutation_sum_isSemisimple P c

theorem allHecke_good_isSemisimple_of_auxiliary (N m : ℕ) [NeZero N]
    (hN : 0 < N) (p q : Nat.Primes) (hpN : ¬ p.val ∣ N)
    (hpmod : (p.val : ZMod N) = 1) (hqN : ¬ q.val ∣ N) (hm : 0 < m) :
    Module.End.IsSemisimple (allHecke N (2*m) hN (even_two_mul m) q) := by
  apply semisimple_of_spanning_images _
    (cuspCornerHecke N q.val (2*m) hN q.property hqN)
    (boundaryCornerHecke N m hN p q)
    (cuspCornerInclusion N (2*m) hN) (boundaryCorner N m hN p).subtype
  · intro f
    exact (cuspCornerInclusion_intertwine N (2*m) hN (even_two_mul m) q hqN f).symm
  · intro E
    rfl
  · exact cusp_boundary_spanning N m hN p hpN hpmod hm
  · exact cuspCornerHecke_isSemisimple N q.val (2*m) hN q.property hqN
  · exact boundaryCornerHecke_isSemisimple N m hN p q hpN hqN hm

/-- All good Hecke operators on full Mcirc are semisimple, for arbitrary
level and every positive even weight, including weight two. -/
theorem allHecke_good_isSemisimple (N k : ℕ) [NeZero N]
    (hN : 0 < N) (hk : 0 < k) (heven : Even k)
    (q : Nat.Primes) (hqN : ¬ q.val ∣ N) :
    Module.End.IsSemisimple (allHecke N k hN heven q) := by
  obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp heven
  have hmpos : 0 < m := by omega
  obtain ⟨p,hp,hpgt,hpmod⟩ := Nat.exists_prime_gt_modEq_one N (NeZero.ne N)
  have hpN : ¬ p ∣ N := fun hd => (Nat.le_of_dvd hN hd).not_gt hpgt
  have hpm : (p : ZMod N) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p 1 N).mpr hpmod
  exact allHecke_good_isSemisimple_of_auxiliary N m hN ⟨p,hp⟩ q hpN hpm hqN hmpos

#print axioms boundaryCornerHecke_isSemisimple
#print axioms allHecke_good_isSemisimple
end QuantitativeArithmeticSmallLevelCirc
end
end

/-! ## QuantitativeArithmeticSmallLevelCircFullBasisV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane FinitenessOriginalInput FinitenessOriginalFourier
open SmallLevelOriginal Module

/-- The full trace-new modular space has a normalized simultaneous Hecke
eigenbasis, for arbitrary level and every positive even weight. -/
theorem normalized_joint_basis (N k : ℕ) [NeZero N]
    (hN : 0 < N) (hk : 0 < k) (heven : Even k) :
    ∃ b : Fin (finrank ℂ (space N hN k)) → space N hN k,
      LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ ∧
      (∀ j, coefficient N hN k 1 (b j) = 1) ∧
      ∀ j, ∃ e : Nat.Primes → ℂ, ∀ p : Nat.Primes,
        ModularHecke.primeHecke N p.val p.property (k : ℤ) (b j).val = e p • (b j).val :=
  normalized_joint_basis_of_good_semisimple N k hN heven
    (allHecke_good_isSemisimple N k hN hk heven)

/-- Original Euler solutions which are genuine modular forms. -/
def modularSolutions (N k : ℕ) :=
  {f : ℕ → ℂ // IsSolution N k f ∧ IsModular N k f}

theorem modularSolutions_count_le (N k : ℕ) [NeZero N]
    (hN : 0 < N) (hk : 0 < k) (heven : Even k) :
    Finite (modularSolutions N k) ∧
      Nat.card (modularSolutions N k) ≤ finrank ℂ (space N hN k) := by
  classical
  have hrep (f : modularSolutions N k) :
      ∃ F : space N hN k, (F.val : ℍ → ℂ) = fourierFunction k f.val :=
    original_modular_mem_space hN hk heven f.property.1 f.property.2
  let F : modularSolutions N k → space N hN k := fun f => (hrep f).choose
  let J : modularSolutions N k → S N k := fun f => ⟨f.val,f.property.1⟩
  have hJ : Function.Injective J := fun f g h =>
    Subtype.ext (congrArg (fun f : S N k => f.val) h)
  have hi := (FinitenessOriginalDiskIndependence.normalized_independent N k).comp J hJ
  have hli : LinearIndependent ℂ F := by
    apply LinearIndependent.of_comp (coefficientSequence N hN k)
    have he : (fun f => coefficientSequence N hN k (F f)) =
        (fun f : modularSolutions N k => fullCoefficients f.val k) := by
      funext f n
      exact original_coefficient f.property.1 (F f) (hrep f).choose_spec n
    change LinearIndependent ℂ (fun f => coefficientSequence N hN k (F f))
    rw [he]
    exact hi
  have hf : Finite (modularSolutions N k) := hli.finite
  let := hf
  let := Fintype.ofFinite (modularSolutions N k)
  exact ⟨hf, by rw [Nat.card_eq_fintype_card]; exact hli.fintype_card_le_finrank⟩

/-- The genuine modular intersection has exactly the dimension of full
Mcirc, including its Eisenstein contribution and the weight-two case. -/
theorem modularSolutions_count (N k : ℕ) [NeZero N]
    (hN : 0 < N) (hk : 0 < k) (heven : Even k) :
    Finite (modularSolutions N k) ∧
      Nat.card (modularSolutions N k) = finrank ℂ (space N hN k) := by
  classical
  obtain ⟨hfinite, hupper⟩ := modularSolutions_count_le N k hN hk heven
  let := hfinite
  obtain ⟨b,hli,_,hone,he⟩ := normalized_joint_basis N k hN hk heven
  have hsol (j) : IsSolution N k (ModularLSeries.coefficients (b j).val) := by
    obtain ⟨e,he⟩ := he j
    exact eigenform_isSolution hk heven (b j) (hone j) e he
  let J : Fin (finrank ℂ (space N hN k)) → modularSolutions N k := fun j =>
    ⟨ModularLSeries.coefficients (b j).val,hsol j,(b j).val,(modular_fourierFunction (b j)).symm⟩
  have hJ : Function.Injective J := by
    intro i j hij
    apply hli.injective
    apply Subtype.ext
    apply DFunLike.coe_injective
    rw [← modular_fourierFunction (b i),← modular_fourierFunction (b j)]
    exact congrArg (fourierFunction k) (congrArg Subtype.val hij)
  have hlower := Nat.card_le_card_of_injective J hJ
  simp only [Nat.card_fin] at hlower
  exact ⟨hfinite, Nat.le_antisymm hupper hlower⟩

#print axioms normalized_joint_basis
#print axioms modularSolutions_count
end QuantitativeArithmeticSmallLevelCirc
end
end

/-! ## QuantitativeArithmeticSmallLevelCircExactCountV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane FinitenessOriginalInput SmallLevelOriginal Module

/-- The modular members of the original solution set are exactly, and
without repetitions, the normalized simultaneous Hecke eigenbasis of
the full trace-new space. This is a single arbitrary-level theorem. -/
theorem modular_solutions_are_eigenbasis (N k : ℕ) [NeZero N]
    (hN : 0 < N) (hk : 0 < k) (heven : Even k) :
    ∃ b : Fin (finrank ℂ (space N hN k)) → space N hN k,
      LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ ∧
      (∀ j, coefficient N hN k 1 (b j) = 1) ∧
      (∀ j, ∃ e : Nat.Primes → ℂ, ∀ p : Nat.Primes,
        ModularHecke.primeHecke N p.val p.property (k : ℤ) (b j).val = e p • (b j).val) ∧
      ∀ f : ℕ → ℂ, (IsSolution N k f ∧ IsModular N k f) ↔
        ∃! j, ModularLSeries.coefficients (b j).val = f := by
  classical
  obtain ⟨b,hli,hspan,hone,he⟩ := normalized_joint_basis N k hN hk heven
  have hsol (j) : IsSolution N k (ModularLSeries.coefficients (b j).val) := by
    obtain ⟨e,he⟩ := he j
    exact eigenform_isSolution hk heven (b j) (hone j) e he
  let J : Fin (finrank ℂ (space N hN k)) → modularSolutions N k := fun j =>
    ⟨ModularLSeries.coefficients (b j).val,hsol j,(b j).val,(modular_fourierFunction (b j)).symm⟩
  have hJ : Function.Injective J := by
    intro i j hij
    apply hli.injective
    apply Subtype.ext
    apply DFunLike.coe_injective
    rw [← modular_fourierFunction (b i),← modular_fourierFunction (b j)]
    exact congrArg (fourierFunction k) (congrArg Subtype.val hij)
  obtain ⟨hfinite,hcard⟩ := modularSolutions_count N k hN hk heven
  let := hfinite
  have hbij : Function.Bijective J := hJ.bijective_of_nat_card_le (by simpa using hcard.le)
  refine ⟨b,hli,hspan,hone,he,fun f => ?_⟩
  constructor
  · intro hf
    obtain ⟨j,hj⟩ := hbij.surjective ⟨f,hf⟩
    have hjc : ModularLSeries.coefficients (b j).val = f := congrArg Subtype.val hj
    refine ⟨j,hjc,fun i hi => ?_⟩
    apply hJ
    exact Subtype.ext (hi.trans hjc.symm)
  · rintro ⟨j,hj,_⟩
    have hp := (J j).property
    change IsSolution N k (ModularLSeries.coefficients (b j).val) ∧
      IsModular N k (ModularLSeries.coefficients (b j).val) at hp
    rwa [hj] at hp

/-- Once a converse theorem supplies modularity, the exact solution
count is automatic, at any level. No per-level count argument remains. -/
theorem original_count_eq {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (heven : Even k)
    (hmod : ∀ f : ℕ → ℂ, IsSolution N k f → IsModular N k f) :
    Finite (S N k) ∧ Nat.card (S N k) = finrank ℂ (space N hN k) := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨hfinite,hcard⟩ := modularSolutions_count N k hN hk heven
  let := hfinite
  let e : S N k ≃ modularSolutions N k :=
    { toFun := fun f => ⟨f.val,f.property,hmod f.val f.property⟩
      invFun := fun f => ⟨f.val,f.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Finite.of_injective e e.injective,(Nat.card_congr e).trans hcard⟩

theorem smallLevels_count_eq_of_modular (h : SmallLevelsTheorem)
    (N k : ℕ) (hN : 0 < N) (h36 : N ≤ 36) (h29 : N ≠ 29) (h31 : N ≠ 31)
    (hk : 0 < k) (heven : Even k) :
    Finite (S N k) ∧ Nat.card (S N k) = finrank ℂ (space N hN k) :=
  original_count_eq hN hk heven (h N k hN h36 h29 h31 hk heven)

#print axioms modular_solutions_are_eigenbasis
#print axioms original_count_eq
#print axioms smallLevels_count_eq_of_modular
end QuantitativeArithmeticSmallLevelCirc
end
end
