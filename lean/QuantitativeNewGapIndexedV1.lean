module

public import QuantitativeNewGapAllPrimesV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticCongruenceStrip QuantitativeArithmeticCrossPrime UpperHalfPlane
open scoped lp

abbrev PrimeOldIndex (N : ℕ) := {p : ℕ // p∈N.primeFactors} × Bool

theorem primeOld_le (N : ℕ) (hN : 0<N) (i : PrimeOldIndex N) :
    gamma N≤oldGroup N hN i.1.val i.2 := by
  have hp := Nat.mem_primeFactors.mp i.1.property
  cases hb : i.2
  · simpa only [oldGroup,hb,Bool.false_eq_true,ite_false] using
      gamma_le_of_dvd (Nat.div_dvd_of_dvd hp.2.1)
  · simpa only [oldGroup,hb,ite_true] using
      gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hp.2.1)

instance primeOld_finite (N : ℕ) (hN : 0<N) (p : ℕ) (b : Bool) :
    Finite (oldGroup N hN p b ⧸ (gamma N).subgroupOf (oldGroup N hN p b)) := by
  let : NeZero N := ⟨hN.ne'⟩
  cases b
  · change Finite (gamma (N/p) ⧸ (gamma N).subgroupOf (gamma (N/p)))
    infer_instance
  · change Finite (frickeOldGroup N (N/p) hN ⧸
      (gamma N).subgroupOf (frickeOldGroup N (N/p) hN))
    infer_instance

theorem weightedLocalOldEnergy_bool (N : ℕ) (hN : 0<N)
    (p : {p : ℕ // p∈N.primeFactors})
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    (∑ b : Bool,‖(AsymptoticCongruenceOldSpace.space N (oldGroup N hN p.val b)
      (primeOld_le N hN (p,b)) hε ht z).starProjection v‖^2)=
      weightedLocalOldEnergy N hN p.val hε ht z v := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  have hp : p.val.Prime ∧ p.val∣N :=
    ⟨(Nat.mem_primeFactors.mp p.property).1,(Nat.mem_primeFactors.mp p.property).2.1⟩
  simp only [Fintype.sum_bool,weightedLocalOldEnergy,dite_eq_left hp,oldGroup,
    Bool.false_eq_true,ite_false,ite_true,AsymptoticCongruenceOldSpace.lowerSpace,
    AsymptoticCongruenceOldSpace.frickeSpace]
  exact add_comm _ _

/-- Exact canonical prime-by-Boolean family used by old-observation
recombiners. The inclusion and finite relative quotient are proved above. -/
theorem indexed_old_energy_eq (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    (∑ i : PrimeOldIndex N,
      ‖(AsymptoticCongruenceOldSpace.space N (oldGroup N hN i.1.val i.2)
        (primeOld_le N hN i) hε ht z).starProjection v‖^2)=
      (N.primeFactors.toList.map fun p => weightedLocalOldEnergy N hN p hε ht z v).sum := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [weightedLocalOldEnergy_bool]
  exact (Finset.sum_coe_sort N.primeFactors
    (fun p => weightedLocalOldEnergy N hN p hε ht z v)).trans
    (Finset.sum_map_toList N.primeFactors (fun p => weightedLocalOldEnergy N hN p hε ht z v)).symm

/-- Uniform gap for the actual total-new quotient projection, with
exactly the finite old-group family used by source-observability. -/
theorem totalNew_indexed_weighted_gap (N : ℕ) (hN : 0<N) :
    ∃ γ : ℝ, 0<γ ∧ ∀ {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
      (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),
      v∈AsymptoticCongruenceQuotient.quotientSpace N hε ht z →
      γ*‖v-(AsymptoticTotalNewCorner.stripSpace N hN hε ht z).starProjection v‖^2≤
        ∑ i : PrimeOldIndex N,
          ‖(AsymptoticCongruenceOldSpace.space N (oldGroup N hN i.1.val i.2)
            (primeOld_le N hN i) hε ht z).starProjection v‖^2 := by
  obtain ⟨γ,hγ,hgap⟩ := totalNew_weighted_old_energy_gap N hN
  refine ⟨γ,hγ,?_⟩
  intro ε hε t ht z v hv
  rw [indexed_old_energy_eq]
  exact hgap hε ht z v hv

#print axioms primeOld_le
#print axioms primeOld_finite
#print axioms totalNew_indexed_weighted_gap

end QuantitativeNewGap
