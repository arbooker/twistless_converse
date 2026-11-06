module

public import QuantitativeNewGapRepeatedAllV1
public import QuantitativeNewGapJointProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticPolarIsometry
open scoped lp

/-- Energy of the two literal old projections at a prime of the level. -/
def localOldEnergy (N : ℕ) (hN : 0<N) (p : ℕ)
    (f : ℓ²(Classes (gamma N),ℂ)) : ℝ := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  exact if hp : p.Prime ∧ p∣N then
    ‖(space (gamma_le_of_dvd (Nat.div_dvd_of_dvd hp.2))).starProjection f‖^2+
    ‖(space (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hp.2))).starProjection f‖^2 else 0

theorem localOldEnergy_nonneg (N : ℕ) (hN : 0<N) (p : ℕ)
    (f : ℓ²(Classes (gamma N),ℂ)) : 0≤localOldEnergy N hN p f := by
  classical
  unfold localOldEnergy
  split
  · positivity
  · exact le_rfl

/-- Every actual prime-local new complement has positive coercivity,
uniform on the full infinite quotient Hilbert space. -/
theorem localSpace_old_energy_gap (N : ℕ) (hN : 0<N) (p : ℕ) :
    ∃ γ : ℝ, 0<γ ∧ ∀ f : ℓ²(Classes (gamma N),ℂ),
      γ*‖f-(AsymptoticTotalNewCorner.localSpace N hN p).starProjection f‖^2≤
        localOldEnergy N hN p f := by
  classical
  by_cases hp : p.Prime ∧ p∣N
  · obtain ⟨M,rfl⟩ := hp.2
    have hM : 0<M := by nlinarith
    let : NeZero (p*M) := ⟨hN.ne'⟩
    obtain ⟨γ,hγ,hgap⟩ := prime_coset_old_gap M p hM hp.1
    refine ⟨γ,hγ,?_⟩
    intro f
    rw [starProjection_congr _ _ (AsymptoticTotalNewCorner.localSpace_mul_eq M p hM hp.1)]
    simpa only [localOldEnergy,dite_eq_left hp,Nat.mul_div_cancel_left M hp.1.pos] using hgap f
  · refine ⟨1,by norm_num,?_⟩
    intro f
    have hv : AsymptoticTotalNewCorner.localSpace N hN p=⊤ := by
      simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_right hp]
    rw [starProjection_congr _ _ hv,Submodule.starProjection_top]
    simp [localOldEnergy,hp]

/-- A single positive coefficient controls the sum of all actual local
distances on any finite prime list. No commutation is needed for this step. -/
theorem finite_local_energy_gap (N : ℕ) (hN : 0<N) (l : List ℕ) :
    ∃ γ : ℝ, 0<γ ∧ ∀ f : ℓ²(Classes (gamma N),ℂ),
      γ*(l.map fun p => ‖f-(AsymptoticTotalNewCorner.localSpace N hN p).starProjection f‖^2).sum≤
        (l.map fun p => localOldEnergy N hN p f).sum := by
  induction l with
  | nil => exact ⟨1,by norm_num,by simp⟩
  | cons p l ih =>
    obtain ⟨a,ha,hag⟩ := localSpace_old_energy_gap N hN p
    obtain ⟨b,hb,hbg⟩ := ih
    refine ⟨min a b,lt_min ha hb,?_⟩
    intro f
    simp only [List.map_cons,List.sum_cons,mul_add]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg _)).trans (hag f)
    · exact (mul_le_mul_of_nonneg_right (min_le_right a b)
        (List.sum_nonneg (fun x hx => by
          obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
          positivity))).trans (hbg f)

#print axioms localSpace_old_energy_gap
#print axioms finite_local_energy_gap

end QuantitativeNewGap
