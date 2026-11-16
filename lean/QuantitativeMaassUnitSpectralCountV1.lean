module

public import QuantitativeMaassUnitWindowCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip

namespace QuantitativeMaass

universe u

/-- The literal principal cuspidal unit-window count is finite and O_N(t),
with the constant chosen before the orthonormal eigenfamily and the centre. -/
theorem principal_unit_window_linear (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (ι : Type u) (v : ι → AutomorphicSpace N),
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      ∀ e : ι → ℝ,(∀ i,0≤e i) →
      (∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) →
      ∀ t : ℝ,1≤t → (principalWindowIndices e (t-1/2) (t+1/2)).Finite ∧
        (Nat.card (principalWindowIndices e (t-1/2) (t+1/2)):ℝ)≤C*t := by
  obtain ⟨C,hC,hcount⟩ := cuspidal_unit_finset_linear N hN
  refine ⟨C,hC,?_⟩
  intro ι v hv hcusp e he hgraph t ht
  let S := principalWindowIndices e (t-1/2) (t+1/2)
  have hf : S.Finite := principalWindowIndices_finite N hN v hv hcusp e he hgraph _ _
  let : Fintype S := hf.fintype
  refine ⟨hf,?_⟩
  have hh := hcount S t ht (fun i : S => v i.val) (fun i : S => Real.sqrt (e i.val-1/4))
    (hv.comp _ Subtype.val_injective) (fun i => hcusp i.val) (fun i => i.property.2)
    (fun i => ?_) Finset.univ
  · simpa only [Finset.card_univ,Nat.card_eq_fintype_card] using hh
  · have hs := Real.sq_sqrt (sub_nonneg.mpr i.property.1)
    have heq : 1/4+(Real.sqrt (e i.val-1/4))^2=e i.val := by linarith
    rw [heq]
    exact hgraph i.val

/-- Unit intervals starting anywhere on the nonnegative principal axis have
at most C_N(s+1) cusp eigenvectors, including the fixed low-energy range. -/
theorem principal_unit_interval_linear (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (ι : Type u) (v : ι → AutomorphicSpace N),
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      ∀ e : ι → ℝ,(∀ i,0≤e i) →
      (∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) →
      ∀ s : ℝ,0≤s → (principalWindowIndices e s (s+1)).Finite ∧
        (Nat.card (principalWindowIndices e s (s+1)):ℝ)≤C*(s+1) := by
  obtain ⟨A,hA,hunit⟩ := principal_unit_window_linear N hN
  obtain ⟨B,hB,hcoarse⟩ := cuspidal_spectral_band_polynomial N hN
  refine ⟨A+B*4^6,by positivity,?_⟩
  intro ι v hv hcusp e he hgraph s hs
  refine ⟨principalWindowIndices_finite N hN v hv hcusp e he hgraph _ _,?_⟩
  by_cases hlarge : 1/2≤s
  · have hh := (hunit ι v hv hcusp e he hgraph (s+1/2) (by linarith)).2
    rw [show s+1/2-1/2=s by ring,show s+1/2+1/2=s+1 by ring] at hh
    have hb0 : 0≤B*4^6*(s+1) := by positivity
    nlinarith
  · have hsmall : s<1/2 := lt_of_not_ge hlarge
    have hb := hcoarse ι v hv hcusp e he hgraph 3 (by norm_num)
    have hsub : principalWindowIndices e s (s+1)⊆{i | e i≤3} := by
      intro i hi
      have hr := pow_le_pow_left₀ (Real.sqrt_nonneg (e i-1/4)) hi.2.2 2
      have hsq := Real.sq_sqrt (sub_nonneg.mpr hi.1)
      have hss : (s+1)^2≤(3/2:ℝ)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      change e i≤3
      nlinarith
    have hn : (Nat.card (principalWindowIndices e s (s+1)):ℝ)≤
        (Nat.card {i // e i≤3}:ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub hb.1
    have hb' : (Nat.card {i // e i≤3}:ℝ)≤B*4^6 := by norm_num at hb ⊢; exact hb.2
    have hc0 : 0≤B*4^6*s := by positivity
    have ha0 : 0≤A*(s+1) := by positivity
    nlinarith

#print axioms principal_unit_window_linear
#print axioms principal_unit_interval_linear

end QuantitativeMaass
