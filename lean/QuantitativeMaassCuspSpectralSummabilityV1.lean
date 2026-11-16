module

public import QuantitativeMaassCuspPolynomialCountV1
public import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass

/-- Polynomial counting makes a sufficiently high resolvent weight summable.
The proof uses finite unit-energy bands, not a prescribed enumeration. -/
theorem summable_inverse_eighth_of_polynomial_bands {ι : Type*}
    (e : ι → ℝ) (he : ∀ i,0≤e i) (B : ℝ) (hB : 0≤B)
    (hfinite : ∀ E : ℝ,0≤E → {i | e i≤E}.Finite)
    (hcount : ∀ E : ℝ,0≤E → (Nat.card {i // e i≤E}:ℝ)≤B*(E+1)^6) :
    Summable (fun i => 1/(e i+1)^8) := by
  classical
  let S : ℕ → Set ι := fun n => {i | ⌊e i⌋₊=n}
  have hsub (n : ℕ) : S n ⊆ {i | e i≤(n:ℝ)+1} := by
    intro i hi
    have h := Nat.lt_floor_add_one (e i)
    rw [show ⌊e i⌋₊=n from hi] at h
    exact h.le
  have hfin (n : ℕ) : (S n).Finite := (hfinite ((n:ℝ)+1) (by positivity)).subset (hsub n)
  let (n : ℕ) : Fintype (S n) := (hfin n).fintype
  have hcard (n : ℕ) : (Fintype.card (S n):ℝ)≤B*((n:ℝ)+2)^6 := by
    let : Fintype ↥({i | e i≤(n:ℝ)+1}:Set ι) := (hfinite ((n:ℝ)+1) (by positivity)).fintype
    have hnat := Nat.card_le_card_of_injective (Set.inclusion (hsub n)) (Set.inclusion_injective (hsub n))
    have hc : (Nat.card (S n):ℝ)≤(Nat.card {i // e i≤(n:ℝ)+1}:ℝ) := by exact_mod_cast hnat
    have h := hc.trans (hcount ((n:ℝ)+1) (by positivity))
    simpa only [Nat.card_eq_fintype_card,show (n:ℝ)+1+1=(n:ℝ)+2 by ring] using h
  have hlocal (n : ℕ) : (∑' i : S n,1/(e i.val+1)^8)≤(64*B)/((n:ℝ)+1)^2 := by
    have hn : 0<(n:ℝ)+1 := by positivity
    have hpoint (i : S n) : 1/(e i.val+1)^8≤1/((n:ℝ)+1)^8 := by
      have hfloor := Nat.floor_le (he i.val)
      rw [show ⌊e i.val⌋₊=n from i.property] at hfloor
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ hn.le (by linarith) 8)
    have hratio : ((n:ℝ)+2)^6/((n:ℝ)+1)^8≤64/((n:ℝ)+1)^2 := by
      have hp := pow_le_pow_left₀ (by positivity : 0≤(n:ℝ)+2)
        (by linarith only [show (0:ℝ)≤(n:ℝ) by positivity] : (n:ℝ)+2≤2*((n:ℝ)+1)) 6
      calc
        _ ≤ (2*((n:ℝ)+1))^6/((n:ℝ)+1)^8 := div_le_div_of_nonneg_right hp (by positivity)
        _ = _ := by field_simp; ring
    calc
      _ = ∑ i : S n,1/(e i.val+1)^8 := tsum_fintype _
      _ ≤ ∑ _i : S n,1/((n:ℝ)+1)^8 := Finset.sum_le_sum (fun i _ => hpoint i)
      _ = (Fintype.card (S n):ℝ)/((n:ℝ)+1)^8 := by simp [div_eq_mul_inv]
      _ ≤ (B*((n:ℝ)+2)^6)/((n:ℝ)+1)^8 := div_le_div_of_nonneg_right (hcard n) (by positivity)
      _ = B*(((n:ℝ)+2)^6/((n:ℝ)+1)^8) := by ring
      _ ≤ B*(64/((n:ℝ)+1)^2) := mul_le_mul_of_nonneg_left hratio hB
      _ = _ := by ring
  have hp : Summable (fun n : ℕ => (64*B)/((n:ℝ)+1)^2) := by
    have hh : Summable (fun n : ℕ => 1/(n:ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hs := (summable_nat_add_iff 1).mpr hh
    simpa only [Nat.cast_add,Nat.cast_one,mul_one_div] using hs.mul_left (64*B)
  apply (summable_partition (fun i => (by positivity : (0:ℝ)≤1/(e i+1)^8))
    (s:=S) (fun i => ⟨⌊e i⌋₊,rfl,fun n hn => hn.symm⟩)).mpr
  refine ⟨fun n => (hasSum_fintype _).summable,?_⟩
  exact Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => by positivity)) hlocal hp

/-- The actual nonnegative Friedrichs energies of any orthonormal cuspidal
family have a summable eighth resolvent weight, for every positive level. -/
theorem cuspidal_inverse_eighth_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) :
    Summable (fun i => 1/(e i+1)^8) := by
  obtain ⟨B,hB,h⟩ := cuspidal_spectral_band_polynomial N hN
  exact summable_inverse_eighth_of_polynomial_bands e he B hB.le
    (fun E hE => (h ι v hv hcusp e he hgraph E hE).1)
    (fun E hE => (h ι v hv hcusp e he hgraph E hE).2)

#print axioms summable_inverse_eighth_of_polynomial_bands
#print axioms cuspidal_inverse_eighth_summable

end QuantitativeMaass
