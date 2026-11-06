module

public import SpanningTraceDigitsV1
public import SpanningCoordinateDefectsV1
public import SpanningClassicalExceptionalV1

set_option autoImplicit false

@[expose] public section

namespace SpanningClassicalZones

open Set SpanningCoherentLifts SpanningProjectedWords SpanningKernelDefects
open SpanningExceptionalSet

/-- Convert an interior fractional-position inequality into the natural digit
index used in the periodic block. The outer block index may be any integer. -/
theorem digit_of_ratio {D n i₀ P j : ℕ} (_hD : 0<D) (_hn : 0<n) (l : ℤ)
    (hlo : (i₀:ℝ) ≤ (j:ℝ)-(D*n:ℕ)*(l:ℝ))
    (hup : (j:ℝ)-(D*n:ℕ)*(l:ℝ)+(P:ℝ)<n) :
    ∃ i : ℕ, i₀ ≤ i ∧ i+P<n ∧ (j:ℤ)=(D*n:ℕ)*(l:ℤ)+i := by
  let z : ℤ := (j:ℤ)-(D*n:ℕ)*l
  have hzlo : (i₀:ℤ)≤z := by exact_mod_cast hlo
  have hzup : z+P<(n:ℤ) := by exact_mod_cast hup
  have hz : 0≤z := (Int.natCast_nonneg _).trans hzlo
  refine ⟨z.toNat,?_,?_,?_⟩
  · exact_mod_cast (show (i₀:ℤ)≤(z.toNat:ℤ) by simpa [Int.toNat_of_nonneg hz] using hzlo)
  · exact_mod_cast (show (z.toNat:ℤ)+P<(n:ℤ) by simpa [Int.toNat_of_nonneg hz] using hzup)
  · rw [Int.toNat_of_nonneg hz]
    dsimp [z]
    ring

/-- The diagonal tower contains every fixed outer block, with an arbitrarily
large remaining inner factor. -/
theorem diagonal_factor {p r : ℕ} (hp : 2≤p) (hr : 2≤r) (b c L : ℕ) :
    ∃ a₀ : ℕ, ∀ a≥a₀, ∃ n : ℕ, Tower p r n ∧ L<n ∧
      (p*r)^a = (p^b*r^c)*((p*r)*n) := by
  refine ⟨b+c+L+2,?_⟩
  intro a ha
  let n := p^(a-b-1)*r^(a-c-1)
  have hb : b+1≤a := by omega
  have hc : c+1≤a := by omega
  have he : L<a-b-1 := by omega
  have hpow : a-b-1 < p^(a-b-1) := Nat.lt_pow_self (by omega)
  have hrpow : 0<r^(a-c-1) := pow_pos (by omega) _
  refine ⟨n,⟨a-b-1,a-c-1,rfl⟩,?_,?_⟩
  · exact he.trans (hpow.trans_le (Nat.le_mul_of_pos_right _ hrpow))
  · dsimp [n]
    rw [mul_pow]
    have hba : b+1+(a-b-1)=a := by omega
    have hca : c+1+(a-c-1)=a := by omega
    calc
      p^a*r^a = (p^b*p*p^(a-b-1))*(r^c*r*r^(a-c-1)) := by
        rw [← pow_succ, ← pow_add, hba, ← pow_succ, ← pow_add, hca]
      _ = _ := by ring

/-- An entry into the periodic circle arc gives a real interval with a
uniform margin from both endpoints. -/
theorem entry_interval {Q p r D : ℕ} {x : ℝ}
    (hx : (x:Circle) ∉ exceptional Q p r (periodicArc D)) :
    ∃ b c : ℕ, ∃ l : ℤ, ∃ η : ℝ, 0<η ∧
      η < (Q*p^b*r^c:ℕ)*(x:ℝ)-(l:ℝ) ∧
      (Q*p^b*r^c:ℕ)*(x:ℝ)-(l:ℝ)<1/(D:ℝ)-η := by
  simp only [exceptional,mem_ofPred_eq,not_forall,not_not] at hx
  obtain ⟨b,c,t,ht,he⟩ := hx
  have hzero : ((((Q*p^b*r^c:ℕ):ℝ)*x-t:ℝ):Circle)=0 := by
    rw [AddCircle.coe_sub]
    have hc : ((((Q*p^b*r^c:ℕ):ℝ)*x:ℝ):Circle) = (Q*p^b*r^c) • (x:Circle) := by
      rw [← AddCircle.coe_nsmul,nsmul_eq_mul]
    rw [hc,← he,sub_self]
  obtain ⟨l,hl⟩ := (AddCircle.coe_eq_zero_iff 1).mp hzero
  have hl' : (l:ℝ)=((Q*p^b*r^c:ℕ):ℝ)*x-t := by simpa using hl
  let η := min t (1/(D:ℝ)-t)/2
  have hη : 0<η := half_pos (lt_min ht.1 (sub_pos.mpr ht.2))
  refine ⟨b,c,l,η,hη,?_,?_⟩
  · have hh := min_le_left t (1/(D:ℝ)-t)
    dsimp [η] at *
    linarith
  · have hh := min_le_right t (1/(D:ℝ)-t)
    dsimp [η] at *
    linarith

#print axioms digit_of_ratio
#print axioms diagonal_factor
#print axioms entry_interval

end SpanningClassicalZones
