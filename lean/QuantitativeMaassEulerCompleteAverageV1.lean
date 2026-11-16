module

public import QuantitativeMaassEulerCompletePhaseV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass

/-- A literal finite average of the absolutely convergent Fourier--Bessel
series, with frequency extraction and reindexing proved inside Lean. -/
theorem principalEulerCore_complete_average {b : ℕ→ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) {p : ℕ} (hp : 0<p) (x y : ℝ) (hy : 0<y) :
    (∑ a∈Finset.range p,principalEulerCore b r σ ((x+(a:ℝ))/p,y/p))=
      (p:ℂ)*principalEulerCore (fun n => b (p*n)) r σ (x,y) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hs : ∀ a∈Finset.range p,Summable (fun n =>
      principalEulerTermNat b r σ n ((x+(a:ℝ))/p,y/p)) :=
    fun a _ => principalEulerTermNat_summable hb r σ _ (div_pos hy hpR)
  simp_rw [principalEulerCore_nat]
  rw [←Summable.tsum_finsetSum hs]
  let f : ℕ→ℂ := fun n => if n=0 then 0 else
    (b n*(MaassKBessel.moment 0 r (2*Real.pi*(n:ℝ)*(y/p)):ℂ))*
      ((if p∣n then (p:ℂ) else 0)*eulerParityPhase σ n (x/p))
  have hsum (n : ℕ) : (∑ a∈Finset.range p,
      principalEulerTermNat b r σ n ((x+(a:ℝ))/p,y/p))=f n := by
    by_cases hn : n=0
    · simp [principalEulerTermNat,hn,f]
    · simp only [principalEulerTermNat,f,ite_eq_right hn]
      rw [←Finset.mul_sum,eulerParityPhase_complete hp]
  simp_rw [hsum]
  have hinj : Function.Injective (fun n : ℕ => p*n) := by
    intro n m h
    exact Nat.eq_of_mul_eq_mul_left hp h
  have hsupp : Function.support f⊆Set.range (fun n : ℕ => p*n) := by
    intro n hn
    have hd : p∣n := by
      by_contra hd
      exact hn (by simp [f,hd])
    obtain ⟨m,hm⟩ := hd
    exact ⟨m,hm.symm⟩
  rw [←hinj.tsum_eq hsupp,←tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [f,principalEulerTermNat,hn]
  have hpn : p*n≠0 := Nat.mul_ne_zero hp.ne' hn
  have harg (z : ℝ) : 2*Real.pi*((p*n:ℕ):ℝ)*(z/p)=2*Real.pi*(n:ℝ)*z := by
    push_cast
    field_simp
  have hphase : eulerParityPhase σ (p*n) (x/p)=eulerParityPhase σ n x := by
    unfold eulerParityPhase
    rw [harg]
  dsimp only [f]
  rw [ite_eq_right hpn,ite_eq_left (dvd_mul_right p n),harg,hphase]
  rw [principalEulerTermNat,ite_eq_right hn]
  ring

theorem principalEulerCore_coefficient_smul (b : ℕ→ℂ) (c : ℂ) (r : ℝ) (σ : ℕ) (z : ℝ×ℝ) :
    principalEulerCore (fun n => c*b n) r σ z=c*principalEulerCore b r σ z := by
  simp only [principalEulerCore,principalEulerTerm,mul_assoc,tsum_mul_left]

/-- A ramified coefficient relation implies the corresponding complete
average, before the common sqrt(y) factor is reinserted. -/
theorem principalEulerCore_average_of_row {b : ℕ→ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) {p : ℕ} (hp : 0<p) (c : ℂ)
    (hrow : ∀ n,b (p*n)=c*b n) (x y : ℝ) (hy : 0<y) :
    (∑ a∈Finset.range p,principalEulerCore b r σ ((x+(a:ℝ))/p,y/p))=
      (p:ℂ)*c*principalEulerCore b r σ (x,y) := by
  rw [principalEulerCore_complete_average hb r σ hp x y hy]
  simp_rw [hrow]
  rw [principalEulerCore_coefficient_smul]
  ring

#print axioms principalEulerCore_complete_average
#print axioms principalEulerCore_average_of_row
end QuantitativeMaass
