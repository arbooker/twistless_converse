module

public import FinitenessRamanujanFourierV1
public import FinitenessHolomorphicSpaceV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessTwistedAnalyticBridge

open Complex FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  FinitenessRamanujanFourier FinitenessAnalyticReconstruction FinitenessHolomorphicSpace

/-- The remaining arithmetic obligation, stated using the actual
Ramanujan coefficient twist and the original analytic continuation predicate. -/
def TwistedContinuations (N Q k : ℕ) (f : ℕ → ℂ) : Prop :=
  ∀ q : ℕ, q ∣ Q → Continuation (Nat.lcm N (q^2)) k (twisted f q)

/-- ALL analytic consequences of twisted continuation, including the
literal row-system law and the finite two-sign multiplier restriction. -/
theorem laws_of_continuations {N Q m : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hg : f =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^τ))
    (hc : TwistedContinuations N Q (2*m) f) :
    ∃ χ : ℕ → ℂ, (∀ q, χ q=I^(2*m) ∨ χ q = -I^(2*m)) ∧
      (∀ q, ‖χ q‖=1) ∧ Laws N Q χ m (fourier (fullCoefficients f (2*m))) := by
  classical
  have hall : ∀ q : ℕ, ∃ ε : ℂ, (ε=1 ∨ ε = -1) ∧
      (q ∣ Q → ∀ z : ℂ, 0 < z.im →
        twist (fourier (fullCoefficients f (2*m))) q z =
          ((ε : ℂ)*I^(2*m))/((((Real.sqrt (Nat.lcm N (q^2)) : ℝ):ℂ)*z)^(2*m))*
            twist (fourier (fullCoefficients f (2*m))) q (-1/((Nat.lcm N (q^2) : ℕ)*z))) := by
    intro q
    by_cases hq : q ∣ Q
    · have hqp : 0 < q := Nat.pos_of_dvd_of_pos hq hQ
      have hL : 0 < Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hqp _)
      obtain ⟨ε,hε,he⟩ := FinitenessOriginalFricke.fricke_of_continuation hL
        (twisted_zero hf0 q) (twisted_growth hg q) (hc q hq)
      refine ⟨ε,hε,fun _ z hz => ?_⟩
      have hr : 0 < (-1/((Nat.lcm N (q^2) : ℕ)*z)).im := by
        simpa only [ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
          (L := (Nat.lcm N (q^2) : ℝ)) (by exact_mod_cast hL) hz
      simpa only [fourier_twisted hf0 hg q (2*m) hz, fourier_twisted hf0 hg q (2*m) hr] using he z hz
    · exact ⟨1,Or.inl rfl,fun h => (hq h).elim⟩
  choose ε hε he using hall
  refine ⟨fun q => (ε q : ℂ)*I^(2*m),?_,?_,?_⟩
  · intro q
    rcases hε q with h | h
    · left; simp [h]
    · right; simp [h]
  · intro q
    rcases hε q with h | h <;> simp [h]
  · exact he

/-- The Fourier disk representative is canonical and lies in the exact
holomorphic space whose O_N(k) dimension bound was already checked. -/
theorem disk_mem_space {N Q m : ℕ} {χ : ℕ → ℂ} {f : ℕ → ℂ}
    (hN : 0 < N) (hQ : 0 < Q)
    (hf0 : f 0=0) {τ : ℝ} (hg : f =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^τ))
    (hlaw : Laws N Q χ m (fourier (fullCoefficients f (2*m)))) :
    (⟨disk (fullCoefficients f (2*m)), disk_holomorphic (polynomial_bound hf0 hg (2*m))⟩ : FinitenessDiskJet.space)
      ∈ space N Q χ m := by
  refine ⟨disk_zero (fullCoefficients_zero hf0 (2*m)), fun _ hw => disk_outside _ hw, ?_, ?_⟩
  · intro z
    unfold FinitenessHolomorphicSpace.lift
    rw [q_periodic]
  · intro q hq z hz
    have hqp : 0 < q := Nat.pos_of_dvd_of_pos hq hQ
    have hL : 0 < Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hqp _)
    have heq : ∀ w : ℂ, 0 < w.im → lift (disk (fullCoefficients f (2*m))) w =
        fourier (fullCoefficients f (2*m)) w := fun _ hw => disk_eq_fourier _ hw
    have ht : ∀ w : ℂ, 0 < w.im →
        twist (lift (disk (fullCoefficients f (2*m)) )) q w =
          twist (fourier (fullCoefficients f (2*m))) q w := by
      intro w hw
      apply Finset.sum_congr rfl
      intro a _
      exact heq _ (by simpa using hw)
    rw [ht z hz]
    have hr : 0 < (-1/((Nat.lcm N (q^2) : ℕ)*z)).im := by
      simpa only [ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
        (L := (Nat.lcm N (q^2) : ℝ)) (by exact_mod_cast hL) hz
    rw [ht _ hr]
    exact hlaw q hq z hz

#print axioms laws_of_continuations
#print axioms disk_mem_space

end FinitenessTwistedAnalyticBridge
