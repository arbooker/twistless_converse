module

public import SpanningClassicalLocalV1
public import SpanningCompactConcentrationV1

set_option autoImplicit false

@[expose] public section

namespace SpanningClassicalConcentration

open Set SpanningClassicalZones SpanningCompactConcentration SpanningExceptionalSet
open SpanningProjectedWords IndependentBases SpanningCoherentLifts SpanningKernelDefects

/-- Cobham periodic blocks concentrate their defects near a finite rational
set, by Furstenberg's theorem and compactness. -/
theorem words_concentrate {A : Type*} {Q p r P i₀ : ℕ}
    (hQ : 0<Q) (hp : 2≤p) (hr : 2≤r) (hi : Independent p r) (W : ℕ → ℤ → A)
    (hperiod : ∀ m n, Tower p r m → Tower p r n → ∀ (l : ℤ) (i : ℕ),
      i₀ ≤ i → i+P<n → W (m*((p*r)*n)) (((p*r)*n:ℕ)*l+(i+P:ℕ)) =
        W (m*((p*r)*n)) (((p*r)*n:ℕ)*l+i)) :
    ∃ F : Finset ℚ, ∀ ε : ℝ, 0<ε → ∃ a₀ : ℕ, ∀ a≥a₀, ∀ j : ℕ,
      j<Q*(p*r)^a → W ((p*r)^a) (j+P:ℕ)≠W ((p*r)^a) j →
        ∃ s∈F, |(j:ℝ)/(Q*(p*r)^a:ℕ)-(s:ℝ)|<ε := by
  have hE := exceptional_finite hp hr hi (periodicArc_open (p*r))
    (periodicArc_proper_exceptional hQ (Nat.mul_pos (by omega) (by omega)))
  obtain ⟨F,hF⟩ := exceptional_rational_lifts hp hE
  let D : ℕ → Set ℝ := fun a => {x | ∃ j : ℕ, j<Q*(p*r)^a ∧
    W ((p*r)^a) (j+P:ℕ)≠W ((p*r)^a) j ∧ (j:ℝ)/(Q*(p*r)^a:ℕ)=x}
  have hbound : ∀ a, D a ⊆ Icc 0 1 := by
    rintro a x ⟨j,hj,_,rfl⟩
    have hpos : (0:ℝ)<(Q*(p*r)^a:ℕ) := by positivity
    exact ⟨by positivity,(div_le_one hpos).mpr (by exact_mod_cast hj.le)⟩
  have hlocal : ∀ x ∈ Icc (0:ℝ) 1, (∀ s∈F,(s:ℝ)≠x) →
      ∃ U : Set ℝ, IsOpen U ∧ x∈U ∧ ∃ n : ℕ, ∀ a≥n, Disjoint U (D a) := by
    intro x hx hn
    have hxE : (x:Circle) ∉ exceptional Q p r (periodicArc (p*r)) := by
      intro he
      obtain ⟨s,hs,he⟩ := hF x hx he
      exact hn s hs he
    obtain ⟨U,hU,hxU,n,hperiodU⟩ := local_periodicity hQ hp hr W hperiod hxE
    refine ⟨U,hU,hxU,n,?_⟩
    intro a ha
    apply Set.disjoint_left.mpr
    rintro y hy ⟨j,_,hne,rfl⟩
    exact hne (hperiodU a ha j hy)
  have hconc := concentration_of_local_exclusion D F hbound hlocal
  refine ⟨F,fun ε hε => ?_⟩
  obtain ⟨n,hn⟩ := hconc ε hε
  exact ⟨n,fun a ha j hj hne => hn a ha _ ⟨j,hj,hne,rfl⟩⟩

/-- Rational concentration for the actual stationary trace kernels. No
bound on the cardinality of the defect set is needed or asserted. -/
theorem stationary_concentration {K : Type} [Field K] [Finite K]
    {N Q c d : ℕ} {L : Set ℕ} (hQ : 0<Q) (hc : 2≤c) (hd : 2≤d)
    (hi : Independent c d) (hcN : Nat.Coprime N c) (hdN : Nat.Coprime N d)
    (hdiv : ∀ ell∈L,ell∣Q) (E : ∀ a b : ℕ, TraceLift (K:=K) N L Q (c^a*d^b)) :
    ∃ P : ℕ, 0<P ∧ ∃ F : Finset ℚ, ∀ ε : ℝ, 0<ε → ∀ T : ℝ,
      ∃ R : ℕ, 0<R ∧ Q∣R ∧ T<(R:ℝ) ∧
        ∀ j∈coordinateDefects (K:=K) N L R P,
          ∃ s∈F, |(j:ℝ)/(R:ℝ)-(s:ℝ)|<ε := by
  classical
  have hEt : ∀ n, Tower c d n → Nonempty (TraceLift (K:=K) N L Q n) := by
    rintro n ⟨a,b,rfl⟩
    exact ⟨E a b⟩
  let Et : ∀ n, Tower c d n → TraceLift (K:=K) N L Q n := fun n hn => Classical.choice (hEt n hn)
  obtain ⟨s,t,P,i₀,hs,ht,hP,hperiod⟩ := periodic_trace_words hQ hc hd hi hcN hdN hdiv Et
  let p := c^s
  let r := d^t
  have hp : 2≤p := hc.trans (le_self_pow₀ (by omega) hs.ne')
  have hr : 2≤r := hd.trans (le_self_pow₀ (by omega) ht.ne')
  obtain ⟨F,hF⟩ := words_concentrate hQ hp hr (independent_powers hi hs ht)
    (towerWord Et) hperiod
  refine ⟨P,hP,F,fun ε hε T => ?_⟩
  obtain ⟨a₀,ha₀⟩ := hF ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt T
  let a := a₀+k+1
  have hD : 2≤p*r := by nlinarith
  have hpow : a<(p*r)^a := Nat.lt_pow_self (by omega)
  have hR : 0<Q*(p*r)^a := by positivity
  have hlarge : k<Q*(p*r)^a := by
    have hle := Nat.le_mul_of_pos_left ((p*r)^a) hQ
    have hka : k<a := by dsimp [a]; omega
    omega
  refine ⟨Q*(p*r)^a,hR,dvd_mul_right Q _,hk.trans (by exact_mod_cast hlarge),?_⟩
  intro j hj
  have htower : Tower c d ((p*r)^a) := tower_pow ⟨s,t,rfl⟩ a
  have hj' : j< Q*(p*r)^a ∧ ∃ v : SpanningLinearKernels.augmentedSubmodule (K:=K)
      N L (Q*(p*r)^a), v.val j ≠ v.val (j+P:ℕ) := by
    simpa only [coordinateDefects,Finset.mem_filter,Finset.mem_range] using hj
  apply ha₀ a (by dsimp [a]; omega) j hj'.1
  have hdiff : (Et ((p*r)^a) htower).wordNat j ≠ (Et ((p*r)^a) htower).wordNat (j+P) := by
    apply (word_different_iff (Et ((p*r)^a) htower) j P).mp
    have hh := hj'.2
    rw [Nat.mul_comm Q] at hh
    exact hh
  simpa only [towerWord,dite_eq_left htower,TraceLift.wordNat] using hdiff.symm

#print axioms words_concentrate
#print axioms stationary_concentration

end SpanningClassicalConcentration
