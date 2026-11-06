module

public import SpanningSpectralTracesV1

@[expose] public section

namespace SpanningInitialSpectralVanishing

open SpanningSpectralTraces SpanningSpectralCoordinates SpanningVandermonde
  SpanningActualKernel SpanningWindows SpanningTraceAlgebra

noncomputable def remainingFrequencies (Q:ℕ) (S:Set ℕ) : Finset (Fin Q) :=
  @Finset.filter _ (fun i:Fin Q => ∀q∈S,¬q∣i.val) (Classical.decPred _) Finset.univ

theorem augmented_zero_of_spectral_count {N Q:ℕ} {S:Set ℕ}
    (hQ:0<Q) (hdiv:∀q∈S,q∣Q)
    (hsize:((remainingFrequencies Q S).card:ℝ)<radius N Q 1)
    {K:Type*} [Field K] [CharZero K] {ζ:K} (hζ:IsPrimitiveRoot ζ Q)
    (f:ℤ → K) (hf:Augmented N S Q f) : f=0 := by
  classical
  let z := fun i:Fin Q => ζ^i.val
  have hi : Function.Injective z := fun i j he => Fin.ext (hζ.pow_inj i.isLt j.isLt he)
  have hnz : ∀i,z i≠0 := fun i => pow_ne_zero _ (hζ.ne_zero (Nat.ne_of_gt hQ))
  have hzQ : ∀i,z i^Q=1 := by
    intro i
    dsimp [z]
    rw [←pow_mul,mul_comm i.val Q,pow_mul,hζ.pow_eq_one,one_pow]
  obtain ⟨a,ha,_⟩ := exponential_expansion hQ hi hnz hzQ f hf.1.1
  let R := remainingFrequencies Q S
  have hout : ∀i,i∉R → a i=0 := by
    intro i hnot
    have hh : ¬∀q∈S,¬q∣i.val := by
      intro h
      apply hnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩
    push Not at hh
    obtain ⟨q,hq,hqi⟩ := hh
    apply coefficient_zero_of_trace hQ hζ (hdiv q hq) (i:=i) (hqi:=hqi)
    rw [ha]
    exact hf.2 q hq
  have hfzero : ∀j:ℕ,j<R.card → f j=0 := by
    intro j hj
    have hleg : Legal (radius N Q 1) (j:ℤ) :=
      legal_interval hsize (by omega) (by exact_mod_cast hj)
    have he := hf.1.2 1 (one_dvd Q) j hleg
    simpa [trace] using he
  have ha0 : a=0 := by
    apply sparse_moments_zero hi hnz R (le_refl R.card) hout (s:=0)
    intro j hj
    have he := congrFun ha (j:ℤ)
    simpa only [exponentialWord,zpow_natCast,zero_add] using he.trans (hfzero j hj)
  rw [←ha,ha0]
  funext n
  simp [exponentialWord]

theorem complex_augmented_zero_of_spectral_count {N Q:ℕ} {S:Set ℕ}
    (hQ:0<Q) (hdiv:∀q∈S,q∣Q)
    (hsize:((remainingFrequencies Q S).card:ℝ)<radius N Q 1) :
    ∀f:ℤ → ℂ,Augmented N S Q f → f=0 :=
  augmented_zero_of_spectral_count hQ hdiv hsize
    (Complex.isPrimitiveRoot_exp Q (Nat.ne_of_gt hQ))

#print axioms augmented_zero_of_spectral_count
#print axioms complex_augmented_zero_of_spectral_count

end SpanningInitialSpectralVanishing
