module

public import SmallLevelThreeBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThree

open Complex UpperHalfPlane FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction FinitenessAnalyticReconstruction

theorem twist_three (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (z : ℂ) :
    twist F 3 z=F (z+1/3)+F (z-1/3) := by
  unfold twist
  rw [show (Finset.range 3).filter (fun a => Nat.Coprime a 3)={1,2} by decide]
  norm_num
  rw [show z+2/3=(z-1/3)+1 by ring, hp]

/-- Coherent one- and three-twist laws, with exactly the same original
root. The good-prime condition is the only arithmetic restriction. -/
theorem original_three_laws {N k : ℕ} (hN : 0<N) (hgood : ¬3∣N)
    {f : ℕ → ℂ} (hf : IsSolution N k f) :
    ∃ χ : ℂ,
      (∀ z : ℂ, 0<z.im → fourier (fullCoefficients f k) z=
        χ/(((Real.sqrt N:ℂ)*z)^k)*fourier (fullCoefficients f k) (-1/((N:ℂ)*z))) ∧
      ∀ z : ℂ, 0<z.im →
        fourier (fullCoefficients f k) ((z+1)/3)+fourier (fullCoefficients f k) ((z-1)/3)=
        χ/(((Real.sqrt N:ℂ)*z)^k)*
          (fourier (fullCoefficients f k) (-1/(3*(N:ℂ)*z)+1/3)+
           fourier (fullCoefficients f k) (-1/(3*(N:ℂ)*z)-1/3)) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  have hr1 : FinitenessNormalizedTwistProduct.root N f 1=1 := by
    simp [FinitenessNormalizedTwistProduct.root]
  have hr3 : FinitenessNormalizedTwistProduct.root N f 3=1 := by
    simp [FinitenessNormalizedTwistProduct.root,
      (by decide : Nat.Prime 3).primeFactors, FinitenessNormalizedTwistLocal.sign, hgood]
  have hcop : Nat.Coprime N 3 :=
    (((by decide : Nat.Prime 3).coprime_iff_not_dvd).mpr hgood).symm
  have hlcm : Nat.lcm N (3^2)=N*9 := by simpa using (hcop.pow_right 2).lcm_eq_mul
  have hsqrt : Real.sqrt (N*9:ℕ)=3*Real.sqrt (N:ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
    norm_num
    ring
  refine ⟨ε*Complex.I^k,?_,?_⟩
  · intro z hz
    simpa [hr1, twist, Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 3 (by decide) (z/3)
      (by simpa using div_pos hz (by norm_num : (0:ℝ)<3))
    rw [hr3, one_mul, hlcm, hsqrt, ofReal_mul, ofReal_ofNat,
      twist_three _ (periodic _), twist_three _ (periodic _)] at h
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
    rw [show (3*(Real.sqrt N:ℂ))*(z/3)=(Real.sqrt N:ℂ)*z by ring,
      show -1/(((N:ℂ)*9)*(z/3))= -1/(3*(N:ℂ)*z) by ring] at h
    rw [show (z+1)/3=z/3+1/3 by ring,
      show (z-1)/3=z/3-1/3 by ring]
    exact h

/-- The actual two-branch identity from the original Euler hypotheses.
It is valid at zero Hecke eigenvalue and requires no modularity premise. -/
theorem original_pair {N k : ℕ} (hN : 0<N) (hgood : ¬3∣N)
    {f : ℕ → ℂ} (hf : IsSolution N k f) (z : ℍ) :
    fourier (fullCoefficients f k) (((z:ℂ)+1)/3)+
      fourier (fullCoefficients f k) (((z:ℂ)-1)/3)=
    (3:ℂ)^k*(fourier (fullCoefficients f k) ((lowerBranch N 1 • z : ℍ):ℂ)/((N:ℂ)*(z:ℂ)+1)^k)+
    (3:ℂ)^k*(fourier (fullCoefficients f k) ((lowerBranch N (-1) • z : ℍ):ℂ)/(-(N:ℂ)*(z:ℂ)+1)^k) := by
  obtain ⟨χ,hfr,htw⟩ := original_three_laws hN hgood hf
  have hplus := lowerBranch_fricke hN _ χ hfr 1 z
  have hminus := lowerBranch_fricke hN _ χ hfr (-1) z
  norm_num only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, sub_neg_eq_add] at hplus hminus
  rw [hplus, hminus, htw z z.im_pos]
  ring

#print axioms original_three_laws
#print axioms original_pair

end SmallLevelThree
