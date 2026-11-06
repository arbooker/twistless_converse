module

public import SmallLevelRamifiedTwoMatrixV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelRamifiedTwo

open Matrix UpperHalfPlane
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

/-- The coherent original and modulus-two Fricke identities give the
normalized Atkin-Lehner eigenmatrix, without dividing by a root number. -/
theorem eigen_of_fricke {N a k : ℕ} (hN : 0<N) (ha : 2*a=N+2)
    (F : ℂ → ℂ) (χ δ : ℂ)
    (hfr : ∀ z : ℂ, 0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (htw : ∀ z : ℂ, 0<z.im → F (z+1/2)=
      (δ*χ)/(((Real.sqrt 2:ℂ)*(Real.sqrt N:ℂ)*z)^k)*F (-1/(2*(N:ℂ)*z)+1/2)) :
    (fun z : ℍ => F z) ∣[(k:ℤ)] Q N a ha=δ • (fun z : ℍ => F z) := by
  funext z
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hs : (Real.sqrt N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have ht : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr sqrt_two_ne
  have hz : (z:ℂ)≠0 := z.ne_zero
  have hd : (N:ℂ)*(z:ℂ)+2≠0 := by
    have hh := denom_ne_zero (Q N a ha) z
    rw [Q_denom] at hh
    exact (div_ne_zero_iff.mp hh).1
  let w : ℍ := Q N a ha • z
  let v : ℂ := (w:ℂ)-1/2
  have hvpos : 0<v.im := by simpa [v] using w.im_pos
  have hv0 : v≠0 := by intro h; simp [h] at hvpos
  have hac : 2*(a:ℂ)=(N:ℂ)+2 := by exact_mod_cast ha
  have hv : v=(z:ℂ)/((N:ℂ)*(z:ℂ)+2) := by
    dsimp only [v, w]
    rw [Q_point]
    calc
      _ = (2*((a:ℂ)*(z:ℂ)+1)-((N:ℂ)*(z:ℂ)+2))/(2*((N:ℂ)*(z:ℂ)+2)) := by
        field_simp [hd]
        field_simp [show (z:ℂ)*(N:ℂ)+2≠0 by simpa only [mul_comm] using hd]
      _ = _ := by
        rw [show 2*((a:ℂ)*(z:ℂ)+1)-((N:ℂ)*(z:ℂ)+2)=2*(z:ℂ) by
          linear_combination (z:ℂ)*hac]
        field_simp
  have hi : -1/(2*(N:ℂ)*v)+1/2= -1/((N:ℂ)*(z:ℂ)) := by
    rw [hv]
    field_simp
    ring
  have hez := hfr z z.im_pos
  have hev := htw v hvpos
  rw [show v+1/2=(w:ℂ) by dsimp [v]; ring, hi] at hev
  have ez : F z*((Real.sqrt N:ℂ)*(z:ℂ))^k=χ*F (-1/((N:ℂ)*(z:ℂ))) := by
    rw [hez]; field_simp
  have ev : F w*((Real.sqrt 2:ℂ)*(Real.sqrt N:ℂ)*v)^k=
      (δ*χ)*F (-1/((N:ℂ)*(z:ℂ))) := by
    rw [hev]; field_simp [hv0, hs, ht]
  have halg : (((N:ℂ)*(z:ℂ)+2)/(Real.sqrt 2:ℂ))*
      ((Real.sqrt 2:ℂ)*(Real.sqrt N:ℂ)*v)=(Real.sqrt N:ℂ)*(z:ℂ) := by
    rw [hv]
    field_simp [hd, ht]
  have he : F w=δ*F z*(((N:ℂ)*(z:ℂ)+2)/(Real.sqrt 2:ℂ))^k := by
    apply mul_right_cancel₀ (pow_ne_zero k (mul_ne_zero (mul_ne_zero ht hs) hv0))
    calc
      _ = δ*(F z*((Real.sqrt N:ℂ)*(z:ℂ))^k) := by rw [ev, ez]; ring
      _ = _ := by rw [mul_assoc, ← mul_pow, halg]; ring
  rw [Q_slash]
  change F w*(((N:ℂ)*(z:ℂ)+2)/(Real.sqrt 2:ℂ))^(-(k:ℤ))=δ*F z
  rw [he, zpow_neg, zpow_natCast, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero k (div_ne_zero hd ht)), mul_one]

/-- The actual modulus-two eigenlaw with its original root sign. The
conductor equality holds at every level congruent to two modulo four. -/
theorem original_eigen {N a k : ℕ} (hN : 0<N) (ha : 2*a=N+2)
    (hL : Nat.lcm N (2^2)=2*N) {f : ℕ → ℂ} (hf : IsSolution N k f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
      SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] Q N a ha=
        δ • SmallLevelOriginal.fourierFunction k f := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  refine ⟨FinitenessNormalizedTwistProduct.root N f 2,
    FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2, ?_⟩
  apply eigen_of_fricke hN ha _ (ε*Complex.I^k)
  · intro z hz
    have h := hlaw 1 (by decide) z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using h
  · intro z hz
    have h := hlaw 2 (by decide) z hz
    have ht (G : ℂ → ℂ) (w : ℂ) :
        FinitenessAnalyticReconstruction.twist G 2 w=G (w+1/2) := by
      unfold FinitenessAnalyticReconstruction.twist
      rw [show (Finset.range 2).filter (fun a => Nat.Coprime a 2)={1} by decide]
      simp
    have hsqrt : Real.sqrt (2*N:ℕ)=Real.sqrt 2*Real.sqrt (N:ℝ) := by
      rw [Nat.cast_mul, Real.sqrt_mul (by norm_num)]
      norm_num
    rw [hL, hsqrt, Complex.ofReal_mul, ht, ht] at h
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h

#print axioms eigen_of_fricke
#print axioms original_eigen

end SmallLevelRamifiedTwo
