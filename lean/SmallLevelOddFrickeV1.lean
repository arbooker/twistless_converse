module

public import SmallLevelFrickeGeneratorsV1
public import FinitenessOriginalTwistedContinuationsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelGenerators

open Matrix UpperHalfPlane ModularGroup
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

def oddMatrix (N a : ℕ) (ha : 2*a=N+1) : SL(2,ℤ) :=
  ⟨!![(a:ℤ),1;(N:ℤ),2], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
    have hh : 2*(a:ℤ)=(N:ℤ)+1 := by exact_mod_cast ha
    omega⟩

theorem odd_point (N a : ℕ) (ha : 2*a=N+1) (z : ℍ) :
    ((oddMatrix N a ha • z : ℍ):ℂ)=((a:ℂ)*(z:ℂ)+1)/((N:ℂ)*(z:ℂ)+2) := by
  rw [coe_specialLinearGroup_apply]
  simp [oddMatrix]

theorem odd_denom (N a : ℕ) (ha : 2*a=N+1) (z : ℍ) :
    denom (oddMatrix N a ha) z=(N:ℂ)*(z:ℂ)+2 := by
  simp [ModularGroup.denom_apply, oddMatrix]

/-- Comparing the single-term modulus-two twist with the original Fricke
law gives an integral determinant-one transformation at every odd level. -/
theorem odd_of_fricke {N a k : ℕ} (hN : 0<N) (ha : 2*a=N+1)
    (F : ℂ → ℂ) (χ : ℂ)
    (hfr : ∀ z : ℂ, 0<z.im →
      F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (htw : ∀ z : ℂ, 0<z.im →
      F (z+1/2)=χ/((2*(Real.sqrt N:ℂ)*z)^k)*F (-1/(4*(N:ℂ)*z)+1/2)) :
    (fun z : ℍ => F z) ∣[(k:ℤ)] oddMatrix N a ha=(fun z : ℍ => F z) := by
  funext z
  have hn : (N:ℂ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hs : (Real.sqrt N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hz : (z:ℂ)≠0 := z.ne_zero
  have hd : (N:ℂ)*(z:ℂ)+2≠0 := by
    rw [← odd_denom N a ha]
    exact denom_ne_zero _ _
  let w : ℍ := oddMatrix N a ha • z
  let v : ℂ := (w:ℂ)-1/2
  have hvpos : 0<v.im := by simpa [v] using w.im_pos
  have hv0 : v≠0 := by intro h; simp [h] at hvpos
  have hac : 2*(a:ℂ)=(N:ℂ)+1 := by exact_mod_cast ha
  have hv : v=(z:ℂ)/(2*((N:ℂ)*(z:ℂ)+2)) := by
    dsimp only [v, w]
    rw [odd_point]
    calc
      _ = (2*((a:ℂ)*(z:ℂ)+1)-((N:ℂ)*(z:ℂ)+2))/(2*((N:ℂ)*(z:ℂ)+2)) := by
        field_simp [hd]
        field_simp [show (z:ℂ)*(N:ℂ)+2≠0 by simpa only [mul_comm] using hd]
      _ = _ := by
        congr 1
        linear_combination (z:ℂ)*hac
  have hi : -1/(4*(N:ℂ)*v)+1/2= -1/((N:ℂ)*(z:ℂ)) := by
    rw [hv]
    field_simp
    ring
  have hez := hfr z z.im_pos
  have hev := htw v hvpos
  rw [show v+1/2=(w:ℂ) by dsimp [v]; ring, hi] at hev
  have ez : F z*((Real.sqrt N:ℂ)*(z:ℂ))^k=
      χ*F (-1/((N:ℂ)*(z:ℂ))) := by rw [hez]; field_simp
  have ev : F w*(2*(Real.sqrt N:ℂ)*v)^k=
      χ*F (-1/((N:ℂ)*(z:ℂ))) := by rw [hev]; field_simp [hv0, hs]
  have halg : ((N:ℂ)*(z:ℂ)+2)*(2*(Real.sqrt N:ℂ)*v)=
      (Real.sqrt N:ℂ)*(z:ℂ) := by
    rw [hv]
    field_simp [hd]
  have he : F w=F z*((N:ℂ)*(z:ℂ)+2)^k := by
    apply mul_right_cancel₀ (pow_ne_zero k
      (mul_ne_zero (mul_ne_zero (by norm_num : (2:ℂ)≠0) hs) hv0))
    rw [ev, ← ez, mul_assoc, ← mul_pow, halg]
  rw [ModularForm.SL_slash_apply, odd_denom]
  change F w*((N:ℂ)*(z:ℂ)+2)^(-(k:ℤ))=F z
  rw [he, zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hd), mul_one]

theorem original_odd {N a k : ℕ} (hN : 0<N) (ha : 2*a=N+1)
    (hodd : ¬2∣N) {f : ℕ → ℂ} (hf : IsSolution N k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] oddMatrix N a ha=
      SmallLevelOriginal.fourierFunction k f := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  have hr1 : FinitenessNormalizedTwistProduct.root N f 1=1 := by
    simp [FinitenessNormalizedTwistProduct.root]
  have hr2 : FinitenessNormalizedTwistProduct.root N f 2=1 := by
    simp [FinitenessNormalizedTwistProduct.root,
      Nat.prime_two.primeFactors, FinitenessNormalizedTwistLocal.sign, hodd]
  have hcop : Nat.Coprime N 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd).symm
  have hlcm : Nat.lcm N (2^2)=N*4 := by
    simpa using (hcop.pow_right 2).lcm_eq_mul
  have hsqrt : Real.sqrt (N*4:ℕ)=2*Real.sqrt (N:ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
    norm_num
    ring
  apply odd_of_fricke hN ha _ (ε*Complex.I^k)
  · intro z hz
    have h := hlaw 1 (by decide) z hz
    simpa [hr1, FinitenessAnalyticReconstruction.twist, Finset.sum_range_succ] using h
  · intro z hz
    have h := hlaw 2 (by decide) z hz
    have ht (G : ℂ → ℂ) (w : ℂ) :
        FinitenessAnalyticReconstruction.twist G 2 w=G (w+1/2) := by
      unfold FinitenessAnalyticReconstruction.twist
      rw [show (Finset.range 2).filter (fun a => Nat.Coprime a 2)={1} by decide]
      simp
    rw [hr2, one_mul, hlcm, hsqrt, Complex.ofReal_mul, Complex.ofReal_ofNat,
      ht, ht] at h
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm (N:ℂ) 4] using h

#print axioms odd_of_fricke
#print axioms original_odd

end SmallLevelGenerators
