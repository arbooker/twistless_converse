module

public import AsymptoticClassicalLSeriesV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalLSeries

open UpperHalfPlane Complex MeasureTheory Set

/-- The substitution `t ↦ 1/(N*t)` turns a Fricke relation on the
positive imaginary axis into the Mellin functional equation. -/
theorem mellin_fricke (N : ℝ) (hN : 0 < N) (g : ℝ → ℂ) (k ε : ℂ)
    (hfr : ∀ t : ℝ, 0 < t →
      g ((N*t)⁻¹) = ε * (N : ℂ)^(k/2) * (t : ℂ)^k * g t) (w : ℂ) :
    mellin g w = ε * (N : ℂ)^(k/2-w) * mellin g (k-w) := by
  have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have H : mellin (fun t : ℝ => g ((N*t)⁻¹)) (-w) =
      ε * (N : ℂ)^(k/2) * mellin g (k-w) := by
    calc
      _ = mellin (fun t : ℝ => (ε * (N : ℂ)^(k/2)) • ((t : ℂ)^k • g t)) (-w) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [hfr t ht]
        simp only [smul_eq_mul]
        ring
      _ = _ := by
        rw [mellin_const_smul, mellin_cpow_smul]
        simp only [smul_eq_mul]
        congr 2
        ring
  rw [mellin_comp_mul_left (fun t => g t⁻¹) (-w) hN, mellin_comp_inv,
    neg_neg, smul_eq_mul] at H
  apply mul_left_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hNc) : (N : ℂ)^w ≠ 0)
  rw [H]
  calc
    ε * (N : ℂ)^(k/2) * mellin g (k-w) =
      ε * ((N : ℂ)^w * (N : ℂ)^(k/2-w)) * mellin g (k-w) := by
        rw [← Complex.cpow_add _ _ hNc]
        congr 2
        ring
    _ = _ := by ring

/-- With the conductor normalization in E(N,k), an axial Fricke sign
becomes precisely the reflection `s ↦ 1-s` of the entire completion. -/
theorem entireCompletion_reflection (N k : ℕ) [NeZero N] (hk : 0 < k)
    (f : CuspForm (AsymptoticClassicalCusp.level N) (k : ℤ)) (ε : ℂ)
    (hfr : ∀ t : ℝ, 0 < t →
      f (ofComplex (Complex.I * ((N : ℝ)*t)⁻¹)) =
        ε * (N : ℂ)^((k : ℂ)/2) * (t : ℂ)^(k : ℂ) *
          f (ofComplex (Complex.I*t))) (s : ℂ) :
    entireCompletion N k hk f s = ε * entireCompletion N k hk f (1-s) := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hm := mellin_fricke (N : ℝ) hN (fun t => f (ofComplex (Complex.I*t)))
    (k : ℂ) ε hfr (s + ((k : ℂ)-1)/2)
  simp only [Complex.ofReal_natCast] at hm
  have he (z : ℂ) : ModularForm.Λ (by exact_mod_cast hk) f z =
      mellin (fun t => f (ofComplex (Complex.I*t))) z :=
    congrFun (CuspForm.Λ_eq_mellin (by exact_mod_cast hk) f) z
  unfold entireCompletion
  rw [he, hm, he]
  rw [show (k : ℂ) - (s + ((k : ℂ)-1)/2) = 1-s+((k : ℂ)-1)/2 by ring]
  calc
    _ = ε * (2 * ((N : ℂ)^((s-1/2)/2) *
        (N : ℂ)^((k : ℂ)/2-(s+((k : ℂ)-1)/2))) *
        mellin (fun t => f (ofComplex (Complex.I*t))) (1-s+((k : ℂ)-1)/2)) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hNc]
      congr 3
      ring

#print axioms mellin_fricke
#print axioms entireCompletion_reflection

end AsymptoticClassicalLSeries
