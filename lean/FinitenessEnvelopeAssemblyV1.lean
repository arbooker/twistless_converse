module

public import FinitenessGlobalHeightV1

@[expose] public section

namespace FinitenessEnvelopeAssembly

open FinitenessGlobalHeight FinitenessCertificate FinitenessAnalyticReconstruction
open FinitenessHeightEnvelope

abbrev Point := {z : ℂ // 0 < z.im}

def height (z : Point) : ℝ := z.val.im
noncomputable def value (F : ℂ → ℂ) (b : ℕ) (z : Point) : ℝ :=
  z.val.im^b * ‖F z.val‖

theorem value_nonneg (F : ℂ → ℂ) (b : ℕ) (z : Point) : 0 ≤ value F b z :=
  mul_nonneg (pow_nonneg z.property.le _) (norm_nonneg _)

theorem tail_nonempty (F : ℂ → ℂ) (b : ℕ) (y : ℝ) (hy : 0 < y) :
    (tailSet height (value F b) y).Nonempty := by
  let z : Point := ⟨⟨0,y⟩,hy⟩
  exact ⟨value F b z, z, le_rfl, rfl⟩

theorem envelope_nonneg (F : ℂ → ℂ) (b : ℕ) (y : ℝ) (hy : 0 < y)
    (hb : BddAbove (tailSet height (value F b) y)) :
    0 ≤ envelope height (value F b) y := by
  obtain ⟨a, z, hz, rfl⟩ := tail_nonempty F b y hy
  exact (value_nonneg F b z).trans (le_csSup hb ⟨z, hz, rfl⟩)

/-- All near-boundary growth is forced by the actual FEs. The only
analytic input remaining here is boundedness at each POSITIVE tail height. -/
theorem global_bound {N Q : ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N Q hQ) (P : Parameters A)
    (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (χ : ℕ → ℂ) (m : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
      twist F q z = χ q / (((Real.sqrt (Nat.lcm N (q^2)) : ℝ) : ℂ) * z)^(2*m) *
        twist F q (-1 / ((Nat.lcm N (q^2) : ℕ) * z)))
    (htail : ∀ y : ℝ, 0 < y → ∃ C : ℝ,
      ∀ z : ℂ, y ≤ z.im → z.im^(m+P.s) * ‖F z‖ ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ M = envelope height (value F (m+P.s)) P.ε ∧
      ∀ z : ℂ, 0 < z.im → z.im^(m+P.s) * ‖F z‖ ≤ M := by
  have hb (y : ℝ) (hy : 0 < y) : BddAbove (tailSet height (value F (m+P.s)) y) := by
    obtain ⟨C,hC⟩ := htail y hy
    refine ⟨C,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact hC z.val hz
  have hne := tail_nonempty F (m+P.s)
  have hr : 1 < P.ρ⁻¹ := (one_lt_inv₀ P.rho_pos).mpr P.rho_lt_one
  have hpoint (z : Point) (_hz : 0 < height z) (hze : height z < P.ε) :
      value F (m+P.s) z ≤ envelope height (value F (m+P.s)) (P.ρ⁻¹ * height z) := by
    have ht : 0 < P.ρ⁻¹ * height z := mul_pos (inv_pos.mpr P.rho_pos) z.property
    apply pointwise hN A P F hp χ m hχ hFE z.val z.property hze.le
      (envelope_nonneg F (m+P.s) _ ht (hb _ ht))
    intro w hw
    have hwp : 0 < w.im := (div_pos z.property P.rho_pos).trans_le hw
    exact le_csSup (hb _ ht) ⟨⟨w,hwp⟩, by simpa [height, div_eq_mul_inv, mul_comm] using hw, rfl⟩
  refine ⟨envelope height (value F (m+P.s)) P.ε,
    envelope_nonneg F (m+P.s) P.ε P.epsilon_pos (hb _ P.epsilon_pos), rfl, ?_⟩
  intro z hz
  exact pointwise_global_bound height (value F (m+P.s)) P.epsilon_pos hr hne hb hpoint
    ⟨z,hz⟩ hz

#print axioms global_bound

end FinitenessEnvelopeAssembly
