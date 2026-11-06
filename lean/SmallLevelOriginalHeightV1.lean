module

public import FinitenessAllLevelAutomaticGrowthV1
public import SmallLevelOriginalV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open FinitenessAllLevelGlobalHeight FinitenessOriginalInput

/-- The previously checked original-input reconstruction gives one global
inverse-height bound. Its exponent and constant may depend on the solution. -/
theorem inverse_height_bound {N p : ℕ} (hN : 0<N) (hp : p.Prime)
    (hgood : ¬p∣N) (hlarge : N<p^2) {m : ℕ} {f : ℕ → ℂ}
    (hf : IsSolution N (2*m) f) :
    ∃ b : ℕ, ∃ M : ℝ, 0≤M ∧ ∀ z : UpperHalfPlane,
      z.im^b*‖fourierFunction (2*m) f z‖≤M := by
  obtain ⟨Q,hQ,_hNQ,hpQ,⟨A⟩⟩ :=
    FinitenessAllLevelAuxiliary.certificate_at_prime hN hp hlarge
  obtain ⟨P⟩ := parameters_exist hN hQ A (norm_nonneg (f p))
  obtain ⟨M,hM,hb⟩ := FinitenessAllLevelAutomaticGrowth.original_height hN A P
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using And.intro hp hgood)
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using hpQ) hf
    (by intro q hq; simpa only [Finset.mem_singleton.mp hq] using (le_rfl : ‖f p‖≤‖f p‖))
  exact ⟨m+P.s,M,hM,fun z => hb z z.im_pos⟩

#print axioms inverse_height_bound

end SmallLevelOriginal
