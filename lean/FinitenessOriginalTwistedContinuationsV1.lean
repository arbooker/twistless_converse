module

public import FinitenessNormalizedTwistProductV1
public import FinitenessTwistedAnalyticBridgeV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessOriginalTwistedContinuations

open Complex FinitenessOriginalInput FinitenessNormalizedTwistProduct
  FinitenessTwistedAnalyticBridge FinitenessRamanujanFourier FinitenessInputBounds

/-- Twisting preserves the specified original root number and multiplies
it by the explicit product of ramified local signs. This also covers
identically zero twists, for which a root cannot be recovered by uniqueness. -/
theorem continuation_with_sign {N k : ℕ} {f : ℕ → ℂ} (hN : 0<N)
    (hf : EulerData N f) {q : ℕ} (hq : 0<q)
    (F : ℂ → ℂ) (hFd : Differentiable ℂ F) (hFo : FiniteOrder F)
    {a : ℝ} (hFa : ∀ s : ℂ, a<s.re → F s=completed N k f s)
    (ε : ℂ) (hFE : ∀ s : ℂ, F s=ε*F (1-s)) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ FiniteOrder G ∧
      (∃ c : ℝ, ∀ s : ℂ, c<s.re → G s=completed (Nat.lcm N (q^2)) k (twisted f q) s) ∧
      ∀ s : ℂ, G s=(root N f q*ε)*G (1-s) := by
  obtain ⟨b,hb⟩ := FinitenessTwistedEulerProduct.original_product hf
  refine ⟨fun s => product N f q s*F s,(product_entire N f q).mul hFd,?_,?_,?_⟩
  · exact bound_finiteOrder (FinitenessFiniteOrder.mul (product_bound N f q)
      (finiteOrder_bound hFd.continuous hFo))
  · refine ⟨max a b,fun s hs => ?_⟩
    dsimp only
    rw [hFa s (lt_of_le_of_lt (le_max_left _ _) hs)]
    exact (completed_identity hN hq s
      (hb s (lt_of_le_of_lt (le_max_right _ _) hs) q hq.ne')).symm
  · intro s
    dsimp only
    rw [FinitenessNormalizedTwistProduct.reciprocal hf hN q s,hFE s]
    ring

/-- Every positive literal Ramanujan twist has its required entire
finite-order continuation and real sign, derived from ORIGINAL inputs.
This includes zero twists and imposes no admissibility restriction on N. -/
theorem continuation {N k : ℕ} {f : ℕ → ℂ} (hN : 0<N)
    (hf : IsSolution N k f) {q : ℕ} (hq : 0<q) :
    Continuation (Nat.lcm N (q^2)) k (twisted f q) := by
  obtain ⟨F,hFd,hFo,⟨a,hFa⟩,ε,hε,hFE⟩ := hf.continuation
  obtain ⟨G,hGd,hGo,hGc,hGE⟩ := continuation_with_sign hN hf.toEulerData hq F hFd hFo hFa ε hFE
  refine ⟨G,hGd,hGo,hGc,root N f q*ε,?_,hGE⟩
  rcases root_unit hf.toEulerData q with h|h <;> rcases hε with he|he <;> simp [h,he]

theorem all_twisted {N Q k : ℕ} {f : ℕ → ℂ} (hN : 0<N) (hQ : 0<Q)
    (hf : IsSolution N k f) : TwistedContinuations N Q k f :=
  fun _ hq => continuation hN hf (Nat.pos_of_dvd_of_pos hq hQ)

/-- One original root number determines every positive twist law. The
local multiplier is the explicit Euler-product root, rather than a newly
chosen sign for each modulus. -/
theorem coherent_solution_laws {N k : ℕ} {f : ℕ → ℂ} (hN : 0<N)
    (hf : IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ q : ℕ, 0<q → ∀ z : ℂ, 0<z.im →
      FinitenessAnalyticReconstruction.twist
        (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k)) q z=
      (root N f q*ε*I^k)/((((Real.sqrt (Nat.lcm N (q^2)):ℝ):ℂ)*z)^k)*
        FinitenessAnalyticReconstruction.twist
          (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
          q (-1/((Nat.lcm N (q^2):ℕ)*z)) := by
  obtain ⟨F,hFd,hFo,⟨a,hFa⟩,ε,hε,hFE⟩ := hf.continuation
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨ε,hε,?_⟩
  intro q hq z hz
  obtain ⟨G,hGd,hGo,⟨c,hGc⟩,hGE⟩ :=
    continuation_with_sign hN hf.toEulerData hq F hFd hFo hFa ε hFE
  have hrnorm : ‖root N f q*ε‖=1 := by
    rcases root_unit hf.toEulerData q with h|h <;> rcases hε with he|he <;> simp [h,he]
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  have he := FinitenessOriginalFricke.fricke_with_sign hL (twisted_zero hf.zero q)
    (twisted_growth hg q) G hGd hGo hGc hrnorm hGE z hz
  have hr : 0<(-1/((Nat.lcm N (q^2):ℕ)*z)).im := by
    simpa only [ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L:=(Nat.lcm N (q^2):ℝ)) (by exact_mod_cast hL) hz
  simpa only [fourier_twisted hf.zero hg q k hz,fourier_twisted hf.zero hg q k hr] using he

/-- The original Euler-product/Dirichlet hypotheses now imply every
literal holomorphic row law needed by the checked finite-dimensional space.
There is no remaining assumed twisted functional equation. -/
theorem solution_laws {N Q m : ℕ} {f : ℕ → ℂ} (hN : 0<N) (hQ : 0<Q)
    (hf : IsSolution N (2*m) f) :
    ∃ χ : ℕ → ℂ, (∀ q, χ q=I^(2*m) ∨ χ q= -I^(2*m)) ∧
      (∀ q, ‖χ q‖=1) ∧
      FinitenessHolomorphicSpace.Laws N Q χ m
        (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f (2*m))) := by
  obtain ⟨ε,hε,he⟩ := coherent_solution_laws hN hf
  refine ⟨fun q => root N f q*ε*I^(2*m),?_,?_,?_⟩
  · intro q
    rcases root_unit hf.toEulerData q with h|h <;> rcases hε with h'|h' <;> simp [h,h']
  · intro q
    rcases root_unit hf.toEulerData q with h|h <;> rcases hε with h'|h' <;> simp [h,h']
  · intro q hq
    exact he q (Nat.pos_of_dvd_of_pos hq hQ)

#print axioms continuation
#print axioms continuation_with_sign
#print axioms coherent_solution_laws
#print axioms all_twisted
#print axioms solution_laws

end FinitenessOriginalTwistedContinuations
