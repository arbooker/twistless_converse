module

public import FinitenessAllLevelHolomorphicSpaceV1
public import FinitenessSignPatternsV1
public import FinitenessFiniteUnionV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelEigenvalueFibers

open Complex FinitenessOriginalInput FinitenessOriginalDiskIndependence
  FinitenessFourierConstruction FinitenessOriginalFourier
  FinitenessAllLevelHolomorphicSpace QuantitativeArithmeticRetainedReconstruction

/-- Original Euler solutions with one prescribed unramified coefficient. -/
def fiber (N k p : ℕ) (a : ℂ) : Set (ℕ → ℂ) :=
  {f | IsSolution N k f ∧ f p = a}

def toSolution {N k p : ℕ} {a : ℂ} (f : fiber N k p a) : S N k :=
  ⟨f.val, f.property.1⟩

theorem toSolution_injective {N k p : ℕ} {a : ℂ} :
    Function.Injective (toSolution (N := N) (k := k) (p := p) (a := a)) := by
  intro f g h
  exact Subtype.ext (congrArg (fun x : S N k => x.val) h)

theorem independent {N k p : ℕ} {a : ℂ} :
    LinearIndependent ℂ (fun f : fiber N k p a => representative N k (toSolution f)) :=
  (FinitenessOriginalDiskIndependence.independent N k).comp
    toSolution toSolution_injective

theorem complete_laws {N m p : ℕ} (f : S N (2 * m)) (hp : p.Prime)
    (hgood : ¬ p ∣ N) {a : ℂ} (ha : f.val p = a) :
    CompleteLaws {p} (fun _ => a) m
      (FinitenessHolomorphicSpace.lift (representative N (2 * m) f).val) := by
  intro q hq z hz
  have hqp := Finset.mem_singleton.mp hq
  subst q
  have hlift (w : ℂ) (hw : 0 < w.im) :
      FinitenessHolomorphicSpace.lift (representative N (2 * m) f).val w =
        fourier (fullCoefficients f.val (2 * m)) w := disk_eq_fourier _ hw
  have htrace : completeTwist
      (FinitenessHolomorphicSpace.lift (representative N (2 * m) f).val) p z =
      completeTwist (fourier (fullCoefficients f.val (2 * m))) p z := by
    unfold completeTwist
    apply Finset.sum_congr rfl
    intro b _
    apply hlift
    simpa using hz
  have hz1 := QuantitativeArithmeticRamifiedFullTrace.dilation_height hp.pos hz
  have hz2 : 0 < ((p : ℂ) ^ 2 * z).im := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (pow_pos (by exact_mod_cast hp.pos) 2) hz
  rw [htrace, hlift _ hz1, hlift _ hz2]
  simpa only [FinitenessAllLevelGoodTrace.firstMultiplier, ha] using
    FinitenessAllLevelGoodTrace.original_complete_even f.property.toEulerData hp hgood m hz

theorem cover {N Q m p : ℕ} (hN : 0 < N) (hQ : 0 < Q)
    (hp : p.Prime) (hgood : ¬ p ∣ N) {a : ℂ} (f : fiber N (2 * m) p a) :
    ∃ e : FinitenessSignPatterns.Pattern Q,
      representative N (2 * m) (toSolution f) ∈
        space N Q {p} (FinitenessSignPatterns.multiplier Q m e) (fun _ => a) m := by
  obtain ⟨e, he⟩ := FinitenessSignPatterns.cover hN hQ (toSolution f)
  exact ⟨e, he, complete_laws (toSolution f) hp hgood f.property.2⟩

/-- Each fixed-eigenvalue fiber is finite. The same constant bounds all
fibers in |a| <= L and all positive even weights, at every positive level.
This does not assert that the union over a is finite. -/
theorem uniform_fiber_bound {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℕ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ a : ℂ, ‖a‖ ≤ L →
      (fiber N (2 * m) p a).Finite ∧ (fiber N (2 * m) p a).ncard ≤ C * m := by
  classical
  obtain ⟨Q, C, hQ, _hNQ, _hpQ, hC, hd⟩ := good_prime_level hN hp hlarge hL
  refine ⟨2 ^ (Q + 1) * C, Nat.mul_pos (pow_pos (by norm_num) _) hC, ?_⟩
  intro m hm a ha
  let W : FinitenessSignPatterns.Pattern Q → Submodule ℂ FinitenessDiskJet.space :=
    fun e => space N Q {p} (FinitenessSignPatterns.multiplier Q m e) (fun _ => a) m
  have hdim (e : FinitenessSignPatterns.Pattern Q) :
      FiniteDimensional ℂ (W e) ∧ Module.finrank ℂ (W e) ≤ C * m :=
    hd (FinitenessSignPatterns.multiplier Q m e) (fun _ => a) m hm
      (fun q _ => FinitenessSignPatterns.unit_norm Q m e q) ha
  let inst : ∀ e, FiniteDimensional ℂ (W e) := fun e => (hdim e).1
  obtain ⟨hfinite, hcard⟩ := FinitenessFiniteUnion.bound W
    (fun f : fiber N (2 * m) p a => representative N (2 * m) (toSolution f))
    independent (cover hN hQ hp hgood) (C * m) (fun e => (hdim e).2)
  refine ⟨Set.finite_coe_iff.mp hfinite, ?_⟩
  simpa only [Nat.card_coe_set_eq, FinitenessSignPatterns.card, Nat.mul_assoc] using hcard

#print axioms complete_laws
#print axioms cover
#print axioms uniform_fiber_bound

end FinitenessAllLevelEigenvalueFibers
