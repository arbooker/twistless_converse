module

public import QuantitativeNinaMaassTraceDiamondsV1
public import AsymptoticClassicalBadHeckeLowerV1
public import AsymptoticClassicalLocalAtkinTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Matrix UpperHalfPlane ConjAct
open QuantitativeMaass AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticClassicalCusp AsymptoticClassicalCosets AsymptoticCongruenceLabels
open AsymptoticClassicalDiscriminant AsymptoticAtkinLehner
open scoped Pointwise MatrixGroups

/-!
The ramified correspondence uses literal weight-zero pullback sums. The
group/coset identities are reused, but no holomorphic cusp-form statement
is applied to a Maass function. This draft first establishes the vanishing
of the actual upper-branch sum at square divisors of the level. The simple
ramified square relation is obtained from the same two trace equations.
Normalized Fourier amplitudes remain a later obligation.
-/

namespace QuantitativeNinaMaass

theorem matrixPullbackTrace_congr {G G' H H' : Subgroup (GL (Fin 2) ℝ)}
    [G.IsArithmetic] [G'.IsArithmetic] [H.IsArithmetic] [H'.IsArithmetic]
    (hG : G = G') (hH : H = H') (f : ℍ → ℂ)
    (hf : ∀ a : G, ∀ z : ℍ, f (a.val • z) = f z)
    (hf' : ∀ a : G', ∀ z : ℍ, f (a.val • z) = f z) :
    matrixPullbackTrace G H f hf = matrixPullbackTrace G' H' f hf' := by
  subst G'
  subst H'
  rfl

theorem matrixPullback_invariant (G : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℝ)
    (f : ℍ → ℂ) (hf : ∀ a : G, ∀ z : ℍ, f (a.val • z) = f z) :
    ∀ a : ↥(toConjAct g⁻¹ • G), ∀ z : ℍ,
      f (g • (a.val • z)) = f (g • z) := by
  rintro ⟨_, a, ha, rfl⟩ z
  change f (g • ((g⁻¹ * a * g) • z)) = f (g • z)
  simp only [mul_smul, smul_inv_smul]
  exact hf ⟨a, ha⟩ (g • z)

/-- Conjugation covariance for the literal weight-zero finite trace. -/
theorem matrixPullbackTrace_translate (G H : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [H.IsArithmetic] (g : GL (Fin 2) ℝ)
    [(toConjAct g⁻¹ • G).IsArithmetic] [(toConjAct g⁻¹ • H).IsArithmetic]
    (f : ℍ → ℂ) (hf : ∀ a : G, ∀ z : ℍ, f (a.val • z) = f z) (z : ℍ) :
    matrixPullbackTrace (toConjAct g⁻¹ • G) (toConjAct g⁻¹ • H)
      (fun w => f (g • w)) (matrixPullback_invariant G g f hf) z =
        matrixPullbackTrace G H f hf (g • z) := by
  classical
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  let := conjugate_finiteRelIndex G H g
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  let := Fintype.ofFinite
    (↥(toConjAct g⁻¹ • H) ⧸ (toConjAct g⁻¹ • G).subgroupOf (toConjAct g⁻¹ • H))
  change (∑ q : ↥(toConjAct g⁻¹ • H) ⧸
    (toConjAct g⁻¹ • G).subgroupOf (toConjAct g⁻¹ • H), CosetTrace.value _ _ _ q z) =
      ∑ q : H ⧸ G.subgroupOf H, CosetTrace.value _ _ _ q (g • z)
  rw [← (conjugateTraceEquiv G H g).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h a =>
    rw [show conjugateTraceEquiv G H g (QuotientGroup.mk a) =
      QuotientGroup.mk (imageRepresentative (conjugationHom g) H
        (toConjAct g⁻¹ • H) rfl a) from imageEquivOfEq_mk ..]
    change f (g • ((g⁻¹ * a.val * g)⁻¹ • z)) = f (a.val⁻¹ • (g • z))
    simp only [_root_.mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]

/-- The actual p upper branches, before their Maass normalization. -/
def upperBranchSum (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  ∑ a : Fin p, f (triangularGL 1 (a.val : ℤ) p (by norm_num) (by exact_mod_cast hp) • z)

def normalizedUpperBranches (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) * upperBranchSum p hp f z

theorem upperBranchSum_const_mul (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (c : ℂ) (z : ℍ) :
    upperBranchSum p hp (fun w => c * f w) z = c * upperBranchSum p hp f z := by
  simp only [upperBranchSum, Finset.mul_sum]

/-- The p+1 ordinary trace cosets at a simple prime, on arbitrary
invariant functions with no holomorphic structure. -/
theorem matrixPullbackTrace_prime_sum (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (hpM : ¬ p ∣ M) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : ℍ → ℂ) (hf : ∀ a : level (p * M), ∀ z : ℍ, f (a.val • z) = f z) (z : ℍ) :
    matrixPullbackTrace (level (p * M)) (level M) f hf z =
      f z + ∑ a : Fin p, f (SpecialLinearGroup.mapGL ℝ (traceSL M p A B hAB a.val) • z) := by
  classical
  let : (level (p * M)).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let := Fintype.ofFinite (level M ⧸ (level (p * M)).subgroupOf (level M))
  let e := (traceCosetEquiv M p hM hpM A B hAB).trans (traceEquiv (p * M) M).symm
  have hn : CosetTrace.value ((level (p * M)).subgroupOf (level M)) f
      (fun a w => hf ⟨a.val.val, a.property⟩ w) (e none) z = f z := by
    have he : e none = QuotientGroup.mk
        ((SpecialLinearGroup.mapGL ℝ).subgroupMap (CongruenceSubgroup.Gamma0 M) 1) := by
      apply (traceEquiv (p * M) M).injective
      rw [traceEquiv_mk]
      change (traceEquiv (p * M) M) ((traceEquiv (p * M) M).symm _) = _
      rw [Equiv.apply_symm_apply]
      change QuotientGroup.mk (1 : gamma M) =
        QuotientGroup.mk (integralLabel.subgroupMap (CongruenceSubgroup.Gamma0 M) 1)
      rw [map_one]
    rw [he]
    change f ((SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℤ)))⁻¹ • z) = f z
    rw [map_one, inv_one, one_smul]
  have hs (a : Fin p) : CosetTrace.value ((level (p * M)).subgroupOf (level M)) f
      (fun a w => hf ⟨a.val.val, a.property⟩ w) (e (some a)) z =
        f (SpecialLinearGroup.mapGL ℝ (traceSL M p A B hAB a.val) • z) := by
    let t : CongruenceSubgroup.Gamma0 M :=
      ⟨traceSL M p A B hAB a.val, traceSL_mem M p A B hAB a.val⟩
    have he : e (some a) = QuotientGroup.mk
        ((SpecialLinearGroup.mapGL ℝ).subgroupMap (CongruenceSubgroup.Gamma0 M) t⁻¹) := by
      apply (traceEquiv (p * M) M).injective
      rw [traceEquiv_mk]
      change (traceEquiv (p * M) M) ((traceEquiv (p * M) M).symm _) = _
      rw [Equiv.apply_symm_apply]
      change QuotientGroup.mk (traceRepresentative M p A B hAB (some a)) = _
      congr 1
      apply Subtype.ext
      exact (map_inv integralLabel _).symm
    rw [he]
    change f ((SpecialLinearGroup.mapGL ℝ (traceSL M p A B hAB a.val)⁻¹)⁻¹ • z) = _
    rw [map_inv, inv_inv]
  change (∑ q : level M ⧸ (level (p * M)).subgroupOf (level M),
    CosetTrace.value _ _ _ q z) = _
  rw [← e.sum_comp, Fintype.sum_option, hn]
  exact congrArg (fun w => f z + w) (Finset.sum_congr rfl (fun a _ => hs a))

theorem localAtkin_pullback_invariant (M p : ℕ) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : ℍ → ℂ) (hf : ∀ a : level (p * M), ∀ z : ℍ, f (a.val • z) = f z) :
    ∀ a : level (p * M), ∀ z : ℍ,
      f (localAtkinReal M p hp A B hAB • (a.val • z)) =
        f (localAtkinReal M p hp A B hAB • z) := by
  intro a z
  exact matrixPullback_invariant (level (p * M)) (localAtkinReal M p hp A B hAB) f hf
    ⟨a.val, by rw [localAtkinReal_normalizes]; exact a.property⟩ z

theorem localAtkin_pullback_square (M p : ℕ) (hp : 0 < p) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : ℍ → ℂ) (hf : ∀ a : level (p * M), ∀ z : ℍ, f (a.val • z) = f z) (z : ℍ) :
    f (localAtkinReal M p hp A B hAB • (localAtkinReal M p hp A B hAB • z)) = f z := by
  rw [← mul_smul, localAtkinReal_square, mul_smul, UpperHalfPlane.glScalar_smul]
  exact hf ⟨_, ⟨_, localSquare_mem M p A B hAB, rfl⟩⟩ z

/-- Weight-zero I + WU identity; normalization is introduced only after
this literal identity of finite sums. -/
theorem upperBranchSum_localAtkin (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (hpM : ¬ p ∣ M) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : ℍ → ℂ) (hf : ∀ a : level (p * M), ∀ z : ℍ, f (a.val • z) = f z) (z : ℍ) :
    upperBranchSum p (Fact.out : p.Prime).pos
      (fun w => f (localAtkinReal M p (Fact.out : p.Prime).pos A B hAB • w)) z =
        matrixPullbackTrace (level (p * M)) (level M) f hf z - f z := by
  rw [matrixPullbackTrace_prime_sum M p hM hpM A B hAB, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  rw [← mul_smul, localAtkin_upper_branch, mul_smul,
    ← scalar_eq_positiveScalarReal, UpperHalfPlane.glScalar_smul]

theorem localAtkin_pullback_trace_zero (M p : ℕ) [NeZero M] [NeZero p]
    (hp : 0 < p) (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : ℍ → ℂ) (hf : ∀ a : level (p * M), ∀ z : ℍ, f (a.val • z) = f z)
    (hz : matrixPullbackTrace (level (p * M)) (dilationLevel M p hp) f hf = 0) :
    matrixPullbackTrace (level (p * M)) (level M)
      (fun w => f (localAtkinReal M p hp A B hAB • w))
      (localAtkin_pullback_invariant M p hp A B hAB f hf) = 0 := by
  let g := localAtkinReal M p hp A B hAB
  have hG : toConjAct g⁻¹ • level (p * M) = level (p * M) :=
    localAtkinReal_normalizes M p hp A B hAB
  have hH : toConjAct g⁻¹ • dilationLevel M p hp = level M :=
    localAtkinReal_oldGroup_back M p hp A B hAB
  let : (toConjAct g⁻¹ • level (p * M)).IsArithmetic := by rw [hG]; infer_instance
  let : (toConjAct g⁻¹ • dilationLevel M p hp).IsArithmetic := by rw [hH]; infer_instance
  funext z
  have h := matrixPullbackTrace_translate (level (p * M)) (dilationLevel M p hp) g f hf z
  rw [hz] at h
  have hc := matrixPullbackTrace_congr hG hH (fun w => f (g • w))
    (matrixPullback_invariant (level (p * M)) g f hf)
    (localAtkin_pullback_invariant M p hp A B hAB f hf)
  exact (congrFun hc z).symm.trans h

/-- The second trace equation gives the negative local involution before
the factor p^(-1/2) is applied. -/
theorem upperBranchSum_simple_eq_neg_local (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (hpM : ¬ p ∣ M) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : ℍ → ℂ) (hf : ∀ a : level (p * M), ∀ z : ℍ, f (a.val • z) = f z)
    (hz : matrixPullbackTrace (level (p * M))
      (dilationLevel M p (Fact.out : p.Prime).pos) f hf = 0) (z : ℍ) :
    upperBranchSum p (Fact.out : p.Prime).pos f z =
      -f (localAtkinReal M p (Fact.out : p.Prime).pos A B hAB • z) := by
  let hp := (Fact.out : p.Prime).pos
  let g := localAtkinReal M p hp A B hAB
  have h := upperBranchSum_localAtkin M p hM hpM A B hAB (fun w => f (g • w))
    (localAtkin_pullback_invariant M p hp A B hAB f hf) z
  have hs : (fun w => f (g • (g • w))) = f :=
    funext (localAtkin_pullback_square M p hp A B hAB f hf)
  rw [hs, localAtkin_pullback_trace_zero M p hp A B hAB f hf hz] at h
  simpa only [Pi.zero_apply, zero_sub] using h

theorem continuous_new_dilation_trace_zero (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : 0 < p)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val)
    (hnew : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel (Nat.mul_pos hp hM) (Nat.dvd_mul_left M p)) :
    matrixPullbackTrace (level (p * M)) (dilationLevel M p hp) f.val
      (representative_matrix_invariant (p * M) f) = 0 := by
  have hz := (continuous_fricke_trace_zero_iff (Nat.mul_pos hp hM)
    (Nat.dvd_mul_left M p) f hf).mp hnew.2
  have he := matrixPullbackTrace_target_congr (level (p * M))
    (frickeOldLevel (p * M) M (Nat.mul_pos hp hM)) (dilationLevel M p hp)
    (frickeOldLevel_eq_dilationLevel M p hM hp) f.val
    (representative_matrix_invariant (p * M) f)
  exact he.symm.trans hz

/-- Both physical trace equations imply the precise simple-ramified
square factor 1/p for the actual normalized upper-branch operator. -/
theorem normalizedUpperBranches_simple_square (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hM : 0 < M) (hpM : ¬ p ∣ M) (A B : ℤ)
    (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val)
    (hnew : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel (Nat.mul_pos (Fact.out : p.Prime).pos hM) (Nat.dvd_mul_left M p))
    (z : ℍ) :
    normalizedUpperBranches p (Fact.out : p.Prime).pos
      (normalizedUpperBranches p (Fact.out : p.Prime).pos f.val) z = (p : ℂ)⁻¹ * f.val z := by
  let hp := (Fact.out : p.Prime).pos
  let g := localAtkinReal M p hp A B hAB
  let hi := representative_matrix_invariant (p * M) f
  have hfirst : matrixPullbackTrace (level (p * M)) (level M) f.val hi = 0 := by
    rw [matrixPullbackTrace_level (Nat.dvd_mul_left M p)]
    exact (continuous_trace_zero_iff (Nat.dvd_mul_left M p) f hf).mp hnew.1
  have hsecond : matrixPullbackTrace (level (p * M)) (dilationLevel M p hp) f.val hi = 0 := by
    exact continuous_new_dilation_trace_zero M p hM hp f hf hnew
  have hu : upperBranchSum p hp f.val = fun w => -f.val (g • w) :=
    funext (upperBranchSum_simple_eq_neg_local M p hM hpM A B hAB f.val hi hsecond)
  have huw := upperBranchSum_localAtkin M p hM hpM A B hAB f.val hi z
  rw [hfirst] at huw
  have hsquare : upperBranchSum p hp (upperBranchSum p hp f.val) z = f.val z := by
    rw [hu]
    rw [show (fun w => -f.val (g • w)) = (fun w => (-1 : ℂ) * f.val (g • w)) by
      funext w; ring]
    rw [upperBranchSum_const_mul, huw]
    simp
  let c : ℂ := (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ)
  have hc : c * c = (p : ℂ)⁻¹ := by
    change (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity),
      Complex.ofReal_inv, Complex.ofReal_natCast]
  change c * upperBranchSum p hp (fun w => c * upperBranchSum p hp f.val w) z = _
  rw [upperBranchSum_const_mul, hsquare, ← mul_assoc, hc]

/-- A representative-compatible coset bijection identifies the actual
upper-branch sum with the trace of the pulled-back function. -/
theorem matrixPullbackTrace_upper_cosets (N M p : ℕ) [NeZero N] [NeZero M]
    (hp : 0 < p)
    (e : Fin p ≃ level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M))
    (he : ∀ a, e a = QuotientGroup.mk (upperRepresentative M a.val))
    (f : ℍ → ℂ) (hf : ∀ a : level N, ∀ z : ℍ, f (a.val • z) = f z) (z : ℍ) :
    matrixPullbackTrace (upperDilationLevel N p hp) (level M)
      (fun w => f (upperDilationReal p hp • w))
      (matrixPullback_invariant (level N) (upperDilationReal p hp) f hf) z =
        upperBranchSum p hp f z := by
  classical
  let : (upperDilationLevel N p hp).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := upperDilationLevel N p hp)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let := Fintype.ofFinite (level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M))
  change (∑ q : level M ⧸ (upperDilationLevel N p hp).subgroupOf (level M),
    CosetTrace.value _ _ _ q z) = _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [he a]
  change f (upperDilationReal p hp •
    ((SpecialLinearGroup.mapGL ℝ (upperSL (-(a.val : ℤ))))⁻¹ • z)) = _
  have hi : (SpecialLinearGroup.mapGL ℝ (upperSL (-(a.val : ℤ))))⁻¹ =
      SpecialLinearGroup.mapGL ℝ (upperSL a.val) := by
    rw [← map_inv]
    congr 1
    apply Subtype.ext
    change Matrix.adjugate !![1, -(a.val : ℤ); 0, 1] = !![1, (a.val : ℤ); 0, 1]
    simp [Matrix.adjugate_fin_two]
  rw [hi, ← mul_smul, upperDilation_translation]

/-- At a square divisor of the level, the second physical new-trace
equation annihilates the actual normalized ramified correspondence. -/
theorem normalizedUpperBranches_repeated_zero (M p : ℕ) [NeZero M]
    (hM : 0 < M) (hp : p.Prime) (hpM : p ∣ M)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val)
    (hnew : let : NeZero p := ⟨hp.ne_zero⟩
      AutomorphicL2.denseEmbedding _ _ f ∈
        newTraceKernel (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p)) :
    normalizedUpperBranches p hp.pos f.val = 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let G := level (p * M)
  let H := dilationLevel M p hp.pos
  let g := upperDilationReal p hp.pos
  have hH : toConjAct g⁻¹ • H = level M := upper_translate_dilationLevel M p hp.pos
  let : (toConjAct g⁻¹ • G).IsArithmetic :=
    inferInstanceAs (upperDilationLevel (p * M) p hp.pos).IsArithmetic
  let : (toConjAct g⁻¹ • H).IsArithmetic := by rw [hH]; infer_instance
  have hz : matrixPullbackTrace G H f.val (representative_matrix_invariant (p * M) f) = 0 := by
    exact continuous_new_dilation_trace_zero M p hM hp.pos f hf hnew
  funext z
  have ht := matrixPullbackTrace_translate G H g f.val
    (representative_matrix_invariant (p * M) f) z
  rw [hz] at ht
  have hc := matrixPullbackTrace_upper_cosets (p * M) M p hp.pos
    (upperLowerCosetEquiv M p hp hpM) (upperLowerCosetEquiv_mk M p hp hpM)
    f.val (representative_matrix_invariant (p * M) f) z
  rw [← matrixPullbackTrace_target_congr (upperDilationLevel (p * M) p hp.pos)
    (toConjAct g⁻¹ • H) (level M) hH] at hc
  change (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) * upperBranchSum p hp.pos f.val z = 0
  have hzero : upperBranchSum p hp.pos f.val z = 0 := by
    apply hc.symm.trans
    simpa only [G, g, upperDilationLevel, Pi.zero_apply] using ht
  rw [hzero, mul_zero]

/-- The literal normalized ramified correspondence has the exact Euler
quadratic factor on every continuous vector satisfying all new equations. -/
theorem normalizedUpperBranches_bad_square (N p : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : p ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hv : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN)
    (z : ℍ) :
    normalizedUpperBranches p hp.pos (normalizedUpperBranches p hp.pos f.val) z =
      (if p ^ 2 ∣ N then (0 : ℂ) else (p : ℂ)⁻¹) * f.val z := by
  obtain ⟨M, rfl⟩ := hpN
  have hM : 0 < M := by
    by_contra h
    have hm : M = 0 := by omega
    simp [hm] at hN
  let : NeZero M := ⟨hM.ne'⟩
  let : Fact p.Prime := ⟨hp⟩
  have htrace : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p) := by
    simp only [newSpace, Submodule.mem_iInf] at hv
    have h := hv ⟨p, hp, Nat.dvd_mul_right p M⟩
    simpa only [Nat.mul_div_cancel_left M hp.pos] using h
  by_cases hpM : p ∣ M
  · have hsq : p ^ 2 ∣ p * M := by
      rw [pow_two]
      exact mul_dvd_mul_left p hpM
    rw [ite_eq_left hsq, normalizedUpperBranches_repeated_zero M p hM hp hpM f hf htrace]
    simp only [normalizedUpperBranches, upperBranchSum, Pi.zero_apply,
      Finset.sum_const_zero, mul_zero, zero_mul]
  · have hsq : ¬ p ^ 2 ∣ p * M := by
      rw [pow_two, mul_dvd_mul_iff_left hp.ne_zero]
      exact hpM
    rw [ite_eq_right hsq]
    have hc := hp.coprime_iff_not_dvd.mpr hpM
    have hab : (p : ℤ) * Nat.gcdA p M + (M : ℤ) * Nat.gcdB p M = 1 := by
      have h := Nat.gcd_eq_gcd_ab p M
      rw [hc.gcd_eq_one, Nat.cast_one] at h
      exact h.symm
    exact normalizedUpperBranches_simple_square M p hM hpM _ _ hab f hf htrace z

/-- Actual ramified eigenvalues satisfy the original bad-prime condition.
The eigenrelation is for the literal upper-branch function operator; the
local quadratic equation is a conclusion, not an input. -/
theorem ramified_eigenvalue_square (N p : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : p ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hv : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN)
    (hf0 : f ≠ 0) (ell : ℂ)
    (he : normalizedUpperBranches p hp.pos f.val = fun z => ell * f.val z) :
    ell ^ 2 = if p ^ 2 ∣ N then (0 : ℂ) else (p : ℂ)⁻¹ := by
  have hx : ∃ z, f.val z ≠ 0 := by
    by_contra! h
    apply hf0
    apply Subtype.ext
    funext z
    exact h z
  obtain ⟨z, hz⟩ := hx
  have h := normalizedUpperBranches_bad_square N p hN hp hpN f hf hv z
  rw [he] at h
  change (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) *
    upperBranchSum p hp.pos (fun w => ell * f.val w) z = _ at h
  rw [upperBranchSum_const_mul, mul_left_comm] at h
  change ell * normalizedUpperBranches p hp.pos f.val z = _ at h
  rw [he] at h
  apply mul_right_cancel₀ hz
  simpa only [pow_two, mul_assoc] using h

#print axioms matrixPullback_invariant
#print axioms matrixPullbackTrace_congr
#print axioms matrixPullbackTrace_translate
#print axioms upperBranchSum_const_mul
#print axioms matrixPullbackTrace_prime_sum
#print axioms localAtkin_pullback_invariant
#print axioms localAtkin_pullback_square
#print axioms upperBranchSum_localAtkin
#print axioms localAtkin_pullback_trace_zero
#print axioms upperBranchSum_simple_eq_neg_local
#print axioms continuous_new_dilation_trace_zero
#print axioms normalizedUpperBranches_simple_square
#print axioms matrixPullbackTrace_upper_cosets
#print axioms normalizedUpperBranches_repeated_zero
#print axioms normalizedUpperBranches_bad_square
#print axioms ramified_eigenvalue_square

end QuantitativeNinaMaass
