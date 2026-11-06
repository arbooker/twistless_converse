module

public import SmallLevelOriginalTaylorRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessRamanujanSum FinitenessFourierConstruction FinitenessAnalyticReconstruction

/-- The Ramanujan-twisted additive transform is literally the finite sum
of original additive transforms, on one half-plane uniform in the translate. -/
theorem ramanujan_additive_sum {N k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) (q : ℕ) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      SmallLevelAdditive.transform (fullCoefficients (twisted f q) k) r s=
        ∑ j∈residues q, SmallLevelAdditive.original k f (r+(j:ℝ)/q) s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have ha := polynomial_bound hf.zero hg k
  have ha0 := fullCoefficients_zero hf.zero k
  have hqa := polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) k
  have hqa0 := fullCoefficients_zero (twisted_zero hf.zero q) k
  obtain ⟨B,hB⟩ := additive_convergence_halfplane ha ha0
  obtain ⟨C,hC⟩ := additive_convergence_halfplane hqa hqa0
  refine ⟨max B C,?_⟩
  intro r s hs
  have hsB : B<s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsC : C<s.re := lt_of_le_of_lt (le_max_right _ _) hs
  rw [← (hC r s hsC).2]
  have he : EqOn
      (fun y : ℝ => fourier (fullCoefficients (twisted f q) k) ((r:ℂ)+(y:ℂ)*I))
      (fun y : ℝ => ∑ j∈residues q,
        fourier (fullCoefficients f k) (((r+(j:ℝ)/q:ℝ):ℂ)+(y:ℂ)*I)) (Ioi 0) := by
    intro y hy
    dsimp only
    rw [fourier_twisted hf.zero hg q k (by simpa using hy)]
    unfold twist residues
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  rw [mellin_congr_positive he s]
  unfold mellin
  simp only [Finset.smul_sum]
  rw [integral_finsetSum (residues q) (fun j _ => (hB (r+(j:ℝ)/q) s hsB).1)]
  apply Finset.sum_congr rfl
  intro j _
  exact (hB (r+(j:ℝ)/q) s hsB).2

/-- The literal finite-grid Ramanujan sum used in the manuscript. -/
def ramanujanAdditive (k : ℕ) (f : ℕ → ℂ) (q : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  ∑ j∈residues q, SmallLevelAdditive.original k f (r+(j:ℝ)/q) s

def ramanujanTaylorSum (k : ℕ) (f : ℕ → ℂ) (q : ℕ) (L r : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ n∈Finset.range M, (I*(L:ℂ)*(r:ℂ))^n*Ring.choose (s+(n:ℂ)-(k:ℂ)) n*
    ramanujanAdditive k f q (-1/(L*r)) (s+(n:ℂ))

/-- The full manuscript Taylor--Fricke row, with every twist expanded as
an explicit primitive finite sum of the original additive transforms. -/
theorem original_finite_sum_taylor_rows {N k : ℕ} (hN : 0<N) (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm N (q^2)) r (FinitenessNormalizedTwistProduct.root N f q*ε*I^k) M))
          {s : ℂ | B-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          ramanujanAdditive k f q r s-
            (FinitenessNormalizedTwistProduct.root N f q*ε*I^k)*
              (((Nat.lcm N (q^2):ℝ)*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*
              ramanujanTaylorSum k f q (Nat.lcm N (q^2)) r M s=
            mellin (frickeError k (fullCoefficients (twisted f q) k)
              (Nat.lcm N (q^2)) r (FinitenessNormalizedTwistProduct.root N f q*ε*I^k) M) s := by
  obtain ⟨ε,hε,hrows⟩ := original_ramanujan_taylor_rows hN hk hf
  refine ⟨ε,hε,?_⟩
  intro q hq r hr
  obtain ⟨B,hB⟩ := hrows q hq r hr
  obtain ⟨C,hC⟩ := ramanujan_additive_sum hf q
  refine ⟨max B C,?_⟩
  intro M
  constructor
  · intro s hs
    apply (hB M).1 s
    change max B C-(M:ℝ)<s.re at hs
    change B-(M:ℝ)<s.re
    linarith [le_max_left B C]
  · intro s hs
    have hsB : B<s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : C<s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hm := (hB M).2 s hsB
    rw [hC r s hsC] at hm
    have he : normalizedTaylorSum k (fullCoefficients (twisted f q) k)
        (Nat.lcm N (q^2)) r M s=ramanujanTaylorSum k f q (Nat.lcm N (q^2)) r M s := by
      unfold normalizedTaylorSum ramanujanTaylorSum ramanujanAdditive
      apply Finset.sum_congr rfl
      intro n _
      rw [hC _ (s+(n:ℂ)) (by
        simp only [Complex.add_re,Complex.natCast_re]
        exact lt_of_lt_of_le hsC (le_add_of_nonneg_right (Nat.cast_nonneg n)))]
    rw [he] at hm
    exact hm

#print axioms ramanujan_additive_sum
#print axioms original_finite_sum_taylor_rows
end SmallLevelTaylor
