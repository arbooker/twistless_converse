module

public import QuantitativeNinaMaassPartialNewV1
public import QuantitativeNinaMaassNewParityV1
public import AsymptoticClassicalNewDimensionCoefficientV1
public import AsymptoticClassicalNewDimensionAdmissibleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass AsymptoticCongruenceStrip
open AsymptoticClassicalPetersson AsymptoticClassicalDimension
open scoped Topology

/-!
The all-level short-interval count in the actual physical trace-new space.
The spectral basis is the existing geometric basis at each positive level.
Prime removal uses the proved physical band recurrence; only the arithmetic
finite-difference identities are reused from the classical development.

Draft pending the full pinned-compiler check. The coefficient-map bridge
to the original Euler solutions is a separate remaining obligation.
-/

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance

local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- A dimension of the actual geometric parity band with the selected
physical trace equations. The zero-level branch is never used below. -/
def partialParityCount (N : ℕ) (P : Set ℕ) (a b σ : ℝ) : ℕ :=
  if hN : 0 < N then
    let : NeZero N := ⟨hN.ne'⟩
    Module.finrank ℂ ((geometricCuspSpectrum N hN).partialParityBand a b σ P)
  else 0

theorem partialParityCount_eq (N : ℕ) [NeZero N] (hN : 0 < N)
    (P : Set ℕ) (a b σ : ℝ) :
    partialParityCount N P a b σ =
      Module.finrank ℂ ((geometricCuspSpectrum N hN).partialParityBand a b σ P) := by
  rw [partialParityCount, dite_eq_left hN]

theorem partialParityCount_covers (N : ℕ) (hN : 0 < N) (P : Set ℕ)
    (hP : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ P) (a b σ : ℝ) :
    partialParityCount N P a b σ = partialParityCount N univ a b σ := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [partialParityCount_eq N hN, partialParityCount_eq N hN]
  apply LinearEquiv.finrank_eq
  apply LinearEquiv.ofEq
  unfold CuspEnergySpectrum.partialParityBand
  rw [partialNewSpace_eq_newSpace_of_covers N hN P hP, partialNewSpace_univ]

theorem cusp_parity_coefficient (N : ℕ) (hN : 0 < N) :
    (quotientMeasure N).real univ / (4 * Real.pi) = fullLeading N := by
  rw [Measure.real, quotientMeasure_univ N hN, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
  unfold fullLeading
  field_simp
  ring

theorem partialParityCount_simple (M p : ℕ) (hM : 0 < M) (hp : p.Prime)
    (hcp : p.Coprime M) (P : Set ℕ) (hpP : p ∉ P) (a b σ : ℝ) :
    partialParityCount (p * M) (insert p P) a b σ +
      2 * partialParityCount M P a b σ = partialParityCount (p * M) P a b σ := by
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  simp only [partialParityCount_eq M hM,
    partialParityCount_eq (p * M) (Nat.mul_pos hp.pos hM)]
  exact CuspEnergySpectrum.partialParityBand_simple_finrank M p hM hp hcp
    (geometricCuspSpectrum M hM) (geometricCuspSpectrum (p * M) (Nat.mul_pos hp.pos hM))
    a b σ P hpP

theorem empty_partialParityCount_short_weyl (N : ℕ) (hN : 0 < N)
    (σ : ℝ) (hσ : σ ^ 2 = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => (partialParityCount N ∅ t (t + ε t) σ : ℝ) / (t * ε t))
      atTop (𝓝 (fullLeading N)) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hh := (geometricCuspSpectrum N hN).parityBand_short_weyl σ hσ ε hε hproduct
  have he (a b : ℝ) : partialParityCount N ∅ a b σ =
      Module.finrank ℂ ((geometricCuspSpectrum N hN).parityBand a b σ) := by
    rw [partialParityCount_eq N hN]
    exact ((LinearEquiv.ofEq _ _
      ((geometricCuspSpectrum N hN).partialParityBand_empty a b σ)).trans
        (Submodule.topEquiv)).finrank_eq
  simpa only [he, cusp_parity_coefficient N hN] using hh

/-- The repeated-2 base uses the actual overlap at every level divisible
by four, without a newform-decomposition or index assumption. -/
theorem two_partialParityCount_short_weyl (N : ℕ) (hN : 0 < N) (h4 : 4 ∣ N)
    (σ : ℝ) (hσ : σ ^ 2 = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => (partialParityCount N {2} t (t + ε t) σ : ℝ) / (t * ε t))
      atTop (𝓝 (twoLeading N)) := by
  obtain ⟨L, hNL⟩ := h4
  have heN : N = 2 * (2 * L) := by omega
  clear hNL
  subst N
  have hL : 0 < L := by omega
  let : NeZero L := ⟨hL.ne'⟩
  let S := geometricCuspSpectrum L hL
  let T := geometricCuspSpectrum (2 * L) (Nat.mul_pos (by decide) hL)
  let V := geometricCuspSpectrum (2 * (2 * L)) hN
  have hh := CuspEnergySpectrum.repeated_two_traceNewParityBand_short_weyl L hL S T V
    σ hσ ε hε hproduct
  have hcount (a b : ℝ) : partialParityCount (2 * (2 * L)) {2} a b σ =
      Module.finrank ℂ (T.traceNewParityBand V (Nat.dvd_mul_left (2 * L) 2) a b σ) := by
    rw [partialParityCount_eq _ hN]
    apply LinearEquiv.finrank_eq
    apply LinearEquiv.ofEq
    change V.partialParityBand a b σ {2} = _
    rw [show ({2} : Set ℕ) = insert 2 ∅ by ext p; simp,
      CuspEnergySpectrum.partialParityBand_insert (2 * L) 2
        (Nat.mul_pos (by decide) hL) Nat.prime_two T V a b σ ∅,
      CuspEnergySpectrum.partialParityBand_empty, inf_top_eq]
  have hd2 : 2 * (2 * L) / 2 = 2 * L := Nat.mul_div_cancel_left _ (by decide)
  have hd4 : 2 * (2 * L) / 4 = L := by
    rw [show 2 * (2 * L) = 4 * L by ring]
    exact Nat.mul_div_cancel_left _ (by decide)
  have hcoeff : ((quotientMeasure (2 * (2 * L))).real univ -
      2 * (quotientMeasure (2 * L)).real univ + (quotientMeasure L).real univ) /
        (4 * Real.pi) = twoLeading (2 * (2 * L)) := by
    rw [add_div, sub_div, mul_div_assoc,
      cusp_parity_coefficient _ hN,
      cusp_parity_coefficient _ (Nat.mul_pos (by decide) hL), cusp_parity_coefficient _ hL]
    simp only [twoLeading, fullLeading, hd2, hd4]
    ring
  simpa only [hcount, hcoeff] using hh

/-- Induction over the actual simply ramified prime conditions. The base
estimate is generic here and is instantiated below by the two proved
geometric base laws, under the original shrinking-window hypotheses. -/
theorem partialParityCount_difference_limit (b : ℕ) (P : Set ℕ) (C : ℕ → ℝ)
    (σ : ℝ) (ε : ℝ → ℝ)
    (hbase : ∀ N, 0 < N → b ∣ N →
      Tendsto (fun t => (partialParityCount N P t (t + ε t) σ : ℝ) / (t * ε t))
        atTop (𝓝 (C N)))
    (ps : List ℕ) (N : ℕ) (hN : 0 < N) (hb : b ∣ N)
    (hs : SimplePrimesAt ps N) (hc : ∀ p ∈ ps, p.Coprime b)
    (hout : ∀ p ∈ ps, p ∉ P) :
    Tendsto (fun t =>
      (partialParityCount N ((ps.toFinset : Set ℕ) ∪ P) t (t + ε t) σ : ℝ) / (t * ε t))
      atTop (𝓝 (simpleDifference ps C N)) := by
  induction ps generalizing N with
  | nil => simpa only [List.toFinset_nil, Finset.coe_empty, Set.empty_union, simpleDifference]
      using hbase N hN hb
  | cons p ps ih =>
    have hp := hs.2 p List.mem_cons_self
    obtain ⟨M, rfl⟩ := hp.2.1
    have hM : 0 < M := by nlinarith
    have hd : p * M / p = M := Nat.mul_div_cancel_left M hp.1.pos
    have hsM : SimplePrimesAt ps M := by simpa only [hd] using hs.tail_div hN
    have hbM : b ∣ M := by
      simpa only [hd] using base_dvd_div hb (Nat.dvd_mul_right p M) (hc p List.mem_cons_self)
    have hc' : ∀ q ∈ ps, q.Coprime b := fun q hq => hc q (List.mem_cons_of_mem p hq)
    have hout' : ∀ q ∈ ps, q ∉ P := fun q hq => hout q (List.mem_cons_of_mem p hq)
    have hu := ih (p * M) hN hb hs.tail hc' hout'
    have hl := ih M hM hbM hsM hc' hout'
    have hpP : p ∉ (ps.toFinset : Set ℕ) ∪ P := by
      simp only [Set.mem_union, Finset.mem_coe, List.mem_toFinset, not_or]
      exact ⟨(List.nodup_cons.mp hs.1).1, hout p List.mem_cons_self⟩
    have hcop : p.Coprime M := by simpa only [hd] using hp.2.2
    have hset : ((p :: ps).toFinset : Set ℕ) ∪ P = insert p ((ps.toFinset : Set ℕ) ∪ P) := by
      ext q
      simp [or_assoc]
    have heq (t : ℝ) :
        (partialParityCount (p * M) (((p :: ps).toFinset : Set ℕ) ∪ P) t (t + ε t) σ : ℝ) /
          (t * ε t) =
        (partialParityCount (p * M) ((ps.toFinset : Set ℕ) ∪ P) t (t + ε t) σ : ℝ) /
          (t * ε t) -
          2 * ((partialParityCount M ((ps.toFinset : Set ℕ) ∪ P) t (t + ε t) σ : ℝ) /
            (t * ε t)) := by
      have heR :
          (partialParityCount (p * M) (insert p ((ps.toFinset : Set ℕ) ∪ P)) t (t + ε t) σ : ℝ) +
            2 * (partialParityCount M ((ps.toFinset : Set ℕ) ∪ P) t (t + ε t) σ : ℝ) =
          (partialParityCount (p * M) ((ps.toFinset : Set ℕ) ∪ P) t (t + ε t) σ : ℝ) := by
        exact_mod_cast partialParityCount_simple M p hM hp.1 hcop
          ((ps.toFinset : Set ℕ) ∪ P) hpP t (t + ε t) σ
      rw [hset, ← mul_div_assoc, ← sub_div]
      congr 1
      linarith
    simpa only [heq, simpleDifference, hd] using hu.sub (hl.const_mul 2)

/-- The original shrinking-window hypotheses give the exact arithmetic
coefficient for the actual simultaneous trace-new parity space at every
admissible level. No decomposition or new-count conclusion is assumed. -/
theorem actual_new_parity_short_weyl (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (σ : ℝ) (hσ : σ ^ 2 = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => (partialParityCount N univ t (t + ε t) σ : ℝ) / (t * ε t))
      atTop (𝓝 (AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
  by_cases h4 : 4 ∣ N
  · have hh := partialParityCount_difference_limit 4 {2} twoLeading σ ε
      (fun M hM hM4 => two_partialParityCount_short_weyl M hM hM4 σ hσ ε hε hproduct)
      (oddPrimeList N) N hN.1 h4 (oddPrimeList_simple N hN)
      (oddPrimeList_coprime_four N)
      (fun p hp => by simpa only [Set.mem_singleton_iff] using oddPrimeList_ne_two N p hp)
    have hc := twoDifference_arithmetic N hN.1 h4 (oddPrimeList_simple N hN)
    change simpleDifference (oddPrimeList N) twoLeading N =
      AsymptoticTotalNewCorner.arithmeticCoefficient N at hc
    have hcover : ∀ p : ℕ, p.Prime → p ∣ N →
        p ∈ ((oddPrimeList N).toFinset : Set ℕ) ∪ {2} := by
      intro p hp hd
      rcases oddPrimeList_covers N hN.1 p hp hd with h | h
      · exact Or.inl (List.mem_toFinset.mpr h)
      · exact Or.inr h
    simpa only [hc, partialParityCount_covers N hN.1 _ hcover] using hh
  · have hh := partialParityCount_difference_limit 1 ∅ fullLeading σ ε
      (fun M hM _ => empty_partialParityCount_short_weyl M hM σ hσ ε hε hproduct)
      (allPrimeList N) N hN.1 (one_dvd N) (allPrimeList_simple N hN h4)
      (fun p _ => Nat.coprime_one_right p) (by simp)
    have hc := fullDifference_arithmetic N hN.1 (allPrimeList_simple N hN h4)
    change simpleDifference (allPrimeList N) fullLeading N =
      AsymptoticTotalNewCorner.arithmeticCoefficient N at hc
    have hcover : ∀ p : ℕ, p.Prime → p ∣ N →
        p ∈ ((allPrimeList N).toFinset : Set ℕ) ∪ ∅ := by
      intro p hp hd
      exact Or.inl (List.mem_toFinset.mpr (allPrimeList_covers N hN.1 p hp hd))
    simpa only [hc, partialParityCount_covers N hN.1 _ hcover] using hh

/-- A usable eventual lower estimate with exactly the manuscript's two
parities and shrinking-window assumptions. This counts physical new
dimensions; the map into literal Euler solutions is still a later step. -/
theorem original_new_parity_count_lower (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop)
    (c : ℝ) (hc : c < AsymptoticTotalNewCorner.arithmeticCoefficient N) :
    ∀ᶠ t in atTop, c * (t * ε t) ≤
      (partialParityCount N univ t (t + ε t) ((-1 : ℝ) ^ δ) : ℝ) := by
  have hsign : ((-1 : ℝ) ^ δ) ^ 2 = 1 := by
    rcases hδ with rfl | rfl <;> norm_num
  have hlim := actual_new_parity_short_weyl N hN _ hsign ε hε hproduct
  have hl := hlim.eventually (lt_mem_nhds hc)
  filter_upwards [hl, hε, eventually_ge_atTop (1 : ℝ)] with t ht he ht1
  have hd : 0 < t * ε t := mul_pos (by linarith) he.1
  exact ((lt_div_iff₀ hd).mp ht).le

#print axioms partialParityCount_eq
#print axioms partialParityCount_covers
#print axioms cusp_parity_coefficient
#print axioms partialParityCount_simple
#print axioms empty_partialParityCount_short_weyl
#print axioms two_partialParityCount_short_weyl
#print axioms partialParityCount_difference_limit
#print axioms actual_new_parity_short_weyl
#print axioms original_new_parity_count_lower

end QuantitativeNinaMaass
