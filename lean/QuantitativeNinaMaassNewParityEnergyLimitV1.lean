module

public import QuantitativeNinaMaassWindowEnergyParityV1
public import QuantitativeNinaMaassNewParityEnergyMassV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticClassicalDimension
open scoped Topology InnerProductSpace FourierTransform SchwartzMap ENNReal

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

theorem smoothPacketMultiplier_principal_energy (f : SchwartzMap ℝ ℂ) (e : ℝ)
    (he : 1 / 4 ≤ e) :
    smoothPacketMultiplier f e = cosinePacket f (Real.sqrt (e - 1 / 4)) := by
  have heq : e = 1 / 4 + (Real.sqrt (e - 1 / 4)) ^ 2 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr he)]
    ring
  conv_lhs => rw [heq, smoothPacketMultiplier_principal]

/-- The convergent ordinary principal energy and its nonnegative extended
sum agree for every actual compact smooth packet. -/
theorem principalPacketEnergy_ofReal {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN)
    (w : S.Index → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ)) :
    (∑' i : {i // 1 / 4 ≤ S.energy i},
      ENNReal.ofReal (‖cosinePacket f (Real.sqrt (S.energy i.val - 1 / 4))‖ ^ 2) *
        ENNReal.ofReal (w i.val)) = ENNReal.ofReal (principalPacketEnergy S w f) := by
  have heq (i : {i // 1 / 4 ≤ S.energy i}) :
      smoothPacketMultiplier f (S.energy i.val) =
        cosinePacket f (Real.sqrt (S.energy i.val - 1 / 4)) :=
    smoothPacketMultiplier_principal_energy f _ i.property
  simp_rw [← ENNReal.ofReal_mul (sq_nonneg _), ← heq]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun i : {i // 1 / 4 ≤ S.energy i} => mul_nonneg (sq_nonneg _) (hw i.val).1)
    (principalPacketEnergy_summable S w hw f hc)).symm

def packetParityMass (N : ℕ) (P : Set ℕ) (η : ℝ) (f : SchwartzMap ℝ ℂ) : ℝ≥0∞ :=
  partialParityEnergyMass N P η (fun r => ENNReal.ofReal (‖cosinePacket f r‖ ^ 2))

def packetParityEnergy (N : ℕ) (P : Set ℕ) (η : ℝ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  (packetParityMass N P η f).toReal

theorem packetParityMass_empty (N : ℕ) [NeZero N] (hN : 0 < N)
    (η : ℝ) (hη : η ^ 2 = 1) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    packetParityMass N ∅ η f = ENNReal.ofReal
      (principalPacketEnergy (geometricCuspSpectrum N hN)
        (cuspParityBasisWeight (geometricCuspSpectrum N hN) η) f) := by
  rw [packetParityMass, partialParityEnergyMass_empty_eq N hN η hη]
  exact principalPacketEnergy_ofReal _ _ (cuspParityBasisWeight_bounds _ η hη) f hc

theorem packetParityMass_univ (N : ℕ) [NeZero N] (hN : 0 < N)
    (η : ℝ) (hη : η ^ 2 = 1) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    packetParityMass N univ η f = ENNReal.ofReal
      (principalPacketEnergy (geometricCuspSpectrum N hN)
        (newParitySpectralWeight (geometricCuspSpectrum N hN) η) f) := by
  rw [packetParityMass, partialParityEnergyMass_univ_eq N hN η hη]
  exact principalPacketEnergy_ofReal _ _ (newParitySpectralWeight_bounds _ η) f hc

/-- Actual packet summability proves finiteness of every partial-new
weighted mass before any recurrence is converted to real subtraction. -/
theorem packetParityMass_ne_top (N : ℕ) (hN : 0 < N) (P : Set ℕ)
    (η : ℝ) (hη : η ^ 2 = 1) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) : packetParityMass N P η f ≠ ∞ := by
  let : NeZero N := ⟨hN.ne'⟩
  apply ne_top_of_le_ne_top _ (partialParityEnergyMass_le_empty N hN P η _)
  change packetParityMass N ∅ η f ≠ ∞
  rw [packetParityMass_empty N hN η hη f hc]
  exact ENNReal.ofReal_ne_top

theorem packetParityEnergy_empty (N : ℕ) [NeZero N] (hN : 0 < N)
    (η : ℝ) (hη : η ^ 2 = 1) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    packetParityEnergy N ∅ η f = principalPacketEnergy (geometricCuspSpectrum N hN)
      (cuspParityBasisWeight (geometricCuspSpectrum N hN) η) f := by
  rw [packetParityEnergy, packetParityMass_empty N hN η hη f hc, ENNReal.toReal_ofReal]
  exact tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem packetParityEnergy_univ (N : ℕ) [NeZero N] (hN : 0 < N)
    (η : ℝ) (hη : η ^ 2 = 1) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    packetParityEnergy N univ η f = principalPacketEnergy (geometricCuspSpectrum N hN)
      (newParitySpectralWeight (geometricCuspSpectrum N hN) η) f := by
  rw [packetParityEnergy, packetParityMass_univ N hN η hη f hc, ENNReal.toReal_ofReal]
  exact tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem packetParityEnergy_simple (M p : ℕ) (hM : 0 < M) (hp : p.Prime)
    (hcp : p.Coprime M) (P : Set ℕ) (hpP : p ∉ P) (η : ℝ) (hη : η ^ 2 = 1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ)) :
    packetParityEnergy (p * M) (insert p P) η f + 2 * packetParityEnergy M P η f =
      packetParityEnergy (p * M) P η f := by
  have hh := congrArg ENNReal.toReal (partialParityEnergyMass_simple M p hM hp hcp P hpP η
    (fun r => ENNReal.ofReal (‖cosinePacket f r‖ ^ 2)))
  change (packetParityMass (p * M) (insert p P) η f + 2 * packetParityMass M P η f).toReal =
    (packetParityMass (p * M) P η f).toReal at hh
  rw [ENNReal.toReal_add (packetParityMass_ne_top _ (Nat.mul_pos hp.pos hM) _ η hη f hc)
    (ENNReal.mul_ne_top (by norm_num) (packetParityMass_ne_top M hM P η hη f hc)),
    ENNReal.toReal_mul] at hh
  simpa only [packetParityEnergy, ENNReal.toReal_ofNat] using hh

theorem packetParityEnergy_repeated_two (L : ℕ) (hL : 0 < L)
    (η : ℝ) (hη : η ^ 2 = 1) (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) :
    packetParityEnergy (2 * (2 * L)) {2} η f + 2 * packetParityEnergy (2 * L) ∅ η f =
      packetParityEnergy (2 * (2 * L)) ∅ η f + packetParityEnergy L ∅ η f := by
  have h2 : 0 < 2 * L := Nat.mul_pos (by decide) hL
  have h4 : 0 < 2 * (2 * L) := Nat.mul_pos (by decide) h2
  have hh := congrArg ENNReal.toReal (partialParityEnergyMass_repeated_two L hL η hη
    (fun r => ENNReal.ofReal (‖cosinePacket f r‖ ^ 2)))
  change (packetParityMass (2 * (2 * L)) {2} η f + 2 * packetParityMass (2 * L) ∅ η f).toReal =
    (packetParityMass (2 * (2 * L)) ∅ η f + packetParityMass L ∅ η f).toReal at hh
  rw [ENNReal.toReal_add (packetParityMass_ne_top _ h4 _ η hη f hc)
      (ENNReal.mul_ne_top (by norm_num) (packetParityMass_ne_top _ h2 _ η hη f hc)),
    ENNReal.toReal_add (packetParityMass_ne_top _ h4 _ η hη f hc)
      (packetParityMass_ne_top _ hL _ η hη f hc), ENNReal.toReal_mul] at hh
  simpa only [packetParityEnergy, ENNReal.toReal_ofNat] using hh

theorem packetParityEnergy_covers (N : ℕ) (hN : 0 < N) (P : Set ℕ)
    (hP : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ P) (η : ℝ) (f : SchwartzMap ℝ ℂ) :
    packetParityEnergy N P η f = packetParityEnergy N univ η f := by
  rw [packetParityEnergy, packetParityEnergy, packetParityMass, packetParityMass,
    partialParityEnergyMass_covers N hN P hP]

/-- The full-cusp parity energy is the base law for weighted prime removal.
Its proof uses the actual packet at the original manuscript schedule. -/
theorem originalPacketParityEnergy_empty_limit (N : ℕ) (hN : 0 < N)
    (η : ℝ) (hη : η ^ 2 = 1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => packetParityEnergy N ∅ η (originalWindowMajorant K hc ε t) / (t * ε t))
      atTop (𝓝 (fullLeading N)) := by
  let : NeZero N := ⟨hN.ne'⟩
  simpa only [packetParityEnergy_empty N hN η hη _ (originalWindowMajorant_compact K hc ε _),
    cusp_parity_coefficient N hN] using
    originalWindowMajorant_principal_parity_limit (geometricCuspSpectrum N hN)
      η hη K he hc hK hm ε hε hproduct

/-- The repeated-two base is an identity of convergent actual packet
energies at three levels; its arithmetic coefficient keeps the overlap. -/
theorem originalPacketParityEnergy_two_limit (N : ℕ) (hN : 0 < N) (h4 : 4 ∣ N)
    (η : ℝ) (hη : η ^ 2 = 1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => packetParityEnergy N {2} η (originalWindowMajorant K hc ε t) / (t * ε t))
      atTop (𝓝 (twoLeading N)) := by
  obtain ⟨L, hNL⟩ := h4
  have heN : N = 2 * (2 * L) := by omega
  clear hNL
  subst N
  have hL : 0 < L := by omega
  have h2 : 0 < 2 * L := Nat.mul_pos (by decide) hL
  have hu := originalPacketParityEnergy_empty_limit _ hN η hη K he hc hK hm ε hε hproduct
  have hm' := originalPacketParityEnergy_empty_limit _ h2 η hη K he hc hK hm ε hε hproduct
  have hl := originalPacketParityEnergy_empty_limit _ hL η hη K he hc hK hm ε hε hproduct
  have hcoeff : fullLeading (2 * (2 * L)) - 2 * fullLeading (2 * L) + fullLeading L =
      twoLeading (2 * (2 * L)) := by
    have hd2 : 2 * (2 * L) / 2 = 2 * L := Nat.mul_div_cancel_left _ (by decide)
    have hd4 : 2 * (2 * L) / 4 = L := by
      rw [show 2 * (2 * L) = 4 * L by ring]
      exact Nat.mul_div_cancel_left _ (by decide)
    simp only [twoLeading, fullLeading, hd2, hd4]
    ring
  have heq (t : ℝ) :
      packetParityEnergy (2 * (2 * L)) {2} η (originalWindowMajorant K hc ε t) / (t * ε t) =
        packetParityEnergy (2 * (2 * L)) ∅ η (originalWindowMajorant K hc ε t) / (t * ε t) -
          2 * (packetParityEnergy (2 * L) ∅ η (originalWindowMajorant K hc ε t) / (t * ε t)) +
            packetParityEnergy L ∅ η (originalWindowMajorant K hc ε t) / (t * ε t) := by
    have hh := packetParityEnergy_repeated_two L hL η hη _ (originalWindowMajorant_compact K hc ε t)
    rw [← mul_div_assoc, ← sub_div, ← add_div]
    congr 1
    linarith
  simpa only [heq, hcoeff] using (hu.sub (hm'.const_mul 2)).add hl

/-- Prime-removal limit for actual compact packet energies. The generic
base input below is instantiated by the proved whole-cusp and repeated-two
packet laws; every recurrence is the proved physical finite-band identity. -/
theorem packetParityEnergy_difference_limit (b : ℕ) (P : Set ℕ) (C : ℕ → ℝ)
    (η : ℝ) (hη : η ^ 2 = 1) (f : ℝ → SchwartzMap ℝ ℂ)
    (hfc : ∀ t, HasCompactSupport (f t : ℝ → ℂ)) (ε : ℝ → ℝ)
    (hbase : ∀ N, 0 < N → b ∣ N →
      Tendsto (fun t => packetParityEnergy N P η (f t) / (t * ε t)) atTop (𝓝 (C N)))
    (ps : List ℕ) (N : ℕ) (hN : 0 < N) (hb : b ∣ N)
    (hs : SimplePrimesAt ps N) (hc : ∀ p ∈ ps, p.Coprime b)
    (hout : ∀ p ∈ ps, p ∉ P) :
    Tendsto (fun t => packetParityEnergy N ((ps.toFinset : Set ℕ) ∪ P) η (f t) / (t * ε t))
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
        packetParityEnergy (p * M) (((p :: ps).toFinset : Set ℕ) ∪ P) η (f t) / (t * ε t) =
          packetParityEnergy (p * M) ((ps.toFinset : Set ℕ) ∪ P) η (f t) / (t * ε t) -
            2 * (packetParityEnergy M ((ps.toFinset : Set ℕ) ∪ P) η (f t) / (t * ε t)) := by
      have hh := packetParityEnergy_simple M p hM hp.1 hcop
        ((ps.toFinset : Set ℕ) ∪ P) hpP η hη (f t) (hfc t)
      rw [hset, ← mul_div_assoc, ← sub_div]
      congr 1
      linarith
    simpa only [heq, simpleDifference, hd] using hu.sub (hl.const_mul 2)

/-- Sharp principal new-parity packet energy at every admissible level,
for the actual majorant and precisely the manuscript width assumptions.
The whole completed-space energy additionally contains exceptional terms. -/
theorem originalPacketParityEnergy_univ_limit (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (η : ℝ) (hη : η ^ 2 = 1) (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x : ℂ))))
    (hK : ∀ x, 0 ≤ K x) (hm : (∫ x, K x) = 1)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => packetParityEnergy N univ η (originalWindowMajorant K hc ε t) / (t * ε t))
      atTop (𝓝 (AsymptoticTotalNewCorner.arithmeticCoefficient N)) := by
  by_cases h4 : 4 ∣ N
  · have hh := packetParityEnergy_difference_limit 4 {2} twoLeading η hη
      (originalWindowMajorant K hc ε) (originalWindowMajorant_compact K hc ε) ε
      (fun M hM hM4 => originalPacketParityEnergy_two_limit M hM hM4 η hη K he hc hK hm ε hε hproduct)
      (oddPrimeList N) N hN.1 h4 (oddPrimeList_simple N hN)
      (oddPrimeList_coprime_four N)
      (fun p hp => by simpa only [Set.mem_singleton_iff] using oddPrimeList_ne_two N p hp)
    have hcoeff := twoDifference_arithmetic N hN.1 h4 (oddPrimeList_simple N hN)
    change simpleDifference (oddPrimeList N) twoLeading N =
      AsymptoticTotalNewCorner.arithmeticCoefficient N at hcoeff
    have hcover : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ ((oddPrimeList N).toFinset : Set ℕ) ∪ {2} := by
      intro p hp hd
      rcases oddPrimeList_covers N hN.1 p hp hd with h | h
      · exact Or.inl (List.mem_toFinset.mpr h)
      · exact Or.inr h
    simpa only [hcoeff, packetParityEnergy_covers N hN.1 _ hcover] using hh
  · have hh := packetParityEnergy_difference_limit 1 ∅ fullLeading η hη
      (originalWindowMajorant K hc ε) (originalWindowMajorant_compact K hc ε) ε
      (fun M hM _ => originalPacketParityEnergy_empty_limit M hM η hη K he hc hK hm ε hε hproduct)
      (allPrimeList N) N hN.1 (one_dvd N) (allPrimeList_simple N hN h4)
      (fun p _ => Nat.coprime_one_right p) (by simp)
    have hcoeff := fullDifference_arithmetic N hN.1 (allPrimeList_simple N hN h4)
    change simpleDifference (allPrimeList N) fullLeading N =
      AsymptoticTotalNewCorner.arithmeticCoefficient N at hcoeff
    have hcover : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ ((allPrimeList N).toFinset : Set ℕ) ∪ ∅ := by
      intro p hp hd
      exact Or.inl (List.mem_toFinset.mpr (allPrimeList_covers N hN.1 p hp hd))
    simpa only [hcoeff, packetParityEnergy_covers N hN.1 _ hcover] using hh

#print axioms smoothPacketMultiplier_principal_energy
#print axioms principalPacketEnergy_ofReal
#print axioms packetParityMass_empty
#print axioms packetParityMass_univ
#print axioms packetParityMass_ne_top
#print axioms packetParityEnergy_empty
#print axioms packetParityEnergy_univ
#print axioms packetParityEnergy_simple
#print axioms packetParityEnergy_repeated_two
#print axioms packetParityEnergy_covers
#print axioms originalPacketParityEnergy_empty_limit
#print axioms originalPacketParityEnergy_two_limit
#print axioms packetParityEnergy_difference_limit
#print axioms originalPacketParityEnergy_univ_limit

end QuantitativeNinaMaass
