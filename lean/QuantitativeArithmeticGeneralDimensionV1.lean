module

public import QuantitativeArithmeticPartialRepeatedV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticGeneralDimension

open UpperHalfPlane Filter AsymptoticSectorComparison AsymptoticClassicalCusp
open AsymptoticClassicalDimension QuantitativeArithmeticPartialRepeated
open QuantitativeEulerOldProjectionClassicalDimension

/-- The finite local second-difference expression for the leading dimension.
Absent primes do nothing; simply ramified primes have no overlap term. -/
def leading : List ℕ → ℕ → ℝ
  | [], N => fullLeading N
  | p::ps, N => if p∣N then leading ps N - 2*leading ps (N/p) +
      (if p∣N/p then leading ps (N/p/p) else 0) else leading ps N

theorem insert_not_dvd (N p : ℕ) (hN : 0<N) (hp : ¬p∣N) (k : ℤ) (S : Set ℕ) :
    partialNewSpace N hN k (insert p S)=partialNewSpace N hN k S := by
  ext f
  simp only [mem_partialNewSpace,Set.mem_insert_iff]
  constructor
  · intro h q hq
    exact h q (Or.inr hq)
  · intro h q hq
    rcases hq with he|he
    · exact (hp (he ▸ q.property.2)).elim
    · exact h q he

/-- All positive levels have a bounded classical dimension remainder after
any finite set of prime-new conditions. No admissibility hypothesis is used. -/
theorem partial_dimension_bounded (ps : List ℕ) (hd : ps.Nodup)
    (hp : ∀p∈ps,p.Prime) (N : ℕ) (hN : 0<N) :
    ∃ B : ℝ,∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (partialNewSpace N hN (k:ℤ) (ps.toFinset:Set ℕ)):ℝ)-
        leading ps N*k|≤B := by
  induction ps generalizing N with
  | nil =>
    have hset : (([].toFinset : Finset ℕ):Set ℕ)=∅ := by ext p; simp
    have hdim (k : ℕ) := congrArg
      (fun S : Set ℕ => Module.finrank ℂ (partialNewSpace N hN (k:ℤ) S)) hset
    simpa only [hdim,leading] using empty_dimension_bounded N hN
  | cons p ps ih =>
    have hprime := hp p List.mem_cons_self
    have hdt := (List.nodup_cons.mp hd).2
    have hpt : ∀q∈ps,q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hpS : p∉(ps.toFinset:Set ℕ) := by
      simpa only [Finset.mem_coe,List.mem_toFinset] using (List.nodup_cons.mp hd).1
    have heven : ∀ᶠ k in evenWeights,Even k :=
      Filter.Eventually.filter_mono inf_le_right
        (Filter.eventually_principal.mpr (fun _ h => h))
    have hset : ((p::ps).toFinset:Set ℕ)=insert p (ps.toFinset:Set ℕ) := by
      ext q
      simp
    by_cases hdiv : p∣N
    · obtain ⟨M,rfl⟩ := hdiv
      have hM : 0<M := by
        by_contra hz
        have : M=0 := by omega
        simp [this] at hN
      let : NeZero M := ⟨hM.ne'⟩
      let : NeZero p := ⟨hprime.ne_zero⟩
      have hdM : p*M/p=M := Nat.mul_div_cancel_left M hprime.pos
      obtain ⟨Bu,hu⟩ := ih hdt hpt (p*M) hN
      obtain ⟨Bm,hm⟩ := ih hdt hpt M hM
      by_cases hrepeat : p∣M
      · obtain ⟨L,rfl⟩ := hrepeat
        have hL : 0<L := by
          by_contra hz
          have : L=0 := by omega
          simp [this] at hM
        have hdL : p*L/p=L := Nat.mul_div_cancel_left L hprime.pos
        obtain ⟨Bl,hl⟩ := ih hdt hpt L hL
        refine ⟨Bu+2*Bm+Bl,?_⟩
        filter_upwards [heven,hu,hm,hl] with k hk hu hm hl
        have he := partialNewSpace_repeated_finrank L p hL hprime k hk
          (ps.toFinset:Set ℕ) hpS
        have heR :
            (Module.finrank ℂ (partialNewSpace (p*(p*L)) hN (k:ℤ)
              (insert p (ps.toFinset:Set ℕ))):ℝ)+
              2*(Module.finrank ℂ (partialNewSpace (p*L) hM (k:ℤ) (ps.toFinset:Set ℕ)):ℝ)=
            (Module.finrank ℂ (partialNewSpace (p*(p*L)) hN (k:ℤ) (ps.toFinset:Set ℕ)):ℝ)+
              (Module.finrank ℂ (partialNewSpace L hL (k:ℤ) (ps.toFinset:Set ℕ)):ℝ) := by
          exact_mod_cast he
        rw [hset]
        simp only [leading,ite_eq_left (Nat.dvd_mul_right p (p*L)),hdM,
          ite_eq_left (Nat.dvd_mul_right p L),hdL]
        rw [abs_le] at hu hm hl ⊢
        constructor <;> nlinarith [hu.1,hu.2,hm.1,hm.2,hl.1,hl.2]
      · refine ⟨Bu+2*Bm,?_⟩
        filter_upwards [heven,hu,hm] with k hk hu hm
        have he := partialNewSpace_simple_finrank M p hM hprime
          (hprime.coprime_iff_not_dvd.mpr hrepeat) k hk (ps.toFinset:Set ℕ) hpS
        have heR :
            (Module.finrank ℂ (partialNewSpace (p*M) hN (k:ℤ)
              (insert p (ps.toFinset:Set ℕ))):ℝ)+
              2*(Module.finrank ℂ (partialNewSpace M hM (k:ℤ) (ps.toFinset:Set ℕ)):ℝ)=
            (Module.finrank ℂ (partialNewSpace (p*M) hN (k:ℤ) (ps.toFinset:Set ℕ)):ℝ) := by
          exact_mod_cast he
        rw [hset]
        simp only [leading,ite_eq_left (Nat.dvd_mul_right p M),hdM,ite_eq_right hrepeat,add_zero]
        rw [abs_le] at hu hm ⊢
        constructor <;> nlinarith [hu.1,hu.2,hm.1,hm.2]
    · obtain ⟨B,hB⟩ := ih hdt hpt N hN
      refine ⟨B,?_⟩
      filter_upwards [hB] with k hk
      rw [hset,insert_not_dvd N p hN hdiv]
      simpa only [leading,ite_eq_right hdiv] using hk

/-- Applying every prime-divisor condition gives the actual classical
newspace, with the same bounded error at every positive level. -/
theorem new_dimension_bounded (N : ℕ) (hN : 0<N) :
    ∃ B : ℝ,∀ᶠ k : ℕ in evenWeights,
      |(Module.finrank ℂ (newSpace N hN (k:ℤ)):ℝ)-
        leading N.primeFactors.toList N*k|≤B := by
  have hd := N.primeFactors.nodup_toList
  have hp : ∀p∈N.primeFactors.toList,p.Prime := fun p h => (Nat.mem_primeFactors.mp (Finset.mem_toList.mp h)).1
  obtain ⟨B,hB⟩ := partial_dimension_bounded N.primeFactors.toList hd hp N hN
  refine ⟨B,?_⟩
  have he (k : ℕ) : partialNewSpace N hN (k:ℤ)
      (N.primeFactors.toList.toFinset:Set ℕ)=newSpace N hN (k:ℤ) := by
    ext f
    simp only [mem_partialNewSpace,mem_newSpace]
    constructor
    · intro h p
      apply h p
      simpa only [Finset.mem_coe,List.mem_toFinset] using
        Finset.mem_toList.mpr (Nat.mem_primeFactors.mpr ⟨p.property.1,p.property.2,hN.ne'⟩)
    · intro h p _
      exact h p
  have hdim (k : ℕ) := congrArg
    (fun U : Submodule ℂ (CuspForm (level N) (k:ℤ)) => Module.finrank ℂ U) (he k)
  simpa only [hdim] using hB

#print axioms partial_dimension_bounded
#print axioms new_dimension_bounded

end QuantitativeArithmeticGeneralDimension
