module

public import QuantitativeArithmeticRepeatedJoinV1
public import AsymptoticClassicalMultiplicityRepeatedV1
public import QuantitativeEulerOldProjectionClassicalDimensionBaseV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticClassicalRepeated

open UpperHalfPlane Matrix AsymptoticCongruenceLabels AsymptoticClassicalCusp
open QuantitativeArithmeticRepeatedJoin
open AsymptoticCongruenceStrip
open scoped MatrixGroups

/-- The integral conjugation identity before passage to projective classes. -/
theorem conjugate_real (p : ℕ) (hp : 0<p) (A : SL(2,ℤ))
    (b : ℤ) (hb : A 0 1=(p:ℤ)*b) :
    SpecialLinearGroup.mapGL ℝ A*dilationReal p hp=
      dilationReal p hp*SpecialLinearGroup.mapGL ℝ (conjugate p A b hb) := by
  apply Units.ext
  change A.val.map (fun z : ℤ => (z:ℝ))*(dilationReal p hp).val=
    (dilationReal p hp).val*(conjugate p A b hb).val.map (fun z : ℤ => (z:ℝ))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilationReal,dilationGL,GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero,
      conjugate,Matrix.mul_apply,Fin.sum_univ_two,hb]
  all_goals ring

/-- The honest classical old groups generate the expected group at every
repeated prime, including exponent two of an odd prime. -/
theorem repeated_old_join_eq (L p : ℕ) (_hL : 0<L) (hp : p.Prime) :
    level (p*L)⊔dilationLevel (p*L) p hp.pos=dilationLevel L p hp.pos := by
  let : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · exact sup_le (level_le_dilation_conjugate L p hp.pos)
      (dilationLevel_mono hp.pos (Nat.dvd_mul_left L p))
  · rintro g ⟨a,⟨A,hA,rfl⟩,rfl⟩
    let J := level (p*L)⊔dilationLevel (p*L) p hp.pos
    let φ : SL(2,ℤ) →* GL (Fin 2) ℝ :=
      (MulAut.conj (dilationReal p hp.pos)⁻¹).toMonoidHom.comp (SpecialLinearGroup.mapGL ℝ)
    have ht (u : ℤ) : φ (upperSL u)∈J := by
      apply (show dilationLevel (p*L) p hp.pos≤J from le_sup_right)
      exact ⟨SpecialLinearGroup.mapGL ℝ (upperSL u),
        ⟨upperSL u,upper_mem (p*L) u,rfl⟩,rfl⟩
    have hz (B : SL(2,ℤ)) (hB : B∈CongruenceSubgroup.Gamma0 L) (hb : (p:ℤ)∣B 0 1) : φ B∈J := by
      obtain ⟨b,hb⟩ := hb
      have he : φ B=SpecialLinearGroup.mapGL ℝ (conjugate p B b hb) := by
        change (dilationReal p hp.pos)⁻¹*SpecialLinearGroup.mapGL ℝ B*dilationReal p hp.pos=_
        rw [mul_assoc,conjugate_real p hp.pos B b hb,← mul_assoc,inv_mul_cancel,one_mul]
      rw [he]
      apply (show level (p*L)≤J from le_sup_left)
      exact ⟨conjugate p B b hb,conjugate_mem L p B hB b hb,rfl⟩
    obtain ⟨v,u,hvu⟩ := upper_reduce p A
    have hB := hz (upperSL v*A*upperSL u)
      ((CongruenceSubgroup.Gamma0 L).mul_mem
        ((CongruenceSubgroup.Gamma0 L).mul_mem (upper_mem L v) hA) (upper_mem L u)) hvu
    rw [map_mul,map_mul] at hB
    exact (J.mul_mem_cancel_left (ht v)).mp ((J.mul_mem_cancel_right (ht u)).mp hB)

theorem repeated_old_intersection_finrank (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (k : ℤ) :
    Module.finrank ℂ ↥(LinearMap.range (restrict k
      (level_antitone (Nat.dvd_mul_left (p * L) p))) ⊓
      LinearMap.range (restrict k (level_le_dilation_conjugate (p * L) p hp.pos))) =
        Module.finrank ℂ (CuspForm (level L) k) := by
  let : NeZero L := ⟨hL.ne'⟩
  let : NeZero (p * L) := ⟨(Nat.mul_pos hp.pos hL).ne'⟩
  let : NeZero (p * (p * L)) := ⟨(Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)).ne'⟩
  have he := restrict_intersection_finrank
    (G := level (p * (p * L))) (H := level (p * L))
    (L := dilationLevel (p * L) p hp.pos) (J := dilationLevel L p hp.pos) k
    (level_antitone (Nat.dvd_mul_left (p * L) p))
    (level_le_dilation_conjugate (p * L) p hp.pos)
    ((level_antitone (Nat.dvd_mul_left (p * L) p)).trans
      (level_le_dilation_conjugate L p hp.pos)) (repeated_old_join_eq L p hL hp)
  exact he.trans (dilationLevel_finrank L p hp.pos k)

theorem primeOldIntersection_repeated_finrank (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (k : ℤ) :
    Module.finrank ℂ (primeOldIntersection (p * (p * L))
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k (repeatedPrime L p hp)) =
        Module.finrank ℂ (CuspForm (level L) k) := by
  have hd : p * (p * L) / p = p * L := Nat.mul_div_cancel_left (p * L) hp.pos
  have h1 := restrict_range_group_congr
    (G := level (p * (p * L))) (H := level (p * (p * L) / p)) (J := level (p * L)) k
    (level_antitone (Nat.div_dvd_of_dvd (Nat.dvd_mul_right p (p * L))))
    (level_antitone (Nat.dvd_mul_left (p * L) p)) (congrArg level hd)
  have hgroup : frickeOldLevel (p * (p * L)) (p * (p * L) / p)
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) = dilationLevel (p * L) p hp.pos := by
    exact (congrArg (fun d => frickeOldLevel (p * (p * L)) d
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))) hd).trans
        (frickeOldLevel_eq_dilationLevel (p * L) p (Nat.mul_pos hp.pos hL) hp.pos)
  have h2 := restrict_range_group_congr
    (G := level (p * (p * L)))
    (H := frickeOldLevel (p * (p * L)) (p * (p * L) / p)
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)))
    (J := dilationLevel (p * L) p hp.pos) k
    (level_le_frickeOldLevel (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))
      (Nat.div_dvd_of_dvd (Nat.dvd_mul_right p (p * L))))
    (level_le_dilation_conjugate (p * L) p hp.pos) hgroup
  have hi := congrArg₂ (fun A B : Submodule ℂ (CuspForm (level (p * (p * L))) k) => A ⊓ B) h1 h2
  change primeOldIntersection (p * (p * L))
    (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k (repeatedPrime L p hp) = _ at hi
  rw [hi]
  exact repeated_old_intersection_finrank L p hL hp k

/-- The exact classical second-difference formula for one repeated prime
 trace kernel. -/
theorem primeKernel_repeated_finrank (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (k : ℤ) :
    Module.finrank ℂ (primeTraceKernel (p * (p * L))
      (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k (repeatedPrime L p hp)) +
        2 * Module.finrank ℂ (CuspForm (level (p * L)) k) =
      Module.finrank ℂ (CuspForm (level (p * (p * L))) k) +
        Module.finrank ℂ (CuspForm (level L) k) := by
  have hh := primeKernel_finrank (p * (p * L))
    (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) k (repeatedPrime L p hp)
  rw [primeOldIntersection_repeated_finrank L p hL hp k] at hh
  dsimp only [repeatedPrime] at hh ⊢
  rw [Nat.mul_div_cancel_left (p * L) hp.pos] at hh
  exact hh

/-- The general repeated-prime recurrence preserves a bounded error,
so it can be used without weakening the quantitative remainder. -/
theorem kernel_dimension_bounded (L p : ℕ) (hL : 0<L) (hp : p.Prime) :
    ∃ C : ℝ,∀ᶠ k : ℕ in AsymptoticSectorComparison.evenWeights,
      |(Module.finrank ℂ (primeTraceKernel (p*(p*L))
        (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)) (k:ℤ) (repeatedPrime L p hp)):ℝ)-
          (AsymptoticClassicalDimension.fullLeading (p*(p*L))-
            2*AsymptoticClassicalDimension.fullLeading (p*L)+
              AsymptoticClassicalDimension.fullLeading L)*k|≤C := by
  have hM := Nat.mul_pos hp.pos hL
  have hN := Nat.mul_pos hp.pos hM
  obtain ⟨Cu,hu⟩ := QuantitativeEulerOldProjectionClassicalDimension.full_dimension_bounded (p*(p*L)) hN
  obtain ⟨Cm,hm⟩ := QuantitativeEulerOldProjectionClassicalDimension.full_dimension_bounded (p*L) hM
  obtain ⟨Cl,hl⟩ := QuantitativeEulerOldProjectionClassicalDimension.full_dimension_bounded L hL
  refine ⟨Cu+2*Cm+Cl,?_⟩
  filter_upwards [hu,hm,hl] with k hu hm hl
  have he := primeKernel_repeated_finrank L p hL hp (k:ℤ)
  have heR :
      (Module.finrank ℂ (primeTraceKernel (p*(p*L)) hN (k:ℤ) (repeatedPrime L p hp)):ℝ)+
        2*(Module.finrank ℂ (CuspForm (level (p*L)) (k:ℤ)):ℝ)=
      (Module.finrank ℂ (CuspForm (level (p*(p*L))) (k:ℤ)):ℝ)+
        (Module.finrank ℂ (CuspForm (level L) (k:ℤ)):ℝ) := by exact_mod_cast he
  rw [abs_le] at hu hm hl ⊢
  constructor <;> nlinarith [hu.1,hu.2,hm.1,hm.2,hl.1,hl.2]

#print axioms repeated_old_join_eq
#print axioms repeated_old_intersection_finrank
#print axioms primeOldIntersection_repeated_finrank
#print axioms primeKernel_repeated_finrank
#print axioms kernel_dimension_bounded

end QuantitativeArithmeticClassicalRepeated
