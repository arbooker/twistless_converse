module

public import QuantitativeSpectralObservabilityReductionV1
public import QuantitativeSpectralObservabilityDecodedV1
public import AsymptoticDecodedQuotientV1
public import AsymptoticCongruenceDefectV1
public import AsymptoticOrbitBranchV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set
open AsymptoticCongruenceLabels AsymptoticHyperbolicArea
open AsymptoticOrbitDecode AsymptoticCompactBranch AsymptoticOrbitDiagonal
open QuantitativeSpectralObservabilityDecoded
open scoped MatrixGroups BigOperators lp

/-- Finite coordinatewise reconstruction controls the actual counting-L²
energy. Different coordinates may use different rows. -/
theorem finite_reconstruction_energy {I A : Type*} [Fintype I]
    (f : ℓ²(A,ℂ)) (u d : I → ℓ²(A,ℂ))
    (h : ∀ a, f a=0 ∨ ∃ i, f a=u i a-d i a) :
    ‖f‖^2 ≤ 2 * ∑ i, (‖u i‖^2+‖d i‖^2) := by
  classical
  have hn (v : ℓ²(A,ℂ)) : HasSum (fun a => ‖v a‖^2) (‖v‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) v
  have hp (a : A) : ‖f a‖^2 ≤ 2 * ∑ i, (‖u i a‖^2+‖d i a‖^2) := by
    rcases h a with ha | ⟨i,hi⟩
    · rw [ha,norm_zero,zero_pow (by decide : 2≠0)]
      positivity
    · have hs := Finset.single_le_sum
        (fun j (_ : j∈Finset.univ) => add_nonneg (sq_nonneg ‖u j a‖) (sq_nonneg ‖d j a‖))
        (Finset.mem_univ i)
      have ht := norm_sub_le (u i a) (d i a)
      rw [hi]
      have hsq := pow_le_pow_left₀ (norm_nonneg (u i a-d i a)) ht 2
      nlinarith [sq_nonneg (‖u i a‖-‖d i a‖)]
  have hr := (hasSum_sum (fun i (_ : i∈Finset.univ) => (hn (u i)).add (hn (d i)))).mul_left 2
  have hh := (hn f).summable.tsum_le_tsum hp hr.summable
  rwa [(hn f).tsum_eq,hr.tsum_eq] at hh

def terminalBand (ε H : ℝ) : Set ℍ := terminal ε ∩ {z | z.im ≤ H}

def terminalRectangle (ε H : ℝ) : Set ℍ :=
  {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ ε ≤ z.im ∧ z.im ≤ H}

theorem terminalRectangle_compact {ε : ℝ} (hε : 0<ε) (H : ℝ) :
    IsCompact (terminalRectangle ε H) := by
  have he : UpperHalfPlane.coe '' terminalRectangle ε H =
      Complex.measurableEquivRealProd.symm '' (Icc (0:ℝ) 1 ×ˢ Icc ε H) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(w.re,w.im),⟨⟨hw.1,hw.2.1⟩,hw.2.2⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,hxy,rfl⟩
      exact ⟨⟨⟨x,y⟩,hε.trans_le hxy.2.1⟩,⟨hxy.1.1,hxy.1.2,hxy.2⟩,rfl⟩
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff,he]
  apply (isCompact_Icc.prod isCompact_Icc).image
  exact Complex.equivRealProdCLM.symm.continuous

theorem terminalBand_subset_rectangle (ε H : ℝ) :
    terminalBand ε H ⊆ terminalRectangle ε H := by
  intro z hz
  exact ⟨hz.1.1.1,hz.1.1.2.le,hz.1.2.le,hz.2⟩

theorem cap_eq_one_of_terminal {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ)
    (hz : z∈terminal ε) : cap ε t z=1 := by
  have hh : (1:ℝ) ≤ z.im/ε := (one_le_div hε).mpr hz.2.le
  simp only [cap,min_eq_right hh,one_pow]

theorem decode_eq_self_of_terminal {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (x : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) (g : AsymptoticRationalGroup.Group)
    (hg : g • x∈terminal ε) : decode ε t x v g=v g := by
  rw [decode,AsymptoticCongruenceQuotient.foldLabel_self x g hg.1,
    cap_eq_one_of_terminal hε t (g • x) hg]
  simp

/-- The actual compact sampler and finitely many literal congruence
defects observe the whole truncated terminal strip. -/
theorem terminalBand_energy (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    (H : ℝ) (t : ℕ) (W : Finset (List SL(2,ℤ)))
    (hW : ∀ z∈terminalBand ε H, ∃ l∈W,
      integralLabel l.prod • z∈wideCompactCover N H)
    (x : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    ‖corner (terminalBand ε H) x v‖^2 ≤
      2 * ∑ l : W, (‖sampling N hN H hε t x v‖^2+
        ‖AsymptoticCongruenceDefect.operator l.val.prod
          (terminalRectangle_compact hε H) hε t x v‖^2) := by
  classical
  let u (l : W) := AsymptoticOrbitBranch.reindexLinear
    (Equiv.mulLeft (integralLabel l.val.prod)) (sampling N hN H hε t x v)
  let d (l : W) := AsymptoticCongruenceDefect.operator l.val.prod
    (terminalRectangle_compact hε H) hε t x v
  have he := finite_reconstruction_energy (corner (terminalBand ε H) x v) u d (by
    intro g
    by_cases hg : g • x∈terminalBand ε H
    · obtain ⟨l,hl,hlg⟩ := hW (g • x) hg
      right
      refine ⟨⟨l,hl⟩,?_⟩
      have hrect := terminalBand_subset_rectangle ε H hg
      have himg : (integralLabel l.prod*g) • x∈wideCompactCover N H := by
        simpa only [mul_smul] using hlg
      change corner (terminalBand ε H) x v g =
        sampling N hN H hε t x v (integralLabel l.prod*g) -
          AsymptoticCongruenceDefect.operator l.prod (terminalRectangle_compact hε H) hε t x v g
      rw [corner_apply,ite_eq_left hg,sampling_decode,ite_eq_left himg,
        AsymptoticCongruenceDefect.operator_decode,ite_eq_left hrect,
        cap_eq_one_of_terminal hε t (g • x) hg.1,
        decode_eq_self_of_terminal hε t x v g hg.1]
      simp
    · left
      rw [corner_apply,ite_eq_right hg])
  simpa only [u,d,AsymptoticOrbitBranch.reindex_norm] using he

#print axioms finite_reconstruction_energy
#print axioms terminalBand_energy

end QuantitativeSpectralObservability
