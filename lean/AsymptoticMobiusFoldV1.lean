module

public import AsymptoticHyperbolicSlashV1
public import AsymptoticMassTransportV1
public import FinitenessGlobalHeightV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticMobiusFold

open UpperHalfPlane Matrix Set AsymptoticHyperbolicSlash

/-- Translation matrices, over either the rationals or the reals. -/
def translation {K : Type*} [Field K] (r : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,r;0,1] (by simp)

theorem translation_det {K : Type*} [Field K] (r : K) : (translation r).det.val=1 := by
  change Matrix.det !![1,r;0,1]=1
  simp

theorem translation_action (r : ℝ) (z : ℍ) :
    ((translation r • z:ℍ):ℂ)=(z:ℂ)+(r:ℂ) := by
  rw [coe_smul_of_det_pos (by rw [translation_det]; norm_num)]
  change ((1:ℂ)*(z:ℂ)+(r:ℂ))/((0:ℂ)*(z:ℂ)+1)=_
  ring

theorem translation_phase (r : ℝ) (k : ℕ) (z : ℍ) : phase (translation r) k z=1 := by
  have hd : denom (translation r) z=1 := by
    change (0:ℂ)*(z:ℂ)+1=1
    ring
  simp [phase,hd]

noncomputable def fold (g : GL (Fin 2) ℝ) (n : ℤ) : GL (Fin 2) ℝ := translation (-(n:ℝ))*g

theorem fold_action (g : GL (Fin 2) ℝ) (n : ℤ) (z : ℍ) :
    ((fold g n • z:ℍ):ℂ)=((g • z:ℍ):ℂ)-(n:ℂ) := by
  rw [fold,mul_smul,translation_action]
  push_cast
  ring

theorem fold_im (g : GL (Fin 2) ℝ) (n : ℤ) (z : ℍ) : (fold g n • z).im=(g • z).im := by
  simpa using congrArg Complex.im (fold_action g n z)

theorem fold_re (g : GL (Fin 2) ℝ) (n : ℤ) (z : ℍ) :
    (fold g n • z).re=(g • z).re-(n:ℝ) := by
  simpa using congrArg Complex.re (fold_action g n z)

theorem fold_phase (g : GL (Fin 2) ℝ) (hg : 0<g.det.val) (n : ℤ) (k : ℕ) (z : ℍ) :
    phase (fold g n) k z=phase g k z := by
  rw [fold,phase_mul _ _ hg,translation_phase,one_mul]

theorem fold_mem_strip_iff (g : GL (Fin 2) ℝ) (n : ℤ) (z : ℍ) :
    fold g n • z∈AsymptoticMassTransport.strip ↔ n=Int.floor (g • z).re := by
  change (0≤(fold g n • z).re ∧ (fold g n • z).re<1) ↔ _
  rw [fold_re,eq_comm,Int.floor_eq_iff]
  constructor <;> intro hn <;> constructor <;> linarith [hn.1,hn.2]

theorem periodic_fold (g : GL (Fin 2) ℝ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (n : ℤ) (z : ℍ) : F (fold g n • z:ℍ)=F (g • z:ℍ) := by
  rw [fold_action]
  have hp' : Function.Periodic F (1:ℂ) := hp
  simpa using (hp'.zsmul n).sub_eq ((g • z:ℍ):ℂ)

/-- Only finitely many translation folds can meet a fixed compact
observation region. The chosen folds do not depend on weight. -/
theorem compact_folds (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsCompact s) :
    ∃ I : Finset ℤ,∀ z∈s,Int.floor (g • z).re∈I := by
  have hc : Continuous (fun z : ℍ => (g • z).re) :=
    continuous_re.comp (continuous_const_smul g)
  obtain ⟨a,ha⟩ := hs.bddBelow_image hc.continuousOn
  obtain ⟨b,hb⟩ := hs.bddAbove_image hc.continuousOn
  refine ⟨Finset.Icc (Int.floor a) (Int.floor b),?_⟩
  intro z hz
  exact Finset.mem_Icc.mpr ⟨Int.floor_mono (ha (Set.mem_image_of_mem _ hz)),
    Int.floor_mono (hb (Set.mem_image_of_mem _ hz))⟩

#print axioms translation_action
#print axioms fold_phase
#print axioms fold_mem_strip_iff
#print axioms compact_folds

end AsymptoticMobiusFold
