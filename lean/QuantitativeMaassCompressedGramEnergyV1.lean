module

public import QuantitativeMaassFiniteEnergyPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

/-- Add the identity on the discarded space to a compressed Gram operator.
The expression is polynomial even for an approximate projection. -/
def extendedCompressedGram (G P : E →L[ℂ] E) : E →L[ℂ] E := P*G*P+(1-P)

omit [CompleteSpace E] [Fintype ι] in
theorem extendedCompressedGram_norm (G P : E →L[ℂ] E) (hG : ‖G‖≤1) (hP : ‖P‖≤1) :
    ‖extendedCompressedGram G P‖≤3 := by
  have hp : ‖P*G‖≤1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg P])
  have hpp : ‖P*G*P‖≤1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (P*G)])
  have hi : ‖(1:E →L[ℂ] E)‖≤1 := ContinuousLinearMap.norm_id_le
  have hs := norm_sub_le (1:E →L[ℂ] E) P
  exact (norm_add_le _ _).trans (by nlinarith)

/-- Replacing a projection in the compressed Gram operator costs only a
fixed multiple of its squared Hilbert--Schmidt error. -/
theorem extendedCompressedGram_energy (b : OrthonormalBasis ι ℂ E)
    (G P Q : E →L[ℂ] E) (hG : ‖G‖≤1) (hP : ‖P‖≤1) (hQ : ‖Q‖≤1) :
    finiteBandEnergy b (extendedCompressedGram G Q-extendedCompressedGram G P) ≤
      10*finiteBandEnergy b (Q-P) := by
  have hqg : ‖Q*G‖≤1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg Q])
  have hgp : ‖G*P‖≤1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg G])
  have hqg2 : ‖Q*G‖^2≤1 := by nlinarith [norm_nonneg (Q*G)]
  have hgp2 : ‖G*P‖^2≤1 := by nlinarith [norm_nonneg (G*P)]
  have he := finiteBandEnergy_nonneg b (Q-P)
  have hleft := (finiteBandEnergy_left b (Q*G) (Q-P)).trans
    (mul_le_mul_of_nonneg_right hqg2 he)
  have hright := (finiteBandEnergy_right b (Q-P) (G*P)).trans
    (mul_le_mul_of_nonneg_right hgp2 he)
  simp only [one_mul] at hleft hright
  have hid : extendedCompressedGram G Q-extendedCompressedGram G P=
      ((Q*G)*(Q-P)+(Q-P)*(G*P))+(-(Q-P)) := by
    unfold extendedCompressedGram
    noncomm_ring
  have hneg : finiteBandEnergy b (-(Q-P))=finiteBandEnergy b (Q-P) := by
    simp [finiteBandEnergy,norm_sub_rev]
  have ha := finiteBandEnergy_add b ((Q*G)*(Q-P)) ((Q-P)*(G*P))
  have hb := finiteBandEnergy_add b (((Q*G)*(Q-P)+(Q-P)*(G*P))) (-(Q-P))
  rw [hneg] at hb
  rw [hid]
  linarith

#print axioms extendedCompressedGram_norm
#print axioms extendedCompressedGram_energy

end QuantitativeMaass
