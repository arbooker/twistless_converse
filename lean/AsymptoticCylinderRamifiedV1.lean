module

public import AsymptoticRamifiedObservationV1
public import AsymptoticCylinderTwistV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderRamified

open UpperHalfPlane Set FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticCylinder

def eigenvalue {N : ℕ} (e : Sector N) (p : ℕ) : ℂ := if p^2∣N then 0 else delta e p

theorem eigenvalue_norm_le {N : ℕ} (e : Sector N) (p : ℕ) : ‖eigenvalue e p‖≤1 := by
  unfold eigenvalue
  split_ifs <;> simp only [norm_zero,zero_le_one,delta_norm,le_refl]

theorem coefficient_row {N h d : ℕ} (e : Sector N) (p : ℕ) (hp : p.Prime) (hpN : p∣N)
    (a : AsymptoticRamifiedSectors.sector N h d e) (n : ℕ) :
    a.val.val (p*n)=eigenvalue e p*(p:ℂ)^h*a.val.val n := by
  by_cases hsq : p^2∣N
  · rw [eigenvalue,ite_eq_left hsq,a.property.2.2 p hp hsq n]
    ring
  · rw [eigenvalue,ite_eq_right hsq]
    exact a.property.2.1 p (mem_simplePrimes.mpr ⟨hp,hpN,hsq⟩) n

noncomputable def operator {N : ℕ} (e : Sector N) (p : ℕ) (hp : p.Prime)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  (AsymptoticRamifiedObservation.residual p hp.pos hs hε t m (eigenvalue e p)).comp
    AsymptoticCylinderLift.lift.toContinuousLinearMap

theorem operator_norm_le {N : ℕ} (e : Sector N) (p : ℕ) (hp : p.Prime)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    ‖operator e p hp hs hε t m‖≤AsymptoticRamifiedObservation.bound p hp.pos hs hε t+
      AsymptoticTwistObservation.branchBound 1 hs hε t := by
  have hl : ‖AsymptoticCylinderLift.lift.toContinuousLinearMap‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖AsymptoticCylinderLift.lift f‖≤1*‖f‖
    rw [AsymptoticCylinderLift.lift_norm,one_mul]
  have hb := AsymptoticRamifiedObservation.residual_norm_le p hp.pos hs hε t m (eigenvalue e p)
  have hδ := mul_le_mul_of_nonneg_right (eigenvalue_norm_le e p)
    (AsymptoticTwistObservation.branchBound_nonneg 1 hs hε t)
  rw [one_mul] at hδ
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hl (norm_nonneg _)).trans
  rw [mul_one]
  exact hb.trans (add_le_add le_rfl hδ)

theorem sector_annihilated {N Q : ℕ} {hQ : 0<Q} {A : Certificate N Q hQ}
    (P : Parameters A) (h : ℕ) (e : Sector N) (p : ℕ) (hp : p.Prime) (hpN : p∣N)
    {s : Set ℍ} (hs : IsCompact s)
    (w : holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (hw : w∈eulerCylinderSector P h e) :
    operator e p hp hs P.epsilon_pos (P.s+4) (h+1) (w:Space)=0 := by
  obtain ⟨a,rfl⟩ := hw
  exact AsymptoticRamifiedObservation.residual_eq_zero p hp.pos hs P.epsilon_pos (P.s+4) h
    (eigenvalue e p) a.val.val (coefficientSpace_polynomial _ a.val)
    (coefficient_row e p hp hpN a) _
    (AsymptoticCylinderLift.lift_fourierMap h (P.s+4) (h+1+P.s) P.epsilon_pos (by omega) a.val)

#print axioms coefficient_row
#print axioms operator_norm_le
#print axioms sector_annihilated

end AsymptoticCylinderRamified
