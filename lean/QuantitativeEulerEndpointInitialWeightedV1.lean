module

public import QuantitativeEulerEndpointInitialPowerV1
public import QuantitativeEulerEndpointInitialSandwichV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialWeighted
open QuantitativeEulerEndpointInitialPower

variable {𝔄 ι : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄] [Fintype ι]
variable (D : ι → 𝔄) (hD : ∀ i, 0≤D i) (C a : ι → ℝ)
  (hC : ∀ i, ‖D i‖≤(C i)^2) (ha : ∀ i, 0<a i)

def total : 𝔄 := ∑ i, (a i)⁻¹ • D i

def cap : ℝ := 1+∑ i, (a i)⁻¹*(C i)^2

def energy : 𝔄 := (cap C a)⁻¹ • total D a

def initial (m : ℕ) : 𝔄 := powerFilter (energy D C a) (2*m)

include ha in
theorem cap_pos : 0<cap C a := by
  have hh : 0≤∑ i, (a i)⁻¹*(C i)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (inv_nonneg.mpr (ha i).le) (sq_nonneg _))
  unfold cap
  linarith

include hD ha in
theorem total_nonneg : 0≤total D a :=
  Finset.sum_nonneg (fun i _ => smul_nonneg (inv_nonneg.mpr (ha i).le) (hD i))

include hC ha in
omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem total_norm_le : ‖total D a‖≤cap C a := by
  apply (norm_sum_le _ _).trans
  have hh : (∑ i, ‖(a i)⁻¹ • D i‖)≤∑ i, (a i)⁻¹*(C i)^2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (ha i))]
    exact mul_le_mul_of_nonneg_left (hC i) (inv_nonneg.mpr (ha i).le)
  exact hh.trans (by unfold cap; linarith)

include hD hC ha in
theorem energy_order : 0≤energy D C a ∧ energy D C a≤1 := by
  have hcap := cap_pos C a ha
  have h0 := total_nonneg D hD a ha
  have h1 : total D a≤(cap C a) • (1:𝔄) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hcap.le h0).mp (total_norm_le D C a hC ha)
  have hscaled := smul_le_smul_of_nonneg_left h1 (inv_nonneg.mpr hcap.le)
  simp only [smul_smul,inv_mul_cancel₀ hcap.ne',one_smul] at hscaled
  exact ⟨smul_nonneg (inv_nonneg.mpr hcap.le) h0,hscaled⟩

include hD ha in
theorem component_le (i : ι) : D i≤(cap C a*a i) • energy D C a := by
  classical
  have hsum : (a i)⁻¹ • D i≤total D a :=
    Finset.single_le_sum (fun j _ => smul_nonneg (inv_nonneg.mpr (ha j).le) (hD j)) (Finset.mem_univ i)
  have hh := smul_le_smul_of_nonneg_left hsum (ha i).le
  simp only [smul_smul,mul_inv_cancel₀ (ha i).ne',one_smul] at hh
  have he : (cap C a*a i) • energy D C a=a i • total D a := by
    rw [energy,smul_smul]
    congr 1
    field_simp [(cap_pos C a ha).ne']
  rw [he]
  exact hh

include hD hC ha in
theorem initial_order (m : ℕ) : 0 ≤ initial D C a m ∧ initial D C a m≤1 :=
  powerFilter_order _ (energy_order D hD C a hC ha).1 (energy_order D hD C a hC ha).2 (2*m)

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem initial_fixed (E : 𝔄) (hDE : ∀ i, D i*E=0) (m : ℕ) : initial D C a m*E=E := by
  apply powerFilter_fixed
  simp only [energy,total,smul_mul_assoc,Finset.sum_mul,hDE,smul_zero,Finset.sum_const_zero]

include hD hC ha in
/-- All original component energies are controlled simultaneously by the
same finite polynomial. The weighted cap is paid once at initialization. -/
theorem component_sandwich_norm (m : ℕ) (i : ι) :
    ‖powerFilter (energy D C a) m*D i*powerFilter (energy D C a) m‖≤
      (cap C a*a i)/(((2*m:ℕ):ℝ)+1) := by
  let X := powerFilter (energy D C a) m
  have horder := energy_order D hD C a hC ha
  have hX0 := (powerFilter_order _ horder.1 horder.2 m).1
  have hX := IsSelfAdjoint.of_nonneg hX0
  have hh := hX.conjugate_le_conjugate (component_le D hD C a ha i)
  have he : X*((cap C a*a i) • energy D C a)*X=
      (cap C a*a i) • (X*energy D C a*X) := by rw [mul_smul_comm,smul_mul_assoc]
  rw [he] at hh
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hh (hX.conjugate_nonneg (hD i))
  have hb := mul_pos (cap_pos C a ha) (ha i)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hb] at hn
  exact hn.trans ((mul_le_mul_of_nonneg_left
    (sandwiched_energy_norm _ horder.1 horder.2 m) hb.le).trans_eq (by ring))

#print axioms cap_pos
#print axioms energy_order
#print axioms component_le
#print axioms initial_order
#print axioms initial_fixed
#print axioms component_sandwich_norm
end QuantitativeEulerEndpointInitialWeighted
