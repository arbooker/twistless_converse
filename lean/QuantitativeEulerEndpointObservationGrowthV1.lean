module

public import QuantitativeEulerEndpointGeometryGrowthV1
public import QuantitativeEulerEndpointSectorSourceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeNewGap QuantitativeSpectralObservability
open QuantitativeSpectralExceptionalReducedRows
open scoped Classical MatrixGroups

theorem scalar_family_cost_bound {V L ε K H C : ℝ} (t : ℕ) (hV : 4≤V)
    (hL : |L|≤V) (hε : |ε|≤V) (hK : |K|≤V) (hH : |H|≤V) (hC : |C⁻¹|≤V) :
    |L*(1+ε*K*(H/C+3)^2)^(2*t)|≤V^(1+18*t) := by
  have hV0 : 0≤V := by linarith
  have hV1 : 1≤V := by linarith
  have hV3 : 3≤V := by linarith
  have htwo : (2:ℝ)≤V^2 := by nlinarith
  have hHC : |H/C|≤V^2 := by
    rw [div_eq_mul_inv,abs_mul]
    simpa only [pow_two] using mul_le_mul hH hC (abs_nonneg _) hV0
  have hHC3 : |H/C+3|≤V^3 := by
    have hh := two_height_sum_bound hV3 2 hHC htwo
    have ha := abs_add_le (H/C) 3
    rw [abs_of_pos (by norm_num : (0:ℝ)<3)] at ha
    linarith
  have hinner0 : |ε*K*(H/C+3)^2|≤V^8 := by
    rw [abs_mul,abs_mul,abs_pow]
    calc
      _ ≤ (V*V)*(V^3)^2 := mul_le_mul
        (mul_le_mul hε hK (abs_nonneg _) hV0)
        (pow_le_pow_left₀ (abs_nonneg _) hHC3 2) (by positivity) (by positivity)
      _ = _ := by ring
  have hinner : |1+ε*K*(H/C+3)^2|≤V^9 := by
    have hh := two_height_sum_bound hV3 8 hinner0 (show (0:ℝ)≤V^8 by positivity)
    have ha := abs_add_le (1:ℝ) (ε*K*(H/C+3)^2)
    rw [abs_one] at ha
    linarith
  rw [abs_mul,abs_pow]
  calc
    _ ≤ V*(V^9)^(2*t) := mul_le_mul hL
      (pow_le_pow_left₀ (abs_nonneg _) hinner _) (by positivity) hV0
    _ = _ := by rw [←pow_mul,pow_add,pow_one]; congr 1; congr 1; omega

variable (N : ℕ) (hN : 0<N) (sector : Sector N) (S : Finset SL(2,ℤ))
  (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)

theorem sector_observation_power_bound (W : Finset (List SL(2,ℤ))) (B H ε V : ℝ) (t : ℕ)
    (hV : 4≤V) (hB : |B|≤V) (hH : |H|≤V) (hε : |ε|≤V)
    (hterminal : |terminalObservationConstant S W|≤V)
    (hgap : |(sectorGap N hN)⁻¹|≤V)
    (hcard : (Fintype.card (SectorFamilyIndex N):ℝ)≤V)
    (hL : ∀ i, |sectorFamilyL N hN sector S hS i|≤V)
    (hK : ∀ i, |sectorFamilyK N hN sector S hS i|≤V)
    (hC : ∀ i, |(sectorFamilyC N hN sector S hS i)⁻¹|≤V) :
    sectorObservationCost N hN sector S hS W B H ε t≤V^(7+72*t) := by
  have hV0 : 0≤V := by linarith
  have hV1 : 1≤V := by linarith
  have hV3 : 3≤V := by linarith
  have hV2 : V≤V^2 := by nlinarith
  have hV4 : 4≤V^2 := by nlinarith
  have hfamily (i) : |sectorFamilyCost N hN sector S hS H ε t i|≤V^(1+18*t) :=
    scalar_family_cost_bound t hV (hL i) hε (hK i) hH (hC i)
  have hsum : (∑ i, (sectorFamilyCost N hN sector S hS H ε t i)^2)≤V^(3+36*t) := by
    calc
      _ ≤ ∑ _i : SectorFamilyIndex N, (V^(1+18*t))^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hfamily i) 2)
      _ = (Fintype.card (SectorFamilyIndex N):ℝ)*(V^(1+18*t))^2 := by simp
      _ ≤ V*(V^(1+18*t))^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = _ := by rw [←pow_mul,←pow_succ']; congr 1; omega
  have hgap0 : 0≤(sectorGap N hN)⁻¹ := inv_nonneg.mpr (sectorGap_pos N hN).le
  have hgap' : (sectorGap N hN)⁻¹≤V := (le_abs_self _).trans hgap
  have hgsum : (sectorGap N hN)⁻¹*∑ i,(sectorFamilyCost N hN sector S hS H ε t i)^2≤V^(4+36*t) := by
    calc
      _ ≤ V*V^(3+36*t) := mul_le_mul hgap' hsum (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hV0
      _ = _ := by rw [←pow_succ']; congr 1; omega
  have hsecond : 1+(sectorGap N hN)⁻¹*∑ i,(sectorFamilyCost N hN sector S hS H ε t i)^2≤V^(5+36*t) := by
    have hh := two_height_sum_bound hV3 (4+36*t) hgsum (show (0:ℝ)≤V^(4+36*t) by positivity)
    convert hh using 1 <;> ring
  have hfirst : |terminalObservationConstant S W*(1+B^2*(H+3)^2)^(2*t)|≤V^(2+36*t) := by
    have hh := scalar_family_cost_bound (V:=V^2) (L:=terminalObservationConstant S W)
      (ε:=1) (K:=B^2) (H:=H) (C:=1) t hV4 (hterminal.trans hV2)
      (by norm_num only [abs_one,inv_one]; nlinarith)
      (by simpa only [abs_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg B) hB 2)
      (hH.trans hV2) (by norm_num only [abs_one,inv_one]; nlinarith)
    simp only [one_mul,div_one] at hh
    convert hh using 1
    ring_nf
  unfold sectorObservationCost
  calc
    _ ≤ |terminalObservationConstant S W*(1+B^2*(H+3)^2)^(2*t)| *
        (1+(sectorGap N hN)⁻¹*∑ i,(sectorFamilyCost N hN sector S hS H ε t i)^2) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ V^(2+36*t)*V^(5+36*t) := mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by rw [←pow_add]; congr 1; omega

#print axioms scalar_family_cost_bound
#print axioms sector_observation_power_bound
end QuantitativeEulerEndpointPrepared
