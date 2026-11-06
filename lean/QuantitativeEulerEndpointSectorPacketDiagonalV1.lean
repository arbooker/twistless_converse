module

public import QuantitativeEulerEndpointSectorCountBoundaryV1
public import QuantitativeEulerEndpointSectorPacketBudgetV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticSectorSigns QuantitativeSpectralObservability Polynomial
open QuantitativeEulerDensityGenerators Filter Asymptotics
open scoped Classical MatrixGroups

/-- All original sector packets at H=n have O(1/log(n+1)) summed excess
above the arithmetic leading coefficient. Constants are fixed before n and t.
The packet reciprocal cuts have the separately proved polynomial budget. -/
theorem prepared_sector_packet_diagonal (N : ℕ) [NeZero N] (hN : 2≤N)
    (hAdm : GridAdmissibleGap.Admissible N)
    (excluded : Finset ℕ) (hex : baselineDenominators N⊆excluded) (threshold : ℕ)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    let d := fun e => sectorPacketWitness N hN e excluded hex threshold S hS hε
    ∃ A : ℝ, 0<A ∧ ∃ M : ℕ, 0<M ∧ ∀ n : ℕ,M≤n → ∀ (t : ℕ),1≤t →
      ∑ e : Sector N,cornerMass ((d e).packet n n t)≤
        4*Real.pi*AsymptoticTotalNewCorner.arithmeticCoefficient N+A/Real.log (n+1:ℝ) := by
  intro d
  let V := ∑ e : Sector N,∑ i : SectorFamilyIndex N,max 0 (sectorFamilyB N (NeZero.pos N) e S hS i)
  have hV : 0≤V := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  have hVi (e : Sector N) (i : SectorFamilyIndex N) : sectorFamilyB N (NeZero.pos N) e S hS i≤V := by
    apply (le_max_right 0 _).trans
    apply (Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (SectorFamilyIndex N))) =>
      le_max_left 0 (sectorFamilyB N (NeZero.pos N) e S hS j)) (Finset.mem_univ i)).trans
    exact Finset.single_le_sum
      (fun e' (_ : e'∈(Finset.univ : Finset (Sector N))) =>
        Finset.sum_nonneg (fun j (_ : j∈(Finset.univ : Finset (SectorFamilyIndex N))) =>
          le_max_left 0 (sectorFamilyB N (NeZero.pos N) e' S hS j))) (Finset.mem_univ e)
  let T := ∑ e : Sector N,sectorTailConstant N (NeZero.pos N) e S hS
  let E := ε⁻¹*∑ e : Sector N,(d e).A0
  have hT : 0≤T := Finset.sum_nonneg (fun e _ => sectorTailConstant_nonneg N (NeZero.pos N) e S hS)
  have hE : 0≤E := mul_nonneg (inv_nonneg.mpr hε.le) (Finset.sum_nonneg (fun e _ => (d e).hA0.le))
  obtain ⟨m,hm⟩ := exists_nat_gt (max ε⁻¹ 4+V)
  refine ⟨1+T+E,by positivity,m+1,by omega,?_⟩
  intro n hn t ht
  have hn0 : 0<n := by omega
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn0
  have hmn : (m:ℝ)≤n := by exact_mod_cast (show m≤n by omega)
  have hbound : max ε⁻¹ 4+V≤(n:ℝ) := hm.le.trans hmn
  have hbase : 0≤max ε⁻¹ 4 := (by norm_num : (0:ℝ)≤4).trans (le_max_right _ _)
  have hheight : max ε⁻¹ 4≤(n:ℝ) := (le_add_of_nonneg_right hV).trans hbound
  have hdata : ∀ e i, sectorFamilyB N (NeZero.pos N) e S hS i≤(n:ℝ) :=
    fun e i => (hVi e i).trans ((le_add_of_nonneg_left hbase).trans hbound)
  have hh := prepared_sector_packet_sum_arithmetic N hN hAdm excluded hex threshold S hS hε hn0 hheight hdata ht
  have hlog : 0<Real.log (n+1:ℝ) := Real.log_pos (by linarith)
  have hlogn : Real.log (n+1:ℝ)≤(n:ℝ) := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos (by linarith : (0:ℝ)<n+1)
  have htail : T/(n:ℝ)≤T/Real.log (n+1:ℝ) := div_le_div_of_nonneg_left hT hlog hlogn
  have hone : 0≤1/Real.log (n+1:ℝ) := by positivity
  change ∑ e : Sector N,cornerMass ((d e).packet n n t)≤
    4*Real.pi*AsymptoticTotalNewCorner.arithmeticCoefficient N+T/(n:ℝ)+E/Real.log (n+1:ℝ) at hh
  have he : (1+T+E)/Real.log (n+1:ℝ)=1/Real.log (n+1:ℝ)+T/Real.log (n+1:ℝ)+E/Real.log (n+1:ℝ) := by ring
  rw [he]
  linarith

#print axioms prepared_sector_packet_diagonal
end QuantitativeEulerEndpointPrepared
