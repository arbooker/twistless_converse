module

public import QuantitativeNinaMaassOldBandsV1
public import QuantitativeMaassUnitSpectralCountV1
public import QuantitativeMaassUnitBandCoverV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Module QuantitativeNinaMaass Set

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0 < N) :
    NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance

local instance (N : ℕ) (hN : 0 < N) :
    InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

local instance {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance

local instance {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance



/-- The actual finite cusp eigenfamily count is bounded by C*t*L on
a wide interval, with a single constant independent of its width. -/
theorem wide_cuspidal_family_linear (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (t L : ℝ),6≤t → 1≤L → L≤t/4 →
      ∀ (f : ι → AutomorphicSpace N) (r : ι → ℝ),Orthonormal ℂ f →
      (∀ i,f i∈localCuspidalSpace N hN) → (∀ i,r i∈Icc (t-L) (t+L)) →
      (∀ i,FriedrichsGraph N (f i) (((1/4+(r i)^2:ℝ):ℂ) • f i)) →
      (Fintype.card ι:ℝ)≤C*t*L := by
  obtain ⟨C,hC,hunit⟩ := cuspidal_unit_finset_linear N hN
  refine ⟨8*C,by positivity,?_⟩
  intro ι _ t L ht hL hLt f r hf hcus hr hgraph
  classical
  obtain ⟨n,hn,s,hs,hcover⟩ := unit_band_cover t L ht hL hLt
  let P := fun j : Fin n => fun i : ι => r i∈Icc (s j-1/2) (s j+1/2)
  have hbound (j : Fin n) : (Fintype.card {i // P j i}:ℝ)≤2*C*t := by
    have hj : 1≤s j := by have hh := (hs j).1; linarith
    have hh := hunit {i // P j i} (s j) hj (fun i => f i) (fun i => r i)
      (hf.comp Subtype.val Subtype.val_injective) (fun i => hcus i) (fun i => i.property)
      (fun i => hgraph i) Finset.univ
    simp only [Finset.card_univ] at hh
    exact hh.trans (by have hc := mul_le_mul_of_nonneg_left (hs j).2 hC.le; nlinarith only [hc])
  have hcard := finite_cover_card_le P (fun i => hcover (r i) (hr i))
  have hc : (Fintype.card ι:ℝ)≤∑ j : Fin n,(Fintype.card {i // P j i}:ℝ) := by
    exact_mod_cast hcard
  have hsum := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hbound j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hn' := mul_le_mul_of_nonneg_right hn (show 0≤2*C*t by positivity)
  exact (hc.trans hsum).trans (by nlinarith only [hn'])

/-- The full actual cusp parity band has dimension at most C_N*t*L,
including the exponentially growing widths used for localization. -/
theorem parityBand_wide_finrank_bound (N : ℕ) [NeZero N] (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (S : CuspEnergySpectrum N hN) (σ t L : ℝ),
      6≤t → 1≤L → L≤t/4 →
      (finrank ℂ (S.parityBand (t-L) (t+L) σ):ℝ)≤C*t*L := by
  obtain ⟨C,hC,hcount⟩ := wide_cuspidal_family_linear N hN
  refine ⟨C,hC,?_⟩
  intro S σ t L ht hL hLt
  classical
  have ho : Orthonormal ℂ (fun j => (S.basis j : AutomorphicSpace N)) :=
    S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let J := principalWindowIndices S.energy (t-L) (t+L)
  have hJ : J.Finite := principalWindowIndices_finite N hN _ ho (fun j => (S.basis j).property)
    S.energy S.energy_nonneg S.graph _ _
  let : Fintype J := hJ.fintype
  have hh := hcount t L ht hL hLt
    (fun i : J => (S.basis i.val : AutomorphicSpace N))
    (fun i : J => Real.sqrt (S.energy i.val-1/4))
    (ho.comp Subtype.val Subtype.val_injective) (fun i => (S.basis i.val).property)
    (fun i => i.property.2) (fun i => ?_)
  · let := S.band_finiteDimensional (t-L) (t+L)
    have hle := Submodule.finrank_le (S.parityBand (t-L) (t+L) σ)
    have hr := cuspPrincipalWindowSpace_finrank N hN S.basis S.energy S.energy_nonneg S.graph
      (t-L) (t+L)
    change finrank ℂ (S.band (t-L) (t+L))=_ at hr
    rw [hr] at hle
    have hle' : (finrank ℂ (S.parityBand (t-L) (t+L) σ):ℝ)≤(Fintype.card J:ℝ) := by
      exact_mod_cast (by simpa only [J,Nat.card_eq_fintype_card] using hle)
    exact hle'.trans hh
  · have hs := Real.sq_sqrt (sub_nonneg.mpr i.property.1)
    have heq : 1/4+(Real.sqrt (S.energy i.val-1/4))^2=S.energy i.val := by linarith
    rw [heq]
    exact S.graph i.val

#print axioms wide_cuspidal_family_linear
#print axioms parityBand_wide_finrank_bound

end QuantitativeMaass
