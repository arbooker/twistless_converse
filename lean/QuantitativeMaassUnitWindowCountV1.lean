module

public import QuantitativeMaassUnitWindowMajorantV1
public import QuantitativeMaassUnitCoreEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

universe u

/-- Uniform linear counting for every finite orthonormal principal cuspidal
family in a unit spectral interval. The kernel and core are constructed. -/
theorem cuspidal_unit_finset_linear (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (ι : Type u) (t : ℝ),1≤t →
      ∀ (v : ι → AutomorphicSpace N) (r : ι → ℝ),
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      (∀ i,r i∈Icc (t-1/2) (t+1/2)) →
      (∀ i,FriedrichsGraph N (v i) (((1/4+(r i)^2:ℝ):ℂ) • v i)) →
      ∀ s : Finset ι,(s.card:ℝ)≤C*t := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨K,hK,he,hm,hc⟩ := exists_positive_bandlimited_window_kernel
  obtain ⟨R,hR,hmajor⟩ := exists_unit_window_majorant K hK hm
  let hRp := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨D,hD,hcore⟩ := exists_principal_unit_core_mass N hN
  obtain ⟨C,hC,hupper⟩ := windowAbelColumn_unit_core_energy N hN K he hc hK hm R hR D hD
  refine ⟨8*C,by positivity,?_⟩
  intro ι t ht v r hv hcusp hr hgraph s
  let S := wideCompactCover N (D*t)
  have hS : IsCompact S := wideCompactCover_compact N hN (D*t)
  let A := quotientRestriction N S hS hS.measurableSet
  let T := windowWavePacket N K hc R hRp (t-3/4) (t+3/4)
  let c := windowAbelColumn N K he hc R hRp (t-3/4) (t+3/4)
  have hlower (i : ι) : (1:ℝ)/8≤‖A (T (v i))‖^2 := by
    have hmass := hcore t (r i) ht (hr i) (v i) (hv.norm_eq_one i) (hcusp i) (hgraph i)
    have hscalar := hmajor t (r i) (hr i)
    let m := smoothedWindow K R
      (Icc (t-3/4) (t+3/4)∪Icc (-(t+3/4)) (-(t-3/4))) (r i)
    have hmhalf : (1:ℝ)/2≤m := hscalar
    have hm2 : (1:ℝ)/4≤m^2 := by nlinarith
    have hnorm : ‖A (T (v i))‖^2=m^2*‖A (v i)‖^2 := by
      dsimp only [T]
      rw [windowWavePacket_principal N K he hc R hRp (t-3/4) (t+3/4)
        (by linarith) (r i) (hgraph i),map_smul,norm_smul,mul_pow,
        Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [hnorm]
    change 1≤2*‖A (v i)‖^2 at hmass
    have hh := mul_le_mul_of_nonneg_right hm2 (sq_nonneg ‖A (v i)‖)
    nlinarith
  have hci : IntegrableOn (fun x => ‖c x‖^2) S volume :=
    ((windowAbelColumn_continuous N K he hc R hRp (t-3/4) (t+3/4)).norm.pow 2).continuousOn.integrableOn_compact hS
  have hb : ENNReal.ofReal ((s.card:ℝ)*(1/8))≤ENNReal.ofReal (C*t) := by
    calc
      _ = ∑ _i∈s,ENNReal.ofReal ((1:ℝ)/8) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ i∈s,ENNReal.ofReal (‖A (T (v i))‖^2) :=
        Finset.sum_le_sum (fun i _ => ENNReal.ofReal_le_ofReal (hlower i))
      _ ≤ ∑' i,ENNReal.ofReal (‖A (T (v i))‖^2) := ENNReal.sum_le_tsum s
      _ ≤ ∫⁻ x in S,ENNReal.ofReal (‖c x‖^2) :=
        windowWavePacket_raw_compact_bessel N K he hc R hRp (t-3/4) (t+3/4) v hv S hS
      _ = ENNReal.ofReal (∫ x in S,‖c x‖^2) :=
        (ofReal_integral_eq_lintegral_ofReal hci (Eventually.of_forall (fun x => sq_nonneg _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hupper t ht)
  have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤C*t)).mp hb
  nlinarith

#print axioms cuspidal_unit_finset_linear

end QuantitativeMaass
