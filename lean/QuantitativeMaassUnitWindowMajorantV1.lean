module

public import QuantitativeMaassWindowMajorantV1
public import QuantitativeArithmeticMaassCuspLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeSpectralObservability QuantitativeArithmeticMaassCuspBand
open scoped Topology MatrixGroups InnerProductSpace ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- One fixed smoothing radius majorizes every unit spectral interval, with
multiplier at least one half on that interval. -/
theorem exists_unit_window_majorant (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ R : ℝ,1≤R ∧ ∀ t r : ℝ,r∈Icc (t-1/2) (t+1/2) →
      (1:ℝ)/2≤smoothedWindow K R (Icc (t-3/4) (t+3/4)∪Icc (-(t+3/4)) (-(t-3/4))) r := by
  let m := ∫ u,|u| * K u
  have hm0 : 0≤m := integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (hK u))
  let R := 8*m+1
  have hR : 1≤R := by dsimp [R]; linarith
  have hRp : 0<R := by linarith
  refine ⟨R,hR,?_⟩
  intro t r hr
  have hh := enlarged_symmetricWindow_lower K hK hm R hRp
    (t-1/2) (t+1/2) (1/4) r (by norm_num) hr 1
  have ha : t-1/2-1/4=t-3/4 := by ring
  have hb : t+1/2+1/4=t+3/4 := by ring
  simp only [ha,hb,pow_one] at hh
  have htail : m/(R*(1/4))≤1/2 := by
    apply (div_le_iff₀ (by positivity : 0<R*(1/4))).mpr
    dsimp [R]
    linarith
  exact (by linarith : (1:ℝ)/2≤1-m/(R*(1/4))).trans hh

/-- One linear cusp height captures at least half the mass of every normalized
principal cusp eigenvector in every unit interval with centre at least one. -/
theorem exists_principal_unit_core_mass (N : ℕ) (hN : 0<N) :
    ∃ D : ℝ,2≤D ∧ ∀ t r : ℝ,1≤t → r∈Icc (t-1/2) (t+1/2) →
      ∀ v : AutomorphicSpace N,‖v‖=1 → v∈localCuspidalSpace N hN →
      FriedrichsGraph N v (((1/4+r^2:ℝ):ℂ) • v) →
      1≤2*‖quotientRestriction N (wideCompactCover N (D*t))
        (wideCompactCover_compact N hN (D*t)) (wideCompactCover_compact N hN (D*t)).measurableSet v‖^2 := by
  let n : ℝ := Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  let T : ℝ := 8*n*N^2*(N+1)
  have hT : 0≤T := by dsimp [T,n]; positivity
  let D := 2+Real.sqrt (3*T)
  have hD : 2≤D := by dsimp [D]; linarith [Real.sqrt_nonneg (3*T)]
  have hDsq : 3*T≤D^2 := by
    dsimp [D]
    nlinarith [Real.sq_sqrt (by positivity : 0≤3*T),Real.sqrt_nonneg (3*T)]
  refine ⟨D,hD,?_⟩
  intro t r ht hr v hv hcusp hgraph
  obtain ⟨u,hu,hform⟩ := (friedrichsGraph_iff_form N _ _).mp hgraph
  let E := (1:ℝ)/4+r^2
  have henergy : (quotientClosedEnergy N u u).re≤E*‖energyInclusion N u‖^2 := by
    have hself : (inner ℂ v v).re=‖v‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) v
    rw [hform u,hu,inner_smul_right (𝕜:=ℂ) v v ((1/4+r^2:ℝ):ℂ),
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      hself]
  have hE : E≤3*t^2 := by
    have hr0 : 0≤r := by linarith [hr.1]
    have hrr := pow_le_pow_left₀ hr0 hr.2 2
    dsimp [E]
    nlinarith [sq_nonneg (t-1)]
  have hsize : 8*(Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*N^2*(N+1)*E≤(D*t)^2 := by
    calc
      _ = T*E := rfl
      _ ≤ T*(3*t^2) := mul_le_mul_of_nonneg_left hE hT
      _ = (3*T)*t^2 := by ring
      _ ≤ D^2*t^2 := mul_le_mul_of_nonneg_right hDsq (sq_nonneg t)
      _ = _ := by ring
  have hh := cuspidal_bounded_energy_core N hN E (D*t) (by nlinarith) hsize
    u (by simpa only [hu] using hcusp) henergy
  simpa only [hu,hv,one_pow] using hh

#print axioms exists_unit_window_majorant
#print axioms exists_principal_unit_core_mass

end QuantitativeMaass
