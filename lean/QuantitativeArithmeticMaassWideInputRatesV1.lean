module

public import QuantitativeArithmeticMaassWideInputPolynomialV1
public import QuantitativeMaassStrongCutoffWordGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
open Filter QuantitativeNinaMaass
open scoped Topology
namespace QuantitativeMaass.WideInput

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

theorem radius_cost {B L : ℝ} (hL : 1≤L) (hB : B≤L) (n : ℕ) :
    (2:ℝ)^n*(n:ℝ)*radius B L n≤4*(8:ℝ)^n*L := by
  have hn : (n:ℝ)+1≤(2:ℝ)^n := by exact_mod_cast n.lt_two_pow_self.succ_le
  have hRn : radius B L n≤4*((n:ℝ)+1)*L := by
    rw [radius_eq]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (show 0≤L-1 by linarith)]
  have hRpow : radius B L n≤4*(2:ℝ)^n*L := hRn.trans (by gcongr)
  calc
    _ ≤ (2:ℝ)^n*(n:ℝ)*(4*(2:ℝ)^n*L) :=
      mul_le_mul_of_nonneg_left hRpow (by positivity)
    _ ≤ (2:ℝ)^n*(2:ℝ)^n*(4*(2:ℝ)^n*L) := by gcongr; linarith
    _ = _ := by
      rw [show (8:ℝ)=2^3 by norm_num,←pow_mul,Nat.mul_comm 3 n,pow_mul]
      ring

/-- A wide starting window still permits all intermediate windows to remain
sublinear. There is no unit-width input assumption. -/
theorem radius_uniform_quarter (a D : ℝ) (ha : 0≤a) (hD : 0≤D) :
    ∀ᶠ t in atTop,∀ B : ℝ,B≤Real.exp (D*Strong.strongScale t) →
      ∀ n : ℕ,(n:ℝ)≤a*Strong.strongScale t →
        radius B (Real.exp (D*Strong.strongScale t)) n≤t/4 := by
  let K := a+D+4
  have hK : 0≤K := by dsimp only [K]; linarith
  filter_upwards [Strong.exponential_band_width_quarter K hK,
    Strong.strongScale_tendsto.eventually (eventually_ge_atTop (1:ℝ))] with t ht hs
  intro B hB n hn
  let L := Real.exp (D*Strong.strongScale t)
  have hL : 1≤L := Real.one_le_exp (mul_nonneg hD (by linarith))
  have hnexp : (n:ℝ)+1≤Real.exp (a*Strong.strongScale t) :=
    (Real.add_one_le_exp (n:ℝ)).trans (Real.exp_le_exp.mpr hn)
  have hR : radius B L n≤4*((n:ℝ)+1)*L := by
    rw [radius_eq]
    change B≤L at hB
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) (show 0≤L-1 by linarith)]
  have hfour : 4≤Real.exp (4*Strong.strongScale t) := by
    have hh := Real.add_one_le_exp (4*Strong.strongScale t)
    linarith
  apply (hR.trans _).trans ht.2
  calc
    _ ≤ Real.exp (4*Strong.strongScale t)*Real.exp (a*Strong.strongScale t)*L := by gcongr
    _ = Real.exp (K*Strong.strongScale t) := by
      dsimp only [L,K]
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      ring

/-- Actual Gram powers and fixed-band compressed powers agree in weighted
energy, uniformly for exponentially wide input bands and growing powers. -/
theorem weighted_fixed_compression (N : ℕ) [NeZero N] (hN : 0<N)
    (S : CuspEnergySpectrum N hN) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN → ℂ)
    (a Dinput W : ℝ) (ha : 0≤a) (hDi : 0≤Dinput)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ D : ℝ,Dinput≤D ∧ 0<D ∧ ∃ M : ℝ → ℝ,
      Tendsto (fun t => Real.exp (W*Strong.strongScale t)*M t/(t*ε t)) atTop (𝓝 0) ∧
      ∀ᶠ t in atTop,∀ B : ℝ,1≤B → B≤Real.exp (Dinput*Strong.strongScale t) →
        ∀ n : ℕ,(n:ℝ)≤a*Strong.strongScale t → ∀ Bouter : ℝ,
        radius B (Real.exp (D*Strong.strongScale t)) n≤Bouter →
        ∀ {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ (S.band (t-B) (t+B))),
        finiteSourceEnergy v (ambientPath S hδ hν χ t B n-fixedPath S hδ hν χ t B Bouter n)≤M t := by
  obtain ⟨C,hC,hcount⟩ := fixed_count_energy N hN
  let G : ℝ := (4*quotientWeightBound δ*(2*ν:ℝ))^2
  have hG : 0≤G := sq_nonneg _
  let p := a*Real.log 8
  have hp : 0≤p := mul_nonneg ha (Real.log_nonneg (by norm_num))
  let D := Dinput+|W|+p+1
  have hD : 0<D := by dsimp only [D]; linarith [abs_nonneg W]
  have hDiD : Dinput≤D := by dsimp only [D]; linarith [abs_nonneg W]
  let K := 256*C*G
  have hK : 0≤K := by dsimp only [K]; positivity
  let M := fun t => K*t*Real.exp ((p-D)*Strong.strongScale t)
  refine ⟨D,hDiD,hD,M,?_,?_⟩
  · have hlim := (Strong.strong_exponential_div_width ε hε hproduct).const_mul K
    simp only [mul_zero] at hlim
    apply squeeze_zero' _ _ hlim
    · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
      dsimp only [M]
      positivity
    · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
      have hs : 0≤Strong.strongScale t := sq_nonneg _
      have he' : W*Strong.strongScale t+(p-D)*Strong.strongScale t≤-Strong.strongScale t := by
        have hh := mul_le_mul_of_nonneg_right (le_abs_self W) hs
        have hi := mul_nonneg hDi hs
        dsimp only [D]
        nlinarith only [hh,hi]
      have hid : Real.exp (W*Strong.strongScale t)*M t/(t*ε t)=
          K*(Real.exp (W*Strong.strongScale t+(p-D)*Strong.strongScale t)/ε t) := by
        dsimp only [M]
        rw [Real.exp_add]
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he') he.le) hK
  · filter_upwards [radius_uniform_quarter a D ha hD.le,eventually_ge_atTop (6:ℝ)] with t ht ht6
    intro B hB hBi n hn Bouter hout ι _ v
    let L := Real.exp (D*Strong.strongScale t)
    have hL : 1≤L := Real.one_le_exp (mul_nonneg hD.le (sq_nonneg _))
    have hBL : B≤L := hBi.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hDiD (sq_nonneg _)))
    have hL0 : 0<L := Real.exp_pos _
    have hh := hcount S hδ hν χ t B L Bouter ht6 hB hL0 n (ht B hBL n hn) hout n le_rfl v
    have hc := mul_le_mul_of_nonneg_left (radius_cost hL hBL n)
      (show 0≤64*C*G*t/L^2 by positivity)
    have hb : finiteSourceEnergy v
        (ambientPath S hδ hν χ t B n-fixedPath S hδ hν χ t B Bouter n)≤
        K*(8:ℝ)^n*t/L := by
      apply hh.trans
      calc
        _ = (64*C*G*t/L^2)*((2:ℝ)^n*(n:ℝ)*radius B L n) := by dsimp only [G]; ring
        _ ≤ (64*C*G*t/L^2)*(4*(8:ℝ)^n*L) := hc
        _ = _ := by dsimp only [K]; field_simp; ring
    apply hb.trans
    have he := Strong.eight_pow_le_root_exponential a t n hn
    calc
      _ ≤ K*Real.exp (p*Strong.strongScale t)*t/L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hK) (by linarith)
      _ = M t := by
        dsimp only [M,L]
        rw [sub_mul,Real.exp_sub]
        ring

#print axioms weighted_fixed_compression
end QuantitativeMaass.WideInput
