module

public import QuantitativeMaassNewSignGramLeakageV1
public import QuantitativeMaassFixedCompressionEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open QuantitativeNinaMaass ContinuousLinearMap
namespace QuantitativeMaass.WideInput

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

def radius (B L : ℝ) : ℕ → ℝ
  | 0 => B
  | n+1 => radius B L n+L+2

theorem radius_mono (B L : ℝ) (hL : 0≤L) : Monotone (radius B L) := by
  apply monotone_nat_of_le_succ
  intro n
  dsimp only [radius]
  linarith

def projection {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (t B : ℝ) :
    localCuspidalSpace N hN →L[ℂ] localCuspidalSpace N hN :=
  (S.band (t-B) (t+B)).starProjection

theorem projection_norm {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (t B : ℝ) :
    ‖projection S t B‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  simpa only [projection,one_mul] using (S.band (t-B) (t+B)).norm_starProjection_apply_le x

variable {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN)
  {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν) (χ : admissibleGeneratorIndex N hN → ℂ)
  (t B L : ℝ)

/-- Successive compression starts at any prescribed input width B. -/
def path : ℕ → S.band (t-B) (t+B) →L[ℂ] localCuspidalSpace N hN
  | 0 => (S.band (t-B) (t+B)).subtypeL
  | n+1 => (projection S t (radius B L (n+1))).comp
      ((newSignWeightedGram N hN hδ hν χ).comp (path n))

theorem path_mem (n : ℕ) (x : S.band (t-B) (t+B)) :
    path S hδ hν χ t B L n x∈S.band (t-radius B L n) (t+radius B L n) := by
  cases n with
  | zero => exact x.property
  | succ n => exact (S.band _ _).starProjection_apply_mem _

theorem path_norm (n : ℕ) : ‖path S hδ hν χ t B L n‖≤1 := by
  induction n with
  | zero =>
    apply opNorm_le_bound _ zero_le_one
    intro x
    change ‖x.val‖≤1*‖x‖
    simp
  | succ n ih =>
    apply opNorm_le_bound _ zero_le_one
    intro x
    change ‖projection S t (radius B L (n+1))
      (newSignWeightedGram N hN hδ hν χ (path S hδ hν χ t B L n x))‖≤1*‖x‖
    calc
      _ ≤ ‖newSignWeightedGram N hN hδ hν χ (path S hδ hν χ t B L n x)‖ := by
        simpa only [one_mul] using (projection S t _).le_of_opNorm_le (projection_norm S t _) _
      _ ≤ ‖path S hδ hν χ t B L n x‖ := by
        simpa only [one_mul] using (newSignWeightedGram N hN hδ hν χ).le_of_opNorm_le
          (newSignWeightedGram_norm N hN hδ hν χ) _
      _ ≤ _ := (path S hδ hν χ t B L n).le_of_opNorm_le ih x

theorem path_step_energy {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℂ (S.band (t-B) (t+B))) (n : ℕ)
    (hL : 0<L) (ht : radius B L n+L+2≤t) :
    finiteSourceEnergy v ((newSignWeightedGram N hN hδ hν χ).comp
      (path S hδ hν χ t B L n)-path S hδ hν χ t B L (n+1)) ≤
      16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
        (Module.finrank ℂ (S.band (t-radius B L n) (t+radius B L n)):ℝ)/L^2 := by
  let T := (path S hδ hν χ t B L n).codRestrict
    (S.band (t-radius B L n) (t+radius B L n)) (path_mem S hδ hν χ t B L n)
  have hn : ‖T‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro x
    exact (path S hδ hν χ t B L n).le_of_opNorm_le (path_norm S hδ hν χ t B L n) x
  have hh := newSignWeightedGram_nested_energy S hδ hν χ v t (radius B L n) L hL ht T
  have hn2 : ‖T‖^2≤1 := by nlinarith [norm_nonneg T]
  exact hh.trans ((mul_le_mul_of_nonneg_right hn2 (by positivity)).trans_eq (one_mul _))

def ambientPath : ℕ → S.band (t-B) (t+B) →L[ℂ] localCuspidalSpace N hN
  | 0 => (S.band (t-B) (t+B)).subtypeL
  | n+1 => (newSignWeightedGram N hN hδ hν χ).comp (ambientPath n)

def fixedPath (Bouter : ℝ) : ℕ → S.band (t-B) (t+B) →L[ℂ] localCuspidalSpace N hN
  | 0 => (S.band (t-B) (t+B)).subtypeL
  | n+1 => ((projection S t Bouter).comp (newSignWeightedGram N hN hδ hν χ)).comp (fixedPath Bouter n)

/-- The literal normalized Gram and its repeated compression to one outer
band agree up to a quantified energy error, for arbitrary input width. -/
theorem fixed_energy {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℂ (S.band (t-B) (t+B))) (Bouter : ℝ) (n : ℕ)
    (hL : 0<L) (houter : radius B L n≤Bouter)
    (ht : ∀ j<n, radius B L j+L+2≤t) :
    finiteSourceEnergy v (ambientPath S hδ hν χ t B n-fixedPath S hδ hν χ t B Bouter n) ≤
      4*(2:ℝ)^n*∑ j∈Finset.range n,
        16*(4*quotientWeightBound δ*(2*ν:ℝ))^2*
          (Module.finrank ℂ (S.band (t-radius B L j) (t+radius B L j)):ℝ)/L^2 := by
  have hfix (j : ℕ) (hj : j≤n) :
      (projection S t Bouter).comp (path S hδ hν χ t B L j)=path S hδ hν χ t B L j := by
    apply ContinuousLinearMap.ext
    intro x
    change (S.band (t-Bouter) (t+Bouter)).starProjection (path S hδ hν χ t B L j x)=
      path S hδ hν χ t B L j x
    apply (S.band (t-Bouter) (t+Bouter)).starProjection_eq_self_iff.mpr
    have hmono : S.band (t-radius B L j) (t+radius B L j)≤S.band (t-Bouter) (t+Bouter) := by
      apply Submodule.span_mono
      rintro y ⟨i,rfl⟩
      have hr := (radius_mono B L hL.le hj).trans houter
      refine ⟨⟨i.val,i.property.1,?_,?_⟩,rfl⟩
      · linarith [i.property.2.1]
      · linarith [i.property.2.2]
    exact hmono (path_mem S hδ hν χ t B L j x)
  have hb := fixed_compression_energy v (fun _ => newSignWeightedGram N hN hδ hν χ)
    (projection S t Bouter) (ambientPath S hδ hν χ t B)
    (path S hδ hν χ t B L) (fixedPath S hδ hν χ t B Bouter)
    (fun _ => newSignWeightedGram_norm N hN hδ hν χ) (projection_norm S t Bouter)
    rfl rfl (fun _ => rfl) (fun _ => rfl) n hfix
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact path_step_energy S hδ hν χ t B L v j hL (ht j (Finset.mem_range.mp hj))

#print axioms path_step_energy
#print axioms fixed_energy
end QuantitativeMaass.WideInput
