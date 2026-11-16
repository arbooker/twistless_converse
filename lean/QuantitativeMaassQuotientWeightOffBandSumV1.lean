module

public import QuantitativeMaassQuotientWeightOffBandV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open scoped InnerProductSpace

namespace QuantitativeMaass

/-- The separated literal-weight estimate also holds for arbitrary orthonormal
families, with summability proved from its finite-subfamily bound. -/
theorem quotientWeight_separated_tsum {ι : Type*}
    (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (r : ι → ℝ) (μ : ℝ)
    (f : ι → AutomorphicSpace N) (g : AutomorphicSpace N)
    (hf : Orthonormal ℂ f) (hr : ∀ i,0≤r i) (hμ : 0≤μ)
    (hgraph : ∀ i,FriedrichsGraph N (f i) ((r i:ℂ) • f i))
    (hg : FriedrichsGraph N g ((μ:ℂ) • g)) (L : ℝ) (hL : 0<L)
    (hsep : ∀ i,L≤|Real.sqrt (1+r i)-Real.sqrt (1+μ)|) :
    Summable (fun i => ‖inner ℂ (f i).val (quotientWeightMultiplier N hε ht g.val)‖^2) ∧
      (∑' i,‖inner ℂ (f i).val (quotientWeightMultiplier N hε ht g.val)‖^2)≤
        16*(4*quotientWeightBound ε*(2*t:ℝ))^2*‖g‖^2/L^2 := by
  classical
  have hfinite (s : Finset ι) :
      ∑ i∈s,‖inner ℂ (f i).val (quotientWeightMultiplier N hε ht g.val)‖^2≤
        16*(4*quotientWeightBound ε*(2*t:ℝ))^2*‖g‖^2/L^2 := by
    rw [←Finset.sum_coe_sort]
    exact quotientWeight_separated_mass N hε ht (fun i : s => r i) μ
      (fun i : s => f i) g (hf.comp Subtype.val Subtype.val_injective)
      (fun i => hr i) hμ (fun i => hgraph i) hg L hL (fun i => hsep i)
  have hs := summable_of_sum_le (fun _ => sq_nonneg _) hfinite
  exact ⟨hs,hs.tsum_le_of_sum_le hfinite⟩

/-- Summing over a finite orthonormal input band gives its dimension times
the actual weight leakage bound; no output dimension enters. -/
theorem quotientWeight_separated_family_energy {ι κ : Type*} [Fintype κ]
    (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (r : ι → ℝ) (μ : κ → ℝ)
    (f : ι → AutomorphicSpace N) (g : κ → AutomorphicSpace N)
    (hf : Orthonormal ℂ f) (hg : Orthonormal ℂ g)
    (hr : ∀ i,0≤r i) (hμ : ∀ j,0≤μ j)
    (hfgraph : ∀ i,FriedrichsGraph N (f i) ((r i:ℂ) • f i))
    (hggraph : ∀ j,FriedrichsGraph N (g j) ((μ j:ℂ) • g j)) (L : ℝ) (hL : 0<L)
    (hsep : ∀ i j,L≤|Real.sqrt (1+r i)-Real.sqrt (1+μ j)|) :
    (∑ j,∑' i,‖inner ℂ (f i).val (quotientWeightMultiplier N hε ht (g j).val)‖^2)≤
      16*(4*quotientWeightBound ε*(2*t:ℝ))^2*(Fintype.card κ:ℝ)/L^2 := by
  classical
  have hj (j : κ) : (∑' i,‖inner ℂ (f i).val (quotientWeightMultiplier N hε ht (g j).val)‖^2)≤
      16*(4*quotientWeightBound ε*(2*t:ℝ))^2/L^2 := by
    have hh := (quotientWeight_separated_tsum N hε ht r (μ j) f (g j) hf hr (hμ j)
      hfgraph (hggraph j) L hL (fun i => hsep i j)).2
    simpa only [hg.norm_eq_one j,one_pow,mul_one] using hh
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hj j)
  convert hh using 1
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

#print axioms quotientWeight_separated_tsum
#print axioms quotientWeight_separated_family_energy

end QuantitativeMaass
