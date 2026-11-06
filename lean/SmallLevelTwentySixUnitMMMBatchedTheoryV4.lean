module

public import SmallLevelPrimeRatesTheoryV4
public import SmallLevelTwentySixGridFullMatricesV1
public import SmallLevelTwentySixIntegerParametersV1
public import SmallLevelTwentySixResultantBatchedMMMTheoryV4
public import SmallLevelTwentySixUnitMMMTheoryV4
public import SmallLevelTwentySixUnitMMMWeightResultantsTheoryV4
public import SmallLevelTwentySixWeightAbelPhysicalV1

/-! Consolidated chapter: SmallLevelTwentySixUnitMMMBatched. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixUnitMMMBatchedIntegerKernelV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMMBatched
open SmallLevelTwentySixUnitMMM
open Complex SmallLevelTwentySixIntegerParameters

/-- The original finite leading system has no nonzero supported kernel at
any positive integer exponent, for arbitrary unramified Hecke parameters. -/
theorem source_kernel_positive_integer (sx sz : ℤ) (n : ℕ)
    (hx : sx=1 ∨ sx= -1) (hz : sz=1 ∨ sz= -1) (hn : 1≤n)
    (a b : ℂ) (u : Fin 780→ℂ)
    (hu : ∀ i,sourceRows ((sx:ℂ)*2^n) (3^n) ((sz:ℂ)*13^n) (5^n) a b u i=0) :
    ∀ j : Fin 320,u (support j)=0 := by
  by_cases he : sx=1 ∧ n=1
  · rcases he with ⟨rfl,rfl⟩
    rcases hz with rfl|rfl
    · apply WeightResultants.source_kernel_weight_two_plus a b u
      simpa using hu
    · apply WeightResultants.source_kernel_weight_two_minus a b u
      simpa using hu
  have hn' : if sx=1 then 2≤n else 1≤n := by
    split_ifs with hs
    · have hh : n≠1 := fun hh => he ⟨hs,hh⟩
      omega
    · exact hn
  have hX : (sx:ℂ)*2^n≠0 := mul_ne_zero (sign_ne_zero sx hx) (pow_ne_zero _ (by norm_num))
  have hY : (3:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  have hZ : (sz:ℂ)*13^n≠0 := mul_ne_zero (sign_ne_zero sz hz) (pow_ne_zero _ (by norm_num))
  have hW : (5:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  by_cases h300 : u 300=0
  · apply source_zero_chart ((sx:ℝ)*2^n) ((3:ℝ)^n) ((sz:ℂ)*13^n) (5^n) a b
      (signed_two_bound sx n hx hn) (pow_ne_zero _ (by norm_num)) hZ hW u _ h300
    simpa using hu
  obtain ⟨hr,hv⟩ := WeightResultants.source_kernel_resultants
    ((sx:ℂ)*2^n) (3^n) ((sz:ℂ)*13^n) (5^n) a b hX hY hZ hW u hu h300
  have r_independent (x y z w aa bb tt : ℂ) :
      WeightResultants.r x y z w aa bb tt=WeightResultants.r x y z w aa 0 0 := by
    rfl
  have v_independent (x y z w aa bb tt : ℂ) :
      WeightResultants.v x y z w aa bb tt=WeightResultants.v x y z w aa 0 0 := by
    rfl
  rw [r_independent] at hr
  rw [v_independent] at hv
  have hr' : WeightResultants.r ((sx:ℂ)*2^n) (9^n) ((sz:ℂ)*13^n) (25^n) (a*3^n) 0 0=0 := by
    simpa only [square_three,square_five] using hr
  have hv' : WeightResultants.v ((sx:ℂ)*2^n) (9^n) ((sz:ℂ)*13^n) (25^n) (a*3^n) 0 0=0 := by
    simpa only [square_three,square_five] using hv
  have hd := SmallLevelTwentySixResultantBatchedMMM.resultant_zero
    ((sx:ℂ)*2^n) (9^n) ((sz:ℂ)*13^n) (25^n) (a*3^n) hr' hv'
  exact False.elim ((SmallLevelTwentySixWeightAbelPhysical.mmm_nonzero sx sz n hx hz hn') hd)

#print axioms source_kernel_positive_integer
end SmallLevelTwentySixUnitMMMBatched
end
end

/-! ## SmallLevelTwentySixUnitMMMBatchedIntegerRankV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMMBatched
open SmallLevelTwentySixUnitMMM
open Complex Matrix SmallLevelTwentySixGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport

theorem full_leading_kernel_integer (m n : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (sx sz : ℤ) (hx : sx=1 ∨ sx= -1) (hz : sz=1 ∨ sz= -1) (hn : 1≤n)
    (hη : phase m ε= -(sx:ℂ)*(sz:ℂ)) (h₂ : badParameter f 2= -(sx:ℂ))
    (h₁₃ : badParameter f 13= -(sz:ℂ)) :
    ∀ w : Fin 320→ℂ,fullLeadingMatrix m f ε ((m+n:ℕ):ℂ) *ᵥ w=0 → w=0 := by
  have hx' : (sx:ℂ)=1 ∨ (sx:ℂ)= -1 := by rcases hx with rfl|rfl <;> norm_num
  have hz' : (sz:ℂ)=1 ∨ (sz:ℂ)= -1 := by rcases hz with rfl|rfl <;> norm_num
  change ∀ w,((leadingLinearMap m f ε ((m+n:ℕ):ℂ)).comp
    (extension support)).toMatrix' *ᵥ w=0 → w=0
  intro w hw
  have hg : leadingLinearMap m f ε ((m+n:ℕ):ℂ) (extension support w)=0 := by
    simpa only [LinearMap.toMatrix'_mulVec,LinearMap.comp_apply] using hw
  have hsupp : ∀ j : Fin 320,(extension support w) (support j)=0 := by
    apply source_kernel_positive_integer sx sz n hx hz hn
      (badParameter f 3) (badParameter f 5) (extension support w)
    intro i
    have h:=scaled_sourceRows_actual m f ε sx sz ((m+n:ℕ):ℂ)
      hx' hz' hη h₂ h₁₃ (extension support w) i
    norm_num only [parameter_nat_add, Nat.cast_ofNat] at h
    rw [h]
    exact congrFun hg (selectedSource i)
  funext j
  have hj:=hsupp j
  change extend support w (support j)=0 at hj
  simpa only [extend_at support support_injective,Pi.zero_apply] using hj

#print axioms full_leading_kernel_integer
end SmallLevelTwentySixUnitMMMBatched
end
end
