module

public import QuantitativeMaassParityWindowDimensionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- The range of the restricted parity operator is exactly the genuine
reflection eigenspace inside the finite principal spectral band. -/
theorem cuspWindowParity_range_iff {κ : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) (hσ : σ^2=1) (x : cuspPrincipalWindowSpace N hN basis e a b) :
    x∈LinearMap.range (cuspWindowParity N hN basis e henergy hgraph a b σ) ↔
      reflectionIsometry N (x.val:AutomorphicSpace N)=(σ:ℂ) • (x.val:AutomorphicSpace N) := by
  constructor
  · rintro ⟨y,rfl⟩
    exact parityProjection_eigen N σ hσ (y.val:AutomorphicSpace N)
  · intro hx
    refine ⟨x,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change parityProjection N σ (x.val:AutomorphicSpace N)=(x.val:AutomorphicSpace N)
    rw [parityProjection_apply,hx,smul_smul]
    have hs : (σ:ℂ)*(σ:ℂ)=1 := by exact_mod_cast (by nlinarith [hσ] : σ*σ=1)
    rw [hs,one_smul]
    module

/-- The two actual parity dimensions split the entire finite principal band. -/
theorem cuspWindowParity_dimensions_add {κ : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (a b σ : ℝ) (hσ : σ^2=1) :
    Module.finrank ℂ (LinearMap.range (cuspWindowParity N hN basis e henergy hgraph a b σ))+
      Module.finrank ℂ (LinearMap.range (cuspWindowParity N hN basis e henergy hgraph a b (-σ)))=
      Nat.card (principalWindowIndices e a b) := by
  let W := cuspPrincipalWindowSpace N hN basis e a b
  let : FiniteDimensional ℂ W := cuspPrincipalWindowSpace_finiteDimensional N hN basis e henergy hgraph a b
  let P := cuspWindowParity N hN basis e henergy hgraph a b σ
  let Q := cuspWindowParity N hN basis e henergy hgraph a b (-σ)
  have hp : IsIdempotentElem P := cuspWindowParity_idempotent N hN basis e henergy hgraph a b σ hσ
  have hq : IsIdempotentElem Q := cuspWindowParity_idempotent N hN basis e henergy hgraph a b (-σ) (by simpa only [neg_sq] using hσ)
  have hsum : P+Q=1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact parityProjection_add_neg N σ (x.val:AutomorphicSpace N)
  have hn := finite_complementary_projection_finrank P Q hp hq hsum
  exact hn.trans (cuspPrincipalWindowSpace_finrank N hN basis e henergy hgraph a b)

/-- Sharp lower asymptotic for the genuine finite parity spectral dimension
at every positive level, under exactly the original width condition. -/
theorem cuspParityWindow_dimension_eventual_lower {κ : Type*}
    (N : ℕ) [NeZero N] (hN : 0<N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (basis j:AutomorphicSpace N) ((e j:ℂ) • (basis j:AutomorphicSpace N)))
    (σ : ℝ) (hσ : σ^2=1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ t in atTop,(quotientMeasure N).real univ/(4*Real.pi)-η<
      (Module.finrank ℂ (LinearMap.range (cuspWindowParity N hN basis e henergy hgraph t (t+ε t) σ)):ℝ)/(t*ε t) := by
  obtain ⟨p,hp,_hgt,hpN,hNp,hpres,a,b,hab⟩ := exists_lv_prime_data N hN
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d,hd,hbound⟩ := exists_parity_LV_sharp_window_lower N p hN hpN hNp hpres a b hab basis e henergy hgraph η hη
  filter_upwards [hbound σ hσ ε hε hproduct,hε,eventually_gt_atTop (0:ℝ)] with t ht het htp
  exact ht.trans_le (div_le_div_of_nonneg_right
    (sharp_parity_LV_weight_le_dimension N p hN hpN hNp hpres a b hab d basis e henergy hgraph t (t+ε t) σ hσ)
    (mul_pos htp het.1).le)

#print axioms cuspWindowParity_range_iff
#print axioms cuspWindowParity_dimensions_add
#print axioms cuspParityWindow_dimension_eventual_lower

end QuantitativeMaass
