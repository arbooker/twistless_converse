module
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSimplePole
open Complex Filter Set
open scoped Topology

/-- Fill the removable singularity after multiplication by its local parameter. -/
theorem entire_regularization (G : ℂ → ℂ) (k : ℂ)
    (hG : MeromorphicAt G k)
    (hk : (-1:WithTop ℤ)≤meromorphicOrderAt G k)
    (haway : ∀ z : ℂ,z≠k → AnalyticAt ℂ G z) :
    ∃ H : ℂ → ℂ,Differentiable ℂ H ∧ ∀ z : ℂ,z≠k → H z=(z-k)*G z := by
  let R : ℂ → ℂ := fun z => (z-k)*G z
  have hR : MeromorphicAt R k := (analyticAt_id.sub analyticAt_const).meromorphicAt.mul hG
  have horder : 0≤meromorphicOrderAt R k := by
    change 0≤meromorphicOrderAt ((fun z : ℂ => z-k)*G) k
    have hloc : MeromorphicAt (fun z : ℂ => z-k) k := (analyticAt_id.sub analyticAt_const).meromorphicAt
    rw [meromorphicOrderAt_mul hloc hG,
      meromorphicOrderAt_id_sub_const]
    have hh := add_le_add_left hk (1:WithTop ℤ)
    norm_num at hh ⊢
    simpa only [add_comm] using hh
  let H := toMeromorphicNFAt R k
  have he (z : ℂ) (hz : z≠k) : H z=R z :=
    (hR.eqOn_compl_singleton_toMeromorphicNFAt (by simpa using hz)).symm
  refine ⟨H,?_,he⟩
  intro z
  by_cases hz : z=k
  · subst z
    exact (hR.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp horder).differentiableAt
  · have hloc : H=ᶠ[𝓝 z] R := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact he w hw
    exact (((analyticAt_id.sub analyticAt_const).mul (haway z hz)).congr hloc.symm).differentiableAt

/-- A meromorphic function with one possible simple pole is an entire
function plus its principal part; no growth claim is built into this lemma. -/
theorem entire_part (G : ℂ → ℂ) (k : ℂ)
    (hG : MeromorphicAt G k)
    (hk : (-1:WithTop ℤ)≤meromorphicOrderAt G k)
    (haway : ∀ z : ℂ,z≠k → AnalyticAt ℂ G z) :
    ∃ (F : ℂ → ℂ) (r : ℂ),Differentiable ℂ F ∧
      ∀ z : ℂ,z≠k → G z=F z+r/(z-k) := by
  obtain ⟨H,hH,he⟩ := entire_regularization G k hG hk haway
  refine ⟨dslope H k,H k,?_,?_⟩
  · intro z
    by_cases hz : z=k
    · subst z
      obtain ⟨p,hp⟩ := hH.analyticAt k
      exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt
    · exact (differentiableAt_dslope_of_ne hz).mpr (hH z)
  · intro z hz
    rw [dslope_of_ne H hz,slope,smul_eq_mul,he z hz]
    simp only [vsub_eq_sub]
    field_simp [sub_ne_zero.mpr hz]
    ring
#print axioms entire_regularization
#print axioms entire_part
end QuantitativeArithmeticSimplePole
