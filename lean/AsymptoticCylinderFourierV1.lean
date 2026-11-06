module

public import AsymptoticCylinderWeightV1
public import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open MeasureTheory Set Filter AsymptoticFourierNorm InnerProductSpace
open scoped InnerProduct

/-- The horizontal characters of distinct positive frequencies are
orthogonal with the probability normalization used on the cylinder. -/
theorem circle_inner_zero {i j : ℕ} (hij : i≠j) :
    (∫ x : AddCircle (1:ℝ),fourier (j+1:ℕ) x*star (fourier (i+1:ℕ) x)
      ∂AddCircle.haarAddCircle)=0 := by
  have hne : ((i+1:ℕ):ℤ)≠((j+1:ℕ):ℤ) := by exact_mod_cast (show i+1≠j+1 by omega)
  have hh := (orthonormal_fourier (T:=1)).inner_eq_zero hne
  simpa only [fourierLp,ContinuousMap.inner_toLp,starRingEnd_apply] using hh

theorem modeLp_inner_zero (m t : ℕ) {i j : ℕ} (hij : i≠j)
    {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    ⟪modeLp m t i hs hε,modeLp m t j hs hε⟫_ℂ=0 := by
  rw [L2.inner_def]
  let f : AddCircle (1:ℝ) → ℂ := fun x => fourier (j+1:ℕ) x*star (fourier (i+1:ℕ) x)
  let g : ℝ → ℂ := fun y =>
    (Real.sqrt (density m t (scale*(j+1:ℕ)) ε y):ℂ)*
      (Real.sqrt (density m t (scale*(i+1:ℕ)) ε y):ℂ)
  calc
    (∫ z,⟪modeLp m t i hs hε z,modeLp m t j hs hε z⟫_ℂ ∂measure) =
        ∫ z,f z.1*g z.2 ∂measure := by
      apply integral_congr_ae
      filter_upwards [modeLp_coeFn m t i hs hε,modeLp_coeFn m t j hs hε] with z hi hj
      simp only [hi,hj,RCLike.inner_apply,mode,f,g,Complex.star_def,map_mul,Complex.conj_ofReal]
      ring
    _ = (∫ x,f x ∂AddCircle.haarAddCircle)*(∫ y in Ioi 0,g y) := integral_prod_mul f g
    _ = 0 := by rw [circle_inner_zero hij,zero_mul]

/-- The normalized, positive-frequency modes form an orthonormal family
in the actual cylinder L² space. -/
theorem unitMode_orthonormal (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    Orthonormal ℂ (fun n => unitMode m t n hs hε) := by
  constructor
  · intro n
    have h := unitMode_norm_sq m t n hs hε
    nlinarith [norm_nonneg (unitMode m t n hs hε)]
  · intro i j hij
    simp only [unitMode,inner_smul_left,inner_smul_right,modeLp_inner_zero m t hij hs hε,mul_zero]

/-- The closed span of the positive holomorphic Fourier modes. Identifying
all analytic cusp functions with this span is a separate analytic step. -/
noncomputable def holomorphicSpace (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    Submodule ℂ Space :=
  (Submodule.span ℂ (Set.range (fun n => unitMode m t n hs hε))).topologicalClosure

instance holomorphicSpace_complete (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    CompleteSpace (holomorphicSpace m t hs hε) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

noncomputable def modeInSpace (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    holomorphicSpace m t hs hε :=
  ⟨unitMode m t n hs hε,Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n,rfl⟩)⟩

theorem modeInSpace_orthonormal (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    Orthonormal ℂ (fun n => modeInSpace m t n hs hε) :=
  unitMode_orthonormal m t hs hε

theorem modeInSpace_orthogonal_eq_bot (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    (Submodule.span ℂ (Set.range (fun n => modeInSpace m t n hs hε)))ᗮ=⊥ := by
  apply le_antisymm _ bot_le
  intro w hw
  have ha : (w:Space)∈(Submodule.span ℂ (Set.range (fun n => unitMode m t n hs hε)))ᗮ := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨n,rfl⟩ := hv
        exact hw (modeInSpace m t n hs hε) (Submodule.subset_span ⟨n,rfl⟩)
    | zero => exact inner_zero_left _
    | add v₁ v₂ _ _ hv₁ hv₂ => rw [inner_add_left,hv₁,hv₂,add_zero]
    | smul a v _ hv => rw [inner_smul_left,hv,mul_zero]
  have ha' : (w:Space)∈(holomorphicSpace m t hs hε)ᗮ := by
    simpa only [holomorphicSpace,Submodule.orthogonal_closure] using ha
  have hz : (w:Space)=0 := inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal w.property ha')
  change w=0
  exact Subtype.ext hz

/-- The positive Fourier family is a Hilbert basis of its concrete closed
span. No sector dimension formula is used. -/
noncomputable def fourierBasis (m t : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    HilbertBasis ℕ ℂ (holomorphicSpace m t hs hε) :=
  HilbertBasis.mkOfOrthogonalEqBot (modeInSpace_orthonormal m t hs hε)
    (modeInSpace_orthogonal_eq_bot m t hs hε)

@[simp] theorem fourierBasis_apply (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    fourierBasis m t hs hε n=modeInSpace m t n hs hε := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

#print axioms modeInSpace_orthogonal_eq_bot
#print axioms unitMode_orthonormal

end AsymptoticCylinder
