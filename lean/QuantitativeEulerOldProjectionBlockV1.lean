module

public import AsymptoticTranslatedCosetFiberV1
public import AsymptoticRegularTraceV1
public import QuantitativeNewGapRepeatedV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionBlock

open AsymptoticNestedQuotients ContinuousLinearMap
open scoped lp

section Restrict
variable {ι κ : Type*} (j : κ → ι) (hj : Function.Injective j)

/-- Restriction along an actual injection of counting coordinates. -/
def restrictLinear : ℓ²(ι,ℂ) →ₗ[ℂ] ℓ²(κ,ℂ) where
  toFun v := ⟨fun k => v (j k), memℓp_gen
    (((lp.memℓp v).summable (by norm_num)).comp_injective hj)⟩
  map_add' _ _ := by apply lp.ext; rfl
  map_smul' _ _ := by apply lp.ext; rfl

theorem restrictLinear_apply (v : ℓ²(ι,ℂ)) (k : κ) : restrictLinear j hj v k = v (j k) := rfl

include hj in
theorem injective_norm_le (v : ℓ²(ι,ℂ)) (w : ℓ²(κ,ℂ))
    (hwv : ∀ k, w k = v (j k)) : ‖w‖ ≤ ‖v‖ := by
  have hv : HasSum (fun i => ‖v i‖^2) (‖v‖^2) := by
    simpa using lp.hasSum_norm (p := 2) (by norm_num) v
  have hw : HasSum (fun k => ‖w k‖^2) (‖w‖^2) := by
    simpa using lp.hasSum_norm (p := 2) (by norm_num) w
  have hle : (∑' k, ‖w k‖^2) ≤ ∑' i, ‖v i‖^2 :=
    Summable.tsum_le_tsum_of_inj j hj (fun _ _ => sq_nonneg _)
      (fun k => by rw [hwv k]) hw.summable hv.summable
  rw [hw.tsum_eq, hv.tsum_eq] at hle
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hle

theorem restrict_norm_le (v : ℓ²(ι,ℂ)) : ‖restrictLinear j hj v‖ ≤ ‖v‖ :=
  injective_norm_le j hj v (restrictLinear j hj v) (fun _ => rfl)

def restrict : ℓ²(ι,ℂ) →L[ℂ] ℓ²(κ,ℂ) :=
  (restrictLinear j hj).mkContinuous 1 (by intro v; simpa using restrict_norm_le j hj v)

theorem restrict_apply (v : ℓ²(ι,ℂ)) (k : κ) : restrict j hj v k = v (j k) := rfl
end Restrict

section Partition
variable {ι κ : Type*} (p : ι → κ)

def fiber (y : κ) : ℓ²(ι,ℂ) →L[ℂ] ℓ²({i // p i = y},ℂ) :=
  restrict Subtype.val Subtype.val_injective

/-- Countable energy decomposes over the exact fibers, even for an
uncountable partition; no finiteness assumption is used. -/
theorem fiber_energy (v : ℓ²(ι,ℂ)) :
    HasSum (fun y => ‖fiber p y v‖^2) (‖v‖^2) := by
  have hv : HasSum (fun i => ‖v i‖^2) (‖v‖^2) := by
    simpa using lp.hasSum_norm (p := 2) (by norm_num) v
  have hy (y : κ) : HasSum (fun i : {i // p i = y} => ‖v i.val‖^2)
      (‖fiber p y v‖^2) := by
    simpa [fiber, restrict, restrictLinear] using
      lp.hasSum_norm (p := 2) (by norm_num) (fiber p y v)
  exact ((Equiv.sigmaFiberEquiv p).hasSum_iff.mpr hv).sigma hy
end Partition

section Cosets
variable {G : Type*} [Group G] {H S : Subgroup G} (hHS : H ≤ S)

/-- The actual translated finite root block of a global regular-coset
vector. The map is contractive, independently of the translate. -/
def cosetBlock (g : G) : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes (H.subgroupOf S),ℂ) :=
  restrict (translateClass (H := H) (J := S) g) (translateClass_injective g)

theorem cosetBlock_apply (g : G) (v : ℓ²(Classes H,ℂ))
    (q : Classes (H.subgroupOf S)) :
    cosetBlock (H := H) (S := S) g v q = v (translateClass g q) := rfl

theorem cosetBlock_energy (y : Classes S) (v : ℓ²(Classes H,ℂ)) :
    ‖cosetBlock (H := H) (S := S) y.out v‖^2 = ‖fiber (forget hHS) y v‖^2 := by
  have hy : classOf S y.out = y := y.out_eq
  have hb : HasSum (fun q : Classes (H.subgroupOf S) => ‖v (translateClass y.out q)‖^2)
      (‖cosetBlock (H := H) (S := S) y.out v‖^2) := by
    simpa [cosetBlock, restrict, restrictLinear] using
      lp.hasSum_norm (p := 2) (by norm_num) (cosetBlock (H := H) (S := S) y.out v)
  have hf : HasSum (fun q : {q // forget hHS q = classOf S y.out} => ‖v q.val‖^2)
      (‖fiber (forget hHS) (classOf S y.out) v‖^2) := by
    simpa [fiber, restrict, restrictLinear] using
      lp.hasSum_norm (p := 2) (by norm_num) (fiber (forget hHS) (classOf S y.out) v)
  have he := (translatedFibreEquiv hHS y.out).hasSum_iff.mpr hf
  have hh := hb.unique he
  rw [hy] at hh
  exact hh

include hHS in
/-- Exact Parseval decomposition into translated root coset blocks.
This is the norm identity required to sum a uniform finite root gap. -/
theorem cosetBlocks_energy (v : ℓ²(Classes H,ℂ)) :
    HasSum (fun y : Classes S => ‖cosetBlock (H := H) (S := S) y.out v‖^2) (‖v‖^2) := by
  simpa only [cosetBlock_energy hHS] using fiber_energy (forget hHS) v
end Cosets

#print axioms restrict_norm_le
#print axioms fiber_energy
#print axioms cosetBlocks_energy
end QuantitativeEulerOldProjectionBlock
