module

public import AsymptoticClassicalCuspL2V1
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane MeasureTheory AsymptoticClassicalCusp
open scoped ComplexConjugate InnerProduct

/-- The weighted L² inner product is exactly the classical integrand. -/
theorem weighted_inner (k : ℤ) (f g : ℍ → ℂ) (z : ℍ) :
    inner ℂ (weighted k f z) (weighted k g z) = petersson k f g z := by
  have hs : (Real.sqrt (z.im ^ k) : ℂ) * (Real.sqrt (z.im ^ k) : ℂ) = (z.im : ℂ) ^ k := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_zpow]
    congr 1
    simpa only [pow_two] using Real.sq_sqrt (zpow_pos z.im_pos k).le
  change ((Real.sqrt (z.im ^ k) : ℂ) * g z) *
      conj ((Real.sqrt (z.im ^ k) : ℂ) * f z) = conj (f z) * g z * (z.im : ℂ) ^ k
  rw [map_mul, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (z.im ^ k) : ℂ) * (Real.sqrt (z.im ^ k) : ℂ)) *
      (conj (f z) * g z) := by ring
    _ = _ := by rw [hs]; ring

variable (N : ℕ) [NeZero N] (k : ℤ)

instance cuspNormedAddCommGroup : NormedAddCommGroup (CuspForm (level N) k) :=
  NormedAddCommGroup.induced _ _ (embedding N k) (embedding_injective N k)

instance cuspInnerProductSpace : InnerProductSpace ℂ (CuspForm (level N) k) :=
  InnerProductSpace.induced (embedding N k)

instance cusp_complete : CompleteSpace (CuspForm (level N) k) :=
  FiniteDimensional.complete ℂ _

theorem newSpace_closed (hN : 0 < N) : IsClosed (newSpace N hN k : Set (CuspForm (level N) k)) :=
  Submodule.closed_of_finiteDimensional _

instance newSpace_complete (hN : 0 < N) : CompleteSpace (newSpace N hN k) :=
  FiniteDimensional.complete ℂ _

/-- The Petersson product as an actual convergent quotient integral. -/
theorem inner_eq_integral (f g : CuspForm (level N) k) :
    inner ℂ f g = ∫ z, petersson k f g z ∂quotientMeasure N := by
  change inner ℂ (embedding N k f) (embedding N k g) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [embedding_coeFn N k f, embedding_coeFn N k g] with z hf hg
  rw [hf, hg, weighted_inner]

/-- Integrability here is proved by the weighted L² realization. -/
theorem integrable_petersson (f g : CuspForm (level N) k) :
    Integrable (petersson k f g) (quotientMeasure N) := by
  apply (L2.integrable_inner (embedding N k f) (embedding N k g)).congr
  filter_upwards [embedding_coeFn N k f, embedding_coeFn N k g] with z hf hg
  rw [hf, hg, weighted_inner]

#print axioms cusp_complete
#print axioms newSpace_closed
#print axioms newSpace_complete
#print axioms weighted_inner
#print axioms cuspNormedAddCommGroup
#print axioms cuspInnerProductSpace
#print axioms inner_eq_integral
#print axioms integrable_petersson

end AsymptoticClassicalPetersson
