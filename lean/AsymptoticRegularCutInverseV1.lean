module

public import AsymptoticRegularCutNormalFamilyV1
public import AsymptoticRegularObservationInverseV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The cutoff inverse uses the same common series scale as the uncut
family. The terminal identity ensures coercivity for Y≤epsilon. -/
noncomputable def cutInverse (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticCoerciveNeumann.inverse (wholeNormalBound A hN P r s hs) (cutNormal A hN P r s hs e Y z)

theorem cutInverse_mul (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    (cutInverse A hN P r s hs e Y z).comp (cutNormal A hN P r s hs e Y z)=1 :=
  AsymptoticCoerciveNeumann.inverse_mul _ _ (cutNormal_norm_le A hN P r s hs e Y z)
    (cutNormal_coercive A hN P r s hs e Y hY z)

theorem cutNormal_mul_inverse (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    (cutNormal A hN P r s hs e Y z).comp (cutInverse A hN P r s hs e Y z)=1 :=
  AsymptoticCoerciveNeumann.mul_inverse _ _ (cutNormal_norm_le A hN P r s hs e Y z)
    (cutNormal_coercive A hN P r s hs e Y hY z)

theorem cutInverse_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    ‖cutInverse A hN P r s hs e Y z‖≤1 :=
  AsymptoticCoerciveNeumann.inverse_norm_le _ _ (cutNormal_norm_le A hN P r s hs e Y z)
    (cutNormal_coercive A hN P r s hs e Y hY z)

theorem cutInverse_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) :
    Covariant (cutInverse A hN P r s hs e Y) :=
  inverse_covariant _ _ (cutNormal_covariant A hN P r s hs e Y)
    (cutNormal_norm_le A hN P r s hs e Y) (cutNormal_coercive A hN P r s hs e Y hY)

theorem cutInverse_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (cutInverse A hN P r s hs e Y z) a b) :=
  inverse_matrix_measurable _ _ (cutNormal_matrix_measurable A hN P r s hs e Y)
    (cutNormal_norm_le A hN P r s hs e Y) (cutNormal_coercive A hN P r s hs e Y hY) a b

/-- A uniform inverse perturbation estimate for the actual low-height
cutoff, independent of the orbit root and sector. -/
theorem cutInverse_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY0 : 0≤Y) (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    ‖wholeInverse A hN P r s hs e z-cutInverse A hN P r s hs e Y z‖≤cutErrorBound A hN P r s hs Y :=
  (AsymptoticObservation.inverse_sub_norm_le _ _ _ _ (wholeInverse_mul A hN P r s hs e z)
    (cutNormal_mul_inverse A hN P r s hs e Y hY z) (wholeInverse_norm_le A hN P r s hs e z)
    (cutInverse_norm_le A hN P r s hs e Y hY z)).trans (cutNormal_error A hN P r s hs e Y hY0 z)

#print axioms cutInverse_mul
#print axioms cutNormal_mul_inverse
#print axioms cutInverse_norm_le
#print axioms cutInverse_covariant
#print axioms cutInverse_matrix_measurable
#print axioms cutInverse_error

end AsymptoticRegularObservation
