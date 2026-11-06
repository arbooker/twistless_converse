module

public import AsymptoticRamifiedSectorsV1
public import AsymptoticCylinderTraceV1
public import FinitenessFiniteUnionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open FinitenessOriginalInput AsymptoticDiagonalTrace AsymptoticObservation
open scoped BigOperators

/-- The full Fricke-and-ramified-sign sectors in the cylinder, imposing
every positive twist equation and all ramified rows. The auxiliary weight
depends only on the spanning certificate, not on k or the solution. The
exponent s+4 is one above the reconstructed base exponent s+3. -/
noncomputable def eulerCylinderSector {N Q : ℕ} {hQ : 0<Q}
    {A : Certificate N Q hQ} (P : Parameters A) (h : ℕ) (e : Sector N) :
    Submodule ℂ (holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos) :=
  LinearMap.range (AsymptoticRamifiedSectors.cylinderMap N h (h+1+P.s) (P.s+4)
    e P.epsilon_pos (by omega))

theorem eulerCylinderSector_finiteDimensional {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (h : ℕ) (e : Sector N) :
    FiniteDimensional ℂ (eulerCylinderSector P h e) := by
  let _ : FiniteDimensional ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e) :=
    AsymptoticRamifiedSectors.sector_finiteDimensional hN A P h (h+1+P.s) e
  unfold eulerCylinderSector
  infer_instance

noncomputable def eulerCylinder {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (h : ℕ) (f : S N (2*(h+1))) :
    holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos :=
  fourierMap (2*h) (P.s+4) (h+1+P.s) (by positivity) P.epsilon_pos (by omega)
    (eulerCoefficients hN A P (h+1) f)

theorem eulerCylinder_independent {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (h : ℕ) :
    LinearIndependent ℂ (eulerCylinder hN A P h) := by
  have hc : LinearIndependent ℂ (eulerCoefficients hN A P (h+1)) := by
    apply LinearIndependent.of_comp (coefficientSpace (h+1+P.s)).subtype
    exact FinitenessOriginalDiskIndependence.normalized_independent N (2*(h+1))
  exact hc.map' (fourierMap (2*h) (P.s+4) (h+1+P.s) (by positivity) P.epsilon_pos (by omega))
    (LinearMap.ker_eq_bot.mpr
      (fourierMap_injective (2*h) (P.s+4) (h+1+P.s) (by positivity) P.epsilon_pos (by omega)))

theorem eulerCylinder_cover {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (h : ℕ) (f : S N (2*(h+1))) :
    ∃ e : Sector N, eulerCylinder hN A P h f∈eulerCylinderSector P h e := by
  obtain ⟨e,he⟩ := AsymptoticRamifiedSectors.euler_cover hN A P h f
  exact ⟨e,⟨⟨eulerCoefficients hN A P (h+1) f,he⟩,rfl⟩⟩

/-- The actual Euler count is bounded by the sum of the dimensions of
the concrete cylinder sectors. Neither a cover nor independence is assumed. -/
theorem euler_count_le_cylinder_sectors {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (h : ℕ) :
    (S N (2*(h+1))).Finite ∧ (S N (2*(h+1))).ncard≤
      ∑ e : Sector N, Module.finrank ℂ (eulerCylinderSector P h e) := by
  let _ : ∀ e : Sector N, FiniteDimensional ℂ (eulerCylinderSector P h e) :=
    eulerCylinderSector_finiteDimensional hN A P h
  obtain ⟨hf,hb⟩ := FinitenessFiniteUnion.bound_sum (eulerCylinderSector P h)
    (eulerCylinder hN A P h) (eulerCylinder_independent hN A P h) (eulerCylinder_cover hN A P h)
  exact ⟨Set.finite_coe_iff.mp hf,by simpa only [Nat.card_coe_set_eq] using hb⟩

variable {G J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The count-to-trace step for actual Euler solutions in the concrete
cylinder. Geometric reconstruction and observation equations remain the
explicit analytic obligations; all coefficient, dimension and cover
inputs are supplied by checked theorems above. -/
theorem euler_count_le_observation_traces {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (h : ℕ)
    (R₀ : Sector N → G →L[ℂ] Space) (L : Sector N → Space →L[ℂ] J)
    (hR : ∀ e g,‖g‖≤‖(inclusion P.epsilon_pos).comp (R₀ e) g‖)
    (hreconstruct : ∀ e w, w∈eulerCylinderSector P h e →
      ∃ g,(inclusion P.epsilon_pos).comp (R₀ e) g=(w:Space))
    (hobs : ∀ e w, w∈eulerCylinderSector P h e → L e (w:Space)=0) :
    ((S N (2*(h+1))).ncard:ℝ)≤∑ e : Sector N,
      trace (fourierBasis (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
        (holomorphicOperator ((inclusion P.epsilon_pos).comp (R₀ e)) (L e) (hR e)
          (holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)) := by
  let _ : ∀ e : Sector N, FiniteDimensional ℂ (eulerCylinderSector P h e) :=
    eulerCylinderSector_finiteDimensional hN A P h
  have hb : ((S N (2*(h+1))).ncard:ℝ)≤
      ∑ e : Sector N, (Module.finrank ℂ (eulerCylinderSector P h e):ℝ) := by
    exact_mod_cast (euler_count_le_cylinder_sectors hN A P h).2
  apply hb.trans
  apply Finset.sum_le_sum
  intro e _
  exact solution_finrank_le_trace (R₀ e) (L e) (2*h) (P.s+4)
    (show 0<4*Real.pi by positivity)
    P.epsilon_pos (hR e) (eulerCylinderSector P h e) (hreconstruct e) (hobs e)

#print axioms eulerCylinder_independent
#print axioms eulerCylinder_cover
#print axioms euler_count_le_cylinder_sectors
#print axioms euler_count_le_observation_traces

end AsymptoticCylinder
