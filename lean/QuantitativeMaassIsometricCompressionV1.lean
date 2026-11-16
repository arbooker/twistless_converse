module

public import QuantitativeMaassEigenfamilyFiniteV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {G H ι κ : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def filteredCompression (U : G →ₗᵢ[ℂ] H) (K : H →L[ℂ] H) (F : G →L[ℂ] G) : G →L[ℂ] G :=
  U.toContinuousLinearMap.adjoint.comp (K.comp (U.toContinuousLinearMap.comp F))

theorem filteredCompression_eigen (U : G →ₗᵢ[ℂ] H) (K : H →L[ℂ] H) (F : G →L[ℂ] G)
    (g : G) (c : ℂ) (hfix : F g=g) (heigen : K (U g)=c • U g) :
    filteredCompression U K F g=c • g := by
  have hu : U.toContinuousLinearMap.adjoint (U g)=g := by
    simpa only [ContinuousLinearMap.comp_apply,one_apply_eq_self,
      LinearIsometry.coe_toContinuousLinearMap] using!
      congrArg (fun B : G →L[ℂ] G => B g) U.adjoint_comp_self
  simp only [filteredCompression,ContinuousLinearMap.comp_apply,hfix,
    LinearIsometry.coe_toContinuousLinearMap,heigen,map_smul,hu]

/-- Algebraic counting with the actual reconstruction isometry. The spectral
operator and its Hilbert--Schmidt compression remain explicit analytic inputs. -/
theorem filteredCompression_count (U : G →ₗᵢ[ℂ] H) (K : H →L[ℂ] H) (F : G →L[ℂ] G)
    (basis : HilbertBasis ι ℂ G) (v : κ → G) (hv : LinearIndependent ℂ v) (h : κ → ℝ)
    (hfix : ∀ i,F (v i)=v i) (heigen : ∀ i,K (U (v i))=(h i:ℂ) • U (v i))
    (hlower : ∀ i,1≤h i)
    (hB : Summable (fun i => ‖filteredCompression U K F (basis i)‖^2)) :
    Finite κ ∧ (Nat.card κ : ℝ)≤hilbertSchmidtEnergy basis (filteredCompression U K F) :=
  independent_eigenfamily_finite basis _ v hv h
    (fun i => filteredCompression_eigen U K F (v i) (h i) (hfix i) (heigen i)) hlower hB

#print axioms filteredCompression_eigen
#print axioms filteredCompression_count

end QuantitativeMaass
