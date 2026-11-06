module

public import QuantitativeArithmeticSmallLevelCircCuspResolventV1
public import QuantitativeArithmeticSmallLevelCircHeckeInvariantV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelCirc.CuspSpectral

open UpperHalfPlane AsymptoticClassicalCusp

/-- The actual intersection of the cusp space with full Mcirc. -/
def cuspCorner (N k : ℕ) (hN : 0 < N) : Submodule ℂ (CuspForm (level N) (k : ℤ)) :=
  (space N hN k).comap CuspForm.toModularFormₗ

def modularBoundaryDifference (N p m : ℕ) [NeZero N] (hp : 0 < p) :
    ModularForm (level N) ((2 * m : ℕ) : ℤ) →ₗ[ℂ]
      ModularForm (level N) ((2 * m : ℕ) : ℤ) :=
  (1 + (p : ℂ)^(2 * m - 1)) • LinearMap.id -
    ModularHecke.dilationTrace N p hp ((2 * m : ℕ) : ℤ)

theorem boundaryDifference_toModular (N p m : ℕ) [NeZero N] (hp : 0 < p)
    (f : CuspForm (level N) ((2 * m : ℕ) : ℤ)) :
    modularBoundaryDifference N p m hp (CuspForm.toModularFormₗ f) =
      CuspForm.toModularFormₗ (boundaryDifference N p m hp f) := by
  simp [modularBoundaryDifference, boundaryDifference, dilationTrace_toModular]

theorem modularBoundaryDifference_mem (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (F : ModularForm (level N) ((2 * m : ℕ) : ℤ)) (hF : F ∈ space N hN (2 * m)) :
    modularBoundaryDifference N p m hp.pos F ∈ space N hN (2 * m) := by
  have ht := primeHecke_mem_space N p (2 * m) hN hp hpN F hF
  simp only [ModularHecke.primeHecke, hpN, ite_false] at ht
  exact (space N hN (2 * m)).sub_mem ((space N hN (2 * m)).smul_mem _ hF) ht

def cornerBoundaryDifference (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    cuspCorner N (2 * m) hN →ₗ[ℂ] cuspCorner N (2 * m) hN :=
  ((boundaryDifference N p m hp.pos).comp (cuspCorner N (2 * m) hN).subtype).codRestrict
    (cuspCorner N (2 * m) hN) (fun f => by
      change CuspForm.toModularFormₗ (boundaryDifference N p m hp.pos f.val) ∈ space N hN (2 * m)
      rw [← boundaryDifference_toModular]
      exact modularBoundaryDifference_mem N p m hN hp hpN _ f.property)

theorem cornerBoundaryDifference_injective (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) (hm : 0 < m) :
    Function.Injective (cornerBoundaryDifference N p m hN hp hpN) := by
  intro f g he
  apply Subtype.ext
  exact boundaryDifference_injective N p m hN hp hpN hm (congrArg Subtype.val he)

/-- The cusp resolvent also preserves the full trace-new intersection.
This follows from its actual Hecke invariance and finite dimension. -/
def cornerBoundaryResolvent (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) (hm : 0 < m) :
    cuspCorner N (2 * m) hN ≃ₗ[ℂ] cuspCorner N (2 * m) hN :=
  (LinearEquiv.ofInjectiveEndo (cornerBoundaryDifference N p m hN hp hpN)
    (cornerBoundaryDifference_injective N p m hN hp hpN hm)).symm

/-- A form whose boundary defect is cuspidal splits inside Mcirc into an
actual cusp form and an actual eigenform at the boundary eigenvalue. The
cuspidal-defect condition is the separate finite cusp-action calculation. -/
theorem split_of_cuspidal_defect (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N) (hm : 0 < m)
    (F : space N hN (2 * m))
    (H : CuspForm (level N) ((2 * m : ℕ) : ℤ))
    (hH : modularBoundaryDifference N p m hp.pos F.val = CuspForm.toModularFormₗ H) :
    ∃ G : cuspCorner N (2 * m) hN, ∃ E : space N hN (2 * m),
      F.val = CuspForm.toModularFormₗ G.val + E.val ∧
      ModularHecke.dilationTrace N p hp.pos ((2 * m : ℕ) : ℤ) E.val =
        (1 + (p : ℂ)^(2 * m - 1)) • E.val := by
  have hcorner : H ∈ cuspCorner N (2 * m) hN := by
    change CuspForm.toModularFormₗ H ∈ space N hN (2 * m)
    rw [← hH]
    exact modularBoundaryDifference_mem N p m hN hp hpN F.val F.property
  let Hc : cuspCorner N (2 * m) hN := ⟨H, hcorner⟩
  let G := cornerBoundaryResolvent N p m hN hp hpN hm Hc
  have hG : boundaryDifference N p m hp.pos G.val = H :=
    congrArg Subtype.val
      ((LinearEquiv.ofInjectiveEndo (cornerBoundaryDifference N p m hN hp hpN)
        (cornerBoundaryDifference_injective N p m hN hp hpN hm)).apply_symm_apply Hc)
  let E : space N hN (2 * m) :=
    ⟨F.val - CuspForm.toModularFormₗ G.val, (space N hN (2 * m)).sub_mem F.property G.property⟩
  refine ⟨G, E, ?_, ?_⟩
  · change F.val = CuspForm.toModularFormₗ G.val + (F.val - CuspForm.toModularFormₗ G.val)
    abel
  · have he : modularBoundaryDifference N p m hp.pos E.val = 0 := by
      change modularBoundaryDifference N p m hp.pos
        (F.val - CuspForm.toModularFormₗ G.val) = 0
      rw [map_sub, boundaryDifference_toModular, hG, hH, sub_self]
    exact (sub_eq_zero.mp he).symm

#print axioms boundaryDifference_toModular
#print axioms modularBoundaryDifference_mem
#print axioms cornerBoundaryResolvent
#print axioms split_of_cuspidal_defect

end QuantitativeArithmeticSmallLevelCirc.CuspSpectral
