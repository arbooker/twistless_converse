module

public import QuantitativeMaassBandWideCountV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Module QuantitativeNinaMaass

namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- The full actual cusp band has at most C*t*L dimensions. This version
does not impose reflection parity, so it also controls intermediate bands. -/
theorem fullBand_wide_finrank_bound (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (S : CuspEnergySpectrum N hN) (t L : ℝ),
      6≤t → 1≤L → L≤t/4 →
      (finrank ℂ (S.band (t-L) (t+L)):ℝ)≤C*t*L := by
  obtain ⟨C,hC,hcount⟩ := wide_cuspidal_family_linear N hN
  refine ⟨C,hC,?_⟩
  intro S t L ht hL hLt
  classical
  have ho := S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let I := principalWindowIndices S.energy (t-L) (t+L)
  let : Fintype I := (principalWindowIndices_finite N hN _ ho
    (fun i => (S.basis i).property) S.energy S.energy_nonneg S.graph _ _).fintype
  have hh := hcount t L ht hL hLt
    (fun i : I => (S.basis i.val:AutomorphicSpace N))
    (fun i : I => Real.sqrt (S.energy i.val-1/4))
    (ho.comp Subtype.val Subtype.val_injective) (fun i => (S.basis i.val).property)
    (fun i => i.property.2) (fun i => ?_)
  · have hr := cuspPrincipalWindowSpace_finrank N hN S.basis S.energy S.energy_nonneg
      S.graph (t-L) (t+L)
    change finrank ℂ (S.band (t-L) (t+L))=Nat.card I at hr
    rw [hr,Nat.card_eq_fintype_card]
    exact hh
  · have hs := Real.sq_sqrt (sub_nonneg.mpr i.property.1)
    have heq : 1/4+(Real.sqrt (S.energy i.val-1/4))^2=S.energy i.val := by linarith
    rw [heq]
    exact S.graph i.val

#print axioms fullBand_wide_finrank_bound

end QuantitativeMaass
