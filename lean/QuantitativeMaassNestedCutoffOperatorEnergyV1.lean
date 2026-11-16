module

public import QuantitativeMaassNestedCutoffBandsV1
public import QuantitativeMaassRectangularEnergyV1
public import QuantitativeMaassParityWindowDimensionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeNinaMaass

namespace QuantitativeMaass.Weighted

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

/-- Nested-band leakage survives arbitrary bounded input maps into the
inner band. This is the form needed for intermediate factors of a word. -/
theorem nestedBandRemainder_precompose_energy {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype ι]
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (b : Cutoff N)
    (v : OrthonormalBasis ι ℂ E) (t B L : ℝ) (hL : 0<L) (ht : B+L+2≤t)
    (T : E →L[ℂ] S.band (t-B) (t+B)) :
    (∑ i,‖nestedBandRemainder S b t B L ((T (v i)).val:AutomorphicSpace N)‖^2)≤
      ‖T‖^2*(16*b.gradientBound^2*(Module.finrank ℂ (S.band (t-B) (t+B)):ℝ)/L^2) := by
  classical
  let U := S.band (t-B) (t+B)
  let I := principalWindowIndices S.energy (t-B) (t+B)
  have ho := S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  let : Fintype I := (principalWindowIndices_finite N hN _ ho
    (fun i => (S.basis i).property) S.energy S.energy_nonneg S.graph (t-B) (t+B)).fintype
  let : FiniteDimensional ℂ U := S.band_finiteDimensional _ _
  let c : OrthonormalBasis I ℂ U :=
    cuspPrincipalWindowBasis N hN S.basis S.energy (t-B) (t+B)
  let J : U →L[ℂ] AutomorphicSpace N :=
    (localCuspidalSpace N hN).subtypeL.comp U.subtypeL
  let A := (nestedBandRemainder S b t B L).comp J
  have hright := rectangular_energy_right v c A T
  have henergy : (∑ i,‖A (c i)‖^2)≤
      16*b.gradientBound^2*(Fintype.card I:ℝ)/L^2 := by
    let f : I → AutomorphicSpace N := fun i => (S.basis i.val:AutomorphicSpace N)
    let r : I → ℝ := fun i => Real.sqrt (S.energy i.val-1/4)
    have hgraph (i : I) : FriedrichsGraph N (f i) (((1/4+(r i)^2:ℝ):ℂ) • f i) := by
      have heq : 1/4+(r i)^2=S.energy i.val := by
        have hh := Real.sq_sqrt (sub_nonneg.mpr i.property.1)
        dsimp only [r]
        linarith
      rw [heq]
      exact S.graph i.val
    have hh := nestedBandRemainder_energy S b f r
      (ho.comp Subtype.val Subtype.val_injective) hgraph t B L hL ht
      (fun i => i.property.2)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x : AutomorphicSpace N => ‖nestedBandRemainder S b t B L x‖^2)
      (cuspPrincipalWindowBasis_coe N hN S.basis S.energy (t-B) (t+B) i)
  have hdim : Module.finrank ℂ U=Fintype.card I := Module.finrank_eq_card_basis c.toBasis
  have hh := hright.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg ‖T‖))
  rw [←hdim] at hh
  exact hh

#print axioms nestedBandRemainder_precompose_energy

end QuantitativeMaass.Weighted
