module

public import QuantitativeMaassCuspidalRemainderOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeNinaMaass

namespace QuantitativeMaass.Weighted

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- Cutoff remainder outside a band enlarged by an explicit buffer L+2
around an input band of radius B. -/
def nestedBandRemainder {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    (b : Cutoff N) (t B L : ℝ) : AutomorphicSpace N →L[ℂ] localCuspidalSpace N hN :=
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  (1-V.starProjection).comp (cuspidalCutoff N hN b)

/-- The actual squared leakage estimate between nested bands. Its constant
does not grow with either band radius; only the input dimension appears. -/
theorem nestedBandRemainder_energy {κ : Type*} [Fintype κ]
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (b : Cutoff N)
    (g : κ → AutomorphicSpace N) (r : κ → ℝ) (hg : Orthonormal ℂ g)
    (hggraph : ∀ j,FriedrichsGraph N (g j) (((1/4+(r j)^2:ℝ):ℂ) • g j))
    (t B L : ℝ) (hL : 0<L) (ht : B+L+2≤t)
    (hin : ∀ j,r j∈Icc (t-B) (t+B)) :
    (∑ j,‖nestedBandRemainder S b t B L (g j)‖^2)≤
      16*b.gradientBound^2*(Fintype.card κ:ℝ)/L^2 := by
  classical
  let I := principalWindowIndices S.energy (t-(B+L+2)) (t+(B+L+2))
  let V := S.band (t-(B+L+2)) (t+(B+L+2))
  let : FiniteDimensional ℂ V := S.band_finiteDimensional _ _
  have htail (j : κ) : ‖nestedBandRemainder S b t B L (g j)‖^2=
      ∑' i : {i // i∉I},‖inner ℂ (S.basis i.val).val.val
        (multiplier N b (g j).val)‖^2 := by
    change ‖cuspidalCutoff N hN b (g j)-V.starProjection (cuspidalCutoff N hN b (g j))‖^2=_
    rw [hilbertBasis_projection_tail S.basis I]
    exact tsum_congr (fun i => by rw [cuspidalCutoff_inner])
  simp_rw [htail]
  have ho := S.basis.orthonormal.comp_linearIsometry (localCuspidalSpace N hN).subtypeₗᵢ
  apply smooth_cutoff_separated_family_energy N b (fun i : {i // i∉I} => S.energy i.val)
    (fun j => 1/4+(r j)^2) (fun i : {i // i∉I} => (S.basis i.val:AutomorphicSpace N))
    g (ho.comp Subtype.val Subtype.val_injective) hg (fun i => S.energy_nonneg i.val)
    (fun _ => by positivity) (fun i => S.graph i.val) hggraph L hL
  intro i j
  apply principal_separation_energy (S.energy i.val) (1/4+(r j)^2) L
    (S.energy_nonneg i.val) (by positivity)
  have hr : 0≤r j := by have hh := (hin j).1; linarith
  rw [add_sub_cancel_left,Real.sqrt_sq hr]
  have hout : B+L+2≤|Real.sqrt (S.energy i.val-1/4)-t| := by
    have hh := outside_principal_window_distance S.energy t ((B+L+2)-3)
      (by linarith) i.val (by simpa only [sub_add_cancel] using i.property)
    simpa only [sub_add_cancel] using hh
  have hinput : |r j-t|≤B := abs_le.mpr ⟨by have hh := (hin j).1; linarith,
    by have hh := (hin j).2; linarith⟩
  have htri := abs_add_le (Real.sqrt (S.energy i.val-1/4)-r j) (r j-t)
  have hid : Real.sqrt (S.energy i.val-1/4)-r j+(r j-t)=
      Real.sqrt (S.energy i.val-1/4)-t := by ring
  rw [hid] at htri
  linarith

#print axioms nestedBandRemainder_energy

end QuantitativeMaass.Weighted
