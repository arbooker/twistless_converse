module

public import QuantitativeMaassSpectralCutoffScalarV1
public import QuantitativeMaassShiftedWaveStrongLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventCutoffOperator (A : H →L[ℂ] H) (ε : ℝ) : H →L[ℂ] H :=
  cfc (p:=IsSelfAdjoint) (resolventCutoff ε) A

def boundedResolventOperator (A : H →L[ℂ] H) (ε : ℝ) : H →L[ℂ] H :=
  cfc (p:=IsSelfAdjoint) (boundedResolventGenerator ε) A

theorem resolventCutoffOperator_norm_le (A : H →L[ℂ] H) (ε : ℝ) (hε : 0<ε) :
    ‖resolventCutoffOperator A ε‖≤1 :=
  norm_cfc_le zero_le_one (fun s _ => resolventCutoff_norm_le ε s hε)

theorem boundedResolventOperator_norm_le (A : H →L[ℂ] H) (ε : ℝ) (hε : 0<ε) :
    ‖boundedResolventOperator A ε‖≤ε⁻¹+1 :=
  norm_cfc_le (by positivity) (fun s _ => boundedResolventGenerator_norm_le ε s hε)

theorem resolventCutoffOperator_commute (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ε : ℝ) :
    Commute (resolventCutoffOperator A ε) A := by
  have h := cfc_commute_cfc (p:=IsSelfAdjoint) (resolventCutoff ε) (id : ℝ → ℝ) A
  rw [cfc_id ℝ A hA] at h
  exact h

/-- The bounded regularized generator equals the inverse resolvent minus
identity after the explicit cutoff. This is an exact CFC identity. -/
theorem resolventCutoffOperator_generator_identity (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (ε : ℝ) (hε : 0<ε) :
    A*(resolventCutoffOperator A ε+boundedResolventOperator A ε*resolventCutoffOperator A ε)=
      resolventCutoffOperator A ε := by
  have hp := resolventCutoff_continuous ε hε
  have hb := boundedResolventGenerator_continuous ε hε
  have he : cfc (fun s : ℝ => s*(resolventCutoff ε s+
      boundedResolventGenerator ε s*resolventCutoff ε s)) A=cfc (resolventCutoff ε) A := by
    apply cfc_congr
    intro s _
    exact resolventCutoff_generator_identity ε s hε
  rw [cfc_mul (fun s : ℝ => s) (fun s => resolventCutoff ε s+
      boundedResolventGenerator ε s*resolventCutoff ε s) A continuous_id.continuousOn
      (hp.add (hb.mul hp)).continuousOn,
    cfc_id' ℝ A hA,cfc_add (a:=A) (resolventCutoff ε)
      (fun s => boundedResolventGenerator ε s*resolventCutoff ε s)
      hp.continuousOn (hb.mul hp).continuousOn,
    cfc_mul (boundedResolventGenerator ε) (resolventCutoff ε) A hb.continuousOn hp.continuousOn] at he
  exact he

theorem resolventCutoffOperator_residual_norm (A : H →L[ℂ] H)
    (hp : A.IsPositive) (hn : ‖A‖≤1) (ε : ℝ) (hε : 0<ε) :
    ‖(resolventCutoffOperator A ε-1)*A‖≤ε := by
  have hc := resolventCutoff_continuous ε hε
  have he : (resolventCutoffOperator A ε-1)*A=
      cfc (fun s : ℝ => s*(resolventCutoff ε s-1)) A := by
    rw [cfc_mul (fun s : ℝ => s) (fun s => resolventCutoff ε s-1) A
      continuous_id.continuousOn (hc.sub continuous_const).continuousOn,
      cfc_id' ℝ A hp.isSelfAdjoint,cfc_sub (resolventCutoff ε) (fun _ : ℝ => 1) A
        hc.continuousOn continuous_const.continuousOn,cfc_const (1:ℝ) A hp.isSelfAdjoint,map_one]
    have hcomm := (resolventCutoffOperator_commute A hp.isSelfAdjoint ε).eq
    change (resolventCutoffOperator A ε-1)*A=A*(resolventCutoffOperator A ε-1)
    rw [sub_mul,mul_sub,one_mul,mul_one,hcomm]
  rw [he]
  apply norm_cfc_le hε.le
  intro s hs
  exact resolventCutoff_residual_bound ε s hε (positiveContraction_spectrum_bound A hp hn hs).1

/-- Every cutoff output belongs to the full actual Friedrichs domain, with
the Laplacian represented there by a bounded operator. -/
theorem friedrichsCutoff_graph (N : ℕ) (ε : ℝ) (hε : 0<ε) (v : AutomorphicSpace N) :
    FriedrichsGraph N (resolventCutoffOperator (friedrichsResolvent N) ε v)
      (boundedResolventOperator (friedrichsResolvent N) ε
        (resolventCutoffOperator (friedrichsResolvent N) ε v)) := by
  have he := congrArg (fun B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => B v)
    (resolventCutoffOperator_generator_identity (friedrichsResolvent N)
      (friedrichsResolvent_isSelfAdjoint N) ε hε)
  exact he

#print axioms resolventCutoffOperator_generator_identity
#print axioms resolventCutoffOperator_residual_norm
#print axioms friedrichsCutoff_graph

end QuantitativeMaass.Wave
