module

public import AsymptoticSectorReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstructedCount

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticDiagonalTrace AsymptoticObservation FinitenessOriginalInput

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- A single scalar-majorant choice shared by the hyperbolic and
regular counting realizations, independent of weight and sector. -/
noncomputable def parameters (P : Parameters A) : Parameters A :=
  Classical.choose (AsymptoticCertificateOperators.contraction_bound_parameters A P)

theorem parameters_cutoff (P : Parameters A) : (parameters A P).ε=P.ε :=
  (Classical.choose_spec (AsymptoticCertificateOperators.contraction_bound_parameters A P)).1

theorem parameters_bound (P : Parameters A) :
    (parameters A P).ρ^((parameters A P).s+3-1)*
      AsymptoticCertificateOperators.lowConstant A (parameters A P)<1/2 :=
  (Classical.choose_spec (AsymptoticCertificateOperators.contraction_bound_parameters A P)).2.2.2

theorem parameters_hyperbolic_contraction (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (hχ : ∀ q,q∣Q → ‖χ q‖=1) (m : ℕ) :
    ‖AsymptoticCertificateOperators.low A hN (parameters A P) χ ((parameters A P).s+3) m‖<1/2 :=
  (AsymptoticCertificateOperators.low_norm_le A hN (parameters A P) χ hχ (by omega) m).trans_lt
    (parameters_bound A P)

noncomputable def reconstruction (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] Space :=
  AsymptoticCylinderReconstruction.extension A hN (parameters A P) (multiplier e) (h+1)

theorem reconstruction_norm_le (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) :
    ‖reconstruction A hN P h e‖≤
      1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P) :=
  AsymptoticCylinderReconstruction.extension_norm_le A hN (parameters A P) (multiplier e)
    (fun q _ => multiplier_norm e q) (h+1)
    (parameters_hyperbolic_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) (h+1))

theorem terminal_lower_bound (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (g : AsymptoticCylinderTerminal.Space (parameters A P).ε) :
    ‖g‖≤‖(inclusion (parameters A P).epsilon_pos).comp (reconstruction A hN P h e) g‖ :=
  AsymptoticCylinderReconstruction.extension_inclusion_norm_ge A hN (parameters A P) (multiplier e)
    (h+1) (lt_trans (parameters_hyperbolic_contraction A hN P (multiplier e)
      (fun q _ => multiplier_norm e q) (h+1)) (by norm_num)) g

theorem reconstruct_sector (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (w : holomorphicSpace (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi)
      (parameters A P).epsilon_pos) (hw : w∈eulerCylinderSector (parameters A P) h e) :
    ∃ g,(inclusion (parameters A P).epsilon_pos).comp (reconstruction A hN P h e) g=(w:Space) :=
  AsymptoticSectorReconstruction.sector_reconstructed A hN (parameters A P) h e
    (lt_trans (parameters_hyperbolic_contraction A hN P (multiplier e)
      (fun q _ => multiplier_norm e q) (h+1)) (by norm_num)) w hw

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The Euler count-to-trace inequality with the geometric reconstruction,
its terminal lower bound and its action on sectors all supplied by
proofs. Only the observation stack and its known equations remain inputs. -/
theorem count_le_traces (hN : 0<N) (P : Parameters A) (h : ℕ)
    (L : Sector N → Space →L[ℂ] J)
    (hobs : ∀ e w,w∈eulerCylinderSector (parameters A P) h e → L e (w:Space)=0) :
    ((S N (2*(h+1))).ncard:ℝ)≤∑ e : Sector N,
      trace (fourierBasis (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi)
        (parameters A P).epsilon_pos)
        (holomorphicOperator ((inclusion (parameters A P).epsilon_pos).comp
          (reconstruction A hN P h e)) (L e) (terminal_lower_bound A hN P h e)
          (holomorphicSpace (2*h) ((parameters A P).s+4) (by positivity : 0<4*Real.pi)
            (parameters A P).epsilon_pos)) :=
  euler_count_le_observation_traces hN A (parameters A P) h
    (reconstruction A hN P h) L (terminal_lower_bound A hN P h) (reconstruct_sector A hN P h) hobs

#print axioms parameters_bound
#print axioms parameters_hyperbolic_contraction
#print axioms reconstruction_norm_le
#print axioms terminal_lower_bound
#print axioms reconstruct_sector
#print axioms count_le_traces

end AsymptoticReconstructedCount
