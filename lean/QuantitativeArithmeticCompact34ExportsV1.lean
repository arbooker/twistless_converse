module
public meta import Lean.Elab.Command
public import QuantitativeArithmeticRationalRecurrenceInterfaceV1

/-! Compatibility names for the original level34 consumers. Every generated
proof is just an application of the common indexed theorem; Lean elaborates
and kernel-checks these declarations normally. No computation is trusted. -/

public meta section
open Lean Elab Command

elab "export_rhs_interfaces" : command => do
  for i in [:411] do
    let declarations := [
      s!"theorem rhsPivot{i}_add (X Y Z W a b : ℂ) (r t : Fin 546 → ℂ) :
        rhsPivot{i} X Y Z W a b (r+t) = rhsPivot{i} X Y Z W a b r + rhsPivot{i} X Y Z W a b t :=
        rhs_add ⟨{i}, by decide⟩ X Y Z W a b r t",
      s!"theorem rhsPivot{i}_smul (X Y Z W a b c : ℂ) (r : Fin 546 → ℂ) :
        rhsPivot{i} X Y Z W a b (c • r) = c * rhsPivot{i} X Y Z W a b r :=
        rhs_smul ⟨{i}, by decide⟩ X Y Z W a b c r",
      s!"def rhsPivot{i}Map (X Y Z W a b : ℂ) : (Fin 546 → ℂ) →ₗ[ℂ] ℂ :=
        rhsMap ⟨{i}, by decide⟩ X Y Z W a b",
      s!"theorem rhsPivot{i}_analytic (X Y Z W a b : ℂ → ℂ) (r : ℂ → Fin 546 → ℂ) (x : ℂ)
        (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
        (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
        (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
        (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
        (hr : ∀ j, AnalyticAt ℂ (fun t => r t j) x) :
        AnalyticAt ℂ (fun t => rhsPivot{i} (X t) (Y t) (Z t) (W t) (a t) (b t) (r t)) x :=
        rhs_analytic ⟨{i}, by decide⟩ X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr"
    ]
    for source in declarations do
      match Parser.runParserCategory (← getEnv) `command source with
      | .error message => throwError "RHS interface {i}: {message}"
      | .ok declaration => elabCommand declaration
