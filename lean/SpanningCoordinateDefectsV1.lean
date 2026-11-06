module

public import SpanningCoherentLiftsV1

@[expose] public section

namespace SpanningKernelDefects

open SpanningActualKernel SpanningLinearKernels SpanningCoherentLifts
open SpanningFiniteDimensions
variable {K : Type} [Field K]

/-- Positions where at least one actual augmented-kernel vector has a
nonzero P-step difference. This is one common support set for the space. -/
noncomputable def coordinateDefects (N : ℕ) (L : Set ℕ) (Q P : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range Q).filter (fun j => ∃v:augmentedSubmodule (K:=K) N L Q,
    v.val j≠v.val (j+P:ℕ))

theorem word_different_iff {N Q p : ℕ} {L : Set ℕ}
    (e : TraceLift (K:=K) N L Q p) (j P : ℕ) :
    (∃v:augmentedSubmodule (K:=K) N L (p*Q),v.val j≠v.val (j+P:ℕ)) ↔
      e.wordNat j≠e.wordNat (j+P) := by
  constructor
  · rintro ⟨v,hv⟩ he
    obtain ⟨u,rfl⟩ := e.equiv.surjective v
    exact hv (congrArg (fun f:Module.Dual K (augmentedSubmodule (K:=K) N L Q) => f u) he)
  · intro he
    by_contra! hn
    apply he
    ext u
    exact hn (e.equiv u)

noncomputable def letterDefects {A : Type*} (Q P : ℕ) (w : ℕ → A) : Finset ℕ := by
  classical
  exact (Finset.range Q).filter (fun j => w j≠w (j+P))

theorem coordinateDefects_eq {N Q p : ℕ} {L : Set ℕ}
    (e : TraceLift (K:=K) N L Q p) (P : ℕ) :
    coordinateDefects (K:=K) N L (p*Q) P=
      letterDefects (p*Q) P e.wordNat := by
  classical
  ext j
  simp only [coordinateDefects,letterDefects,Finset.mem_filter,Finset.mem_range,word_different_iff e]

#print axioms coordinateDefects_eq

end SpanningKernelDefects
