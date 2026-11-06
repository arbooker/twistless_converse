module

/- Overlapping local periods force an eventual global period. -/
public import CobhamColoringV1

@[expose] public section

namespace CobhamLocalPeriods

variable {A : Type*}

def PeriodOn (f : ℕ → A) (p L R : ℕ) : Prop :=
  ∀ j, L≤j → j+p≤R → f j=f (j+p)

/-- Transport a period across another periodic interval. The overlap
must contain a segment of length p+q; no Fine--Wilf theorem is assumed. -/
theorem glue {f : ℕ → A} {p q L R M S : ℕ}
    (hp : PeriodOn f p L R) (hq : PeriodOn f q M S)
    (hq0 : 0<q) (hLM : L≤M) (_hRS : R≤S) (hov : M+p+q≤R) :
    PeriodOn f p L S := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hjs
    by_cases hjr : j+p≤R
    · exact hp j hj hjr
    · have hlow : M≤j-q := by omega
      have hstep : j-q<j := by omega
      have he1 := hq (j-q) hlow (by omega)
      have he2 := hq (j-q+p) (by omega) (by omega)
      have he3 := ih (j-q) hstep (by omega) (by omega)
      have h1 : j-q+q=j := by omega
      have h2 : j-q+p+q=j+p := by omega
      rw [h1] at he1
      rw [h2] at he2
      exact he1.symm.trans (he3.trans he2)

theorem eventual_period_of_windows {f : ℕ → A} {B T M : ℕ}
    (hB : 0<B) (hT : 4*T≤B)
    (hw : ∀ x, M≤x → ∃ p, 0<p ∧ p≤T ∧
      PeriodOn f p (x*B+T) ((x+2)*B-T)) :
    ∃ p, 0<p ∧ BKKCommonFactor.EventuallyPeriodic p f := by
  obtain ⟨p,hp0,hpT,hp⟩ := hw M le_rfl
  have hall (t : ℕ) : PeriodOn f p (M*B+T) ((M+t+2)*B-T) := by
    induction t with
    | zero => simpa using hp
    | succ t ih =>
      obtain ⟨q,hq0,hqT,hq⟩ := hw (M+t+1) (by omega)
      apply glue ih hq hq0
      · nlinarith
      · have h1 : (M+t+2)*B≤(M+t+1+2)*B := by nlinarith
        omega
      · have h1 : T≤(M+t+2)*B := by nlinarith
        have h2 : (M+t+2)*B=(M+t+1)*B+B := by ring
        omega
  refine ⟨p,hp0,M*B+T,?_⟩
  intro j hj
  apply hall (j+p+T) j hj
  have h1 : j+p+T≤(M+(j+p+T)+2)*B := by nlinarith
  omega

#print axioms glue
#print axioms eventual_period_of_windows

end CobhamLocalPeriods
