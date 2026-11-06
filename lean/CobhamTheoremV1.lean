module

/- Cobham's theorem, via finite scale colorings and the local-period
argument of Krebs. No Cobham/Fagnot/S-unit hypothesis is used here. -/
public import CobhamClosePowersV1
public import CobhamPeriodTransferV1
public import CobhamStatementV1

@[expose] public section

namespace CobhamTheorem

open AutomaticSequences BKKCommonFactor IndependentBases
open CobhamColoring CobhamLocalPeriods CobhamPeriodTransfer

theorem periodic_of_colorings {A : Type} {f : ℕ → A} {k l : ℕ}
    (hk : 2≤k) (hl : 2≤l) (hi : Independent k l)
    (ca : ScalingColoring k f) (cb : ScalingColoring l f) :
    ∃ p, 0<p ∧ EventuallyPeriodic p f := by
  classical
  let : Finite ca.State := ca.finite
  let : Finite cb.State := cb.finite
  obtain ⟨X,hX,hpairs⟩ := bounded_repeated_pairs ca.color cb.color
  obtain ⟨M,hM⟩ := eventually_infinite_fibers cb.color
  obtain ⟨m,n,hm,hn,hclose1,hclose2⟩ :=
    CobhamClosePowers.close_powers hk hl (8*(X+2))
  let U := k^m
  let V := l^n
  have hne : U≠V := by
    intro he
    have := (hi m n he).1
    omega
  let d := (U-V)+(V-U)
  have hd : 0<d := by dsimp [d]; omega
  have hsign : U=V+d ∨ V=U+d := by dsimp [d]; omega
  have hclose : 8*((X+2)*d)<V := by
    change 8*(X+2)*U<(8*(X+2)+1)*V at hclose1
    change 8*(X+2)*V<(8*(X+2)+1)*U at hclose2
    rcases hsign with h | h
    · nlinarith only [hclose1,h]
    · nlinarith only [hclose2,h,hd]
  let T := (X+2)*d+1
  have hT : 4*T≤V := by
    have hp : 0<(X+2)*d := Nat.mul_pos (by omega) hd
    dsimp [T]
    omega
  apply eventual_period_of_windows (show 0<V from pow_pos (by omega) _) hT
  intro x hx
  obtain ⟨u,v,huv,_huX,hvX,hcu,hcv,hca⟩ := hpairs (cb.color x) (hM x hx)
  have hmargin : (v+2)*d<T := by dsimp [T]; nlinarith
  have ha : ∀ r, r<2*U → f (u*U+r)=f (v*U+r) := by
    intro r hr
    simpa only [Nat.mul_comm] using ca.same u v hca m r hr
  have hbu : ∀ r, r<2*V → f (x*V+r)=f (u*V+r) := by
    intro r hr
    simpa only [Nat.mul_comm] using cb.same x u hcu.symm n r hr
  have hbv : ∀ r, r<2*V → f (x*V+r)=f (v*V+r) := by
    intro r hr
    simpa only [Nat.mul_comm] using cb.same x v hcv.symm n r hr
  refine ⟨(v-u)*d,Nat.mul_pos (by omega) hd,?_,?_⟩
  · have : v-u≤X := by omega
    dsimp [T]
    nlinarith
  · rcases hsign with h | h
    · exact period_up h hd huv hmargin ha hbu hbv
    · exact period_down h hd huv hmargin ha hbu hbv

theorem cobham {A : Type} [Fintype A] {k l : ℕ}
    (hk : 2≤k) (hl : 2≤l) (hi : Independent k l) {f : ℕ → A}
    (hkf : Automatic k f) (hlf : Automatic l f) :
    ∃ p, 0<p ∧ EventuallyPeriodic p f :=
  periodic_of_colorings hk hl hi (scalingColoring (by omega) hkf)
    (scalingColoring (by omega) hlf)

theorem cobhamInput : ClassicalCobham.Statement := by
  intro A _ k l hk hl hi f hkf hlf
  exact cobham hk hl hi hkf hlf

#print axioms cobham
#print axioms cobhamInput

end CobhamTheorem
