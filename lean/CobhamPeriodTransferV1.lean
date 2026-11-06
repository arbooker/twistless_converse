module

/- Three finite-color equalities produce a nonzero local period. -/
public import CobhamLocalPeriodsV1

@[expose] public section

namespace CobhamPeriodTransfer

open CobhamLocalPeriods
variable {Alphabet : Type*} {f : ℕ → Alphabet}

private theorem window_coordinates {x B T p j : ℕ}
    (hj : x*B+T≤j) (hjr : j+p≤(x+2)*B-T) :
    x*B+(j-x*B)=j ∧ T≤j-x*B ∧ (j-x*B)+p+T≤2*B := by
  have h1 : (x+2)*B=x*B+2*B := by ring
  omega

theorem period_up {A B d u v x T : ℕ}
    (hAB : A=B+d) (hd : 0<d) (huv : u<v) (hmargin : (v+2)*d<T)
    (ha : ∀ r, r<2*A → f (u*A+r)=f (v*A+r))
    (hbu : ∀ r, r<2*B → f (x*B+r)=f (u*B+r))
    (hbv : ∀ r, r<2*B → f (x*B+r)=f (v*B+r)) :
    PeriodOn f ((v-u)*d) (x*B+T) ((x+2)*B-T) := by
  intro j hj hjr
  let z := j-x*B
  obtain ⟨hz,hzlo,hzhi⟩ := window_coordinates hj hjr
  change x*B+z=j at hz
  change T≤z at hzlo
  change z+(v-u)*d+T≤2*B at hzhi
  have hT : 0<T := by omega
  have hud : u*d≤z := by nlinarith
  have hr : z-u*d<2*A := by omega
  have he1 : u*B+z=u*A+(z-u*d) := by
    have := Nat.sub_add_cancel hud
    nlinarith
  have he2 : v*A+(z-u*d)=v*B+(z+(v-u)*d) := by
    have := Nat.sub_add_cancel hud
    have := Nat.sub_add_cancel (Nat.le_of_lt huv)
    nlinarith
  calc
    f j = f (x*B+z) := congrArg f hz.symm
    _ = f (u*B+z) := hbu z (by omega)
    _ = f (u*A+(z-u*d)) := congrArg f he1
    _ = f (v*A+(z-u*d)) := ha _ hr
    _ = f (v*B+(z+(v-u)*d)) := congrArg f he2
    _ = f (x*B+(z+(v-u)*d)) := (hbv _ (by omega)).symm
    _ = f (j+(v-u)*d) := by congr 1; omega

theorem period_down {A B d u v x T : ℕ}
    (hAB : B=A+d) (_hd : 0<d) (huv : u<v) (hmargin : (v+2)*d<T)
    (ha : ∀ r, r<2*A → f (u*A+r)=f (v*A+r))
    (hbu : ∀ r, r<2*B → f (x*B+r)=f (u*B+r))
    (hbv : ∀ r, r<2*B → f (x*B+r)=f (v*B+r)) :
    PeriodOn f ((v-u)*d) (x*B+T) ((x+2)*B-T) := by
  intro j hj hjr
  let z := j-x*B
  obtain ⟨hz,hzlo,hzhi⟩ := window_coordinates hj hjr
  change x*B+z=j at hz
  change T≤z at hzlo
  change z+(v-u)*d+T≤2*B at hzhi
  have hT : 0<T := by omega
  have hr : z+v*d<2*A := by nlinarith
  have he1 : v*B+z=v*A+(z+v*d) := by nlinarith
  have he2 : u*A+(z+v*d)=u*B+(z+(v-u)*d) := by
    have := Nat.sub_add_cancel (Nat.le_of_lt huv)
    nlinarith
  calc
    f j = f (x*B+z) := congrArg f hz.symm
    _ = f (v*B+z) := hbv z (by omega)
    _ = f (v*A+(z+v*d)) := congrArg f he1
    _ = f (u*A+(z+v*d)) := (ha _ hr).symm
    _ = f (u*B+(z+(v-u)*d)) := congrArg f he2
    _ = f (x*B+(z+(v-u)*d)) := (hbu _ (by omega)).symm
    _ = f (j+(v-u)*d) := by congr 1; omega

#print axioms period_up
#print axioms period_down

end CobhamPeriodTransfer
