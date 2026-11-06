module

public import SmallLevelFiniteShiftBlockV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter Set
open scoped Topology

variable {ι κ : Type*} [Fintype ι]

def regularizedStack (d : ℕ) (G : ℂ → ι → ℂ) (k z : ℂ) (b : Fin (d+1)×ι) : ℂ :=
  if b.1=0 then (z-k)*G z b.2 else G (z-(b.1.val:ℂ)) b.2

def regularizedBlock (d : ℕ) (A : ℂ → Matrix κ ι ℂ)
    (C : ℕ → ℂ → Matrix κ ι ℂ) (Q : Fin (d+1) → ℂ → Matrix κ ι ℂ) (z : ℂ) :
    Matrix (Fin (d+1)×κ) (Fin (d+1)×ι) ℂ := fun r b =>
  if r.1=0 then (if b.1=0 then A z r.2 b.2 else 0)
  else (if b.1=r.1 then A (z-r.1.val) r.2 b.2 else 0)-
    (if b.1=0 then Q r.1 z r.2 b.2 else 0)-
    ∑ a∈Finset.range (r.1.val-1),
      if b.1=lowerIndex r.1 a then C a (z-r.1.val) r.2 b.2 else 0

theorem regularizedBlock_apply (d : ℕ) (A : ℂ → Matrix κ ι ℂ)
    (C : ℕ → ℂ → Matrix κ ι ℂ) (Q : Fin (d+1) → ℂ → Matrix κ ι ℂ)
    (z : ℂ) (r : Fin (d+1)×κ) (w : Fin (d+1)×ι → ℂ) :
    (∑ b, regularizedBlock d A C Q z r b*w b)=
      if r.1=0 then ∑ j, A z r.2 j*w (0,j)
      else (∑ j, A (z-r.1.val) r.2 j*w (r.1,j))-
        (∑ j, Q r.1 z r.2 j*w (0,j))-
        ∑ a∈Finset.range (r.1.val-1), ∑ j, C a (z-r.1.val) r.2 j*w (lowerIndex r.1 a,j) := by
  by_cases hn : r.1=0
  · simp only [regularizedBlock,hn,ite_true]
    exact block_delta_apply _ _ _
  · simp only [regularizedBlock,hn,ite_false,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul]
    rw [Finset.sum_comm,block_delta_apply,block_delta_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact block_delta_apply _ _ _

omit [Fintype ι] in
theorem regularizedBlock_analytic (d : ℕ) (A : ℂ → Matrix κ ι ℂ)
    (C : ℕ → ℂ → Matrix κ ι ℂ) (Q : Fin (d+1) → ℂ → Matrix κ ι ℂ)
    (hA : ∀ z i j, AnalyticAt ℂ (fun s => A s i j) z)
    (hC : ∀ n z i j, AnalyticAt ℂ (fun s => C n s i j) z)
    (x : ℂ) (hQ : ∀ n i j, AnalyticAt ℂ (fun z => Q n z i j) x)
    (r : Fin (d+1)×κ) (b : Fin (d+1)×ι) :
    AnalyticAt ℂ (fun z => regularizedBlock d A C Q z r b) x := by
  unfold regularizedBlock
  by_cases hn : r.1=0
  · simp only [hn,ite_true]
    by_cases hb : b.1=0
    · simpa only [hb,ite_true] using hA x r.2 b.2
    · simpa only [hb,ite_false] using (analyticAt_const (v:=(0:ℂ)))
  · simp only [hn,ite_false]
    apply AnalyticAt.sub
    · apply AnalyticAt.sub
      · by_cases hb : b.1=r.1
        · simp only [hb,ite_true]
          exact (hA (x-r.1.val) r.2 b.2).comp (f:=fun z : ℂ => z-(r.1.val:ℂ))
            (analyticAt_id.sub analyticAt_const)
        · simpa only [hb,ite_false] using (analyticAt_const (v:=(0:ℂ)))
      · by_cases hb : b.1=0
        · simpa only [hb,ite_true] using hQ r.1 r.2 b.2
        · simpa only [hb,ite_false] using (analyticAt_const (v:=(0:ℂ)))
    · apply Finset.analyticAt_fun_sum
      intro a _
      by_cases hb : b.1=lowerIndex r.1 a
      · simp only [hb,ite_true]
        exact (hC a (x-r.1.val) r.2 b.2).comp (f:=fun z : ℂ => z-(r.1.val:ℂ))
          (analyticAt_id.sub analyticAt_const)
      · simpa only [hb,ite_false] using (analyticAt_const (v:=(0:ℂ)))

/-- The regularized block agrees with the original lower-point recurrence,
provided the coefficient of the top function has the stated scalar factor. -/
theorem regularizedBlock_recurrence (d : ℕ) (A : ℂ → Matrix κ ι ℂ)
    (C : ℕ → ℂ → Matrix κ ι ℂ) (Q : Fin (d+1) → ℂ → Matrix κ ι ℂ)
    (G : ℂ → ι → ℂ) (k z : ℂ) (n : Fin (d+1)) (i : κ) (hn : n≠0)
    (hfactor : ∀ j, C (n.val-1) (z-n.val) i j=(z-k)*Q n z i j) :
    (∑ b, regularizedBlock d A C Q z (n,i) b*regularizedStack d G k z b)=
      (∑ j, A (z-n.val) i j*G (z-n.val) j)-
        ∑ a∈Finset.range n.val, ∑ j, C a (z-n.val) i j*G (z-((n.val-1-a:ℕ):ℂ)) j := by
  have hnpos : 0<n.val := Fin.pos_iff_ne_zero.mpr hn
  have hnv : n.val=(n.val-1)+1 := by omega
  rw [regularizedBlock_apply]
  simp only [hn,ite_false,regularizedStack,ite_true]
  have htail : (∑ a∈Finset.range (n.val-1), ∑ j, C a (z-n.val) i j*
      (if lowerIndex n a=0 then (z-k)*G z j else G (z-((lowerIndex n a).val:ℂ)) j))=
      ∑ a∈Finset.range (n.val-1), ∑ j, C a (z-n.val) i j*G (z-((n.val-1-a:ℕ):ℂ)) j := by
    apply Finset.sum_congr rfl
    intro a ha
    have hne : lowerIndex n a≠0 := by
      intro h
      have hh := congrArg Fin.val h
      simp only [lowerIndex,Fin.val_zero] at hh
      have := Finset.mem_range.mp ha
      omega
    simp only [hne,ite_false]
    rfl
  rw [htail]
  have hlast : (∑ j, C (n.val-1) (z-n.val) i j*G (z-((n.val-1-(n.val-1):ℕ):ℂ)) j)=
      ∑ j, Q n z i j*((z-k)*G z j) := by
    simp only [Nat.sub_self,Nat.cast_zero,sub_zero,hfactor]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum : (∑ a∈Finset.range n.val, ∑ j, C a (z-n.val) i j*G (z-((n.val-1-a:ℕ):ℂ)) j)=
      (∑ a∈Finset.range (n.val-1), ∑ j, C a (z-n.val) i j*G (z-((n.val-1-a:ℕ):ℂ)) j)+
        (∑ j, C (n.val-1) (z-n.val) i j*G (z-((n.val-1-(n.val-1):ℕ):ℂ)) j) := by
    simpa only [← hnv] using Finset.sum_range_succ
      (fun a => ∑ j, C a (z-n.val) i j*G (z-((n.val-1-a:ℕ):ℂ)) j) (n.val-1)
  rw [hsum,hlast]
  ring

#print axioms regularizedBlock_apply
#print axioms regularizedBlock_recurrence
end SmallLevelFiniteShift
