module

public import GridSupportGeometryV1

@[expose] public section

namespace GridRationalDenominators

theorem common_grid (N : ℕ) (hN : 0<N) (E : Finset ℚ) :
    ∃G:ℕ,0<G ∧ N∣G ∧ ∀x∈E,∃k:ℤ,(G:ℝ)*(x:ℝ)=k := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨N,hN,dvd_refl N,by simp⟩
  | @insert x E hx ih =>
    obtain ⟨G,hG,hNG,hE⟩ := ih
    refine ⟨G*x.den,Nat.mul_pos hG x.den_pos,hNG.trans (dvd_mul_right G _),?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with hxy|hy
    · subst y
      refine ⟨x.num*G,?_⟩
      have hd : (x.den:ℝ)≠0 := by exact_mod_cast x.den_ne_zero
      rw [Rat.cast_def]
      push_cast
      field_simp
    · obtain ⟨k,hk⟩ := hE y hy
      refine ⟨k*x.den,?_⟩
      push_cast
      nlinarith [hk]

#print axioms common_grid

end GridRationalDenominators
