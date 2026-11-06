module

public import AsymptoticIntegralSubgroupV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRationalLocalIntegral

/-- A rational number integral at every finite prime is an integer. -/
theorem integer_of_all_padic (r : ℚ)
    (hr : ∀ p : ℕ,p.Prime → padicNorm p r≤1) : ∃ a : ℤ,r=(a:ℚ) := by
  have hd : r.den=1 := by
    by_contra h
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd h
    let : Fact p.Prime := ⟨hp⟩
    have hpn : ¬(p:ℤ)∣r.num := by
      intro hpn
      have hpn' : p∣r.num.natAbs := Int.natCast_dvd.mp hpn
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpn' hpd r.reduced
    have hn := (padicNorm.int_eq_one_iff r.num).mpr hpn
    have hb := hr p hp
    nth_rw 1 [← r.num_div_den] at hb
    rw [padicNorm.div,hn] at hb
    have hpos : 0<padicNorm p (r.den:ℚ) :=
      lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero (by exact_mod_cast r.den_nz)).symm
    have he : padicNorm p (r.den:ℚ)=1 :=
      le_antisymm (by simpa only [Int.cast_natCast] using padicNorm.of_int (p:=p) (r.den:ℤ))
        ((div_le_one₀ hpos).mp hb)
    exact (padicNorm.nat_eq_one_iff r.den).mp he hpd
  exact ⟨r.num,(Rat.coe_int_num_of_den_eq_one hd).symm⟩

/-- Local integrality at every prime exactly characterizes integer
rational numbers; no denominator restriction is left as a hypothesis. -/
theorem all_padic_iff_integer (r : ℚ) :
    (∀ p : ℕ,p.Prime → padicNorm p r≤1) ↔ ∃ a : ℤ,r=(a:ℚ) := by
  constructor
  · exact integer_of_all_padic r
  · rintro ⟨a,rfl⟩ p hp
    let : Fact p.Prime := ⟨hp⟩
    exact padicNorm.of_int a

#print axioms integer_of_all_padic
#print axioms all_padic_iff_integer

end AsymptoticRationalLocalIntegral
