module

public import GridParametersV1

@[expose] public section

namespace GridSupportGeometry

open GridCarrier CompleteRowCosets SpanningCyclicCoordinates

theorem integer_near_grid {G v J : ℕ} (hG : 0<G) (hv : 0<v) (j : Fin (G*v))
    (k : ℤ) (hclose : |(j.val:ℤ)-k*v|≤(J:ℤ)) :
    j∈Set.range (gridIndex hG hv J) := by
  let a := residue hG k
  let t : Offsets J := ⟨(j.val:ℤ)-k*v,Finset.mem_Icc.mpr (abs_le.mp hclose)⟩
  refine ⟨(a,t),?_⟩
  change residue (Nat.mul_pos hG hv) ((a.val:ℤ)*v+t.val)=j
  rw [←residue_nat (Nat.mul_pos hG hv) j]
  apply (residue_eq_iff (Nat.mul_pos hG hv) _ _).mpr
  have ha := (residue_mod hG k).mul_right' (c:=(v:ℤ))
  have hat := ha.add_right t.val
  have ht : k*(v:ℤ)+t.val=j.val := by dsimp [t]; ring
  simpa only [Nat.cast_mul,ht] using hat

theorem half_floor_bound {v R : ℕ} (hR : 0<R) (hv : 16*R≤v) :
    (v:ℝ)/(16*R)≤((v/(8*R):ℕ):ℝ) := by
  have hd : 0<8*R := by omega
  have hJ : 1≤v/(8*R) := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have hrem := Nat.mod_lt v hd
  have he := Nat.div_add_mod v (8*R)
  have hb : v≤(v/(8*R))*(16*R) := by nlinarith
  apply (div_le_iff₀ (by positivity : (0:ℝ)<16*R)).mpr
  exact_mod_cast hb

theorem normalized_near_grid {G v R : ℕ} (hG : 0<G) (hv : 0<v) (hR : 0<R)
    (hvR : 16*R≤v) (j : Fin (G*v)) (x : ℝ) (k : ℤ)
    (hx : (G:ℝ)*x=k)
    (hnear : |(j.val:ℝ)/((G:ℝ)*v)-x|<(1:ℝ)/(16*R*G)) :
    j∈Set.range (gridIndex hG hv (v/(8*R))) := by
  have hG' : (0:ℝ)<G := by exact_mod_cast hG
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have hR' : (0:ℝ)<R := by exact_mod_cast hR
  have hprod : (0:ℝ)<(G:ℝ)*v := mul_pos hG' hv'
  have he : (j.val:ℝ)-(k:ℝ)*v=((j.val:ℝ)/((G:ℝ)*v)-x)*((G:ℝ)*v) := by
    rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hprod)]
    nlinarith [hx]
  have hab : |(j.val:ℝ)-(k:ℝ)*v|<(v:ℝ)/(16*R) := by
    rw [he,abs_mul,abs_of_pos hprod]
    have hh := mul_lt_mul_of_pos_right hnear hprod
    have hi : ((1:ℝ)/(16*R*G))*((G:ℝ)*v)=(v:ℝ)/(16*R) := by field_simp
    rwa [hi] at hh
  have hbound := hab.le.trans (half_floor_bound hR hvR)
  apply integer_near_grid hG hv j k
  have hb := abs_le.mp hbound
  apply abs_le.mpr
  constructor
  · exact_mod_cast hb.1
  · apply (Int.cast_le (R:=ℝ)).mp
    push_cast
    exact hb.2

#print axioms normalized_near_grid

end GridSupportGeometry
