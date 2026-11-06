module

public import SmallLevelElevenEllipticV1
public import SmallLevelOddWordsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelEleven
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def letter : Fin 9 → SL(2,ℤ)
  | 0 => T
  | 1 => T⁻¹
  | 2 => lower 11
  | 3 => (lower 11)⁻¹
  | 4 => -1
  | 5 => oddMatrix 11 6 (by decide)
  | 6 => (oddMatrix 11 6 (by decide))⁻¹
  | 7 => A
  | 8 => A⁻¹

def word (w : List (Fin 9)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 11∈K) (hZ : -1∈K)
    (h2 : oddMatrix 11 6 (by decide)∈K) (h3 : A∈K)
    (w : List (Fin 9)) : word w∈K := by
  have hl (i : Fin 9) : letter i∈K := by
    fin_cases i
    · exact hT
    · exact K.inv_mem hT
    · exact hU
    · exact K.inv_mem hU
    · exact hZ
    · exact h2
    · exact K.inv_mem h2
    · exact h3
    · exact K.inv_mem h3
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def repRow (c d : ZMod 11) : SL(2,ℤ) :=
  match c.val*11+d.val with
  | 11 | 22 | 33 | 44 | 55 | 66 | 77 | 88 | 99 | 110 => ⟨!![0,-1;1,0], by decide⟩
  | 12 | 24 | 36 | 48 | 60 | 72 | 84 | 96 | 108 | 120 => ⟨!![0,-1;1,1], by decide⟩
  | 21 | 31 | 41 | 51 | 61 | 71 | 81 | 91 | 101 | 111 => ⟨!![-1,0;1,-1], by decide⟩
  | 13 | 26 | 39 | 52 | 65 | 67 | 80 | 93 | 106 | 119 => ⟨!![0,-1;1,2], by decide⟩
  | 16 | 32 | 37 | 53 | 58 | 74 | 79 | 95 | 100 | 116 => ⟨!![-1,0;2,-1], by decide⟩
  | 14 | 28 | 42 | 45 | 59 | 73 | 87 | 90 | 104 | 118 => ⟨!![0,-1;1,3], by decide⟩
  | 17 | 23 | 40 | 46 | 63 | 69 | 86 | 92 | 109 | 115 => ⟨!![-1,-1;2,1], by decide⟩
  | 18 | 25 | 43 | 50 | 57 | 75 | 82 | 89 | 107 | 114 => ⟨!![-1,0;3,-1], by decide⟩
  | 15 | 30 | 34 | 49 | 64 | 68 | 83 | 98 | 102 | 117 => ⟨!![0,-1;1,4], by decide⟩
  | 20 | 29 | 38 | 47 | 56 | 76 | 85 | 94 | 103 | 112 => ⟨!![-1,1;1,-2], by decide⟩
  | 19 | 27 | 35 | 54 | 62 | 70 | 78 | 97 | 105 | 113 => ⟨!![-1,-1;3,2], by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 11) : List (Fin 9) :=
  match c.val*11+d.val with
  | 11 | 22 | 33 | 44 | 55 | 66 | 77 | 88 | 99 | 110 => [4]
  | 21 | 31 | 41 | 51 | 61 | 71 | 81 | 91 | 101 | 111 => [4]
  | 16 | 32 | 37 | 53 | 58 | 74 | 79 | 95 | 100 | 116 => [4]
  | 18 | 25 | 43 | 50 | 57 | 75 | 82 | 89 | 107 | 114 => [4]
  | 15 | 30 | 34 | 49 | 64 | 68 | 83 | 98 | 102 | 117 => [4, 6, 0]
  | 20 | 29 | 38 | 47 | 56 | 76 | 85 | 94 | 103 | 112 => [4]
  | 19 | 27 | 35 | 54 | 62 | 70 | 78 | 97 | 105 | 113 => [1, 5]
  | _ => []

def edgeTRow (c d : ZMod 11) : List (Fin 9) :=
  match c.val*11+d.val with
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => [0]
  | 21 | 31 | 41 | 51 | 61 | 71 | 81 | 91 | 101 | 111 => [1]
  | 17 | 23 | 40 | 46 | 63 | 69 | 86 | 92 | 109 | 115 => [1, 5, 3, 7]
  | 15 | 30 | 34 | 49 | 64 | 68 | 83 | 98 | 102 | 117 => [6, 0]
  | 19 | 27 | 35 | 54 | 62 | 70 | 78 | 97 | 105 | 113 => [8, 0]
  | _ => []

def rep (g : SL(2,ZMod 11)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_nonzero (g : SL(2,ZMod 11)) : g.1 1 0≠0 ∨ g.1 1 1≠0 := by
  by_contra h
  push Not at h
  have hd := g.det_coe
  rw [det_fin_two, h.1, h.2] at hd
  norm_num at hd
  exact (by decide : (0:ZMod 11)≠1) hd

theorem edgeSRow_checked : ∀ c d : ZMod 11, c≠0 ∨ d≠0 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by decide

theorem edgeTRow_checked : ∀ c d : ZMod 11, c≠0 ∨ d≠0 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by decide

theorem edgeS_checked (g : SL(2,ZMod 11)) :
    rep g*S*(rep (g*reduction 11 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 11 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 11 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 11)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_nonzero g)

theorem edgeT_checked (g : SL(2,ZMod 11)) :
    rep g*T*(rep (g*reduction 11 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 11 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 11 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 11)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_nonzero g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 11)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 11, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower 11∈K) (hZ : -1∈K)
    (h2 : oddMatrix 11 6 (by decide)∈K) (h3 : A∈K)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 11) : γ∈K := by
  apply transversal_mem (reduction 11) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hT hU hZ h2 h3 _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hT hU hZ h2 h3 _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edgeS_checked
#print axioms edgeT_checked
#print axioms gamma0_mem

end SmallLevelEleven
