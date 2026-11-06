module

public import SmallLevelOddWordsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section
namespace SmallLevelTwentyOneGeneration
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def generator : Fin 28 → SL(2,ℤ)
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![1,0;21,1],by decide⟩
  | 2 => ⟨!![2,-1;-21,11],by decide⟩
  | 3 => ⟨!![5,-2;-42,17],by decide⟩
  | 4 => ⟨!![5,2;42,17],by decide⟩
  | 5 => ⟨!![5,1;-21,-4],by decide⟩
  | 6 => ⟨!![5,-1;21,-4],by decide⟩
  | 7 => ⟨!![22,3;-147,-20],by decide⟩
  | 8 => ⟨!![-41,-7;252,43],by decide⟩
  | 9 => ⟨!![86,13;-483,-73],by decide⟩
  | 10 => ⟨!![131,20;-714,-109],by decide⟩
  | 11 => ⟨!![47,4;-294,-25],by decide⟩
  | 12 => ⟨!![5,1;-21,-4],by decide⟩
  | 13 => ⟨!![-121,-19;777,122],by decide⟩
  | 14 => ⟨!![1,0;-21,1],by decide⟩
  | 15 => ⟨!![1,-1;0,1],by decide⟩
  | 16 => ⟨!![11,1;21,2],by decide⟩
  | 17 => ⟨!![17,2;42,5],by decide⟩
  | 18 => ⟨!![17,-2;-42,5],by decide⟩
  | 19 => ⟨!![-4,1;-21,5],by decide⟩
  | 20 => ⟨!![-4,-1;21,5],by decide⟩
  | 21 => ⟨!![43,7;-252,-41],by decide⟩
  | 22 => ⟨!![-20,-3;147,22],by decide⟩
  | 23 => ⟨!![-73,-13;483,86],by decide⟩
  | 24 => ⟨!![-109,-20;714,131],by decide⟩
  | 25 => ⟨!![-25,-4;294,47],by decide⟩
  | 26 => ⟨!![122,19;-777,-121],by decide⟩
  | _ => ⟨!![-4,-1;21,5],by decide⟩

def letter : Fin 57 → SL(2,ℤ)
  | 0 => generator 0
  | 1 => (generator 0)⁻¹
  | 2 => generator 1
  | 3 => (generator 1)⁻¹
  | 4 => generator 2
  | 5 => (generator 2)⁻¹
  | 6 => generator 3
  | 7 => (generator 3)⁻¹
  | 8 => generator 4
  | 9 => (generator 4)⁻¹
  | 10 => generator 5
  | 11 => (generator 5)⁻¹
  | 12 => generator 6
  | 13 => (generator 6)⁻¹
  | 14 => generator 7
  | 15 => (generator 7)⁻¹
  | 16 => generator 8
  | 17 => (generator 8)⁻¹
  | 18 => generator 9
  | 19 => (generator 9)⁻¹
  | 20 => generator 10
  | 21 => (generator 10)⁻¹
  | 22 => generator 11
  | 23 => (generator 11)⁻¹
  | 24 => generator 12
  | 25 => (generator 12)⁻¹
  | 26 => generator 13
  | 27 => (generator 13)⁻¹
  | 28 => generator 14
  | 29 => (generator 14)⁻¹
  | 30 => generator 15
  | 31 => (generator 15)⁻¹
  | 32 => generator 16
  | 33 => (generator 16)⁻¹
  | 34 => generator 17
  | 35 => (generator 17)⁻¹
  | 36 => generator 18
  | 37 => (generator 18)⁻¹
  | 38 => generator 19
  | 39 => (generator 19)⁻¹
  | 40 => generator 20
  | 41 => (generator 20)⁻¹
  | 42 => generator 21
  | 43 => (generator 21)⁻¹
  | 44 => generator 22
  | 45 => (generator 22)⁻¹
  | 46 => generator 23
  | 47 => (generator 23)⁻¹
  | 48 => generator 24
  | 49 => (generator 24)⁻¹
  | 50 => generator 25
  | 51 => (generator 25)⁻¹
  | 52 => generator 26
  | 53 => (generator 26)⁻¹
  | 54 => generator 27
  | 55 => (generator 27)⁻¹
  | _ => -1

def word (w : List (Fin 57)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hg : ∀ i, generator i∈K)
    (hz : -1∈K) (w : List (Fin 57)) : word w∈K := by
  have hl (i : Fin 57) : letter i∈K := by
    fin_cases i
    · exact hg 0
    · exact K.inv_mem (hg 0)
    · exact hg 1
    · exact K.inv_mem (hg 1)
    · exact hg 2
    · exact K.inv_mem (hg 2)
    · exact hg 3
    · exact K.inv_mem (hg 3)
    · exact hg 4
    · exact K.inv_mem (hg 4)
    · exact hg 5
    · exact K.inv_mem (hg 5)
    · exact hg 6
    · exact K.inv_mem (hg 6)
    · exact hg 7
    · exact K.inv_mem (hg 7)
    · exact hg 8
    · exact K.inv_mem (hg 8)
    · exact hg 9
    · exact K.inv_mem (hg 9)
    · exact hg 10
    · exact K.inv_mem (hg 10)
    · exact hg 11
    · exact K.inv_mem (hg 11)
    · exact hg 12
    · exact K.inv_mem (hg 12)
    · exact hg 13
    · exact K.inv_mem (hg 13)
    · exact hg 14
    · exact K.inv_mem (hg 14)
    · exact hg 15
    · exact K.inv_mem (hg 15)
    · exact hg 16
    · exact K.inv_mem (hg 16)
    · exact hg 17
    · exact K.inv_mem (hg 17)
    · exact hg 18
    · exact K.inv_mem (hg 18)
    · exact hg 19
    · exact K.inv_mem (hg 19)
    · exact hg 20
    · exact K.inv_mem (hg 20)
    · exact hg 21
    · exact K.inv_mem (hg 21)
    · exact hg 22
    · exact K.inv_mem (hg 22)
    · exact hg 23
    · exact K.inv_mem (hg 23)
    · exact hg 24
    · exact K.inv_mem (hg 24)
    · exact hg 25
    · exact K.inv_mem (hg 25)
    · exact hg 26
    · exact K.inv_mem (hg 26)
    · exact hg 27
    · exact K.inv_mem (hg 27)
    · exact hz
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact hl i)

def rowClass (c d : ZMod 21) : ℕ :=
  ([32, 0, 0, 32, 0, 0, 32, 32, 0, 32, 0, 0, 32, 0, 32, 32, 0, 0, 32, 0, 0, 1, 2, 4, 7, 12, 19, 25, 24, 17, 10, 6, 8, 13, 21, 27, 28, 23, 15, 9, 5, 3, 1, 8, 2, 13, 4, 21, 7, 27, 12, 28, 19, 23, 25, 15, 24, 9, 17, 5, 10, 3, 6, 32, 14, 16, 32, 22, 20, 32, 26, 14, 32, 18, 22, 32, 11, 26, 32, 16, 18, 32, 20, 11, 1, 23, 8, 25, 2, 15, 13, 24, 4, 9, 21, 17, 7, 5, 27, 10, 12, 3, 28, 6, 19, 1, 15, 21, 10, 19, 2, 9, 27, 6, 25, 4, 5, 28, 8, 24, 7, 3, 23, 13, 17, 12, 32, 22, 14, 32, 16, 11, 32, 26, 22, 32, 20, 16, 32, 18, 26, 32, 14, 20, 32, 11, 18, 32, 31, 29, 30, 31, 29, 30, 32, 29, 30, 31, 29, 30, 31, 32, 30, 31, 29, 30, 31, 29, 1, 17, 23, 7, 8, 5, 25, 27, 2, 10, 15, 12, 13, 3, 24, 28, 4, 6, 9, 19, 21, 32, 20, 18, 32, 11, 22, 32, 26, 20, 32, 14, 11, 32, 16, 26, 32, 18, 14, 32, 22, 16, 1, 5, 15, 28, 21, 8, 10, 24, 19, 7, 2, 3, 9, 23, 27, 13, 6, 17, 25, 12, 4, 1, 4, 12, 25, 17, 6, 13, 27, 23, 9, 3, 2, 7, 19, 24, 10, 8, 21, 28, 15, 5, 32, 16, 22, 32, 14, 18, 32, 26, 16, 32, 11, 14, 32, 20, 26, 32, 22, 11, 32, 18, 20, 1, 21, 19, 9, 6, 4, 28, 24, 3, 13, 12, 15, 10, 2, 27, 25, 5, 8, 7, 23, 17, 32, 29, 31, 30, 29, 31, 30, 32, 31, 30, 29, 31, 30, 29, 32, 30, 29, 31, 30, 29, 31, 32, 18, 11, 32, 20, 14, 32, 26, 18, 32, 16, 20, 32, 22, 26, 32, 11, 16, 32, 14, 22, 1, 12, 17, 13, 23, 3, 7, 24, 8, 28, 5, 4, 25, 6, 27, 9, 2, 19, 10, 21, 15, 1, 19, 6, 28, 3, 12, 10, 27, 5, 7, 17, 21, 9, 4, 24, 13, 15, 2, 25, 8, 23, 32, 11, 20, 32, 18, 16, 32, 26, 11, 32, 22, 18, 32, 14, 26, 32, 20, 22, 32, 16, 14, 1, 6, 3, 10, 5, 17, 9, 24, 15, 25, 23, 19, 28, 12, 27, 7, 21, 4, 13, 2, 8, 1, 3, 5, 9, 15, 23, 28, 27, 21, 13, 8, 6, 10, 17, 24, 25, 19, 12, 7, 4, 2] : List ℕ).getD (c.val*21+d.val) 32

def repRow (c d : ZMod 21) : SL(2,ℤ) :=
  match rowClass c d with
  | 0 => ⟨!![1,0;0,1],by decide⟩
  | 1 => ⟨!![0,-1;1,0],by decide⟩
  | 2 => ⟨!![0,-1;1,1],by decide⟩
  | 3 => ⟨!![0,-1;1,-1],by decide⟩
  | 4 => ⟨!![0,-1;1,2],by decide⟩
  | 5 => ⟨!![0,-1;1,-2],by decide⟩
  | 6 => ⟨!![-1,0;2,-1],by decide⟩
  | 7 => ⟨!![0,-1;1,3],by decide⟩
  | 8 => ⟨!![-1,0;-2,-1],by decide⟩
  | 9 => ⟨!![0,-1;1,-3],by decide⟩
  | 10 => ⟨!![-1,1;2,-3],by decide⟩
  | 11 => ⟨!![-1,0;3,-1],by decide⟩
  | 12 => ⟨!![0,-1;1,4],by decide⟩
  | 13 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 14 => ⟨!![-1,0;-3,-1],by decide⟩
  | 15 => ⟨!![0,-1;1,-4],by decide⟩
  | 16 => ⟨!![1,1;-3,-2],by decide⟩
  | 17 => ⟨!![-1,2;2,-5],by decide⟩
  | 18 => ⟨!![-1,1;3,-4],by decide⟩
  | 19 => ⟨!![-1,0;4,-1],by decide⟩
  | 20 => ⟨!![-1,1;-3,2],by decide⟩
  | 21 => ⟨!![-1,-2;-2,-5],by decide⟩
  | 22 => ⟨!![-1,-1;-3,-4],by decide⟩
  | 23 => ⟨!![-1,0;-4,-1],by decide⟩
  | 24 => ⟨!![-1,3;2,-7],by decide⟩
  | 25 => ⟨!![1,1;-4,-3],by decide⟩
  | 26 => ⟨!![-1,2;3,-7],by decide⟩
  | 27 => ⟨!![-1,-3;-2,-7],by decide⟩
  | 28 => ⟨!![-1,1;-4,3],by decide⟩
  | 29 => ⟨!![3,1;-7,-2],by decide⟩
  | 30 => ⟨!![2,1;-7,-3],by decide⟩
  | 31 => ⟨!![-3,1;-7,2],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 21) : List (Fin 57) :=
  match rowClass c d with
  | 1 => [56]
  | 2 => [1]
  | 3 => [56, 0]
  | 6 => [56]
  | 8 => [56]
  | 11 => [56]
  | 14 => [56]
  | 16 => [56]
  | 17 => [1, 5, 6]
  | 19 => [56]
  | 20 => [56]
  | 21 => [56, 5, 3, 8]
  | 23 => [56]
  | 25 => [56]
  | 28 => [56]
  | 29 => [56]
  | 30 => [56]
  | 31 => [56]
  | _ => []

def edgeTRow (c d : ZMod 21) : List (Fin 57) :=
  match rowClass c d with
  | 0 => [0]
  | 6 => [56, 1]
  | 11 => [56]
  | 12 => [56, 11]
  | 16 => [56, 1, 5, 6]
  | 19 => [56]
  | 22 => [56, 5, 23, 11]
  | 23 => [12]
  | 25 => [10, 4, 0]
  | 27 => [56, 5, 3, 13]
  | 29 => [1, 5, 11]
  | 30 => [10, 14, 6]
  | 31 => [5, 3, 8]
  | _ => []

def rep (g : SL(2,ZMod 21)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem nonprimitive_annihilator : ∀ c d : ZMod 21, ¬rowClass c d<32 →
    ((7*c=0 ∧ 7*d=0) ∨ (3*c=0 ∧ 3*d=0)) := by decide

theorem row_primitive (g : SL(2,ZMod 21)) : rowClass (g.1 1 0) (g.1 1 1)<32 := by
  by_contra h
  have hd := g.det_coe
  rw [det_fin_two] at hd
  rcases nonprimitive_annihilator _ _ h with h|h
  · have hz : (7:ZMod 21)=0 := by
      linear_combination -7*hd+(g.1 0 0)*h.2-(g.1 0 1)*h.1
    exact (by decide : (7:ZMod 21)≠0) hz
  · have hz : (3:ZMod 21)=0 := by
      linear_combination -3*hd+(g.1 0 0)*h.2-(g.1 0 1)*h.1
    exact (by decide : (3:ZMod 21)≠0) hz

theorem edgeSRow_checked : ∀ c d : ZMod 21, rowClass c d<32 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by decide

theorem edgeTRow_checked : ∀ c d : ZMod 21, rowClass c d<32 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by decide

theorem edgeS_checked (g : SL(2,ZMod 21)) :
    rep g*S*(rep (g*reduction 21 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 21 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 21 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 21)) := by decide
    simp [rep,hS,Matrix.mul_apply,Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 21)) :
    rep g*T*(rep (g*reduction 21 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 21 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 21 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 21)) := by decide
    simp [rep,hT,Matrix.mul_apply,Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 21)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 21, repRow 0 d=1 := by decide
  simpa only [rep,hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hg : ∀ i, generator i∈K)
    (hz : -1∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 21) : γ∈K := by
  apply transversal_mem (reduction 21) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hg hz _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hg hz _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms row_primitive
#print axioms edgeS_checked
#print axioms edgeT_checked
#print axioms gamma0_mem
end SmallLevelTwentyOneGeneration
