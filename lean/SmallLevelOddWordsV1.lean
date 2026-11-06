module

public import SmallLevelOddFrickeV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
@[expose] public section

namespace SmallLevelGenerators
open Matrix ModularGroup
open scoped MatrixGroups

def oddLetter (N a : ℕ) (ha : 2*a=N+1) : Fin 7 → SL(2,ℤ)
  | 0 => T
  | 1 => T⁻¹
  | 2 => lower N
  | 3 => (lower N)⁻¹
  | 4 => -1
  | 5 => oddMatrix N a ha
  | 6 => (oddMatrix N a ha)⁻¹

def oddWord (N a : ℕ) (ha : 2*a=N+1) (w : List (Fin 7)) : SL(2,ℤ) :=
  (w.map (oddLetter N a ha)).prod

theorem oddWord_mem (N a : ℕ) (ha : 2*a=N+1) (K : Subgroup SL(2,ℤ))
    (hT : T∈K) (hU : lower N∈K) (hZ : -1∈K) (hA : oddMatrix N a ha∈K)
    (w : List (Fin 7)) : oddWord N a ha w∈K := by
  have hl (i : Fin 7) : oddLetter N a ha i∈K := by
    fin_cases i
    · exact hT
    · exact K.inv_mem hT
    · exact hU
    · exact K.inv_mem hU
    · exact hZ
    · exact hA
    · exact K.inv_mem hA
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

#print axioms oddWord_mem

end SmallLevelGenerators
