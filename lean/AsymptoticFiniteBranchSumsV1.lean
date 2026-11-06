module

public import AsymptoticFiniteBranchExpressionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane

noncomputable def ofFinset {ι : Type*} (s : Finset ι) (f : ι → Branch) : Expression := s.toList.map f
noncomputable def sumExpressions {ι : Type*} (s : Finset ι) (f : ι → Expression) : Expression := s.toList.flatMap f

theorem holomorphicSum_ofFinset {ι : Type*} (s : Finset ι) (f : ι → Branch) (m : ℕ) :
    holomorphicSum (ofFinset s f) m=∑ i∈s,holomorphic (f i) m := by
  simp only [holomorphicSum,ofFinset,List.map_map,Function.comp_def,Finset.sum_map_toList]

theorem regularSum_ofFinset {ι : Type*} (s : Finset ι) (f : ι → Branch) (z : ℍ) :
    regularSum (ofFinset s f) z=∑ i∈s,regular (f i) z := by
  simp only [regularSum,ofFinset,List.map_map,Function.comp_def,Finset.sum_map_toList]

theorem holomorphicSum_flatMap {ι : Type*} (l : List ι) (f : ι → Expression) (m : ℕ) :
    holomorphicSum (l.flatMap f) m=(l.map (fun i => holomorphicSum (f i) m)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    exact (holomorphicSum_append (f i) (l.flatMap f) m).trans (congrArg (fun T => holomorphicSum (f i) m+T) ih)

theorem regularSum_flatMap {ι : Type*} (l : List ι) (f : ι → Expression) (z : ℍ) :
    regularSum (l.flatMap f) z=(l.map (fun i => regularSum (f i) z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    exact (regularSum_append (f i) (l.flatMap f) z).trans (congrArg (fun T => regularSum (f i) z+T) ih)

theorem holomorphicSum_sumExpressions {ι : Type*} (s : Finset ι) (f : ι → Expression) (m : ℕ) :
    holomorphicSum (sumExpressions s f) m=∑ i∈s,holomorphicSum (f i) m :=
  (holomorphicSum_flatMap s.toList f m).trans (Finset.sum_map_toList _ _)

theorem regularSum_sumExpressions {ι : Type*} (s : Finset ι) (f : ι → Expression) (z : ℍ) :
    regularSum (sumExpressions s f) z=∑ i∈s,regularSum (f i) z :=
  (regularSum_flatMap s.toList f z).trans (Finset.sum_map_toList _ _)

#print axioms holomorphicSum_ofFinset
#print axioms regularSum_ofFinset
#print axioms holomorphicSum_sumExpressions
#print axioms regularSum_sumExpressions

end AsymptoticFiniteBranch
