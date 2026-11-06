module

public import AsymptoticQuotientSandwichV1
public import AsymptoticQuotientEquivarianceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticQuotientOperators

open AsymptoticNestedQuotients AsymptoticRegularTrace ContinuousLinearMap InnerProductSpace
open scoped lp InnerProduct

variable {G ι : Type*} [Group G] {H : Subgroup G}

/-- Apply the listed local operators in order. -/
noncomputable def word (B : ι → ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) :
    List ι → ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)
  | [] => 1
  | i::l => (word B l).comp (B i)

theorem word_supported {T : Subgroup G} (hT : H≤T)
    (B : ι → ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (l : List ι) (hB : ∀ i∈l,Supported hT (B i)) : Supported hT (word B l) := by
  induction l with
  | nil => exact AsymptoticPartitionSupport.supported_one (forget hT)
  | cons i l ih =>
    exact AsymptoticPartitionSupport.supported_comp (forget hT) _ _
      (ih (fun j hj => hB j (List.mem_cons_of_mem i hj))) (hB i (List.mem_cons_self))

theorem word_equivariant
    (B : ι → ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (l : List ι) (hB : ∀ i∈l,Equivariant (B i)) : Equivariant (word B l) := by
  induction l with
  | nil => exact equivariant_one
  | cons i l ih =>
    exact equivariant_comp _ _ (ih (fun j hj => hB j (List.mem_cons_of_mem i hj)))
      (hB i List.mem_cons_self)

theorem gram_diagonal (B : ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ)) (q : Classes H) :
    matrix (B.adjoint.comp B) q q=((‖B (delta q)‖^2:ℝ):ℂ) := by
  rw [matrix_cross,inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow]
  rfl

/-- The squared rooted norm of a product factors under subgroup
separation and right equivariance. Commutativity of the factors is not
needed, and the factors need not be finite coset sums. -/
theorem word_norm_sq (S T : ι → Subgroup G) (hS : ∀ i,H≤S i) (hT : ∀ i,H≤T i)
    (hsep : ∀ i,S i⊓T i≤H) (hother : ∀ i j,j≠i → S j≤T i)
    (B : ι → ℓ²(Classes H,ℂ) →L[ℂ] ℓ²(Classes H,ℂ))
    (hB : ∀ i,Supported (hS i) (B i)) (he : ∀ i,Equivariant (B i))
    (l : List ι) (hl : l.Nodup) :
    ‖word B l (delta (classOf H 1))‖^2=
      (l.map (fun i => ‖B i (delta (classOf H 1))‖^2)).prod := by
  induction l with
  | nil => simp [word,delta]
  | cons i l ih =>
    have hn := List.nodup_cons.mp hl
    have hs : Supported (hT i) (word B l) := by
      apply word_supported
      intro j hj
      exact supported_mono (hS j) (hT i)
        (hother i j (fun h => hn.1 (h ▸ hj))) (B j) (hB j)
    have hsa : Supported (hT i) ((word B l).adjoint.comp (word B l)) :=
      AsymptoticPartitionSupport.supported_comp (forget (hT i)) _ _
        (AsymptoticPartitionSupport.supported_adjoint (forget (hT i)) _ hs) hs
    have hea := equivariant_comp (word B l).adjoint (word B l)
      (equivariant_adjoint _ (word_equivariant B l (fun j _ => he j)))
      (word_equivariant B l (fun j _ => he j))
    have hh := separated_sandwich (hS i) (hT i) (hsep i) (B i)
      ((word B l).adjoint.comp (word B l)) (hB i) hsa
      (((‖word B l (delta (classOf H 1))‖^2):ℝ):ℂ)
      (fun q => (equivariant_diagonal _ hea q).trans (gram_diagonal _ _))
    have hg : (B i).adjoint.comp (((word B l).adjoint.comp (word B l)).comp (B i))=
        (word B (i::l)).adjoint.comp (word B (i::l)) := by
      simp only [word,adjoint_comp,comp_assoc]
    rw [hg,gram_diagonal] at hh
    have hr : ‖word B (i::l) (delta (classOf H 1))‖^2=
        ‖word B l (delta (classOf H 1))‖^2*‖B i (delta (classOf H 1))‖^2 := by
      exact_mod_cast hh
    rw [hr,ih hn.2,List.map_cons,List.prod_cons,mul_comm]

#print axioms word_supported
#print axioms word_equivariant
#print axioms gram_diagonal
#print axioms word_norm_sq

end AsymptoticQuotientOperators
