module

public import QuantitativeArithmeticSmallLevelNineteenGridAnalyticTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenGridExceptionalCentersV1
public import QuantitativeArithmeticSmallLevelNineteenGridGroupRowsV1
public import QuantitativeArithmeticSmallLevelNineteenGridSystemTheoryV4
public import SmallLevelTaylorRowCoefficientsV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelNineteenFullGroup. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelNineteenFullGroupMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullGroup
open Matrix ModularGroup UpperHalfPlane SmallLevelNormalized SmallLevelGenerators SmallLevelOriginal
open QuantitativeArithmeticSmallLevelNineteen
open scoped MatrixGroups ModularForm
def generator : Fin 7 → SL(2,ℤ) :=
  ![T,lower 19,tenthMinus,T⁻¹,(lower 19)⁻¹,tenthMinus⁻¹,-1]

theorem original_generator (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 7) :
    generator i ∈ slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f) := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have ht : T∈K := original_T (2*m) f
  have hu : lower 19∈K := original_lower (by decide) hf
  have he : tenthMinus∈K := (original_tenth_matrices hf).1
  fin_cases i
  · exact ht
  · exact hu
  · exact he
  · exact K.inv_mem ht
  · exact K.inv_mem hu
  · exact K.inv_mem he
  · exact SmallLevelThirtySix.slash_neg_one_even _ m

theorem original_word (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (w : List (Fin 7)) :
    (w.map generator).prod ∈ slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih => exact Subgroup.mul_mem _ (original_generator m hf i) ih

def poleMatrix : Fin 91 → SL(2,ℤ) :=
  ![⟨!![1,-1;-38,39],by decide⟩,⟨!![1,-1;-19,20],by decide⟩,⟨!![1,-1;19,-18],by decide⟩,⟨!![1,-1;38,-37],by decide⟩,⟨!![1,0;-57,1],by decide⟩,⟨!![1,0;-38,1],by decide⟩,⟨!![1,0;-19,1],by decide⟩,⟨!![1,0;19,1],by decide⟩,⟨!![1,0;38,1],by decide⟩,⟨!![1,0;57,1],by decide⟩,⟨!![2,-1;-95,48],by decide⟩,⟨!![2,-1;-57,29],by decide⟩,⟨!![2,-1;-19,10],by decide⟩,⟨!![2,-1;19,-9],by decide⟩,⟨!![2,-1;57,-28],by decide⟩,⟨!![9,-10;19,-21],by decide⟩,⟨!![9,-8;-19,17],by decide⟩,⟨!![9,-1;-152,17],by decide⟩,⟨!![9,-1;19,-2],by decide⟩,⟨!![9,-1;190,-21],by decide⟩,⟨!![9,1;-19,-2],by decide⟩,⟨!![10,-9;-171,154],by decide⟩,⟨!![10,-9;19,-17],by decide⟩,⟨!![10,-9;209,-188],by decide⟩,⟨!![10,-1;-19,2],by decide⟩,⟨!![10,1;19,2],by decide⟩,⟨!![15,-8;-133,71],by decide⟩,⟨!![15,-7;-152,71],by decide⟩,⟨!![17,-16;-171,161],by decide⟩,⟨!![17,-9;-304,161],by decide⟩,⟨!![17,-9;19,-10],by decide⟩,⟨!![17,-9;342,-181],by decide⟩,⟨!![17,-8;-19,9],by decide⟩,⟨!![17,-1;-152,9],by decide⟩,⟨!![18,-19;19,-20],by decide⟩,⟨!![18,-17;-19,18],by decide⟩,⟨!![18,-1;-323,18],by decide⟩,⟨!![18,-1;19,-1],by decide⟩,⟨!![18,1;-19,-1],by decide⟩,⟨!![20,-21;-19,20],by decide⟩,⟨!![20,-19;19,-18],by decide⟩,⟨!![20,-1;-399,20],by decide⟩,⟨!![20,-1;-19,1],by decide⟩,⟨!![20,1;19,1],by decide⟩,⟨!![21,-11;-418,219],by decide⟩,⟨!![21,-11;-19,10],by decide⟩,⟨!![21,-11;380,-199],by decide⟩,⟨!![21,-10;19,-9],by decide⟩,⟨!![21,-1;-608,29],by decide⟩,⟨!![21,-1;-209,10],by decide⟩,⟨!![21,-1;190,-9],by decide⟩,⟨!![23,-12;-665,347],by decide⟩,⟨!![23,-12;-228,119],by decide⟩,⟨!![23,-12;209,-109],by decide⟩,⟨!![28,-3;19,-2],by decide⟩,⟨!![28,-1;57,-2],by decide⟩,⟨!![28,1;-57,-2],by decide⟩,⟨!![28,3;-19,-2],by decide⟩,⟨!![29,-28;57,-55],by decide⟩,⟨!![29,-26;19,-17],by decide⟩,⟨!![29,1;57,2],by decide⟩,⟨!![29,3;19,2],by decide⟩,⟨!![36,-19;19,-10],by decide⟩,⟨!![37,-19;76,-39],by decide⟩,⟨!![37,-2;19,-1],by decide⟩,⟨!![37,-1;38,-1],by decide⟩,⟨!![37,1;-38,-1],by decide⟩,⟨!![37,2;-19,-1],by decide⟩,⟨!![39,-19;76,-37],by decide⟩,⟨!![39,-2;-19,1],by decide⟩,⟨!![39,-1;-38,1],by decide⟩,⟨!![39,1;38,1],by decide⟩,⟨!![39,2;19,1],by decide⟩,⟨!![40,-21;-19,10],by decide⟩,⟨!![40,-1;-399,10],by decide⟩,⟨!![48,1;95,2],by decide⟩,⟨!![48,5;19,2],by decide⟩,⟨!![55,-28;57,-29],by decide⟩,⟨!![59,-30;-57,29],by decide⟩,⟨!![59,-3;-570,29],by decide⟩,⟨!![61,-32;-589,309],by decide⟩,⟨!![61,-31;-608,309],by decide⟩,⟨!![86,3;57,2],by decide⟩,⟨!![109,-12;209,-23],by decide⟩,⟨!![119,-107;228,-205],by decide⟩,⟨!![181,-9;342,-17],by decide⟩,⟨!![188,-9;209,-10],by decide⟩,⟨!![199,-11;380,-21],by decide⟩,⟨!![205,-107;228,-119],by decide⟩,⟨!![230,-11;-209,10],by decide⟩,⟨!![251,-131;-228,119],by decide⟩]

def poleWord : Fin 91 → List (Fin 7) :=
  ![[4,4,3],[4,3],[1,3],[1,1,3],[4,4,4],[4,4],[4],[1],[1,1],[1,1,1],[4,4,2],[4,2],[2],[1,2],[1,1,2],[5,4,6,3],[3,5,6,3],[4,5,4,6],[5,4,6],[1,5,4,6],[3,5,6],[4,5,3],[5,3],[1,5,3],[3,5,6,4,6],[5],[2,0,2,6],[2,1,6,2],[2,1,6,3],[4,0,2,6],[0,2,6],[1,0,2,6],[3,1,6,2],[2,0,4,6],[0,4,6,3],[3,1,6,3],[4,0,4,6],[0,4,6],[3,1,6],[3,4,3],[0,1,3],[4,3,4],[3,4],[0,1],[4,3,2],[3,2],[1,3,2],[0,1,2],[4,2,4],[2,4],[1,2,4],[4,2,2],[2,2],[1,2,2],[0,5,4,6],[5,4,6,4],[3,5,6,1],[3,3,5,6],[5,1,3],[0,5,3],[5,1],[0,5],[0,0,2,6],[5,4,6,2],[0,0,4,6],[0,4,6,4],[3,1,6,1],[3,3,1,6],[5,1,2],[3,3,4],[3,4,4],[0,1,1],[0,0,1],[3,3,2],[2,4,4],[5,1,1],[0,0,5],[0,4,6,2],[3,4,2],[2,3,4],[2,3,2],[2,4,2],[0,5,1],[5,5,4,6],[5,5,3],[5,3,4],[0,2,6,4],[5,0,4,6],[0,2,6,2],[3,2,4],[3,2,2]]

theorem poleMatrix_word (i : Fin 91) : poleMatrix i=((poleWord i).map generator).prod := by
  fin_cases i <;> decide

theorem original_pole_matrices (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 91) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] poleMatrix i=fourierFunction (2*m) f := by
  change poleMatrix i ∈ slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  rw [poleMatrix_word]
  exact original_word m hf _

theorem poleMatrix_lower_ne_zero (i : Fin 91) : (poleMatrix i).val 1 0≠0 := by
  fin_cases i <;> decide

#print axioms original_pole_matrices
#print axioms poleMatrix_lower_ne_zero
end QuantitativeArithmeticSmallLevelNineteenFullGroup
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenFullGroupCentersV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullGroup
open Complex Matrix SmallLevelAdditive SmallLevelOriginal
open FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelNineteen (exceptionalCenter invariant_matrix_fourier)
open scoped MatrixGroups ModularForm

def centerSpecs : Fin 13 → (Fin 91 × ℕ × ℕ) :=
  ![(4,2,3249),(5,3,1444),(55,4,3249),(6,6,361),(18,12,361),(13,54,361),(14,56,3249),(11,58,3249),(12,60,361),(16,102,361),(2,108,361),(58,110,3249),(3,111,1444)]
def centerMatrix (i : Fin 13) : Fin 91 := (centerSpecs i).1
def centerGrid (i : Fin 13) : ℕ := (centerSpecs i).2.1
def centerScale (i : Fin 13) : ℕ := (centerSpecs i).2.2
def centerEntry (i : Fin 13) (r c : Fin 2) : ℤ := (poleMatrix (centerMatrix i)).val r c

theorem center_geometry (i : Fin 13) :
    centerEntry i 1 0*(centerGrid i:ℤ)+114*centerEntry i 1 1=0 ∧
    centerEntry i 1 0^2=(centerScale i:ℤ) ∧ 0<centerScale i := by
  revert i
  decide

/-- All thirteen grid cusps mapped to infinity by the known words give
entire Mellin transforms, with their initial additive-series agreement. -/
theorem original_center_rows {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 13) :
    (∀ s : ℂ, AnalyticAt ℂ (exceptionalCenter (2*m) f (centerGrid i)) s) ∧
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      exceptionalCenter (2*m) f (centerGrid i) s=
        original (2*m) f ((centerGrid i:ℝ)/114) s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hC : (centerEntry i 1 0:ℝ)≠0 := by
    exact_mod_cast poleMatrix_lower_ne_zero (centerMatrix i)
  have hdetZ : centerEntry i 0 0*centerEntry i 1 1-
      centerEntry i 0 1*centerEntry i 1 0=1 := by
    simpa only [centerEntry,Matrix.det_fin_two] using (poleMatrix (centerMatrix i)).property
  have hdet : (centerEntry i 0 0:ℝ)*(centerEntry i 1 1:ℝ)-
      (centerEntry i 0 1:ℝ)*(centerEntry i 1 0:ℝ)=1 := by exact_mod_cast hdetZ
  have hC2 : (centerEntry i 1 0:ℝ)^2=(centerScale i:ℝ) := by
    exact_mod_cast (center_geometry i).2.1
  have hcenter : -(centerEntry i 1 1:ℝ)/(centerEntry i 1 0:ℝ)=(centerGrid i:ℝ)/114 := by
    have hzero : (centerEntry i 1 0:ℝ)*(centerGrid i:ℝ)+114*(centerEntry i 1 1:ℝ)=0 := by
      exact_mod_cast (center_geometry i).1
    apply (div_eq_div_iff hC (by norm_num : (114:ℝ)≠0)).2
    nlinarith
  have hF := invariant_matrix_fourier (2*m) f (poleMatrix (centerMatrix i))
    (original_pole_matrices m hf (centerMatrix i))
  have he := QuantitativeArithmeticSmallLevelNineteenTwoMellin.matrix_center_entire
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    (2*m) (by omega) (centerEntry i 0 0:ℝ) (centerEntry i 0 1:ℝ)
    (centerEntry i 1 0:ℝ) (centerEntry i 1 1:ℝ) hC hdet
    (centerScale i) (center_geometry i).2.2 hC2
    (by simpa only [centerEntry,Complex.ofReal_intCast] using hF)
  rw [hcenter] at he
  simpa only [exceptionalCenter,original] using he

#print axioms center_geometry
#print axioms original_center_rows
end QuantitativeArithmeticSmallLevelNineteenFullGroup
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenFullGroupGeometryV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullGroup
open Complex Matrix Set SmallLevelAdditive FinitenessOriginalFourier
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic (gridVector gridIndex gridVector_index)
open scoped MatrixGroups ModularForm

def specs : Fin 516 → (Fin 91 × ℤ × ℤ) :=
  ![(0,108,-2),(1,84,-5),(1,102,-4),(1,108,-3),(1,111,-2),(2,72,7),(2,90,8),(2,96,9),(2,99,10),(2,102,12),(2,104,15),(2,105,18),(2,106,24),(2,107,42),(2,109,-30),(2,110,-12),(2,111,-6),(2,112,-3),(3,102,4),(3,108,6),(3,110,12),(3,112,-6),(4,1,2),(4,3,-6),(4,4,-4),(4,6,-3),(5,2,6),(5,4,-12),(5,6,-6),(5,12,-4),(6,2,3),(6,3,6),(6,4,12),(6,5,30),(6,7,-42),(6,8,-24),(6,9,-18),(6,10,-15),(6,12,-12),(6,15,-10),(6,18,-9),(6,24,-8),(6,42,-7),(7,3,2),(7,6,3),(7,12,4),(7,30,5),(8,6,2),(9,2,1),(10,54,-2),(10,57,0),(10,58,-6),(10,60,-3),(11,54,-3),(11,56,-2),(11,57,0),(11,59,-8),(11,60,-6),(11,62,-5),(12,24,-11),(12,42,-10),(12,48,-9),(12,51,-8),(12,54,-6),(12,56,-3),(12,57,0),(12,58,6),(12,59,24),(12,61,-48),(12,62,-30),(12,63,-24),(12,64,-21),(12,66,-18),(12,69,-16),(12,72,-15),(12,78,-14),(12,96,-13),(13,18,13),(13,36,14),(13,42,15),(13,45,16),(13,48,18),(13,50,21),(13,51,24),(13,52,30),(13,53,48),(13,55,-24),(13,56,-6),(13,57,0),(13,58,3),(13,60,6),(13,63,8),(13,66,9),(13,72,10),(13,90,11),(14,52,5),(14,54,6),(14,55,8),(14,57,0),(14,58,2),(14,60,3),(15,90,55),(15,108,56),(16,66,-53),(16,84,-52),(16,90,-51),(16,93,-50),(16,96,-48),(16,98,-45),(16,99,-42),(16,100,-36),(16,101,-18),(16,103,-90),(16,104,-72),(16,105,-66),(16,106,-63),(16,108,-60),(16,111,-58),(17,12,-6),(17,13,-9),(17,15,-7),(18,0,57),(18,3,58),(18,6,60),(18,8,63),(18,9,66),(18,10,72),(18,11,90),(18,13,18),(18,14,36),(18,15,42),(18,16,45),(18,18,48),(18,21,50),(18,24,51),(18,30,52),(18,48,53),(19,12,6),(20,0,-57),(20,6,-56),(20,24,-55),(21,102,-6),(21,103,-8),(21,104,-7),(22,66,61),(22,84,62),(22,90,63),(22,93,64),(22,96,66),(22,98,69),(22,99,72),(22,100,78),(22,101,96),(22,103,24),(22,104,42),(22,105,48),(22,106,51),(22,108,54),(22,111,56),(23,102,6),(24,0,-57),(24,3,-56),(24,6,-54),(24,8,-51),(24,9,-48),(24,10,-42),(24,11,-24),(24,13,-96),(24,14,-78),(24,15,-72),(24,16,-69),(24,18,-66),(24,21,-64),(24,24,-63),(24,30,-62),(24,48,-61),(25,0,57),(25,6,58),(25,24,59),(26,60,-12),(26,61,-18),(26,66,-13),(27,51,-11),(27,53,-9),(27,54,-12),(28,106,-11),(28,107,-10),(28,108,-12),(29,60,-6),(30,24,103),(30,42,104),(30,48,105),(30,51,106),(30,54,108),(30,56,111),(30,57,114),(30,58,120),(30,59,138),(30,61,66),(30,62,84),(30,63,90),(30,64,93),(30,66,96),(30,69,98),(30,72,99),(30,78,100),(30,96,101),(31,60,6),(32,18,-101),(32,36,-100),(32,42,-99),(32,45,-98),(32,48,-96),(32,50,-93),(32,51,-90),(32,52,-84),(32,53,-66),(32,55,-138),(32,56,-120),(32,57,-114),(32,58,-111),(32,60,-108),(32,63,-106),(32,66,-105),(32,72,-104),(32,90,-103),(33,6,-12),(33,7,-15),(33,9,-13),(34,84,109),(34,102,110),(34,108,111),(34,111,112),(35,72,-107),(35,90,-106),(35,96,-105),(35,99,-104),(35,102,-102),(35,104,-99),(35,105,-96),(35,106,-90),(35,107,-72),(35,109,-144),(35,110,-126),(35,111,-120),(35,112,-117),(36,6,-6),(37,2,117),(37,3,120),(37,4,126),(37,5,144),(37,7,72),(37,8,90),(37,9,96),(37,10,99),(37,12,102),(37,15,104),(37,18,105),(37,24,106),(37,42,107),(38,3,-112),(38,6,-111),(38,12,-110),(38,30,-109),(39,84,-119),(39,102,-118),(39,108,-117),(39,111,-116),(40,72,121),(40,90,122),(40,96,123),(40,99,124),(40,102,126),(40,104,129),(40,105,132),(40,106,138),(40,107,156),(40,109,84),(40,110,102),(40,111,108),(40,112,111),(41,6,-6),(42,2,-111),(42,3,-108),(42,4,-102),(42,5,-84),(42,7,-156),(42,8,-138),(42,9,-132),(42,10,-129),(42,12,-126),(42,15,-124),(42,18,-123),(42,24,-122),(42,42,-121),(43,3,116),(43,6,117),(43,12,118),(43,30,119),(44,60,-6),(45,24,-125),(45,42,-124),(45,48,-123),(45,51,-122),(45,54,-120),(45,56,-117),(45,57,-114),(45,58,-108),(45,59,-90),(45,61,-162),(45,62,-144),(45,63,-138),(45,64,-135),(45,66,-132),(45,69,-130),(45,72,-129),(45,78,-128),(45,96,-127),(46,60,6),(47,18,127),(47,36,128),(47,42,129),(47,45,130),(47,48,132),(47,50,135),(47,51,138),(47,52,144),(47,53,162),(47,55,90),(47,56,108),(47,57,114),(47,58,117),(47,60,120),(47,63,122),(47,66,123),(47,72,124),(47,90,125),(48,6,-4),(49,6,-12),(50,6,12),(51,60,-4),(52,59,-11),(52,60,-12),(53,60,12),(54,0,171),(54,3,172),(54,6,174),(54,8,177),(54,9,180),(54,10,186),(54,11,204),(54,13,132),(54,14,150),(54,15,156),(54,16,159),(54,18,162),(54,21,164),(54,24,165),(54,30,166),(54,48,167),(55,0,57),(55,2,58),(55,3,60),(55,5,52),(55,6,54),(55,8,55),(56,0,-57),(57,0,-171),(57,6,-170),(57,24,-169),(58,106,59),(58,108,60),(58,109,62),(58,111,54),(58,112,56),(59,66,175),(59,84,176),(59,90,177),(59,93,178),(59,96,180),(59,98,183),(59,99,186),(59,100,192),(59,101,210),(59,103,138),(59,104,156),(59,105,162),(59,106,165),(59,108,168),(59,111,170),(60,0,57),(61,0,171),(61,6,172),(61,24,173),(62,24,217),(62,42,218),(62,48,219),(62,51,220),(62,54,222),(62,56,225),(62,57,228),(62,58,234),(62,59,252),(62,61,180),(62,62,198),(62,63,204),(62,64,207),(62,66,210),(62,69,212),(62,72,213),(62,78,214),(62,96,215),(63,54,56),(63,58,60),(63,59,51),(63,60,54),(63,63,55),(64,2,231),(64,3,234),(64,4,240),(64,5,258),(64,7,186),(64,8,204),(64,9,210),(64,10,213),(64,12,216),(64,15,218),(64,18,219),(64,24,220),(64,42,221),(65,2,120),(65,4,102),(65,6,108),(65,12,110),(66,6,-112),(67,3,-226),(67,6,-225),(67,12,-224),(67,30,-223),(68,51,59),(68,54,60),(68,55,63),(68,56,54),(68,60,58),(69,2,-225),(69,3,-222),(69,4,-216),(69,5,-198),(69,7,-270),(69,8,-252),(69,9,-246),(69,10,-243),(69,12,-240),(69,15,-238),(69,18,-237),(69,24,-236),(69,42,-235),(70,2,-108),(70,4,-126),(70,6,-120),(70,12,-118),(71,6,116),(72,3,230),(72,6,231),(72,12,232),(72,30,233),(73,24,-239),(73,42,-238),(73,48,-237),(73,51,-236),(73,54,-234),(73,56,-231),(73,57,-228),(73,58,-222),(73,59,-204),(73,61,-276),(73,62,-258),(73,63,-252),(73,64,-249),(73,66,-246),(73,69,-244),(73,72,-243),(73,78,-242),(73,96,-241),(74,3,-12),(75,0,57),(76,0,285),(76,6,286),(76,24,287),(77,54,111),(77,56,112),(77,57,114),(77,59,106),(77,60,108),(77,62,109),(78,54,-117),(78,56,-116),(78,57,-114),(78,59,-122),(78,60,-120),(78,62,-119),(79,6,-12),(80,60,-12),(81,58,-12),(82,0,171),(83,12,60),(84,102,60),(84,103,59),(85,6,60),(86,6,102),(87,6,60),(88,59,103),(88,60,102),(89,6,-126),(90,59,-125),(90,60,-126)]
def matrixIndex (i : Fin 516) : Fin 91 := (specs i).1
def source (i : Fin 516) : ℤ := (specs i).2.1
def partner (i : Fin 516) : ℤ := (specs i).2.2
def entry (i : Fin 516) (r c : Fin 2) : ℤ := (poleMatrix (matrixIndex i)).val r c

theorem integer_geometry (i : Fin 516) :
    entry i 1 0*source i+114*entry i 1 1≠0 ∧
    114*(entry i 0 0*source i+114*entry i 0 1)=
      partner i*(entry i 1 0*source i+114*entry i 1 1) := by
  revert i
  decide

def center (i : Fin 516) : ℝ := (source i:ℝ)/114
def rate (i : Fin 516) : ℝ := ((entry i 1 0:ℝ)*center i+entry i 1 1)^2
def derivativeRate (i : Fin 516) : ℝ :=
  (entry i 1 0:ℝ)*((entry i 1 0:ℝ)*center i+entry i 1 1)

theorem denominator_ne_zero (i : Fin 516) :
    (entry i 1 0:ℝ)*center i+entry i 1 1≠0 := by
  have h : (entry i 1 0:ℝ)*(source i:ℝ)+114*(entry i 1 1:ℝ)≠0 := by
    exact_mod_cast (integer_geometry i).1
  unfold center
  intro he
  apply h
  nlinarith

theorem partner_identity (i : Fin 516) :
    ((entry i 0 0:ℝ)*center i+entry i 0 1)/
      ((entry i 1 0:ℝ)*center i+entry i 1 1)=(partner i:ℝ)/114 := by
  have he : (114:ℝ)*((entry i 0 0:ℝ)*(source i:ℝ)+114*(entry i 0 1:ℝ))=
      (partner i:ℝ)*((entry i 1 0:ℝ)*(source i:ℝ)+114*(entry i 1 1:ℝ)) := by
    exact_mod_cast (integer_geometry i).2
  apply (div_eq_div_iff (denominator_ne_zero i) (by norm_num : (114:ℝ)≠0)).2
  unfold center
  nlinarith [he]

theorem rate_pos (i : Fin 516) : 0<rate i := sq_pos_of_ne_zero (denominator_ne_zero i)

#print axioms integer_geometry
#print axioms partner_identity
end QuantitativeArithmeticSmallLevelNineteenFullGroup
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenFullGroupTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullGroup
open Complex Matrix Set SmallLevelAdditive FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic (gridVector gridIndex gridVector_index)
open QuantitativeArithmeticSmallLevelNineteen (invariant_matrix_fourier)
open scoped MatrixGroups ModularForm

/-- Every one of the 516 group rows used in the pole certificates, with
its full Taylor remainder, follows from the original Euler/Fricke input. -/
theorem original_group_rows {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 516) :
    ∃ (B : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector (2*m) f s (gridIndex (source i))-
          (rate i:ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (I*(derivativeRate i:ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              gridVector (2*m) f (s+(n:ℂ)) (gridIndex (partner i)))=error M s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hdetZ : entry i 0 0*entry i 1 1-entry i 0 1*entry i 1 0=1 := by
    simpa only [entry,Matrix.det_fin_two] using (poleMatrix (matrixIndex i)).property
  have hdet : (entry i 0 0:ℝ)*(entry i 1 1:ℝ)-(entry i 0 1:ℝ)*(entry i 1 0:ℝ)=1 := by
    exact_mod_cast hdetZ
  have hC : (entry i 1 0:ℝ)≠0 := by
    exact_mod_cast poleMatrix_lower_ne_zero (matrixIndex i)
  have hF := invariant_matrix_fourier (2*m) f (poleMatrix (matrixIndex i))
    (original_pole_matrices m hf (matrixIndex i))
  have he := QuantitativeArithmeticTwoSequenceTaylor.matrix_even_rows
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m)) m
    (entry i 0 0:ℝ) (entry i 0 1:ℝ) (entry i 1 0:ℝ) (entry i 1 1:ℝ)
    (center i) hC (by rw [hdet]; norm_num) (denominator_ne_zero i) 1
    (by
      simp only [hdet,Complex.ofReal_one,one_pow,mul_one,Complex.ofReal_intCast]
      simpa only [entry] using hF)
  obtain ⟨B,error,h⟩ := he
  refine ⟨B,error,fun M => ⟨(h M).1,?_⟩⟩
  intro s hs
  have he := (h M).2 s hs
  simp only [hdet,div_one,one_mul,partner_identity] at he
  simpa only [rate,derivativeRate,gridVector_index,grid,original,center,
    Nat.cast_ofNat] using he

def coefficient (m : ℕ) (i : Fin 516) (n : ℕ) (s : ℂ) : ℂ :=
  (rate i:ℂ)^(s-(m:ℂ))*(I*(derivativeRate i:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

theorem coefficient_analytic (m : ℕ) (i : Fin 516) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (coefficient m i n) z := by
  have hc : (rate i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (rate_pos i).ne'
  have hp : AnalyticAt ℂ (fun s : ℂ => (rate i:ℂ)^(s-(m:ℂ))) z := by
    simp_rw [Complex.cpow_def_of_ne_zero hc]
    fun_prop
  exact (hp.mul analyticAt_const).mul (SmallLevelTaylor.binomial_shift_analytic (2*m) n z)

/-- Common half-plane for the full finite family, with the leading term
separated from all positive shifts. -/
theorem original_group_system {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ (B : ℝ) (error : Fin 516→ℕ→ℂ→ℂ), ∀ i : Fin 516, ∀ M : ℕ,
      AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector (2*m) f s (gridIndex (source i))-
          coefficient m i 0 s*gridVector (2*m) f s (gridIndex (partner i))=
        error i M s+∑ n∈Finset.range M, coefficient m i (n+1) s*
          gridVector (2*m) f (s+((n:ℂ)+1)) (gridIndex (partner i)) := by
  choose b err h using original_group_rows hf
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 516) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,fun i M => err i (M+1),?_⟩
  intro i M
  constructor
  · intro s hs
    apply (h i (M+1)).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M+1:ℕ):ℝ)<s.re
    push_cast
    linarith [hbB i]
  · intro s hs
    have he := (h i (M+1)).2 s (lt_of_le_of_lt (hbB i) hs)
    rw [Finset.sum_range_succ'] at he
    simp only [Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one,
      Nat.cast_add,Nat.cast_one] at he
    simp only [coefficient,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,
      mul_one,Nat.cast_add,Nat.cast_one]
    rw [mul_add,Finset.mul_sum] at he
    simp only [mul_assoc,one_mul] at he ⊢
    linear_combination he

#print axioms original_group_rows
#print axioms original_group_system
end QuantitativeArithmeticSmallLevelNineteenFullGroup
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenFullGroupLaurentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16384
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullGroup
open Complex
open QuantitativeArithmeticSmallLevelNineteenGridSystem
  (threePrimeMonomial primeParameter real_three_prime_power)

def rateIndex : Fin 516 → Fin 9 :=
  ![7,8,7,6,5,8,7,6,5,4,3,2,1,0,0,1,2,3,7,4,1,1,2,2,4,6,1,1,4,7,3,2,1,0,0,1,2,3,4,5,6,7,8,5,6,7,8,7,6,7,2,1,6,6,4,2,2,4,6,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,6,4,2,2,4,6,8,7,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,4,1,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,4,6,7,8,4,2,6,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,4,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,6,7,8,4,0,8,7,1,4,6,2,4,4,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,4,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,4,1,7,8,7,6,5,8,7,6,5,4,3,2,1,0,0,1,2,3,4,3,2,1,0,0,1,2,3,4,5,6,7,8,5,6,7,8,8,7,6,5,8,7,6,5,4,3,2,1,0,0,1,2,3,4,3,2,1,0,0,1,2,3,4,5,6,7,8,5,6,7,8,4,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,4,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,7,4,4,7,4,4,4,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,6,4,2,2,4,6,6,6,7,8,6,4,2,2,4,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,6,7,8,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,7,1,1,4,7,3,2,1,0,0,1,2,3,4,5,6,7,8,1,1,4,7,7,5,6,7,8,7,4,1,1,7,3,2,1,0,0,1,2,3,4,5,6,7,8,1,1,4,7,7,5,6,7,8,8,7,6,5,4,3,2,1,0,0,1,2,3,4,5,6,7,8,2,6,6,7,8,6,4,2,2,4,6,6,4,2,2,4,6,4,4,1,6,4,4,4,4,4,4,4,4,4,4,4]
def rateNum : Fin 9 → ℕ := ![1,1,1,4,1,9,4,9,36]
def rateDen : Fin 9 → ℕ := ![36,9,4,9,1,4,1,1,1]
def ratePowers : Fin 9 → ℤ×ℤ×ℤ := ![(-2,-2,0),(0,-2,0),(-2,0,0),(2,-2,0),(0,0,0),(-2,2,0),(2,0,0),(0,2,0),(2,2,0)]
def powers (i : Fin 516) : ℤ×ℤ×ℤ := ratePowers (rateIndex i)

theorem integer_rate (i : Fin 516) :
    (entry i 1 0*source i+114*entry i 1 1)^2*(rateDen (rateIndex i):ℤ)=
      114^2*(rateNum (rateIndex i):ℤ) := by
  revert i
  decide

theorem rateDen_pos (j : Fin 9) : 0<rateDen j := by revert j; decide

theorem rate_value (j : Fin 9) :
    (rateNum j:ℝ)/(rateDen j:ℝ)=
      (2:ℝ)^(ratePowers j).1*(3:ℝ)^(ratePowers j).2.1*(19:ℝ)^(ratePowers j).2.2 := by
  fin_cases j <;> norm_num [rateNum,rateDen,ratePowers]

theorem rate_certificate (i : Fin 516) :
    rate i=(2:ℝ)^(powers i).1*(3:ℝ)^(powers i).2.1*(19:ℝ)^(powers i).2.2 := by
  have he : ((entry i 1 0:ℝ)*(source i:ℝ)+114*(entry i 1 1:ℝ))^2*
      (rateDen (rateIndex i):ℝ)=114^2*(rateNum (rateIndex i):ℝ) := by
    exact_mod_cast integer_rate i
  have hd : (rateDen (rateIndex i):ℝ)≠0 := by
    exact_mod_cast (rateDen_pos (rateIndex i)).ne'
  change rate i=(2:ℝ)^(ratePowers (rateIndex i)).1*
    (3:ℝ)^(ratePowers (rateIndex i)).2.1*(19:ℝ)^(ratePowers (rateIndex i)).2.2
  rw [← rate_value]
  apply (eq_div_iff hd).2
  unfold rate center
  linear_combination (1/12996:ℝ)*he

def symbolic (X Y Z : ℂ) (i : Fin 516) : ℂ := threePrimeMonomial (powers i) X Y Z

theorem coefficient_laurent (m : ℕ) (s : ℂ) (i : Fin 516) :
    coefficient m i 0 s=symbolic
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 19 m s) i := by
  simp only [coefficient,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one]
  rw [real_three_prime_power _ _ (rate_certificate i)]
  rfl

theorem primeParameter_shift {p : ℕ} (hp : p≠0) (m : ℕ) (s : ℂ) :
    primeParameter p m (s-1)=primeParameter p m s/(p:ℂ) := by
  unfold primeParameter
  rw [show s-1-(m:ℂ)=(s-(m:ℂ))-1 by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one]

theorem first_coefficient (m : ℕ) (s : ℂ) (i : Fin 516) :
    coefficient m i 1 (s-1)=I*(s-((2*m:ℕ):ℂ))*(derivativeRate i:ℂ)*
      symbolic (primeParameter 2 m s/2) (primeParameter 3 m s/3)
        (primeParameter 19 m s/19) i := by
  have h0 := coefficient_laurent m (s-1) i
  simp only [primeParameter_shift (by decide : 2≠0),
    primeParameter_shift (by decide : 3≠0),primeParameter_shift (by decide : 19≠0)] at h0
  norm_num only [Nat.cast_ofNat] at h0
  simp only [coefficient,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one] at h0
  simp only [coefficient,Nat.cast_one,pow_one,Ring.choose_one_right,sub_add_cancel]
  rw [h0]
  ring

#print axioms rate_certificate
#print axioms coefficient_laurent
#print axioms first_coefficient
end QuantitativeArithmeticSmallLevelNineteenFullGroup
end
end
