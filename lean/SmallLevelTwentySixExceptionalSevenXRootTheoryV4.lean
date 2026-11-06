module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FinCases
public import QuantitativeArithmeticComplexHornerBoundsTheoryV4
public import SmallLevelTwentySixExceptionalCurveV1

/-! Consolidated chapter: SmallLevelTwentySixExceptionalSevenXRoot. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixExceptionalSevenXRootDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace SmallLevelTwentySixExceptionalSevenXRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def pCoefficient : ℕ→ℚ := fun j => match j with
  | 0 => (17472/25)
  | 1 => (-92336/125)
  | 2 => (1912/25)
  | 3 => (7738/25)
  | 4 => (-1047/5)
  | 5 => (361/5)
  | 6 => (-13/1)
  | 7 => (1/1)
  | _ => 0
def centerQ : Fin 7→ℚ×ℚ := ![((-134261111671114367698493238527/100000000000000000000000000000),(0/1)),((132864592279672520188890209741/100000000000000000000000000000),(-157628457575128056495733054987/200000000000000000000000000000)),((132864592279672520188890209741/100000000000000000000000000000),(394071143937820141239332637467/500000000000000000000000000000)),((274260248001336092283006361517/62500000000000000000000000000),(-968573764805491711871169456797/500000000000000000000000000000)),((274260248001336092283006361517/62500000000000000000000000000),(1937147529610983423742338913593/1000000000000000000000000000000)),((181811958442183645009432788869/125000000000000000000000000000),(-2713749091797754585912043305591/1000000000000000000000000000000)),((181811958442183645009432788869/125000000000000000000000000000),(271374909179775458591204330559/100000000000000000000000000000))]
def radiusQ : ℚ := (1/100000000000000000000)
def pRoot : ℂ[X] := hornerPolynomial (fun j => (pCoefficient j:ℂ)) 8 0

theorem pRoot_monic : pRoot.Monic := by
  norm_num [pRoot,hornerPolynomial,pCoefficient]
  monicity!

theorem pRoot_degree : pRoot.degree=(7:WithBot ℕ) := by
  norm_num [pRoot,hornerPolynomial,pCoefficient]
  compute_degree!

#print axioms pRoot_monic
#print axioms pRoot_degree

end SmallLevelTwentySixExceptionalSevenXRoot
end
end

/-! ## SmallLevelTwentySixExceptionalSevenXRootNodeBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixExceptionalSevenXRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def node0Center : ℚ×ℚ := ((-134261111671114367698493238527/100000000000000000000000000000),(0/1))
def node0R : ℚ := (2/1)
def node0Bound : ℚ := (18324914319606424401/100000000000000000000000000000000000000)
def node0State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-2409748968240582164929718576508577/1000000000000000000000000000000000000000000000000000000000000),(0/1))
  | 1 => ((260268960721841196395414701611054383288828383695531213851145553/500000000000000000000000000000000000000000000000000000000000),(0/1))
  | 2 => ((-234473315796810654625262458045545450441883064219220033236081229/250000000000000000000000000000000000000000000000000000000000),(0/1))
  | 3 => ((755522764977582221484504016700163953364984870099067335406929623/1000000000000000000000000000000000000000000000000000000000000),(0/1))
  | 4 => ((-332190579555239576371744593400873458132932397724936680033432353/1000000000000000000000000000000000000000000000000000000000000),(0/1))
  | 5 => ((914565491279612120688960135077694431737548039085936517129729/10000000000000000000000000000000000000000000000000000000000),(0/1))
  | 6 => ((-1434261111671114367698493238527/100000000000000000000000000000),(0/1))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node0Error : ℕ→ℚ := fun j => match j with
  | 0 => (792552442993475524479366657383/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1 => (385252783960218766251595488907/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 2 => (370344079452250773070306869541/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 3 => (152493722118035609918574027431/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 4 => (508004090572781580200130817/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 5 => (0/1)
  | 6 => (0/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node0Distance : Fin 7→ℚ := ![(1/1),(2671/1000),(2671/1000),(573/100),(573/100),(2797/1000),(2797/1000)]
theorem node0_norm : |node0Center.1|+|node0Center.2|≤node0R := by decide +kernel
theorem node0_error_nonneg : ∀ j : Fin 9,0≤node0Error j.val := by decide +kernel
theorem node0_terminal : |(node0State 8).1|+|(node0State 8).2|≤node0Error 8 := by decide +kernel
theorem node0_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node0Center (node0State (j.val+1)) (node0State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node0Center (node0State (j.val+1)) (node0State j.val)).2|+
    node0R*node0Error (j.val+1)≤node0Error j.val := by decide +kernel
theorem node0_final : |(node0State 0).1|+|(node0State 0).2|+node0Error 0≤node0Bound := by decide +kernel

theorem node0_bound : ‖pRoot.eval (ratComplex (centerQ 0))‖≤(node0Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node0Center
    node0State node0Error node0R node0Bound 8
    node0_norm (fun j hj => node0_error_nonneg ⟨j,by omega⟩)
    node0_terminal (fun j hj => node0_steps ⟨j,hj⟩) node0_final

theorem node0_distance_positive : ∀ j : Fin 7,0<node0Distance j := by decide +kernel
theorem node0_distance_diagonal : node0Distance 0=1  := by decide +kernel
theorem node0_distance_lower : ∀ j : Fin 7,(0:Fin 7)≠j →
    node0Distance j≤max |(centerQ 0).1-(centerQ j).1| |(centerQ 0).2-(centerQ j).2| := by decide +kernel
theorem node0_bound_product : node0Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node0Distance j := by decide +kernel

#print axioms node0_bound
#print axioms node0_distance_lower



def node1Center : ℚ×ℚ := ((132864592279672520188890209741/100000000000000000000000000000),(-157628457575128056495733054987/200000000000000000000000000000))
def node1R : ℚ := (3/1)
def node1Bound : ℚ := (1327339149842047419/50000000000000000000000000000000000000)
def node1State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-36656317345391946917772735002949/125000000000000000000000000000000000000000000000000000000000),(123644396707815318031891261319707/1000000000000000000000000000000000000000000000000000000000000))
  | 1 => ((-38909550165941818434181164955315008609842823294941451490655707/100000000000000000000000000000000000000000000000000000000000),(-230808384399709903465359630404121150498632006735234100214399229/1000000000000000000000000000000000000000000000000000000000000))
  | 2 => ((135429100008157516773491889420545272647016481770253455188996919/500000000000000000000000000000000000000000000000000000000000),(-32615128401717750756421585090238100203850165761097880012393/2500000000000000000000000000000000000000000000000000000000))
  | 3 => ((112526930638104756986391891928370029561560119338159412307082797/1000000000000000000000000000000000000000000000000000000000000),(2846551511663537058909774110475524205233373066906267967390027/50000000000000000000000000000000000000000000000000000000000))
  | 4 => ((-25695191236592104916719264069649748727377181170529582956332021/200000000000000000000000000000000000000000000000000000000000),(-16681006974557184680304730108009803806262465650576360380562643/500000000000000000000000000000000000000000000000000000000000))
  | 5 => ((448573877806952681612454466058145378085698018310650383915631/8000000000000000000000000000000000000000000000000000000000),(81515256676440190164644338354408388104074428531958883971633/10000000000000000000000000000000000000000000000000000000000))
  | 6 => ((-1167135407720327479811109790259/100000000000000000000000000000),(-157628457575128056495733054987/200000000000000000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node1Error : ℕ→ℚ := fun j => match j with
  | 0 => (7264033557587621184810943939209/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1 => (9602548288191281298792949923629/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 2 => (3176816583101607769007779222873/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 3 => (513450182955696268633930286183/100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 4 => (9819800653138999413387558233/8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 5 => (0/1)
  | 6 => (0/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node1Distance : Fin 7→ℚ := ![(2671/1000),(1/1),(197/125),(3059/1000),(3059/1000),(77/40),(3501/1000)]
theorem node1_norm : |node1Center.1|+|node1Center.2|≤node1R := by decide +kernel
theorem node1_error_nonneg : ∀ j : Fin 9,0≤node1Error j.val := by decide +kernel
theorem node1_terminal : |(node1State 8).1|+|(node1State 8).2|≤node1Error 8 := by decide +kernel
theorem node1_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node1Center (node1State (j.val+1)) (node1State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node1Center (node1State (j.val+1)) (node1State j.val)).2|+
    node1R*node1Error (j.val+1)≤node1Error j.val := by decide +kernel
theorem node1_final : |(node1State 0).1|+|(node1State 0).2|+node1Error 0≤node1Bound := by decide +kernel

theorem node1_bound : ‖pRoot.eval (ratComplex (centerQ 1))‖≤(node1Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node1Center
    node1State node1Error node1R node1Bound 8
    node1_norm (fun j hj => node1_error_nonneg ⟨j,by omega⟩)
    node1_terminal (fun j hj => node1_steps ⟨j,hj⟩) node1_final

theorem node1_distance_positive : ∀ j : Fin 7,0<node1Distance j := by decide +kernel
theorem node1_distance_diagonal : node1Distance 1=1  := by decide +kernel
theorem node1_distance_lower : ∀ j : Fin 7,(1:Fin 7)≠j →
    node1Distance j≤max |(centerQ 1).1-(centerQ j).1| |(centerQ 1).2-(centerQ j).2| := by decide +kernel
theorem node1_bound_product : node1Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node1Distance j := by decide +kernel

#print axioms node1_bound
#print axioms node1_distance_lower



def node2Center : ℚ×ℚ := ((132864592279672520188890209741/100000000000000000000000000000),(394071143937820141239332637467/500000000000000000000000000000))
def node2R : ℚ := (3/1)
def node2Bound : ℚ := (1327339149842047419/50000000000000000000000000000000000000)
def node2State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((50911413565594738031843175286469/500000000000000000000000000000000000000000000000000000000000),(-83812756860586115030474268453581/500000000000000000000000000000000000000000000000000000000000))
  | 1 => ((-194547750829709092170905824776600829270952776997682147345743547/500000000000000000000000000000000000000000000000000000000000),(230808384399709903465359630403825789493607298136271674005372683/1000000000000000000000000000000000000000000000000000000000000))
  | 2 => ((2708582000163150335469837788410464773302870847871541303309871/10000000000000000000000000000000000000000000000000000000000),(3261512840171775075642158509025734728199340156559472886749521/250000000000000000000000000000000000000000000000000000000000))
  | 3 => ((112526930638104756986391891928416896083958945319336787673849519/1000000000000000000000000000000000000000000000000000000000000),(-28465515116635370589097741104723898760536358393688839782674151/500000000000000000000000000000000000000000000000000000000000))
  | 4 => ((-16059494522870065572949540043532869045518306823253135679324033/125000000000000000000000000000000000000000000000000000000000),(8340503487278592340152365053994630002837741654480873652271787/250000000000000000000000000000000000000000000000000000000000))
  | 5 => ((1752241710183408912548650258039679642040250111543632978750117/31250000000000000000000000000000000000000000000000000000000),(-203788141691100475411610845885762402556325907589991655033953/25000000000000000000000000000000000000000000000000000000000))
  | 6 => ((-1167135407720327479811109790259/100000000000000000000000000000),(394071143937820141239332637467/500000000000000000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node2Error : ℕ→ℚ := fun j => match j with
  | 0 => (4390589059239450700930315329057/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1 => (904228626315745304163204002983/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 2 => (586023657566802089664148899939/62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 3 => (34155204209121052771054025551/12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 4 => (26911373296420234834305654713/31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 5 => (0/1)
  | 6 => (0/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node2Distance : Fin 7→ℚ := ![(2671/1000),(197/125),(1/1),(3059/1000),(3059/1000),(3501/1000),(77/40)]
theorem node2_norm : |node2Center.1|+|node2Center.2|≤node2R := by decide +kernel
theorem node2_error_nonneg : ∀ j : Fin 9,0≤node2Error j.val := by decide +kernel
theorem node2_terminal : |(node2State 8).1|+|(node2State 8).2|≤node2Error 8 := by decide +kernel
theorem node2_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node2Center (node2State (j.val+1)) (node2State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node2Center (node2State (j.val+1)) (node2State j.val)).2|+
    node2R*node2Error (j.val+1)≤node2Error j.val := by decide +kernel
theorem node2_final : |(node2State 0).1|+|(node2State 0).2|+node2Error 0≤node2Bound := by decide +kernel

theorem node2_bound : ‖pRoot.eval (ratComplex (centerQ 2))‖≤(node2Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node2Center
    node2State node2Error node2R node2Bound 8
    node2_norm (fun j hj => node2_error_nonneg ⟨j,by omega⟩)
    node2_terminal (fun j hj => node2_steps ⟨j,hj⟩) node2_final

theorem node2_distance_positive : ∀ j : Fin 7,0<node2Distance j := by decide +kernel
theorem node2_distance_diagonal : node2Distance 2=1  := by decide +kernel
theorem node2_distance_lower : ∀ j : Fin 7,(2:Fin 7)≠j →
    node2Distance j≤max |(centerQ 2).1-(centerQ j).1| |(centerQ 2).2-(centerQ j).2| := by decide +kernel
theorem node2_bound_product : node2Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node2Distance j := by decide +kernel

#print axioms node2_bound
#print axioms node2_distance_lower

def node3Center : ℚ×ℚ := ((274260248001336092283006361517/62500000000000000000000000000),(-968573764805491711871169456797/500000000000000000000000000000))
def node3R : ℚ := (7/1)
def node3Bound : ℚ := (2832945425084035989/10000000000000000000000000000000000000)
def node3State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((382196046257076004944465267438543/500000000000000000000000000000000000000000000000000000000000),(286022530371114631144973742150497/1000000000000000000000000000000000000000000000000000000000000))
  | 1 => ((-26657947223291086140617448428962284686910976110100772470635559/200000000000000000000000000000000000000000000000000000000000),(-29420263796217567769536067603841414887859575266177105577828083/500000000000000000000000000000000000000000000000000000000000))
  | 2 => ((6020746231524297911023989274186913390467555540155363232193423/50000000000000000000000000000000000000000000000000000000000),(7949609333420140169323485228805312724447068240607243619823991/200000000000000000000000000000000000000000000000000000000000))
  | 3 => ((1006547182243845375212973641470395345458548258499441814860899/200000000000000000000000000000000000000000000000000000000000),(11279705809858738655617726764773986805567515548639024220528783/1000000000000000000000000000000000000000000000000000000000000))
  | 4 => ((-59021192368009685944633102534444666559983508152488168408787651/1000000000000000000000000000000000000000000000000000000000000),(-23484320989717360029542084132674287158048990125578022993026931/1000000000000000000000000000000000000000000000000000000000000))
  | 5 => ((7664327718621319418272933379234568719099490360583837457143287/250000000000000000000000000000000000000000000000000000000000),(127841811009089075355252076481888651205369798856139705118951/15625000000000000000000000000000000000000000000000000000000))
  | 6 => ((-538239751998663907716993638483/62500000000000000000000000000),(-968573764805491711871169456797/500000000000000000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node3Error : ℕ→ℚ := fun j => match j with
  | 0 => (209397807805380681350197312020013/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1 => (59741714819945022090940740015487/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 2 => (2112956372599181482979110901769/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 3 => (282887773404867030215666936419/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 4 => (38047878132928072983003287821/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 5 => (0/1)
  | 6 => (0/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node3Distance : Fin 7→ℚ := ![(573/100),(3059/1000),(3059/1000),(1/1),(1937/500),(2933/1000),(93/20)]
theorem node3_norm : |node3Center.1|+|node3Center.2|≤node3R := by decide +kernel
theorem node3_error_nonneg : ∀ j : Fin 9,0≤node3Error j.val := by decide +kernel
theorem node3_terminal : |(node3State 8).1|+|(node3State 8).2|≤node3Error 8 := by decide +kernel
theorem node3_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node3Center (node3State (j.val+1)) (node3State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node3Center (node3State (j.val+1)) (node3State j.val)).2|+
    node3R*node3Error (j.val+1)≤node3Error j.val := by decide +kernel
theorem node3_final : |(node3State 0).1|+|(node3State 0).2|+node3Error 0≤node3Bound := by decide +kernel

theorem node3_bound : ‖pRoot.eval (ratComplex (centerQ 3))‖≤(node3Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node3Center
    node3State node3Error node3R node3Bound 8
    node3_norm (fun j hj => node3_error_nonneg ⟨j,by omega⟩)
    node3_terminal (fun j hj => node3_steps ⟨j,hj⟩) node3_final

theorem node3_distance_positive : ∀ j : Fin 7,0<node3Distance j := by decide +kernel
theorem node3_distance_diagonal : node3Distance 3=1  := by decide +kernel
theorem node3_distance_lower : ∀ j : Fin 7,(3:Fin 7)≠j →
    node3Distance j≤max |(centerQ 3).1-(centerQ j).1| |(centerQ 3).2-(centerQ j).2| := by decide +kernel
theorem node3_bound_product : node3Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node3Distance j := by decide +kernel

#print axioms node3_bound
#print axioms node3_distance_lower



def node4Center : ℚ×ℚ := ((274260248001336092283006361517/62500000000000000000000000000),(1937147529610983423742338913593/1000000000000000000000000000000))
def node4R : ℚ := (7/1)
def node4Bound : ℚ := (2832945425084035989/10000000000000000000000000000000000000)
def node4State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-1077663649464717824762921897280949/500000000000000000000000000000000000000000000000000000000000),(4061659949112423319776397418799971/1000000000000000000000000000000000000000000000000000000000000))
  | 1 => ((-1041326063409808052367869079258005241232575111519258053789523/7812500000000000000000000000000000000000000000000000000000),(3677532974527195971192008450546085469555830712079242054144697/62500000000000000000000000000000000000000000000000000000000))
  | 2 => ((120414924630485958220479785483804100492693776194157092220344171/1000000000000000000000000000000000000000000000000000000000000),(-19874023333550350423308713071893935194909525099586866454248963/500000000000000000000000000000000000000000000000000000000000))
  | 3 => ((2516367955609613438032434103693601726860239407071934610238339/500000000000000000000000000000000000000000000000000000000000),(-5639852904929369327808863382366997955538555650266637825002161/500000000000000000000000000000000000000000000000000000000000))
  | 4 => ((-14755298092002421486158275633611007317453077617611931600398863/250000000000000000000000000000000000000000000000000000000000),(11742160494858680014771042066334834546920628192681941234640287/500000000000000000000000000000000000000000000000000000000000))
  | 5 => ((6131462174897055534618346703388429834291436681836566901280067/200000000000000000000000000000000000000000000000000000000000),(-255683622018178150710504152963645312658740933804562416599419/31250000000000000000000000000000000000000000000000000000000))
  | 6 => ((-538239751998663907716993638483/62500000000000000000000000000),(1937147529610983423742338913593/1000000000000000000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node4Error : ℕ→ℚ := fun j => match j with
  | 0 => (174285524932559930418562408840153/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1 => (24870365874546533774251429579421/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 2 => (28224174137071745306917627064601/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 3 => (3913978040888508778614975320967/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 4 => (356909925754339017577876648743/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 5 => (0/1)
  | 6 => (0/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node4Distance : Fin 7→ℚ := ![(573/100),(3059/1000),(3059/1000),(1937/500),(1/1),(93/20),(2933/1000)]
theorem node4_norm : |node4Center.1|+|node4Center.2|≤node4R := by decide +kernel
theorem node4_error_nonneg : ∀ j : Fin 9,0≤node4Error j.val := by decide +kernel
theorem node4_terminal : |(node4State 8).1|+|(node4State 8).2|≤node4Error 8 := by decide +kernel
theorem node4_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node4Center (node4State (j.val+1)) (node4State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node4Center (node4State (j.val+1)) (node4State j.val)).2|+
    node4R*node4Error (j.val+1)≤node4Error j.val := by decide +kernel
theorem node4_final : |(node4State 0).1|+|(node4State 0).2|+node4Error 0≤node4Bound := by decide +kernel

theorem node4_bound : ‖pRoot.eval (ratComplex (centerQ 4))‖≤(node4Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node4Center
    node4State node4Error node4R node4Bound 8
    node4_norm (fun j hj => node4_error_nonneg ⟨j,by omega⟩)
    node4_terminal (fun j hj => node4_steps ⟨j,hj⟩) node4_final

theorem node4_distance_positive : ∀ j : Fin 7,0<node4Distance j := by decide +kernel
theorem node4_distance_diagonal : node4Distance 4=1  := by decide +kernel
theorem node4_distance_lower : ∀ j : Fin 7,(4:Fin 7)≠j →
    node4Distance j≤max |(centerQ 4).1-(centerQ j).1| |(centerQ 4).2-(centerQ j).2| := by decide +kernel
theorem node4_bound_product : node4Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node4Distance j := by decide +kernel

#print axioms node4_bound
#print axioms node4_distance_lower



def node5Center : ℚ×ℚ := ((181811958442183645009432788869/125000000000000000000000000000),(-2713749091797754585912043305591/1000000000000000000000000000000))
def node5R : ℚ := (5/1)
def node5Bound : ℚ := (1116169460001966447/8000000000000000000000000000000000000)
def node5State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((1547516945876196937880657568855861/1000000000000000000000000000000000000000000000000000000000000),(7267075746872011113784011834899/20000000000000000000000000000000000000000000000000000000000))
  | 1 => ((-107227722945967581350515809912079164968026807125449236958584263/1000000000000000000000000000000000000000000000000000000000000),(-200061878666726673605386455090876451681586248149810120527483433/1000000000000000000000000000000000000000000000000000000000000))
  | 2 => ((154153506946820317483061351765752357470573405331611924029931667/1000000000000000000000000000000000000000000000000000000000000),(240107485423800122005315706538988200752146277967910941776853/1600000000000000000000000000000000000000000000000000000000))
  | 3 => ((-7760262259528773651177192121436164327302367197464138804181581/250000000000000000000000000000000000000000000000000000000000),(4525937149451484636979515902915686923123284285209098026988481/100000000000000000000000000000000000000000000000000000000000))
  | 4 => ((-16301890417852500321474570104220812331272034059028697382748721/250000000000000000000000000000000000000000000000000000000000),(-4527259609944058646261538715424962021669710704058482457955561/50000000000000000000000000000000000000000000000000000000000))
  | 5 => ((48042679835665031090903451471915085600830379280270858127287023/1000000000000000000000000000000000000000000000000000000000000),(1711529099985228634733218428781973765900737914498975249733421/62500000000000000000000000000000000000000000000000000000000))
  | 6 => ((-1443188041557816354990567211131/125000000000000000000000000000),(-2713749091797754585912043305591/1000000000000000000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node5Error : ℕ→ℚ := fun j => match j with
  | 0 => (475552198423138991445845726795273/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1 => (95016825563735359780347355452267/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 2 => (18891010965399161199195273859721/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 3 => (3633758713131167013803851854171/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 4 => (511322281075389899247984067951/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 5 => (0/1)
  | 6 => (0/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node5Distance : Fin 7→ℚ := ![(2797/1000),(77/40),(3501/1000),(2933/1000),(93/20),(1/1),(5427/1000)]
theorem node5_norm : |node5Center.1|+|node5Center.2|≤node5R := by decide +kernel
theorem node5_error_nonneg : ∀ j : Fin 9,0≤node5Error j.val := by decide +kernel
theorem node5_terminal : |(node5State 8).1|+|(node5State 8).2|≤node5Error 8 := by decide +kernel
theorem node5_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node5Center (node5State (j.val+1)) (node5State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node5Center (node5State (j.val+1)) (node5State j.val)).2|+
    node5R*node5Error (j.val+1)≤node5Error j.val := by decide +kernel
theorem node5_final : |(node5State 0).1|+|(node5State 0).2|+node5Error 0≤node5Bound := by decide +kernel

theorem node5_bound : ‖pRoot.eval (ratComplex (centerQ 5))‖≤(node5Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node5Center
    node5State node5Error node5R node5Bound 8
    node5_norm (fun j hj => node5_error_nonneg ⟨j,by omega⟩)
    node5_terminal (fun j hj => node5_steps ⟨j,hj⟩) node5_final

theorem node5_distance_positive : ∀ j : Fin 7,0<node5Distance j := by decide +kernel
theorem node5_distance_diagonal : node5Distance 5=1  := by decide +kernel
theorem node5_distance_lower : ∀ j : Fin 7,(5:Fin 7)≠j →
    node5Distance j≤max |(centerQ 5).1-(centerQ j).1| |(centerQ 5).2-(centerQ j).2| := by decide +kernel
theorem node5_bound_product : node5Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node5Distance j := by decide +kernel

#print axioms node5_bound
#print axioms node5_distance_lower

def node6Center : ℚ×ℚ := ((181811958442183645009432788869/125000000000000000000000000000),(271374909179775458591204330559/100000000000000000000000000000))
def node6R : ℚ := (5/1)
def node6Bound : ℚ := (1116169460001966447/8000000000000000000000000000000000000)
def node6State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-425433501319797946969095884707643/1000000000000000000000000000000000000000000000000000000000000),(48995591465601873840243145651503/50000000000000000000000000000000000000000000000000000000000))
  | 1 => ((-26806930736491895337628952478014684178031827711791892970618489/250000000000000000000000000000000000000000000000000000000000),(100030939333363336802693227545844071234205059738766192581010883/500000000000000000000000000000000000000000000000000000000000))
  | 2 => ((154153506946820317483061351766054999499394999250267526734300127/1000000000000000000000000000000000000000000000000000000000000),(-150067178389875076253322316586768244106404730215145051374616923/1000000000000000000000000000000000000000000000000000000000000))
  | 3 => ((-31041049038115094604708768485671716365552646891366705287361421/1000000000000000000000000000000000000000000000000000000000000),(-707177679601794474528049359831968350247379218632296693596899/15625000000000000000000000000000000000000000000000000000000))
  | 4 => ((-65207561671410001285898280416930123983694056400965127452603727/1000000000000000000000000000000000000000000000000000000000000),(9054519219888117292523077430848060395020923188881595779465309/100000000000000000000000000000000000000000000000000000000000))
  | 5 => ((12010669958916257772725862867980128274753493697360670553474551/250000000000000000000000000000000000000000000000000000000000),(-171152909998522863473321842878134307785918009814398468252229/6250000000000000000000000000000000000000000000000000000000))
  | 6 => ((-1443188041557816354990567211131/125000000000000000000000000000),(271374909179775458591204330559/100000000000000000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node6Error : ℕ→ℚ := fun j => match j with
  | 0 => (25138573483011731050204537702279/50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1 => (12541155008848283975083951927911/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 2 => (4947735572834374588067502223179/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 3 => (1837219619450717904915484375493/500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 4 => (61096382416861230978391773361/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 5 => (0/1)
  | 6 => (0/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node6Distance : Fin 7→ℚ := ![(2797/1000),(3501/1000),(77/40),(93/20),(2933/1000),(5427/1000),(1/1)]
theorem node6_norm : |node6Center.1|+|node6Center.2|≤node6R := by decide +kernel
theorem node6_error_nonneg : ∀ j : Fin 9,0≤node6Error j.val := by decide +kernel
theorem node6_terminal : |(node6State 8).1|+|(node6State 8).2|≤node6Error 8 := by decide +kernel
theorem node6_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node6Center (node6State (j.val+1)) (node6State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node6Center (node6State (j.val+1)) (node6State j.val)).2|+
    node6R*node6Error (j.val+1)≤node6Error j.val := by decide +kernel
theorem node6_final : |(node6State 0).1|+|(node6State 0).2|+node6Error 0≤node6Bound := by decide +kernel

theorem node6_bound : ‖pRoot.eval (ratComplex (centerQ 6))‖≤(node6Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node6Center
    node6State node6Error node6R node6Bound 8
    node6_norm (fun j hj => node6_error_nonneg ⟨j,by omega⟩)
    node6_terminal (fun j hj => node6_steps ⟨j,hj⟩) node6_final

theorem node6_distance_positive : ∀ j : Fin 7,0<node6Distance j := by decide +kernel
theorem node6_distance_diagonal : node6Distance 6=1  := by decide +kernel
theorem node6_distance_lower : ∀ j : Fin 7,(6:Fin 7)≠j →
    node6Distance j≤max |(centerQ 6).1-(centerQ j).1| |(centerQ 6).2-(centerQ j).2| := by decide +kernel
theorem node6_bound_product : node6Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node6Distance j := by decide +kernel

#print axioms node6_bound
#print axioms node6_distance_lower

end SmallLevelTwentySixExceptionalSevenXRoot
end
end

/-! ## SmallLevelTwentySixExceptionalSevenXRootTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentySixExceptionalSevenXRoot. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixExceptionalSevenXRootGeometryV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace SmallLevelTwentySixExceptionalSevenXRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def distanceQ (i : Fin 7) : Fin 7→ℚ :=
  ![node0Distance,node1Distance,node2Distance,node3Distance,node4Distance,node5Distance,node6Distance] i
def pBoundQ : Fin 7→ℚ := ![node0Bound,node1Bound,node2Bound,node3Bound,node4Bound,node5Bound,node6Bound]
theorem distance_positive (i : Fin 7) : ∀ j : Fin 7,0<distanceQ i j := by
  fin_cases i
  · exact node0_distance_positive
  · exact node1_distance_positive
  · exact node2_distance_positive
  · exact node3_distance_positive
  · exact node4_distance_positive
  · exact node5_distance_positive
  · exact node6_distance_positive

theorem distance_diagonal (i : Fin 7) : distanceQ i i=1 := by
  fin_cases i
  · exact node0_distance_diagonal
  · exact node1_distance_diagonal
  · exact node2_distance_diagonal
  · exact node3_distance_diagonal
  · exact node4_distance_diagonal
  · exact node5_distance_diagonal
  · exact node6_distance_diagonal

theorem distance_lower (i : Fin 7) : ∀ j : Fin 7,i≠j → distanceQ i j≤max |(centerQ i).1-(centerQ j).1| |(centerQ i).2-(centerQ j).2| := by
  fin_cases i
  · exact node0_distance_lower
  · exact node1_distance_lower
  · exact node2_distance_lower
  · exact node3_distance_lower
  · exact node4_distance_lower
  · exact node5_distance_lower
  · exact node6_distance_lower

theorem bound_product (i : Fin 7) : pBoundQ i=(1/100:ℚ)*radiusQ*∏ j : Fin 7,distanceQ i j := by
  fin_cases i
  · exact node0_bound_product
  · exact node1_bound_product
  · exact node2_bound_product
  · exact node3_bound_product
  · exact node4_bound_product
  · exact node5_bound_product
  · exact node6_bound_product

theorem all_P_value_bounds (i : Fin 7) : ‖pRoot.eval (ratComplex (centerQ i))‖≤(pBoundQ i:ℝ) := by
  fin_cases i
  · exact node0_bound
  · exact node1_bound
  · exact node2_bound
  · exact node3_bound
  · exact node4_bound
  · exact node5_bound
  · exact node6_bound


end SmallLevelTwentySixExceptionalSevenXRoot
end
end

/-! ## SmallLevelTwentySixExceptionalSevenXRootCoverV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixExceptionalSevenXRoot
open QuantitativeArithmeticComplexHornerBounds Polynomial Finset

theorem distance_le_norm (i j : Fin 7) (hij : i≠j) :
    (distanceQ i j:ℝ)≤‖ratComplex (centerQ i)-ratComplex (centerQ j)‖ := by
  have h : (distanceQ i j:ℝ)≤max |((centerQ i).1:ℝ)-((centerQ j).1:ℝ)|
      |((centerQ i).2:ℝ)-((centerQ j).2:ℝ)| := by
    exact_mod_cast distance_lower i j hij
  apply h.trans
  apply max_le
  · simpa using Complex.abs_re_le_norm (ratComplex (centerQ i)-ratComplex (centerQ j))
  · simpa using Complex.abs_im_le_norm (ratComplex (centerQ i)-ratComplex (centerQ j))

theorem center_injective : Function.Injective (fun i : Fin 7 => ratComplex (centerQ i)) := by
  intro i j hij
  change ratComplex (centerQ i)=ratComplex (centerQ j) at hij
  by_contra hne
  have h := distance_le_norm i j hne
  rw [hij,sub_self,norm_zero] at h
  have hp : 0<(distanceQ i j:ℝ) := by exact_mod_cast distance_positive i j
  exact (not_le_of_gt hp) h

theorem radius_positive : 0<(radiusQ:ℝ) := by
  exact_mod_cast (show (0:ℚ)<radiusQ by decide +kernel)

theorem p_bound_erase_product (i : Fin 7) : (pBoundQ i:ℝ)=
    (1/100:ℝ)*(radiusQ:ℝ)*∏ j ∈ (Finset.univ : Finset (Fin 7)).erase i,(distanceQ i j:ℝ) := by
  have h : (pBoundQ i:ℝ)=(1/100:ℝ)*(radiusQ:ℝ)*∏ j : Fin 7,(distanceQ i j:ℝ) := by
    have hq := congrArg (fun q : ℚ => (q:ℝ)) (bound_product i)
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_prod] using hq
  have hp : (∏ j ∈ (Finset.univ : Finset (Fin 7)).erase i,(distanceQ i j:ℝ))=
      ∏ j : Fin 7,(distanceQ i j:ℝ) := by
    simpa only [distance_diagonal,Rat.cast_one,mul_one] using
      Finset.prod_erase_mul Finset.univ (fun j : Fin 7 => (distanceQ i j:ℝ)) (Finset.mem_univ i)
  rw [hp]
  exact h

/-- Every root of the concrete degree-7 polynomial lies in a certified disk.
The proof uses only exact rational certificates and barycentric interpolation. -/
theorem pRoot_root_in_disk (z : ℂ) (hz : pRoot.eval z=0) :
    ∃ i : Fin 7,‖z-ratComplex (centerQ i)‖<(radiusQ:ℝ) := by
  have hsmall : ∑ i : Fin 7,
      ‖Lagrange.nodalWeight Finset.univ (fun j => ratComplex (centerQ j)) i*
        pRoot.eval (ratComplex (centerQ i))‖/(radiusQ:ℝ)<1 := by
    apply lt_of_le_of_lt _ (show (∑ _i : Fin 7,(1/100:ℝ))<1 by norm_num)
    apply Finset.sum_le_sum
    intro i _hi
    apply (div_le_iff₀ radius_positive).mpr
    apply QuantitativeArithmeticPolynomialRootCover.nodal_eval_bound_of_separations
      Finset.univ (fun j => ratComplex (centerQ j)) pRoot i
      (fun j => (distanceQ i j:ℝ)) (1/100:ℝ) (radiusQ:ℝ)
    · intro j _hj
      exact_mod_cast distance_positive i j
    · intro j hj
      exact distance_le_norm i j (Finset.mem_erase.mp hj).1.symm
    · rw [← p_bound_erase_product]
      exact all_P_value_bounds i
  obtain ⟨i,_hi,h⟩ := QuantitativeArithmeticPolynomialRootCover.monic_root_cover
    Finset.univ (fun j => ratComplex (centerQ j)) (fun _ => (radiusQ:ℝ)) pRoot
    center_injective.injOn pRoot_monic (by simpa using pRoot_degree)
    (fun _ _ => radius_positive) hsmall z hz
  exact ⟨i,h⟩

#print axioms center_injective
#print axioms pRoot_root_in_disk
end SmallLevelTwentySixExceptionalSevenXRoot
end
end

/-! ## SmallLevelTwentySixExceptionalSevenXRootNormBoundsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace SmallLevelTwentySixExceptionalSevenXRoot
open Complex Polynomial QuantitativeArithmeticComplexHornerBounds
def lowerQ : Fin 7→ℚ := ![(901/500),(1193/500),(1193/500),(2876/125),(2876/125),(9479/1000),(9479/1000)]
def upperQ : Fin 7→ℚ := ![(1803/1000),(2387/1000),(2387/1000),(23009/1000),(23009/1000),(237/25),(237/25)]
theorem lower_enclosure : ∀ i : Fin 7,lowerQ i≤
    (centerQ i).1^2+(centerQ i).2^2-radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ) := by decide +kernel
theorem upper_enclosure : ∀ i : Fin 7,
    (centerQ i).1^2+(centerQ i).2^2+radiusQ*(2*(|(centerQ i).1|+|(centerQ i).2|)+radiusQ)≤upperQ i := by decide +kernel

theorem root_norm_bounds (z : ℂ) (hz : pRoot.eval z=0) :
    ∃ i : Fin 7,(lowerQ i:ℝ)≤‖z‖^2 ∧ ‖z‖^2≤(upperQ i:ℝ) := by
  obtain ⟨i,hi⟩:=pRoot_root_in_disk z hz
  exact ⟨i,squared_norm_enclosure_of_rational_error z (centerQ i) radiusQ
    (lowerQ i) (upperQ i) (by decide +kernel) hi.le (lower_enclosure i) (upper_enclosure i)⟩
theorem polynomial_binding (x y : ℂ) :
    SmallLevelTwentySixExceptionalCurve.extraFactor7 x y=125*pRoot.eval x := by
  norm_num [SmallLevelTwentySixExceptionalCurve.extraFactor7,pRoot,pCoefficient,
    eval_hornerPolynomial,hornerValue]
  ring
#print axioms polynomial_binding
#print axioms root_norm_bounds

end SmallLevelTwentySixExceptionalSevenXRoot
end
end
end
