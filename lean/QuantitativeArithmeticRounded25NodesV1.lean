module
public import QuantitativeArithmeticRoundedHornerTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFivePositiveRootP67DataV1
public import QuantitativeArithmeticSmallLevelTwentyFivePositiveRootH66DataV1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.PositiveRoot
open QuantitativeArithmeticComplexHornerBounds
namespace Rounded
def precision : ℚ := 10^400
theorem precision_pos : 0<precision := pow_pos (by norm_num) _
end Rounded

def node0Center : ℚ × ℚ := (-7731116863398081872423513323821840598824192894395711702249401205110544243176759829300944829072736549549589488869608020575545750780790006535678126740875967868433178296416017357940128295311246571556910397714214343421885369639140470963461734616183059098978333957023841755633993994470339906583254117357160*centerUnit,0*centerUnit)

def node0R : ℚ := 8

def node0PBound : ℚ := (128922116004130914531515980265124328974892014191442996577044444275908409527731712812358410921831460892896299045897143211269572178652864923131827127569659734624529890023181547696888987220578354927473343998921900922708001323226674151426259262309840602792179589684829407451828109982406284890596437799764725595003646615793421650650401318638962489920540121197777493549366534339473094488103019508294274279628703597107577608749262427579141392573026318116870048738194621197199572781463355226378955281186650019304824686664947715662584900438826692938134113159636717980912678084295019849832092719544900498101963780954243092071084178484115740719299180677265033940521961118104226337525017717291046671738831177905842956166934217728737029170709975333165757582439082899429730845873235611467201205019718408452012159382242159580299034632805881929/555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node0PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node0Center (68-j) j
def node0PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node0R (68-j)
def node0HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node0Center (67-j) j
def node0HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node0R (67-j)

theorem node0_norm_upper : |node0Center.1|+|node0Center.2|≤node0R := by decide +kernel
theorem node0_error_nonneg : ∀ j : Fin 69, 0≤node0PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node0R]) _
theorem node0_terminal : |(node0PState 68).1|+|(node0PState 68).2|≤node0PError 68 := by
  simp [node0PState, node0PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node0_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node0Center (node0PState (j+1)) (node0PState j)).1|+
    |(ratResidual (pCoefficient j) node0Center (node0PState (j+1)) (node0PState j)).2|+
    node0R*node0PError (j+1)≤node0PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node0_final : |(node0PState 0).1|+|(node0PState 0).2|+node0PError 0≤node0PBound := by
  decide +kernel
theorem node0_P_value_bound : ‖p67.eval (ratComplex node0Center)‖≤(node0PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node0_norm_upper 68 node0_final

theorem node0_H_error_nonneg : ∀ j : Fin 68,0≤node0HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node0R]) _
theorem node0_H_terminal : |(node0HState 67).1|+|(node0HState 67).2|≤node0HError 67 := by
  simp [node0HState, node0HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node0_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node0Center (node0HState (j.val+1)) (node0HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node0Center (node0HState (j.val+1)) (node0HState j.val)).2|+
    node0R*node0HError (j.val+1)≤node0HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node0_H_value_error :
    ‖h66.eval (ratComplex node0Center)-ratComplex (node0HState 0)‖≤(node0HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node0_norm_upper 67
#print axioms node0_P_value_bound
#print axioms node0_H_value_error

def node1Center : ℚ × ℚ := (-3469124363525693942456360652729350872183193560850350419039405902332767674458943640641105837197575196900008378003652868368696082853291711843613762151572803054625996833480130638881988623857544021851927706522662402485573368565519570597729432209982522744839409696075999969783174241131477310411974548382317*centerUnit,0*centerUnit)

def node1R : ℚ := 4

def node1PBound : ℚ := (266604143051802094912564606217599327694020547693264475580148022396174088710602114863361406055297460690749735267288668636315816428869797106386692265154864959142704622807151490524468592668496033391045953849988305798951749385692269407931891114172989888127474834539469662516513649862831013323390868945363651413407758649968205028017027380845828009148211540981519623715920072981809450262403992083498161454728282864743244990152573167272006693595339152082141873040289216970601582726336162951213078202396280902809376491058133355285001448324606274767088282081889150765672983110503974771395056504154487628110308695699750832713210933388914196444343698093533124267570684508119957694562979859666269047352918795561742211324404099827680376738420753988420528567657571137750665989968474164384074166819860480428637035419/86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node1PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node1Center (68-j) j
def node1PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node1R (68-j)
def node1HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node1Center (67-j) j
def node1HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node1R (67-j)

theorem node1_norm_upper : |node1Center.1|+|node1Center.2|≤node1R := by decide +kernel
theorem node1_error_nonneg : ∀ j : Fin 69, 0≤node1PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node1R]) _
theorem node1_terminal : |(node1PState 68).1|+|(node1PState 68).2|≤node1PError 68 := by
  simp [node1PState, node1PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node1_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node1Center (node1PState (j+1)) (node1PState j)).1|+
    |(ratResidual (pCoefficient j) node1Center (node1PState (j+1)) (node1PState j)).2|+
    node1R*node1PError (j+1)≤node1PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node1_final : |(node1PState 0).1|+|(node1PState 0).2|+node1PError 0≤node1PBound := by
  decide +kernel
theorem node1_P_value_bound : ‖p67.eval (ratComplex node1Center)‖≤(node1PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node1_norm_upper 68 node1_final

theorem node1_H_error_nonneg : ∀ j : Fin 68,0≤node1HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node1R]) _
theorem node1_H_terminal : |(node1HState 67).1|+|(node1HState 67).2|≤node1HError 67 := by
  simp [node1HState, node1HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node1_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node1Center (node1HState (j.val+1)) (node1HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node1Center (node1HState (j.val+1)) (node1HState j.val)).2|+
    node1R*node1HError (j.val+1)≤node1HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node1_H_value_error :
    ‖h66.eval (ratComplex node1Center)-ratComplex (node1HState 0)‖≤(node1HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node1_norm_upper 67
#print axioms node1_P_value_bound
#print axioms node1_H_value_error

def node2Center : ℚ × ℚ := (-2372181636872802304238285129620991197653404382756660906221611656201089044514536589456653911173699645666505608965772512986933628017816858669051222276829721417273057658452679188236952005253035875701978871470928105180114310916912529945292269038150395922602303450211502122645657747265149799173197800446258*centerUnit,0*centerUnit)

def node2R : ℚ := 3

def node2PBound : ℚ := (17442807694074833015040189424923483301316878739533830662300965391876774343701317115274488299129034557925474519351299965868392351232469819100461960938014221273190837386560160978499460948617395185918414362421334922307632123369383028960482233425689848236348027082924660633222994612513919900150760643636581523108541831674738496929899069580489983775976777496957677538197590069335120940337049992033371000575624708113416848727455439171309948844155313173352384338858055811602066141230083514752850838932062678716643852306914676664990363455984536220771325931903163979521931584263562703278790670787640809706753730809899016567461969146807882653938251421133281051815889170848747856562426477091375614208950517898883448171338626927223098671723547709036697522626031077233243605412164960410710372961504751324110031429691/372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node2PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node2Center (68-j) j
def node2PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node2R (68-j)
def node2HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node2Center (67-j) j
def node2HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node2R (67-j)

theorem node2_norm_upper : |node2Center.1|+|node2Center.2|≤node2R := by decide +kernel
theorem node2_error_nonneg : ∀ j : Fin 69, 0≤node2PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node2R]) _
theorem node2_terminal : |(node2PState 68).1|+|(node2PState 68).2|≤node2PError 68 := by
  simp [node2PState, node2PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node2_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node2Center (node2PState (j+1)) (node2PState j)).1|+
    |(ratResidual (pCoefficient j) node2Center (node2PState (j+1)) (node2PState j)).2|+
    node2R*node2PError (j+1)≤node2PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node2_final : |(node2PState 0).1|+|(node2PState 0).2|+node2PError 0≤node2PBound := by
  decide +kernel
theorem node2_P_value_bound : ‖p67.eval (ratComplex node2Center)‖≤(node2PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node2_norm_upper 68 node2_final

theorem node2_H_error_nonneg : ∀ j : Fin 68,0≤node2HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node2R]) _
theorem node2_H_terminal : |(node2HState 67).1|+|(node2HState 67).2|≤node2HError 67 := by
  simp [node2HState, node2HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node2_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node2Center (node2HState (j.val+1)) (node2HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node2Center (node2HState (j.val+1)) (node2HState j.val)).2|+
    node2R*node2HError (j.val+1)≤node2HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node2_H_value_error :
    ‖h66.eval (ratComplex node2Center)-ratComplex (node2HState 0)‖≤(node2HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node2_norm_upper 67
#print axioms node2_P_value_bound
#print axioms node2_H_value_error

def node3Center : ℚ × ℚ := (324035757008175194132230367425226336203406919141712267598409731184835408213797838249997565762119261303391827970616728225268779486636228072513694632503613111792317768282132278829924840712455203225478362181927104306776842802619795589484388926238293430433078544059208108895706289548267717884416972833687*centerUnit,0*centerUnit)

def node3R : ℚ := 1

def node3PBound : ℚ := (942094838091473111284248519475099883447072788680900792227030222742541548223384474506220559692134308294125729642387721466859664251647466079006764010294730074786482189443515141982716035215948354644999287101349108028319030864838453019330390062933516785214474174608863949012234582535451536932908630126281659466627229679564025273986282019047303377377114085229006715925934837736661434836451136453743199237199192493615293764452557644896050972862214181254670571540692756666773169446333568260243075515299120899950739646175767889096399296062683346137914730586936158237396024595838446771413128760168885722699823504285175833738554439330323249650192531907250879778633372370050993457332307363867117967794320561016248697858630472511745417510380981661513579731489996408835500718802706156918716983/888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node3PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node3Center (68-j) j
def node3PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node3R (68-j)
def node3HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node3Center (67-j) j
def node3HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node3R (67-j)

theorem node3_norm_upper : |node3Center.1|+|node3Center.2|≤node3R := by decide +kernel
theorem node3_error_nonneg : ∀ j : Fin 69, 0≤node3PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node3R]) _
theorem node3_terminal : |(node3PState 68).1|+|(node3PState 68).2|≤node3PError 68 := by
  simp [node3PState, node3PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node3_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node3Center (node3PState (j+1)) (node3PState j)).1|+
    |(ratResidual (pCoefficient j) node3Center (node3PState (j+1)) (node3PState j)).2|+
    node3R*node3PError (j+1)≤node3PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node3_final : |(node3PState 0).1|+|(node3PState 0).2|+node3PError 0≤node3PBound := by
  decide +kernel
theorem node3_P_value_bound : ‖p67.eval (ratComplex node3Center)‖≤(node3PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node3_norm_upper 68 node3_final

theorem node3_H_error_nonneg : ∀ j : Fin 68,0≤node3HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node3R]) _
theorem node3_H_terminal : |(node3HState 67).1|+|(node3HState 67).2|≤node3HError 67 := by
  simp [node3HState, node3HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node3_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node3Center (node3HState (j.val+1)) (node3HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node3Center (node3HState (j.val+1)) (node3HState j.val)).2|+
    node3R*node3HError (j.val+1)≤node3HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node3_H_value_error :
    ‖h66.eval (ratComplex node3Center)-ratComplex (node3HState 0)‖≤(node3HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node3_norm_upper 67
#print axioms node3_P_value_bound
#print axioms node3_H_value_error

def node4Center : ℚ × ℚ := (994494257701558516444721798015096001077317186184770129383426609973727302774256092027951562041665120888885113809029750483520250713626798669739255550547824934972758366595740869205033301278437544837865785423021666254643022279784265291043312119358174671954726641994623573079195307119126205672843528606823*centerUnit,0*centerUnit)

def node4R : ℚ := 1

def node4PBound : ℚ := (6951890319901497724050224481483582814350423126487842409642899071178519935708354154668514477650284781571983994587026242545249273747795625794125057181591345465976627417988783140271692214089645603826299198316481846339682875520091079625247643407378188040779048473982744666022756762032626946116211061902488469431128448988580922553120621133905003288221291839440947049795245929868796779939473179652875304733239825066265826698334783197747078803678147329516580447113783770953725924858323465110036442536043738950475476517483136251814678535577669281704296744846491497409425391533738941660341589291023727506003155167501641627000283648906630417860548290052914107823790405309776358672787157359993135948949369634033392747103747855929788165572559973081179353147755396304192912684854543226822735777968525079/1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node4PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node4Center (68-j) j
def node4PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node4R (68-j)
def node4HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node4Center (67-j) j
def node4HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node4R (67-j)

theorem node4_norm_upper : |node4Center.1|+|node4Center.2|≤node4R := by decide +kernel
theorem node4_error_nonneg : ∀ j : Fin 69, 0≤node4PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node4R]) _
theorem node4_terminal : |(node4PState 68).1|+|(node4PState 68).2|≤node4PError 68 := by
  simp [node4PState, node4PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node4_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node4Center (node4PState (j+1)) (node4PState j)).1|+
    |(ratResidual (pCoefficient j) node4Center (node4PState (j+1)) (node4PState j)).2|+
    node4R*node4PError (j+1)≤node4PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node4_final : |(node4PState 0).1|+|(node4PState 0).2|+node4PError 0≤node4PBound := by
  decide +kernel
theorem node4_P_value_bound : ‖p67.eval (ratComplex node4Center)‖≤(node4PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node4_norm_upper 68 node4_final

theorem node4_H_error_nonneg : ∀ j : Fin 68,0≤node4HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node4R]) _
theorem node4_H_terminal : |(node4HState 67).1|+|(node4HState 67).2|≤node4HError 67 := by
  simp [node4HState, node4HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node4_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node4Center (node4HState (j.val+1)) (node4HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node4Center (node4HState (j.val+1)) (node4HState j.val)).2|+
    node4R*node4HError (j.val+1)≤node4HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node4_H_value_error :
    ‖h66.eval (ratComplex node4Center)-ratComplex (node4HState 0)‖≤(node4HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node4_norm_upper 67
#print axioms node4_P_value_bound
#print axioms node4_H_value_error

def node5Center : ℚ × ℚ := (1699746731079027765866829491995688423031463602583299360809893606309285723237909733205455806874822630062378426105959277351007882013302466556594102198026691931318909709946413987543212600631175274611057448014860029163267785301102764545543320655967557360542870640138722243874882045364215741736493512499800*centerUnit,0*centerUnit)

def node5R : ℚ := 2

def node5PBound : ℚ := (518525106310032566239515807136712069370275113741829408213376438785349387201285364089414680338136030504718417271917762297829046815270305979980405320671993414752225347396014957892094621046214084397316728223413119291700597053183248453385519556711054248982582488045547606014381984177073699590336834647095371438785210135029936041511394708386251744413873756458578375160561253679524556959663504282703107677314157815961184778486587705494663707238889990629932549442383532997666983537251982873180397599451504842944478878792722430672201861495881101334803915355656231257462413279087056359151277505173500979462787737778630269032230806871379755175567659939548209940056646484051827320957531628570228586570860715154157873794495933896464768520726125671115558502360384551263789267335548689645998776098141811297431/11102230246251565404236316680908203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node5PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node5Center (68-j) j
def node5PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node5R (68-j)
def node5HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node5Center (67-j) j
def node5HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node5R (67-j)

theorem node5_norm_upper : |node5Center.1|+|node5Center.2|≤node5R := by decide +kernel
theorem node5_error_nonneg : ∀ j : Fin 69, 0≤node5PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node5R]) _
theorem node5_terminal : |(node5PState 68).1|+|(node5PState 68).2|≤node5PError 68 := by
  simp [node5PState, node5PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node5_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node5Center (node5PState (j+1)) (node5PState j)).1|+
    |(ratResidual (pCoefficient j) node5Center (node5PState (j+1)) (node5PState j)).2|+
    node5R*node5PError (j+1)≤node5PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node5_final : |(node5PState 0).1|+|(node5PState 0).2|+node5PError 0≤node5PBound := by
  decide +kernel
theorem node5_P_value_bound : ‖p67.eval (ratComplex node5Center)‖≤(node5PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node5_norm_upper 68 node5_final

theorem node5_H_error_nonneg : ∀ j : Fin 68,0≤node5HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node5R]) _
theorem node5_H_terminal : |(node5HState 67).1|+|(node5HState 67).2|≤node5HError 67 := by
  simp [node5HState, node5HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node5_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node5Center (node5HState (j.val+1)) (node5HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node5Center (node5HState (j.val+1)) (node5HState j.val)).2|+
    node5R*node5HError (j.val+1)≤node5HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node5_H_value_error :
    ‖h66.eval (ratComplex node5Center)-ratComplex (node5HState 0)‖≤(node5HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node5_norm_upper 67
#print axioms node5_P_value_bound
#print axioms node5_H_value_error

def node6Center : ℚ × ℚ := (2439025057563764203902094395101995132833858202023024448210125187803319030333943578493293992291052597586094807259061781421050915144286176158444720510349803006358771091696948719576555704025763516127633941813114762429269361978674280200856044518941731220477066613837361838194828026336025440534002218699235*centerUnit,0*centerUnit)

def node6R : ℚ := 3

def node6PBound : ℚ := (6112804648473063667694826914345909375615744396413512138169273657193270183995815478543373383949967175455868884914571910335402984058883142960275591198645357046577434467999464924736684203882692845903125963503935408912916136658144921569921725506454259436020520194596597380243941691520760038093628291261057040395991549321173687591033336046696722407773228704729273904105752122501486268858010060319913507690215017948533413211182941528985007513201199356427882302920677339813231760576269167789502509102096891850387372182581461560362181365859785674326207365075936971361975566797655059989684967921939226879996077299508109121974782054069474667319045660892647257234166887451938123174129604948439828657656465575090390531617395655074908233251088285164204211635488782887414498520802519846009027955559713/67762635780344027125465800054371356964111328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node6PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node6Center (68-j) j
def node6PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node6R (68-j)
def node6HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node6Center (67-j) j
def node6HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node6R (67-j)

theorem node6_norm_upper : |node6Center.1|+|node6Center.2|≤node6R := by decide +kernel
theorem node6_error_nonneg : ∀ j : Fin 69, 0≤node6PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node6R]) _
theorem node6_terminal : |(node6PState 68).1|+|(node6PState 68).2|≤node6PError 68 := by
  simp [node6PState, node6PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node6_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node6Center (node6PState (j+1)) (node6PState j)).1|+
    |(ratResidual (pCoefficient j) node6Center (node6PState (j+1)) (node6PState j)).2|+
    node6R*node6PError (j+1)≤node6PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node6_final : |(node6PState 0).1|+|(node6PState 0).2|+node6PError 0≤node6PBound := by
  decide +kernel
theorem node6_P_value_bound : ‖p67.eval (ratComplex node6Center)‖≤(node6PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node6_norm_upper 68 node6_final

theorem node6_H_error_nonneg : ∀ j : Fin 68,0≤node6HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node6R]) _
theorem node6_H_terminal : |(node6HState 67).1|+|(node6HState 67).2|≤node6HError 67 := by
  simp [node6HState, node6HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node6_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node6Center (node6HState (j.val+1)) (node6HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node6Center (node6HState (j.val+1)) (node6HState j.val)).2|+
    node6R*node6HError (j.val+1)≤node6HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node6_H_value_error :
    ‖h66.eval (ratComplex node6Center)-ratComplex (node6HState 0)‖≤(node6HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node6_norm_upper 67
#print axioms node6_P_value_bound
#print axioms node6_H_value_error

def node7Center : ℚ × ℚ := (3295629823431785660101149584131521381077697620567856000004384574627818903706541183327374214762347579134641221698506668879234479603126925509925472218371834771537711764669134840300275782024087600844068978060518669746321238528551205411377113260771395169341322561768001600910031730945165993232026237078174*centerUnit,0*centerUnit)

def node7R : ℚ := 4

def node7PBound : ℚ := (3017332965066951590009673824931336997620970971457903863147941413413083613228698653827784969215908981665662570120830435288938833129455238702991344718863178766019393817796073848565979730086264451595343438095606396248935923186800885006028053892461609452665314399518452235155023757147608184509161658684318092698217984987153941709649698253437234053256539244195780894779531811732697345302703331055762603557986953058677122382777735834830192414171665973018149649970756089594214851857666530411291475218491692373402940168587384941617756110698472506558766174480225810953606807531837871054124005267986393790370417511440158111478139627938905081142635654800862260981828383688076366795815730712193069522098470210160147506267976536532214385205343851155000217405406399911250741877620758121999743717886153793599645943/1776356839400250464677810668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node7PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node7Center (68-j) j
def node7PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node7R (68-j)
def node7HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node7Center (67-j) j
def node7HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node7R (67-j)

theorem node7_norm_upper : |node7Center.1|+|node7Center.2|≤node7R := by decide +kernel
theorem node7_error_nonneg : ∀ j : Fin 69, 0≤node7PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node7R]) _
theorem node7_terminal : |(node7PState 68).1|+|(node7PState 68).2|≤node7PError 68 := by
  simp [node7PState, node7PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node7_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node7Center (node7PState (j+1)) (node7PState j)).1|+
    |(ratResidual (pCoefficient j) node7Center (node7PState (j+1)) (node7PState j)).2|+
    node7R*node7PError (j+1)≤node7PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node7_final : |(node7PState 0).1|+|(node7PState 0).2|+node7PError 0≤node7PBound := by
  decide +kernel
theorem node7_P_value_bound : ‖p67.eval (ratComplex node7Center)‖≤(node7PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node7_norm_upper 68 node7_final

theorem node7_H_error_nonneg : ∀ j : Fin 68,0≤node7HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node7R]) _
theorem node7_H_terminal : |(node7HState 67).1|+|(node7HState 67).2|≤node7HError 67 := by
  simp [node7HState, node7HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node7_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node7Center (node7HState (j.val+1)) (node7HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node7Center (node7HState (j.val+1)) (node7HState j.val)).2|+
    node7R*node7HError (j.val+1)≤node7HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node7_H_value_error :
    ‖h66.eval (ratComplex node7Center)-ratComplex (node7HState 0)‖≤(node7HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node7_norm_upper 67
#print axioms node7_P_value_bound
#print axioms node7_H_value_error

def node8Center : ℚ × ℚ := (14163859317693310629779046952082907920107846029613841932887170718731423259307476350059780598420443815074241524243751015402555265542818984828773489938136066018122583215971767145580298640468470924741202699730531576445227752801646782512345088075025054017027648317997615495003595054180726705209430363898504*centerUnit,0*centerUnit)

def node8R : ℚ := 15

def node8PBound : ℚ := (1189889378806529263924649306245778262940130061643274864764750101449395486207590113514853995879256794730558289363568828700623775401800683934948865262525389755365692683820005906898870261099731236758262500702961696746076185297365011700814314206606491876489530869259127358651830570895638258981046521236925285952324256168602854677230806432889722962793616165044870972567987620779628411286014390555182310427131490515722645833769940531210230904083278336595203239227296481074623625654251854067389182806463869644191006146170582920929063550573801512558112720758227649824182982941712458635189761713296846382829599554998953320595281112304279591693066438636861459216476452686421665869565507849637191978767674910476839680409285250464491673580109264159626609248539103226946799506385158650698828731037090403611493076668399730735023569386847486636831437/88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node8PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node8Center (68-j) j
def node8PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node8R (68-j)
def node8HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node8Center (67-j) j
def node8HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node8R (67-j)

theorem node8_norm_upper : |node8Center.1|+|node8Center.2|≤node8R := by decide +kernel
theorem node8_error_nonneg : ∀ j : Fin 69, 0≤node8PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node8R]) _
theorem node8_terminal : |(node8PState 68).1|+|(node8PState 68).2|≤node8PError 68 := by
  simp [node8PState, node8PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node8_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node8Center (node8PState (j+1)) (node8PState j)).1|+
    |(ratResidual (pCoefficient j) node8Center (node8PState (j+1)) (node8PState j)).2|+
    node8R*node8PError (j+1)≤node8PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node8_final : |(node8PState 0).1|+|(node8PState 0).2|+node8PError 0≤node8PBound := by
  decide +kernel
theorem node8_P_value_bound : ‖p67.eval (ratComplex node8Center)‖≤(node8PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node8_norm_upper 68 node8_final

theorem node8_H_error_nonneg : ∀ j : Fin 68,0≤node8HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node8R]) _
theorem node8_H_terminal : |(node8HState 67).1|+|(node8HState 67).2|≤node8HError 67 := by
  simp [node8HState, node8HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node8_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node8Center (node8HState (j.val+1)) (node8HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node8Center (node8HState (j.val+1)) (node8HState j.val)).2|+
    node8R*node8HError (j.val+1)≤node8HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node8_H_value_error :
    ‖h66.eval (ratComplex node8Center)-ratComplex (node8HState 0)‖≤(node8HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node8_norm_upper 67
#print axioms node8_P_value_bound
#print axioms node8_H_value_error

def node9Center : ℚ × ℚ := (16882670402645422586464202071736358633005581911599755390001274406917246093402666139337953791806079362144901472160428392918302135710101925937337323444491879637374061389985950272735066156234994791672123011835827664593529341024920376237514869726970752272551355701202934630350305431754176171013333407548941*centerUnit,0*centerUnit)

def node9R : ℚ := 17

def node9PBound : ℚ := (63529637042673532215127610260157823261928988823718206057882839296746280154077187951064646609997030662161042424021034784991982156566778591235348747994762236853657064734721247097977389495660701171078798632783464534464855316619497355775067396596193816341425844738507055686459739343828535370561355605556786156418343746512432674341565545900976918179008052272593566341553478040966098457253701392449230310565757290205644694099103629661810210075760357239714476532527698866914561278411922467377292178871825887272401209338435293193120461131675295692886441499189307313930968214167913690143174327446932113279027631453216530520349646286236310050989332090387216028863161629474601702389134375962680750376039047166318974435818533580364273828905265821085043298682273014596728343391293008975547614926120271272181836335133785767254828510346693862123133043013543/108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node9PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node9Center (68-j) j
def node9PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node9R (68-j)
def node9HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node9Center (67-j) j
def node9HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node9R (67-j)

theorem node9_norm_upper : |node9Center.1|+|node9Center.2|≤node9R := by decide +kernel
theorem node9_error_nonneg : ∀ j : Fin 69, 0≤node9PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node9R]) _
theorem node9_terminal : |(node9PState 68).1|+|(node9PState 68).2|≤node9PError 68 := by
  simp [node9PState, node9PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node9_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node9Center (node9PState (j+1)) (node9PState j)).1|+
    |(ratResidual (pCoefficient j) node9Center (node9PState (j+1)) (node9PState j)).2|+
    node9R*node9PError (j+1)≤node9PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node9_final : |(node9PState 0).1|+|(node9PState 0).2|+node9PError 0≤node9PBound := by
  decide +kernel
theorem node9_P_value_bound : ‖p67.eval (ratComplex node9Center)‖≤(node9PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node9_norm_upper 68 node9_final

theorem node9_H_error_nonneg : ∀ j : Fin 68,0≤node9HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node9R]) _
theorem node9_H_terminal : |(node9HState 67).1|+|(node9HState 67).2|≤node9HError 67 := by
  simp [node9HState, node9HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node9_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node9Center (node9HState (j.val+1)) (node9HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node9Center (node9HState (j.val+1)) (node9HState j.val)).2|+
    node9R*node9HError (j.val+1)≤node9HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node9_H_value_error :
    ‖h66.eval (ratComplex node9Center)-ratComplex (node9HState 0)‖≤(node9HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node9_norm_upper 67
#print axioms node9_P_value_bound
#print axioms node9_H_value_error

def node10Center : ℚ × ℚ := (57098951801922414218638763278561940503172217785749985437830859656550981957395881984680342100302370727420965490045622145828307510407776743451826480396286813937226445110727364840158886659570062197357454040730970488714174457087214896190553288589355270120768064836649233009350606839166051277521752649951016*centerUnit,0*centerUnit)

def node10R : ℚ := 58

def node10PBound : ℚ := (2513965936787782863037851461015331320368360736406590244382038222883961692724380154314980193163687586085787919800697369129538463705659529655197329729248513172954963133478492250398357046125346048730562887275839797140833745532015108854744635058567043276666855336093493870639813811036793862650786533585971622759322575999715820208513619338457930751861776802196151250832635493184682987972564975358158707551547641420368486045690901661093835742119714143918393246663566422261351293887250859283852853805943243423744968415235854507830961265693638315681124492067887007654347058837002060239714010691597771067953901919410400409991153538647254657634190683469746588282445719518513888468085621614367783051393154776238070389326854492457029926901955141173223970428429682478135199359844578526345425785606113457581029660518981899017761770188432813092942610628088605458751594121422580604967107/264697796016968855958850781462388113141059875488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node10PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node10Center (68-j) j
def node10PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node10R (68-j)
def node10HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node10Center (67-j) j
def node10HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node10R (67-j)

theorem node10_norm_upper : |node10Center.1|+|node10Center.2|≤node10R := by decide +kernel
theorem node10_error_nonneg : ∀ j : Fin 69, 0≤node10PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node10R]) _
theorem node10_terminal : |(node10PState 68).1|+|(node10PState 68).2|≤node10PError 68 := by
  simp [node10PState, node10PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node10_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node10Center (node10PState (j+1)) (node10PState j)).1|+
    |(ratResidual (pCoefficient j) node10Center (node10PState (j+1)) (node10PState j)).2|+
    node10R*node10PError (j+1)≤node10PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node10_final : |(node10PState 0).1|+|(node10PState 0).2|+node10PError 0≤node10PBound := by
  decide +kernel
theorem node10_P_value_bound : ‖p67.eval (ratComplex node10Center)‖≤(node10PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node10_norm_upper 68 node10_final

theorem node10_H_error_nonneg : ∀ j : Fin 68,0≤node10HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node10R]) _
theorem node10_H_terminal : |(node10HState 67).1|+|(node10HState 67).2|≤node10HError 67 := by
  simp [node10HState, node10HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node10_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node10Center (node10HState (j.val+1)) (node10HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node10Center (node10HState (j.val+1)) (node10HState j.val)).2|+
    node10R*node10HError (j.val+1)≤node10HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node10_H_value_error :
    ‖h66.eval (ratComplex node10Center)-ratComplex (node10HState 0)‖≤(node10HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node10_norm_upper 67
#print axioms node10_P_value_bound
#print axioms node10_H_value_error

def node11Center : ℚ × ℚ := (-43283460105639687324124674486574027804453425241536420323882336482107322258568881931282069981878181550127475175575665109859946773711208825814253781422966954547784372760430176889994223419858293092321470007477838441590736202783012153078367310641258047121108621030822544475254015252891847113539959046701*centerUnit,-53887903274747933860253702414885093120531668838626335546492317845146514206261763059766959206036666004362060349095725546209971114694399762590921297133424385955166452123092685284594800989511392067980151365923916230181269630433220674353872374285332804648777728182174459054999852023114975230891618730646*centerUnit)

def node11R : ℚ := 1

def node11PBound : ℚ := (3395579786138587252415951759189459274100503303278779987930606348729551167588421978511454001319823143967780910581622917277783711140752238247833284617911542287371686257241262466362705140118855690904048140226076818117132957170369405880134732198565778602962758815453294844377105931859566665404178652868086190771986954010149259131809806207308845836388769657243612467587436783452763008993541239875976997843859052072236456286940830377382268731478642507489277328718716853574226249200119593913494474566227885667834178218158773096576760828668768118991462412745009933183388467580439792310132880886261018144269402722365900729701094156727979128477485783164641007932864480515251467806982933802682371421202306321238319143682250239131711925418130381007211342679652883514953198555267542985294537499503/1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node11PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node11Center (68-j) j
def node11PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node11R (68-j)
def node11HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node11Center (67-j) j
def node11HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node11R (67-j)

theorem node11_norm_upper : |node11Center.1|+|node11Center.2|≤node11R := by decide +kernel
theorem node11_error_nonneg : ∀ j : Fin 69, 0≤node11PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node11R]) _
theorem node11_terminal : |(node11PState 68).1|+|(node11PState 68).2|≤node11PError 68 := by
  simp [node11PState, node11PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node11_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node11Center (node11PState (j+1)) (node11PState j)).1|+
    |(ratResidual (pCoefficient j) node11Center (node11PState (j+1)) (node11PState j)).2|+
    node11R*node11PError (j+1)≤node11PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node11_final : |(node11PState 0).1|+|(node11PState 0).2|+node11PError 0≤node11PBound := by
  decide +kernel
theorem node11_P_value_bound : ‖p67.eval (ratComplex node11Center)‖≤(node11PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node11_norm_upper 68 node11_final

theorem node11_H_error_nonneg : ∀ j : Fin 68,0≤node11HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node11R]) _
theorem node11_H_terminal : |(node11HState 67).1|+|(node11HState 67).2|≤node11HError 67 := by
  simp [node11HState, node11HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node11_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node11Center (node11HState (j.val+1)) (node11HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node11Center (node11HState (j.val+1)) (node11HState j.val)).2|+
    node11R*node11HError (j.val+1)≤node11HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node11_H_value_error :
    ‖h66.eval (ratComplex node11Center)-ratComplex (node11HState 0)‖≤(node11HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node11_norm_upper 67
#print axioms node11_P_value_bound
#print axioms node11_H_value_error

def node12Center : ℚ × ℚ := (-43283460105639687324124674486574027804453425241536420323882336482107322258568881931282069981878181550127475175575665109859946773711208825814253781422966954547784372760430176889994223419858293092321470007477838441590736202783012153078367310641258047121108621030822544475254015252891847113539959046701*centerUnit,53887903274747933860253702414885093120531668838626335546492317845146514206261763059766959206036666004362060349095725546209971114694399762590921297133424385955166452123092685284594800989511392067980151365923916230181269630433220674353872374285332804648777728182174459054999852023114975230891618730645*centerUnit)

def node12R : ℚ := 1

def node12PBound : ℚ := (3395579786138587252415951759189459274100503303278779987930606348729551167588421978511454001319823143967780910581622917277783711140752238247833284617911542287371686257241262466362705140118855690904048140226076818117132957170369405880134732198565778602962758815453294844377105931859566665404178652868086190771986954010149259131809806207308845836388769657243612467587436783452763008993541239875976997843859052072236456286940830377382268731478642507489277328718716853574226249200119593913494474566227885667834178218158773096576760828668768118991462412745009933183388467580439792310132880886261018144269402722365900729701094156727979128477485783164641007932864480515251467806982933802682371421202306321238319143682250239131711925418130381007211342679652883514953198555267542985294537499503/1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node12PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node12Center (68-j) j
def node12PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node12R (68-j)
def node12HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node12Center (67-j) j
def node12HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node12R (67-j)

theorem node12_norm_upper : |node12Center.1|+|node12Center.2|≤node12R := by decide +kernel
theorem node12_error_nonneg : ∀ j : Fin 69, 0≤node12PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node12R]) _
theorem node12_terminal : |(node12PState 68).1|+|(node12PState 68).2|≤node12PError 68 := by
  simp [node12PState, node12PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node12_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node12Center (node12PState (j+1)) (node12PState j)).1|+
    |(ratResidual (pCoefficient j) node12Center (node12PState (j+1)) (node12PState j)).2|+
    node12R*node12PError (j+1)≤node12PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node12_final : |(node12PState 0).1|+|(node12PState 0).2|+node12PError 0≤node12PBound := by
  decide +kernel
theorem node12_P_value_bound : ‖p67.eval (ratComplex node12Center)‖≤(node12PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node12_norm_upper 68 node12_final

theorem node12_H_error_nonneg : ∀ j : Fin 68,0≤node12HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node12R]) _
theorem node12_H_terminal : |(node12HState 67).1|+|(node12HState 67).2|≤node12HError 67 := by
  simp [node12HState, node12HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node12_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node12Center (node12HState (j.val+1)) (node12HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node12Center (node12HState (j.val+1)) (node12HState j.val)).2|+
    node12R*node12HError (j.val+1)≤node12HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node12_H_value_error :
    ‖h66.eval (ratComplex node12Center)-ratComplex (node12HState 0)‖≤(node12HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node12_norm_upper 67
#print axioms node12_P_value_bound
#print axioms node12_H_value_error

def node13Center : ℚ × ℚ := (2078399454628958172369536364422688611318444885165100088399251916490002614634994092677190391201143515803077369072946209660522210630068420458851461498679910206300207448283573989539178155168683694739537142312808736136160136837657891750801911178845682591517011199216660229654708118433577766830615013503832*centerUnit,-57847881181383156975606268842878388462392490599160782617591286338333503538275783611932977748965824420761304373135943352152179094118874439901873775475532551530577960650219508704972093225530013177174924466052565757132533095056655846155026934736728988762954542454073966524961123200884725185985544831747*centerUnit)

def node13R : ℚ := 3

def node13PBound : ℚ := (18928217584786366026211144489864346394645619323958296113287953240398539164327024494476182509980049175753324042040522878276563389632459503573950310566421295107996235837517624626712127128611520039084514729408975437941077773317611015687837166550028287094546348453900446374599544068227800591763446071378191996995084949273827797647356498359695463967713924514592377837618047511535014472328506317285067541301033571883313401054829917661926759177479442345191621727971037438540093096969884567174035859139011846618076254260090153273627575069478575231156125919752421814642227584417399553401930274816428814299993411566342006188114909013779641593148288825686497448657493442558105849585704109442316682119739621031864857721537391067035758007795978820957789791991049760135651845202599706024164484866094770057/1058791184067875423835403125849552452564239501953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node13PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node13Center (68-j) j
def node13PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node13R (68-j)
def node13HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node13Center (67-j) j
def node13HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node13R (67-j)

theorem node13_norm_upper : |node13Center.1|+|node13Center.2|≤node13R := by decide +kernel
theorem node13_error_nonneg : ∀ j : Fin 69, 0≤node13PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node13R]) _
theorem node13_terminal : |(node13PState 68).1|+|(node13PState 68).2|≤node13PError 68 := by
  simp [node13PState, node13PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node13_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node13Center (node13PState (j+1)) (node13PState j)).1|+
    |(ratResidual (pCoefficient j) node13Center (node13PState (j+1)) (node13PState j)).2|+
    node13R*node13PError (j+1)≤node13PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node13_final : |(node13PState 0).1|+|(node13PState 0).2|+node13PError 0≤node13PBound := by
  decide +kernel
theorem node13_P_value_bound : ‖p67.eval (ratComplex node13Center)‖≤(node13PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node13_norm_upper 68 node13_final

theorem node13_H_error_nonneg : ∀ j : Fin 68,0≤node13HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node13R]) _
theorem node13_H_terminal : |(node13HState 67).1|+|(node13HState 67).2|≤node13HError 67 := by
  simp [node13HState, node13HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node13_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node13Center (node13HState (j.val+1)) (node13HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node13Center (node13HState (j.val+1)) (node13HState j.val)).2|+
    node13R*node13HError (j.val+1)≤node13HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node13_H_value_error :
    ‖h66.eval (ratComplex node13Center)-ratComplex (node13HState 0)‖≤(node13HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node13_norm_upper 67
#print axioms node13_P_value_bound
#print axioms node13_H_value_error

def node14Center : ℚ × ℚ := (2078399454628958172369536364422688611318444885165100088399251916490002614634994092677190391201143515803077369072946209660522210630068420458851461498679910206300207448283573989539178155168683694739537142312808736136160136837657891750801911178845682591517011199216660229654708118433577766830615013503832*centerUnit,57847881181383156975606268842878388462392490599160782617591286338333503538275783611932977748965824420761304373135943352152179094118874439901873775475532551530577960650219508704972093225530013177174924466052565757132533095056655846155026934736728988762954542454073966524961123200884725185985544831746*centerUnit)

def node14R : ℚ := 3

def node14PBound : ℚ := (18928217584786366026211144489864346394645619323958296113287953240398539164327024494476182509980049175753324042040522878276563389632459503573950310566421295107996235837517624626712127128611520039084514729408975437941077773317611015687837166550028287094546348453900446374599544068227800591763446071378191996995084949273827797647356498359695463967713924514592377837618047511535014472328506317285067541301033571883313401054829917661926759177479442345191621727971037438540093096969884567174035859139011846618076254260090153273627575069478575231156125919752421814642227584417399553401930274816428814299993411566342006188114909013779641593148288825686497448657493442558105849585704109442316682119739621031864857721537391067035758007795978820957789791991049760135651845202599706024164484866094770057/1058791184067875423835403125849552452564239501953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node14PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node14Center (68-j) j
def node14PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node14R (68-j)
def node14HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node14Center (67-j) j
def node14HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node14R (67-j)

theorem node14_norm_upper : |node14Center.1|+|node14Center.2|≤node14R := by decide +kernel
theorem node14_error_nonneg : ∀ j : Fin 69, 0≤node14PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node14R]) _
theorem node14_terminal : |(node14PState 68).1|+|(node14PState 68).2|≤node14PError 68 := by
  simp [node14PState, node14PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node14_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node14Center (node14PState (j+1)) (node14PState j)).1|+
    |(ratResidual (pCoefficient j) node14Center (node14PState (j+1)) (node14PState j)).2|+
    node14R*node14PError (j+1)≤node14PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node14_final : |(node14PState 0).1|+|(node14PState 0).2|+node14PError 0≤node14PBound := by
  decide +kernel
theorem node14_P_value_bound : ‖p67.eval (ratComplex node14Center)‖≤(node14PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node14_norm_upper 68 node14_final

theorem node14_H_error_nonneg : ∀ j : Fin 68,0≤node14HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node14R]) _
theorem node14_H_terminal : |(node14HState 67).1|+|(node14HState 67).2|≤node14HError 67 := by
  simp [node14HState, node14HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node14_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node14Center (node14HState (j.val+1)) (node14HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node14Center (node14HState (j.val+1)) (node14HState j.val)).2|+
    node14R*node14HError (j.val+1)≤node14HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node14_H_value_error :
    ‖h66.eval (ratComplex node14Center)-ratComplex (node14HState 0)‖≤(node14HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node14_norm_upper 67
#print axioms node14_P_value_bound
#print axioms node14_H_value_error

def node15Center : ℚ × ℚ := (935864252254825608035552641557755210844772862319197131657264370080213374611900869619366745480514269087531998484315995901215349418537908284245883260495951515802086940593137655333028295366866183537459999930732575045025071830584081424609591343397490444015712127071851723058217099320008274934062885542383*centerUnit,-148020478269407092888166797600121241270906802999611959459475386776445336007402886566842046512916319447398744500696011436461799404611700627631306222295061603013176229463505811621881040257943764074662501255408674044444794894198015157079125310528962327168604924659266187851671657612430653116784772614852*centerUnit)

def node15R : ℚ := 2

def node15PBound : ℚ := (664298899220223477326236872700144695464901717384053040717959946404577674926981120047172789354184376044199265951632221358524306420186589607998254288684811789203964054615033510082665886292545572254554658267426381108648574876270191730926692458251171890637490466420614909876821677015230257049813738476775295581630427100546564894319899575995110757921176944735784933790315463337834270855436433712703145589824670129553812619404224440164708805745311153382062780476601558760526207855505350022182000900295708948989366740548706122571541116562889411904490789090064670347891273955718267198840976147266953823494969661854056852486237075329142435790115955060772313324597699629626271289496775957486568686442326152186925414092033380904267511363187726706031208761644164702829504632484403883377950082959/135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node15PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node15Center (68-j) j
def node15PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node15R (68-j)
def node15HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node15Center (67-j) j
def node15HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node15R (67-j)

theorem node15_norm_upper : |node15Center.1|+|node15Center.2|≤node15R := by decide +kernel
theorem node15_error_nonneg : ∀ j : Fin 69, 0≤node15PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node15R]) _
theorem node15_terminal : |(node15PState 68).1|+|(node15PState 68).2|≤node15PError 68 := by
  simp [node15PState, node15PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node15_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node15Center (node15PState (j+1)) (node15PState j)).1|+
    |(ratResidual (pCoefficient j) node15Center (node15PState (j+1)) (node15PState j)).2|+
    node15R*node15PError (j+1)≤node15PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node15_final : |(node15PState 0).1|+|(node15PState 0).2|+node15PError 0≤node15PBound := by
  decide +kernel
theorem node15_P_value_bound : ‖p67.eval (ratComplex node15Center)‖≤(node15PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node15_norm_upper 68 node15_final

theorem node15_H_error_nonneg : ∀ j : Fin 68,0≤node15HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node15R]) _
theorem node15_H_terminal : |(node15HState 67).1|+|(node15HState 67).2|≤node15HError 67 := by
  simp [node15HState, node15HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node15_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node15Center (node15HState (j.val+1)) (node15HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node15Center (node15HState (j.val+1)) (node15HState j.val)).2|+
    node15R*node15HError (j.val+1)≤node15HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node15_H_value_error :
    ‖h66.eval (ratComplex node15Center)-ratComplex (node15HState 0)‖≤(node15HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node15_norm_upper 67
#print axioms node15_P_value_bound
#print axioms node15_H_value_error

def node16Center : ℚ × ℚ := (935864252254825608035552641557755210844772862319197131657264370080213374611900869619366745480514269087531998484315995901215349418537908284245883260495951515802086940593137655333028295366866183537459999930732575045025071830584081424609591343397490444015712127071851723058217099320008274934062885542383*centerUnit,148020478269407092888166797600121241270906802999611959459475386776445336007402886566842046512916319447398744500696011436461799404611700627631306222295061603013176229463505811621881040257943764074662501255408674044444794894198015157079125310528962327168604924659266187851671657612430653116784772614851*centerUnit)

def node16R : ℚ := 2

def node16PBound : ℚ := (664298899220223477326236872700144695464901717384053040717959946404577674926981120047172789354184376044199265951632221358524306420186589607998254288684811789203964054615033510082665886292545572254554658267426381108648574876270191730926692458251171890637490466420614909876821677015230257049813738476775295581630427100546564894319899575995110757921176944735784933790315463337834270855436433712703145589824670129553812619404224440164708805745311153382062780476601558760526207855505350022182000900295708948989366740548706122571541116562889411904490789090064670347891273955718267198840976147266953823494969661854056852486237075329142435790115955060772313324597699629626271289496775957486568686442326152186925414092033380904267511363187726706031208761644164702829504632484403883377950082959/135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node16PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node16Center (68-j) j
def node16PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node16R (68-j)
def node16HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node16Center (67-j) j
def node16HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node16R (67-j)

theorem node16_norm_upper : |node16Center.1|+|node16Center.2|≤node16R := by decide +kernel
theorem node16_error_nonneg : ∀ j : Fin 69, 0≤node16PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node16R]) _
theorem node16_terminal : |(node16PState 68).1|+|(node16PState 68).2|≤node16PError 68 := by
  simp [node16PState, node16PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node16_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node16Center (node16PState (j+1)) (node16PState j)).1|+
    |(ratResidual (pCoefficient j) node16Center (node16PState (j+1)) (node16PState j)).2|+
    node16R*node16PError (j+1)≤node16PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node16_final : |(node16PState 0).1|+|(node16PState 0).2|+node16PError 0≤node16PBound := by
  decide +kernel
theorem node16_P_value_bound : ‖p67.eval (ratComplex node16Center)‖≤(node16PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node16_norm_upper 68 node16_final

theorem node16_H_error_nonneg : ∀ j : Fin 68,0≤node16HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node16R]) _
theorem node16_H_terminal : |(node16HState 67).1|+|(node16HState 67).2|≤node16HError 67 := by
  simp [node16HState, node16HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node16_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node16Center (node16HState (j.val+1)) (node16HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node16Center (node16HState (j.val+1)) (node16HState j.val)).2|+
    node16R*node16HError (j.val+1)≤node16HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node16_H_value_error :
    ‖h66.eval (ratComplex node16Center)-ratComplex (node16HState 0)‖≤(node16HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node16_norm_upper 67
#print axioms node16_P_value_bound
#print axioms node16_H_value_error

def node17Center : ℚ × ℚ := (-82681139428326773883862377664610434633198206387849046908397909143308027667006441865647014913562261287255300756387684269936903359092070564907972535879670605256268854210366293461555474357545754512866879786245395283065487916161814227302109852901834723843682785455627304429068258069351104694978925559280*centerUnit,-241958496642011711044279725699188703282706200897791303497093862567385263679962951509231941116471481048115754027092308929723484462439228383811705984883599937224565004977778330806949427292718533401832955405902194399777904637465431818258063505109970246770217998992118308931465164815817687454876218982273*centerUnit)

def node17R : ℚ := 1

def node17PBound : ℚ := (94511920347449101936414384450370458627369228306323170275997730216357663104742432783914235538406060738435215996550014433031311495556610605802210690510110957134193577306466500530643989746612240371409534119369495175619246242465333799375498659760341400140444451892251602235855554524370560535715243686742932466103250901678947828019513220133375612342390343618972825015050622395431841289471159920298990042501872827521836407493302015270123765530348750615074877340166441669889851970936931172912093362547618898230983458840777472094960677825393964715368948905683460784013096245375599720821629370699634124556857407600990685741104593350091504941899030053401679945678152519809603176390586210225092052001388168244604313555113855844326431243521833916145700616363495351898895176863923067997035888291/4336808689942017736029811203479766845703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node17PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node17Center (68-j) j
def node17PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node17R (68-j)
def node17HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node17Center (67-j) j
def node17HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node17R (67-j)

theorem node17_norm_upper : |node17Center.1|+|node17Center.2|≤node17R := by decide +kernel
theorem node17_error_nonneg : ∀ j : Fin 69, 0≤node17PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node17R]) _
theorem node17_terminal : |(node17PState 68).1|+|(node17PState 68).2|≤node17PError 68 := by
  simp [node17PState, node17PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node17_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node17Center (node17PState (j+1)) (node17PState j)).1|+
    |(ratResidual (pCoefficient j) node17Center (node17PState (j+1)) (node17PState j)).2|+
    node17R*node17PError (j+1)≤node17PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node17_final : |(node17PState 0).1|+|(node17PState 0).2|+node17PError 0≤node17PBound := by
  decide +kernel
theorem node17_P_value_bound : ‖p67.eval (ratComplex node17Center)‖≤(node17PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node17_norm_upper 68 node17_final

theorem node17_H_error_nonneg : ∀ j : Fin 68,0≤node17HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node17R]) _
theorem node17_H_terminal : |(node17HState 67).1|+|(node17HState 67).2|≤node17HError 67 := by
  simp [node17HState, node17HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node17_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node17Center (node17HState (j.val+1)) (node17HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node17Center (node17HState (j.val+1)) (node17HState j.val)).2|+
    node17R*node17HError (j.val+1)≤node17HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node17_H_value_error :
    ‖h66.eval (ratComplex node17Center)-ratComplex (node17HState 0)‖≤(node17HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node17_norm_upper 67
#print axioms node17_P_value_bound
#print axioms node17_H_value_error

def node18Center : ℚ × ℚ := (-82681139428326773883862377664610434633198206387849046908397909143308027667006441865647014913562261287255300756387684269936903359092070564907972535879670605256268854210366293461555474357545754512866879786245395283065487916161814227302109852901834723843682785455627304429068258069351104694978925559280*centerUnit,241958496642011711044279725699188703282706200897791303497093862567385263679962951509231941116471481048115754027092308929723484462439228383811705984883599937224565004977778330806949427292718533401832955405902194399777904637465431818258063505109970246770217998992118308931465164815817687454876218982272*centerUnit)

def node18R : ℚ := 1

def node18PBound : ℚ := (94511920347449101936414384450370458627369228306323170275997730216357663104742432783914235538406060738435215996550014433031311495556610605802210690510110957134193577306466500530643989746612240371409534119369495175619246242465333799375498659760341400140444451892251602235855554524370560535715243686742932466103250901678947828019513220133375612342390343618972825015050622395431841289471159920298990042501872827521836407493302015270123765530348750615074877340166441669889851970936931172912093362547618898230983458840777472094960677825393964715368948905683460784013096245375599720821629370699634124556857407600990685741104593350091504941899030053401679945678152519809603176390586210225092052001388168244604313555113855844326431243521833916145700616363495351898895176863923067997035888291/4336808689942017736029811203479766845703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node18PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node18Center (68-j) j
def node18PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node18R (68-j)
def node18HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node18Center (67-j) j
def node18HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node18R (67-j)

theorem node18_norm_upper : |node18Center.1|+|node18Center.2|≤node18R := by decide +kernel
theorem node18_error_nonneg : ∀ j : Fin 69, 0≤node18PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node18R]) _
theorem node18_terminal : |(node18PState 68).1|+|(node18PState 68).2|≤node18PError 68 := by
  simp [node18PState, node18PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node18_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node18Center (node18PState (j+1)) (node18PState j)).1|+
    |(ratResidual (pCoefficient j) node18Center (node18PState (j+1)) (node18PState j)).2|+
    node18R*node18PError (j+1)≤node18PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node18_final : |(node18PState 0).1|+|(node18PState 0).2|+node18PError 0≤node18PBound := by
  decide +kernel
theorem node18_P_value_bound : ‖p67.eval (ratComplex node18Center)‖≤(node18PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node18_norm_upper 68 node18_final

theorem node18_H_error_nonneg : ∀ j : Fin 68,0≤node18HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node18R]) _
theorem node18_H_terminal : |(node18HState 67).1|+|(node18HState 67).2|≤node18HError 67 := by
  simp [node18HState, node18HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node18_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node18Center (node18HState (j.val+1)) (node18HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node18Center (node18HState (j.val+1)) (node18HState j.val)).2|+
    node18R*node18HError (j.val+1)≤node18HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node18_H_value_error :
    ‖h66.eval (ratComplex node18Center)-ratComplex (node18HState 0)‖≤(node18HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node18_norm_upper 67
#print axioms node18_P_value_bound
#print axioms node18_H_value_error

def node19Center : ℚ × ℚ := (314649556417553739003969703109336144132891466624289574167053862041487761921512798743112346973733237498112843204745505574514575515497457156481730854439565925805491653502159305164536035532084140431415995022188063727504429532993623989614096243069639341640918373958772936794043151349150429758467927806462*centerUnit,-283401939228589856006420164379445370740141178105329922520764911618564847778299154258339991289139290179458070918451299092613615477245760956141213178434570502808097553802472831495217726680087504767954562853746786205037370435060495248550963192163097644009469888897544631271193809037896567160951125231070*centerUnit)

def node19R : ℚ := 1

def node19PBound : ℚ := (3765954332780860235750688064806629616126915604574582228419802051505108067324604931079428148199101426453549998394095489197183771162369939398653323995537918146024210084102674147276273290706354863244179594237513638842605431509591105682544906041016671490922420630738646452313941459120132184570077750128369156677773487768354515838200646653059540148126791829455149688275614249479030821406315412902235928627037341436012909234924352549193906311842346515403719290342045389780853408774923178392043938420659568513942662639023435785234637805946653044298614153096044041265046848484643588129791069239531208517998422590078726978122130655333789199740348894300573385700603716571492830179754983703984172213417056818140089189049328526798283169570473210278089019480137530364977859892222136942316371929/1776356839400250464677810668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node19PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node19Center (68-j) j
def node19PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node19R (68-j)
def node19HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node19Center (67-j) j
def node19HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node19R (67-j)

theorem node19_norm_upper : |node19Center.1|+|node19Center.2|≤node19R := by decide +kernel
theorem node19_error_nonneg : ∀ j : Fin 69, 0≤node19PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node19R]) _
theorem node19_terminal : |(node19PState 68).1|+|(node19PState 68).2|≤node19PError 68 := by
  simp [node19PState, node19PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node19_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node19Center (node19PState (j+1)) (node19PState j)).1|+
    |(ratResidual (pCoefficient j) node19Center (node19PState (j+1)) (node19PState j)).2|+
    node19R*node19PError (j+1)≤node19PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node19_final : |(node19PState 0).1|+|(node19PState 0).2|+node19PError 0≤node19PBound := by
  decide +kernel
theorem node19_P_value_bound : ‖p67.eval (ratComplex node19Center)‖≤(node19PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node19_norm_upper 68 node19_final

theorem node19_H_error_nonneg : ∀ j : Fin 68,0≤node19HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node19R]) _
theorem node19_H_terminal : |(node19HState 67).1|+|(node19HState 67).2|≤node19HError 67 := by
  simp [node19HState, node19HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node19_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node19Center (node19HState (j.val+1)) (node19HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node19Center (node19HState (j.val+1)) (node19HState j.val)).2|+
    node19R*node19HError (j.val+1)≤node19HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node19_H_value_error :
    ‖h66.eval (ratComplex node19Center)-ratComplex (node19HState 0)‖≤(node19HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node19_norm_upper 67
#print axioms node19_P_value_bound
#print axioms node19_H_value_error

def node20Center : ℚ × ℚ := (314649556417553739003969703109336144132891466624289574167053862041487761921512798743112346973733237498112843204745505574514575515497457156481730854439565925805491653502159305164536035532084140431415995022188063727504429532993623989614096243069639341640918373958772936794043151349150429758467927806462*centerUnit,283401939228589856006420164379445370740141178105329922520764911618564847778299154258339991289139290179458070918451299092613615477245760956141213178434570502808097553802472831495217726680087504767954562853746786205037370435060495248550963192163097644009469888897544631271193809037896567160951125231069*centerUnit)

def node20R : ℚ := 1

def node20PBound : ℚ := (3765954332780860235750688064806629616126915604574582228419802051505108067324604931079428148199101426453549998394095489197183771162369939398653323995537918146024210084102674147276273290706354863244179594237513638842605431509591105682544906041016671490922420630738646452313941459120132184570077750128369156677773487768354515838200646653059540148126791829455149688275614249479030821406315412902235928627037341436012909234924352549193906311842346515403719290342045389780853408774923178392043938420659568513942662639023435785234637805946653044298614153096044041265046848484643588129791069239531208517998422590078726978122130655333789199740348894300573385700603716571492830179754983703984172213417056818140089189049328526798283169570473210278089019480137530364977859892222136942316371929/1776356839400250464677810668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node20PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node20Center (68-j) j
def node20PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node20R (68-j)
def node20HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node20Center (67-j) j
def node20HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node20R (67-j)

theorem node20_norm_upper : |node20Center.1|+|node20Center.2|≤node20R := by decide +kernel
theorem node20_error_nonneg : ∀ j : Fin 69, 0≤node20PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node20R]) _
theorem node20_terminal : |(node20PState 68).1|+|(node20PState 68).2|≤node20PError 68 := by
  simp [node20PState, node20PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node20_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node20Center (node20PState (j+1)) (node20PState j)).1|+
    |(ratResidual (pCoefficient j) node20Center (node20PState (j+1)) (node20PState j)).2|+
    node20R*node20PError (j+1)≤node20PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node20_final : |(node20PState 0).1|+|(node20PState 0).2|+node20PError 0≤node20PBound := by
  decide +kernel
theorem node20_P_value_bound : ‖p67.eval (ratComplex node20Center)‖≤(node20PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node20_norm_upper 68 node20_final

theorem node20_H_error_nonneg : ∀ j : Fin 68,0≤node20HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node20R]) _
theorem node20_H_terminal : |(node20HState 67).1|+|(node20HState 67).2|≤node20HError 67 := by
  simp [node20HState, node20HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node20_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node20Center (node20HState (j.val+1)) (node20HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node20Center (node20HState (j.val+1)) (node20HState j.val)).2|+
    node20R*node20HError (j.val+1)≤node20HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node20_H_value_error :
    ‖h66.eval (ratComplex node20Center)-ratComplex (node20HState 0)‖≤(node20HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node20_norm_upper 67
#print axioms node20_P_value_bound
#print axioms node20_H_value_error

def node21Center : ℚ × ℚ := (1459090657826412738966220459845120064647833653170073456123896099763913679110711671385015070535254371372412263093957449463182808545632753830310322006483907649479299600487141633148225332186500971206290751649199301966625088078714091072011245178841073382967979471443430819131622897491112065721438781717918*centerUnit,-292207742655665435173922576665133629828748091105159482105766360101331976396652612162806896288621844982474241318284424392747222441771240500045379022896308596401519728373358795001750913968895708891859410034487257945104982323609417152424838268676178284839133882801172834437529849528346278023591078784847*centerUnit)

def node21R : ℚ := 2

def node21PBound : ℚ := (1136064417271149319428072166755862250121437797113422658622625339094216620185698439815934930682282684657251421545314187689967205047824817516119499372745741449201953219624424073993787964810147275131271171750328965484981640406012482524827582706709550794312633745267971192979022383138430900472167048110869423178920807321729062611908086472375421598045453453317344458848019075669298363089370779711643134193585015996431986413950326704685501821459078568266394416797571144505449780196110634667943550001122652441537655229531862588191247401897796754196141542708334864147712492575136394126013330522698110680141985399848889610135760569954598944865268208616811826310762468344230611360598526751178912138223833704544012951435154023231371281109629745231530180616253024637086474808060743676039884001019057472101/355271367880050092935562133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node21PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node21Center (68-j) j
def node21PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node21R (68-j)
def node21HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node21Center (67-j) j
def node21HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node21R (67-j)

theorem node21_norm_upper : |node21Center.1|+|node21Center.2|≤node21R := by decide +kernel
theorem node21_error_nonneg : ∀ j : Fin 69, 0≤node21PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node21R]) _
theorem node21_terminal : |(node21PState 68).1|+|(node21PState 68).2|≤node21PError 68 := by
  simp [node21PState, node21PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node21_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node21Center (node21PState (j+1)) (node21PState j)).1|+
    |(ratResidual (pCoefficient j) node21Center (node21PState (j+1)) (node21PState j)).2|+
    node21R*node21PError (j+1)≤node21PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node21_final : |(node21PState 0).1|+|(node21PState 0).2|+node21PError 0≤node21PBound := by
  decide +kernel
theorem node21_P_value_bound : ‖p67.eval (ratComplex node21Center)‖≤(node21PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node21_norm_upper 68 node21_final

theorem node21_H_error_nonneg : ∀ j : Fin 68,0≤node21HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node21R]) _
theorem node21_H_terminal : |(node21HState 67).1|+|(node21HState 67).2|≤node21HError 67 := by
  simp [node21HState, node21HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node21_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node21Center (node21HState (j.val+1)) (node21HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node21Center (node21HState (j.val+1)) (node21HState j.val)).2|+
    node21R*node21HError (j.val+1)≤node21HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node21_H_value_error :
    ‖h66.eval (ratComplex node21Center)-ratComplex (node21HState 0)‖≤(node21HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node21_norm_upper 67
#print axioms node21_P_value_bound
#print axioms node21_H_value_error

def node22Center : ℚ × ℚ := (1459090657826412738966220459845120064647833653170073456123896099763913679110711671385015070535254371372412263093957449463182808545632753830310322006483907649479299600487141633148225332186500971206290751649199301966625088078714091072011245178841073382967979471443430819131622897491112065721438781717918*centerUnit,292207742655665435173922576665133629828748091105159482105766360101331976396652612162806896288621844982474241318284424392747222441771240500045379022896308596401519728373358795001750913968895708891859410034487257945104982323609417152424838268676178284839133882801172834437529849528346278023591078784846*centerUnit)

def node22R : ℚ := 2

def node22PBound : ℚ := (1136064417271149319428072166755862250121437797113422658622625339094216620185698439815934930682282684657251421545314187689967205047824817516119499372745741449201953219624424073993787964810147275131271171750328965484981640406012482524827582706709550794312633745267971192979022383138430900472167048110869423178920807321729062611908086472375421598045453453317344458848019075669298363089370779711643134193585015996431986413950326704685501821459078568266394416797571144505449780196110634667943550001122652441537655229531862588191247401897796754196141542708334864147712492575136394126013330522698110680141985399848889610135760569954598944865268208616811826310762468344230611360598526751178912138223833704544012951435154023231371281109629745231530180616253024637086474808060743676039884001019057472101/355271367880050092935562133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node22PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node22Center (68-j) j
def node22PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node22R (68-j)
def node22HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node22Center (67-j) j
def node22HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node22R (67-j)

theorem node22_norm_upper : |node22Center.1|+|node22Center.2|≤node22R := by decide +kernel
theorem node22_error_nonneg : ∀ j : Fin 69, 0≤node22PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node22R]) _
theorem node22_terminal : |(node22PState 68).1|+|(node22PState 68).2|≤node22PError 68 := by
  simp [node22PState, node22PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node22_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node22Center (node22PState (j+1)) (node22PState j)).1|+
    |(ratResidual (pCoefficient j) node22Center (node22PState (j+1)) (node22PState j)).2|+
    node22R*node22PError (j+1)≤node22PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node22_final : |(node22PState 0).1|+|(node22PState 0).2|+node22PError 0≤node22PBound := by
  decide +kernel
theorem node22_P_value_bound : ‖p67.eval (ratComplex node22Center)‖≤(node22PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node22_norm_upper 68 node22_final

theorem node22_H_error_nonneg : ∀ j : Fin 68,0≤node22HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node22R]) _
theorem node22_H_terminal : |(node22HState 67).1|+|(node22HState 67).2|≤node22HError 67 := by
  simp [node22HState, node22HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node22_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node22Center (node22HState (j.val+1)) (node22HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node22Center (node22HState (j.val+1)) (node22HState j.val)).2|+
    node22R*node22HError (j.val+1)≤node22HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node22_H_value_error :
    ‖h66.eval (ratComplex node22Center)-ratComplex (node22HState 0)‖≤(node22HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node22_norm_upper 67
#print axioms node22_P_value_bound
#print axioms node22_H_value_error

def node23Center : ℚ × ℚ := (-2323090251338743115611333104703600172639666764477765731678151543612364548564477155576790878245581221885531085076094366146134112832657501745285799832869235912099500398071628862696976743542611142442472528445236244894827023312374503384166429997493924987195320969080544662541097890843994785389089515134157*centerUnit,-335133018596528604069721009574930437205028463448844130827587183805344823986548012237015195337557876449347799457651000351258858199568175536082331675012644514075029672391504461104918474054017968695343634644557813654769174649276991417644823866875932815591685817947280144670016213294154233513977129124393*centerUnit)

def node23R : ℚ := 3

def node23PBound : ℚ := (39503970769231358236834290194138266814072212786224884371884680933820827096363697072235029462680487711475131004527615486141117939866462275077707318093768012863021043224808063229874409464686347619365122333430387018661318476116482474043235387859904722744248422187361507550889347423661363792848718226720525244195865375220626382960089776393848716282064940029584613943018876996133536877000599211133365770770640756134411595652974590998855942000255540322625838069536530649443031308751451414771022221300137643103350554266476821073028191920905298038972318172784463908932458557840714025837811363424842971111435026162144037900766103530766070380146607242466514627226832952094352979649296108987164507502601027391804544585694956027265059199369679862046693087554972260433911971096939522015703332632352831134713808189/710542735760100185871124267578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node23PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node23Center (68-j) j
def node23PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node23R (68-j)
def node23HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node23Center (67-j) j
def node23HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node23R (67-j)

theorem node23_norm_upper : |node23Center.1|+|node23Center.2|≤node23R := by decide +kernel
theorem node23_error_nonneg : ∀ j : Fin 69, 0≤node23PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node23R]) _
theorem node23_terminal : |(node23PState 68).1|+|(node23PState 68).2|≤node23PError 68 := by
  simp [node23PState, node23PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node23_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node23Center (node23PState (j+1)) (node23PState j)).1|+
    |(ratResidual (pCoefficient j) node23Center (node23PState (j+1)) (node23PState j)).2|+
    node23R*node23PError (j+1)≤node23PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node23_final : |(node23PState 0).1|+|(node23PState 0).2|+node23PError 0≤node23PBound := by
  decide +kernel
theorem node23_P_value_bound : ‖p67.eval (ratComplex node23Center)‖≤(node23PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node23_norm_upper 68 node23_final

theorem node23_H_error_nonneg : ∀ j : Fin 68,0≤node23HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node23R]) _
theorem node23_H_terminal : |(node23HState 67).1|+|(node23HState 67).2|≤node23HError 67 := by
  simp [node23HState, node23HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node23_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node23Center (node23HState (j.val+1)) (node23HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node23Center (node23HState (j.val+1)) (node23HState j.val)).2|+
    node23R*node23HError (j.val+1)≤node23HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node23_H_value_error :
    ‖h66.eval (ratComplex node23Center)-ratComplex (node23HState 0)‖≤(node23HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node23_norm_upper 67
#print axioms node23_P_value_bound
#print axioms node23_H_value_error

def node24Center : ℚ × ℚ := (-2323090251338743115611333104703600172639666764477765731678151543612364548564477155576790878245581221885531085076094366146134112832657501745285799832869235912099500398071628862696976743542611142442472528445236244894827023312374503384166429997493924987195320969080544662541097890843994785389089515134157*centerUnit,335133018596528604069721009574930437205028463448844130827587183805344823986548012237015195337557876449347799457651000351258858199568175536082331675012644514075029672391504461104918474054017968695343634644557813654769174649276991417644823866875932815591685817947280144670016213294154233513977129124392*centerUnit)

def node24R : ℚ := 3

def node24PBound : ℚ := (39503970769231358236834290194138266814072212786224884371884680933820827096363697072235029462680487711475131004527615486141117939866462275077707318093768012863021043224808063229874409464686347619365122333430387018661318476116482474043235387859904722744248422187361507550889347423661363792848718226720525244195865375220626382960089776393848716282064940029584613943018876996133536877000599211133365770770640756134411595652974590998855942000255540322625838069536530649443031308751451414771022221300137643103350554266476821073028191920905298038972318172784463908932458557840714025837811363424842971111435026162144037900766103530766070380146607242466514627226832952094352979649296108987164507502601027391804544585694956027265059199369679862046693087554972260433911971096939522015703332632352831134713808189/710542735760100185871124267578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node24PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node24Center (68-j) j
def node24PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node24R (68-j)
def node24HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node24Center (67-j) j
def node24HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node24R (67-j)

theorem node24_norm_upper : |node24Center.1|+|node24Center.2|≤node24R := by decide +kernel
theorem node24_error_nonneg : ∀ j : Fin 69, 0≤node24PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node24R]) _
theorem node24_terminal : |(node24PState 68).1|+|(node24PState 68).2|≤node24PError 68 := by
  simp [node24PState, node24PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node24_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node24Center (node24PState (j+1)) (node24PState j)).1|+
    |(ratResidual (pCoefficient j) node24Center (node24PState (j+1)) (node24PState j)).2|+
    node24R*node24PError (j+1)≤node24PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node24_final : |(node24PState 0).1|+|(node24PState 0).2|+node24PError 0≤node24PBound := by
  decide +kernel
theorem node24_P_value_bound : ‖p67.eval (ratComplex node24Center)‖≤(node24PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node24_norm_upper 68 node24_final

theorem node24_H_error_nonneg : ∀ j : Fin 68,0≤node24HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node24R]) _
theorem node24_H_terminal : |(node24HState 67).1|+|(node24HState 67).2|≤node24HError 67 := by
  simp [node24HState, node24HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node24_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node24Center (node24HState (j.val+1)) (node24HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node24Center (node24HState (j.val+1)) (node24HState j.val)).2|+
    node24R*node24HError (j.val+1)≤node24HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node24_H_value_error :
    ‖h66.eval (ratComplex node24Center)-ratComplex (node24HState 0)‖≤(node24HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node24_norm_upper 67
#print axioms node24_P_value_bound
#print axioms node24_H_value_error

def node25Center : ℚ × ℚ := (1700008659733667206757010618448031894176152385703558013163473492320340943225700037005341366023226223355744984416411509932829437226383313587616699818145063286008923420702621809660508004742949558033890439044100069248603355728395431437827579408647655085226282075947099467418176519304902818168897246306818*centerUnit,-448859489778172043670601233050835525661192057351732055032957114344166866337406960131927880749780753683010630734413282225698308996550295536109992731544181911301520274555326661623887863604274899224484499235475182971068549707265160768000059260882702326540127970621112249778794153703707714285417310084627*centerUnit)

def node25R : ℚ := 3

def node25PBound : ℚ := (104221356713675449450037918417044550018257184200122889527589510870143005083225499593272139068173750817276804419501879225497629022733603790914467229539884498196443524561553606293941230090262254212347996844961047034062489525195352886424885502910738303499335153977430909481535529867801105085724350128564874037905296767066918702957196859556200882932959045981306306984571897774707187906189992608428780764887658908708296111068039761792023821284654794761526948744537609855618849918060753383444677938827901640417623722839116693782380143448090100146128391627372304091636930725809877959808103406600423282689145471631923024536463710964848550497376057654135311646804149802867795221837099329029333658343733577887675202416099838402924689546225733793518414066988639171108250714266491915814040460941793867/271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node25PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node25Center (68-j) j
def node25PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node25R (68-j)
def node25HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node25Center (67-j) j
def node25HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node25R (67-j)

theorem node25_norm_upper : |node25Center.1|+|node25Center.2|≤node25R := by decide +kernel
theorem node25_error_nonneg : ∀ j : Fin 69, 0≤node25PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node25R]) _
theorem node25_terminal : |(node25PState 68).1|+|(node25PState 68).2|≤node25PError 68 := by
  simp [node25PState, node25PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node25_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node25Center (node25PState (j+1)) (node25PState j)).1|+
    |(ratResidual (pCoefficient j) node25Center (node25PState (j+1)) (node25PState j)).2|+
    node25R*node25PError (j+1)≤node25PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node25_final : |(node25PState 0).1|+|(node25PState 0).2|+node25PError 0≤node25PBound := by
  decide +kernel
theorem node25_P_value_bound : ‖p67.eval (ratComplex node25Center)‖≤(node25PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node25_norm_upper 68 node25_final

theorem node25_H_error_nonneg : ∀ j : Fin 68,0≤node25HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node25R]) _
theorem node25_H_terminal : |(node25HState 67).1|+|(node25HState 67).2|≤node25HError 67 := by
  simp [node25HState, node25HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node25_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node25Center (node25HState (j.val+1)) (node25HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node25Center (node25HState (j.val+1)) (node25HState j.val)).2|+
    node25R*node25HError (j.val+1)≤node25HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node25_H_value_error :
    ‖h66.eval (ratComplex node25Center)-ratComplex (node25HState 0)‖≤(node25HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node25_norm_upper 67
#print axioms node25_P_value_bound
#print axioms node25_H_value_error

def node26Center : ℚ × ℚ := (1700008659733667206757010618448031894176152385703558013163473492320340943225700037005341366023226223355744984416411509932829437226383313587616699818145063286008923420702621809660508004742949558033890439044100069248603355728395431437827579408647655085226282075947099467418176519304902818168897246306818*centerUnit,448859489778172043670601233050835525661192057351732055032957114344166866337406960131927880749780753683010630734413282225698308996550295536109992731544181911301520274555326661623887863604274899224484499235475182971068549707265160768000059260882702326540127970621112249778794153703707714285417310084626*centerUnit)

def node26R : ℚ := 3

def node26PBound : ℚ := (104221356713675449450037918417044550018257184200122889527589510870143005083225499593272139068173750817276804419501879225497629022733603790914467229539884498196443524561553606293941230090262254212347996844961047034062489525195352886424885502910738303499335153977430909481535529867801105085724350128564874037905296767066918702957196859556200882932959045981306306984571897774707187906189992608428780764887658908708296111068039761792023821284654794761526948744537609855618849918060753383444677938827901640417623722839116693782380143448090100146128391627372304091636930725809877959808103406600423282689145471631923024536463710964848550497376057654135311646804149802867795221837099329029333658343733577887675202416099838402924689546225733793518414066988639171108250714266491915814040460941793867/271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node26PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node26Center (68-j) j
def node26PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node26R (68-j)
def node26HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node26Center (67-j) j
def node26HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node26R (67-j)

theorem node26_norm_upper : |node26Center.1|+|node26Center.2|≤node26R := by decide +kernel
theorem node26_error_nonneg : ∀ j : Fin 69, 0≤node26PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node26R]) _
theorem node26_terminal : |(node26PState 68).1|+|(node26PState 68).2|≤node26PError 68 := by
  simp [node26PState, node26PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node26_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node26Center (node26PState (j+1)) (node26PState j)).1|+
    |(ratResidual (pCoefficient j) node26Center (node26PState (j+1)) (node26PState j)).2|+
    node26R*node26PError (j+1)≤node26PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node26_final : |(node26PState 0).1|+|(node26PState 0).2|+node26PError 0≤node26PBound := by
  decide +kernel
theorem node26_P_value_bound : ‖p67.eval (ratComplex node26Center)‖≤(node26PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node26_norm_upper 68 node26_final

theorem node26_H_error_nonneg : ∀ j : Fin 68,0≤node26HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node26R]) _
theorem node26_H_terminal : |(node26HState 67).1|+|(node26HState 67).2|≤node26HError 67 := by
  simp [node26HState, node26HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node26_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node26Center (node26HState (j.val+1)) (node26HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node26Center (node26HState (j.val+1)) (node26HState j.val)).2|+
    node26R*node26HError (j.val+1)≤node26HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node26_H_value_error :
    ‖h66.eval (ratComplex node26Center)-ratComplex (node26HState 0)‖≤(node26HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node26_norm_upper 67
#print axioms node26_P_value_bound
#print axioms node26_H_value_error

def node27Center : ℚ × ℚ := (1155290716292923440707012040582988825613508645235277350056185566308658938690502447361492649311156704018909868249833241548739380741970017260247339755581373933546722744959852308388894155729759317949097601933320756127750662487136271276711923841783276334679952012075574928326177245533113040867020828597617*centerUnit,-457688005177931195371964661346774411772545229987512556708913576747542706457050831061434934214344557059487727871422294772786320970405573057082625333359507959931210934256755161522181580269315059835453565548397307636136951077787274081478646073449336370219559701868494475232787318682186312889568343963394*centerUnit)

def node27R : ℚ := 2

def node27PBound : ℚ := (86640256935520133296240845393460201012567628275914140822905223794342077156821886061282978814425501272007839130994971318637899511703186512640995779696395310856544789458148656591098119556820099005011839366946395762233761886038548811369365786506082491783661135061979531647658852385073560313922064088720439865077828839696849534488478167249127823221414758305677727875205061011718791532899216822995619831482042154390365901332506430375198615837119432564545032712841574033272356354484670378164420214821561766407191964855058594041387976217213990634329865300154676719687408331780682276618754867404194845347107409031183301416743104192560785110686795244079814082126020853580679474806014433364612335474313748672508783880823272443091774189967772148909425881807541897529451442408671857580392201459/138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node27PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node27Center (68-j) j
def node27PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node27R (68-j)
def node27HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node27Center (67-j) j
def node27HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node27R (67-j)

theorem node27_norm_upper : |node27Center.1|+|node27Center.2|≤node27R := by decide +kernel
theorem node27_error_nonneg : ∀ j : Fin 69, 0≤node27PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node27R]) _
theorem node27_terminal : |(node27PState 68).1|+|(node27PState 68).2|≤node27PError 68 := by
  simp [node27PState, node27PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node27_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node27Center (node27PState (j+1)) (node27PState j)).1|+
    |(ratResidual (pCoefficient j) node27Center (node27PState (j+1)) (node27PState j)).2|+
    node27R*node27PError (j+1)≤node27PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node27_final : |(node27PState 0).1|+|(node27PState 0).2|+node27PError 0≤node27PBound := by
  decide +kernel
theorem node27_P_value_bound : ‖p67.eval (ratComplex node27Center)‖≤(node27PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node27_norm_upper 68 node27_final

theorem node27_H_error_nonneg : ∀ j : Fin 68,0≤node27HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node27R]) _
theorem node27_H_terminal : |(node27HState 67).1|+|(node27HState 67).2|≤node27HError 67 := by
  simp [node27HState, node27HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node27_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node27Center (node27HState (j.val+1)) (node27HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node27Center (node27HState (j.val+1)) (node27HState j.val)).2|+
    node27R*node27HError (j.val+1)≤node27HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node27_H_value_error :
    ‖h66.eval (ratComplex node27Center)-ratComplex (node27HState 0)‖≤(node27HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node27_norm_upper 67
#print axioms node27_P_value_bound
#print axioms node27_H_value_error

def node28Center : ℚ × ℚ := (1155290716292923440707012040582988825613508645235277350056185566308658938690502447361492649311156704018909868249833241548739380741970017260247339755581373933546722744959852308388894155729759317949097601933320756127750662487136271276711923841783276334679952012075574928326177245533113040867020828597617*centerUnit,457688005177931195371964661346774411772545229987512556708913576747542706457050831061434934214344557059487727871422294772786320970405573057082625333359507959931210934256755161522181580269315059835453565548397307636136951077787274081478646073449336370219559701868494475232787318682186312889568343963393*centerUnit)

def node28R : ℚ := 2

def node28PBound : ℚ := (86640256935520133296240845393460201012567628275914140822905223794342077156821886061282978814425501272007839130994971318637899511703186512640995779696395310856544789458148656591098119556820099005011839366946395762233761886038548811369365786506082491783661135061979531647658852385073560313922064088720439865077828839696849534488478167249127823221414758305677727875205061011718791532899216822995619831482042154390365901332506430375198615837119432564545032712841574033272356354484670378164420214821561766407191964855058594041387976217213990634329865300154676719687408331780682276618754867404194845347107409031183301416743104192560785110686795244079814082126020853580679474806014433364612335474313748672508783880823272443091774189967772148909425881807541897529451442408671857580392201459/138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node28PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node28Center (68-j) j
def node28PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node28R (68-j)
def node28HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node28Center (67-j) j
def node28HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node28R (67-j)

theorem node28_norm_upper : |node28Center.1|+|node28Center.2|≤node28R := by decide +kernel
theorem node28_error_nonneg : ∀ j : Fin 69, 0≤node28PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node28R]) _
theorem node28_terminal : |(node28PState 68).1|+|(node28PState 68).2|≤node28PError 68 := by
  simp [node28PState, node28PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node28_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node28Center (node28PState (j+1)) (node28PState j)).1|+
    |(ratResidual (pCoefficient j) node28Center (node28PState (j+1)) (node28PState j)).2|+
    node28R*node28PError (j+1)≤node28PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node28_final : |(node28PState 0).1|+|(node28PState 0).2|+node28PError 0≤node28PBound := by
  decide +kernel
theorem node28_P_value_bound : ‖p67.eval (ratComplex node28Center)‖≤(node28PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node28_norm_upper 68 node28_final

theorem node28_H_error_nonneg : ∀ j : Fin 68,0≤node28HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node28R]) _
theorem node28_H_terminal : |(node28HState 67).1|+|(node28HState 67).2|≤node28HError 67 := by
  simp [node28HState, node28HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node28_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node28Center (node28HState (j.val+1)) (node28HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node28Center (node28HState (j.val+1)) (node28HState j.val)).2|+
    node28R*node28HError (j.val+1)≤node28HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node28_H_value_error :
    ‖h66.eval (ratComplex node28Center)-ratComplex (node28HState 0)‖≤(node28HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node28_norm_upper 67
#print axioms node28_P_value_bound
#print axioms node28_H_value_error

def node29Center : ℚ × ℚ := (130367047534486416733619663293369373845451276194418056510546684766656484591744660908147050868611788046764715391825936810145204083879730122353288419764143386883028704234968355059241845561264181776049722839315967593548626212023813175845027898305458297317585716951820702986409491395518262988537853933934*centerUnit,-609967220274840538018536149489640971756641828204208972005727377518752786330808861039476123583710751986549205527947008502567250203327433564240269610923360807341315270640284884125581915515074958921872258460434637568794692705436276969141240005185544102255341444915757395266915416109932110407410797983850*centerUnit)

def node29R : ℚ := 1

def node29PBound : ℚ := (2059548866142646152278778021752285932201853685085319840496014217595200192619576126249330415368752610630540752872282469681394792506837712493850784487318365926798155836749767166642786981101259581184240521349787058686404670793960349251330106624047415587730643663850118407757004281369129729678379824621172008847999701898494805201271753777941724673675224134126934270230017022144173537193854985903528275481419984592795018552695884843948053003707691249696131952481958408181196803385749879193693110963093990803093650191454788776899068704272577746870799175523460418114119883781101540943932893919334911491927457843911452025496798023904130375527532959392132576620111030405586725102270541938189236836238357722352960033718279074881565977344861895729678266949251589408436670424614438292415302830523/17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node29PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node29Center (68-j) j
def node29PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node29R (68-j)
def node29HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node29Center (67-j) j
def node29HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node29R (67-j)

theorem node29_norm_upper : |node29Center.1|+|node29Center.2|≤node29R := by decide +kernel
theorem node29_error_nonneg : ∀ j : Fin 69, 0≤node29PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node29R]) _
theorem node29_terminal : |(node29PState 68).1|+|(node29PState 68).2|≤node29PError 68 := by
  simp [node29PState, node29PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node29_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node29Center (node29PState (j+1)) (node29PState j)).1|+
    |(ratResidual (pCoefficient j) node29Center (node29PState (j+1)) (node29PState j)).2|+
    node29R*node29PError (j+1)≤node29PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node29_final : |(node29PState 0).1|+|(node29PState 0).2|+node29PError 0≤node29PBound := by
  decide +kernel
theorem node29_P_value_bound : ‖p67.eval (ratComplex node29Center)‖≤(node29PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node29_norm_upper 68 node29_final

theorem node29_H_error_nonneg : ∀ j : Fin 68,0≤node29HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node29R]) _
theorem node29_H_terminal : |(node29HState 67).1|+|(node29HState 67).2|≤node29HError 67 := by
  simp [node29HState, node29HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node29_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node29Center (node29HState (j.val+1)) (node29HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node29Center (node29HState (j.val+1)) (node29HState j.val)).2|+
    node29R*node29HError (j.val+1)≤node29HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node29_H_value_error :
    ‖h66.eval (ratComplex node29Center)-ratComplex (node29HState 0)‖≤(node29HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node29_norm_upper 67
#print axioms node29_P_value_bound
#print axioms node29_H_value_error

def node30Center : ℚ × ℚ := (130367047534486416733619663293369373845451276194418056510546684766656484591744660908147050868611788046764715391825936810145204083879730122353288419764143386883028704234968355059241845561264181776049722839315967593548626212023813175845027898305458297317585716951820702986409491395518262988537853933934*centerUnit,609967220274840538018536149489640971756641828204208972005727377518752786330808861039476123583710751986549205527947008502567250203327433564240269610923360807341315270640284884125581915515074958921872258460434637568794692705436276969141240005185544102255341444915757395266915416109932110407410797983849*centerUnit)

def node30R : ℚ := 1

def node30PBound : ℚ := (2059548866142646152278778021752285932201853685085319840496014217595200192619576126249330415368752610630540752872282469681394792506837712493850784487318365926798155836749767166642786981101259581184240521349787058686404670793960349251330106624047415587730643663850118407757004281369129729678379824621172008847999701898494805201271753777941724673675224134126934270230017022144173537193854985903528275481419984592795018552695884843948053003707691249696131952481958408181196803385749879193693110963093990803093650191454788776899068704272577746870799175523460418114119883781101540943932893919334911491927457843911452025496798023904130375527532959392132576620111030405586725102270541938189236836238357722352960033718279074881565977344861895729678266949251589408436670424614438292415302830523/17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node30PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node30Center (68-j) j
def node30PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node30R (68-j)
def node30HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node30Center (67-j) j
def node30HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node30R (67-j)

theorem node30_norm_upper : |node30Center.1|+|node30Center.2|≤node30R := by decide +kernel
theorem node30_error_nonneg : ∀ j : Fin 69, 0≤node30PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node30R]) _
theorem node30_terminal : |(node30PState 68).1|+|(node30PState 68).2|≤node30PError 68 := by
  simp [node30PState, node30PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node30_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node30Center (node30PState (j+1)) (node30PState j)).1|+
    |(ratResidual (pCoefficient j) node30Center (node30PState (j+1)) (node30PState j)).2|+
    node30R*node30PError (j+1)≤node30PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node30_final : |(node30PState 0).1|+|(node30PState 0).2|+node30PError 0≤node30PBound := by
  decide +kernel
theorem node30_P_value_bound : ‖p67.eval (ratComplex node30Center)‖≤(node30PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node30_norm_upper 68 node30_final

theorem node30_H_error_nonneg : ∀ j : Fin 68,0≤node30HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node30R]) _
theorem node30_H_terminal : |(node30HState 67).1|+|(node30HState 67).2|≤node30HError 67 := by
  simp [node30HState, node30HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node30_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node30Center (node30HState (j.val+1)) (node30HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node30Center (node30HState (j.val+1)) (node30HState j.val)).2|+
    node30R*node30HError (j.val+1)≤node30HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node30_H_value_error :
    ‖h66.eval (ratComplex node30Center)-ratComplex (node30HState 0)‖≤(node30HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node30_norm_upper 67
#print axioms node30_P_value_bound
#print axioms node30_H_value_error

def node31Center : ℚ × ℚ := (277371967835046195849407528644738815215586378090934179333464892092863181725784684005468191422342957948112624134359436343167541098104355185415012694485223112157469317134343862443482700322331334213698680767675815925148917233917201609360567140089883073624346720264014691944188688612374877151647687973148*centerUnit,-688031376987506088107727804783180996586604885261309816995710276382947398966447320972465848720942096306618685457469918268450974530219991463619008781556543196750343995549636581022698121800839526502076044058421709598979083788684132726836999267573025807023151359358840230095344113636294136023200960757352*centerUnit)

def node31R : ℚ := 1

def node31PBound : ℚ := (47586412702689167965141552621292646259415336494058024870207922821557746527036192224355881804990006284508547430640366742634221620614394248398626437897112554097917519816675076456958422803697337774064927289494799548324051711455939143741580360844956664947618349055052296927767332144431647523799044860962661814687245493870394956699416079874066253477862293751045625306010757660951081785869493522571348248128224667305659247321639032507781079467243733655908681175907432553953908253759285383093182781174628498613872185952627074163183455816725931476767870750729768892608632728568626544608427734038251846792102693257705790816306369082730831522659145407895604579457807268874627862683892776746392943131210417760321367142708742223521213524492943999321404343450753025868970668115569908049845665981739/177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node31PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node31Center (68-j) j
def node31PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node31R (68-j)
def node31HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node31Center (67-j) j
def node31HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node31R (67-j)

theorem node31_norm_upper : |node31Center.1|+|node31Center.2|≤node31R := by decide +kernel
theorem node31_error_nonneg : ∀ j : Fin 69, 0≤node31PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node31R]) _
theorem node31_terminal : |(node31PState 68).1|+|(node31PState 68).2|≤node31PError 68 := by
  simp [node31PState, node31PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node31_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node31Center (node31PState (j+1)) (node31PState j)).1|+
    |(ratResidual (pCoefficient j) node31Center (node31PState (j+1)) (node31PState j)).2|+
    node31R*node31PError (j+1)≤node31PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node31_final : |(node31PState 0).1|+|(node31PState 0).2|+node31PError 0≤node31PBound := by
  decide +kernel
theorem node31_P_value_bound : ‖p67.eval (ratComplex node31Center)‖≤(node31PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node31_norm_upper 68 node31_final

theorem node31_H_error_nonneg : ∀ j : Fin 68,0≤node31HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node31R]) _
theorem node31_H_terminal : |(node31HState 67).1|+|(node31HState 67).2|≤node31HError 67 := by
  simp [node31HState, node31HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node31_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node31Center (node31HState (j.val+1)) (node31HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node31Center (node31HState (j.val+1)) (node31HState j.val)).2|+
    node31R*node31HError (j.val+1)≤node31HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node31_H_value_error :
    ‖h66.eval (ratComplex node31Center)-ratComplex (node31HState 0)‖≤(node31HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node31_norm_upper 67
#print axioms node31_P_value_bound
#print axioms node31_H_value_error

def node32Center : ℚ × ℚ := (277371967835046195849407528644738815215586378090934179333464892092863181725784684005468191422342957948112624134359436343167541098104355185415012694485223112157469317134343862443482700322331334213698680767675815925148917233917201609360567140089883073624346720264014691944188688612374877151647687973148*centerUnit,688031376987506088107727804783180996586604885261309816995710276382947398966447320972465848720942096306618685457469918268450974530219991463619008781556543196750343995549636581022698121800839526502076044058421709598979083788684132726836999267573025807023151359358840230095344113636294136023200960757351*centerUnit)

def node32R : ℚ := 1

def node32PBound : ℚ := (47586412702689167965141552621292646259415336494058024870207922821557746527036192224355881804990006284508547430640366742634221620614394248398626437897112554097917519816675076456958422803697337774064927289494799548324051711455939143741580360844956664947618349055052296927767332144431647523799044860962661814687245493870394956699416079874066253477862293751045625306010757660951081785869493522571348248128224667305659247321639032507781079467243733655908681175907432553953908253759285383093182781174628498613872185952627074163183455816725931476767870750729768892608632728568626544608427734038251846792102693257705790816306369082730831522659145407895604579457807268874627862683892776746392943131210417760321367142708742223521213524492943999321404343450753025868970668115569908049845665981739/177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node32PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node32Center (68-j) j
def node32PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node32R (68-j)
def node32HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node32Center (67-j) j
def node32HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node32R (67-j)

theorem node32_norm_upper : |node32Center.1|+|node32Center.2|≤node32R := by decide +kernel
theorem node32_error_nonneg : ∀ j : Fin 69, 0≤node32PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node32R]) _
theorem node32_terminal : |(node32PState 68).1|+|(node32PState 68).2|≤node32PError 68 := by
  simp [node32PState, node32PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node32_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node32Center (node32PState (j+1)) (node32PState j)).1|+
    |(ratResidual (pCoefficient j) node32Center (node32PState (j+1)) (node32PState j)).2|+
    node32R*node32PError (j+1)≤node32PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node32_final : |(node32PState 0).1|+|(node32PState 0).2|+node32PError 0≤node32PBound := by
  decide +kernel
theorem node32_P_value_bound : ‖p67.eval (ratComplex node32Center)‖≤(node32PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node32_norm_upper 68 node32_final

theorem node32_H_error_nonneg : ∀ j : Fin 68,0≤node32HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node32R]) _
theorem node32_H_terminal : |(node32HState 67).1|+|(node32HState 67).2|≤node32HError 67 := by
  simp [node32HState, node32HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node32_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node32Center (node32HState (j.val+1)) (node32HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node32Center (node32HState (j.val+1)) (node32HState j.val)).2|+
    node32R*node32HError (j.val+1)≤node32HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node32_H_value_error :
    ‖h66.eval (ratComplex node32Center)-ratComplex (node32HState 0)‖≤(node32HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node32_norm_upper 67
#print axioms node32_P_value_bound
#print axioms node32_H_value_error

def node33Center : ℚ × ℚ := (-1812117798648562677406838156846644683752035433514087348824770691121277970195574773092813205643071106175623168045789387401697378671477869525881004245791130449072921259052633683295694449251413073035577312735465014355596433566220064144079719104073454332993145179629662358125734866533674216878737026007036*centerUnit,-726642835897938445403494747300427423266323690177599712132269193642150466173525207273817422828849510763061706647275146901278918636936258653367747860348400179343381257485416604158581509253984456706692657087122118055086974067619319536162917346932930171815407888244330887482701096396135583239748590389040*centerUnit)

def node33R : ℚ := 3

def node33PBound : ℚ := (1041390126725737629118374439830932035161814799902983760702714376904415608509687642259408179132662376339666752792073300963716920865342731877898013628258120058483094501369088688303373814846598628973777447626625570722454952157041973587178626728033655547904521189885962877951239390383067703173565782311920732789340468461889411981704807053601709184071348310671122842848000077558947760865720128454304799563632203129419504752994243263050671546305190508364803162885198595679829999901521339788183180210167973404011587769015510929534651606909915134792975150643089548833369829382293976346761180541021162243434864537591704019457655494726643067112917545022039176507546645955102679357098460156005361686062929936022630734520566131709132763860252638990686505260359069045385904505130986074904435518206723108839442081501/2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node33PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node33Center (68-j) j
def node33PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node33R (68-j)
def node33HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node33Center (67-j) j
def node33HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node33R (67-j)

theorem node33_norm_upper : |node33Center.1|+|node33Center.2|≤node33R := by decide +kernel
theorem node33_error_nonneg : ∀ j : Fin 69, 0≤node33PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node33R]) _
theorem node33_terminal : |(node33PState 68).1|+|(node33PState 68).2|≤node33PError 68 := by
  simp [node33PState, node33PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node33_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node33Center (node33PState (j+1)) (node33PState j)).1|+
    |(ratResidual (pCoefficient j) node33Center (node33PState (j+1)) (node33PState j)).2|+
    node33R*node33PError (j+1)≤node33PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node33_final : |(node33PState 0).1|+|(node33PState 0).2|+node33PError 0≤node33PBound := by
  decide +kernel
theorem node33_P_value_bound : ‖p67.eval (ratComplex node33Center)‖≤(node33PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node33_norm_upper 68 node33_final

theorem node33_H_error_nonneg : ∀ j : Fin 68,0≤node33HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node33R]) _
theorem node33_H_terminal : |(node33HState 67).1|+|(node33HState 67).2|≤node33HError 67 := by
  simp [node33HState, node33HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node33_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node33Center (node33HState (j.val+1)) (node33HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node33Center (node33HState (j.val+1)) (node33HState j.val)).2|+
    node33R*node33HError (j.val+1)≤node33HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node33_H_value_error :
    ‖h66.eval (ratComplex node33Center)-ratComplex (node33HState 0)‖≤(node33HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node33_norm_upper 67
#print axioms node33_P_value_bound
#print axioms node33_H_value_error

def node34Center : ℚ × ℚ := (-1812117798648562677406838156846644683752035433514087348824770691121277970195574773092813205643071106175623168045789387401697378671477869525881004245791130449072921259052633683295694449251413073035577312735465014355596433566220064144079719104073454332993145179629662358125734866533674216878737026007036*centerUnit,726642835897938445403494747300427423266323690177599712132269193642150466173525207273817422828849510763061706647275146901278918636936258653367747860348400179343381257485416604158581509253984456706692657087122118055086974067619319536162917346932930171815407888244330887482701096396135583239748590389039*centerUnit)

def node34R : ℚ := 3

def node34PBound : ℚ := (1041390126725737629118374439830932035161814799902983760702714376904415608509687642259408179132662376339666752792073300963716920865342731877898013628258120058483094501369088688303373814846598628973777447626625570722454952157041973587178626728033655547904521189885962877951239390383067703173565782311920732789340468461889411981704807053601709184071348310671122842848000077558947760865720128454304799563632203129419504752994243263050671546305190508364803162885198595679829999901521339788183180210167973404011587769015510929534651606909915134792975150643089548833369829382293976346761180541021162243434864537591704019457655494726643067112917545022039176507546645955102679357098460156005361686062929936022630734520566131709132763860252638990686505260359069045385904505130986074904435518206723108839442081501/2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node34PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node34Center (68-j) j
def node34PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node34R (68-j)
def node34HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node34Center (67-j) j
def node34HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node34R (67-j)

theorem node34_norm_upper : |node34Center.1|+|node34Center.2|≤node34R := by decide +kernel
theorem node34_error_nonneg : ∀ j : Fin 69, 0≤node34PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node34R]) _
theorem node34_terminal : |(node34PState 68).1|+|(node34PState 68).2|≤node34PError 68 := by
  simp [node34PState, node34PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node34_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node34Center (node34PState (j+1)) (node34PState j)).1|+
    |(ratResidual (pCoefficient j) node34Center (node34PState (j+1)) (node34PState j)).2|+
    node34R*node34PError (j+1)≤node34PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node34_final : |(node34PState 0).1|+|(node34PState 0).2|+node34PError 0≤node34PBound := by
  decide +kernel
theorem node34_P_value_bound : ‖p67.eval (ratComplex node34Center)‖≤(node34PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node34_norm_upper 68 node34_final

theorem node34_H_error_nonneg : ∀ j : Fin 68,0≤node34HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node34R]) _
theorem node34_H_terminal : |(node34HState 67).1|+|(node34HState 67).2|≤node34HError 67 := by
  simp [node34HState, node34HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node34_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node34Center (node34HState (j.val+1)) (node34HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node34Center (node34HState (j.val+1)) (node34HState j.val)).2|+
    node34R*node34HError (j.val+1)≤node34HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node34_H_value_error :
    ‖h66.eval (ratComplex node34Center)-ratComplex (node34HState 0)‖≤(node34HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node34_norm_upper 67
#print axioms node34_P_value_bound
#print axioms node34_H_value_error

def node35Center : ℚ × ℚ := (-1425219908764927141679988733000177649366945292411719633963733873083168664790713708763205993551954446287375251473084701631342653771440033597349543314770632510463752015570602493864640583714247547341068921261371138221141137213924166969446274099521010277888453480918846407608813687130297018219559996819285*centerUnit,-746595419984176814637704455913591260688952462438437881070281972421867063842973520400402347242367462918215538026178490118283565163799693546534836835461248527922495914115665791259261179494020105232950301831657844656842044766930145694329706921982049725019276030351058816488793843351360899479273941480218*centerUnit)

def node35R : ℚ := 3

def node35PBound : ℚ := (12905239595575546528863861499699584266834156897599242564665479052784468940541251018479674605160845972555129867207408433584827929735189289271398521457437784209306850144287720662286374095284487045754897913408350345249573604474063727412749335924359914698003595126860288124393622933478404966622358036899447060973026725247920115314752960171567222423513723822614619966620620622107974371462445792117186623425286828634918177693692530488565008274646524529576434394356001246605724680121021092269177752498478266685826632330595239473867122301265147799005372140705672467306350595594943067790274882189319405043101421491672677039984867747947061440001323733486696331606068841320135881627383390439261144555906322078327311722146834312738081149320883714750762355335712874225179106241395906209097601754271675349690900929/2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node35PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node35Center (68-j) j
def node35PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node35R (68-j)
def node35HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node35Center (67-j) j
def node35HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node35R (67-j)

theorem node35_norm_upper : |node35Center.1|+|node35Center.2|≤node35R := by decide +kernel
theorem node35_error_nonneg : ∀ j : Fin 69, 0≤node35PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node35R]) _
theorem node35_terminal : |(node35PState 68).1|+|(node35PState 68).2|≤node35PError 68 := by
  simp [node35PState, node35PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node35_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node35Center (node35PState (j+1)) (node35PState j)).1|+
    |(ratResidual (pCoefficient j) node35Center (node35PState (j+1)) (node35PState j)).2|+
    node35R*node35PError (j+1)≤node35PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node35_final : |(node35PState 0).1|+|(node35PState 0).2|+node35PError 0≤node35PBound := by
  decide +kernel
theorem node35_P_value_bound : ‖p67.eval (ratComplex node35Center)‖≤(node35PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node35_norm_upper 68 node35_final

theorem node35_H_error_nonneg : ∀ j : Fin 68,0≤node35HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node35R]) _
theorem node35_H_terminal : |(node35HState 67).1|+|(node35HState 67).2|≤node35HError 67 := by
  simp [node35HState, node35HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node35_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node35Center (node35HState (j.val+1)) (node35HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node35Center (node35HState (j.val+1)) (node35HState j.val)).2|+
    node35R*node35HError (j.val+1)≤node35HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node35_H_value_error :
    ‖h66.eval (ratComplex node35Center)-ratComplex (node35HState 0)‖≤(node35HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node35_norm_upper 67
#print axioms node35_P_value_bound
#print axioms node35_H_value_error

def node36Center : ℚ × ℚ := (-1425219908764927141679988733000177649366945292411719633963733873083168664790713708763205993551954446287375251473084701631342653771440033597349543314770632510463752015570602493864640583714247547341068921261371138221141137213924166969446274099521010277888453480918846407608813687130297018219559996819285*centerUnit,746595419984176814637704455913591260688952462438437881070281972421867063842973520400402347242367462918215538026178490118283565163799693546534836835461248527922495914115665791259261179494020105232950301831657844656842044766930145694329706921982049725019276030351058816488793843351360899479273941480217*centerUnit)

def node36R : ℚ := 3

def node36PBound : ℚ := (12905239595575546528863861499699584266834156897599242564665479052784468940541251018479674605160845972555129867207408433584827929735189289271398521457437784209306850144287720662286374095284487045754897913408350345249573604474063727412749335924359914698003595126860288124393622933478404966622358036899447060973026725247920115314752960171567222423513723822614619966620620622107974371462445792117186623425286828634918177693692530488565008274646524529576434394356001246605724680121021092269177752498478266685826632330595239473867122301265147799005372140705672467306350595594943067790274882189319405043101421491672677039984867747947061440001323733486696331606068841320135881627383390439261144555906322078327311722146834312738081149320883714750762355335712874225179106241395906209097601754271675349690900929/2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node36PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node36Center (68-j) j
def node36PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node36R (68-j)
def node36HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node36Center (67-j) j
def node36HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node36R (67-j)

theorem node36_norm_upper : |node36Center.1|+|node36Center.2|≤node36R := by decide +kernel
theorem node36_error_nonneg : ∀ j : Fin 69, 0≤node36PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node36R]) _
theorem node36_terminal : |(node36PState 68).1|+|(node36PState 68).2|≤node36PError 68 := by
  simp [node36PState, node36PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node36_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node36Center (node36PState (j+1)) (node36PState j)).1|+
    |(ratResidual (pCoefficient j) node36Center (node36PState (j+1)) (node36PState j)).2|+
    node36R*node36PError (j+1)≤node36PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node36_final : |(node36PState 0).1|+|(node36PState 0).2|+node36PError 0≤node36PBound := by
  decide +kernel
theorem node36_P_value_bound : ‖p67.eval (ratComplex node36Center)‖≤(node36PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node36_norm_upper 68 node36_final

theorem node36_H_error_nonneg : ∀ j : Fin 68,0≤node36HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node36R]) _
theorem node36_H_terminal : |(node36HState 67).1|+|(node36HState 67).2|≤node36HError 67 := by
  simp [node36HState, node36HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node36_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node36Center (node36HState (j.val+1)) (node36HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node36Center (node36HState (j.val+1)) (node36HState j.val)).2|+
    node36R*node36HError (j.val+1)≤node36HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node36_H_value_error :
    ‖h66.eval (ratComplex node36Center)-ratComplex (node36HState 0)‖≤(node36HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node36_norm_upper 67
#print axioms node36_P_value_bound
#print axioms node36_H_value_error

def node37Center : ℚ × ℚ := (-365656132485667701403874058301717741213714184205478552477587177760779295237767954633487495656688153353275427134110330729637908136949502172497243777427018796671884957775646507301420528674040187116154594422694506899485461295798567537547930245236719828458404303128592961576895487005880603047981929663476*centerUnit,-970546804536678871728430539484087679530679637159146746177950400277441069502616605349264488120645389653987911698659306249483811371579450089684979996803057782401269109883120964443959751014080981372284079656586972810800374767450322077355911708866932337126558143352589519774632414614871750644614251145581*centerUnit)

def node37R : ℚ := 2

def node37PBound : ℚ := (17646670980848647245913961733000116675421430180257409216789143058789274857010760816451990510244132896442493547114229515990272428050910001881622068921556856809793354434508211090350269439412412893886928978366975485796843069276126132738121804275209248377101303799761683824371611604041045547357747527300917060427014176356255843513556209555326514400191959650148844787544107348437683208417231375957931490310285921492754650273504052192046512228006732811057828736155578611151814311227892976174044213838975698779173512105102066572866883474216153496175258111309859427101816396275776372783313085576231868803946250569569215278346854845623350129060846832966205822020261817396046821704606768216067565203767035957550001686687824369994068283079189636030132502919383247721936185791880002907689409518612081/43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node37PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node37Center (68-j) j
def node37PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node37R (68-j)
def node37HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node37Center (67-j) j
def node37HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node37R (67-j)

theorem node37_norm_upper : |node37Center.1|+|node37Center.2|≤node37R := by decide +kernel
theorem node37_error_nonneg : ∀ j : Fin 69, 0≤node37PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node37R]) _
theorem node37_terminal : |(node37PState 68).1|+|(node37PState 68).2|≤node37PError 68 := by
  simp [node37PState, node37PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node37_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node37Center (node37PState (j+1)) (node37PState j)).1|+
    |(ratResidual (pCoefficient j) node37Center (node37PState (j+1)) (node37PState j)).2|+
    node37R*node37PError (j+1)≤node37PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node37_final : |(node37PState 0).1|+|(node37PState 0).2|+node37PError 0≤node37PBound := by
  decide +kernel
theorem node37_P_value_bound : ‖p67.eval (ratComplex node37Center)‖≤(node37PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node37_norm_upper 68 node37_final

theorem node37_H_error_nonneg : ∀ j : Fin 68,0≤node37HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node37R]) _
theorem node37_H_terminal : |(node37HState 67).1|+|(node37HState 67).2|≤node37HError 67 := by
  simp [node37HState, node37HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node37_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node37Center (node37HState (j.val+1)) (node37HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node37Center (node37HState (j.val+1)) (node37HState j.val)).2|+
    node37R*node37HError (j.val+1)≤node37HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node37_H_value_error :
    ‖h66.eval (ratComplex node37Center)-ratComplex (node37HState 0)‖≤(node37HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node37_norm_upper 67
#print axioms node37_P_value_bound
#print axioms node37_H_value_error

def node38Center : ℚ × ℚ := (-365656132485667701403874058301717741213714184205478552477587177760779295237767954633487495656688153353275427134110330729637908136949502172497243777427018796671884957775646507301420528674040187116154594422694506899485461295798567537547930245236719828458404303128592961576895487005880603047981929663476*centerUnit,970546804536678871728430539484087679530679637159146746177950400277441069502616605349264488120645389653987911698659306249483811371579450089684979996803057782401269109883120964443959751014080981372284079656586972810800374767450322077355911708866932337126558143352589519774632414614871750644614251145580*centerUnit)

def node38R : ℚ := 2

def node38PBound : ℚ := (17646670980848647245913961733000116675421430180257409216789143058789274857010760816451990510244132896442493547114229515990272428050910001881622068921556856809793354434508211090350269439412412893886928978366975485796843069276126132738121804275209248377101303799761683824371611604041045547357747527300917060427014176356255843513556209555326514400191959650148844787544107348437683208417231375957931490310285921492754650273504052192046512228006732811057828736155578611151814311227892976174044213838975698779173512105102066572866883474216153496175258111309859427101816396275776372783313085576231868803946250569569215278346854845623350129060846832966205822020261817396046821704606768216067565203767035957550001686687824369994068283079189636030132502919383247721936185791880002907689409518612081/43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node38PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node38Center (68-j) j
def node38PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node38R (68-j)
def node38HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node38Center (67-j) j
def node38HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node38R (67-j)

theorem node38_norm_upper : |node38Center.1|+|node38Center.2|≤node38R := by decide +kernel
theorem node38_error_nonneg : ∀ j : Fin 69, 0≤node38PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node38R]) _
theorem node38_terminal : |(node38PState 68).1|+|(node38PState 68).2|≤node38PError 68 := by
  simp [node38PState, node38PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node38_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node38Center (node38PState (j+1)) (node38PState j)).1|+
    |(ratResidual (pCoefficient j) node38Center (node38PState (j+1)) (node38PState j)).2|+
    node38R*node38PError (j+1)≤node38PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node38_final : |(node38PState 0).1|+|(node38PState 0).2|+node38PError 0≤node38PBound := by
  decide +kernel
theorem node38_P_value_bound : ‖p67.eval (ratComplex node38Center)‖≤(node38PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node38_norm_upper 68 node38_final

theorem node38_H_error_nonneg : ∀ j : Fin 68,0≤node38HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node38R]) _
theorem node38_H_terminal : |(node38HState 67).1|+|(node38HState 67).2|≤node38HError 67 := by
  simp [node38HState, node38HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node38_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node38Center (node38HState (j.val+1)) (node38HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node38Center (node38HState (j.val+1)) (node38HState j.val)).2|+
    node38R*node38HError (j.val+1)≤node38HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node38_H_value_error :
    ‖h66.eval (ratComplex node38Center)-ratComplex (node38HState 0)‖≤(node38HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node38_norm_upper 67
#print axioms node38_P_value_bound
#print axioms node38_H_value_error

def node39Center : ℚ × ℚ := (1518082542057473967009433059625812807288300181387692464748474041856710124916294561878088746349957810025185974136065568730958629909872313990496547238667770746292027108817725833611315275656563401453322924216881866450627236890681229896535465930100019452909919618805592765200895701405764875167541516205647*centerUnit,-1260815629554360893112736501590816256358441659429224697150795537387691671695560484310738444855785111464275014237053812403437152982546132553907951172270492657925708213163639108429894725550068294536384026802581859503275571725298930070740370579698792365362574220289834461613476025282257712744628150831335*centerUnit)

def node39R : ℚ := 3

def node39PBound : ℚ := (9616852539327102084515428370936231555676359241987334527541408933335234847375477029884945561802260551977482626544222228189473548016072372946690504568017113474077597355655404963953841785869115282192054838417732894920516645772484228196242423721256822914744582488562134545425575132006706421560771746488364076211427885760177260048922467287971662706162763071327897158595205784651241236761999350098013053069538985814970110111644173340276630637221666072237058638423518162729887066134186739863848670443783816220632467932338496924411472344543924877790284351826499889640872529993874728617412414324361788233453366444293387160893444162697743452145206946839718746936880865801057327546982445954601625885657234862013651481643833890615776874292999264456309763084985321059220442288118195814470460331380016620427/5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node39PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node39Center (68-j) j
def node39PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node39R (68-j)
def node39HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node39Center (67-j) j
def node39HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node39R (67-j)

theorem node39_norm_upper : |node39Center.1|+|node39Center.2|≤node39R := by decide +kernel
theorem node39_error_nonneg : ∀ j : Fin 69, 0≤node39PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node39R]) _
theorem node39_terminal : |(node39PState 68).1|+|(node39PState 68).2|≤node39PError 68 := by
  simp [node39PState, node39PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node39_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node39Center (node39PState (j+1)) (node39PState j)).1|+
    |(ratResidual (pCoefficient j) node39Center (node39PState (j+1)) (node39PState j)).2|+
    node39R*node39PError (j+1)≤node39PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node39_final : |(node39PState 0).1|+|(node39PState 0).2|+node39PError 0≤node39PBound := by
  decide +kernel
theorem node39_P_value_bound : ‖p67.eval (ratComplex node39Center)‖≤(node39PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node39_norm_upper 68 node39_final

theorem node39_H_error_nonneg : ∀ j : Fin 68,0≤node39HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node39R]) _
theorem node39_H_terminal : |(node39HState 67).1|+|(node39HState 67).2|≤node39HError 67 := by
  simp [node39HState, node39HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node39_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node39Center (node39HState (j.val+1)) (node39HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node39Center (node39HState (j.val+1)) (node39HState j.val)).2|+
    node39R*node39HError (j.val+1)≤node39HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node39_H_value_error :
    ‖h66.eval (ratComplex node39Center)-ratComplex (node39HState 0)‖≤(node39HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node39_norm_upper 67
#print axioms node39_P_value_bound
#print axioms node39_H_value_error

def node40Center : ℚ × ℚ := (1518082542057473967009433059625812807288300181387692464748474041856710124916294561878088746349957810025185974136065568730958629909872313990496547238667770746292027108817725833611315275656563401453322924216881866450627236890681229896535465930100019452909919618805592765200895701405764875167541516205647*centerUnit,1260815629554360893112736501590816256358441659429224697150795537387691671695560484310738444855785111464275014237053812403437152982546132553907951172270492657925708213163639108429894725550068294536384026802581859503275571725298930070740370579698792365362574220289834461613476025282257712744628150831334*centerUnit)

def node40R : ℚ := 3

def node40PBound : ℚ := (9616852539327102084515428370936231555676359241987334527541408933335234847375477029884945561802260551977482626544222228189473548016072372946690504568017113474077597355655404963953841785869115282192054838417732894920516645772484228196242423721256822914744582488562134545425575132006706421560771746488364076211427885760177260048922467287971662706162763071327897158595205784651241236761999350098013053069538985814970110111644173340276630637221666072237058638423518162729887066134186739863848670443783816220632467932338496924411472344543924877790284351826499889640872529993874728617412414324361788233453366444293387160893444162697743452145206946839718746936880865801057327546982445954601625885657234862013651481643833890615776874292999264456309763084985321059220442288118195814470460331380016620427/5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node40PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node40Center (68-j) j
def node40PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node40R (68-j)
def node40HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node40Center (67-j) j
def node40HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node40R (67-j)

theorem node40_norm_upper : |node40Center.1|+|node40Center.2|≤node40R := by decide +kernel
theorem node40_error_nonneg : ∀ j : Fin 69, 0≤node40PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node40R]) _
theorem node40_terminal : |(node40PState 68).1|+|(node40PState 68).2|≤node40PError 68 := by
  simp [node40PState, node40PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node40_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node40Center (node40PState (j+1)) (node40PState j)).1|+
    |(ratResidual (pCoefficient j) node40Center (node40PState (j+1)) (node40PState j)).2|+
    node40R*node40PError (j+1)≤node40PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node40_final : |(node40PState 0).1|+|(node40PState 0).2|+node40PError 0≤node40PBound := by
  decide +kernel
theorem node40_P_value_bound : ‖p67.eval (ratComplex node40Center)‖≤(node40PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node40_norm_upper 68 node40_final

theorem node40_H_error_nonneg : ∀ j : Fin 68,0≤node40HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node40R]) _
theorem node40_H_terminal : |(node40HState 67).1|+|(node40HState 67).2|≤node40HError 67 := by
  simp [node40HState, node40HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node40_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node40Center (node40HState (j.val+1)) (node40HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node40Center (node40HState (j.val+1)) (node40HState j.val)).2|+
    node40R*node40HError (j.val+1)≤node40HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node40_H_value_error :
    ‖h66.eval (ratComplex node40Center)-ratComplex (node40HState 0)‖≤(node40HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node40_norm_upper 67
#print axioms node40_P_value_bound
#print axioms node40_H_value_error

def node41Center : ℚ × ℚ := (-1294444551659494083696930584047964562717822186245522227333595667976292847073251569551072946354926451180374876891005427290882149849054609557934204576181429175812027514814294753039258717257570016982690097118361490350270349150360039505914164077166876788587401544124122843164563181556387468859398704491283*centerUnit,-1658145549429960328278192299429566840503982909864713281818881653287921167310563671603359543809381354392156510136936137201835098284331278610879326548291972198700571064171103123994272195400272970724967041433615045951047696421657503268231240343739862434777927892318799851331013439331547089000622947851488*centerUnit)

def node41R : ℚ := 3

def node41PBound : ℚ := (1434984343336569026606068454742620216264492207085230885747596337432219183911105637350487392791206856328501852419156145816336862433352122583974804265090939342856904468717912123980239516449296282411906111180625728572592451347806975365612748820409779515933988666113351886922104580632330030315556131824269342495946265003583717851167900776094934529494288859544161962727027725141836385596719818854343272205219872268763687233481013480125619868622552216794150037075183051359513864468881127446406497273177045649104458223415781231935869205321779603158828385236200751294207373658013841829077282598657336030253516671581661419571606098538047008641504985948759788870421002859010913972073639473396498559632739259636095101913795946861001715644757363494483019570027538750704126046482539148601205768020838518557/8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node41PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node41Center (68-j) j
def node41PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node41R (68-j)
def node41HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node41Center (67-j) j
def node41HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node41R (67-j)

theorem node41_norm_upper : |node41Center.1|+|node41Center.2|≤node41R := by decide +kernel
theorem node41_error_nonneg : ∀ j : Fin 69, 0≤node41PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node41R]) _
theorem node41_terminal : |(node41PState 68).1|+|(node41PState 68).2|≤node41PError 68 := by
  simp [node41PState, node41PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node41_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node41Center (node41PState (j+1)) (node41PState j)).1|+
    |(ratResidual (pCoefficient j) node41Center (node41PState (j+1)) (node41PState j)).2|+
    node41R*node41PError (j+1)≤node41PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node41_final : |(node41PState 0).1|+|(node41PState 0).2|+node41PError 0≤node41PBound := by
  decide +kernel
theorem node41_P_value_bound : ‖p67.eval (ratComplex node41Center)‖≤(node41PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node41_norm_upper 68 node41_final

theorem node41_H_error_nonneg : ∀ j : Fin 68,0≤node41HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node41R]) _
theorem node41_H_terminal : |(node41HState 67).1|+|(node41HState 67).2|≤node41HError 67 := by
  simp [node41HState, node41HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node41_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node41Center (node41HState (j.val+1)) (node41HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node41Center (node41HState (j.val+1)) (node41HState j.val)).2|+
    node41R*node41HError (j.val+1)≤node41HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node41_H_value_error :
    ‖h66.eval (ratComplex node41Center)-ratComplex (node41HState 0)‖≤(node41HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node41_norm_upper 67
#print axioms node41_P_value_bound
#print axioms node41_H_value_error

def node42Center : ℚ × ℚ := (-1294444551659494083696930584047964562717822186245522227333595667976292847073251569551072946354926451180374876891005427290882149849054609557934204576181429175812027514814294753039258717257570016982690097118361490350270349150360039505914164077166876788587401544124122843164563181556387468859398704491283*centerUnit,1658145549429960328278192299429566840503982909864713281818881653287921167310563671603359543809381354392156510136936137201835098284331278610879326548291972198700571064171103123994272195400272970724967041433615045951047696421657503268231240343739862434777927892318799851331013439331547089000622947851487*centerUnit)

def node42R : ℚ := 3

def node42PBound : ℚ := (1434984343336569026606068454742620216264492207085230885747596337432219183911105637350487392791206856328501852419156145816336862433352122583974804265090939342856904468717912123980239516449296282411906111180625728572592451347806975365612748820409779515933988666113351886922104580632330030315556131824269342495946265003583717851167900776094934529494288859544161962727027725141836385596719818854343272205219872268763687233481013480125619868622552216794150037075183051359513864468881127446406497273177045649104458223415781231935869205321779603158828385236200751294207373658013841829077282598657336030253516671581661419571606098538047008641504985948759788870421002859010913972073639473396498559632739259636095101913795946861001715644757363494483019570027538750704126046482539148601205768020838518557/8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node42PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node42Center (68-j) j
def node42PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node42R (68-j)
def node42HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node42Center (67-j) j
def node42HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node42R (67-j)

theorem node42_norm_upper : |node42Center.1|+|node42Center.2|≤node42R := by decide +kernel
theorem node42_error_nonneg : ∀ j : Fin 69, 0≤node42PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node42R]) _
theorem node42_terminal : |(node42PState 68).1|+|(node42PState 68).2|≤node42PError 68 := by
  simp [node42PState, node42PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node42_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node42Center (node42PState (j+1)) (node42PState j)).1|+
    |(ratResidual (pCoefficient j) node42Center (node42PState (j+1)) (node42PState j)).2|+
    node42R*node42PError (j+1)≤node42PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node42_final : |(node42PState 0).1|+|(node42PState 0).2|+node42PError 0≤node42PBound := by
  decide +kernel
theorem node42_P_value_bound : ‖p67.eval (ratComplex node42Center)‖≤(node42PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node42_norm_upper 68 node42_final

theorem node42_H_error_nonneg : ∀ j : Fin 68,0≤node42HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node42R]) _
theorem node42_H_terminal : |(node42HState 67).1|+|(node42HState 67).2|≤node42HError 67 := by
  simp [node42HState, node42HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node42_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node42Center (node42HState (j.val+1)) (node42HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node42Center (node42HState (j.val+1)) (node42HState j.val)).2|+
    node42R*node42HError (j.val+1)≤node42HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node42_H_value_error :
    ‖h66.eval (ratComplex node42Center)-ratComplex (node42HState 0)‖≤(node42HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node42_norm_upper 67
#print axioms node42_P_value_bound
#print axioms node42_H_value_error

def node43Center : ℚ × ℚ := (4882036797075783162985288541950279050866860169637069584124641585320705269351328715881724523896702294369971111660551938851499202036946575786361362865966409144946873429543655982054817300675667986563950222223971091361093593221397767046158564607230022146468465078223291042346159531093325084432738537682921*centerUnit,-1755315697783283514234502850181004150673164558901598820196198797355588230921736023288943852687644259225130095321221236111969469836316324535491394790146776702008422215024335425718197098113190316363551423997390323981554823827539255240355189789093335236414396541826400601424868038842285717805622063708704*centerUnit)

def node43R : ℚ := 7

def node43PBound : ℚ := (189383106758079986433751397528441446730187153178220097166667811176698257694731771587536645852315484499667871558089886967456482722751307665703134770856456766211518827429890858261752976287715043089879014600583953992211069957776383215556269649324750269791717272990660757661035210965463423043339840061376750780300027037082854592219979377813809724392556329916308428140209896404517134108852528727626539578086055063573386003536861019077962662880748570511521963331481784567500538393807415512128327841573770157413079006290228289227937545758200627354005895060908394877071206633369907457315863294436126896061155619724813172009818565547863153272770525598491815563958312176353796937535838082023980534442280702864398007346191364251005881489781949541139201744729468005535488239496242895944192014176728583582475975578781517831/11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node43PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node43Center (68-j) j
def node43PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node43R (68-j)
def node43HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node43Center (67-j) j
def node43HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node43R (67-j)

theorem node43_norm_upper : |node43Center.1|+|node43Center.2|≤node43R := by decide +kernel
theorem node43_error_nonneg : ∀ j : Fin 69, 0≤node43PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node43R]) _
theorem node43_terminal : |(node43PState 68).1|+|(node43PState 68).2|≤node43PError 68 := by
  simp [node43PState, node43PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node43_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node43Center (node43PState (j+1)) (node43PState j)).1|+
    |(ratResidual (pCoefficient j) node43Center (node43PState (j+1)) (node43PState j)).2|+
    node43R*node43PError (j+1)≤node43PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node43_final : |(node43PState 0).1|+|(node43PState 0).2|+node43PError 0≤node43PBound := by
  decide +kernel
theorem node43_P_value_bound : ‖p67.eval (ratComplex node43Center)‖≤(node43PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node43_norm_upper 68 node43_final

theorem node43_H_error_nonneg : ∀ j : Fin 68,0≤node43HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node43R]) _
theorem node43_H_terminal : |(node43HState 67).1|+|(node43HState 67).2|≤node43HError 67 := by
  simp [node43HState, node43HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node43_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node43Center (node43HState (j.val+1)) (node43HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node43Center (node43HState (j.val+1)) (node43HState j.val)).2|+
    node43R*node43HError (j.val+1)≤node43HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node43_H_value_error :
    ‖h66.eval (ratComplex node43Center)-ratComplex (node43HState 0)‖≤(node43HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node43_norm_upper 67
#print axioms node43_P_value_bound
#print axioms node43_H_value_error

def node44Center : ℚ × ℚ := (4882036797075783162985288541950279050866860169637069584124641585320705269351328715881724523896702294369971111660551938851499202036946575786361362865966409144946873429543655982054817300675667986563950222223971091361093593221397767046158564607230022146468465078223291042346159531093325084432738537682921*centerUnit,1755315697783283514234502850181004150673164558901598820196198797355588230921736023288943852687644259225130095321221236111969469836316324535491394790146776702008422215024335425718197098113190316363551423997390323981554823827539255240355189789093335236414396541826400601424868038842285717805622063708703*centerUnit)

def node44R : ℚ := 7

def node44PBound : ℚ := (189383106758079986433751397528441446730187153178220097166667811176698257694731771587536645852315484499667871558089886967456482722751307665703134770856456766211518827429890858261752976287715043089879014600583953992211069957776383215556269649324750269791717272990660757661035210965463423043339840061376750780300027037082854592219979377813809724392556329916308428140209896404517134108852528727626539578086055063573386003536861019077962662880748570511521963331481784567500538393807415512128327841573770157413079006290228289227937545758200627354005895060908394877071206633369907457315863294436126896061155619724813172009818565547863153272770525598491815563958312176353796937535838082023980534442280702864398007346191364251005881489781949541139201744729468005535488239496242895944192014176728583582475975578781517831/11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node44PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node44Center (68-j) j
def node44PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node44R (68-j)
def node44HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node44Center (67-j) j
def node44HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node44R (67-j)

theorem node44_norm_upper : |node44Center.1|+|node44Center.2|≤node44R := by decide +kernel
theorem node44_error_nonneg : ∀ j : Fin 69, 0≤node44PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node44R]) _
theorem node44_terminal : |(node44PState 68).1|+|(node44PState 68).2|≤node44PError 68 := by
  simp [node44PState, node44PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node44_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node44Center (node44PState (j+1)) (node44PState j)).1|+
    |(ratResidual (pCoefficient j) node44Center (node44PState (j+1)) (node44PState j)).2|+
    node44R*node44PError (j+1)≤node44PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node44_final : |(node44PState 0).1|+|(node44PState 0).2|+node44PError 0≤node44PBound := by
  decide +kernel
theorem node44_P_value_bound : ‖p67.eval (ratComplex node44Center)‖≤(node44PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node44_norm_upper 68 node44_final

theorem node44_H_error_nonneg : ∀ j : Fin 68,0≤node44HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node44R]) _
theorem node44_H_terminal : |(node44HState 67).1|+|(node44HState 67).2|≤node44HError 67 := by
  simp [node44HState, node44HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node44_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node44Center (node44HState (j.val+1)) (node44HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node44Center (node44HState (j.val+1)) (node44HState j.val)).2|+
    node44R*node44HError (j.val+1)≤node44HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node44_H_value_error :
    ‖h66.eval (ratComplex node44Center)-ratComplex (node44HState 0)‖≤(node44HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node44_norm_upper 67
#print axioms node44_P_value_bound
#print axioms node44_H_value_error

def node45Center : ℚ × ℚ := (-328275945024590090664495514955096401917745886608059495846334234220608014340078752360696967520014834738367969090276361871249411894576799512278033370166044236434701233967848863970782610616216564174164942318389678775766733449056785046418704317495304664925468312242555019817673385594672170790121528515361*centerUnit,-1808220086778323797012700496917248069431181273778571477210199350108509084003448005564889716066795117116832528798718722334964699420476348574970194236653776017404179328272718784609730777048095013295903749240264345895738305495144554707216275404910595517552240512686219253527529820195295104654788881022377*centerUnit)

def node45R : ℚ := 3

def node45PBound : ℚ := (4014980973941861796478564402564078700696752080597308822094492089543246526534788343694099310192959186534584554351963093110865115812843380212973041113341137213483036922923837142632646322961215531532399232618660205400554498258663628344320947648431451467581765585120250715705027264528346219879037787993842319031653962536806628724929483144426403927197846475779383272232368403386922754794838535753018148787207252626342406042776363523816457482611871997374069829347940906917168556867516304166114440685090609410034208166859817473493544699773389182591629671117728295170663368977498266190214319500633929501060103044444414691883187058622804067516380405348166388369762203897079623387762764520843808210516504393014824512370723957368042565321135120207514639680490444545099320393561779198863875753354311353/142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node45PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node45Center (68-j) j
def node45PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node45R (68-j)
def node45HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node45Center (67-j) j
def node45HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node45R (67-j)

theorem node45_norm_upper : |node45Center.1|+|node45Center.2|≤node45R := by decide +kernel
theorem node45_error_nonneg : ∀ j : Fin 69, 0≤node45PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node45R]) _
theorem node45_terminal : |(node45PState 68).1|+|(node45PState 68).2|≤node45PError 68 := by
  simp [node45PState, node45PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node45_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node45Center (node45PState (j+1)) (node45PState j)).1|+
    |(ratResidual (pCoefficient j) node45Center (node45PState (j+1)) (node45PState j)).2|+
    node45R*node45PError (j+1)≤node45PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node45_final : |(node45PState 0).1|+|(node45PState 0).2|+node45PError 0≤node45PBound := by
  decide +kernel
theorem node45_P_value_bound : ‖p67.eval (ratComplex node45Center)‖≤(node45PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node45_norm_upper 68 node45_final

theorem node45_H_error_nonneg : ∀ j : Fin 68,0≤node45HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node45R]) _
theorem node45_H_terminal : |(node45HState 67).1|+|(node45HState 67).2|≤node45HError 67 := by
  simp [node45HState, node45HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node45_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node45Center (node45HState (j.val+1)) (node45HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node45Center (node45HState (j.val+1)) (node45HState j.val)).2|+
    node45R*node45HError (j.val+1)≤node45HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node45_H_value_error :
    ‖h66.eval (ratComplex node45Center)-ratComplex (node45HState 0)‖≤(node45HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node45_norm_upper 67
#print axioms node45_P_value_bound
#print axioms node45_H_value_error

def node46Center : ℚ × ℚ := (-328275945024590090664495514955096401917745886608059495846334234220608014340078752360696967520014834738367969090276361871249411894576799512278033370166044236434701233967848863970782610616216564174164942318389678775766733449056785046418704317495304664925468312242555019817673385594672170790121528515361*centerUnit,1808220086778323797012700496917248069431181273778571477210199350108509084003448005564889716066795117116832528798718722334964699420476348574970194236653776017404179328272718784609730777048095013295903749240264345895738305495144554707216275404910595517552240512686219253527529820195295104654788881022376*centerUnit)

def node46R : ℚ := 3

def node46PBound : ℚ := (4014980973941861796478564402564078700696752080597308822094492089543246526534788343694099310192959186534584554351963093110865115812843380212973041113341137213483036922923837142632646322961215531532399232618660205400554498258663628344320947648431451467581765585120250715705027264528346219879037787993842319031653962536806628724929483144426403927197846475779383272232368403386922754794838535753018148787207252626342406042776363523816457482611871997374069829347940906917168556867516304166114440685090609410034208166859817473493544699773389182591629671117728295170663368977498266190214319500633929501060103044444414691883187058622804067516380405348166388369762203897079623387762764520843808210516504393014824512370723957368042565321135120207514639680490444545099320393561779198863875753354311353/142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node46PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node46Center (68-j) j
def node46PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node46R (68-j)
def node46HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node46Center (67-j) j
def node46HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node46R (67-j)

theorem node46_norm_upper : |node46Center.1|+|node46Center.2|≤node46R := by decide +kernel
theorem node46_error_nonneg : ∀ j : Fin 69, 0≤node46PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node46R]) _
theorem node46_terminal : |(node46PState 68).1|+|(node46PState 68).2|≤node46PError 68 := by
  simp [node46PState, node46PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node46_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node46Center (node46PState (j+1)) (node46PState j)).1|+
    |(ratResidual (pCoefficient j) node46Center (node46PState (j+1)) (node46PState j)).2|+
    node46R*node46PError (j+1)≤node46PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node46_final : |(node46PState 0).1|+|(node46PState 0).2|+node46PError 0≤node46PBound := by
  decide +kernel
theorem node46_P_value_bound : ‖p67.eval (ratComplex node46Center)‖≤(node46PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node46_norm_upper 68 node46_final

theorem node46_H_error_nonneg : ∀ j : Fin 68,0≤node46HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node46R]) _
theorem node46_H_terminal : |(node46HState 67).1|+|(node46HState 67).2|≤node46HError 67 := by
  simp [node46HState, node46HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node46_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node46Center (node46HState (j.val+1)) (node46HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node46Center (node46HState (j.val+1)) (node46HState j.val)).2|+
    node46R*node46HError (j.val+1)≤node46HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node46_H_value_error :
    ‖h66.eval (ratComplex node46Center)-ratComplex (node46HState 0)‖≤(node46HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node46_norm_upper 67
#print axioms node46_P_value_bound
#print axioms node46_H_value_error

def node47Center : ℚ × ℚ := (-1291021759414212820881919705827735610661685449513019207243904223070440590118182411279551081063336312947154557447995207078994471600793355708412173241099841257017884931620008653327588607366307377906700400857396088701225527988575309721138820821927906775869640774429168044702298806306416519382210020793639*centerUnit,-1847886412210693132277918803993091157011460686228364663107151846796670831526823579755925672298182541257891128028042496360009818500081749266873638699252456398554752550367955782643213059329101484996145536185458591239581711921719068173136078698876725589043003883085140391544355182048654034930201237538032*centerUnit)

def node47R : ℚ := 4

def node47PBound : ℚ := (1451752763257130714193450021209644034313295220031458303214596261156055272056536371818151531567599225528026235429315688022330433840933976246683896841926271738154592357449513834246361718561950052687171808151372184590171180756077996171009514292277264691148419790155281324454493626936902313281899781850790577455264530044330455881232183285706375823612400259668572967504585836998159535294860824981930747523450813098585956573977166688910603432266181873762761740644243602187545461052334499837756756271445580635470524708150455220108455930369764336325443926762012280513193942492035008500849387594641903840437560980610937084807285554111755352237370976143610854743534654963589656885136111371282437677914953502826593989983738253818017889475119333023579310227468804096367031377844068059128294810512879476613/1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node47PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node47Center (68-j) j
def node47PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node47R (68-j)
def node47HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node47Center (67-j) j
def node47HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node47R (67-j)

theorem node47_norm_upper : |node47Center.1|+|node47Center.2|≤node47R := by decide +kernel
theorem node47_error_nonneg : ∀ j : Fin 69, 0≤node47PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node47R]) _
theorem node47_terminal : |(node47PState 68).1|+|(node47PState 68).2|≤node47PError 68 := by
  simp [node47PState, node47PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node47_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node47Center (node47PState (j+1)) (node47PState j)).1|+
    |(ratResidual (pCoefficient j) node47Center (node47PState (j+1)) (node47PState j)).2|+
    node47R*node47PError (j+1)≤node47PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node47_final : |(node47PState 0).1|+|(node47PState 0).2|+node47PError 0≤node47PBound := by
  decide +kernel
theorem node47_P_value_bound : ‖p67.eval (ratComplex node47Center)‖≤(node47PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node47_norm_upper 68 node47_final

theorem node47_H_error_nonneg : ∀ j : Fin 68,0≤node47HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node47R]) _
theorem node47_H_terminal : |(node47HState 67).1|+|(node47HState 67).2|≤node47HError 67 := by
  simp [node47HState, node47HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node47_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node47Center (node47HState (j.val+1)) (node47HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node47Center (node47HState (j.val+1)) (node47HState j.val)).2|+
    node47R*node47HError (j.val+1)≤node47HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node47_H_value_error :
    ‖h66.eval (ratComplex node47Center)-ratComplex (node47HState 0)‖≤(node47HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node47_norm_upper 67
#print axioms node47_P_value_bound
#print axioms node47_H_value_error

def node48Center : ℚ × ℚ := (-1291021759414212820881919705827735610661685449513019207243904223070440590118182411279551081063336312947154557447995207078994471600793355708412173241099841257017884931620008653327588607366307377906700400857396088701225527988575309721138820821927906775869640774429168044702298806306416519382210020793639*centerUnit,1847886412210693132277918803993091157011460686228364663107151846796670831526823579755925672298182541257891128028042496360009818500081749266873638699252456398554752550367955782643213059329101484996145536185458591239581711921719068173136078698876725589043003883085140391544355182048654034930201237538031*centerUnit)

def node48R : ℚ := 4

def node48PBound : ℚ := (1451752763257130714193450021209644034313295220031458303214596261156055272056536371818151531567599225528026235429315688022330433840933976246683896841926271738154592357449513834246361718561950052687171808151372184590171180756077996171009514292277264691148419790155281324454493626936902313281899781850790577455264530044330455881232183285706375823612400259668572967504585836998159535294860824981930747523450813098585956573977166688910603432266181873762761740644243602187545461052334499837756756271445580635470524708150455220108455930369764336325443926762012280513193942492035008500849387594641903840437560980610937084807285554111755352237370976143610854743534654963589656885136111371282437677914953502826593989983738253818017889475119333023579310227468804096367031377844068059128294810512879476613/1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node48PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node48Center (68-j) j
def node48PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node48R (68-j)
def node48HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node48Center (67-j) j
def node48HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node48R (67-j)

theorem node48_norm_upper : |node48Center.1|+|node48Center.2|≤node48R := by decide +kernel
theorem node48_error_nonneg : ∀ j : Fin 69, 0≤node48PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node48R]) _
theorem node48_terminal : |(node48PState 68).1|+|(node48PState 68).2|≤node48PError 68 := by
  simp [node48PState, node48PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node48_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node48Center (node48PState (j+1)) (node48PState j)).1|+
    |(ratResidual (pCoefficient j) node48Center (node48PState (j+1)) (node48PState j)).2|+
    node48R*node48PError (j+1)≤node48PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node48_final : |(node48PState 0).1|+|(node48PState 0).2|+node48PError 0≤node48PBound := by
  decide +kernel
theorem node48_P_value_bound : ‖p67.eval (ratComplex node48Center)‖≤(node48PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node48_norm_upper 68 node48_final

theorem node48_H_error_nonneg : ∀ j : Fin 68,0≤node48HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node48R]) _
theorem node48_H_terminal : |(node48HState 67).1|+|(node48HState 67).2|≤node48HError 67 := by
  simp [node48HState, node48HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node48_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node48Center (node48HState (j.val+1)) (node48HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node48Center (node48HState (j.val+1)) (node48HState j.val)).2|+
    node48R*node48HError (j.val+1)≤node48HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node48_H_value_error :
    ‖h66.eval (ratComplex node48Center)-ratComplex (node48HState 0)‖≤(node48HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node48_norm_upper 67
#print axioms node48_P_value_bound
#print axioms node48_H_value_error

def node49Center : ℚ × ℚ := (455504125856675731187304849388662150009622861429240106976118524972483006344202847281205880628713768841896547352996607847448031278178939079006167769730002700318391739977843605674173428543104362643784489531769556216851129483870795854906263833485789204800823076572998204469905019209692155341822075894768*centerUnit,-1940966961997595766149610174879273282851128040684838232535948569654079868933360263081196650434742381455588772024225557242050928924890551709605858386836813774360304851936838229673802234680112500041246531063527251815358778164499338212293426495065492986866933589937255969884999668317840720008471950068789*centerUnit)

def node49R : ℚ := 3

def node49PBound : ℚ := (2389844729597274492702606067010171392426091266190411721783822495647332077627790605558559918045897364098026492856324233939563129351192071057943905099612973644775598494233400408932025086097882946995544782331568605898873226697355048789529243290475197428571557960318905151813637408963372087698464597146840595629031997243259587935414948655407154511609958795499961021356479043493880647863121192967704802984497012202093530454494909399218519573955736581737116021568372313461057953681278685234525411927742923338572436843499546311052381443287840115079502995575697732988637396530499285704684448284765719848101113469863734476625015035768508257142857018049412598109088693279680625889482669078695843373981013572427584509753340554110578622987169210592393916788210336870558237652164332707396901975394907/6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node49PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node49Center (68-j) j
def node49PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node49R (68-j)
def node49HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node49Center (67-j) j
def node49HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node49R (67-j)

theorem node49_norm_upper : |node49Center.1|+|node49Center.2|≤node49R := by decide +kernel
theorem node49_error_nonneg : ∀ j : Fin 69, 0≤node49PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node49R]) _
theorem node49_terminal : |(node49PState 68).1|+|(node49PState 68).2|≤node49PError 68 := by
  simp [node49PState, node49PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node49_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node49Center (node49PState (j+1)) (node49PState j)).1|+
    |(ratResidual (pCoefficient j) node49Center (node49PState (j+1)) (node49PState j)).2|+
    node49R*node49PError (j+1)≤node49PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node49_final : |(node49PState 0).1|+|(node49PState 0).2|+node49PError 0≤node49PBound := by
  decide +kernel
theorem node49_P_value_bound : ‖p67.eval (ratComplex node49Center)‖≤(node49PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node49_norm_upper 68 node49_final

theorem node49_H_error_nonneg : ∀ j : Fin 68,0≤node49HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node49R]) _
theorem node49_H_terminal : |(node49HState 67).1|+|(node49HState 67).2|≤node49HError 67 := by
  simp [node49HState, node49HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node49_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node49Center (node49HState (j.val+1)) (node49HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node49Center (node49HState (j.val+1)) (node49HState j.val)).2|+
    node49R*node49HError (j.val+1)≤node49HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node49_H_value_error :
    ‖h66.eval (ratComplex node49Center)-ratComplex (node49HState 0)‖≤(node49HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node49_norm_upper 67
#print axioms node49_P_value_bound
#print axioms node49_H_value_error

def node50Center : ℚ × ℚ := (455504125856675731187304849388662150009622861429240106976118524972483006344202847281205880628713768841896547352996607847448031278178939079006167769730002700318391739977843605674173428543104362643784489531769556216851129483870795854906263833485789204800823076572998204469905019209692155341822075894768*centerUnit,1940966961997595766149610174879273282851128040684838232535948569654079868933360263081196650434742381455588772024225557242050928924890551709605858386836813774360304851936838229673802234680112500041246531063527251815358778164499338212293426495065492986866933589937255969884999668317840720008471950068788*centerUnit)

def node50R : ℚ := 3

def node50PBound : ℚ := (2389844729597274492702606067010171392426091266190411721783822495647332077627790605558559918045897364098026492856324233939563129351192071057943905099612973644775598494233400408932025086097882946995544782331568605898873226697355048789529243290475197428571557960318905151813637408963372087698464597146840595629031997243259587935414948655407154511609958795499961021356479043493880647863121192967704802984497012202093530454494909399218519573955736581737116021568372313461057953681278685234525411927742923338572436843499546311052381443287840115079502995575697732988637396530499285704684448284765719848101113469863734476625015035768508257142857018049412598109088693279680625889482669078695843373981013572427584509753340554110578622987169210592393916788210336870558237652164332707396901975394907/6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node50PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node50Center (68-j) j
def node50PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node50R (68-j)
def node50HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node50Center (67-j) j
def node50HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node50R (67-j)

theorem node50_norm_upper : |node50Center.1|+|node50Center.2|≤node50R := by decide +kernel
theorem node50_error_nonneg : ∀ j : Fin 69, 0≤node50PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node50R]) _
theorem node50_terminal : |(node50PState 68).1|+|(node50PState 68).2|≤node50PError 68 := by
  simp [node50PState, node50PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node50_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node50Center (node50PState (j+1)) (node50PState j)).1|+
    |(ratResidual (pCoefficient j) node50Center (node50PState (j+1)) (node50PState j)).2|+
    node50R*node50PError (j+1)≤node50PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node50_final : |(node50PState 0).1|+|(node50PState 0).2|+node50PError 0≤node50PBound := by
  decide +kernel
theorem node50_P_value_bound : ‖p67.eval (ratComplex node50Center)‖≤(node50PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node50_norm_upper 68 node50_final

theorem node50_H_error_nonneg : ∀ j : Fin 68,0≤node50HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node50R]) _
theorem node50_H_terminal : |(node50HState 67).1|+|(node50HState 67).2|≤node50HError 67 := by
  simp [node50HState, node50HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node50_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node50Center (node50HState (j.val+1)) (node50HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node50Center (node50HState (j.val+1)) (node50HState j.val)).2|+
    node50R*node50HError (j.val+1)≤node50HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node50_H_value_error :
    ‖h66.eval (ratComplex node50Center)-ratComplex (node50HState 0)‖≤(node50HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node50_norm_upper 67
#print axioms node50_P_value_bound
#print axioms node50_H_value_error

def node51Center : ℚ × ℚ := (-3691365673087735853178883230342764385517363528087952706980874557331474135254731748215912766010415662268191395497419617803446483739041986012704466268421386276182741332426957172722588806010710433162627567212487309343212769180863014101056941543512024042289883503808840817093830326968785613221481183324993*centerUnit,-2078271300905875774596241924540692932716362651672052586066138113118143888049058824193538178142481554247989319232277739275114860837587224831876552016164701990956887711827064656056439405020669529129165045461114277403863863546789132645057414601576535563401242812611929000862822778909183057844025680320123*centerUnit)

def node51R : ℚ := 6

def node51PBound : ℚ := (224993903198788119076418935934111581604470047147279111228092980315995911418438694791415296244364752452022939643227188468442070148204277194923076818609857655998229351301896839795139285073655336171600397352660309980042511678649995380993557398091343291043747477926309604968948285183075634567703317986314797786751739642366046265555413757542866943115191032427024010732005680253272288766627417691643903278206042776567549180921495201891406337760468283524976969202273858500328293481380482177344000538208441076702785163971051460842708171253173290743718445046414222213395066496307970483593653422720083968597029268366076010307592732947854318837443132975426129106943565657979175459278565102510734864829696249152202705921787879775042230485859331948908955602312197406376332707347118672256465327254213988350205829898043103/69388939039072283776476979255676269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node51PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node51Center (68-j) j
def node51PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node51R (68-j)
def node51HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node51Center (67-j) j
def node51HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node51R (67-j)

theorem node51_norm_upper : |node51Center.1|+|node51Center.2|≤node51R := by decide +kernel
theorem node51_error_nonneg : ∀ j : Fin 69, 0≤node51PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node51R]) _
theorem node51_terminal : |(node51PState 68).1|+|(node51PState 68).2|≤node51PError 68 := by
  simp [node51PState, node51PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node51_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node51Center (node51PState (j+1)) (node51PState j)).1|+
    |(ratResidual (pCoefficient j) node51Center (node51PState (j+1)) (node51PState j)).2|+
    node51R*node51PError (j+1)≤node51PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node51_final : |(node51PState 0).1|+|(node51PState 0).2|+node51PError 0≤node51PBound := by
  decide +kernel
theorem node51_P_value_bound : ‖p67.eval (ratComplex node51Center)‖≤(node51PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node51_norm_upper 68 node51_final

theorem node51_H_error_nonneg : ∀ j : Fin 68,0≤node51HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node51R]) _
theorem node51_H_terminal : |(node51HState 67).1|+|(node51HState 67).2|≤node51HError 67 := by
  simp [node51HState, node51HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node51_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node51Center (node51HState (j.val+1)) (node51HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node51Center (node51HState (j.val+1)) (node51HState j.val)).2|+
    node51R*node51HError (j.val+1)≤node51HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node51_H_value_error :
    ‖h66.eval (ratComplex node51Center)-ratComplex (node51HState 0)‖≤(node51HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node51_norm_upper 67
#print axioms node51_P_value_bound
#print axioms node51_H_value_error

def node52Center : ℚ × ℚ := (-3691365673087735853178883230342764385517363528087952706980874557331474135254731748215912766010415662268191395497419617803446483739041986012704466268421386276182741332426957172722588806010710433162627567212487309343212769180863014101056941543512024042289883503808840817093830326968785613221481183324993*centerUnit,2078271300905875774596241924540692932716362651672052586066138113118143888049058824193538178142481554247989319232277739275114860837587224831876552016164701990956887711827064656056439405020669529129165045461114277403863863546789132645057414601576535563401242812611929000862822778909183057844025680320122*centerUnit)

def node52R : ℚ := 6

def node52PBound : ℚ := (224993903198788119076418935934111581604470047147279111228092980315995911418438694791415296244364752452022939643227188468442070148204277194923076818609857655998229351301896839795139285073655336171600397352660309980042511678649995380993557398091343291043747477926309604968948285183075634567703317986314797786751739642366046265555413757542866943115191032427024010732005680253272288766627417691643903278206042776567549180921495201891406337760468283524976969202273858500328293481380482177344000538208441076702785163971051460842708171253173290743718445046414222213395066496307970483593653422720083968597029268366076010307592732947854318837443132975426129106943565657979175459278565102510734864829696249152202705921787879775042230485859331948908955602312197406376332707347118672256465327254213988350205829898043103/69388939039072283776476979255676269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node52PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node52Center (68-j) j
def node52PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node52R (68-j)
def node52HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node52Center (67-j) j
def node52HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node52R (67-j)

theorem node52_norm_upper : |node52Center.1|+|node52Center.2|≤node52R := by decide +kernel
theorem node52_error_nonneg : ∀ j : Fin 69, 0≤node52PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node52R]) _
theorem node52_terminal : |(node52PState 68).1|+|(node52PState 68).2|≤node52PError 68 := by
  simp [node52PState, node52PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node52_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node52Center (node52PState (j+1)) (node52PState j)).1|+
    |(ratResidual (pCoefficient j) node52Center (node52PState (j+1)) (node52PState j)).2|+
    node52R*node52PError (j+1)≤node52PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node52_final : |(node52PState 0).1|+|(node52PState 0).2|+node52PError 0≤node52PBound := by
  decide +kernel
theorem node52_P_value_bound : ‖p67.eval (ratComplex node52Center)‖≤(node52PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node52_norm_upper 68 node52_final

theorem node52_H_error_nonneg : ∀ j : Fin 68,0≤node52HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node52R]) _
theorem node52_H_terminal : |(node52HState 67).1|+|(node52HState 67).2|≤node52HError 67 := by
  simp [node52HState, node52HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node52_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node52Center (node52HState (j.val+1)) (node52HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node52Center (node52HState (j.val+1)) (node52HState j.val)).2|+
    node52R*node52HError (j.val+1)≤node52HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node52_H_value_error :
    ‖h66.eval (ratComplex node52Center)-ratComplex (node52HState 0)‖≤(node52HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node52_norm_upper 67
#print axioms node52_P_value_bound
#print axioms node52_H_value_error

def node53Center : ℚ × ℚ := (2220943990848338388292982710869470465795480775071556091065928394027876345664282905375192834444869768976685819876539534397322757499895668914795280868951568424446411687853175027279987740527616617594092553731653646124673391363929272677843324295936066699691398402822732257815267014194242245004396196105059*centerUnit,-2383089543014865369261457627676305091527740528519548507142559314708965130696098071768978563973791427008193598599605850355299838261085687388669319729585086071368288932458502640941110534433791393432071998400203992296312938017493491325824013861866624784200024680983978887068813154671395229304057505846579*centerUnit)

def node53R : ℚ := 5

def node53PBound : ℚ := (4393748726249180213568976419824845230343845123699338712321830057834862009310281636234226390530413823255207678903417182063711509459949460068524770558383373518221625204496746184698678970034471184216805581184740990876324497958801868015679454796114353899703657207472456185926692151618008843250743092790248289036244629138943312534541974040367525674296387803250931682154643895548922325754531801545909960643340112880692947094170524628001232359291639262062570351783828766887021482839608855240621587297675935577148101625403701628238637053326147641311317869405504986710396619193506180419768643739838060941209280765516671788267946193592765638891214975768069675562886935716230677430595447525703921980029146405025567826989853762579187192297026610911056142112334022673136885171909539439985085657236321193286111029/8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node53PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node53Center (68-j) j
def node53PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node53R (68-j)
def node53HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node53Center (67-j) j
def node53HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node53R (67-j)

theorem node53_norm_upper : |node53Center.1|+|node53Center.2|≤node53R := by decide +kernel
theorem node53_error_nonneg : ∀ j : Fin 69, 0≤node53PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node53R]) _
theorem node53_terminal : |(node53PState 68).1|+|(node53PState 68).2|≤node53PError 68 := by
  simp [node53PState, node53PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node53_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node53Center (node53PState (j+1)) (node53PState j)).1|+
    |(ratResidual (pCoefficient j) node53Center (node53PState (j+1)) (node53PState j)).2|+
    node53R*node53PError (j+1)≤node53PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node53_final : |(node53PState 0).1|+|(node53PState 0).2|+node53PError 0≤node53PBound := by
  decide +kernel
theorem node53_P_value_bound : ‖p67.eval (ratComplex node53Center)‖≤(node53PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node53_norm_upper 68 node53_final

theorem node53_H_error_nonneg : ∀ j : Fin 68,0≤node53HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node53R]) _
theorem node53_H_terminal : |(node53HState 67).1|+|(node53HState 67).2|≤node53HError 67 := by
  simp [node53HState, node53HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node53_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node53Center (node53HState (j.val+1)) (node53HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node53Center (node53HState (j.val+1)) (node53HState j.val)).2|+
    node53R*node53HError (j.val+1)≤node53HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node53_H_value_error :
    ‖h66.eval (ratComplex node53Center)-ratComplex (node53HState 0)‖≤(node53HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node53_norm_upper 67
#print axioms node53_P_value_bound
#print axioms node53_H_value_error

def node54Center : ℚ × ℚ := (2220943990848338388292982710869470465795480775071556091065928394027876345664282905375192834444869768976685819876539534397322757499895668914795280868951568424446411687853175027279987740527616617594092553731653646124673391363929272677843324295936066699691398402822732257815267014194242245004396196105059*centerUnit,2383089543014865369261457627676305091527740528519548507142559314708965130696098071768978563973791427008193598599605850355299838261085687388669319729585086071368288932458502640941110534433791393432071998400203992296312938017493491325824013861866624784200024680983978887068813154671395229304057505846578*centerUnit)

def node54R : ℚ := 5

def node54PBound : ℚ := (4393748726249180213568976419824845230343845123699338712321830057834862009310281636234226390530413823255207678903417182063711509459949460068524770558383373518221625204496746184698678970034471184216805581184740990876324497958801868015679454796114353899703657207472456185926692151618008843250743092790248289036244629138943312534541974040367525674296387803250931682154643895548922325754531801545909960643340112880692947094170524628001232359291639262062570351783828766887021482839608855240621587297675935577148101625403701628238637053326147641311317869405504986710396619193506180419768643739838060941209280765516671788267946193592765638891214975768069675562886935716230677430595447525703921980029146405025567826989853762579187192297026610911056142112334022673136885171909539439985085657236321193286111029/8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node54PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node54Center (68-j) j
def node54PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node54R (68-j)
def node54HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node54Center (67-j) j
def node54HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node54R (67-j)

theorem node54_norm_upper : |node54Center.1|+|node54Center.2|≤node54R := by decide +kernel
theorem node54_error_nonneg : ∀ j : Fin 69, 0≤node54PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node54R]) _
theorem node54_terminal : |(node54PState 68).1|+|(node54PState 68).2|≤node54PError 68 := by
  simp [node54PState, node54PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node54_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node54Center (node54PState (j+1)) (node54PState j)).1|+
    |(ratResidual (pCoefficient j) node54Center (node54PState (j+1)) (node54PState j)).2|+
    node54R*node54PError (j+1)≤node54PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node54_final : |(node54PState 0).1|+|(node54PState 0).2|+node54PError 0≤node54PBound := by
  decide +kernel
theorem node54_P_value_bound : ‖p67.eval (ratComplex node54Center)‖≤(node54PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node54_norm_upper 68 node54_final

theorem node54_H_error_nonneg : ∀ j : Fin 68,0≤node54HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node54R]) _
theorem node54_H_terminal : |(node54HState 67).1|+|(node54HState 67).2|≤node54HError 67 := by
  simp [node54HState, node54HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node54_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node54Center (node54HState (j.val+1)) (node54HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node54Center (node54HState (j.val+1)) (node54HState j.val)).2|+
    node54R*node54HError (j.val+1)≤node54HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node54_H_value_error :
    ‖h66.eval (ratComplex node54Center)-ratComplex (node54HState 0)‖≤(node54HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node54_norm_upper 67
#print axioms node54_P_value_bound
#print axioms node54_H_value_error

def node55Center : ℚ × ℚ := (-2321742230674973651196738471278150805193768119350830544397223945363034650079384835939032701355865206020729147999005173604223635891729427938166117504013773293671133418499765924996688295502696159911170558890241927070503145764572479509683296873089507399973974753930249717115115161337575170656978586248438*centerUnit,-2473984097505321993874769641971642526753765061289746884835401811852575783572726786994216730132501751902700197803039029893533743659813586646562634916327483950587957978080760322317442751651431434215215722595886129641800254427069507075602579094410873172177568458535214464235985867143017833902939128838628*centerUnit)

def node55R : ℚ := 5

def node55PBound : ℚ := (5110141058094764194736806484709211197750904064917228157834445651667601492231071516830222056112948853068714577635361921734100855676360826344842634111978866140136714500800095221872867008180106887128701645447182231534058871431621260666964367859218985278450298308964128032554742622741723738427467685502466230180703553691876163077698284282570228897437287275433618139982810174996336097511638544161207739885698662758937014466239451864941900466562500090320323523387784040580349968873199368269013212438656417526223235444859688495885605459365942783350195091292671481408743187076622000157908347831890372710168271679552924179234166153408808082611078075822110640882117804776025217331783988638386466809560117368029274795910847360955727579927488771957079481274012082519366234402382626571721612170475460654164049/363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node55PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node55Center (68-j) j
def node55PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node55R (68-j)
def node55HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node55Center (67-j) j
def node55HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node55R (67-j)

theorem node55_norm_upper : |node55Center.1|+|node55Center.2|≤node55R := by decide +kernel
theorem node55_error_nonneg : ∀ j : Fin 69, 0≤node55PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node55R]) _
theorem node55_terminal : |(node55PState 68).1|+|(node55PState 68).2|≤node55PError 68 := by
  simp [node55PState, node55PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node55_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node55Center (node55PState (j+1)) (node55PState j)).1|+
    |(ratResidual (pCoefficient j) node55Center (node55PState (j+1)) (node55PState j)).2|+
    node55R*node55PError (j+1)≤node55PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node55_final : |(node55PState 0).1|+|(node55PState 0).2|+node55PError 0≤node55PBound := by
  decide +kernel
theorem node55_P_value_bound : ‖p67.eval (ratComplex node55Center)‖≤(node55PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node55_norm_upper 68 node55_final

theorem node55_H_error_nonneg : ∀ j : Fin 68,0≤node55HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node55R]) _
theorem node55_H_terminal : |(node55HState 67).1|+|(node55HState 67).2|≤node55HError 67 := by
  simp [node55HState, node55HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node55_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node55Center (node55HState (j.val+1)) (node55HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node55Center (node55HState (j.val+1)) (node55HState j.val)).2|+
    node55R*node55HError (j.val+1)≤node55HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node55_H_value_error :
    ‖h66.eval (ratComplex node55Center)-ratComplex (node55HState 0)‖≤(node55HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node55_norm_upper 67
#print axioms node55_P_value_bound
#print axioms node55_H_value_error

def node56Center : ℚ × ℚ := (-2321742230674973651196738471278150805193768119350830544397223945363034650079384835939032701355865206020729147999005173604223635891729427938166117504013773293671133418499765924996688295502696159911170558890241927070503145764572479509683296873089507399973974753930249717115115161337575170656978586248438*centerUnit,2473984097505321993874769641971642526753765061289746884835401811852575783572726786994216730132501751902700197803039029893533743659813586646562634916327483950587957978080760322317442751651431434215215722595886129641800254427069507075602579094410873172177568458535214464235985867143017833902939128838627*centerUnit)

def node56R : ℚ := 5

def node56PBound : ℚ := (5110141058094764194736806484709211197750904064917228157834445651667601492231071516830222056112948853068714577635361921734100855676360826344842634111978866140136714500800095221872867008180106887128701645447182231534058871431621260666964367859218985278450298308964128032554742622741723738427467685502466230180703553691876163077698284282570228897437287275433618139982810174996336097511638544161207739885698662758937014466239451864941900466562500090320323523387784040580349968873199368269013212438656417526223235444859688495885605459365942783350195091292671481408743187076622000157908347831890372710168271679552924179234166153408808082611078075822110640882117804776025217331783988638386466809560117368029274795910847360955727579927488771957079481274012082519366234402382626571721612170475460654164049/363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node56PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node56Center (68-j) j
def node56PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node56R (68-j)
def node56HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node56Center (67-j) j
def node56HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node56R (67-j)

theorem node56_norm_upper : |node56Center.1|+|node56Center.2|≤node56R := by decide +kernel
theorem node56_error_nonneg : ∀ j : Fin 69, 0≤node56PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node56R]) _
theorem node56_terminal : |(node56PState 68).1|+|(node56PState 68).2|≤node56PError 68 := by
  simp [node56PState, node56PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node56_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node56Center (node56PState (j+1)) (node56PState j)).1|+
    |(ratResidual (pCoefficient j) node56Center (node56PState (j+1)) (node56PState j)).2|+
    node56R*node56PError (j+1)≤node56PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node56_final : |(node56PState 0).1|+|(node56PState 0).2|+node56PError 0≤node56PBound := by
  decide +kernel
theorem node56_P_value_bound : ‖p67.eval (ratComplex node56Center)‖≤(node56PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node56_norm_upper 68 node56_final

theorem node56_H_error_nonneg : ∀ j : Fin 68,0≤node56HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node56R]) _
theorem node56_H_terminal : |(node56HState 67).1|+|(node56HState 67).2|≤node56HError 67 := by
  simp [node56HState, node56HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node56_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node56Center (node56HState (j.val+1)) (node56HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node56Center (node56HState (j.val+1)) (node56HState j.val)).2|+
    node56R*node56HError (j.val+1)≤node56HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node56_H_value_error :
    ‖h66.eval (ratComplex node56Center)-ratComplex (node56HState 0)‖≤(node56HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node56_norm_upper 67
#print axioms node56_P_value_bound
#print axioms node56_H_value_error

def node57Center : ℚ × ℚ := (1735546860225992158390436159910350529177168543303759551683659222558564479917801646055094539413236111206089314021355789806352935249687052927341753350075787804782189974500919386182090939261311569041811134933015376116829515062887316030848412810217702880946171275750103152390392448232482043435406725394841*centerUnit,-3240022049245456969915243943826694177583882674050604001335265815404665567400153851445814272510001012809007784251389953133561082455738667204719601781936634676174254524791629278125432319366795165718304429982329726202960153431134486767718423341242001192622148174637868344847203636625641788715295131755238*centerUnit)

def node57R : ℚ := 5

def node57PBound : ℚ := (2052055648866173464629579074430018985855443546059982537183939455351964572934820546726572825796800086416931657007638474852775415469726051188899136690577115755371289994564336178826611584246091824010081655852714041466486753776110177872253610580232585825878668212117488021709772297148321447009188236142770887470580407201212608361463230545377671955392506905383068955280529546962714444597585297798219792160688700119979562414958735661731747688473955767008795767493222092549441873793493456158974132999102407149264746396473814792421255799044552259294009701218614899920564357321635869495763490502746315447714012339507599462479863774357924842587637563645612156790636344742047725955435930933611787201709383267637256186982328480577878178762657533044169352180308251264520533202468428342383088438877830545317/1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node57PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node57Center (68-j) j
def node57PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node57R (68-j)
def node57HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node57Center (67-j) j
def node57HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node57R (67-j)

theorem node57_norm_upper : |node57Center.1|+|node57Center.2|≤node57R := by decide +kernel
theorem node57_error_nonneg : ∀ j : Fin 69, 0≤node57PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node57R]) _
theorem node57_terminal : |(node57PState 68).1|+|(node57PState 68).2|≤node57PError 68 := by
  simp [node57PState, node57PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node57_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node57Center (node57PState (j+1)) (node57PState j)).1|+
    |(ratResidual (pCoefficient j) node57Center (node57PState (j+1)) (node57PState j)).2|+
    node57R*node57PError (j+1)≤node57PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node57_final : |(node57PState 0).1|+|(node57PState 0).2|+node57PError 0≤node57PBound := by
  decide +kernel
theorem node57_P_value_bound : ‖p67.eval (ratComplex node57Center)‖≤(node57PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node57_norm_upper 68 node57_final

theorem node57_H_error_nonneg : ∀ j : Fin 68,0≤node57HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node57R]) _
theorem node57_H_terminal : |(node57HState 67).1|+|(node57HState 67).2|≤node57HError 67 := by
  simp [node57HState, node57HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node57_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node57Center (node57HState (j.val+1)) (node57HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node57Center (node57HState (j.val+1)) (node57HState j.val)).2|+
    node57R*node57HError (j.val+1)≤node57HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node57_H_value_error :
    ‖h66.eval (ratComplex node57Center)-ratComplex (node57HState 0)‖≤(node57HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node57_norm_upper 67
#print axioms node57_P_value_bound
#print axioms node57_H_value_error

def node58Center : ℚ × ℚ := (1735546860225992158390436159910350529177168543303759551683659222558564479917801646055094539413236111206089314021355789806352935249687052927341753350075787804782189974500919386182090939261311569041811134933015376116829515062887316030848412810217702880946171275750103152390392448232482043435406725394841*centerUnit,3240022049245456969915243943826694177583882674050604001335265815404665567400153851445814272510001012809007784251389953133561082455738667204719601781936634676174254524791629278125432319366795165718304429982329726202960153431134486767718423341242001192622148174637868344847203636625641788715295131755237*centerUnit)

def node58R : ℚ := 5

def node58PBound : ℚ := (2052055648866173464629579074430018985855443546059982537183939455351964572934820546726572825796800086416931657007638474852775415469726051188899136690577115755371289994564336178826611584246091824010081655852714041466486753776110177872253610580232585825878668212117488021709772297148321447009188236142770887470580407201212608361463230545377671955392506905383068955280529546962714444597585297798219792160688700119979562414958735661731747688473955767008795767493222092549441873793493456158974132999102407149264746396473814792421255799044552259294009701218614899920564357321635869495763490502746315447714012339507599462479863774357924842587637563645612156790636344742047725955435930933611787201709383267637256186982328480577878178762657533044169352180308251264520533202468428342383088438877830545317/1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node58PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node58Center (68-j) j
def node58PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node58R (68-j)
def node58HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node58Center (67-j) j
def node58HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node58R (67-j)

theorem node58_norm_upper : |node58Center.1|+|node58Center.2|≤node58R := by decide +kernel
theorem node58_error_nonneg : ∀ j : Fin 69, 0≤node58PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node58R]) _
theorem node58_terminal : |(node58PState 68).1|+|(node58PState 68).2|≤node58PError 68 := by
  simp [node58PState, node58PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node58_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node58Center (node58PState (j+1)) (node58PState j)).1|+
    |(ratResidual (pCoefficient j) node58Center (node58PState (j+1)) (node58PState j)).2|+
    node58R*node58PError (j+1)≤node58PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node58_final : |(node58PState 0).1|+|(node58PState 0).2|+node58PError 0≤node58PBound := by
  decide +kernel
theorem node58_P_value_bound : ‖p67.eval (ratComplex node58Center)‖≤(node58PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node58_norm_upper 68 node58_final

theorem node58_H_error_nonneg : ∀ j : Fin 68,0≤node58HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node58R]) _
theorem node58_H_terminal : |(node58HState 67).1|+|(node58HState 67).2|≤node58HError 67 := by
  simp [node58HState, node58HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node58_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node58Center (node58HState (j.val+1)) (node58HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node58Center (node58HState (j.val+1)) (node58HState j.val)).2|+
    node58R*node58HError (j.val+1)≤node58HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node58_H_value_error :
    ‖h66.eval (ratComplex node58Center)-ratComplex (node58HState 0)‖≤(node58HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node58_norm_upper 67
#print axioms node58_P_value_bound
#print axioms node58_H_value_error

def node59Center : ℚ × ℚ := (-1762059518557522997916600748741901578941393917871477269639150665835000402987923515257524419223474322934862421256738947587880091726829364754614640797150800225889804242715753363479816971828471994388219020434101179555411572890439111017191739443905142927326718838216156085880313795764583679053525438357265*centerUnit,-3944351470706968763825805928429835935719340186867137131822936571204317670350680740912301075507209465863787675758226404062351176222066857349312511238118180239043973223309883448327826065860770778067189236854024488641990940405021714698386150720838357052165932234499602185057806571307691933879456753402729*centerUnit)

def node59R : ℚ := 6

def node59PBound : ℚ := (2890163072652841833234425358896496461209935347286599586996689775542757803668091915873925126228606606493314579282815909614676101269366431959051702310472523628489831713419427769113897503048908586264120322389671443612526285316148420280331080854920624868548871497801756839655652323668230287239794139686971672569417571168865455238987838038667108180003302725421662428291547346140584101922435348743156156294920134714698390147156162472589822189811395471956496642040836866291424060171916320323339667825138003135764165510734782654644388064307153492377947775803282640063863196468433885683514897786576396605398040065708647164657425455725784882053334735463592549989694258344556539387465209473468244160845036577119474550185063794342902020870613450950335711371720012553457880560639238640386009274255889915824424567703/423516473627150169534161250339820981025695800781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node59PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node59Center (68-j) j
def node59PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node59R (68-j)
def node59HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node59Center (67-j) j
def node59HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node59R (67-j)

theorem node59_norm_upper : |node59Center.1|+|node59Center.2|≤node59R := by decide +kernel
theorem node59_error_nonneg : ∀ j : Fin 69, 0≤node59PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node59R]) _
theorem node59_terminal : |(node59PState 68).1|+|(node59PState 68).2|≤node59PError 68 := by
  simp [node59PState, node59PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node59_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node59Center (node59PState (j+1)) (node59PState j)).1|+
    |(ratResidual (pCoefficient j) node59Center (node59PState (j+1)) (node59PState j)).2|+
    node59R*node59PError (j+1)≤node59PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node59_final : |(node59PState 0).1|+|(node59PState 0).2|+node59PError 0≤node59PBound := by
  decide +kernel
theorem node59_P_value_bound : ‖p67.eval (ratComplex node59Center)‖≤(node59PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node59_norm_upper 68 node59_final

theorem node59_H_error_nonneg : ∀ j : Fin 68,0≤node59HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node59R]) _
theorem node59_H_terminal : |(node59HState 67).1|+|(node59HState 67).2|≤node59HError 67 := by
  simp [node59HState, node59HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node59_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node59Center (node59HState (j.val+1)) (node59HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node59Center (node59HState (j.val+1)) (node59HState j.val)).2|+
    node59R*node59HError (j.val+1)≤node59HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node59_H_value_error :
    ‖h66.eval (ratComplex node59Center)-ratComplex (node59HState 0)‖≤(node59HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node59_norm_upper 67
#print axioms node59_P_value_bound
#print axioms node59_H_value_error

def node60Center : ℚ × ℚ := (-1762059518557522997916600748741901578941393917871477269639150665835000402987923515257524419223474322934862421256738947587880091726829364754614640797150800225889804242715753363479816971828471994388219020434101179555411572890439111017191739443905142927326718838216156085880313795764583679053525438357265*centerUnit,3944351470706968763825805928429835935719340186867137131822936571204317670350680740912301075507209465863787675758226404062351176222066857349312511238118180239043973223309883448327826065860770778067189236854024488641990940405021714698386150720838357052165932234499602185057806571307691933879456753402728*centerUnit)

def node60R : ℚ := 6

def node60PBound : ℚ := (2890163072652841833234425358896496461209935347286599586996689775542757803668091915873925126228606606493314579282815909614676101269366431959051702310472523628489831713419427769113897503048908586264120322389671443612526285316148420280331080854920624868548871497801756839655652323668230287239794139686971672569417571168865455238987838038667108180003302725421662428291547346140584101922435348743156156294920134714698390147156162472589822189811395471956496642040836866291424060171916320323339667825138003135764165510734782654644388064307153492377947775803282640063863196468433885683514897786576396605398040065708647164657425455725784882053334735463592549989694258344556539387465209473468244160845036577119474550185063794342902020870613450950335711371720012553457880560639238640386009274255889915824424567703/423516473627150169534161250339820981025695800781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node60PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node60Center (68-j) j
def node60PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node60R (68-j)
def node60HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node60Center (67-j) j
def node60HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node60R (67-j)

theorem node60_norm_upper : |node60Center.1|+|node60Center.2|≤node60R := by decide +kernel
theorem node60_error_nonneg : ∀ j : Fin 69, 0≤node60PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node60R]) _
theorem node60_terminal : |(node60PState 68).1|+|(node60PState 68).2|≤node60PError 68 := by
  simp [node60PState, node60PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node60_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node60Center (node60PState (j+1)) (node60PState j)).1|+
    |(ratResidual (pCoefficient j) node60Center (node60PState (j+1)) (node60PState j)).2|+
    node60R*node60PError (j+1)≤node60PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node60_final : |(node60PState 0).1|+|(node60PState 0).2|+node60PError 0≤node60PBound := by
  decide +kernel
theorem node60_P_value_bound : ‖p67.eval (ratComplex node60Center)‖≤(node60PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node60_norm_upper 68 node60_final

theorem node60_H_error_nonneg : ∀ j : Fin 68,0≤node60HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node60R]) _
theorem node60_H_terminal : |(node60HState 67).1|+|(node60HState 67).2|≤node60HError 67 := by
  simp [node60HState, node60HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node60_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node60Center (node60HState (j.val+1)) (node60HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node60Center (node60HState (j.val+1)) (node60HState j.val)).2|+
    node60R*node60HError (j.val+1)≤node60HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node60_H_value_error :
    ‖h66.eval (ratComplex node60Center)-ratComplex (node60HState 0)‖≤(node60HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node60_norm_upper 67
#print axioms node60_P_value_bound
#print axioms node60_H_value_error

def node61Center : ℚ × ℚ := (1162111164298750667238893510859525714974666077276056552230513682971755779538947518371310621532476256023582312283995102286242355467313875115069823643206021861154867623639026767970010202406130052918441274092403080495293951510668774579536647480670000752000497309722967664631427320123719322522340733743563*centerUnit,-5192761064539095615446039423686346335506921724222993621069000296834277644743920582756746077594803560563648789692671700514973477356640240243820816610234222631322154461176716691740136565533055336514136662280423486160176858500048665341748987709393911015820488536049441558562430760237795197603142925137312*centerUnit)

def node61R : ℚ := 7

def node61PBound : ℚ := (2647974958362388050152195462746604502449097668094977371031403968071511454066006533688684140304218842080349781766669102822875535244125071304258240746323768706193199798121671499673569177251730687230940469026152272493054740364171594666520118196262769443292205392505192239606263548054213521026395648521515605610106714520827803816104835796560717230911627337505447769821254925512426206759405821064044459791716211079716312991109129747425048052465915040023961897273186099721977296401432791827674046644661875461409223907555563194430810993715388466733286860729861008520682152535835190896852846044753775599085439031814745722619543330138552490530231197959039347949336514828673059891153264008869816428995006678646064989052146191818331099278735049018097707832575108453802055307699488239705327598198012224136604528357973975288206740047/555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node61PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node61Center (68-j) j
def node61PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node61R (68-j)
def node61HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node61Center (67-j) j
def node61HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node61R (67-j)

theorem node61_norm_upper : |node61Center.1|+|node61Center.2|≤node61R := by decide +kernel
theorem node61_error_nonneg : ∀ j : Fin 69, 0≤node61PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node61R]) _
theorem node61_terminal : |(node61PState 68).1|+|(node61PState 68).2|≤node61PError 68 := by
  simp [node61PState, node61PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node61_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node61Center (node61PState (j+1)) (node61PState j)).1|+
    |(ratResidual (pCoefficient j) node61Center (node61PState (j+1)) (node61PState j)).2|+
    node61R*node61PError (j+1)≤node61PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node61_final : |(node61PState 0).1|+|(node61PState 0).2|+node61PError 0≤node61PBound := by
  decide +kernel
theorem node61_P_value_bound : ‖p67.eval (ratComplex node61Center)‖≤(node61PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node61_norm_upper 68 node61_final

theorem node61_H_error_nonneg : ∀ j : Fin 68,0≤node61HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node61R]) _
theorem node61_H_terminal : |(node61HState 67).1|+|(node61HState 67).2|≤node61HError 67 := by
  simp [node61HState, node61HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node61_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node61Center (node61HState (j.val+1)) (node61HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node61Center (node61HState (j.val+1)) (node61HState j.val)).2|+
    node61R*node61HError (j.val+1)≤node61HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node61_H_value_error :
    ‖h66.eval (ratComplex node61Center)-ratComplex (node61HState 0)‖≤(node61HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node61_norm_upper 67
#print axioms node61_P_value_bound
#print axioms node61_H_value_error

def node62Center : ℚ × ℚ := (1162111164298750667238893510859525714974666077276056552230513682971755779538947518371310621532476256023582312283995102286242355467313875115069823643206021861154867623639026767970010202406130052918441274092403080495293951510668774579536647480670000752000497309722967664631427320123719322522340733743563*centerUnit,5192761064539095615446039423686346335506921724222993621069000296834277644743920582756746077594803560563648789692671700514973477356640240243820816610234222631322154461176716691740136565533055336514136662280423486160176858500048665341748987709393911015820488536049441558562430760237795197603142925137311*centerUnit)

def node62R : ℚ := 7

def node62PBound : ℚ := (2647974958362388050152195462746604502449097668094977371031403968071511454066006533688684140304218842080349781766669102822875535244125071304258240746323768706193199798121671499673569177251730687230940469026152272493054740364171594666520118196262769443292205392505192239606263548054213521026395648521515605610106714520827803816104835796560717230911627337505447769821254925512426206759405821064044459791716211079716312991109129747425048052465915040023961897273186099721977296401432791827674046644661875461409223907555563194430810993715388466733286860729861008520682152535835190896852846044753775599085439031814745722619543330138552490530231197959039347949336514828673059891153264008869816428995006678646064989052146191818331099278735049018097707832575108453802055307699488239705327598198012224136604528357973975288206740047/555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node62PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node62Center (68-j) j
def node62PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node62R (68-j)
def node62HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node62Center (67-j) j
def node62HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node62R (67-j)

theorem node62_norm_upper : |node62Center.1|+|node62Center.2|≤node62R := by decide +kernel
theorem node62_error_nonneg : ∀ j : Fin 69, 0≤node62PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node62R]) _
theorem node62_terminal : |(node62PState 68).1|+|(node62PState 68).2|≤node62PError 68 := by
  simp [node62PState, node62PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node62_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node62Center (node62PState (j+1)) (node62PState j)).1|+
    |(ratResidual (pCoefficient j) node62Center (node62PState (j+1)) (node62PState j)).2|+
    node62R*node62PError (j+1)≤node62PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node62_final : |(node62PState 0).1|+|(node62PState 0).2|+node62PError 0≤node62PBound := by
  decide +kernel
theorem node62_P_value_bound : ‖p67.eval (ratComplex node62Center)‖≤(node62PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node62_norm_upper 68 node62_final

theorem node62_H_error_nonneg : ∀ j : Fin 68,0≤node62HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node62R]) _
theorem node62_H_terminal : |(node62HState 67).1|+|(node62HState 67).2|≤node62HError 67 := by
  simp [node62HState, node62HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node62_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node62Center (node62HState (j.val+1)) (node62HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node62Center (node62HState (j.val+1)) (node62HState j.val)).2|+
    node62R*node62HError (j.val+1)≤node62HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node62_H_value_error :
    ‖h66.eval (ratComplex node62Center)-ratComplex (node62HState 0)‖≤(node62HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node62_norm_upper 67
#print axioms node62_P_value_bound
#print axioms node62_H_value_error

def node63Center : ℚ × ℚ := (643325610835764044668509993152158607947115134257943584557293084287884817875404972344754288201372100725823351583068551856765629490045021409605341294737414172491182989578053305807659516314840208661472329298320031538370413772351659511644316090598613243226592492978237941128410804620221095709204893502809*centerUnit,-17917103623549026284028573938412247051309869391854416386756415697025928765952166450266101940647822822897245138713281913425110616527555127228517671481991522627575735826970712775046259816689168215402193920638434348621131050385376733198932268638344363636139619144236651236392591542673420230100024346942650*centerUnit)

def node63R : ℚ := 19

def node63PBound : ℚ := (1134566431782834393745752184366521278456892782718967893357770456665106663226349841857509694109837531400807437052753780088096185845211946558518123317505981832003135677323012351236431389833415799831206392466801942939582424883049776803763639977516932743813291589060688029870180534257682345827483720873227711960746444080949846900084505325360020952398377198284498744746273201946080871409903980156846970241217165870669698315910528346400202493940068061175869822236453885464761146528394751902000266894045689967368033025486405086454221559648930510674152633593610452072931107766941059096987569382719754931035370085987446833297922942279926029410909440279982354806823551337117711600672181492655115360286029801117927902297250475007257580571773626578801183872014529672447240875422760307952847734475295039489470890652381242261001591595623560052398402072674358586434038208871/1164153218269348144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node63PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node63Center (68-j) j
def node63PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node63R (68-j)
def node63HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node63Center (67-j) j
def node63HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node63R (67-j)

theorem node63_norm_upper : |node63Center.1|+|node63Center.2|≤node63R := by decide +kernel
theorem node63_error_nonneg : ∀ j : Fin 69, 0≤node63PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node63R]) _
theorem node63_terminal : |(node63PState 68).1|+|(node63PState 68).2|≤node63PError 68 := by
  simp [node63PState, node63PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node63_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node63Center (node63PState (j+1)) (node63PState j)).1|+
    |(ratResidual (pCoefficient j) node63Center (node63PState (j+1)) (node63PState j)).2|+
    node63R*node63PError (j+1)≤node63PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node63_final : |(node63PState 0).1|+|(node63PState 0).2|+node63PError 0≤node63PBound := by
  decide +kernel
theorem node63_P_value_bound : ‖p67.eval (ratComplex node63Center)‖≤(node63PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node63_norm_upper 68 node63_final

theorem node63_H_error_nonneg : ∀ j : Fin 68,0≤node63HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node63R]) _
theorem node63_H_terminal : |(node63HState 67).1|+|(node63HState 67).2|≤node63HError 67 := by
  simp [node63HState, node63HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node63_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node63Center (node63HState (j.val+1)) (node63HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node63Center (node63HState (j.val+1)) (node63HState j.val)).2|+
    node63R*node63HError (j.val+1)≤node63HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node63_H_value_error :
    ‖h66.eval (ratComplex node63Center)-ratComplex (node63HState 0)‖≤(node63HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node63_norm_upper 67
#print axioms node63_P_value_bound
#print axioms node63_H_value_error

def node64Center : ℚ × ℚ := (643325610835764044668509993152158607947115134257943584557293084287884817875404972344754288201372100725823351583068551856765629490045021409605341294737414172491182989578053305807659516314840208661472329298320031538370413772351659511644316090598613243226592492978237941128410804620221095709204893502809*centerUnit,17917103623549026284028573938412247051309869391854416386756415697025928765952166450266101940647822822897245138713281913425110616527555127228517671481991522627575735826970712775046259816689168215402193920638434348621131050385376733198932268638344363636139619144236651236392591542673420230100024346942649*centerUnit)

def node64R : ℚ := 19

def node64PBound : ℚ := (1134566431782834393745752184366521278456892782718967893357770456665106663226349841857509694109837531400807437052753780088096185845211946558518123317505981832003135677323012351236431389833415799831206392466801942939582424883049776803763639977516932743813291589060688029870180534257682345827483720873227711960746444080949846900084505325360020952398377198284498744746273201946080871409903980156846970241217165870669698315910528346400202493940068061175869822236453885464761146528394751902000266894045689967368033025486405086454221559648930510674152633593610452072931107766941059096987569382719754931035370085987446833297922942279926029410909440279982354806823551337117711600672181492655115360286029801117927902297250475007257580571773626578801183872014529672447240875422760307952847734475295039489470890652381242261001591595623560052398402072674358586434038208871/1164153218269348144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node64PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node64Center (68-j) j
def node64PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node64R (68-j)
def node64HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node64Center (67-j) j
def node64HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node64R (67-j)

theorem node64_norm_upper : |node64Center.1|+|node64Center.2|≤node64R := by decide +kernel
theorem node64_error_nonneg : ∀ j : Fin 69, 0≤node64PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node64R]) _
theorem node64_terminal : |(node64PState 68).1|+|(node64PState 68).2|≤node64PError 68 := by
  simp [node64PState, node64PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node64_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node64Center (node64PState (j+1)) (node64PState j)).1|+
    |(ratResidual (pCoefficient j) node64Center (node64PState (j+1)) (node64PState j)).2|+
    node64R*node64PError (j+1)≤node64PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node64_final : |(node64PState 0).1|+|(node64PState 0).2|+node64PError 0≤node64PBound := by
  decide +kernel
theorem node64_P_value_bound : ‖p67.eval (ratComplex node64Center)‖≤(node64PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node64_norm_upper 68 node64_final

theorem node64_H_error_nonneg : ∀ j : Fin 68,0≤node64HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node64R]) _
theorem node64_H_terminal : |(node64HState 67).1|+|(node64HState 67).2|≤node64HError 67 := by
  simp [node64HState, node64HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node64_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node64Center (node64HState (j.val+1)) (node64HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node64Center (node64HState (j.val+1)) (node64HState j.val)).2|+
    node64R*node64HError (j.val+1)≤node64HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node64_H_value_error :
    ‖h66.eval (ratComplex node64Center)-ratComplex (node64HState 0)‖≤(node64HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node64_norm_upper 67
#print axioms node64_P_value_bound
#print axioms node64_H_value_error

def node65Center : ℚ × ℚ := (29868879060689033546074636348145376468020884400424495456547165888020591292813357912644703472735947305344861704339351321379708043811543557940557590080321770972871290518952171464919982052181494969524518894215281478842685349952243002029492859006761761085386128365831912656672299899514128503782722247700930*centerUnit,-25714042471928031076925790694566867510488062322258106838694402384450803270676017539210895570816501057579722190482135028498958399174159031334834278244747146301893232618791941524695895383021805793350470192539131728271033309217458091971345415591358261529679306352054021476548546456231411495509916920043289*centerUnit)

def node65R : ℚ := 56

def node65PBound : ℚ := (26929667281281965106276846462464074760304065776766191556986907124632488119437247501816629204698780908530659243617284122075487952152757425417083632156078418373497080688696128100527367121033437055807129042437265941217826811313455300381931799960493239634771257086800805302367725296466284607843047545780985285195982009431119429304053314845416902634656458288172001191944253996407538187398180726189590082693055499897199540769341352432917378073437857930254337603848173010856109981251392543246224426311377706926092217546324423085292696116013736567374987000430877498661414719877074088857432237583762788869370234305797979800479965184025122536989706727178193220540002793946994535968265703702014080499513238080013210578935972758642440437706320422165461585844841835678892993590458157934949594788626139712655385373135197719744330693531259093758004822386613637151607166372721/693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node65PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node65Center (68-j) j
def node65PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node65R (68-j)
def node65HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node65Center (67-j) j
def node65HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node65R (67-j)

theorem node65_norm_upper : |node65Center.1|+|node65Center.2|≤node65R := by decide +kernel
theorem node65_error_nonneg : ∀ j : Fin 69, 0≤node65PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node65R]) _
theorem node65_terminal : |(node65PState 68).1|+|(node65PState 68).2|≤node65PError 68 := by
  simp [node65PState, node65PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node65_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node65Center (node65PState (j+1)) (node65PState j)).1|+
    |(ratResidual (pCoefficient j) node65Center (node65PState (j+1)) (node65PState j)).2|+
    node65R*node65PError (j+1)≤node65PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node65_final : |(node65PState 0).1|+|(node65PState 0).2|+node65PError 0≤node65PBound := by
  decide +kernel
theorem node65_P_value_bound : ‖p67.eval (ratComplex node65Center)‖≤(node65PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node65_norm_upper 68 node65_final

theorem node65_H_error_nonneg : ∀ j : Fin 68,0≤node65HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node65R]) _
theorem node65_H_terminal : |(node65HState 67).1|+|(node65HState 67).2|≤node65HError 67 := by
  simp [node65HState, node65HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node65_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node65Center (node65HState (j.val+1)) (node65HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node65Center (node65HState (j.val+1)) (node65HState j.val)).2|+
    node65R*node65HError (j.val+1)≤node65HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node65_H_value_error :
    ‖h66.eval (ratComplex node65Center)-ratComplex (node65HState 0)‖≤(node65HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node65_norm_upper 67
#print axioms node65_P_value_bound
#print axioms node65_H_value_error

def node66Center : ℚ × ℚ := (29868879060689033546074636348145376468020884400424495456547165888020591292813357912644703472735947305344861704339351321379708043811543557940557590080321770972871290518952171464919982052181494969524518894215281478842685349952243002029492859006761761085386128365831912656672299899514128503782722247700930*centerUnit,25714042471928031076925790694566867510488062322258106838694402384450803270676017539210895570816501057579722190482135028498958399174159031334834278244747146301893232618791941524695895383021805793350470192539131728271033309217458091971345415591358261529679306352054021476548546456231411495509916920043288*centerUnit)

def node66R : ℚ := 56

def node66PBound : ℚ := (26929667281281965106276846462464074760304065776766191556986907124632488119437247501816629204698780908530659243617284122075487952152757425417083632156078418373497080688696128100527367121033437055807129042437265941217826811313455300381931799960493239634771257086800805302367725296466284607843047545780985285195982009431119429304053314845416902634656458288172001191944253996407538187398180726189590082693055499897199540769341352432917378073437857930254337603848173010856109981251392543246224426311377706926092217546324423085292696116013736567374987000430877498661414719877074088857432237583762788869370234305797979800479965184025122536989706727178193220540002793946994535968265703702014080499513238080013210578935972758642440437706320422165461585844841835678892993590458157934949594788626139712655385373135197719744330693531259093758004822386613637151607166372721/693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)


def node66PState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision pCoefficient node66Center (68-j) j
def node66PError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node66R (68-j)
def node66HState (j : ℕ) : ℚ × ℚ :=
  QuantitativeArithmeticRoundedHorner.value Rounded.precision hCoefficient node66Center (67-j) j
def node66HError (j : ℕ) : ℚ :=
  QuantitativeArithmeticRoundedHorner.error Rounded.precision node66R (67-j)

theorem node66_norm_upper : |node66Center.1|+|node66Center.2|≤node66R := by decide +kernel
theorem node66_error_nonneg : ∀ j : Fin 69, 0≤node66PError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node66R]) _
theorem node66_terminal : |(node66PState 68).1|+|(node66PState 68).2|≤node66PError 68 := by
  simp [node66PState, node66PError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node66_all_steps : ∀ j<68,
    |(ratResidual (pCoefficient j) node66Center (node66PState (j+1)) (node66PState j)).1|+
    |(ratResidual (pCoefficient j) node66Center (node66PState (j+1)) (node66PState j)).2|+
    node66R*node66PError (j+1)≤node66PError j := by
  intro j hj
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ hj
theorem node66_final : |(node66PState 0).1|+|(node66PState 0).2|+node66PError 0≤node66PBound := by
  decide +kernel
theorem node66_P_value_bound : ‖p67.eval (ratComplex node66Center)‖≤(node66PBound:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_bound _ _ _ _ _
    Rounded.precision_pos node66_norm_upper 68 node66_final

theorem node66_H_error_nonneg : ∀ j : Fin 68,0≤node66HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.error_nonneg _ _ Rounded.precision_pos
    (by norm_num [node66R]) _
theorem node66_H_terminal : |(node66HState 67).1|+|(node66HState 67).2|≤node66HError 67 := by
  simp [node66HState, node66HError, QuantitativeArithmeticRoundedHorner.value,
    QuantitativeArithmeticRoundedHorner.error]
theorem node66_H_steps : ∀ j : Fin 67,
    |(ratResidual (hCoefficient j.val) node66Center (node66HState (j.val+1)) (node66HState j.val)).1|+
    |(ratResidual (hCoefficient j.val) node66Center (node66HState (j.val+1)) (node66HState j.val)).2|+
    node66R*node66HError (j.val+1)≤node66HError j.val := by
  intro j
  exact QuantitativeArithmeticRoundedHorner.steps _ _ _ _ Rounded.precision_pos _ _ j.isLt
theorem node66_H_value_error :
    ‖h66.eval (ratComplex node66Center)-ratComplex (node66HState 0)‖≤(node66HError 0:ℝ) := by
  exact QuantitativeArithmeticRoundedHorner.polynomial_error _ _ _ _
    Rounded.precision_pos node66_norm_upper 67
#print axioms node66_P_value_bound
#print axioms node66_H_value_error

end QuantitativeArithmeticSmallLevelTwentyFive.PositiveRoot
