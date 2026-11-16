module
public meta import SmallLevelRationalCoefficientComputeV1
public meta import SmallLevelCertificateBatchCommandV1
public import SmallLevelTwentySixMMPPariSyzygyIndexColumnIndexDataSeriesV4
public import SmallLevelSparseRationalPolynomialCheckV1
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
public meta import SmallLevelPolynomialCertificateCommandsV4
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
certificate_batch {
@[expose] public noncomputable section
namespace SmallLevelTwentySixMMPPariSyzygy6Column5
open SmallLevelSparseRationalPolynomialCheck SmallLevelPolynomialCoefficientCertificate
noncomputable def vars (y z w a b u : ℂ) : ℕ→ℂ := fun i => match i with | 0 => y | 1 => z | 2 => w | 3 => a | 4 => b | 5 => u | _ => 0
compact_certificate_declaration noncomputable def r_c0_0 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 5164665296902233408) (.pow (.var 3) 1)) (.constant (-125) 215194387370926392)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 286925849827901856) (.pow (.var 3) 1)) (.constant (-875) 191283899885267904)) (.pow (.var 3) 1)) (.constant (2375) 21253766653918656))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (1) 35422944423197760) (.pow (.var 3) 1)) (.constant (1) 2361529628213184)) (.pow (.var 3) 1)) (.constant (-1) 163995113070360)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 31880649980877984) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 7084588884639552) (.pow (.var 4) 1)) (.constant (125) 2656720831739832))) (.pow (.var 3) 1)) (.add (.mul (.constant (25) 2361529628213184) (.pow (.var 4) 1)) (.constant (6625) 2361529628213184))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 32799022614072) (.pow (.var 4) 1)) (.constant (-125) 43732030152096))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (1) 1967941356844320) (.pow (.var 3) 1)) (.constant (1) 131196090456288)) (.pow (.var 3) 1)) (.constant (-1) 13252130349120)) (.pow (.var 3) 1)) (.constant (-1) 3239409640896)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 3542294442319776) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 393588271368864) (.pow (.var 4) 1)) (.constant (625) 2361529628213184))) (.pow (.var 3) 1)) (.add (.mul (.constant (25) 131196090456288) (.pow (.var 4) 1)) (.constant (125) 7951278209472))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 2650426069824) (.pow (.var 4) 1)) (.constant (-125) 911083961502))) (.pow (.var 3) 1)) (.add (.mul (.constant (-25) 3239409640896) (.pow (.var 4) 1)) (.constant (-125) 134975401704))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (1) 437320301520960) (.pow (.var 3) 1)) (.constant (1) 29154686768064)) (.pow (.var 3) 1)) (.constant (-1) 2699508034080)) (.pow (.var 3) 1)) (.constant (-1) 359934404544)) (.pow (.var 3) 1)) (.constant (1) 66654519360)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 787176542737728) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 87464060304192) (.pow (.var 4) 1)) (.constant (-125) 131196090456288))) (.pow (.var 3) 1)) (.add (.mul (.constant (25) 29154686768064) (.pow (.var 4) 1)) (.constant (625) 29154686768064))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 539901606816) (.pow (.var 4) 1)) (.constant (-125) 190553508288))) (.pow (.var 3) 1)) (.add (.mul (.constant (-25) 359934404544) (.pow (.var 4) 1)) (.constant (-125) 29994533712))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 13330903872) (.pow (.var 4) 1)) (.constant (125) 4443634624)))))
compact_certificate_declaration noncomputable def n_c0_0 : Poly := rational_polynomial% "125/4443634624:;-125/134975401704:0;1/66654519360:2;-125/29994533712:3;5/13330903872:4;-125/43732030152096:0,0;-1/3239409640896:0,2;-125/911083961502:0,3;-25/3239409640896:0,4;-1/359934404544:2,3;-125/190553508288:3,3;-25/359934404544:3,4;2375/21253766653918656:0,0,0;-1/163995113070360:0,0,2;6625/2361529628213184:0,0,3;-5/32799022614072:0,0,4;-1/13252130349120:0,2,3;125/7951278209472:0,3,3;-5/2650426069824:0,3,4;-1/2699508034080:2,3,3;625/29154686768064:3,3,3;-5/539901606816:3,3,4;-125/215194387370926392:0,0,0,0;-875/191283899885267904:0,0,0,3;1/2361529628213184:0,0,2,3;125/2656720831739832:0,0,3,3;25/2361529628213184:0,0,3,4;1/131196090456288:0,2,3,3;625/2361529628213184:0,3,3,3;25/131196090456288:0,3,3,4;1/29154686768064:2,3,3,3;-125/131196090456288:3,3,3,3;25/29154686768064:3,3,3,4;-125/5164665296902233408:0,0,0,0,3;-125/286925849827901856:0,0,0,3,3;1/35422944423197760:0,0,2,3,3;-125/31880649980877984:0,0,3,3,3;5/7084588884639552:0,0,3,3,4;1/1967941356844320:0,2,3,3,3;-125/3542294442319776:0,3,3,3,3;5/393588271368864:0,3,3,3,4;1/437320301520960:2,3,3,3,3;-125/787176542737728:3,3,3,3,3;5/87464060304192:3,3,3,3,4"
compact_certificate_declaration theorem normalized_c0_0 : r_c0_0.coefficients=n_c0_0 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_0_value (y z w a b u : ℂ) :
    r_c0_0.value (vars y z w a b u)=c0_0 y z w a b := by
  dsimp only [r_c0_0, Expr.value, c0_0, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_0_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_0=c0_0 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_0.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_0).trans (r_c0_0_value y z w a b u))
compact_certificate_declaration noncomputable def r_c0_1 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (625) 20658661187608933632) (.pow (.var 3) 1)) (.constant (625) 860777549483705568)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (875) 2295406798623214848) (.pow (.var 3) 1)) (.constant (625) 127522599923511936)) (.pow (.var 3) 1)) (.constant (-6625) 85015066615674624))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 47230592564263680) (.pow (.var 3) 1)) (.constant (-1) 2623921809125760)) (.pow (.var 3) 1)) (.constant (1) 327990226140720)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (625) 255045199847023872) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 9446118512852736) (.pow (.var 4) 1)) (.constant (-2375) 85015066615674624))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 524784361825152) (.pow (.var 4) 1)) (.constant (-9125) 4723059256426368))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 65598045228144) (.pow (.var 4) 1)) (.constant (-125) 40368027832704))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 5247843618251520) (.pow (.var 3) 1)) (.constant (-7) 1311960904562880)) (.pow (.var 3) 1)) (.constant (-1) 58309373536128)) (.pow (.var 3) 1)) (.constant (1) 3239409640896)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 9446118512852736) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 1049568723650304) (.pow (.var 4) 1)) (.constant (875) 9446118512852736))) (.pow (.var 3) 1)) (.add (.mul (.constant (-35) 262392180912576) (.pow (.var 4) 1)) (.constant (-125) 32799022614072))) (.pow (.var 3) 1)) (.add (.mul (.constant (-25) 58309373536128) (.pow (.var 4) 1)) (.constant (125) 7288671692016))) (.pow (.var 3) 1)) (.add (.mul (.constant (25) 3239409640896) (.pow (.var 4) 1)) (.constant (11125) 12957638563584))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 583093735361280) (.pow (.var 3) 1)) (.constant (-1) 7198688090880)) (.pow (.var 3) 1)) (.constant (-1) 1799672022720)) (.pow (.var 3) 1)) (.constant (1) 199963558080)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 524784361825152) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 116618747072256) (.pow (.var 4) 1)) (.constant (-125) 19436457845376))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 1439737618176) (.pow (.var 4) 1)) (.constant (-625) 4319212854528))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 359934404544) (.pow (.var 4) 1)) (.constant (125) 159970846464))) (.pow (.var 3) 1)) (.mul (.constant (5) 39992711616) (.pow (.var 4) 1)))))
compact_certificate_declaration noncomputable def n_c0_1 : Poly := rational_polynomial% "11125/12957638563584:0;1/199963558080:2;125/159970846464:3;5/39992711616:4;-125/40368027832704:0,0;1/3239409640896:0,2;125/7288671692016:0,3;25/3239409640896:0,4;-1/1799672022720:2,3;-625/4319212854528:3,3;-5/359934404544:3,4;-6625/85015066615674624:0,0,0;1/327990226140720:0,0,2;-9125/4723059256426368:0,0,3;5/65598045228144:0,0,4;-1/58309373536128:0,2,3;-125/32799022614072:0,3,3;-25/58309373536128:0,3,4;-1/7198688090880:2,3,3;-125/19436457845376:3,3,3;-5/1439737618176:3,3,4;625/860777549483705568:0,0,0,0;625/127522599923511936:0,0,0,3;-1/2623921809125760:0,0,2,3;-2375/85015066615674624:0,0,3,3;-5/524784361825152:0,0,3,4;-7/1311960904562880:0,2,3,3;875/9446118512852736:0,3,3,3;-35/262392180912576:0,3,3,4;-1/583093735361280:2,3,3,3;-125/524784361825152:3,3,3,3;-5/116618747072256:3,3,3,4;625/20658661187608933632:0,0,0,0,3;875/2295406798623214848:0,0,0,3,3;-1/47230592564263680:0,0,2,3,3;625/255045199847023872:0,0,3,3,3;-5/9446118512852736:0,0,3,3,4;-1/5247843618251520:0,2,3,3,3;125/9446118512852736:0,3,3,3,3;-5/1049568723650304:0,3,3,3,4"
compact_certificate_declaration theorem normalized_c0_1 : r_c0_1.coefficients=n_c0_1 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_1_value (y z w a b u : ℂ) :
    r_c0_1.value (vars y z w a b u)=c0_1 y z w a b := by
  dsimp only [r_c0_1, Expr.value, c0_1, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_1_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_1=c0_1 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_1.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_1).trans (r_c0_1_value y z w a b u))
compact_certificate_declaration noncomputable def r_c0_2 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 9181627194492859392) (.pow (.var 3) 1)) (.constant (-125) 382567799770535808)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 834693381317532672) (.pow (.var 3) 1)) (.constant (-125) 47820974971316976)) (.pow (.var 3) 1)) (.constant (3875) 255045199847023872))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (1) 283383555385582080) (.pow (.var 3) 1)) (.constant (19) 188922370257054720)) (.pow (.var 3) 1)) (.constant (1) 2623921809125760)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-625) 1020180799388095488) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 56676711077116416) (.pow (.var 4) 1)) (.constant (2875) 340060266462698496))) (.pow (.var 3) 1)) (.add (.mul (.constant (95) 37784474051410944) (.pow (.var 4) 1)) (.constant (30625) 56676711077116416))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 524784361825152) (.pow (.var 4) 1)) (.constant (13375) 6297412341901824))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (1) 31487061709509120) (.pow (.var 3) 1)) (.constant (1) 1049568723650304)) (.pow (.var 3) 1)) (.constant (1) 107648074220544)) (.pow (.var 3) 1)) (.constant (1) 14951121419520)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 37784474051410944) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 6297412341901824) (.pow (.var 4) 1)) (.constant (-625) 18892237025705472))) (.pow (.var 3) 1)) (.add (.mul (.constant (25) 1049568723650304) (.pow (.var 4) 1)) (.constant (625) 740872040223744))) (.pow (.var 3) 1)) (.add (.mul (.constant (25) 107648074220544) (.pow (.var 4) 1)) (.constant (-625) 1399424964867072))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 2990224283904) (.pow (.var 4) 1)) (.constant (-10375) 51830554254336))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 466474988289024) (.pow (.var 3) 1)) (.constant (-31) 777458313815040)) (.pow (.var 3) 1)) (.constant (1) 7198688090880)) (.pow (.var 3) 1)) (.constant (7) 2399562696960)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (625) 4198274894601216) (.pow (.var 3) 1)) (.add (.mul (.constant (-25) 466474988289024) (.pow (.var 4) 1)) (.constant (2375) 1399424964867072))) (.pow (.var 3) 1)) (.add (.mul (.constant (-155) 155491662763008) (.pow (.var 4) 1)) (.constant (-125) 7067802852864))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 1439737618176) (.pow (.var 4) 1)) (.constant (7625) 17276851418112))) (.pow (.var 3) 1)) (.add (.mul (.constant (35) 479912539392) (.pow (.var 4) 1)) (.constant (375) 71098153984)))))
compact_certificate_declaration noncomputable def n_c0_2 : Poly := rational_polynomial% "375/71098153984:;-10375/51830554254336:0;7/2399562696960:2;7625/17276851418112:3;35/479912539392:4;13375/6297412341901824:0,0;1/14951121419520:0,2;-625/1399424964867072:0,3;5/2990224283904:0,4;1/7198688090880:2,3;-125/7067802852864:3,3;5/1439737618176:3,4;3875/255045199847023872:0,0,0;1/2623921809125760:0,0,2;30625/56676711077116416:0,0,3;5/524784361825152:0,0,4;1/107648074220544:0,2,3;625/740872040223744:0,3,3;25/107648074220544:0,3,4;-31/777458313815040:2,3,3;2375/1399424964867072:3,3,3;-155/155491662763008:3,3,4;-125/382567799770535808:0,0,0,0;-125/47820974971316976:0,0,0,3;19/188922370257054720:0,0,2,3;2875/340060266462698496:0,0,3,3;95/37784474051410944:0,0,3,4;1/1049568723650304:0,2,3,3;-625/18892237025705472:0,3,3,3;25/1049568723650304:0,3,3,4;-1/466474988289024:2,3,3,3;625/4198274894601216:3,3,3,3;-25/466474988289024:3,3,3,4;-125/9181627194492859392:0,0,0,0,3;-125/834693381317532672:0,0,0,3,3;1/283383555385582080:0,0,2,3,3;-625/1020180799388095488:0,0,3,3,3;5/56676711077116416:0,0,3,3,4;1/31487061709509120:0,2,3,3,3;-125/37784474051410944:0,3,3,3,3;5/6297412341901824:0,3,3,3,4"
compact_certificate_declaration theorem normalized_c0_2 : r_c0_2.coefficients=n_c0_2 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_2_value (y z w a b u : ℂ) :
    r_c0_2.value (vars y z w a b u)=c0_2 y z w a b := by
  dsimp only [r_c0_2, Expr.value, c0_2, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_2_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_2=c0_2 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_2.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_2).trans (r_c0_2_value y z w a b u))
compact_certificate_declaration noncomputable def r_c0_3 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (875) 330538579001742938112) (.pow (.var 3) 1)) (.constant (875) 13772440791739289088)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (625) 18363254388985718784) (.pow (.var 3) 1)) (.constant (125) 185487418070562816)) (.pow (.var 3) 1)) (.constant (-875) 453413688616931328))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-1) 125948246838036480) (.pow (.var 3) 1)) (.constant (-1) 5247843618251520)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 1360241065850793984) (.pow (.var 3) 1)) (.constant (-125) 340060266462698496)) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 25189649367607296) (.pow (.var 4) 1)) (.constant (-625) 8396549789202432))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 1049568723650304) (.pow (.var 4) 1)) (.constant (-2375) 3148706170950912))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 20991374473006080) (.pow (.var 3) 1)) (.constant (-41) 27988499297341440)) (.pow (.var 3) 1)) (.constant (-1) 79739314237440)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 37784474051410944) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 4198274894601216) (.pow (.var 4) 1)) (.constant (-125) 968832667984896))) (.pow (.var 3) 1)) (.add (.mul (.constant (-205) 5597699859468288) (.pow (.var 4) 1)) (.constant (-875) 2798849929734144))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 15947862847488) (.pow (.var 4) 1)) (.constant (2875) 69107405672448))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (1) 4664749882890240) (.pow (.var 3) 1)) (.constant (31) 3109833255260160)) (.pow (.var 3) 1)) (.constant (1) 10162853775360)) (.pow (.var 3) 1)) (.constant (1) 4265889239040)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 8396549789202432) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 932949976578048) (.pow (.var 4) 1)) (.constant (-625) 2798849929734144))) (.pow (.var 3) 1)) (.add (.mul (.constant (155) 621966651052032) (.pow (.var 4) 1)) (.constant (7625) 621966651052032))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 2032570755072) (.pow (.var 4) 1)) (.constant (125) 4065141510144))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 853177847808) (.pow (.var 4) 1)) (.constant (-4375) 3839300315136)))))
compact_certificate_declaration noncomputable def n_c0_3 : Poly := rational_polynomial% "-4375/3839300315136:;2875/69107405672448:0;1/4265889239040:2;125/4065141510144:3;5/853177847808:4;-2375/3148706170950912:0,0;-1/79739314237440:0,2;-875/2798849929734144:0,3;-5/15947862847488:0,4;1/10162853775360:2,3;7625/621966651052032:3,3;5/2032570755072:3,4;-875/453413688616931328:0,0,0;-1/5247843618251520:0,0,2;-625/8396549789202432:0,0,3;-5/1049568723650304:0,0,4;-41/27988499297341440:0,2,3;-125/968832667984896:0,3,3;-205/5597699859468288:0,3,4;31/3109833255260160:2,3,3;-625/2798849929734144:3,3,3;155/621966651052032:3,3,4;875/13772440791739289088:0,0,0,0;125/185487418070562816:0,0,0,3;-1/125948246838036480:0,0,2,3;-125/340060266462698496:0,0,3,3;-5/25189649367607296:0,0,3,4;-1/20991374473006080:0,2,3,3;-125/37784474051410944:0,3,3,3;-5/4198274894601216:0,3,3,4;1/4664749882890240:2,3,3,3;-125/8396549789202432:3,3,3,3;5/932949976578048:3,3,3,4;875/330538579001742938112:0,0,0,0,3;625/18363254388985718784:0,0,0,3,3;125/1360241065850793984:0,0,3,3,3"
compact_certificate_declaration theorem normalized_c0_3 : r_c0_3.coefficients=n_c0_3 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_3_value (y z w a b u : ℂ) :
    r_c0_3.value (vars y z w a b u)=c0_3 y z w a b := by
  dsimp only [r_c0_3, Expr.value, c0_3, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_3_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_3=c0_3 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_3.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_3).trans (r_c0_3_value y z w a b u))
compact_certificate_declaration noncomputable def r_c0_4 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 661077158003485876224) (.pow (.var 3) 1)) (.constant (-125) 27544881583478578176)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 36726508777971437568) (.pow (.var 3) 1)) (.constant (-2875) 48968678370628583424)) (.pow (.var 3) 1)) (.constant (7625) 16322892790209527808))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 8161446395104763904) (.pow (.var 3) 1)) (.constant (-125) 2720482131701587968)) (.pow (.var 3) 1)) (.constant (23125) 1813654754467725312)) (.pow (.var 3) 1)) (.constant (125) 787176542737728))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-1) 11195399718936576) (.pow (.var 3) 1)) (.constant (-1) 1036611085086720)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (625) 604551584822575104) (.pow (.var 3) 1)) (.constant (6625) 201517194940858368)) (.pow (.var 3) 1)) (.add (.mul (.constant (-25) 11195399718936576) (.pow (.var 4) 1)) (.constant (-125) 430592296882176))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 207322217017344) (.pow (.var 4) 1)) (.constant (-21625) 2487866604208128))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 1243933302104064) (.pow (.var 3) 1)) (.constant (-1) 62824914247680)) (.pow (.var 3) 1)) (.constant (-1) 12797667717120)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 1722369187528704) (.pow (.var 3) 1)) (.add (.mul (.constant (-25) 1243933302104064) (.pow (.var 4) 1)) (.constant (-3875) 2487866604208128))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 12564982849536) (.pow (.var 4) 1)) (.constant (-125) 3839300315136))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 2559533543424) (.pow (.var 4) 1)) (.constant (3875) 15357201260544)))))
compact_certificate_declaration noncomputable def n_c0_4 : Poly := rational_polynomial% "3875/15357201260544:;-21625/2487866604208128:0;-1/12797667717120:2;-125/3839300315136:3;-5/2559533543424:4;125/787176542737728:0,0;-1/1036611085086720:0,2;-125/430592296882176:0,3;-5/207322217017344:0,4;-1/62824914247680:2,3;-3875/2487866604208128:3,3;-5/12564982849536:3,4;7625/16322892790209527808:0,0,0;23125/1813654754467725312:0,0,3;-1/11195399718936576:0,2,3;6625/201517194940858368:0,3,3;-25/11195399718936576:0,3,4;-1/1243933302104064:2,3,3;125/1722369187528704:3,3,3;-25/1243933302104064:3,3,4;-125/27544881583478578176:0,0,0,0;-2875/48968678370628583424:0,0,0,3;-125/2720482131701587968:0,0,3,3;625/604551584822575104:0,3,3,3;-125/661077158003485876224:0,0,0,0,3;-125/36726508777971437568:0,0,0,3,3;-125/8161446395104763904:0,0,3,3,3"
compact_certificate_declaration theorem normalized_c0_4 : r_c0_4.coefficients=n_c0_4 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_4_value (y z w a b u : ℂ) :
    r_c0_4.value (vars y z w a b u)=c0_4 y z w a b := by
  dsimp only [r_c0_4, Expr.value, c0_4, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_4_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_4=c0_4 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_4.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_4).trans (r_c0_4_value y z w a b u))
compact_certificate_declaration noncomputable def r_c0_5 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 97937356741257166848) (.pow (.var 3) 1)) (.constant (-125) 2720482131701587968)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 5440964263403175936) (.pow (.var 3) 1)) (.constant (-12875) 7254619017870901248)) (.pow (.var 3) 1)) (.constant (-875) 33586199156809728))) (.pow (.var 0) 1)) (.add (.mul (.constant (1) 12439333021040640) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 1209103169645150208) (.pow (.var 3) 1)) (.constant (-5375) 806068779763433472)) (.pow (.var 3) 1)) (.constant (125) 8142108886499328)) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 2487866604208128) (.pow (.var 4) 1)) (.constant (20375) 9951466416832512))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (1) 1382148113448960) (.pow (.var 3) 1)) (.constant (1) 153572012605440)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.constant (125) 829288868069376) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 276429622689792) (.pow (.var 4) 1)) (.constant (125) 85055268519936))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 30714402521088) (.pow (.var 4) 1)) (.constant (-125) 7226918240256)))))
compact_certificate_declaration noncomputable def n_c0_5 : Poly := rational_polynomial% "-125/7226918240256:;20375/9951466416832512:0;1/153572012605440:2;125/85055268519936:3;5/30714402521088:4;-875/33586199156809728:0,0;1/12439333021040640:0,2;125/8142108886499328:0,3;5/2487866604208128:0,4;1/1382148113448960:2,3;125/829288868069376:3,3;5/276429622689792:3,4;-125/2720482131701587968:0,0,0;-12875/7254619017870901248:0,0,3;-5375/806068779763433472:0,3,3;-125/97937356741257166848:0,0,0,3;-125/5440964263403175936:0,0,3,3;-125/1209103169645150208:0,3,3,3"
compact_certificate_declaration theorem normalized_c0_5 : r_c0_5.coefficients=n_c0_5 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_5_value (y z w a b u : ℂ) :
    r_c0_5.value (vars y z w a b u)=c0_5 y z w a b := by
  dsimp only [r_c0_5, Expr.value, c0_5, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_5_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_5=c0_5 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_5.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_5).trans (r_c0_5_value y z w a b u))
compact_certificate_declaration noncomputable def r_c0_6 : Expr := (.add (.mul (.add (.mul (.add (.mul (.constant (125) 65291571160838111232) (.pow (.var 0) 1)) (.add (.mul (.constant (125) 1116095233518600192) (.pow (.var 3) 1)) (.constant (125) 67172398313619456))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 146557959956987904) (.pow (.var 3) 1)) (.constant (125) 119417597001990144)) (.pow (.var 3) 1)) (.constant (-14125) 39805865667330048))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-625) 13268621889110016) (.pow (.var 3) 1)) (.constant (-875) 2211436981518336)) (.pow (.var 3) 1)) (.constant (3625) 491430440337408)))
compact_certificate_declaration noncomputable def n_c0_6 : Poly := rational_polynomial% "3625/491430440337408:;-14125/39805865667330048:0;-875/2211436981518336:3;125/67172398313619456:0,0;125/119417597001990144:0,3;-625/13268621889110016:3,3;125/65291571160838111232:0,0,0;125/1116095233518600192:0,0,3;125/146557959956987904:0,3,3"
compact_certificate_declaration theorem normalized_c0_6 : r_c0_6.coefficients=n_c0_6 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_6_value (y z w a b u : ℂ) :
    r_c0_6.value (vars y z w a b u)=c0_6 y z w a b := by
  dsimp only [r_c0_6, Expr.value, c0_6, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_6_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_6=c0_6 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_6.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_6).trans (r_c0_6_value y z w a b u))
compact_certificate_declaration noncomputable def r_c0_7 : Expr := (.add (.mul (.add (.mul (.constant (125) 238835194003980288) (.pow (.var 3) 1)) (.constant (125) 6634310944555008)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 26537243778220032) (.pow (.var 3) 1)) (.constant (625) 8845747926073344)) (.pow (.var 3) 1)) (.constant (-125) 122857610084352)))
compact_certificate_declaration noncomputable def n_c0_7 : Poly := rational_polynomial% "-125/122857610084352:;125/6634310944555008:0;625/8845747926073344:3;125/238835194003980288:0,3;125/26537243778220032:3,3"
compact_certificate_declaration theorem normalized_c0_7 : r_c0_7.coefficients=n_c0_7 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_7_value (y z w a b u : ℂ) :
    r_c0_7.value (vars y z w a b u)=c0_7 y z w a b := by
  dsimp only [r_c0_7, Expr.value, c0_7, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_7_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_7=c0_7 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_7.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_7).trans (r_c0_7_value y z w a b u))
compact_certificate_declaration noncomputable def r_c0_8 : Expr := (.add (.mul (.constant (-125) 159223462669320192) (.pow (.var 0) 1)) (.add (.mul (.constant (-125) 17691495852146688) (.pow (.var 3) 1)) (.constant (125) 1965721761349632)))
compact_certificate_declaration noncomputable def n_c0_8 : Poly := rational_polynomial% "125/1965721761349632:;-125/159223462669320192:0;-125/17691495852146688:3"
compact_certificate_declaration theorem normalized_c0_8 : r_c0_8.coefficients=n_c0_8 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c0_8_value (y z w a b u : ℂ) :
    r_c0_8.value (vars y z w a b u)=c0_8 y z w a b := by
  dsimp only [r_c0_8, Expr.value, c0_8, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c0_8_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c0_8=c0_8 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c0_8.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c0_8).trans (r_c0_8_value y z w a b u))
compact_certificate_declaration noncomputable def r_c1_0 : Expr := (.natural 0)
compact_certificate_declaration noncomputable def n_c1_0 : Poly := rational_polynomial% "0/1:"
compact_certificate_declaration theorem normalized_c1_0 : r_c1_0.coefficients=n_c1_0 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c1_0_value (y z w a b u : ℂ) :
    r_c1_0.value (vars y z w a b u)=c1_0 y z w a b := by
  dsimp only [r_c1_0, Expr.value, c1_0, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c1_0_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c1_0=c1_0 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c1_0.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c1_0).trans (r_c1_0_value y z w a b u))
compact_certificate_declaration noncomputable def r_c1_1 : Expr := (.mul (.add (.mul (.constant (5) 4563) (.pow (.var 3) 1)) (.constant (-5) 507)) (.pow (.var 0) 1))
compact_certificate_declaration noncomputable def n_c1_1 : Poly := rational_polynomial% "-5/507:0;5/4563:0,3"
compact_certificate_declaration theorem normalized_c1_1 : r_c1_1.coefficients=n_c1_1 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c1_1_value (y z w a b u : ℂ) :
    r_c1_1.value (vars y z w a b u)=c1_1 y z w a b := by
  dsimp only [r_c1_1, Expr.value, c1_1, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c1_1_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c1_1=c1_1 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c1_1.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c1_1).trans (r_c1_1_value y z w a b u))
compact_certificate_declaration noncomputable def r_c1_2 : Expr := (.mul (.constant (-5) 2028) (.pow (.var 0) 1))
compact_certificate_declaration noncomputable def n_c1_2 : Poly := rational_polynomial% "-5/2028:0"
compact_certificate_declaration theorem normalized_c1_2 : r_c1_2.coefficients=n_c1_2 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c1_2_value (y z w a b u : ℂ) :
    r_c1_2.value (vars y z w a b u)=c1_2 y z w a b := by
  dsimp only [r_c1_2, Expr.value, c1_2, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c1_2_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c1_2=c1_2 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c1_2.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c1_2).trans (r_c1_2_value y z w a b u))
compact_certificate_declaration noncomputable def r_c1_3 : Expr := (.add (.mul (.constant (-5) 16224) (.pow (.var 0) 1)) (.add (.mul (.constant (15) 5408) (.pow (.var 3) 1)) (.constant (-405) 5408)))
compact_certificate_declaration noncomputable def n_c1_3 : Poly := rational_polynomial% "-405/5408:;-5/16224:0;15/5408:3"
compact_certificate_declaration theorem normalized_c1_3 : r_c1_3.coefficients=n_c1_3 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c1_3_value (y z w a b u : ℂ) :
    r_c1_3.value (vars y z w a b u)=c1_3 y z w a b := by
  dsimp only [r_c1_3, Expr.value, c1_3, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c1_3_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c1_3=c1_3 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c1_3.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c1_3).trans (r_c1_3_value y z w a b u))
compact_certificate_declaration noncomputable def r_c1_4 : Expr := (.constant (-135) 10816)
compact_certificate_declaration noncomputable def n_c1_4 : Poly := rational_polynomial% "-135/10816:"
compact_certificate_declaration theorem normalized_c1_4 : r_c1_4.coefficients=n_c1_4 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c1_4_value (y z w a b u : ℂ) :
    r_c1_4.value (vars y z w a b u)=c1_4 y z w a b := by
  dsimp only [r_c1_4, Expr.value, c1_4, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c1_4_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c1_4=c1_4 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c1_4.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c1_4).trans (r_c1_4_value y z w a b u))
compact_certificate_declaration noncomputable def r_c1_5 : Expr := (.constant (-135) 43264)
compact_certificate_declaration noncomputable def n_c1_5 : Poly := rational_polynomial% "-135/43264:"
compact_certificate_declaration theorem normalized_c1_5 : r_c1_5.coefficients=n_c1_5 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c1_5_value (y z w a b u : ℂ) :
    r_c1_5.value (vars y z w a b u)=c1_5 y z w a b := by
  dsimp only [r_c1_5, Expr.value, c1_5, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c1_5_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c1_5=c1_5 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c1_5.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c1_5).trans (r_c1_5_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_0 : Expr := (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 63761299961755968) (.pow (.var 3) 1)) (.constant (-125) 2656720831739832)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 7084588884639552) (.pow (.var 3) 1)) (.constant (125) 590382407053296)) (.pow (.var 3) 1)) (.constant (125) 9718228922688))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (1) 437320301520960) (.pow (.var 3) 1)) (.constant (1) 29154686768064)) (.pow (.var 3) 1)) (.constant (-1) 2024631025560)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 787176542737728) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 87464060304192) (.pow (.var 4) 1)) (.constant (875) 262392180912576))) (.pow (.var 3) 1)) (.add (.mul (.constant (25) 29154686768064) (.pow (.var 4) 1)) (.constant (125) 1325213034912))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 404926205112) (.pow (.var 4) 1)) (.constant (-125) 98163928512))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (1) 48591144613440) (.pow (.var 3) 1)) (.constant (1) 8098524102240)) (.pow (.var 3) 1)) (.constant (-1) 224959002840)) (.pow (.var 3) 1)) (.constant (1) 66654519360)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 87464060304192) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 9718228922688) (.pow (.var 4) 1)) (.constant (125) 29154686768064))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 1619704820448) (.pow (.var 4) 1)) (.constant (125) 809852410224))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 44991800568) (.pow (.var 4) 1)) (.constant (-875) 119978134848))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 13330903872) (.pow (.var 4) 1)) (.constant (125) 4443634624))))) (.pow (.var 0) 1))
compact_certificate_declaration noncomputable def n_c6_0 : Poly := rational_polynomial% "125/4443634624:0;-125/98163928512:0,0;1/66654519360:0,2;-875/119978134848:0,3;5/13330903872:0,4;125/9718228922688:0,0,0;-1/2024631025560:0,0,2;125/1325213034912:0,0,3;-5/404926205112:0,0,4;-1/224959002840:0,2,3;125/809852410224:0,3,3;-5/44991800568:0,3,4;-125/2656720831739832:0,0,0,0;125/590382407053296:0,0,0,3;1/29154686768064:0,0,2,3;875/262392180912576:0,0,3,3;25/29154686768064:0,0,3,4;1/8098524102240:0,2,3,3;125/29154686768064:0,3,3,3;5/1619704820448:0,3,3,4;-125/63761299961755968:0,0,0,0,3;-125/7084588884639552:0,0,0,3,3;1/437320301520960:0,0,2,3,3;-125/787176542737728:0,0,3,3,3;5/87464060304192:0,0,3,3,4;1/48591144613440:0,2,3,3,3;-125/87464060304192:0,3,3,3,3;5/9718228922688:0,3,3,3,4"
compact_certificate_declaration theorem normalized_c6_0 : r_c6_0.coefficients=n_c6_0 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_0_value (y z w a b u : ℂ) :
    r_c6_0.value (vars y z w a b u)=c6_0 y z w a b := by
  dsimp only [r_c6_0, Expr.value, c6_0, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_0_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_0=c6_0 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_0.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_0).trans (r_c6_0_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_1 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (625) 255045199847023872) (.pow (.var 3) 1)) (.constant (625) 10626883326959328)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 14169177769279104) (.pow (.var 3) 1)) (.constant (-125) 429369023311488)) (.pow (.var 3) 1)) (.constant (-625) 61739336685312))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 583093735361280) (.pow (.var 3) 1)) (.constant (-1) 32394096408960)) (.pow (.var 3) 1)) (.constant (1) 4049262051120)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 1049568723650304) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 116618747072256) (.pow (.var 4) 1)) (.constant (125) 174928120608384))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 6478819281792) (.pow (.var 4) 1)) (.constant (-625) 38872915690752))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 809852410224) (.pow (.var 4) 1)) (.constant (125) 202463102556))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 729946972415232) (.pow (.var 3) 1)) (.constant (-625) 243315657471744)) (.pow (.var 3) 1)) (.constant (125) 3379384131552)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 64788192817920) (.pow (.var 3) 1)) (.constant (-1) 899836011360)) (.pow (.var 3) 1)) (.constant (1) 199963558080)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-625) 116618747072256) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 12957638563584) (.pow (.var 4) 1)) (.constant (-125) 1439737618176))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 179967202272) (.pow (.var 4) 1)) (.constant (-125) 89983601136))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 39992711616) (.pow (.var 4) 1)) (.constant (125) 26661807744)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 81105219157248) (.pow (.var 3) 1)) (.constant (-125) 13517536526208)) (.pow (.var 3) 1)) (.constant (125) 375487125728)) (.pow (.var 3) 1)) (.constant (-3375) 3003897005824)) (.pow (.var 1) 1)) (.mul (.add (.mul (.add (.mul (.constant (-125) 2159606427264) (.pow (.var 3) 1)) (.constant (-625) 719868809088)) (.pow (.var 3) 1)) (.constant (125) 26661807744)) (.pow (.var 3) 2))))
compact_certificate_declaration noncomputable def n_c6_1 : Poly := rational_polynomial% "125/26661807744:0;-3375/3003897005824:1;125/202463102556:0,0;125/3379384131552:0,1;1/199963558080:0,2;-125/89983601136:0,3;5/39992711616:0,4;125/375487125728:1,3;125/26661807744:3,3;-625/61739336685312:0,0,0;1/4049262051120:0,0,2;-625/38872915690752:0,0,3;5/809852410224:0,0,4;-625/243315657471744:0,1,3;-1/899836011360:0,2,3;-125/1439737618176:0,3,3;-5/179967202272:0,3,4;-125/13517536526208:1,3,3;-625/719868809088:3,3,3;625/10626883326959328:0,0,0,0;-125/429369023311488:0,0,0,3;-1/32394096408960:0,0,2,3;125/174928120608384:0,0,3,3;-5/6478819281792:0,0,3,4;-125/729946972415232:0,1,3,3;-1/64788192817920:0,2,3,3;-625/116618747072256:0,3,3,3;-5/12957638563584:0,3,3,4;-125/81105219157248:1,3,3,3;-125/2159606427264:3,3,3,3;625/255045199847023872:0,0,0,0,3;125/14169177769279104:0,0,0,3,3;-1/583093735361280:0,0,2,3,3;125/1049568723650304:0,0,3,3,3;-5/116618747072256:0,0,3,3,4"
compact_certificate_declaration theorem normalized_c6_1 : r_c6_1.coefficients=n_c6_1 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_1_value (y z w a b u : ℂ) :
    r_c6_1.value (vars y z w a b u)=c6_1 y z w a b := by
  dsimp only [r_c6_1, Expr.value, c6_1, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_1_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_1=c6_1 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_1.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_1).trans (r_c6_1_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_2 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 113353422154232832) (.pow (.var 3) 1)) (.constant (-125) 4723059256426368)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 56676711077116416) (.pow (.var 3) 1)) (.constant (5375) 75568948102821888)) (.pow (.var 3) 1)) (.constant (3625) 1574353085475456))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 52556182013896704) (.pow (.var 3) 1)) (.constant (125) 2189840917245696)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (1) 3498562412167680) (.pow (.var 3) 1)) (.constant (7) 932949976578048)) (.pow (.var 3) 1)) (.constant (1) 64788192817920)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 4198274894601216) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 699712482433536) (.pow (.var 4) 1)) (.constant (-125) 310983325526016))) (.pow (.var 3) 1)) (.add (.mul (.constant (175) 932949976578048) (.pow (.var 4) 1)) (.constant (125) 310983325526016))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 12957638563584) (.pow (.var 4) 1)) (.constant (-875) 9423737137152)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 973262629886976) (.pow (.var 3) 1)) (.constant (625) 324420876628992)) (.pow (.var 3) 1)) (.constant (-5375) 216280584419328)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 51830554254336) (.pow (.var 3) 1)) (.constant (-5) 17276851418112)) (.pow (.var 3) 1)) (.constant (-7) 19196501575680)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (625) 84813634234368) (.pow (.var 3) 1)) (.add (.mul (.constant (-25) 51830554254336) (.pow (.var 4) 1)) (.constant (20375) 155491662763008))) (.pow (.var 3) 1)) (.add (.mul (.constant (-125) 17276851418112) (.pow (.var 4) 1)) (.constant (-13625) 34553702836224))) (.pow (.var 3) 1)) (.add (.mul (.constant (-35) 3839300315136) (.pow (.var 4) 1)) (.constant (125) 58171216896)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 648841753257984) (.pow (.var 3) 1)) (.constant (-125) 36046764069888)) (.pow (.var 3) 1)) (.constant (875) 12015588023296)) (.pow (.var 3) 1)) (.constant (-5625) 24031176046592)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (1) 19196501575680) (.pow (.var 3) 1)) (.constant (-1) 1599708464640)) (.pow (.var 3) 1)) (.constant (-9) 355490769920)) (.pow (.var 3) 1)) (.constant (81) 710981539840)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 34553702836224) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 3839300315136) (.pow (.var 4) 1)) (.constant (-2375) 11517900945408))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 319941692928) (.pow (.var 4) 1)) (.constant (-125) 106647230976))) (.pow (.var 3) 1)) (.add (.mul (.constant (-45) 71098153984) (.pow (.var 4) 1)) (.constant (-1125) 142196307968))) (.pow (.var 3) 1)) (.add (.mul (.constant (405) 142196307968) (.pow (.var 4) 1)) (.constant (10125) 142196307968))))))
compact_certificate_declaration noncomputable def n_c6_2 : Poly := rational_polynomial% "10125/142196307968:;125/58171216896:0;-5625/24031176046592:1;81/710981539840:2;-1125/142196307968:3;405/142196307968:4;-875/9423737137152:0,0;-5375/216280584419328:0,1;-7/19196501575680:0,2;-13625/34553702836224:0,3;-35/3839300315136:0,4;875/12015588023296:1,3;-9/355490769920:2,3;-125/106647230976:3,3;-45/71098153984:3,4;3625/1574353085475456:0,0,0;125/2189840917245696:0,0,1;1/64788192817920:0,0,2;125/310983325526016:0,0,3;5/12957638563584:0,0,4;625/324420876628992:0,1,3;-5/17276851418112:0,2,3;20375/155491662763008:0,3,3;-125/17276851418112:0,3,4;-125/36046764069888:1,3,3;-1/1599708464640:2,3,3;-2375/11517900945408:3,3,3;-5/319941692928:3,3,4;-125/4723059256426368:0,0,0,0;5375/75568948102821888:0,0,0,3;125/52556182013896704:0,0,1,3;7/932949976578048:0,0,2,3;-125/310983325526016:0,0,3,3;175/932949976578048:0,0,3,4;125/973262629886976:0,1,3,3;-1/51830554254336:0,2,3,3;625/84813634234368:0,3,3,3;-25/51830554254336:0,3,3,4;-125/648841753257984:1,3,3,3;1/19196501575680:2,3,3,3;-125/34553702836224:3,3,3,3;5/3839300315136:3,3,3,4;-125/113353422154232832:0,0,0,0,3;-125/56676711077116416:0,0,0,3,3;1/3498562412167680:0,0,2,3,3;-125/4198274894601216:0,0,3,3,3;5/699712482433536:0,0,3,3,4"
compact_certificate_declaration theorem normalized_c6_2 : r_c6_2.coefficients=n_c6_2 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_2_value (y z w a b u : ℂ) :
    r_c6_2.value (vars y z w a b u)=c6_2 y z w a b := by
  dsimp only [r_c6_2, Expr.value, c6_2, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_2_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_2=c6_2 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_2.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_2).trans (r_c6_2_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_3 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (875) 4080723197552381952) (.pow (.var 3) 1)) (.constant (875) 170030133231349248)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 151137896205643776) (.pow (.var 3) 1)) (.constant (125) 11625992015818752)) (.pow (.var 3) 1)) (.constant (-125) 1291776890646528))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 52556182013896704) (.pow (.var 3) 1)) (.constant (-125) 2189840917245696)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (-1) 6219666510520320) (.pow (.var 3) 1)) (.constant (-1) 259152771271680)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.constant (-3125) 33586199156809728) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 1243933302104064) (.pow (.var 4) 1)) (.constant (-9125) 3731799906312192))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 51830554254336) (.pow (.var 4) 1)) (.constant (-7375) 621966651052032)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 7786101039095808) (.pow (.var 3) 1)) (.constant (-125) 598930849161216)) (.pow (.var 3) 1)) (.constant (125) 48062352093184)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 414644434034688) (.pow (.var 3) 1)) (.constant (7) 138214811344896)) (.pow (.var 3) 1)) (.constant (7) 2843926159360)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-875) 932949976578048) (.pow (.var 3) 1)) (.add (.mul (.constant (-25) 414644434034688) (.pow (.var 4) 1)) (.constant (-625) 36586273591296))) (.pow (.var 3) 1)) (.add (.mul (.constant (175) 138214811344896) (.pow (.var 4) 1)) (.constant (9125) 69107405672448))) (.pow (.var 3) 1)) (.add (.mul (.constant (35) 568785231872) (.pow (.var 4) 1)) (.constant (4375) 3839300315136)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 2595367013031936) (.pow (.var 3) 1)) (.constant (125) 144187056279552)) (.pow (.var 3) 1)) (.constant (6625) 288374112559104)) (.pow (.var 3) 1)) (.constant (-11625) 48062352093184)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 6398833858560) (.pow (.var 3) 1)) (.constant (-1) 167289774080)) (.pow (.var 3) 1)) (.constant (81) 2843926159360)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 138214811344896) (.pow (.var 3) 1)) (.constant (125) 46071603781632)) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 1279766771712) (.pow (.var 4) 1)) (.constant (3875) 15357201260544))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 33457954816) (.pow (.var 4) 1)) (.constant (375) 568785231872))) (.pow (.var 3) 1)) (.add (.mul (.constant (405) 568785231872) (.pow (.var 4) 1)) (.constant (3375) 284392615936))))))
compact_certificate_declaration noncomputable def n_c6_3 : Poly := rational_polynomial% "3375/284392615936:;4375/3839300315136:0;-11625/48062352093184:1;81/2843926159360:2;375/568785231872:3;405/568785231872:4;-7375/621966651052032:0,0;125/48062352093184:0,1;7/2843926159360:0,2;9125/69107405672448:0,3;35/568785231872:0,4;6625/288374112559104:1,3;-1/167289774080:2,3;3875/15357201260544:3,3;-5/33457954816:3,4;-125/1291776890646528:0,0,0;-125/2189840917245696:0,0,1;-1/259152771271680:0,0,2;-9125/3731799906312192:0,0,3;-5/51830554254336:0,0,4;-125/598930849161216:0,1,3;7/138214811344896:0,2,3;-625/36586273591296:0,3,3;175/138214811344896:0,3,4;125/144187056279552:1,3,3;-1/6398833858560:2,3,3;125/46071603781632:3,3,3;-5/1279766771712:3,3,4;875/170030133231349248:0,0,0,0;125/11625992015818752:0,0,0,3;-125/52556182013896704:0,0,1,3;-1/6219666510520320:0,0,2,3;-3125/33586199156809728:0,0,3,3;-5/1243933302104064:0,0,3,4;-125/7786101039095808:0,1,3,3;-1/414644434034688:0,2,3,3;-875/932949976578048:0,3,3,3;-25/414644434034688:0,3,3,4;-125/2595367013031936:1,3,3,3;-125/138214811344896:3,3,3,3;875/4080723197552381952:0,0,0,0,3;125/151137896205643776:0,0,0,3,3"
compact_certificate_declaration theorem normalized_c6_3 : r_c6_3.coefficients=n_c6_3 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_3_value (y z w a b u : ℂ) :
    r_c6_3.value (vars y z w a b u)=c6_3 y z w a b := by
  dsimp only [r_c6_3, Expr.value, c6_3, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_3_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_3=c6_3 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_3.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_3).trans (r_c6_3_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_4 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 8161446395104763904) (.pow (.var 3) 1)) (.constant (-125) 340060266462698496)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 906827377233862656) (.pow (.var 3) 1)) (.constant (-3125) 604551584822575104)) (.pow (.var 3) 1)) (.constant (-10375) 201517194940858368))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (625) 840898912222347264) (.pow (.var 3) 1)) (.constant (625) 35037454675931136)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (-1) 12439333021040640) (.pow (.var 3) 1)) (.constant (-1) 518305542543360)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.constant (6125) 134344796627238912) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 2487866604208128) (.pow (.var 4) 1)) (.constant (25625) 22390799437873152))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 103661108508672) (.pow (.var 4) 1)) (.constant (125) 292690188730368)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 93433212469149696) (.pow (.var 3) 1)) (.constant (-125) 15572202078191616)) (.pow (.var 3) 1)) (.constant (-2875) 5190734026063872)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (1) 1382148113448960) (.pow (.var 3) 1)) (.constant (5) 552859245379584)) (.pow (.var 3) 1)) (.constant (-47) 307144025210880)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 2487866604208128) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 276429622689792) (.pow (.var 4) 1)) (.constant (125) 155491662763008))) (.pow (.var 3) 1)) (.add (.mul (.constant (125) 552859245379584) (.pow (.var 4) 1)) (.constant (-875) 92143207563264))) (.pow (.var 3) 1)) (.add (.mul (.constant (-235) 61428805042176) (.pow (.var 4) 1)) (.constant (-125) 451682390016)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 3460489350709248) (.pow (.var 3) 1)) (.constant (-125) 1153496450236416)) (.pow (.var 3) 1)) (.constant (375) 96124704186368)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-1) 9307394703360) (.pow (.var 3) 1)) (.constant (-1) 1551232450560)) (.pow (.var 3) 1)) (.constant (27) 1034154967040)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 552859245379584) (.pow (.var 3) 1)) (.constant (-125) 30714402521088)) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 1861478940672) (.pow (.var 4) 1)) (.constant (-125) 787548782592))) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 310246490112) (.pow (.var 4) 1)) (.constant (125) 65629065216))) (.pow (.var 3) 1)) (.add (.mul (.constant (135) 206830993408) (.pow (.var 4) 1)) (.constant (32625) 2275140927488))))))
compact_certificate_declaration noncomputable def n_c6_4 : Poly := rational_polynomial% "32625/2275140927488:;-125/451682390016:0;375/96124704186368:1;27/1034154967040:2;125/65629065216:3;135/206830993408:4;125/292690188730368:0,0;-2875/5190734026063872:0,1;-47/307144025210880:0,2;-875/92143207563264:0,3;-235/61428805042176:0,4;-125/1153496450236416:1,3;-1/1551232450560:2,3;-125/787548782592:3,3;-5/310246490112:3,4;-10375/201517194940858368:0,0,0;625/35037454675931136:0,0,1;-1/518305542543360:0,0,2;25625/22390799437873152:0,0,3;-5/103661108508672:0,0,4;-125/15572202078191616:0,1,3;5/552859245379584:0,2,3;125/155491662763008:0,3,3;125/552859245379584:0,3,4;-125/3460489350709248:1,3,3;-1/9307394703360:2,3,3;-125/30714402521088:3,3,3;-5/1861478940672:3,3,4;-125/340060266462698496:0,0,0,0;-3125/604551584822575104:0,0,0,3;625/840898912222347264:0,0,1,3;-1/12439333021040640:0,0,2,3;6125/134344796627238912:0,0,3,3;-5/2487866604208128:0,0,3,4;125/93433212469149696:0,1,3,3;1/1382148113448960:0,2,3,3;125/2487866604208128:0,3,3,3;5/276429622689792:0,3,3,4;125/552859245379584:3,3,3,3;-125/8161446395104763904:0,0,0,0,3;-125/906827377233862656:0,0,0,3,3"
compact_certificate_declaration theorem normalized_c6_4 : r_c6_4.coefficients=n_c6_4 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_4_value (y z w a b u : ℂ) :
    r_c6_4.value (vars y z w a b u)=c6_4 y z w a b := by
  dsimp only [r_c6_4, Expr.value, c6_4, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_4_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_4=c6_4 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_4.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_4).trans (r_c6_4_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_5 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (2875) 4836412678580600832) (.pow (.var 3) 1)) (.constant (875) 67172398313619456)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 1681797824444694528) (.pow (.var 3) 1)) (.constant (-125) 70074909351862272)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (-125) 33586199156809728) (.pow (.var 3) 1)) (.constant (-4375) 44781598875746304)) (.pow (.var 3) 1)) (.constant (625) 2487866604208128)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 186866424938299392) (.pow (.var 3) 1)) (.constant (-125) 41525872208510976)) (.pow (.var 3) 1)) (.constant (11125) 41525872208510976)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (1) 921432075632640) (.pow (.var 3) 1)) (.constant (1) 30714402521088)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-625) 19902932833665024) (.pow (.var 3) 1)) (.constant (-125) 195126792486912)) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 184286415126528) (.pow (.var 4) 1)) (.constant (4625) 2211436981518336))) (.pow (.var 3) 1)) (.add (.mul (.constant (25) 30714402521088) (.pow (.var 4) 1)) (.constant (12875) 245715220168704)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 4613985800945664) (.pow (.var 3) 1)) (.constant (125) 576748225118208)) (.pow (.var 3) 1)) (.constant (-375) 90470309822464)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (1) 204762683473920) (.pow (.var 3) 1)) (.constant (1) 8531778478080)) (.pow (.var 3) 1)) (.constant (3) 5687852318720)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 368572830253056) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 40952536694784) (.pow (.var 4) 1)) (.constant (125) 4725292695552))) (.pow (.var 3) 1)) (.add (.mul (.constant (5) 1706355695616) (.pow (.var 4) 1)) (.constant (11125) 27301691129856))) (.pow (.var 3) 1)) (.add (.mul (.constant (15) 1137570463744) (.pow (.var 4) 1)) (.constant (-10875) 9100563709952))))))
compact_certificate_declaration noncomputable def n_c6_5 : Poly := rational_polynomial% "-10875/9100563709952:;12875/245715220168704:0;-375/90470309822464:1;3/5687852318720:2;11125/27301691129856:3;15/1137570463744:4;625/2487866604208128:0,0;11125/41525872208510976:0,1;1/30714402521088:0,2;4625/2211436981518336:0,3;25/30714402521088:0,4;125/576748225118208:1,3;1/8531778478080:2,3;125/4725292695552:3,3;5/1706355695616:3,4;875/67172398313619456:0,0,0;-125/70074909351862272:0,0,1;-4375/44781598875746304:0,0,3;-125/41525872208510976:0,1,3;1/921432075632640:0,2,3;-125/195126792486912:0,3,3;5/184286415126528:0,3,4;125/4613985800945664:1,3,3;1/204762683473920:2,3,3;125/368572830253056:3,3,3;5/40952536694784:3,3,4;2875/4836412678580600832:0,0,0,3;-125/1681797824444694528:0,0,1,3;-125/33586199156809728:0,0,3,3;-125/186866424938299392:0,1,3,3;-625/19902932833665024:0,3,3,3"
compact_certificate_declaration theorem normalized_c6_5 : r_c6_5.coefficients=n_c6_5 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_5_value (y z w a b u : ℂ) :
    r_c6_5.value (vars y z w a b u)=c6_5 y z w a b := by
  dsimp only [r_c6_5, Expr.value, c6_5, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_5_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_5=c6_5 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_5.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_5).trans (r_c6_5_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_6 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 3224275119053733888) (.pow (.var 3) 1)) (.constant (-625) 806068779763433472)) (.pow (.var 0) 1)) (.add (.mul (.constant (125) 22390799437873152) (.pow (.var 3) 1)) (.constant (6625) 79611731334660096))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 249155233251065856) (.pow (.var 3) 1)) (.constant (-625) 41525872208510976)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (-1) 1228576100843520) (.pow (.var 3) 1)) (.constant (-23) 1228576100843520)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 39805865667330048) (.pow (.var 3) 1)) (.constant (125) 2948582642024448)) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 245715220168704) (.pow (.var 4) 1)) (.constant (-3875) 2948582642024448))) (.pow (.var 3) 1)) (.add (.mul (.constant (-115) 245715220168704) (.pow (.var 4) 1)) (.constant (-3125) 327620293558272)))))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 27683914805673984) (.pow (.var 3) 1)) (.constant (-125) 3075990533963776)) (.pow (.var 3) 1)) (.constant (1125) 1537995266981888)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (7) 273016911298560) (.pow (.var 3) 1)) (.constant (9) 18201127419904)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-875) 2948582642024448) (.pow (.var 3) 1)) (.constant (-4625) 982860880674816)) (.pow (.var 3) 1)) (.add (.mul (.constant (35) 54603382259712) (.pow (.var 4) 1)) (.constant (125) 9100563709952))) (.pow (.var 3) 1)) (.add (.mul (.constant (225) 18201127419904) (.pow (.var 4) 1)) (.constant (3375) 18201127419904))))))
compact_certificate_declaration noncomputable def n_c6_6 : Poly := rational_polynomial% "3375/18201127419904:;-3125/327620293558272:0;1125/1537995266981888:1;9/18201127419904:2;125/9100563709952:3;225/18201127419904:4;6625/79611731334660096:0,0;-625/41525872208510976:0,1;-23/1228576100843520:0,2;-3875/2948582642024448:0,3;-115/245715220168704:0,4;-125/3075990533963776:1,3;7/273016911298560:2,3;-4625/982860880674816:3,3;35/54603382259712:3,4;-625/806068779763433472:0,0,0;125/22390799437873152:0,0,3;-125/249155233251065856:0,1,3;-1/1228576100843520:0,2,3;125/2948582642024448:0,3,3;-5/245715220168704:0,3,4;-125/27683914805673984:1,3,3;-875/2948582642024448:3,3,3;-125/3224275119053733888:0,0,0,3;125/39805865667330048:0,3,3,3"
compact_certificate_declaration theorem normalized_c6_6 : r_c6_6.coefficients=n_c6_6 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_6_value (y z w a b u : ℂ) :
    r_c6_6.value (vars y z w a b u)=c6_6 y z w a b := by
  dsimp only [r_c6_6, Expr.value, c6_6, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_6_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_6=c6_6 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_6.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_6).trans (r_c6_6_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_7 : Expr := (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 119417597001990144) (.pow (.var 3) 1)) (.constant (-2375) 79611731334660096)) (.pow (.var 0) 1)) (.add (.mul (.constant (125) 166103488834043904) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (-125) 17691495852146688) (.pow (.var 3) 1)) (.constant (-2375) 35382991704293376)) (.pow (.var 3) 1)) (.constant (5125) 3931443522699264)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 18455943203782656) (.pow (.var 3) 1)) (.constant (-375) 6151981067927552)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (-1) 182011274199040) (.pow (.var 3) 1)) (.constant (-9) 91005637099520)) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 5897165284048896) (.pow (.var 3) 1)) (.constant (2875) 3931443522699264)) (.pow (.var 3) 1)) (.add (.mul (.constant (-5) 36402254839808) (.pow (.var 4) 1)) (.constant (-125) 36402254839808))) (.pow (.var 3) 1)) (.add (.mul (.constant (-45) 18201127419904) (.pow (.var 4) 1)) (.constant (-13875) 145609019359232))))))
compact_certificate_declaration noncomputable def n_c6_7 : Poly := rational_polynomial% "-13875/145609019359232:;5125/3931443522699264:0;-375/6151981067927552:1;-9/91005637099520:2;-125/36402254839808:3;-45/18201127419904:4;-2375/79611731334660096:0,0;125/166103488834043904:0,1;-2375/35382991704293376:0,3;125/18455943203782656:1,3;-1/182011274199040:2,3;2875/3931443522699264:3,3;-5/36402254839808:3,4;-125/119417597001990144:0,0,3;-125/17691495852146688:0,3,3;125/5897165284048896:3,3,3"
compact_certificate_declaration theorem normalized_c6_7 : r_c6_7.coefficients=n_c6_7 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_7_value (y z w a b u : ℂ) :
    r_c6_7.value (vars y z w a b u)=c6_7 y z w a b := by
  dsimp only [r_c6_7, Expr.value, c6_7, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_7_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_7=c6_7 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_7.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_7).trans (r_c6_7_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_8 : Expr := (.add (.mul (.add (.mul (.constant (125) 318446925338640384) (.pow (.var 0) 1)) (.add (.mul (.constant (-125) 23588661136195584) (.pow (.var 3) 1)) (.constant (-125) 1965721761349632))) (.pow (.var 0) 1)) (.add (.mul (.constant (3) 364022548398080) (.pow (.var 2) 1)) (.add (.mul (.add (.mul (.constant (-625) 7862887045398528) (.pow (.var 3) 1)) (.constant (-125) 873654116155392)) (.pow (.var 3) 1)) (.add (.mul (.constant (15) 72804509679616) (.pow (.var 4) 1)) (.constant (1875) 145609019359232)))))
compact_certificate_declaration noncomputable def n_c6_8 : Poly := rational_polynomial% "1875/145609019359232:;-125/1965721761349632:0;3/364022548398080:2;-125/873654116155392:3;15/72804509679616:4;125/318446925338640384:0,0;-125/23588661136195584:0,3;-625/7862887045398528:3,3"
compact_certificate_declaration theorem normalized_c6_8 : r_c6_8.coefficients=n_c6_8 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_8_value (y z w a b u : ℂ) :
    r_c6_8.value (vars y z w a b u)=c6_8 y z w a b := by
  dsimp only [r_c6_8, Expr.value, c6_8, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_8_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_8=c6_8 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_8.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_8).trans (r_c6_8_value y z w a b u))
compact_certificate_declaration noncomputable def r_c6_9 : Expr := (.add (.mul (.constant (125) 15725774090797056) (.pow (.var 0) 1)) (.add (.mul (.constant (125) 1747308232310784) (.pow (.var 3) 1)) (.constant (-375) 582436077436928)))
compact_certificate_declaration noncomputable def n_c6_9 : Poly := rational_polynomial% "-375/582436077436928:;125/15725774090797056:0;125/1747308232310784:3"
compact_certificate_declaration theorem normalized_c6_9 : r_c6_9.coefficients=n_c6_9 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c6_9_value (y z w a b u : ℂ) :
    r_c6_9.value (vars y z w a b u)=c6_9 y z w a b := by
  dsimp only [r_c6_9, Expr.value, c6_9, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c6_9_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c6_9=c6_9 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c6_9.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c6_9).trans (r_c6_9_value y z w a b u))
compact_certificate_declaration noncomputable def r_c7_0 : Expr := (.natural 0)
compact_certificate_declaration noncomputable def n_c7_0 : Poly := rational_polynomial% "0/1:"
compact_certificate_declaration theorem normalized_c7_0 : r_c7_0.coefficients=n_c7_0 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c7_0_value (y z w a b u : ℂ) :
    r_c7_0.value (vars y z w a b u)=c7_0 y z w a b := by
  dsimp only [r_c7_0, Expr.value, c7_0, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c7_0_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c7_0=c7_0 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c7_0.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c7_0).trans (r_c7_0_value y z w a b u))
compact_certificate_declaration noncomputable def r_c7_1 : Expr := (.add (.mul (.add (.mul (.constant (5) 369603) (.pow (.var 3) 1)) (.constant (-5) 41067)) (.pow (.var 0) 1)) (.add (.mul (.constant (5) 41067) (.pow (.var 3) 2)) (.constant (-5) 507)))
compact_certificate_declaration noncomputable def n_c7_1 : Poly := rational_polynomial% "-5/507:;-5/41067:0;5/369603:0,3;5/41067:3,3"
compact_certificate_declaration theorem normalized_c7_1 : r_c7_1.coefficients=n_c7_1 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c7_1_value (y z w a b u : ℂ) :
    r_c7_1.value (vars y z w a b u)=c7_1 y z w a b := by
  dsimp only [r_c7_1, Expr.value, c7_1, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c7_1_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c7_1=c7_1 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c7_1.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c7_1).trans (r_c7_1_value y z w a b u))
compact_certificate_declaration noncomputable def r_c7_2 : Expr := (.add (.mul (.constant (-5) 164268) (.pow (.var 0) 1)) (.add (.mul (.constant (-5) 18252) (.pow (.var 3) 1)) (.constant (-5) 2028)))
compact_certificate_declaration noncomputable def n_c7_2 : Poly := rational_polynomial% "-5/2028:;-5/164268:0;-5/18252:3"
compact_certificate_declaration theorem normalized_c7_2 : r_c7_2.coefficients=n_c7_2 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c7_2_value (y z w a b u : ℂ) :
    r_c7_2.value (vars y z w a b u)=c7_2 y z w a b := by
  dsimp only [r_c7_2, Expr.value, c7_2, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c7_2_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c7_2=c7_2 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c7_2.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c7_2).trans (r_c7_2_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_0 : Expr := (.natural 0)
compact_certificate_declaration noncomputable def n_c8_0 : Poly := rational_polynomial% "0/1:"
compact_certificate_declaration theorem normalized_c8_0 : r_c8_0.coefficients=n_c8_0 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_0_value (y z w a b u : ℂ) :
    r_c8_0.value (vars y z w a b u)=c8_0 y z w a b := by
  dsimp only [r_c8_0, Expr.value, c8_0, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_0_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_0=c8_0 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_0.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_0).trans (r_c8_0_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_1 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 255045199847023872) (.pow (.var 3) 1)) (.constant (-125) 10626883326959328)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 9446118512852736) (.pow (.var 3) 1)) (.constant (-125) 393588271368864)) (.pow (.var 3) 1)) (.constant (-625) 1049568723650304))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 59125704765633792) (.pow (.var 3) 1)) (.constant (625) 19708568255211264)) (.pow (.var 3) 1)) (.constant (-125) 273730114655712)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 3148706170950912) (.pow (.var 3) 1)) (.constant (-875) 524784361825152)) (.pow (.var 3) 1)) (.constant (-125) 6859926298368)) (.pow (.var 3) 1)) (.constant (2375) 12957638563584)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 3284761375868544) (.pow (.var 3) 1)) (.constant (625) 1094920458622848)) (.pow (.var 3) 1)) (.constant (-125) 22119605224704)) (.pow (.var 3) 1)) (.constant (-625) 27035073052416)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 116618747072256) (.pow (.var 3) 1)) (.constant (125) 6478819281792)) (.pow (.var 3) 1)) (.constant (125) 3239409640896)) (.pow (.var 3) 1)) (.constant (2375) 1439737618176)) (.pow (.var 3) 1)) (.constant (-125) 26661807744)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 729946972415232) (.pow (.var 3) 1)) (.constant (625) 243315657471744)) (.pow (.var 3) 1)) (.constant (-125) 4505845508736)) (.pow (.var 3) 1)) (.constant (-625) 3003897005824)) (.pow (.var 3) 1)) (.constant (3375) 3003897005824)) (.pow (.var 1) 1)) (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 19436457845376) (.pow (.var 3) 1)) (.constant (125) 809852410224)) (.pow (.var 3) 1)) (.constant (125) 359934404544)) (.pow (.var 3) 1)) (.constant (-125) 26661807744)) (.pow (.var 3) 2))))
compact_certificate_declaration noncomputable def n_c8_1 : Poly := rational_polynomial% "-125/26661807744:0;3375/3003897005824:1;2375/12957638563584:0,0;-625/27035073052416:0,1;2375/1439737618176:0,3;-625/3003897005824:1,3;-125/26661807744:3,3;-625/1049568723650304:0,0,0;-125/273730114655712:0,0,1;-125/6859926298368:0,0,3;-125/22119605224704:0,1,3;125/3239409640896:0,3,3;-125/4505845508736:1,3,3;125/359934404544:3,3,3;-125/10626883326959328:0,0,0,0;-125/393588271368864:0,0,0,3;625/19708568255211264:0,0,1,3;-875/524784361825152:0,0,3,3;625/1094920458622848:0,1,3,3;125/6478819281792:0,3,3,3;625/243315657471744:1,3,3,3;125/809852410224:3,3,3,3;-125/255045199847023872:0,0,0,0,3;-125/9446118512852736:0,0,0,3,3;125/59125704765633792:0,0,1,3,3;-125/3148706170950912:0,0,3,3,3;125/3284761375868544:0,1,3,3,3;125/116618747072256:0,3,3,3,3;125/729946972415232:1,3,3,3,3;125/19436457845376:3,3,3,3,3"
compact_certificate_declaration theorem normalized_c8_1 : r_c8_1.coefficients=n_c8_1 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_1_value (y z w a b u : ℂ) :
    r_c8_1.value (vars y z w a b u)=c8_1 y z w a b := by
  dsimp only [r_c8_1, Expr.value, c8_1, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_1_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_1=c8_1 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_1.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_1).trans (r_c8_1_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_10 : Expr := (.constant (375) 582436077436928)
compact_certificate_declaration noncomputable def n_c8_10 : Poly := rational_polynomial% "375/582436077436928:"
compact_certificate_declaration theorem normalized_c8_10 : r_c8_10.coefficients=n_c8_10 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_10_value (y z w a b u : ℂ) :
    r_c8_10.value (vars y z w a b u)=c8_10 y z w a b := by
  dsimp only [r_c8_10, Expr.value, c8_10, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_10_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_10=c8_10 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_10.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_10).trans (r_c8_10_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_2 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 255045199847023872) (.pow (.var 3) 1)) (.constant (125) 10626883326959328)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 14169177769279104) (.pow (.var 3) 1)) (.constant (875) 3434952186491904)) (.pow (.var 3) 1)) (.constant (2875) 2099137447300608))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 78834273020845056) (.pow (.var 3) 1)) (.constant (-125) 4379681834491392)) (.pow (.var 3) 1)) (.constant (125) 547460229311424)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 4198274894601216) (.pow (.var 3) 1)) (.constant (625) 1049568723650304)) (.pow (.var 3) 1)) (.constant (12875) 466474988289024)) (.pow (.var 3) 1)) (.constant (-125) 809852410224)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 8759363668982784) (.pow (.var 3) 1)) (.constant (-875) 2189840917245696)) (.pow (.var 3) 1)) (.constant (-625) 486631314943488)) (.pow (.var 3) 1)) (.constant (625) 27035073052416)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 174928120608384) (.pow (.var 3) 1)) (.constant (-3875) 233237494144512)) (.pow (.var 3) 1)) (.constant (-125) 1439737618176)) (.pow (.var 3) 1)) (.constant (-2375) 2879475236352)) (.pow (.var 3) 1)) (.constant (-2875) 639883385856)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 973262629886976) (.pow (.var 3) 1)) (.constant (-125) 12015588023296)) (.pow (.var 3) 1)) (.constant (-125) 3003897005824)) (.pow (.var 3) 1)) (.constant (1125) 3003897005824)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 155491662763008) (.pow (.var 3) 1)) (.constant (-125) 51830554254336)) (.pow (.var 3) 1)) (.constant (-125) 5758950472704)) (.pow (.var 3) 1)) (.constant (-875) 213294461952)) (.pow (.var 3) 1)) (.constant (-1125) 71098153984)) (.pow (.var 3) 1)) (.constant (10125) 71098153984))))
compact_certificate_declaration noncomputable def n_c8_2 : Poly := rational_polynomial% "10125/71098153984:;-2875/639883385856:0;1125/3003897005824:1;-1125/71098153984:3;-125/809852410224:0,0;625/27035073052416:0,1;-2375/2879475236352:0,3;-125/3003897005824:1,3;-875/213294461952:3,3;2875/2099137447300608:0,0,0;125/547460229311424:0,0,1;12875/466474988289024:0,0,3;-625/486631314943488:0,1,3;-125/1439737618176:0,3,3;-125/12015588023296:1,3,3;-125/5758950472704:3,3,3;125/10626883326959328:0,0,0,0;875/3434952186491904:0,0,0,3;-125/4379681834491392:0,0,1,3;625/1049568723650304:0,0,3,3;-875/2189840917245696:0,1,3,3;-3875/233237494144512:0,3,3,3;-125/973262629886976:1,3,3,3;-125/51830554254336:3,3,3,3;125/255045199847023872:0,0,0,0,3;125/14169177769279104:0,0,0,3,3;-125/78834273020845056:0,0,1,3,3;-125/4198274894601216:0,0,3,3,3;-125/8759363668982784:0,1,3,3,3;-125/174928120608384:0,3,3,3,3;-125/155491662763008:3,3,3,3,3"
compact_certificate_declaration theorem normalized_c8_2 : r_c8_2.coefficients=n_c8_2 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_2_value (y z w a b u : ℂ) :
    r_c8_2.value (vars y z w a b u)=c8_2 y z w a b := by
  dsimp only [r_c8_2, Expr.value, c8_2, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_2_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_2=c8_2 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_2.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_2).trans (r_c8_2_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_3 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-625) 4080723197552381952) (.pow (.var 3) 1)) (.constant (-625) 170030133231349248)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-875) 453413688616931328) (.pow (.var 3) 1)) (.constant (-625) 8890464482684928)) (.pow (.var 3) 1)) (.constant (-16625) 25189649367607296))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 473005638125070336) (.pow (.var 3) 1)) (.constant (2375) 315337092083380224)) (.pow (.var 3) 1)) (.constant (125) 4379681834491392)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (625) 50379298735214592) (.pow (.var 3) 1)) (.constant (-125) 1526645416218624)) (.pow (.var 3) 1)) (.constant (-47375) 5597699859468288)) (.pow (.var 3) 1)) (.constant (1375) 56542422822912)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 52556182013896704) (.pow (.var 3) 1)) (.constant (625) 8759363668982784)) (.pow (.var 3) 1)) (.constant (625) 898396273741824)) (.pow (.var 3) 1)) (.constant (125) 24955452048384)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (875) 5597699859468288) (.pow (.var 3) 1)) (.constant (4375) 932949976578048)) (.pow (.var 3) 1)) (.constant (29875) 621966651052032)) (.pow (.var 3) 1)) (.constant (8875) 23035801890816)) (.pow (.var 3) 1)) (.constant (7625) 1919650157568)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-625) 3893050519547904) (.pow (.var 3) 1)) (.constant (-3875) 1297683506515968)) (.pow (.var 3) 1)) (.constant (125) 12015588023296)) (.pow (.var 3) 1)) (.constant (2625) 12015588023296)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 34553702836224) (.pow (.var 3) 1)) (.constant (-5875) 69107405672448)) (.pow (.var 3) 1)) (.constant (-3875) 3839300315136)) (.pow (.var 3) 1)) (.constant (375) 142196307968)) (.pow (.var 3) 1)) (.constant (-3375) 284392615936))))
compact_certificate_declaration noncomputable def n_c8_3 : Poly := rational_polynomial% "-3375/284392615936:;7625/1919650157568:0;2625/12015588023296:1;375/142196307968:3;1375/56542422822912:0,0;125/24955452048384:0,1;8875/23035801890816:0,3;125/12015588023296:1,3;-3875/3839300315136:3,3;-16625/25189649367607296:0,0,0;125/4379681834491392:0,0,1;-47375/5597699859468288:0,0,3;625/898396273741824:0,1,3;29875/621966651052032:0,3,3;-3875/1297683506515968:1,3,3;-5875/69107405672448:3,3,3;-625/170030133231349248:0,0,0,0;-625/8890464482684928:0,0,0,3;2375/315337092083380224:0,0,1,3;-125/1526645416218624:0,0,3,3;625/8759363668982784:0,1,3,3;4375/932949976578048:0,3,3,3;-625/3893050519547904:1,3,3,3;-125/34553702836224:3,3,3,3;-625/4080723197552381952:0,0,0,0,3;-875/453413688616931328:0,0,0,3,3;125/473005638125070336:0,0,1,3,3;625/50379298735214592:0,0,3,3,3;125/52556182013896704:0,1,3,3,3;875/5597699859468288:0,3,3,3,3"
compact_certificate_declaration theorem normalized_c8_3 : r_c8_3.coefficients=n_c8_3 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_3_value (y z w a b u : ℂ) :
    r_c8_3.value (vars y z w a b u)=c8_3 y z w a b := by
  dsimp only [r_c8_3, Expr.value, c8_3, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_3_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_3=c8_3 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_3.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_3).trans (r_c8_3_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_4 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 8161446395104763904) (.pow (.var 3) 1)) (.constant (125) 340060266462698496)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 906827377233862656) (.pow (.var 3) 1)) (.constant (875) 100758597470429184)) (.pow (.var 3) 1)) (.constant (27875) 201517194940858368))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 210224728055586816) (.pow (.var 3) 1)) (.constant (-125) 8759363668982784)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 100758597470429184) (.pow (.var 3) 1)) (.constant (125) 8396549789202432)) (.pow (.var 3) 1)) (.constant (625) 574123062509568)) (.pow (.var 3) 1)) (.constant (3875) 1243933302104064)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 35037454675931136) (.pow (.var 3) 1)) (.constant (-5125) 46716606234574848)) (.pow (.var 3) 1)) (.constant (-125) 133095744258048)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 11195399718936576) (.pow (.var 3) 1)) (.constant (-875) 2487866604208128)) (.pow (.var 3) 1)) (.constant (-6125) 621966651052032)) (.pow (.var 3) 1)) (.constant (-4625) 25129965699072)) (.pow (.var 3) 1)) (.constant (-625) 568785231872)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 7786101039095808) (.pow (.var 3) 1)) (.constant (3875) 5190734026063872)) (.pow (.var 3) 1)) (.constant (125) 16963183091712)) (.pow (.var 3) 1)) (.constant (3375) 192249408372736)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 92143207563264) (.pow (.var 3) 1)) (.constant (125) 3412711391232)) (.pow (.var 3) 1)) (.constant (2375) 15357201260544)) (.pow (.var 3) 1)) (.constant (875) 310246490112)) (.pow (.var 3) 1)) (.constant (32625) 1137570463744))))
compact_certificate_declaration noncomputable def n_c8_4 : Poly := rational_polynomial% "32625/1137570463744:;-625/568785231872:0;3375/192249408372736:1;875/310246490112:3;3875/1243933302104064:0,0;-125/133095744258048:0,1;-4625/25129965699072:0,3;125/16963183091712:1,3;2375/15357201260544:3,3;27875/201517194940858368:0,0,0;-125/8759363668982784:0,0,1;625/574123062509568:0,0,3;-5125/46716606234574848:0,1,3;-6125/621966651052032:0,3,3;3875/5190734026063872:1,3,3;125/3412711391232:3,3,3;125/340060266462698496:0,0,0,0;875/100758597470429184:0,0,0,3;-125/210224728055586816:0,0,1,3;125/8396549789202432:0,0,3,3;-125/35037454675931136:0,1,3,3;-875/2487866604208128:0,3,3,3;125/7786101039095808:1,3,3,3;125/92143207563264:3,3,3,3;125/8161446395104763904:0,0,0,0,3;125/906827377233862656:0,0,0,3,3;-125/100758597470429184:0,0,3,3,3;-125/11195399718936576:0,3,3,3,3"
compact_certificate_declaration theorem normalized_c8_4 : r_c8_4.coefficients=n_c8_4 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_4_value (y z w a b u : ℂ) :
    r_c8_4.value (vars y z w a b u)=c8_4 y z w a b := by
  dsimp only [r_c8_4, Expr.value, c8_4, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_4_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_4=c8_4 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_4.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_4).trans (r_c8_4_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_5 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 109918469967740928) (.pow (.var 3) 1)) (.constant (-5375) 201517194940858368)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-625) 134344796627238912) (.pow (.var 3) 1)) (.constant (-125) 1105718490759168)) (.pow (.var 3) 1)) (.constant (-9125) 9951466416832512))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-625) 93433212469149696) (.pow (.var 3) 1)) (.constant (-125) 1730244675354624)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (625) 14927199625248768) (.pow (.var 3) 1)) (.constant (12875) 9951466416832512)) (.pow (.var 3) 1)) (.constant (11875) 552859245379584)) (.pow (.var 3) 1)) (.constant (12125) 40952536694784)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (-625) 10381468052127744) (.pow (.var 3) 1)) (.constant (-125) 104863313657856)) (.pow (.var 3) 1)) (.constant (-1125) 192249408372736)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (-125) 1658577736138752) (.pow (.var 3) 1)) (.constant (-125) 20476268347392)) (.pow (.var 3) 1)) (.constant (-4375) 61428805042176)) (.pow (.var 3) 1)) (.constant (-2875) 3412711391232)) (.pow (.var 3) 1)) (.constant (-8625) 1137570463744))))
compact_certificate_declaration noncomputable def n_c8_5 : Poly := rational_polynomial% "-8625/1137570463744:;12125/40952536694784:0;-1125/192249408372736:1;-2875/3412711391232:3;-9125/9951466416832512:0,0;-125/1730244675354624:0,1;11875/552859245379584:0,3;-125/104863313657856:1,3;-4375/61428805042176:3,3;-5375/201517194940858368:0,0,0;-125/1105718490759168:0,0,3;-625/93433212469149696:0,1,3;12875/9951466416832512:0,3,3;-625/10381468052127744:1,3,3;-125/20476268347392:3,3,3;-125/109918469967740928:0,0,0,3;-625/134344796627238912:0,0,3,3;625/14927199625248768:0,3,3,3;-125/1658577736138752:3,3,3,3"
compact_certificate_declaration theorem normalized_c8_5 : r_c8_5.coefficients=n_c8_5 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_5_value (y z w a b u : ℂ) :
    r_c8_5.value (vars y z w a b u)=c8_5 y z w a b := by
  dsimp only [r_c8_5, Expr.value, c8_5, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_5_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_5=c8_5 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_5.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_5).trans (r_c8_5_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_6 : Expr := (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.constant (125) 806068779763433472) (.pow (.var 3) 1)) (.constant (2875) 806068779763433472)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 89563197751492608) (.pow (.var 3) 1)) (.constant (875) 44781598875746304)) (.pow (.var 3) 1)) (.constant (-125) 510331611119616))) (.pow (.var 0) 1)) (.add (.mul (.constant (125) 20762936104255488) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.constant (-625) 9951466416832512) (.pow (.var 3) 1)) (.constant (-875) 245715220168704)) (.pow (.var 3) 1)) (.constant (-5875) 122857610084352)))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 2306992900472832) (.pow (.var 3) 1)) (.constant (375) 768997633490944)) (.pow (.var 1) 1)) (.add (.mul (.add (.mul (.add (.mul (.constant (125) 276429622689792) (.pow (.var 3) 1)) (.constant (875) 245715220168704)) (.pow (.var 3) 1)) (.constant (625) 13650845564928)) (.pow (.var 3) 1)) (.constant (2625) 1137570463744))))
compact_certificate_declaration noncomputable def n_c8_6 : Poly := rational_polynomial% "2625/1137570463744:;-5875/122857610084352:0;375/768997633490944:1;625/13650845564928:3;-125/510331611119616:0,0;125/20762936104255488:0,1;-875/245715220168704:0,3;125/2306992900472832:1,3;875/245715220168704:3,3;2875/806068779763433472:0,0,0;875/44781598875746304:0,0,3;-625/9951466416832512:0,3,3;125/276429622689792:3,3,3;125/806068779763433472:0,0,0,3;125/89563197751492608:0,0,3,3"
compact_certificate_declaration theorem normalized_c8_6 : r_c8_6.coefficients=n_c8_6 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_6_value (y z w a b u : ℂ) :
    r_c8_6.value (vars y z w a b u)=c8_6 y z w a b := by
  dsimp only [r_c8_6, Expr.value, c8_6, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_6_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_6=c8_6 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_6.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_6).trans (r_c8_6_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_7 : Expr := (.add (.mul (.add (.mul (.add (.mul (.constant (125) 119417597001990144) (.pow (.var 3) 1)) (.constant (125) 4422873963036672)) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (125) 13268621889110016) (.pow (.var 3) 1)) (.constant (5125) 8845747926073344)) (.pow (.var 3) 1)) (.constant (125) 12600780521472))) (.pow (.var 0) 1)) (.add (.mul (.add (.mul (.constant (-125) 245715220168704) (.pow (.var 3) 1)) (.constant (-125) 9100563709952)) (.pow (.var 3) 1)) (.constant (-375) 2141309108224)))
compact_certificate_declaration noncomputable def n_c8_7 : Poly := rational_polynomial% "-375/2141309108224:;125/12600780521472:0;-125/9100563709952:3;125/4422873963036672:0,0;5125/8845747926073344:0,3;-125/245715220168704:3,3;125/119417597001990144:0,0,3;125/13268621889110016:0,3,3"
compact_certificate_declaration theorem normalized_c8_7 : r_c8_7.coefficients=n_c8_7 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_7_value (y z w a b u : ℂ) :
    r_c8_7.value (vars y z w a b u)=c8_7 y z w a b := by
  dsimp only [r_c8_7, Expr.value, c8_7, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_7_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_7=c8_7 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_7.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_7).trans (r_c8_7_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_8 : Expr := (.add (.mul (.add (.mul (.constant (-125) 79611731334660096) (.pow (.var 0) 1)) (.add (.mul (.constant (-125) 1608317804740608) (.pow (.var 3) 1)) (.constant (-125) 81905073389568))) (.pow (.var 0) 1)) (.add (.mul (.constant (625) 145609019359232) (.pow (.var 3) 1)) (.constant (10875) 145609019359232)))
compact_certificate_declaration noncomputable def n_c8_8 : Poly := rational_polynomial% "10875/145609019359232:;-125/81905073389568:0;625/145609019359232:3;-125/79611731334660096:0,0;-125/1608317804740608:0,3"
compact_certificate_declaration theorem normalized_c8_8 : r_c8_8.coefficients=n_c8_8 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_8_value (y z w a b u : ℂ) :
    r_c8_8.value (vars y z w a b u)=c8_8 y z w a b := by
  dsimp only [r_c8_8, Expr.value, c8_8, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_8_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_8=c8_8 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_8.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_8).trans (r_c8_8_value y z w a b u))
compact_certificate_declaration noncomputable def r_c8_9 : Expr := (.add (.mul (.constant (-125) 291218038718464) (.pow (.var 3) 1)) (.constant (-375) 36402254839808))
compact_certificate_declaration noncomputable def n_c8_9 : Poly := rational_polynomial% "-375/36402254839808:;-125/291218038718464:3"
compact_certificate_declaration theorem normalized_c8_9 : r_c8_9.coefficients=n_c8_9 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c8_9_value (y z w a b u : ℂ) :
    r_c8_9.value (vars y z w a b u)=c8_9 y z w a b := by
  dsimp only [r_c8_9, Expr.value, c8_9, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c8_9_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c8_9=c8_9 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c8_9.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c8_9).trans (r_c8_9_value y z w a b u))
compact_certificate_declaration noncomputable def r_c9_0 : Expr := (.natural 0)
compact_certificate_declaration noncomputable def n_c9_0 : Poly := rational_polynomial% "0/1:"
compact_certificate_declaration theorem normalized_c9_0 : r_c9_0.coefficients=n_c9_0 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c9_0_value (y z w a b u : ℂ) :
    r_c9_0.value (vars y z w a b u)=c9_0 y z w a b := by
  dsimp only [r_c9_0, Expr.value, c9_0, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c9_0_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c9_0=c9_0 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c9_0.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c9_0).trans (r_c9_0_value y z w a b u))
compact_certificate_declaration noncomputable def r_c9_1 : Expr := (.add (.mul (.constant (5) 4563) (.pow (.var 3) 1)) (.constant (-5) 507))
compact_certificate_declaration noncomputable def n_c9_1 : Poly := rational_polynomial% "-5/507:;5/4563:3"
compact_certificate_declaration theorem normalized_c9_1 : r_c9_1.coefficients=n_c9_1 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c9_1_value (y z w a b u : ℂ) :
    r_c9_1.value (vars y z w a b u)=c9_1 y z w a b := by
  dsimp only [r_c9_1, Expr.value, c9_1, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c9_1_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c9_1=c9_1 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c9_1.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c9_1).trans (r_c9_1_value y z w a b u))
compact_certificate_declaration noncomputable def r_c9_2 : Expr := (.add (.mul (.constant (-5) 328536) (.pow (.var 0) 1)) (.add (.mul (.constant (5) 36504) (.pow (.var 3) 1)) (.constant (-5) 4056)))
compact_certificate_declaration noncomputable def n_c9_2 : Poly := rational_polynomial% "-5/4056:;-5/328536:0;5/36504:3"
compact_certificate_declaration theorem normalized_c9_2 : r_c9_2.coefficients=n_c9_2 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c9_2_value (y z w a b u : ℂ) :
    r_c9_2.value (vars y z w a b u)=c9_2 y z w a b := by
  dsimp only [r_c9_2, Expr.value, c9_2, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c9_2_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c9_2=c9_2 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c9_2.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c9_2).trans (r_c9_2_value y z w a b u))
compact_certificate_declaration noncomputable def r_c9_3 : Expr := (.add (.mul (.constant (5) 1314144) (.pow (.var 0) 1)) (.add (.mul (.constant (5) 146016) (.pow (.var 3) 1)) (.constant (-5) 16224)))
compact_certificate_declaration noncomputable def n_c9_3 : Poly := rational_polynomial% "-5/16224:;5/1314144:0;5/146016:3"
compact_certificate_declaration theorem normalized_c9_3 : r_c9_3.coefficients=n_c9_3 := by
  staged_rational_coefficients
compact_certificate_declaration theorem r_c9_3_value (y z w a b u : ℂ) :
    r_c9_3.value (vars y z w a b u)=c9_3 y z w a b := by
  dsimp only [r_c9_3, Expr.value, c9_3, vars]
  simp only [sub_eq_add_neg, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
compact_certificate_declaration theorem n_c9_3_value (y z w a b u : ℂ) :
    eval (vars y z w a b u) n_c9_3=c9_3 y z w a b := by
  exact (congrArg (eval (vars y z w a b u)) normalized_c9_3.symm).trans
    ((Expr.eval_coefficients (vars y z w a b u) r_c9_3).trans (r_c9_3_value y z w a b u))
noncomputable def mulShort (p q : Poly) : Poly :=
  if p.length <= q.length then SmallLevelSparseRationalPolynomialCheck.mul p q else SmallLevelSparseRationalPolynomialCheck.mul q p
theorem eval_mulShort (v : ℕ→ℂ) (p q : Poly) :
    eval v (mulShort p q)=eval v p*eval v q := by
  unfold mulShort
  split <;> simp only [eval_mul, mul_comm]
compact_certificate_declaration noncomputable def product_0 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4;0/1:2,3,3,3,3;0/1:3,3,3,3,3;0/1:3,3,3,3,4"
compact_certificate_declaration theorem product_0_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_0 n_c1_0=product_0 := by
  decide +kernel
compact_certificate_declaration theorem product_0_value (v : ℕ→ℂ) :
    eval v product_0=eval v n_c0_0*eval v n_c1_0 := by
  rw [←product_0_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_0 : Poly := rational_polynomial% "0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4;0/1:2,3,3,3,3;0/1:3,3,3,3,3;0/1:3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_0_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_0 [([],(0:ℚ))])=partial_sum_0 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_0_value (v : ℕ→ℂ) :
    eval v partial_sum_0=eval v product_0+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_0_checked, eval_add]
compact_certificate_declaration noncomputable def product_1 : Poly := rational_polynomial% "0/1:"
compact_certificate_declaration theorem product_1_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) [([],(0:ℚ))]=product_1 := by
  decide +kernel
compact_certificate_declaration theorem product_1_value (v : ℕ→ℂ) :
    eval v product_1=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v [([],(0:ℚ))] := by
  rw [←product_1_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_1 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4;0/1:2,3,3,3,3;0/1:3,3,3,3,3;0/1:3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_1_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_0 product_1)=partial_sum_1 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_1_value (v : ℕ→ℂ) :
    eval v partial_sum_1=eval v partial_sum_0+eval v product_1 := by
  rw [←partial_sum_1_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_2 : Poly := rational_polynomial% "0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4;0/1:2,3,3,3,3;0/1:3,3,3,3,3;0/1:3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_2_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_1 product_1)=partial_sum_2 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_2_value (v : ℕ→ℂ) :
    eval v partial_sum_2=eval v partial_sum_1+eval v product_1 := by
  rw [←partial_sum_2_checked, eval_add]
compact_certificate_declaration noncomputable def product_2 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4"
compact_certificate_declaration theorem product_2_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_0 n_c7_0) [([],(0:ℚ))])=product_2 := by
  decide +kernel
compact_certificate_declaration theorem product_2_value (v : ℕ→ℂ) :
    eval v product_2=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_0 n_c7_0) [([],(0:ℚ))]) := by
  rw [←product_2_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_3 : Poly := rational_polynomial% "0/1:;0/1:2;0/1:3;0/1:4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:2,3,3,3,3;0/1:3,3,3,3,3;0/1:3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_3_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_2 product_2)=partial_sum_3 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_3_value (v : ℕ→ℂ) :
    eval v partial_sum_3=eval v partial_sum_2+eval v product_2 := by
  rw [←partial_sum_3_checked, eval_add]
compact_certificate_declaration noncomputable def product_3 : Poly := rational_polynomial% "0/1:"
compact_certificate_declaration theorem product_3_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_0 n_c9_0) [([],(0:ℚ))])=product_3 := by
  decide +kernel
compact_certificate_declaration theorem product_3_value (v : ℕ→ℂ) :
    eval v product_3=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_0 n_c9_0) [([],(0:ℚ))]) := by
  rw [←product_3_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_4 : Poly := rational_polynomial% "0/1:2;0/1:3;0/1:4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:2,3,3,3,3;0/1:3,3,3,3,3;0/1:3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_4_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_3 product_3)=partial_sum_4 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_4_value (v : ℕ→ℂ) :
    eval v partial_sum_4=eval v partial_sum_3+eval v product_3 := by
  rw [←partial_sum_4_checked, eval_add]
compact_certificate_declaration noncomputable def e0 : Poly := partial_sum_4
compact_certificate_declaration theorem checked_0 : checkZero e0=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_0 (y z w a b : ℂ) :
    (certificate y z w a b)[0]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_0 y z w a b))+0)+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_0 y z w a b))+0)))+((-1)*(((c8_0 y z w a b)*(c9_0 y z w a b))+0)))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e0 checked_0
  simp only [e0, eval_add, eval_mul, eval_scale, eval_pow, product_0_value, partial_sum_0_value, product_1_value, partial_sum_1_value, partial_sum_2_value, product_2_value, partial_sum_3_value, product_3_value, partial_sum_4_value, n_c0_0_value y z w a b 0, n_c1_0_value y z w a b 0, n_c6_0_value y z w a b 0, n_c7_0_value y z w a b 0, n_c8_0_value y z w a b 0, n_c9_0_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_0
compact_certificate_declaration noncomputable def product_4 : Poly := rational_polynomial% "-625/2252922754368:0;625/68432528663928:0,0;-1/6758768263104:0,2;4375/60828914367936:0,3;-25/6758768263104:0,4;625/22172139287112672:0,0,0;5/1642380687934272:0,0,2;625/1847678273926056:0,0,3;125/1642380687934272:0,0,4;1/22810842887976:0,2,3;3125/1642380687934272:0,3,3;25/22810842887976:0,3,4;-11875/10775659693536758592:0,0,0,0;1/16629104465334504:0,0,0,2;-36875/1197295521504084288:0,0,0,3;25/16629104465334504:0,0,0,4;1/2463571031901408:0,0,2,3;-3125/10233295055590464:0,0,3,3;25/2463571031901408:0,0,3,4;1/1642380687934272:0,2,3,3;-625/671883008700384:0,3,3,3;25/1642380687934272:0,3,3,4;625/109103554397059680744:0,0,0,0,0;625/3730036047762724128:0,0,0,0,3;-1/92099655500314176:0,0,0,2,3;3125/1197295521504084288:0,0,0,3,3;-25/92099655500314176:0,0,0,3,4;-7/44344278574225344:0,0,2,3,3;4375/299323880376021072:0,0,3,3,3;-175/44344278574225344:0,0,3,3,4;-1/1343766017400768:0,2,3,3,3;4375/133032835722676032:0,3,3,3,3;-25/1343766017400768:0,3,3,3,4;-3125/7855455916588297013568:0,0,0,0,0,3;-625/872828435176477445952:0,0,0,0,3,3;1/5387829846768379296:0,0,0,2,3,3;4375/48490468620915413664:0,0,0,3,3,3;25/5387829846768379296:0,0,0,3,3,4;1/299323880376021072:0,0,2,3,3,3;625/979605426685159872:0,0,3,3,3,3;25/299323880376021072:0,0,3,3,3,4;1/66516417861338016:0,2,3,3,3,3;625/1197295521504084288:0,3,3,3,3,3;25/66516417861338016:0,3,3,3,3,4;-625/23566367749764891040704:0,0,0,0,0,3,3;-625/1309242652764716168928:0,0,0,0,3,3,3;1/32326979080610275776:0,0,0,2,3,3,3;-625/145471405862746240992:0,0,0,3,3,3,3;25/32326979080610275776:0,0,0,3,3,3,4;1/1795943282256126432:0,0,2,3,3,3,3;-625/16163489540305137888:0,0,3,3,3,3,3;25/1795943282256126432:0,0,3,3,3,3,4;1/399098507168028096:0,2,3,3,3,3,3;-625/3591886564512252864:0,3,3,3,3,3,3;25/399098507168028096:0,3,3,3,3,3,4"
compact_certificate_declaration theorem product_4_checked :
    mulShort n_c0_0 n_c1_1=product_4 := by
  decide +kernel
compact_certificate_declaration theorem product_4_value (v : ℕ→ℂ) :
    eval v product_4=eval v n_c0_0*eval v n_c1_1 := by
  rw [←product_4_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_5 : Poly := rational_polynomial% "0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4"
compact_certificate_declaration theorem product_5_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_1 n_c1_0=product_5 := by
  decide +kernel
compact_certificate_declaration theorem product_5_value (v : ℕ→ℂ) :
    eval v product_5=eval v n_c0_1*eval v n_c1_0 := by
  rw [←product_5_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_5 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4"
compact_certificate_declaration theorem partial_sum_5_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_5 [([],(0:ℚ))])=partial_sum_5 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_5_value (v : ℕ→ℂ) :
    eval v partial_sum_5=eval v product_5+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_5_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_6 : Poly := rational_polynomial% "0/1:;-625/2252922754368:0;0/1:2;0/1:3;0/1:4;625/68432528663928:0,0;-1/6758768263104:0,2;4375/60828914367936:0,3;-25/6758768263104:0,4;0/1:2,3;0/1:3,3;0/1:3,4;625/22172139287112672:0,0,0;5/1642380687934272:0,0,2;625/1847678273926056:0,0,3;125/1642380687934272:0,0,4;1/22810842887976:0,2,3;3125/1642380687934272:0,3,3;25/22810842887976:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;-11875/10775659693536758592:0,0,0,0;1/16629104465334504:0,0,0,2;-36875/1197295521504084288:0,0,0,3;25/16629104465334504:0,0,0,4;1/2463571031901408:0,0,2,3;-3125/10233295055590464:0,0,3,3;25/2463571031901408:0,0,3,4;1/1642380687934272:0,2,3,3;-625/671883008700384:0,3,3,3;25/1642380687934272:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;625/109103554397059680744:0,0,0,0,0;625/3730036047762724128:0,0,0,0,3;-1/92099655500314176:0,0,0,2,3;3125/1197295521504084288:0,0,0,3,3;-25/92099655500314176:0,0,0,3,4;-7/44344278574225344:0,0,2,3,3;4375/299323880376021072:0,0,3,3,3;-175/44344278574225344:0,0,3,3,4;-1/1343766017400768:0,2,3,3,3;4375/133032835722676032:0,3,3,3,3;-25/1343766017400768:0,3,3,3,4;-3125/7855455916588297013568:0,0,0,0,0,3;-625/872828435176477445952:0,0,0,0,3,3;1/5387829846768379296:0,0,0,2,3,3;4375/48490468620915413664:0,0,0,3,3,3;25/5387829846768379296:0,0,0,3,3,4;1/299323880376021072:0,0,2,3,3,3;625/979605426685159872:0,0,3,3,3,3;25/299323880376021072:0,0,3,3,3,4;1/66516417861338016:0,2,3,3,3,3;625/1197295521504084288:0,3,3,3,3,3;25/66516417861338016:0,3,3,3,3,4;-625/23566367749764891040704:0,0,0,0,0,3,3;-625/1309242652764716168928:0,0,0,0,3,3,3;1/32326979080610275776:0,0,0,2,3,3,3;-625/145471405862746240992:0,0,0,3,3,3,3;25/32326979080610275776:0,0,0,3,3,3,4;1/1795943282256126432:0,0,2,3,3,3,3;-625/16163489540305137888:0,0,3,3,3,3,3;25/1795943282256126432:0,0,3,3,3,3,4;1/399098507168028096:0,2,3,3,3,3,3;-625/3591886564512252864:0,3,3,3,3,3,3;25/399098507168028096:0,3,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_6_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_4 partial_sum_5)=partial_sum_6 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_6_value (v : ℕ→ℂ) :
    eval v partial_sum_6=eval v product_4+eval v partial_sum_5 := by
  rw [←partial_sum_6_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_7 : Poly := rational_polynomial% "-625/2252922754368:0;0/1:2;0/1:3;0/1:4;625/68432528663928:0,0;-1/6758768263104:0,2;4375/60828914367936:0,3;-25/6758768263104:0,4;0/1:2,3;0/1:3,3;0/1:3,4;625/22172139287112672:0,0,0;5/1642380687934272:0,0,2;625/1847678273926056:0,0,3;125/1642380687934272:0,0,4;1/22810842887976:0,2,3;3125/1642380687934272:0,3,3;25/22810842887976:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;-11875/10775659693536758592:0,0,0,0;1/16629104465334504:0,0,0,2;-36875/1197295521504084288:0,0,0,3;25/16629104465334504:0,0,0,4;1/2463571031901408:0,0,2,3;-3125/10233295055590464:0,0,3,3;25/2463571031901408:0,0,3,4;1/1642380687934272:0,2,3,3;-625/671883008700384:0,3,3,3;25/1642380687934272:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;625/109103554397059680744:0,0,0,0,0;625/3730036047762724128:0,0,0,0,3;-1/92099655500314176:0,0,0,2,3;3125/1197295521504084288:0,0,0,3,3;-25/92099655500314176:0,0,0,3,4;-7/44344278574225344:0,0,2,3,3;4375/299323880376021072:0,0,3,3,3;-175/44344278574225344:0,0,3,3,4;-1/1343766017400768:0,2,3,3,3;4375/133032835722676032:0,3,3,3,3;-25/1343766017400768:0,3,3,3,4;-3125/7855455916588297013568:0,0,0,0,0,3;-625/872828435176477445952:0,0,0,0,3,3;1/5387829846768379296:0,0,0,2,3,3;4375/48490468620915413664:0,0,0,3,3,3;25/5387829846768379296:0,0,0,3,3,4;1/299323880376021072:0,0,2,3,3,3;625/979605426685159872:0,0,3,3,3,3;25/299323880376021072:0,0,3,3,3,4;1/66516417861338016:0,2,3,3,3,3;625/1197295521504084288:0,3,3,3,3,3;25/66516417861338016:0,3,3,3,3,4;-625/23566367749764891040704:0,0,0,0,0,3,3;-625/1309242652764716168928:0,0,0,0,3,3,3;1/32326979080610275776:0,0,0,2,3,3,3;-625/145471405862746240992:0,0,0,3,3,3,3;25/32326979080610275776:0,0,0,3,3,3,4;1/1795943282256126432:0,0,2,3,3,3,3;-625/16163489540305137888:0,0,3,3,3,3,3;25/1795943282256126432:0,0,3,3,3,3,4;1/399098507168028096:0,2,3,3,3,3,3;-625/3591886564512252864:0,3,3,3,3,3,3;25/399098507168028096:0,3,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_7_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_6 product_1)=partial_sum_7 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_7_value (v : ℕ→ℂ) :
    eval v partial_sum_7=eval v partial_sum_6+eval v product_1 := by
  rw [←partial_sum_7_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_8 : Poly := rational_polynomial% "0/1:;-625/2252922754368:0;0/1:2;0/1:3;0/1:4;625/68432528663928:0,0;-1/6758768263104:0,2;4375/60828914367936:0,3;-25/6758768263104:0,4;0/1:2,3;0/1:3,3;0/1:3,4;625/22172139287112672:0,0,0;5/1642380687934272:0,0,2;625/1847678273926056:0,0,3;125/1642380687934272:0,0,4;1/22810842887976:0,2,3;3125/1642380687934272:0,3,3;25/22810842887976:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;-11875/10775659693536758592:0,0,0,0;1/16629104465334504:0,0,0,2;-36875/1197295521504084288:0,0,0,3;25/16629104465334504:0,0,0,4;1/2463571031901408:0,0,2,3;-3125/10233295055590464:0,0,3,3;25/2463571031901408:0,0,3,4;1/1642380687934272:0,2,3,3;-625/671883008700384:0,3,3,3;25/1642380687934272:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;625/109103554397059680744:0,0,0,0,0;625/3730036047762724128:0,0,0,0,3;-1/92099655500314176:0,0,0,2,3;3125/1197295521504084288:0,0,0,3,3;-25/92099655500314176:0,0,0,3,4;-7/44344278574225344:0,0,2,3,3;4375/299323880376021072:0,0,3,3,3;-175/44344278574225344:0,0,3,3,4;-1/1343766017400768:0,2,3,3,3;4375/133032835722676032:0,3,3,3,3;-25/1343766017400768:0,3,3,3,4;-3125/7855455916588297013568:0,0,0,0,0,3;-625/872828435176477445952:0,0,0,0,3,3;1/5387829846768379296:0,0,0,2,3,3;4375/48490468620915413664:0,0,0,3,3,3;25/5387829846768379296:0,0,0,3,3,4;1/299323880376021072:0,0,2,3,3,3;625/979605426685159872:0,0,3,3,3,3;25/299323880376021072:0,0,3,3,3,4;1/66516417861338016:0,2,3,3,3,3;625/1197295521504084288:0,3,3,3,3,3;25/66516417861338016:0,3,3,3,3,4;-625/23566367749764891040704:0,0,0,0,0,3,3;-625/1309242652764716168928:0,0,0,0,3,3,3;1/32326979080610275776:0,0,0,2,3,3,3;-625/145471405862746240992:0,0,0,3,3,3,3;25/32326979080610275776:0,0,0,3,3,3,4;1/1795943282256126432:0,0,2,3,3,3,3;-625/16163489540305137888:0,0,3,3,3,3,3;25/1795943282256126432:0,0,3,3,3,3,4;1/399098507168028096:0,2,3,3,3,3,3;-625/3591886564512252864:0,3,3,3,3,3,3;25/399098507168028096:0,3,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_8_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_7 product_1)=partial_sum_8 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_8_value (v : ℕ→ℂ) :
    eval v partial_sum_8=eval v partial_sum_7+eval v product_1 := by
  rw [←partial_sum_8_checked, eval_add]
compact_certificate_declaration noncomputable def product_6 : Poly := rational_polynomial% "0/1:;625/2252922754368:0;0/1:1;-625/68432528663928:0,0;0/1:0,1;1/6758768263104:0,2;-4375/60828914367936:0,3;25/6758768263104:0,4;0/1:1,3;0/1:3,3;-625/22172139287112672:0,0,0;-5/1642380687934272:0,0,2;-625/1847678273926056:0,0,3;-125/1642380687934272:0,0,4;0/1:0,1,3;-1/22810842887976:0,2,3;-3125/1642380687934272:0,3,3;-25/22810842887976:0,3,4;0/1:1,3,3;0/1:3,3,3;11875/10775659693536758592:0,0,0,0;-1/16629104465334504:0,0,0,2;36875/1197295521504084288:0,0,0,3;-25/16629104465334504:0,0,0,4;-1/2463571031901408:0,0,2,3;3125/10233295055590464:0,0,3,3;-25/2463571031901408:0,0,3,4;0/1:0,1,3,3;-1/1642380687934272:0,2,3,3;625/671883008700384:0,3,3,3;-25/1642380687934272:0,3,3,4;0/1:1,3,3,3;0/1:3,3,3,3;-625/109103554397059680744:0,0,0,0,0;-625/3730036047762724128:0,0,0,0,3;1/92099655500314176:0,0,0,2,3;-3125/1197295521504084288:0,0,0,3,3;25/92099655500314176:0,0,0,3,4;7/44344278574225344:0,0,2,3,3;-4375/299323880376021072:0,0,3,3,3;175/44344278574225344:0,0,3,3,4;1/1343766017400768:0,2,3,3,3;-4375/133032835722676032:0,3,3,3,3;25/1343766017400768:0,3,3,3,4;3125/7855455916588297013568:0,0,0,0,0,3;625/872828435176477445952:0,0,0,0,3,3;-1/5387829846768379296:0,0,0,2,3,3;-4375/48490468620915413664:0,0,0,3,3,3;-25/5387829846768379296:0,0,0,3,3,4;-1/299323880376021072:0,0,2,3,3,3;-625/979605426685159872:0,0,3,3,3,3;-25/299323880376021072:0,0,3,3,3,4;-1/66516417861338016:0,2,3,3,3,3;-625/1197295521504084288:0,3,3,3,3,3;-25/66516417861338016:0,3,3,3,3,4;625/23566367749764891040704:0,0,0,0,0,3,3;625/1309242652764716168928:0,0,0,0,3,3,3;-1/32326979080610275776:0,0,0,2,3,3,3;625/145471405862746240992:0,0,0,3,3,3,3;-25/32326979080610275776:0,0,0,3,3,3,4;-1/1795943282256126432:0,0,2,3,3,3,3;625/16163489540305137888:0,0,3,3,3,3,3;-25/1795943282256126432:0,0,3,3,3,3,4;-1/399098507168028096:0,2,3,3,3,3,3;625/3591886564512252864:0,3,3,3,3,3,3;-25/399098507168028096:0,3,3,3,3,3,4"
compact_certificate_declaration theorem product_6_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_0 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_1 n_c7_0) [([],(0:ℚ))]))=product_6 := by
  decide +kernel
compact_certificate_declaration theorem product_6_value (v : ℕ→ℂ) :
    eval v product_6=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_0 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_1 n_c7_0) [([],(0:ℚ))])) := by
  rw [←product_6_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_9 : Poly := rational_polynomial% "0/1:1;0/1:2;0/1:3;0/1:4;0/1:0,1;0/1:1,3;0/1:2,3;0/1:3,4;0/1:0,1,3;0/1:1,3,3;0/1:2,3,3;0/1:3,3,4;0/1:0,1,3,3;0/1:1,3,3,3;0/1:2,3,3,3;0/1:3,3,3,4"
compact_certificate_declaration theorem partial_sum_9_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_8 product_6)=partial_sum_9 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_9_value (v : ℕ→ℂ) :
    eval v partial_sum_9=eval v partial_sum_8+eval v product_6 := by
  rw [←partial_sum_9_checked, eval_add]
compact_certificate_declaration noncomputable def product_7 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:1;0/1:0,0;0/1:0,1;0/1:0,3;0/1:1,3;0/1:3,3;0/1:0,0,0;0/1:0,0,1;0/1:0,0,3;0/1:0,1,3;0/1:0,3,3;0/1:1,3,3;0/1:3,3,3;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,1,3;0/1:0,0,3,3;0/1:0,1,3,3;0/1:0,3,3,3;0/1:1,3,3,3;0/1:3,3,3,3;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,1,3,3;0/1:0,0,3,3,3;0/1:0,1,3,3,3;0/1:0,3,3,3,3;0/1:1,3,3,3,3;0/1:3,3,3,3,3"
compact_certificate_declaration theorem product_7_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_0 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_1 n_c9_0) [([],(0:ℚ))]))=product_7 := by
  decide +kernel
compact_certificate_declaration theorem product_7_value (v : ℕ→ℂ) :
    eval v product_7=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_0 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_1 n_c9_0) [([],(0:ℚ))])) := by
  rw [←product_7_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_10 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,3;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,1;0/1:0,0,3;0/1:0,3,3;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,1,3;0/1:0,0,3,3;0/1:0,3,3,3;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,1,3,3;0/1:0,0,3,3,3;0/1:0,1,3,3,3;0/1:0,3,3,3,3;0/1:1,3,3,3,3;0/1:3,3,3,3,3"
compact_certificate_declaration theorem partial_sum_10_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_9 product_7)=partial_sum_10 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_10_value (v : ℕ→ℂ) :
    eval v partial_sum_10=eval v partial_sum_9+eval v product_7 := by
  rw [←partial_sum_10_checked, eval_add]
compact_certificate_declaration noncomputable def e1 : Poly := partial_sum_10
compact_certificate_declaration theorem checked_1 : checkZero e1=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_1 (y z w a b : ℂ) :
    (certificate y z w a b)[1]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_1 y z w a b))+(((c0_1 y z w a b)*(c1_0 y z w a b))+0))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_1 y z w a b))+(((c6_1 y z w a b)*(c7_0 y z w a b))+0))))+((-1)*(((c8_0 y z w a b)*(c9_1 y z w a b))+(((c8_1 y z w a b)*(c9_0 y z w a b))+0))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e1 checked_1
  simp only [e1, eval_add, eval_mul, eval_scale, eval_pow, product_4_value, product_5_value, partial_sum_5_value, partial_sum_6_value, product_1_value, partial_sum_7_value, partial_sum_8_value, product_6_value, partial_sum_9_value, product_7_value, partial_sum_10_value, n_c0_0_value y z w a b 0, n_c0_1_value y z w a b 0, n_c1_0_value y z w a b 0, n_c1_1_value y z w a b 0, n_c6_0_value y z w a b 0, n_c6_1_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c8_0_value y z w a b 0, n_c8_1_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_1
compact_certificate_declaration noncomputable def product_8 : Poly := rational_polynomial% "-625/9011691017472:0;625/273730114655712:0,0;-1/27035073052416:0,2;625/60828914367936:0,3;-25/27035073052416:0,4;625/88688557148450688:0,0,0;5/6569522751737088:0,0,2;625/1847678273926056:0,0,3;125/6569522751737088:0,0,4;5/729946972415232:0,2,3;625/386442514808064:0,3,3;125/729946972415232:0,3,4;-11875/43102638774147034368:0,0,0,0;1/66516417861338016:0,0,0,2;-33125/4789182086016337152:0,0,0,3;25/66516417861338016:0,0,0,4;1/5375064069603072:0,0,2,3;-625/16125192208809216:0,0,3,3;25/5375064069603072:0,0,3,4;1/1094920458622848:0,2,3,3;-3125/59125704765633792:0,3,3,3;25/1094920458622848:0,3,3,4;625/436414217588238722976:0,0,0,0,0;4375/387923748967323309312:0,0,0,0,3;-5/4789182086016337152:0,0,0,2,3;-625/5387829846768379296:0,0,0,3,3;-125/4789182086016337152:0,0,0,3,4;-5/266065671445352064:0,0,2,3,3;-3125/4789182086016337152:0,0,3,3,3;-125/266065671445352064:0,0,3,3,4;-5/59125704765633792:0,2,3,3,3;625/266065671445352064:0,3,3,3,3;-125/59125704765633792:0,3,3,3,4;625/10473941222117729351424:0,0,0,0,0,3;625/581885623450984963968:0,0,0,0,3,3;-1/14367546258049011456:0,0,0,2,3,3;625/64653958161220551552:0,0,0,3,3,3;-25/14367546258049011456:0,0,0,3,3,4;-1/798197014336056192:0,0,2,3,3,3;625/7183773129024505728:0,0,3,3,3,3;-25/798197014336056192:0,0,3,3,3,4;-1/177377114296901376:0,2,3,3,3,3;625/1596394028672112384:0,3,3,3,3,3;-25/177377114296901376:0,3,3,3,3,4"
compact_certificate_declaration theorem product_8_checked :
    mulShort n_c0_0 n_c1_2=product_8 := by
  decide +kernel
compact_certificate_declaration theorem product_8_value (v : ℕ→ℂ) :
    eval v product_8=eval v n_c0_0*eval v n_c1_2 := by
  rw [←product_8_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_9 : Poly := rational_polynomial% "-55625/6569522751737088:0,0;-1/20276304789312:0,2;-625/81105219157248:0,3;-25/20276304789312:0,4;625/20466590111180928:0,0,0;-5/1642380687934272:0,0,2;45625/59125704765633792:0,0,3;-125/1642380687934272:0,0,4;1/91243371551904:0,2,3;625/273730114655712:0,3,3;25/91243371551904:0,3,4;33125/43102638774147034368:0,0,0,0;-1/33258208930669008:0,0,0,2;3125/199549253584014048:0,0,0,3;-25/33258208930669008:0,0,0,4;5/9854284127605632:0,0,2,3;625/11086069643556336:0,0,3,3;125/9854284127605632:0,0,3,4;5/6569522751737088:0,2,3,3;-625/6569522751737088:0,3,3,3;125/6569522751737088:0,3,3,4;-3125/436414217588238722976:0,0,0,0,0;-51875/387923748967323309312:0,0,0,0,3;1/140858296647539328:0,0,0,2,3;-79375/43102638774147034368:0,0,0,3,3;25/140858296647539328:0,0,0,3,4;1/29562852382816896:0,0,2,3,3;-625/122799540667085568:0,0,3,3,3;25/29562852382816896:0,0,3,3,4;-1/7390713095704224:0,2,3,3,3;-625/133032835722676032:0,3,3,3,3;-25/7390713095704224:0,3,3,3,4;15625/31421823666353188054272:0,0,0,0,0,3;625/387923748967323309312:0,0,0,0,3,3;-1/4789182086016337152:0,0,0,2,3,3;-625/11409522028450685568:0,0,0,3,3,3;-25/4789182086016337152:0,0,0,3,3,4;-19/4789182086016337152:0,0,2,3,3,3;-625/21551319387073517184:0,0,3,3,3,3;-475/4789182086016337152:0,0,3,3,3,4;-1/532131342890704128:0,2,3,3,3,3;-625/2394591043008168576:0,3,3,3,3,3;-25/532131342890704128:0,3,3,3,3,4;3125/94265470999059564162816:0,0,0,0,0,3,3;4375/10473941222117729351424:0,0,0,0,3,3,3;-1/43102638774147034368:0,0,0,2,3,3,3;3125/1163771246901969927936:0,0,0,3,3,3,3;-25/43102638774147034368:0,0,0,3,3,3,4;-1/4789182086016337152:0,0,2,3,3,3,3;625/43102638774147034368:0,0,3,3,3,3,3;-25/4789182086016337152:0,0,3,3,3,3,4"
compact_certificate_declaration theorem product_9_checked :
    mulShort n_c0_1 n_c1_1=product_9 := by
  decide +kernel
compact_certificate_declaration theorem product_9_value (v : ℕ→ℂ) :
    eval v product_9=eval v n_c0_1*eval v n_c1_1 := by
  rw [←product_9_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_10 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4"
compact_certificate_declaration theorem product_10_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_2 n_c1_0=product_10 := by
  decide +kernel
compact_certificate_declaration theorem product_10_value (v : ℕ→ℂ) :
    eval v product_10=eval v n_c0_2*eval v n_c1_0 := by
  rw [←product_10_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_11 : Poly := rational_polynomial% "0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,2,3,3;0/1:0,0,3,3,3;0/1:0,0,3,3,4;0/1:0,2,3,3,3;0/1:0,3,3,3,3;0/1:0,3,3,3,4"
compact_certificate_declaration theorem partial_sum_11_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_10 [([],(0:ℚ))])=partial_sum_11 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_11_value (v : ℕ→ℂ) :
    eval v partial_sum_11=eval v product_10+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_11_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_12 : Poly := rational_polynomial% "0/1:0;0/1:2;0/1:3;0/1:4;-55625/6569522751737088:0,0;-1/20276304789312:0,2;-625/81105219157248:0,3;-25/20276304789312:0,4;0/1:2,3;0/1:3,3;0/1:3,4;625/20466590111180928:0,0,0;-5/1642380687934272:0,0,2;45625/59125704765633792:0,0,3;-125/1642380687934272:0,0,4;1/91243371551904:0,2,3;625/273730114655712:0,3,3;25/91243371551904:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;33125/43102638774147034368:0,0,0,0;-1/33258208930669008:0,0,0,2;3125/199549253584014048:0,0,0,3;-25/33258208930669008:0,0,0,4;5/9854284127605632:0,0,2,3;625/11086069643556336:0,0,3,3;125/9854284127605632:0,0,3,4;5/6569522751737088:0,2,3,3;-625/6569522751737088:0,3,3,3;125/6569522751737088:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;-3125/436414217588238722976:0,0,0,0,0;-51875/387923748967323309312:0,0,0,0,3;1/140858296647539328:0,0,0,2,3;-79375/43102638774147034368:0,0,0,3,3;25/140858296647539328:0,0,0,3,4;1/29562852382816896:0,0,2,3,3;-625/122799540667085568:0,0,3,3,3;25/29562852382816896:0,0,3,3,4;-1/7390713095704224:0,2,3,3,3;-625/133032835722676032:0,3,3,3,3;-25/7390713095704224:0,3,3,3,4;15625/31421823666353188054272:0,0,0,0,0,3;625/387923748967323309312:0,0,0,0,3,3;-1/4789182086016337152:0,0,0,2,3,3;-625/11409522028450685568:0,0,0,3,3,3;-25/4789182086016337152:0,0,0,3,3,4;-19/4789182086016337152:0,0,2,3,3,3;-625/21551319387073517184:0,0,3,3,3,3;-475/4789182086016337152:0,0,3,3,3,4;-1/532131342890704128:0,2,3,3,3,3;-625/2394591043008168576:0,3,3,3,3,3;-25/532131342890704128:0,3,3,3,3,4;3125/94265470999059564162816:0,0,0,0,0,3,3;4375/10473941222117729351424:0,0,0,0,3,3,3;-1/43102638774147034368:0,0,0,2,3,3,3;3125/1163771246901969927936:0,0,0,3,3,3,3;-25/43102638774147034368:0,0,0,3,3,3,4;-1/4789182086016337152:0,0,2,3,3,3,3;625/43102638774147034368:0,0,3,3,3,3,3;-25/4789182086016337152:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_12_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_9 partial_sum_11)=partial_sum_12 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_12_value (v : ℕ→ℂ) :
    eval v partial_sum_12=eval v product_9+eval v partial_sum_11 := by
  rw [←partial_sum_12_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_13 : Poly := rational_polynomial% "-625/9011691017472:0;0/1:2;0/1:3;0/1:4;-3125/505347903979776:0,0;-7/81105219157248:0,2;625/243315657471744:0,3;-175/81105219157248:0,4;0/1:2,3;0/1:3,3;0/1:3,4;625/16629104465334504:0,0,0;-5/2189840917245696:0,0,2;21875/19708568255211264:0,0,3;-125/2189840917245696:0,0,4;1/56149767108864:0,2,3;25625/6569522751737088:0,3,3;25/56149767108864:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;625/1267724669827853952:0,0,0,0;-1/66516417861338016:0,0,0,2;41875/4789182086016337152:0,0,0,3;-25/66516417861338016:0,0,0,4;41/59125704765633792:0,0,2,3;3125/177377114296901376:0,0,3,3;1025/59125704765633792:0,0,3,4;1/597229341067008:0,2,3,3;-4375/29562852382816896:0,3,3,3;25/597229341067008:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;-625/109103554397059680744:0,0,0,0,0;-11875/96980937241830827328:0,0,0,0,3;29/4789182086016337152:0,0,0,2,3;-3125/1596394028672112384:0,0,0,3,3;725/4789182086016337152:0,0,0,3,4;1/66516417861338016:0,0,2,3,3;-625/108845047409462208:0,0,3,3,3;25/66516417861338016:0,0,3,3,4;-1/4548131135817984:0,2,3,3,3;-625/266065671445352064:0,3,3,3,3;-25/4548131135817984:0,3,3,3,4;4375/7855455916588297013568:0,0,0,0,0,3;3125/1163771246901969927936:0,0,0,0,3,3;-1/3591886564512252864:0,0,0,2,3,3;-4375/96980937241830827328:0,0,0,3,3,3;-25/3591886564512252864:0,0,0,3,3,4;-25/4789182086016337152:0,0,2,3,3,3;625/10775659693536758592:0,0,3,3,3,3;-625/4789182086016337152:0,0,3,3,3,4;-1/133032835722676032:0,2,3,3,3,3;625/4789182086016337152:0,3,3,3,3,3;-25/133032835722676032:0,3,3,3,3,4;3125/94265470999059564162816:0,0,0,0,0,3,3;4375/10473941222117729351424:0,0,0,0,3,3,3;-1/43102638774147034368:0,0,0,2,3,3,3;3125/1163771246901969927936:0,0,0,3,3,3,3;-25/43102638774147034368:0,0,0,3,3,3,4;-1/4789182086016337152:0,0,2,3,3,3,3;625/43102638774147034368:0,0,3,3,3,3,3;-25/4789182086016337152:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_13_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_8 partial_sum_12)=partial_sum_13 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_13_value (v : ℕ→ℂ) :
    eval v partial_sum_13=eval v product_8+eval v partial_sum_12 := by
  rw [←partial_sum_13_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_14 : Poly := rational_polynomial% "0/1:;-625/9011691017472:0;0/1:2;0/1:3;0/1:4;-3125/505347903979776:0,0;-7/81105219157248:0,2;625/243315657471744:0,3;-175/81105219157248:0,4;0/1:2,3;0/1:3,3;0/1:3,4;625/16629104465334504:0,0,0;-5/2189840917245696:0,0,2;21875/19708568255211264:0,0,3;-125/2189840917245696:0,0,4;1/56149767108864:0,2,3;25625/6569522751737088:0,3,3;25/56149767108864:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;625/1267724669827853952:0,0,0,0;-1/66516417861338016:0,0,0,2;41875/4789182086016337152:0,0,0,3;-25/66516417861338016:0,0,0,4;41/59125704765633792:0,0,2,3;3125/177377114296901376:0,0,3,3;1025/59125704765633792:0,0,3,4;1/597229341067008:0,2,3,3;-4375/29562852382816896:0,3,3,3;25/597229341067008:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;-625/109103554397059680744:0,0,0,0,0;-11875/96980937241830827328:0,0,0,0,3;29/4789182086016337152:0,0,0,2,3;-3125/1596394028672112384:0,0,0,3,3;725/4789182086016337152:0,0,0,3,4;1/66516417861338016:0,0,2,3,3;-625/108845047409462208:0,0,3,3,3;25/66516417861338016:0,0,3,3,4;-1/4548131135817984:0,2,3,3,3;-625/266065671445352064:0,3,3,3,3;-25/4548131135817984:0,3,3,3,4;4375/7855455916588297013568:0,0,0,0,0,3;3125/1163771246901969927936:0,0,0,0,3,3;-1/3591886564512252864:0,0,0,2,3,3;-4375/96980937241830827328:0,0,0,3,3,3;-25/3591886564512252864:0,0,0,3,3,4;-25/4789182086016337152:0,0,2,3,3,3;625/10775659693536758592:0,0,3,3,3,3;-625/4789182086016337152:0,0,3,3,3,4;-1/133032835722676032:0,2,3,3,3,3;625/4789182086016337152:0,3,3,3,3,3;-25/133032835722676032:0,3,3,3,3,4;3125/94265470999059564162816:0,0,0,0,0,3,3;4375/10473941222117729351424:0,0,0,0,3,3,3;-1/43102638774147034368:0,0,0,2,3,3,3;3125/1163771246901969927936:0,0,0,3,3,3,3;-25/43102638774147034368:0,0,0,3,3,3,4;-1/4789182086016337152:0,0,2,3,3,3,3;625/43102638774147034368:0,0,3,3,3,3,3;-25/4789182086016337152:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_14_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_13 product_1)=partial_sum_14 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_14_value (v : ℕ→ℂ) :
    eval v partial_sum_14=eval v partial_sum_13+eval v product_1 := by
  rw [←partial_sum_14_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_15 : Poly := rational_polynomial% "-625/9011691017472:0;0/1:2;0/1:3;0/1:4;-3125/505347903979776:0,0;-7/81105219157248:0,2;625/243315657471744:0,3;-175/81105219157248:0,4;0/1:2,3;0/1:3,3;0/1:3,4;625/16629104465334504:0,0,0;-5/2189840917245696:0,0,2;21875/19708568255211264:0,0,3;-125/2189840917245696:0,0,4;1/56149767108864:0,2,3;25625/6569522751737088:0,3,3;25/56149767108864:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;625/1267724669827853952:0,0,0,0;-1/66516417861338016:0,0,0,2;41875/4789182086016337152:0,0,0,3;-25/66516417861338016:0,0,0,4;41/59125704765633792:0,0,2,3;3125/177377114296901376:0,0,3,3;1025/59125704765633792:0,0,3,4;1/597229341067008:0,2,3,3;-4375/29562852382816896:0,3,3,3;25/597229341067008:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;-625/109103554397059680744:0,0,0,0,0;-11875/96980937241830827328:0,0,0,0,3;29/4789182086016337152:0,0,0,2,3;-3125/1596394028672112384:0,0,0,3,3;725/4789182086016337152:0,0,0,3,4;1/66516417861338016:0,0,2,3,3;-625/108845047409462208:0,0,3,3,3;25/66516417861338016:0,0,3,3,4;-1/4548131135817984:0,2,3,3,3;-625/266065671445352064:0,3,3,3,3;-25/4548131135817984:0,3,3,3,4;4375/7855455916588297013568:0,0,0,0,0,3;3125/1163771246901969927936:0,0,0,0,3,3;-1/3591886564512252864:0,0,0,2,3,3;-4375/96980937241830827328:0,0,0,3,3,3;-25/3591886564512252864:0,0,0,3,3,4;-25/4789182086016337152:0,0,2,3,3,3;625/10775659693536758592:0,0,3,3,3,3;-625/4789182086016337152:0,0,3,3,3,4;-1/133032835722676032:0,2,3,3,3,3;625/4789182086016337152:0,3,3,3,3,3;-25/133032835722676032:0,3,3,3,3,4;3125/94265470999059564162816:0,0,0,0,0,3,3;4375/10473941222117729351424:0,0,0,0,3,3,3;-1/43102638774147034368:0,0,0,2,3,3,3;3125/1163771246901969927936:0,0,0,3,3,3,3;-25/43102638774147034368:0,0,0,3,3,3,4;-1/4789182086016337152:0,0,2,3,3,3,3;625/43102638774147034368:0,0,3,3,3,3,3;-25/4789182086016337152:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_15_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_14 product_1)=partial_sum_15 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_15_value (v : ℕ→ℂ) :
    eval v partial_sum_15=eval v partial_sum_14+eval v product_1 := by
  rw [←partial_sum_15_checked, eval_add]
compact_certificate_declaration noncomputable def product_11 : Poly := rational_polynomial% "3125/27035073052416:0;-5625/507658593984256:1;0/1:2;0/1:3;0/1:4;14375/3284761375868544:0,0;3125/13706782037574912:0,1;7/81105219157248:0,2;-4375/182486743103808:0,3;175/81105219157248:0,4;625/190371972744096:1,3;0/1:2,3;625/13517536526208:3,3;0/1:3,4;-625/19708568255211264:0,0,0;625/138781168130445984:0,0,1;5/2189840917245696:0,0,2;-14375/19708568255211264:0,0,3;125/2189840917245696:0,0,4;625/20560173056362368:0,1,3;-1/56149767108864:0,2,3;-625/252673951989888:0,3,3;-25/56149767108864:0,3,4;625/13706782037574912:1,3,3;0/1:2,3,3;-3125/364973486207616:3,3,3;0/1:3,3,4;-625/1657793799005655168:0,0,0,0;1/66516417861338016:0,0,0,2;-625/99774626792007024:0,0,0,3;25/66516417861338016:0,0,0,4;-625/768634161953239296:0,0,1,3;-41/59125704765633792:0,0,2,3;-625/29562852382816896:0,0,3,3;-1025/59125704765633792:0,0,3,4;-4375/370083115014522624:0,1,3,3;-1/597229341067008:0,2,3,3;-25/597229341067008:0,3,3,4;-625/11214639848924928:1,3,3,3;0/1:2,3,3,3;-625/547460229311424:3,3,3,3;0/1:3,3,3,4;625/109103554397059680744:0,0,0,0,0;44375/387923748967323309312:0,0,0,0,3;-29/4789182086016337152:0,0,0,2,3;3125/1795943282256126432:0,0,0,3,3;-725/4789182086016337152:0,0,0,3,4;625/44965098474264498816:0,0,1,3,3;-1/66516417861338016:0,0,2,3,3;625/145126729879282944:0,0,3,3,3;-25/66516417861338016:0,0,3,3,4;625/2498061026348027712:0,1,3,3,3;1/4548131135817984:0,2,3,3,3;625/48375576626427648:0,3,3,3,3;25/4548131135817984:0,3,3,3,4;625/555124672521783936:1,3,3,3,3;3125/29562852382816896:3,3,3,3,3;-4375/7855455916588297013568:0,0,0,0,0,3;-625/193961874483661654656:0,0,0,0,3,3;1/3591886564512252864:0,0,0,2,3,3;11875/387923748967323309312:0,0,0,3,3,3;25/3591886564512252864:0,0,0,3,3,4;625/269790590845586992896:0,0,1,3,3,3;25/4789182086016337152:0,0,2,3,3,3;-4375/43102638774147034368:0,0,3,3,3,3;625/4789182086016337152:0,0,3,3,3,4;625/14988366158088166272:0,1,3,3,3,3;1/133032835722676032:0,2,3,3,3,3;625/598647760752042144:0,3,3,3,3,3;25/133032835722676032:0,3,3,3,3,4;625/3330748035130703616:1,3,3,3,3,3;625/88688557148450688:3,3,3,3,3,3;-3125/94265470999059564162816:0,0,0,0,0,3,3;-4375/10473941222117729351424:0,0,0,0,3,3,3;1/43102638774147034368:0,0,0,2,3,3,3;-3125/1163771246901969927936:0,0,0,3,3,3,3;25/43102638774147034368:0,0,0,3,3,3,4;1/4789182086016337152:0,0,2,3,3,3,3;-625/43102638774147034368:0,0,3,3,3,3,3;25/4789182086016337152:0,0,3,3,3,3,4"
compact_certificate_declaration theorem product_11_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_0 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_1 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_2 n_c7_0) [([],(0:ℚ))])))=product_11 := by
  decide +kernel
compact_certificate_declaration theorem product_11_value (v : ℕ→ℂ) :
    eval v product_11=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_0 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_1 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_2 n_c7_0) [([],(0:ℚ))]))) := by
  rw [←product_11_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_16 : Poly := rational_polynomial% "625/13517536526208:0;-5625/507658593984256:1;-11875/6569522751737088:0,0;3125/13706782037574912:0,1;-15625/729946972415232:0,3;625/190371972744096:1,3;625/13517536526208:3,3;3125/532131342890704128:0,0,0;625/138781168130445984:0,0,1;625/1642380687934272:0,0,3;625/20560173056362368:0,1,3;3125/2189840917245696:0,3,3;625/13706782037574912:1,3,3;-3125/364973486207616:3,3,3;625/5387829846768379296:0,0,0,0;11875/4789182086016337152:0,0,0,3;-625/768634161953239296:0,0,1,3;-625/177377114296901376:0,0,3,3;-4375/370083115014522624:0,1,3,3;-4375/29562852382816896:0,3,3,3;-625/11214639848924928:1,3,3,3;-625/547460229311424:3,3,3,3;-3125/387923748967323309312:0,0,0,0,3;-3125/14367546258049011456:0,0,0,3,3;625/44965098474264498816:0,0,1,3,3;-625/435380189637848832:0,0,3,3,3;625/2498061026348027712:0,1,3,3,3;625/59125704765633792:0,3,3,3,3;625/555124672521783936:1,3,3,3,3;3125/29562852382816896:3,3,3,3,3;-625/1163771246901969927936:0,0,0,0,3,3;-625/43102638774147034368:0,0,0,3,3,3;625/269790590845586992896:0,0,1,3,3,3;-625/14367546258049011456:0,0,3,3,3,3;625/14988366158088166272:0,1,3,3,3,3;625/532131342890704128:0,3,3,3,3,3;625/3330748035130703616:1,3,3,3,3,3;625/88688557148450688:3,3,3,3,3,3"
compact_certificate_declaration theorem partial_sum_16_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_15 product_11)=partial_sum_16 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_16_value (v : ℕ→ℂ) :
    eval v partial_sum_16=eval v partial_sum_15+eval v product_11 := by
  rw [←partial_sum_16_checked, eval_add]
compact_certificate_declaration noncomputable def product_12 : Poly := rational_polynomial% "-625/13517536526208:0;5625/507658593984256:1;0/1:3;11875/6569522751737088:0,0;-3125/13706782037574912:0,1;15625/729946972415232:0,3;-625/190371972744096:1,3;-625/13517536526208:3,3;-3125/532131342890704128:0,0,0;-625/138781168130445984:0,0,1;-625/1642380687934272:0,0,3;-625/20560173056362368:0,1,3;-3125/2189840917245696:0,3,3;-625/13706782037574912:1,3,3;3125/364973486207616:3,3,3;-625/5387829846768379296:0,0,0,0;-11875/4789182086016337152:0,0,0,3;625/768634161953239296:0,0,1,3;625/177377114296901376:0,0,3,3;4375/370083115014522624:0,1,3,3;4375/29562852382816896:0,3,3,3;625/11214639848924928:1,3,3,3;625/547460229311424:3,3,3,3;3125/387923748967323309312:0,0,0,0,3;3125/14367546258049011456:0,0,0,3,3;-625/44965098474264498816:0,0,1,3,3;625/435380189637848832:0,0,3,3,3;-625/2498061026348027712:0,1,3,3,3;-625/59125704765633792:0,3,3,3,3;-625/555124672521783936:1,3,3,3,3;-3125/29562852382816896:3,3,3,3,3;625/1163771246901969927936:0,0,0,0,3,3;625/43102638774147034368:0,0,0,3,3,3;-625/269790590845586992896:0,0,1,3,3,3;625/14367546258049011456:0,0,3,3,3,3;-625/14988366158088166272:0,1,3,3,3,3;-625/532131342890704128:0,3,3,3,3,3;-625/3330748035130703616:1,3,3,3,3,3;-625/88688557148450688:3,3,3,3,3,3"
compact_certificate_declaration theorem product_12_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_0 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_1 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_2 n_c9_0) [([],(0:ℚ))])))=product_12 := by
  decide +kernel
compact_certificate_declaration theorem product_12_value (v : ℕ→ℂ) :
    eval v product_12=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_0 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_1 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_2 n_c9_0) [([],(0:ℚ))]))) := by
  rw [←product_12_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_17 : Poly := rational_polynomial% "0/1:3"
compact_certificate_declaration theorem partial_sum_17_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_16 product_12)=partial_sum_17 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_17_value (v : ℕ→ℂ) :
    eval v partial_sum_17=eval v partial_sum_16+eval v product_12 := by
  rw [←partial_sum_17_checked, eval_add]
compact_certificate_declaration noncomputable def e2 : Poly := partial_sum_17
compact_certificate_declaration theorem checked_2 : checkZero e2=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_2 (y z w a b : ℂ) :
    (certificate y z w a b)[2]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_2 y z w a b))+(((c0_1 y z w a b)*(c1_1 y z w a b))+(((c0_2 y z w a b)*(c1_0 y z w a b))+0)))+((-1)*0))+((-1)*0))+((-1)*(((c6_0 y z w a b)*(c7_2 y z w a b))+(((c6_1 y z w a b)*(c7_1 y z w a b))+(((c6_2 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_2 y z w a b))+(((c8_1 y z w a b)*(c9_1 y z w a b))+(((c8_2 y z w a b)*(c9_0 y z w a b))+0)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e2 checked_2
  simp only [e2, eval_add, eval_mul, eval_scale, eval_pow, product_8_value, product_9_value, product_10_value, partial_sum_11_value, partial_sum_12_value, partial_sum_13_value, product_1_value, partial_sum_14_value, partial_sum_15_value, product_11_value, partial_sum_16_value, product_12_value, partial_sum_17_value, n_c0_0_value y z w a b 0, n_c0_1_value y z w a b 0, n_c0_2_value y z w a b 0, n_c1_0_value y z w a b 0, n_c1_1_value y z w a b 0, n_c1_2_value y z w a b 0, n_c6_0_value y z w a b 0, n_c6_1_value y z w a b 0, n_c6_2_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_0_value y z w a b 0, n_c8_1_value y z w a b 0, n_c8_2_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_2
compact_certificate_declaration noncomputable def product_13 : Poly := rational_polynomial% "-50625/24031176046592:;4375/72093528139776:0;-27/24031176046592:2;9375/24031176046592:3;-675/24031176046592:4;4375/8759363668982784:0,0;1/54070146104832:0,2;4375/486631314943488:0,3;25/54070146104832:0,4;3/12015588023296:2,3;625/16636968032256:3,3;75/12015588023296:3,4;-625/83471583198541824:0,0,0;29/52556182013896704:0,0,2;-83125/473005638125070336:0,0,3;725/52556182013896704:0,0,4;1/176956841797632:0,2,3;-11875/8759363668982784:0,3,3;25/176956841797632:0,3,4;1/49910904096768:2,3,3;-625/182486743103808:3,3,3;25/49910904096768:3,3,4;3125/344821110193176274944:0,0,0,0;1/532131342890704128:0,0,0,2;-625/2947188976010053632:0,0,0,3;25/532131342890704128:0,0,0,4;-1/39417136510422528:0,0,2,3;-625/1064262685781408256:0,0,3,3;-25/39417136510422528:0,0,3,4;-35/52556182013896704:0,2,3,3;625/36385049086543872:0,3,3,3;-875/52556182013896704:0,3,3,4;-7/1946525259773952:2,3,3,3;625/4777834728536064:3,3,3,3;-175/1946525259773952:3,3,3,4;625/3491313740705909783808:0,0,0,0,0;625/387923748967323309312:0,0,0,0,3;-5/38313456688130697216:0,0,0,2,3;625/114940370064392091648:0,0,0,3,3;-125/38313456688130697216:0,0,0,3,4;-7/2128525371562816512:0,0,2,3,3;4375/12771152229376899072:0,0,3,3,3;-175/2128525371562816512:0,0,3,3,4;-1/36385049086543872:0,2,3,3,3;15625/4257050743125633024:0,3,3,3,3;-25/36385049086543872:0,3,3,3,4;-1/13139045503474176:2,3,3,3,3;4375/473005638125070336:3,3,3,3,3;-25/13139045503474176:3,3,3,3,4;625/83791529776941834811392:0,0,0,0,0,3;625/9310169975215759423488:0,0,0,0,3,3;-1/114940370064392091648:0,0,0,2,3,3;-25/114940370064392091648:0,0,0,3,3,4;-1/12771152229376899072:0,0,2,3,3,3;-25/12771152229376899072:0,0,3,3,3,4;1/1419016914375211008:0,2,3,3,3,3;-625/12771152229376899072:0,3,3,3,3,3;25/1419016914375211008:0,3,3,3,3,4;1/157668546041690112:2,3,3,3,3,3;-625/1419016914375211008:3,3,3,3,3,3;25/157668546041690112:3,3,3,3,3,4"
compact_certificate_declaration theorem product_13_checked :
    mulShort n_c0_0 n_c1_3=product_13 := by
  decide +kernel
compact_certificate_declaration theorem product_13_value (v : ℕ→ℂ) :
    eval v product_13=eval v n_c0_0*eval v n_c1_3 := by
  rw [←product_13_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_14 : Poly := rational_polynomial% "-55625/26278091006948352:0,0;-1/81105219157248:0,2;-625/324420876628992:0,3;-25/81105219157248:0,4;625/81866360444723712:0,0,0;-5/6569522751737088:0,0,2;-625/14781426191408448:0,0,3;-125/6569522751737088:0,0,4;1/729946972415232:0,2,3;3125/8759363668982784:0,3,3;25/729946972415232:0,3,4;33125/172410555096588137472:0,0,0,0;-1/133032835722676032:0,0,0,2;45625/9578364172032674304:0,0,0,3;-25/133032835722676032:0,0,0,4;5/118251409531267584:0,0,2,3;625/66516417861338016:0,0,3,3;125/118251409531267584:0,0,3,4;1/2919787889660928:0,2,3,3;625/39417136510422528:0,3,3,3;25/2919787889660928:0,3,3,4;-3125/1745656870352954891904:0,0,0,0,0;-3125/258615832644882206208:0,0,0,0,3;1/1064262685781408256:0,0,0,2,3;11875/172410555096588137472:0,0,0,3,3;25/1064262685781408256:0,0,0,3,4;7/532131342890704128:0,0,2,3,3;-4375/19156728344065348608:0,0,3,3,3;175/532131342890704128:0,0,3,3,4;1/236502819062535168:0,2,3,3,3;625/1064262685781408256:0,3,3,3,3;25/236502819062535168:0,3,3,3,4;-3125/41895764888470917405696:0,0,0,0,0,3;-4375/4655084987607879711744:0,0,0,0,3,3;1/19156728344065348608:0,0,0,2,3,3;-3125/517231665289764412416:0,0,0,3,3,3;25/19156728344065348608:0,0,0,3,3,4;1/2128525371562816512:0,0,2,3,3,3;-625/19156728344065348608:0,0,3,3,3,3;25/2128525371562816512:0,0,3,3,3,4"
compact_certificate_declaration theorem product_14_checked :
    mulShort n_c0_1 n_c1_2=product_14 := by
  decide +kernel
compact_certificate_declaration theorem product_14_value (v : ℕ→ℂ) :
    eval v product_14=eval v n_c0_1*eval v n_c1_2 := by
  rw [←product_14_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_15 : Poly := rational_polynomial% "-625/12015588023296:0;51875/26278091006948352:0,0;-7/243315657471744:0,2;3125/2189840917245696:0,3;-175/243315657471744:0,4;-66875/3192788057344224768:0,0,0;-1/1516043711939328:0,0,2;-38125/177377114296901376:0,0,3;-25/1516043711939328:0,0,4;1/547460229311424:0,2,3;51875/78834273020845056:0,3,3;25/547460229311424:0,3,4;-19375/129307916322441103104:0,0,0,0;-1/266065671445352064:0,0,0,2;-14375/4789182086016337152:0,0,0,3;-25/266065671445352064:0,0,0,4;-1/54577573629815808:0,0,2,3;-3125/354754228593802752:0,0,3,3;-25/54577573629815808:0,0,3,4;43/78834273020845056:0,2,3,3;-25625/709508457187605504:0,3,3,3;1075/78834273020845056:0,3,3,4;625/193961874483661654656:0,0,0,0,0;49375/1163771246901969927936:0,0,0,0,3;-1/1741520758551395328:0,0,0,2,3;263125/517231665289764412416:0,0,0,3,3;-25/1741520758551395328:0,0,0,3,4;5/6385576114688449536:0,0,2,3,3;71875/57470185032196045824:0,0,3,3,3;125/6385576114688449536:0,0,3,3,4;-1/44344278574225344:0,2,3,3,3;625/1596394028672112384:0,3,3,3,3;-25/44344278574225344:0,3,3,3,4;-3125/13965254962823639135232:0,0,0,0,0,3;-19375/13965254962823639135232:0,0,0,0,3,3;1/13262350392045241344:0,0,0,2,3,3;11875/775847497934646618624:0,0,0,3,3,3;25/13262350392045241344:0,0,0,3,3,4;7/9578364172032674304:0,0,2,3,3,3;-625/172410555096588137472:0,0,3,3,3,3;175/9578364172032674304:0,0,3,3,3,4;-5/2128525371562816512:0,2,3,3,3,3;3125/19156728344065348608:0,3,3,3,3,3;-125/2128525371562816512:0,3,3,3,3,4;-625/41895764888470917405696:0,0,0,0,0,3,3;-625/3808705898951901582336:0,0,0,0,3,3,3;1/258615832644882206208:0,0,0,2,3,3,3;-3125/4655084987607879711744:0,0,0,3,3,3,3;25/258615832644882206208:0,0,0,3,3,3,4;1/28735092516098022912:0,0,2,3,3,3,3;-625/172410555096588137472:0,0,3,3,3,3,3;25/28735092516098022912:0,0,3,3,3,3,4"
compact_certificate_declaration theorem product_15_checked :
    mulShort n_c0_2 n_c1_1=product_15 := by
  decide +kernel
compact_certificate_declaration theorem product_15_value (v : ℕ→ℂ) :
    eval v product_15=eval v n_c0_2*eval v n_c1_1 := by
  rw [←product_15_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_16 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,3,3,3"
compact_certificate_declaration theorem product_16_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_3 n_c1_0=product_16 := by
  decide +kernel
compact_certificate_declaration theorem product_16_value (v : ℕ→ℂ) :
    eval v product_16=eval v n_c0_3*eval v n_c1_0 := by
  rw [←product_16_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_18 : Poly := rational_polynomial% "0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,2;0/1:0,0,3;0/1:0,0,4;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,2,3;0/1:0,0,3,3;0/1:0,0,3,4;0/1:0,2,3,3;0/1:0,3,3,3;0/1:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,3,3,3"
compact_certificate_declaration theorem partial_sum_18_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_16 [([],(0:ℚ))])=partial_sum_18 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_18_value (v : ℕ→ℂ) :
    eval v partial_sum_18=eval v product_16+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_18_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_19 : Poly := rational_polynomial% "-625/12015588023296:0;0/1:2;0/1:3;0/1:4;51875/26278091006948352:0,0;-7/243315657471744:0,2;3125/2189840917245696:0,3;-175/243315657471744:0,4;0/1:2,3;0/1:3,3;0/1:3,4;-66875/3192788057344224768:0,0,0;-1/1516043711939328:0,0,2;-38125/177377114296901376:0,0,3;-25/1516043711939328:0,0,4;1/547460229311424:0,2,3;51875/78834273020845056:0,3,3;25/547460229311424:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;-19375/129307916322441103104:0,0,0,0;-1/266065671445352064:0,0,0,2;-14375/4789182086016337152:0,0,0,3;-25/266065671445352064:0,0,0,4;-1/54577573629815808:0,0,2,3;-3125/354754228593802752:0,0,3,3;-25/54577573629815808:0,0,3,4;43/78834273020845056:0,2,3,3;-25625/709508457187605504:0,3,3,3;1075/78834273020845056:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;625/193961874483661654656:0,0,0,0,0;49375/1163771246901969927936:0,0,0,0,3;-1/1741520758551395328:0,0,0,2,3;263125/517231665289764412416:0,0,0,3,3;-25/1741520758551395328:0,0,0,3,4;5/6385576114688449536:0,0,2,3,3;71875/57470185032196045824:0,0,3,3,3;125/6385576114688449536:0,0,3,3,4;-1/44344278574225344:0,2,3,3,3;625/1596394028672112384:0,3,3,3,3;-25/44344278574225344:0,3,3,3,4;-3125/13965254962823639135232:0,0,0,0,0,3;-19375/13965254962823639135232:0,0,0,0,3,3;1/13262350392045241344:0,0,0,2,3,3;11875/775847497934646618624:0,0,0,3,3,3;25/13262350392045241344:0,0,0,3,3,4;7/9578364172032674304:0,0,2,3,3,3;-625/172410555096588137472:0,0,3,3,3,3;175/9578364172032674304:0,0,3,3,3,4;-5/2128525371562816512:0,2,3,3,3,3;3125/19156728344065348608:0,3,3,3,3,3;-125/2128525371562816512:0,3,3,3,3,4;-625/41895764888470917405696:0,0,0,0,0,3,3;-625/3808705898951901582336:0,0,0,0,3,3,3;1/258615832644882206208:0,0,0,2,3,3,3;-3125/4655084987607879711744:0,0,0,3,3,3,3;25/258615832644882206208:0,0,0,3,3,3,4;1/28735092516098022912:0,0,2,3,3,3,3;-625/172410555096588137472:0,0,3,3,3,3,3;25/28735092516098022912:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_19_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_15 partial_sum_18)=partial_sum_19 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_19_value (v : ℕ→ℂ) :
    eval v partial_sum_19=eval v product_15+eval v partial_sum_18 := by
  rw [←partial_sum_19_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_20 : Poly := rational_polynomial% "-625/12015588023296:0;0/1:2;0/1:3;0/1:4;-625/4379681834491392:0,0;-5/121657828735872:0,2;-4375/8759363668982784:0,3;-125/121657828735872:0,4;0/1:2,3;0/1:3,3;0/1:3,4;-625/46952765549179776:0,0,0;-7/4927142063802816:0,0,2;-45625/177377114296901376:0,0,3;-175/4927142063802816:0,0,4;7/2189840917245696:0,2,3;625/615892757975352:0,3,3;175/2189840917245696:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;21875/517231665289764412416:0,0,0,0;-1/88688557148450688:0,0,0,2;625/354754228593802752:0,0,0,3;-25/88688557148450688:0,0,0,4;1/41735791599270912:0,0,2,3;625/1064262685781408256:0,0,3,3;25/41735791599270912:0,0,3,4;35/39417136510422528:0,2,3,3;-14375/709508457187605504:0,3,3,3;875/39417136510422528:0,3,3,4;0/1:2,3,3,3;0/1:3,3,3,3;0/1:3,3,3,4;625/436414217588238722976:0,0,0,0,0;70625/2327542493803939855872:0,0,0,0,3;7/19156728344065348608:0,0,0,2,3;149375/258615832644882206208:0,0,0,3,3;175/19156728344065348608:0,0,0,3,4;89/6385576114688449536:0,0,2,3,3;29375/28735092516098022912:0,0,3,3,3;2225/6385576114688449536:0,0,3,3,4;-1/54577573629815808:0,2,3,3,3;3125/3192788057344224768:0,3,3,3,3;-25/54577573629815808:0,3,3,3,4;-3125/10473941222117729351424:0,0,0,0,0,3;-625/268562595438916137216:0,0,0,0,3,3;1/7836843413481278976:0,0,0,2,3,3;14375/1551694995869293237248:0,0,0,3,3,3;25/7836843413481278976:0,0,0,3,3,4;23/19156728344065348608:0,0,2,3,3,3;-3125/86205277548294068736:0,0,3,3,3,3;575/19156728344065348608:0,0,3,3,3,4;-5/2128525371562816512:0,2,3,3,3,3;3125/19156728344065348608:0,3,3,3,3,3;-125/2128525371562816512:0,3,3,3,3,4;-625/41895764888470917405696:0,0,0,0,0,3,3;-625/3808705898951901582336:0,0,0,0,3,3,3;1/258615832644882206208:0,0,0,2,3,3,3;-3125/4655084987607879711744:0,0,0,3,3,3,3;25/258615832644882206208:0,0,0,3,3,3,4;1/28735092516098022912:0,0,2,3,3,3,3;-625/172410555096588137472:0,0,3,3,3,3,3;25/28735092516098022912:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_20_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_14 partial_sum_19)=partial_sum_20 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_20_value (v : ℕ→ℂ) :
    eval v partial_sum_20=eval v product_14+eval v partial_sum_19 := by
  rw [←partial_sum_20_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_21 : Poly := rational_polynomial% "-50625/24031176046592:;625/72093528139776:0;-27/24031176046592:2;9375/24031176046592:3;-675/24031176046592:4;3125/8759363668982784:0,0;-1/44239210449408:0,2;4375/515256686410752:0,3;-25/44239210449408:0,4;3/12015588023296:2,3;625/16636968032256:3,3;75/12015588023296:3,4;-15625/751244248786876416:0,0,0;-137/157668546041690112:0,0,2;-614375/1419016914375211008:0,0,3;-3425/157668546041690112:0,0,4;155/17518727337965568:0,2,3;-26875/78834273020845056:0,3,3;3875/17518727337965568:0,3,4;1/49910904096768:2,3,3;-625/182486743103808:3,3,3;25/49910904096768:3,3,4;3125/60850784151736989696:0,0,0,0;-5/532131342890704128:0,0,0,2;59375/38313456688130697216:0,0,0,3;-125/532131342890704128:0,0,0,4;-1/709508457187605504:0,0,2,3;-25/709508457187605504:0,0,3,4;35/157668546041690112:0,2,3,3;-4375/1419016914375211008:0,3,3,3;875/157668546041690112:0,3,3,4;-7/1946525259773952:2,3,3,3;625/4777834728536064:3,3,3,3;-175/1946525259773952:3,3,3,4;625/387923748967323309312:0,0,0,0,0;4375/136914264341408226816:0,0,0,0,3;1/4257050743125633024:0,0,0,2,3;603125/1034463330579528824832:0,0,0,3,3;25/4257050743125633024:0,0,0,3,4;1/93905531098359552:0,0,2,3,3;156875/114940370064392091648:0,0,3,3,3;25/93905531098359552:0,0,3,3,4;-5/109155147259631616:0,2,3,3,3;59375/12771152229376899072:0,3,3,3,3;-125/109155147259631616:0,3,3,3,4;-1/13139045503474176:2,3,3,3,3;4375/473005638125070336:3,3,3,3,3;-25/13139045503474176:3,3,3,3,4;-625/2148500763511329097728:0,0,0,0,0,3;-63125/27930509925647278270464:0,0,0,0,3,3;41/344821110193176274944:0,0,0,2,3,3;14375/1551694995869293237248:0,0,0,3,3,3;1025/344821110193176274944:0,0,0,3,3,4;43/38313456688130697216:0,0,2,3,3,3;-3125/86205277548294068736:0,0,3,3,3,3;1075/38313456688130697216:0,0,3,3,3,4;-7/4257050743125633024:0,2,3,3,3,3;4375/38313456688130697216:0,3,3,3,3,3;-175/4257050743125633024:0,3,3,3,3,4;1/157668546041690112:2,3,3,3,3,3;-625/1419016914375211008:3,3,3,3,3,3;25/157668546041690112:3,3,3,3,3,4;-625/41895764888470917405696:0,0,0,0,0,3,3;-625/3808705898951901582336:0,0,0,0,3,3,3;1/258615832644882206208:0,0,0,2,3,3,3;-3125/4655084987607879711744:0,0,0,3,3,3,3;25/258615832644882206208:0,0,0,3,3,3,4;1/28735092516098022912:0,0,2,3,3,3,3;-625/172410555096588137472:0,0,3,3,3,3,3;25/28735092516098022912:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_21_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_13 partial_sum_20)=partial_sum_21 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_21_value (v : ℕ→ℂ) :
    eval v partial_sum_21=eval v product_13+eval v partial_sum_20 := by
  rw [←partial_sum_21_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_22 : Poly := rational_polynomial% "-50625/24031176046592:;625/72093528139776:0;-27/24031176046592:2;9375/24031176046592:3;-675/24031176046592:4;3125/8759363668982784:0,0;-1/44239210449408:0,2;4375/515256686410752:0,3;-25/44239210449408:0,4;3/12015588023296:2,3;625/16636968032256:3,3;75/12015588023296:3,4;-15625/751244248786876416:0,0,0;-137/157668546041690112:0,0,2;-614375/1419016914375211008:0,0,3;-3425/157668546041690112:0,0,4;155/17518727337965568:0,2,3;-26875/78834273020845056:0,3,3;3875/17518727337965568:0,3,4;1/49910904096768:2,3,3;-625/182486743103808:3,3,3;25/49910904096768:3,3,4;3125/60850784151736989696:0,0,0,0;-5/532131342890704128:0,0,0,2;59375/38313456688130697216:0,0,0,3;-125/532131342890704128:0,0,0,4;-1/709508457187605504:0,0,2,3;-25/709508457187605504:0,0,3,4;35/157668546041690112:0,2,3,3;-4375/1419016914375211008:0,3,3,3;875/157668546041690112:0,3,3,4;-7/1946525259773952:2,3,3,3;625/4777834728536064:3,3,3,3;-175/1946525259773952:3,3,3,4;625/387923748967323309312:0,0,0,0,0;4375/136914264341408226816:0,0,0,0,3;1/4257050743125633024:0,0,0,2,3;603125/1034463330579528824832:0,0,0,3,3;25/4257050743125633024:0,0,0,3,4;1/93905531098359552:0,0,2,3,3;156875/114940370064392091648:0,0,3,3,3;25/93905531098359552:0,0,3,3,4;-5/109155147259631616:0,2,3,3,3;59375/12771152229376899072:0,3,3,3,3;-125/109155147259631616:0,3,3,3,4;-1/13139045503474176:2,3,3,3,3;4375/473005638125070336:3,3,3,3,3;-25/13139045503474176:3,3,3,3,4;-625/2148500763511329097728:0,0,0,0,0,3;-63125/27930509925647278270464:0,0,0,0,3,3;41/344821110193176274944:0,0,0,2,3,3;14375/1551694995869293237248:0,0,0,3,3,3;1025/344821110193176274944:0,0,0,3,3,4;43/38313456688130697216:0,0,2,3,3,3;-3125/86205277548294068736:0,0,3,3,3,3;1075/38313456688130697216:0,0,3,3,3,4;-7/4257050743125633024:0,2,3,3,3,3;4375/38313456688130697216:0,3,3,3,3,3;-175/4257050743125633024:0,3,3,3,3,4;1/157668546041690112:2,3,3,3,3,3;-625/1419016914375211008:3,3,3,3,3,3;25/157668546041690112:3,3,3,3,3,4;-625/41895764888470917405696:0,0,0,0,0,3,3;-625/3808705898951901582336:0,0,0,0,3,3,3;1/258615832644882206208:0,0,0,2,3,3,3;-3125/4655084987607879711744:0,0,0,3,3,3,3;25/258615832644882206208:0,0,0,3,3,3,4;1/28735092516098022912:0,0,2,3,3,3,3;-625/172410555096588137472:0,0,3,3,3,3,3;25/28735092516098022912:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_22_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_21 product_1)=partial_sum_22 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_22_value (v : ℕ→ℂ) :
    eval v partial_sum_22=eval v partial_sum_21+eval v product_1 := by
  rw [←partial_sum_22_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_23 : Poly := rational_polynomial% "-50625/24031176046592:;625/72093528139776:0;-27/24031176046592:2;9375/24031176046592:3;-675/24031176046592:4;3125/8759363668982784:0,0;-1/44239210449408:0,2;4375/515256686410752:0,3;-25/44239210449408:0,4;3/12015588023296:2,3;625/16636968032256:3,3;75/12015588023296:3,4;-15625/751244248786876416:0,0,0;-137/157668546041690112:0,0,2;-614375/1419016914375211008:0,0,3;-3425/157668546041690112:0,0,4;155/17518727337965568:0,2,3;-26875/78834273020845056:0,3,3;3875/17518727337965568:0,3,4;1/49910904096768:2,3,3;-625/182486743103808:3,3,3;25/49910904096768:3,3,4;3125/60850784151736989696:0,0,0,0;-5/532131342890704128:0,0,0,2;59375/38313456688130697216:0,0,0,3;-125/532131342890704128:0,0,0,4;-1/709508457187605504:0,0,2,3;-25/709508457187605504:0,0,3,4;35/157668546041690112:0,2,3,3;-4375/1419016914375211008:0,3,3,3;875/157668546041690112:0,3,3,4;-7/1946525259773952:2,3,3,3;625/4777834728536064:3,3,3,3;-175/1946525259773952:3,3,3,4;625/387923748967323309312:0,0,0,0,0;4375/136914264341408226816:0,0,0,0,3;1/4257050743125633024:0,0,0,2,3;603125/1034463330579528824832:0,0,0,3,3;25/4257050743125633024:0,0,0,3,4;1/93905531098359552:0,0,2,3,3;156875/114940370064392091648:0,0,3,3,3;25/93905531098359552:0,0,3,3,4;-5/109155147259631616:0,2,3,3,3;59375/12771152229376899072:0,3,3,3,3;-125/109155147259631616:0,3,3,3,4;-1/13139045503474176:2,3,3,3,3;4375/473005638125070336:3,3,3,3,3;-25/13139045503474176:3,3,3,3,4;-625/2148500763511329097728:0,0,0,0,0,3;-63125/27930509925647278270464:0,0,0,0,3,3;41/344821110193176274944:0,0,0,2,3,3;14375/1551694995869293237248:0,0,0,3,3,3;1025/344821110193176274944:0,0,0,3,3,4;43/38313456688130697216:0,0,2,3,3,3;-3125/86205277548294068736:0,0,3,3,3,3;1075/38313456688130697216:0,0,3,3,3,4;-7/4257050743125633024:0,2,3,3,3,3;4375/38313456688130697216:0,3,3,3,3,3;-175/4257050743125633024:0,3,3,3,3,4;1/157668546041690112:2,3,3,3,3,3;-625/1419016914375211008:3,3,3,3,3,3;25/157668546041690112:3,3,3,3,3,4;-625/41895764888470917405696:0,0,0,0,0,3,3;-625/3808705898951901582336:0,0,0,0,3,3,3;1/258615832644882206208:0,0,0,2,3,3,3;-3125/4655084987607879711744:0,0,0,3,3,3,3;25/258615832644882206208:0,0,0,3,3,3,4;1/28735092516098022912:0,0,2,3,3,3,3;-625/172410555096588137472:0,0,3,3,3,3,3;25/28735092516098022912:0,0,3,3,3,3,4"
compact_certificate_declaration theorem partial_sum_23_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_22 product_1)=partial_sum_23 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_23_value (v : ℕ→ℂ) :
    eval v partial_sum_23=eval v partial_sum_22+eval v product_1 := by
  rw [←partial_sum_23_checked, eval_add]
compact_certificate_declaration noncomputable def product_17 : Poly := rational_polynomial% "16875/24031176046592:;26875/648841753257984:0;-1875/369206250170368:1;27/24031176046592:2;-1875/24031176046592:3;675/24031176046592:4;3125/3091540118464512:0,0;-11875/54827128150299648:0,1;1/44239210449408:0,2;-139375/17518727337965568:0,3;25/44239210449408:0,4;625/507658593984256:1,3;-3/12015588023296:2,3;-625/72093528139776:3,3;-75/12015588023296:3,4;66875/12771152229376899072:0,0,0;-11875/8881994760348542976:0,0,1;137/157668546041690112:0,0,2;625/44344278574225344:0,0,3;3425/157668546041690112:0,0,4;44375/986888306705393664:0,1,3;-155/17518727337965568:0,2,3;85625/157668546041690112:0,3,3;-3875/17518727337965568:0,3,4;625/9968568754599936:1,3,3;-1/49910904096768:2,3,3;-625/324420876628992:3,3,3;-25/49910904096768:3,3,4;-4375/30425392075868494848:0,0,0,0;625/89930196948528997632:0,0,0,1;5/532131342890704128:0,0,0,2;-6875/3483041517102790656:0,0,0,3;125/532131342890704128:0,0,0,4;625/1211181103683892224:0,0,1,3;1/709508457187605504:0,0,2,3;33125/1419016914375211008:0,0,3,3;25/709508457187605504:0,0,3,4;4375/2960664920116180992:0,1,3,3;-35/157668546041690112:0,2,3,3;68125/1419016914375211008:0,3,3,3;-875/157668546041690112:0,3,3,4;-625/36551418766866432:1,3,3,3;7/1946525259773952:2,3,3,3;-14375/52556182013896704:3,3,3,3;175/1946525259773952:3,3,3,4;-625/436414217588238722976:0,0,0,0,0;-14375/716166921170443032576:0,0,0,0,3;-3125/6474974180294087829504:0,0,0,1,3;-1/4257050743125633024:0,0,0,2,3;-15625/39787051176135724032:0,0,0,3,3;-25/4257050743125633024:0,0,0,3,4;-625/27670829830316614656:0,0,1,3,3;-1/93905531098359552:0,0,2,3,3;-25625/28735092516098022912:0,0,3,3,3;-25/93905531098359552:0,0,3,3,4;-625/2049691098541971456:0,1,3,3,3;5/109155147259631616:0,2,3,3,3;-26875/1596394028672112384:0,3,3,3,3;125/109155147259631616:0,3,3,3,4;1/13139045503474176:2,3,3,3,3;4375/473005638125070336:3,3,3,3,3;25/13139045503474176:3,3,3,3,4;3125/10473941222117729351424:0,0,0,0,0,3;81875/27930509925647278270464:0,0,0,0,3,3;-625/19424922540882263488512:0,0,0,1,3,3;-41/344821110193176274944:0,0,0,2,3,3;-625/775847497934646618624:0,0,0,3,3,3;-1025/344821110193176274944:0,0,0,3,3,4;-4375/2158324726764695943168:0,0,1,3,3,3;-43/38313456688130697216:0,0,2,3,3,3;-3125/172410555096588137472:0,0,3,3,3,3;-1075/38313456688130697216:0,0,3,3,3,4;-3125/239813858529410660352:0,1,3,3,3,3;7/4257050743125633024:0,2,3,3,3,3;-625/736797244002513408:0,3,3,3,3,3;175/4257050743125633024:0,3,3,3,3,4;625/26645984281045628928:1,3,3,3,3,3;-1/157668546041690112:2,3,3,3,3,3;625/1419016914375211008:3,3,3,3,3,3;-25/157668546041690112:3,3,3,3,3,4;625/41895764888470917405696:0,0,0,0,0,3,3;625/3808705898951901582336:0,0,0,0,3,3,3;-1/258615832644882206208:0,0,0,2,3,3,3;3125/4655084987607879711744:0,0,0,3,3,3,3;-25/258615832644882206208:0,0,0,3,3,3,4;-1/28735092516098022912:0,0,2,3,3,3,3;625/172410555096588137472:0,0,3,3,3,3,3;-25/28735092516098022912:0,0,3,3,3,3,4"
compact_certificate_declaration theorem product_17_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_1 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_2 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_3 n_c7_0) [([],(0:ℚ))])))=product_17 := by
  decide +kernel
compact_certificate_declaration theorem product_17_value (v : ℕ→ℂ) :
    eval v product_17=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_1 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_2 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_3 n_c7_0) [([],(0:ℚ))]))) := by
  rw [←product_17_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_24 : Poly := rational_polynomial% "-16875/12015588023296:;625/12477726024192:0;-1875/369206250170368:1;1875/6007794011648:3;71875/52556182013896704:0,0;-11875/54827128150299648:0,1;3125/5839575779321856:0,3;625/507658593984256:1,3;3125/108140292209664:3,3;-33125/2128525371562816512:0,0,0;-11875/8881994760348542976:0,0,1;-198125/473005638125070336:0,0,3;44375/986888306705393664:0,1,3;625/3091540118464512:0,3,3;625/9968568754599936:1,3,3;-15625/2919787889660928:3,3,3;-625/6761198239081887744:0,0,0,0;625/89930196948528997632:0,0,0,1;-625/1473594488005026816:0,0,0,3;625/1211181103683892224:0,0,1,3;33125/1419016914375211008:0,0,3,3;4375/2960664920116180992:0,1,3,3;625/13911930533090304:0,3,3,3;-625/36551418766866432:1,3,3,3;-625/4379681834491392:3,3,3,3;625/3491313740705909783808:0,0,0,0,0;36875/3103389991738586474496:0,0,0,0,3;-3125/6474974180294087829504:0,0,0,1,3;21875/114940370064392091648:0,0,0,3,3;-625/27670829830316614656:0,0,1,3,3;18125/38313456688130697216:0,0,3,3,3;-625/2049691098541971456:0,1,3,3,3;-51875/4257050743125633024:0,3,3,3,3;4375/236502819062535168:3,3,3,3,3;625/83791529776941834811392:0,0,0,0,0,3;3125/4655084987607879711744:0,0,0,0,3,3;-625/19424922540882263488512:0,0,0,1,3,3;4375/517231665289764412416:0,0,0,3,3,3;-4375/2158324726764695943168:0,0,1,3,3,3;-3125/57470185032196045824:0,0,3,3,3,3;-3125/239813858529410660352:0,1,3,3,3,3;-3125/4257050743125633024:0,3,3,3,3,3;625/26645984281045628928:1,3,3,3,3,3"
compact_certificate_declaration theorem partial_sum_24_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_23 product_17)=partial_sum_24 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_24_value (v : ℕ→ℂ) :
    eval v partial_sum_24=eval v partial_sum_23+eval v product_17 := by
  rw [←partial_sum_24_checked, eval_add]
compact_certificate_declaration noncomputable def product_18 : Poly := rational_polynomial% "16875/12015588023296:;-625/12477726024192:0;1875/369206250170368:1;-1875/6007794011648:3;-71875/52556182013896704:0,0;11875/54827128150299648:0,1;-3125/5839575779321856:0,3;-625/507658593984256:1,3;-3125/108140292209664:3,3;33125/2128525371562816512:0,0,0;11875/8881994760348542976:0,0,1;198125/473005638125070336:0,0,3;-44375/986888306705393664:0,1,3;-625/3091540118464512:0,3,3;-625/9968568754599936:1,3,3;15625/2919787889660928:3,3,3;625/6761198239081887744:0,0,0,0;-625/89930196948528997632:0,0,0,1;625/1473594488005026816:0,0,0,3;-625/1211181103683892224:0,0,1,3;-33125/1419016914375211008:0,0,3,3;-4375/2960664920116180992:0,1,3,3;-625/13911930533090304:0,3,3,3;625/36551418766866432:1,3,3,3;625/4379681834491392:3,3,3,3;-625/3491313740705909783808:0,0,0,0,0;-36875/3103389991738586474496:0,0,0,0,3;3125/6474974180294087829504:0,0,0,1,3;-21875/114940370064392091648:0,0,0,3,3;625/27670829830316614656:0,0,1,3,3;-18125/38313456688130697216:0,0,3,3,3;625/2049691098541971456:0,1,3,3,3;51875/4257050743125633024:0,3,3,3,3;-4375/236502819062535168:3,3,3,3,3;-625/83791529776941834811392:0,0,0,0,0,3;-3125/4655084987607879711744:0,0,0,0,3,3;625/19424922540882263488512:0,0,0,1,3,3;-4375/517231665289764412416:0,0,0,3,3,3;4375/2158324726764695943168:0,0,1,3,3,3;3125/57470185032196045824:0,0,3,3,3,3;3125/239813858529410660352:0,1,3,3,3,3;3125/4257050743125633024:0,3,3,3,3,3;-625/26645984281045628928:1,3,3,3,3,3"
compact_certificate_declaration theorem product_18_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_0 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_1 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_2 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_3 n_c9_0) [([],(0:ℚ))]))))=product_18 := by
  decide +kernel
compact_certificate_declaration theorem product_18_value (v : ℕ→ℂ) :
    eval v product_18=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_0 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_1 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_2 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_3 n_c9_0) [([],(0:ℚ))])))) := by
  rw [←product_18_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_25 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_25_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_24 product_18)=partial_sum_25 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_25_value (v : ℕ→ℂ) :
    eval v partial_sum_25=eval v partial_sum_24+eval v product_18 := by
  rw [←partial_sum_25_checked, eval_add]
compact_certificate_declaration noncomputable def e3 : Poly := partial_sum_25
compact_certificate_declaration theorem checked_3 : checkZero e3=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_3 (y z w a b : ℂ) :
    (certificate y z w a b)[3]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_3 y z w a b))+(((c0_1 y z w a b)*(c1_2 y z w a b))+(((c0_2 y z w a b)*(c1_1 y z w a b))+(((c0_3 y z w a b)*(c1_0 y z w a b))+0))))+((-1)*0))+((-1)*0))+((-1)*(((c6_1 y z w a b)*(c7_2 y z w a b))+(((c6_2 y z w a b)*(c7_1 y z w a b))+(((c6_3 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_0 y z w a b)*(c9_3 y z w a b))+(((c8_1 y z w a b)*(c9_2 y z w a b))+(((c8_2 y z w a b)*(c9_1 y z w a b))+(((c8_3 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e3 checked_3
  simp only [e3, eval_add, eval_mul, eval_scale, eval_pow, product_13_value, product_14_value, product_15_value, product_16_value, partial_sum_18_value, partial_sum_19_value, partial_sum_20_value, partial_sum_21_value, product_1_value, partial_sum_22_value, partial_sum_23_value, product_17_value, partial_sum_24_value, product_18_value, partial_sum_25_value, n_c0_0_value y z w a b 0, n_c0_1_value y z w a b 0, n_c0_2_value y z w a b 0, n_c0_3_value y z w a b 0, n_c1_0_value y z w a b 0, n_c1_1_value y z w a b 0, n_c1_2_value y z w a b 0, n_c1_3_value y z w a b 0, n_c6_1_value y z w a b 0, n_c6_2_value y z w a b 0, n_c6_3_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_0_value y z w a b 0, n_c8_1_value y z w a b 0, n_c8_2_value y z w a b 0, n_c8_3_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_3
compact_certificate_declaration noncomputable def product_19 : Poly := rational_polynomial% "-16875/48062352093184:;625/54070146104832:0;-9/48062352093184:2;625/12015588023296:3;-225/48062352093184:4;625/17518727337965568:0,0;5/1297683506515968:0,2;625/364973486207616:0,3;125/1297683506515968:0,4;5/144187056279552:2,3;625/76334323912704:3,3;125/144187056279552:3,4;-11875/8514101486251266048:0,0,0;1/13139045503474176:0,0,2;-33125/946011276250140672:0,0,3;25/13139045503474176:0,0,4;1/1061741050785792:0,2,3;-625/3185223152357376:0,3,3;25/1061741050785792:0,3,4;1/216280584419328:2,3,3;-3125/11679151558643712:3,3,3;25/216280584419328:3,3,4;625/86205277548294068736:0,0,0,0;4375/76626913376261394432:0,0,0,3;-5/946011276250140672:0,0,2,3;-625/1064262685781408256:0,0,3,3;-125/946011276250140672:0,0,3,4;-5/52556182013896704:0,2,3,3;-3125/946011276250140672:0,3,3,3;-125/52556182013896704:0,3,3,4;-5/11679151558643712:2,3,3,3;625/52556182013896704:3,3,3,3;-125/11679151558643712:3,3,3,4;625/2068926661159057649664:0,0,0,0,3;625/114940370064392091648:0,0,0,3,3;-1/2838033828750422016:0,0,2,3,3;625/12771152229376899072:0,0,3,3,3;-25/2838033828750422016:0,0,3,3,4;-1/157668546041690112:0,2,3,3,3;625/1419016914375211008:0,3,3,3,3;-25/157668546041690112:0,3,3,3,4;-1/35037454675931136:2,3,3,3,3;625/315337092083380224:3,3,3,3,3;-25/35037454675931136:3,3,3,3,4"
compact_certificate_declaration theorem product_19_checked :
    mulShort n_c0_0 n_c1_4=product_19 := by
  decide +kernel
compact_certificate_declaration theorem product_19_value (v : ℕ→ℂ) :
    eval v product_19=eval v n_c0_0*eval v n_c1_4 := by
  rw [←product_19_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_20 : Poly := rational_polynomial% "-55625/865122337677312:0;-9/24031176046592:2;-5625/96124704186368:3;-225/24031176046592:4;-625/19111338914144256:0,0;-1/40552609578624:0,2;625/729946972415232:0,3;-25/40552609578624:0,4;1/18023382034944:2,3;625/48062352093184:3,3;25/18023382034944:3,4;115625/17028202972502532096:0,0,0;-1/3091540118464512:0,0,2;625/4777834728536064:0,0,3;-25/3091540118464512:0,0,4;1/432561168838656:0,2,3;79375/210224728055586816:0,3,3;25/432561168838656:0,3,4;23/2595367013031936:2,3,3;625/7786101039095808:3,3,3;575/2595367013031936:3,3,4;-41875/1379284440772705099776:0,0,0,0;-1/1064262685781408256:0,0,0,2;625/51084608917507596288:0,0,0,3;-25/1064262685781408256:0,0,0,4;5/118251409531267584:0,0,2,3;-11875/5676067657500844032:0,0,3,3;125/118251409531267584:0,0,3,4;83/210224728055586816:0,2,3,3;-29375/1892022552500281344:0,3,3,3;2075/210224728055586816:0,3,3,4;-1/3893050519547904:2,3,3,3;-25/3893050519547904:3,3,3,4;-3125/13965254962823639135232:0,0,0,0,0;-21875/12413559966954345897984:0,0,0,0,3;1/8514101486251266048:0,0,0,2,3;-4375/689642220386352549888:0,0,0,3,3;25/8514101486251266048:0,0,0,3,4;37/17028202972502532096:0,0,2,3,3;-44375/153253826752522788864:0,0,3,3,3;925/17028202972502532096:0,0,3,3,4;-625/946011276250140672:0,3,3,3,3;-1/210224728055586816:2,3,3,3,3;-625/946011276250140672:3,3,3,3,3;-25/210224728055586816:3,3,3,3,4;-3125/335166119107767339245568:0,0,0,0,0,3;-625/18620339950431518846976:0,0,0,0,3,3;1/153253826752522788864:0,0,0,2,3,3;625/2068926661159057649664:0,0,0,3,3,3;25/153253826752522788864:0,0,0,3,3,4;625/229880740128784183296:0,0,3,3,3,3;-1/1892022552500281344:0,2,3,3,3,3;625/17028202972502532096:0,3,3,3,3,3;-25/1892022552500281344:0,3,3,3,3,4"
compact_certificate_declaration theorem product_20_checked :
    mulShort n_c0_1 n_c1_3=product_20 := by
  decide +kernel
compact_certificate_declaration theorem product_20_value (v : ℕ→ℂ) :
    eval v product_20=eval v n_c0_1*eval v n_c1_3 := by
  rw [←product_20_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_21 : Poly := rational_polynomial% "-625/48062352093184:0;51875/105112364027793408:0,0;-7/973262629886976:0,2;-38125/35037454675931136:0,3;-175/973262629886976:0,4;-66875/12771152229376899072:0,0,0;-1/6064174847757312:0,0,2;3125/2838033828750422016:0,0,3;-25/6064174847757312:0,0,4;-1/2919787889660928:0,2,3;625/14333504185608192:0,3,3;-25/2919787889660928:0,3,4;-19375/517231665289764412416:0,0,0,0;-1/1064262685781408256:0,0,0,2;-153125/114940370064392091648:0,0,0,3;-25/1064262685781408256:0,0,0,4;-5/218310294519263232:0,0,2,3;-3125/1502488497573752832:0,0,3,3;-125/218310294519263232:0,0,3,4;31/315337092083380224:0,2,3,3;-11875/2838033828750422016:0,3,3,3;775/315337092083380224:0,3,3,4;625/775847497934646618624:0,0,0,0,0;625/96980937241830827328:0,0,0,0,3;-19/76626913376261394432:0,0,0,2,3;-14375/689642220386352549888:0,0,0,3,3;-475/76626913376261394432:0,0,0,3,4;-5/2128525371562816512:0,0,2,3,3;3125/38313456688130697216:0,0,3,3,3;-125/2128525371562816512:0,0,3,3,4;5/946011276250140672:0,2,3,3,3;-3125/8514101486251266048:0,3,3,3,3;125/946011276250140672:0,3,3,3,4;625/18620339950431518846976:0,0,0,0,0,3;625/1692758177311956258816:0,0,0,0,3,3;-1/114940370064392091648:0,0,0,2,3,3;3125/2068926661159057649664:0,0,0,3,3,3;-25/114940370064392091648:0,0,0,3,3,4;-1/12771152229376899072:0,0,2,3,3,3;625/76626913376261394432:0,0,3,3,3,3;-25/12771152229376899072:0,0,3,3,3,4"
compact_certificate_declaration theorem product_21_checked :
    mulShort n_c0_2 n_c1_2=product_21 := by
  decide +kernel
compact_certificate_declaration theorem product_21_value (v : ℕ→ℂ) :
    eval v product_21=eval v n_c0_2*eval v n_c1_2 := by
  rw [←product_21_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_22 : Poly := rational_polynomial% "21875/1946525259773952:0;-14375/35037454675931136:0,0;-1/432561168838656:0,2;-18125/11679151558643712:0,3;-25/432561168838656:0,4;11875/1596394028672112384:0,0,0;1/8085566463676416:0,0,2;625/12841782030544896:0,0,3;25/8085566463676416:0,0,4;-25/35037454675931136:0,2,3;-625/7166752092804096:0,3,3;-625/35037454675931136:0,3,4;4375/229880740128784183296:0,0,0,0;1/532131342890704128:0,0,0,2;-625/6761198239081887744:0,0,0,3;25/532131342890704128:0,0,0,4;1/1419016914375211008:0,0,2,3;11875/12771152229376899072:0,0,3,3;25/1419016914375211008:0,0,3,4;1/105112364027793408:0,2,3,3;44375/2838033828750422016:0,3,3,3;25/105112364027793408:0,3,3,4;-4375/6982627481411819567616:0,0,0,0,0;-18125/2068926661159057649664:0,0,0,0,3;-5/38313456688130697216:0,0,0,2,3;-26875/344821110193176274944:0,0,0,3,3;-125/38313456688130697216:0,0,0,3,4;-29/25542304458753798144:0,0,2,3,3;-3125/28735092516098022912:0,0,3,3,3;-725/25542304458753798144:0,0,3,3,4;25/2838033828750422016:0,2,3,3,3;-625/6385576114688449536:0,3,3,3,3;625/2838033828750422016:0,3,3,3,4;21875/502749178661651008868352:0,0,0,0,0,3;625/1551694995869293237248:0,0,0,0,3,3;-1/114940370064392091648:0,0,0,2,3,3;-625/477444614113628688384:0,0,0,3,3,3;-25/114940370064392091648:0,0,0,3,3,4;-1/19156728344065348608:0,0,2,3,3,3;-625/172410555096588137472:0,0,3,3,3,3;-25/19156728344065348608:0,0,3,3,3,4;1/4257050743125633024:0,2,3,3,3,3;-625/38313456688130697216:0,3,3,3,3,3;25/4257050743125633024:0,3,3,3,3,4;4375/1508247535984953026605056:0,0,0,0,0,3,3;3125/83791529776941834811392:0,0,0,0,3,3,3;625/6206779983477172948992:0,0,0,3,3,3,3"
compact_certificate_declaration theorem product_22_checked :
    mulShort n_c0_3 n_c1_1=product_22 := by
  decide +kernel
compact_certificate_declaration theorem product_22_value (v : ℕ→ℂ) :
    eval v product_22=eval v n_c0_3*eval v n_c1_1 := by
  rw [←product_22_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_23 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,3;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,3,3;0/1:0,3,3,3;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,3,3,3"
compact_certificate_declaration theorem product_23_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_4 n_c1_0=product_23 := by
  decide +kernel
compact_certificate_declaration theorem product_23_value (v : ℕ→ℂ) :
    eval v product_23=eval v n_c0_4*eval v n_c1_0 := by
  rw [←product_23_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_26 : Poly := rational_polynomial% "0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,3;0/1:0,2,3;0/1:0,3,3;0/1:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;0/1:0,0,0,0;0/1:0,0,0,3;0/1:0,0,3,3;0/1:0,3,3,3;0/1:0,0,0,0,3;0/1:0,0,0,3,3;0/1:0,0,3,3,3"
compact_certificate_declaration theorem partial_sum_26_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_23 [([],(0:ℚ))])=partial_sum_26 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_26_value (v : ℕ→ℂ) :
    eval v partial_sum_26=eval v product_23+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_26_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_27 : Poly := rational_polynomial% "21875/1946525259773952:0;0/1:2;0/1:3;0/1:4;-14375/35037454675931136:0,0;-1/432561168838656:0,2;-18125/11679151558643712:0,3;-25/432561168838656:0,4;0/1:2,3;0/1:3,3;0/1:3,4;11875/1596394028672112384:0,0,0;1/8085566463676416:0,0,2;625/12841782030544896:0,0,3;25/8085566463676416:0,0,4;-25/35037454675931136:0,2,3;-625/7166752092804096:0,3,3;-625/35037454675931136:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;4375/229880740128784183296:0,0,0,0;1/532131342890704128:0,0,0,2;-625/6761198239081887744:0,0,0,3;25/532131342890704128:0,0,0,4;1/1419016914375211008:0,0,2,3;11875/12771152229376899072:0,0,3,3;25/1419016914375211008:0,0,3,4;1/105112364027793408:0,2,3,3;44375/2838033828750422016:0,3,3,3;25/105112364027793408:0,3,3,4;-4375/6982627481411819567616:0,0,0,0,0;-18125/2068926661159057649664:0,0,0,0,3;-5/38313456688130697216:0,0,0,2,3;-26875/344821110193176274944:0,0,0,3,3;-125/38313456688130697216:0,0,0,3,4;-29/25542304458753798144:0,0,2,3,3;-3125/28735092516098022912:0,0,3,3,3;-725/25542304458753798144:0,0,3,3,4;25/2838033828750422016:0,2,3,3,3;-625/6385576114688449536:0,3,3,3,3;625/2838033828750422016:0,3,3,3,4;21875/502749178661651008868352:0,0,0,0,0,3;625/1551694995869293237248:0,0,0,0,3,3;-1/114940370064392091648:0,0,0,2,3,3;-625/477444614113628688384:0,0,0,3,3,3;-25/114940370064392091648:0,0,0,3,3,4;-1/19156728344065348608:0,0,2,3,3,3;-625/172410555096588137472:0,0,3,3,3,3;-25/19156728344065348608:0,0,3,3,3,4;1/4257050743125633024:0,2,3,3,3,3;-625/38313456688130697216:0,3,3,3,3,3;25/4257050743125633024:0,3,3,3,3,4;4375/1508247535984953026605056:0,0,0,0,0,3,3;3125/83791529776941834811392:0,0,0,0,3,3,3;625/6206779983477172948992:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_27_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_22 partial_sum_26)=partial_sum_27 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_27_value (v : ℕ→ℂ) :
    eval v partial_sum_27=eval v product_22+eval v partial_sum_26 := by
  rw [←partial_sum_27_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_28 : Poly := rational_polynomial% "-625/353913683595264:0;0/1:2;0/1:3;0/1:4;4375/52556182013896704:0,0;-37/3893050519547904:0,2;-23125/8759363668982784:0,3;-925/3893050519547904:0,4;0/1:2,3;0/1:3,3;0/1:3,4;3125/1419016914375211008:0,0,0;-1/24256699391029248:0,0,2;70625/1419016914375211008:0,0,3;-25/24256699391029248:0,0,4;-37/35037454675931136:0,2,3;-625/14333504185608192:0,3,3;-925/35037454675931136:0,3,4;0/1:2,3,3;0/1:3,3,3;0/1:3,3,4;-38125/2068926661159057649664:0,0,0,0;1/1064262685781408256:0,0,0,2;-81875/57470185032196045824:0,0,0,3;25/1064262685781408256:0,0,0,4;-7/315337092083380224:0,0,2,3;-29375/25542304458753798144:0,0,3,3;-175/315337092083380224:0,0,3,4;1/9274620355393536:0,2,3,3;625/54577573629815808:0,3,3,3;25/9274620355393536:0,3,3,4;625/3491313740705909783808:0,0,0,0,0;-14375/6206779983477172948992:0,0,0,0,3;-29/76626913376261394432:0,0,0,2,3;-68125/689642220386352549888:0,0,0,3,3;-725/76626913376261394432:0,0,0,3,4;-89/25542304458753798144:0,0,2,3,3;-3125/114940370064392091648:0,0,3,3,3;-2225/25542304458753798144:0,0,3,3,4;5/354754228593802752:0,2,3,3,3;-11875/25542304458753798144:0,3,3,3,3;125/354754228593802752:0,3,3,3,4;19375/251374589330825504434176:0,0,0,0,0,3;14375/18620339950431518846976:0,0,0,0,3,3;-1/57470185032196045824:0,0,0,2,3,3;625/3103389991738586474496:0,0,0,3,3,3;-25/57470185032196045824:0,0,0,3,3,4;-5/38313456688130697216:0,0,2,3,3,3;3125/689642220386352549888:0,0,3,3,3,3;-125/38313456688130697216:0,0,3,3,3,4;1/4257050743125633024:0,2,3,3,3,3;-625/38313456688130697216:0,3,3,3,3,3;25/4257050743125633024:0,3,3,3,3,4;4375/1508247535984953026605056:0,0,0,0,0,3,3;3125/83791529776941834811392:0,0,0,0,3,3,3;625/6206779983477172948992:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_28_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_21 partial_sum_27)=partial_sum_28 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_28_value (v : ℕ→ℂ) :
    eval v partial_sum_28=eval v product_21+eval v partial_sum_27 := by
  rw [←partial_sum_28_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_29 : Poly := rational_polynomial% "-514375/7786101039095808:0;-9/24031176046592:2;-5625/96124704186368:3;-225/24031176046592:4;625/12366160473858048:0,0;-133/3893050519547904:0,2;-15625/8759363668982784:0,3;-3325/3893050519547904:0,4;1/18023382034944:2,3;625/48062352093184:3,3;25/18023382034944:3,4;153125/17028202972502532096:0,0,0;-115/315337092083380224:0,0,2;128125/709508457187605504:0,0,3;-2875/315337092083380224:0,0,4;1/796305788089344:0,2,3;210625/630674184166760448:0,3,3;25/796305788089344:0,3,4;23/2595367013031936:2,3,3;625/7786101039095808:3,3,3;575/2595367013031936:3,3,4;-11875/243403136606947958784:0,0,0,0;-649375/459761480257568366592:0,0,0,3;19/946011276250140672:0,0,2,3;-165625/51084608917507596288:0,0,3,3;475/946011276250140672:0,0,3,4;317/630674184166760448:0,2,3,3;-23125/5676067657500844032:0,3,3,3;7925/630674184166760448:0,3,3,4;-1/3893050519547904:2,3,3,3;-25/3893050519547904:3,3,3,4;-625/13965254962823639135232:0,0,0,0,0;-625/153253826752522788864:0,0,0,0,3;-5/19156728344065348608:0,0,0,2,3;-18125/172410555096588137472:0,0,0,3,3;-125/19156728344065348608:0,0,0,3,4;-67/51084608917507596288:0,0,2,3,3;-145625/459761480257568366592:0,0,3,3,3;-1675/51084608917507596288:0,0,3,3,4;5/354754228593802752:0,2,3,3,3;-14375/12771152229376899072:0,3,3,3,3;125/354754228593802752:0,3,3,3,4;-1/210224728055586816:2,3,3,3,3;-625/946011276250140672:3,3,3,3,3;-25/210224728055586816:3,3,3,3,4;68125/1005498357323302017736704:0,0,0,0,0,3;625/846379088655978129408:0,0,0,0,3,3;-5/459761480257568366592:0,0,0,2,3,3;3125/6206779983477172948992:0,0,0,3,3,3;-125/459761480257568366592:0,0,0,3,3,4;-5/38313456688130697216:0,0,2,3,3,3;625/86205277548294068736:0,0,3,3,3,3;-125/38313456688130697216:0,0,3,3,3,4;-5/17028202972502532096:0,2,3,3,3,3;3125/153253826752522788864:0,3,3,3,3,3;-125/17028202972502532096:0,3,3,3,3,4;4375/1508247535984953026605056:0,0,0,0,0,3,3;3125/83791529776941834811392:0,0,0,0,3,3,3;625/6206779983477172948992:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_29_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_20 partial_sum_28)=partial_sum_29 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_29_value (v : ℕ→ℂ) :
    eval v partial_sum_29=eval v product_20+eval v partial_sum_28 := by
  rw [←partial_sum_29_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_30 : Poly := rational_polynomial% "-16875/48062352093184:;-424375/7786101039095808:0;-27/48062352093184:2;-625/96124704186368:3;-675/48062352093184:4;18125/210224728055586816:0,0;-59/1946525259773952:0,2;-625/8759363668982784:0,3;-1475/1946525259773952:0,4;1/11091312021504:2,3;625/29492806966272:3,3;25/11091312021504:3,4;14375/1892022552500281344:0,0,0;-7/24256699391029248:0,0,2;413125/2838033828750422016:0,0,3;-175/24256699391029248:0,0,4;7/3185223152357376:0,2,3;86875/630674184166760448:0,3,3;175/3185223152357376:0,3,4;35/2595367013031936:2,3,3;-4375/23358303117287424:3,3,3;875/2595367013031936:3,3,4;-15625/376168483847101390848:0,0,0,0;-623125/459761480257568366592:0,0,0,3;7/473005638125070336:0,0,2,3;-195625/51084608917507596288:0,0,3,3;175/473005638125070336:0,0,3,4;257/630674184166760448:0,2,3,3;-41875/5676067657500844032:0,3,3,3;6425/630674184166760448:0,3,3,4;-1/1459893944830464:2,3,3,3;625/52556182013896704:3,3,3,3;-25/1459893944830464:3,3,3,4;-625/13965254962823639135232:0,0,0,0,0;-15625/4137853322318115299328:0,0,0,0,3;-5/19156728344065348608:0,0,0,2,3;-3125/31347373653925115904:0,0,0,3,3;-125/19156728344065348608:0,0,0,3,4;-5/3004976995147505664:0,0,2,3,3;-123125/459761480257568366592:0,0,3,3,3;-125/3004976995147505664:0,0,3,3,4;1/129001537670473728:0,2,3,3,3;-4375/6385576114688449536:0,3,3,3,3;25/129001537670473728:0,3,3,3,4;-7/210224728055586816:2,3,3,3,3;625/473005638125070336:3,3,3,3,3;-175/210224728055586816:3,3,3,3,4;68125/1005498357323302017736704:0,0,0,0,0,3;625/846379088655978129408:0,0,0,0,3,3;-5/459761480257568366592:0,0,0,2,3,3;3125/6206779983477172948992:0,0,0,3,3,3;-125/459761480257568366592:0,0,0,3,3,4;-5/38313456688130697216:0,0,2,3,3,3;625/86205277548294068736:0,0,3,3,3,3;-125/38313456688130697216:0,0,3,3,3,4;-5/17028202972502532096:0,2,3,3,3,3;3125/153253826752522788864:0,3,3,3,3,3;-125/17028202972502532096:0,3,3,3,3,4;4375/1508247535984953026605056:0,0,0,0,0,3,3;3125/83791529776941834811392:0,0,0,0,3,3,3;625/6206779983477172948992:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_30_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_19 partial_sum_29)=partial_sum_30 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_30_value (v : ℕ→ℂ) :
    eval v partial_sum_30=eval v product_19+eval v partial_sum_29 := by
  rw [←partial_sum_30_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_31 : Poly := rational_polynomial% "-16875/48062352093184:;-424375/7786101039095808:0;-27/48062352093184:2;-625/96124704186368:3;-675/48062352093184:4;18125/210224728055586816:0,0;-59/1946525259773952:0,2;-625/8759363668982784:0,3;-1475/1946525259773952:0,4;1/11091312021504:2,3;625/29492806966272:3,3;25/11091312021504:3,4;14375/1892022552500281344:0,0,0;-7/24256699391029248:0,0,2;413125/2838033828750422016:0,0,3;-175/24256699391029248:0,0,4;7/3185223152357376:0,2,3;86875/630674184166760448:0,3,3;175/3185223152357376:0,3,4;35/2595367013031936:2,3,3;-4375/23358303117287424:3,3,3;875/2595367013031936:3,3,4;-15625/376168483847101390848:0,0,0,0;-623125/459761480257568366592:0,0,0,3;7/473005638125070336:0,0,2,3;-195625/51084608917507596288:0,0,3,3;175/473005638125070336:0,0,3,4;257/630674184166760448:0,2,3,3;-41875/5676067657500844032:0,3,3,3;6425/630674184166760448:0,3,3,4;-1/1459893944830464:2,3,3,3;625/52556182013896704:3,3,3,3;-25/1459893944830464:3,3,3,4;-625/13965254962823639135232:0,0,0,0,0;-15625/4137853322318115299328:0,0,0,0,3;-5/19156728344065348608:0,0,0,2,3;-3125/31347373653925115904:0,0,0,3,3;-125/19156728344065348608:0,0,0,3,4;-5/3004976995147505664:0,0,2,3,3;-123125/459761480257568366592:0,0,3,3,3;-125/3004976995147505664:0,0,3,3,4;1/129001537670473728:0,2,3,3,3;-4375/6385576114688449536:0,3,3,3,3;25/129001537670473728:0,3,3,3,4;-7/210224728055586816:2,3,3,3,3;625/473005638125070336:3,3,3,3,3;-175/210224728055586816:3,3,3,3,4;68125/1005498357323302017736704:0,0,0,0,0,3;625/846379088655978129408:0,0,0,0,3,3;-5/459761480257568366592:0,0,0,2,3,3;3125/6206779983477172948992:0,0,0,3,3,3;-125/459761480257568366592:0,0,0,3,3,4;-5/38313456688130697216:0,0,2,3,3,3;625/86205277548294068736:0,0,3,3,3,3;-125/38313456688130697216:0,0,3,3,3,4;-5/17028202972502532096:0,2,3,3,3,3;3125/153253826752522788864:0,3,3,3,3,3;-125/17028202972502532096:0,3,3,3,3,4;4375/1508247535984953026605056:0,0,0,0,0,3,3;3125/83791529776941834811392:0,0,0,0,3,3,3;625/6206779983477172948992:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_31_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_30 product_1)=partial_sum_31 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_31_value (v : ℕ→ℂ) :
    eval v partial_sum_31=eval v partial_sum_30+eval v product_1 := by
  rw [←partial_sum_31_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_32 : Poly := rational_polynomial% "-16875/48062352093184:;-424375/7786101039095808:0;-27/48062352093184:2;-625/96124704186368:3;-675/48062352093184:4;18125/210224728055586816:0,0;-59/1946525259773952:0,2;-625/8759363668982784:0,3;-1475/1946525259773952:0,4;1/11091312021504:2,3;625/29492806966272:3,3;25/11091312021504:3,4;14375/1892022552500281344:0,0,0;-7/24256699391029248:0,0,2;413125/2838033828750422016:0,0,3;-175/24256699391029248:0,0,4;7/3185223152357376:0,2,3;86875/630674184166760448:0,3,3;175/3185223152357376:0,3,4;35/2595367013031936:2,3,3;-4375/23358303117287424:3,3,3;875/2595367013031936:3,3,4;-15625/376168483847101390848:0,0,0,0;-623125/459761480257568366592:0,0,0,3;7/473005638125070336:0,0,2,3;-195625/51084608917507596288:0,0,3,3;175/473005638125070336:0,0,3,4;257/630674184166760448:0,2,3,3;-41875/5676067657500844032:0,3,3,3;6425/630674184166760448:0,3,3,4;-1/1459893944830464:2,3,3,3;625/52556182013896704:3,3,3,3;-25/1459893944830464:3,3,3,4;-625/13965254962823639135232:0,0,0,0,0;-15625/4137853322318115299328:0,0,0,0,3;-5/19156728344065348608:0,0,0,2,3;-3125/31347373653925115904:0,0,0,3,3;-125/19156728344065348608:0,0,0,3,4;-5/3004976995147505664:0,0,2,3,3;-123125/459761480257568366592:0,0,3,3,3;-125/3004976995147505664:0,0,3,3,4;1/129001537670473728:0,2,3,3,3;-4375/6385576114688449536:0,3,3,3,3;25/129001537670473728:0,3,3,3,4;-7/210224728055586816:2,3,3,3,3;625/473005638125070336:3,3,3,3,3;-175/210224728055586816:3,3,3,3,4;68125/1005498357323302017736704:0,0,0,0,0,3;625/846379088655978129408:0,0,0,0,3,3;-5/459761480257568366592:0,0,0,2,3,3;3125/6206779983477172948992:0,0,0,3,3,3;-125/459761480257568366592:0,0,0,3,3,4;-5/38313456688130697216:0,0,2,3,3,3;625/86205277548294068736:0,0,3,3,3,3;-125/38313456688130697216:0,0,3,3,3,4;-5/17028202972502532096:0,2,3,3,3,3;3125/153253826752522788864:0,3,3,3,3,3;-125/17028202972502532096:0,3,3,3,3,4;4375/1508247535984953026605056:0,0,0,0,0,3,3;3125/83791529776941834811392:0,0,0,0,3,3,3;625/6206779983477172948992:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_32_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_31 product_1)=partial_sum_32 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_32_value (v : ℕ→ℂ) :
    eval v partial_sum_32=eval v partial_sum_31+eval v product_1 := by
  rw [←partial_sum_32_checked, eval_add]
compact_certificate_declaration noncomputable def product_24 : Poly := rational_polynomial% "28125/96124704186368:;156875/7786101039095808:0;-4375/1476825000681472:1;27/48062352093184:2;625/96124704186368:3;675/48062352093184:4;-625/4410308980187136:0,0;-11875/164481384450898944:0,1;59/1946525259773952:0,2;41875/70074909351862272:0,3;1475/1946525259773952:0,4;3125/9137854691716608:1,3;-1/11091312021504:2,3;-15625/3893050519547904:3,3;-25/11091312021504:3,4;23125/51084608917507596288:0,0,0;-30625/35527979041394171904:0,0,1;7/24256699391029248:0,0,2;-625/10433947899817728:0,0,3;175/24256699391029248:0,0,4;49375/11842659680464723968:0,1,3;-7/3185223152357376:0,2,3;-66875/630674184166760448:0,3,3;-175/3185223152357376:0,3,4;625/12652414188530688:1,3,3;-35/2595367013031936:2,3,3;-625/707827367190528:3,3,3;-875/2595367013031936:3,3,4;90625/2068926661159057649664:0,0,0,0;-625/119906929264705330176:0,0,0,1;120625/153253826752522788864:0,0,0,3;-625/159875905686273773568:0,0,1,3;-7/473005638125070336:0,0,2,3;-11875/51084608917507596288:0,0,3,3;-175/473005638125070336:0,0,3,4;3125/53291968562091257856:0,1,3,3;-257/630674184166760448:0,2,3,3;625/32250384417618432:0,3,3,3;-6425/630674184166760448:0,3,3,4;-55625/11842659680464723968:1,3,3,3;1/1459893944830464:2,3,3,3;-33125/315337092083380224:3,3,3,3;25/1459893944830464:3,3,3,4;-625/3491313740705909783808:0,0,0,0,0;-38125/12413559966954345897984:0,0,0,0,3;14375/25899896721176351318016:0,0,0,1,3;5/19156728344065348608:0,0,0,2,3;625/14367546258049011456:0,0,0,3,3;125/19156728344065348608:0,0,0,3,4;11875/959255434117642641408:0,0,1,3,3;5/3004976995147505664:0,0,2,3,3;209375/459761480257568366592:0,0,3,3,3;125/3004976995147505664:0,0,3,3,4;11875/319751811372547547136:0,1,3,3,3;-1/129001537670473728:0,2,3,3,3;98125/25542304458753798144:0,3,3,3,3;-25/129001537670473728:0,3,3,3,4;-625/3947553226821574656:1,3,3,3,3;7/210224728055586816:2,3,3,3,3;-625/473005638125070336:3,3,3,3,3;175/210224728055586816:3,3,3,3,4;-19375/251374589330825504434176:0,0,0,0,0,3;-19375/18620339950431518846976:0,0,0,0,3,3;625/19424922540882263488512:0,0,0,1,3,3;5/459761480257568366592:0,0,0,2,3,3;-19375/12413559966954345897984:0,0,0,3,3,3;125/459761480257568366592:0,0,0,3,3,4;4375/8633298907058783772672:0,0,1,3,3,3;5/38313456688130697216:0,0,2,3,3,3;21875/1379284440772705099776:0,0,3,3,3,3;125/38313456688130697216:0,0,3,3,3,4;625/239813858529410660352:0,1,3,3,3,3;5/17028202972502532096:0,2,3,3,3,3;19375/153253826752522788864:0,3,3,3,3,3;125/17028202972502532096:0,3,3,3,3,4;625/106583937124182515712:1,3,3,3,3,3;625/5676067657500844032:3,3,3,3,3,3;-4375/1508247535984953026605056:0,0,0,0,0,3,3;-3125/83791529776941834811392:0,0,0,0,3,3,3;-625/6206779983477172948992:0,0,0,3,3,3,3"
compact_certificate_declaration theorem product_24_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_2 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_3 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_4 n_c7_0) [([],(0:ℚ))])))=product_24 := by
  decide +kernel
compact_certificate_declaration theorem product_24_value (v : ℕ→ℂ) :
    eval v product_24=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_2 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_3 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_4 n_c7_0) [([],(0:ℚ))]))) := by
  rw [←product_24_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_33 : Poly := rational_polynomial% "-5625/96124704186368:;-66875/1946525259773952:0;-4375/1476825000681472:1;-4375/78834273020845056:0,0;-11875/164481384450898944:0,1;36875/70074909351862272:0,3;3125/9137854691716608:1,3;66875/3893050519547904:3,3;205625/25542304458753798144:0,0,0;-30625/35527979041394171904:0,0,1;243125/2838033828750422016:0,0,3;49375/11842659680464723968:0,1,3;625/19708568255211264:0,3,3;625/12652414188530688:1,3,3;-3125/2919787889660928:3,3,3;3125/1379284440772705099776:0,0,0,0;-625/119906929264705330176:0,0,0,1;-11875/20898249102616743936:0,0,0,3;-625/159875905686273773568:0,0,1,3;-51875/12771152229376899072:0,0,3,3;3125/53291968562091257856:0,1,3,3;68125/5676067657500844032:0,3,3,3;-55625/11842659680464723968:1,3,3,3;-29375/315337092083380224:3,3,3,3;-3125/13965254962823639135232:0,0,0,0,0;-625/91276176227605484544:0,0,0,0,3;14375/25899896721176351318016:0,0,0,1,3;-19375/344821110193176274944:0,0,0,3,3;11875/959255434117642641408:0,0,1,3,3;14375/76626913376261394432:0,0,3,3,3;11875/319751811372547547136:0,1,3,3,3;26875/8514101486251266048:0,3,3,3,3;-625/3947553226821574656:1,3,3,3,3;-3125/335166119107767339245568:0,0,0,0,0,3;-625/2068926661159057649664:0,0,0,0,3,3;625/19424922540882263488512:0,0,0,1,3,3;-4375/4137853322318115299328:0,0,0,3,3,3;4375/8633298907058783772672:0,0,1,3,3,3;625/27044792956327550976:0,0,3,3,3,3;625/239813858529410660352:0,1,3,3,3,3;625/4257050743125633024:0,3,3,3,3,3;625/106583937124182515712:1,3,3,3,3,3;625/5676067657500844032:3,3,3,3,3,3"
compact_certificate_declaration theorem partial_sum_33_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_32 product_24)=partial_sum_33 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_33_value (v : ℕ→ℂ) :
    eval v partial_sum_33=eval v partial_sum_32+eval v product_24 := by
  rw [←partial_sum_33_checked, eval_add]
compact_certificate_declaration noncomputable def product_25 : Poly := rational_polynomial% "5625/96124704186368:;66875/1946525259773952:0;4375/1476825000681472:1;4375/78834273020845056:0,0;11875/164481384450898944:0,1;-36875/70074909351862272:0,3;-3125/9137854691716608:1,3;-66875/3893050519547904:3,3;-205625/25542304458753798144:0,0,0;30625/35527979041394171904:0,0,1;-243125/2838033828750422016:0,0,3;-49375/11842659680464723968:0,1,3;-625/19708568255211264:0,3,3;-625/12652414188530688:1,3,3;3125/2919787889660928:3,3,3;-3125/1379284440772705099776:0,0,0,0;625/119906929264705330176:0,0,0,1;11875/20898249102616743936:0,0,0,3;625/159875905686273773568:0,0,1,3;51875/12771152229376899072:0,0,3,3;-3125/53291968562091257856:0,1,3,3;-68125/5676067657500844032:0,3,3,3;55625/11842659680464723968:1,3,3,3;29375/315337092083380224:3,3,3,3;3125/13965254962823639135232:0,0,0,0,0;625/91276176227605484544:0,0,0,0,3;-14375/25899896721176351318016:0,0,0,1,3;19375/344821110193176274944:0,0,0,3,3;-11875/959255434117642641408:0,0,1,3,3;-14375/76626913376261394432:0,0,3,3,3;-11875/319751811372547547136:0,1,3,3,3;-26875/8514101486251266048:0,3,3,3,3;625/3947553226821574656:1,3,3,3,3;3125/335166119107767339245568:0,0,0,0,0,3;625/2068926661159057649664:0,0,0,0,3,3;-625/19424922540882263488512:0,0,0,1,3,3;4375/4137853322318115299328:0,0,0,3,3,3;-4375/8633298907058783772672:0,0,1,3,3,3;-625/27044792956327550976:0,0,3,3,3,3;-625/239813858529410660352:0,1,3,3,3,3;-625/4257050743125633024:0,3,3,3,3,3;-625/106583937124182515712:1,3,3,3,3,3;-625/5676067657500844032:3,3,3,3,3,3"
compact_certificate_declaration theorem product_25_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_1 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_2 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_3 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_4 n_c9_0) [([],(0:ℚ))]))))=product_25 := by
  decide +kernel
compact_certificate_declaration theorem product_25_value (v : ℕ→ℂ) :
    eval v product_25=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_1 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_2 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_3 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_4 n_c9_0) [([],(0:ℚ))])))) := by
  rw [←product_25_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_34 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_34_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_33 product_25)=partial_sum_34 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_34_value (v : ℕ→ℂ) :
    eval v partial_sum_34=eval v partial_sum_33+eval v product_25 := by
  rw [←partial_sum_34_checked, eval_add]
compact_certificate_declaration noncomputable def e4 : Poly := partial_sum_34
compact_certificate_declaration theorem checked_4 : checkZero e4=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_4 (y z w a b : ℂ) :
    (certificate y z w a b)[4]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_4 y z w a b))+(((c0_1 y z w a b)*(c1_3 y z w a b))+(((c0_2 y z w a b)*(c1_2 y z w a b))+(((c0_3 y z w a b)*(c1_1 y z w a b))+(((c0_4 y z w a b)*(c1_0 y z w a b))+0)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_2 y z w a b)*(c7_2 y z w a b))+(((c6_3 y z w a b)*(c7_1 y z w a b))+(((c6_4 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_1 y z w a b)*(c9_3 y z w a b))+(((c8_2 y z w a b)*(c9_2 y z w a b))+(((c8_3 y z w a b)*(c9_1 y z w a b))+(((c8_4 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e4 checked_4
  simp only [e4, eval_add, eval_mul, eval_scale, eval_pow, product_19_value, product_20_value, product_21_value, product_22_value, product_23_value, partial_sum_26_value, partial_sum_27_value, partial_sum_28_value, partial_sum_29_value, partial_sum_30_value, product_1_value, partial_sum_31_value, partial_sum_32_value, product_24_value, partial_sum_33_value, product_25_value, partial_sum_34_value, n_c0_0_value y z w a b 0, n_c0_1_value y z w a b 0, n_c0_2_value y z w a b 0, n_c0_3_value y z w a b 0, n_c0_4_value y z w a b 0, n_c1_0_value y z w a b 0, n_c1_1_value y z w a b 0, n_c1_2_value y z w a b 0, n_c1_3_value y z w a b 0, n_c1_4_value y z w a b 0, n_c6_2_value y z w a b 0, n_c6_3_value y z w a b 0, n_c6_4_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_1_value y z w a b 0, n_c8_2_value y z w a b 0, n_c8_3_value y z w a b 0, n_c8_4_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_4
compact_certificate_declaration noncomputable def product_26 : Poly := rational_polynomial% "-16875/192249408372736:;625/216280584419328:0;-9/192249408372736:2;625/48062352093184:3;-225/192249408372736:4;625/70074909351862272:0,0;5/5190734026063872:0,2;625/1459893944830464:0,3;125/5190734026063872:0,4;5/576748225118208:2,3;625/305337295650816:3,3;125/576748225118208:3,4;-11875/34056405945005064192:0,0,0;1/52556182013896704:0,0,2;-33125/3784045105000562688:0,0,3;25/52556182013896704:0,0,4;1/4246964203143168:0,2,3;-625/12740892609429504:0,3,3;25/4246964203143168:0,3,4;1/865122337677312:2,3,3;-3125/46716606234574848:3,3,3;25/865122337677312:3,3,4;625/344821110193176274944:0,0,0,0;4375/306507653505045577728:0,0,0,3;-5/3784045105000562688:0,0,2,3;-625/4257050743125633024:0,0,3,3;-125/3784045105000562688:0,0,3,4;-5/210224728055586816:0,2,3,3;-3125/3784045105000562688:0,3,3,3;-125/210224728055586816:0,3,3,4;-5/46716606234574848:2,3,3,3;625/210224728055586816:3,3,3,3;-125/46716606234574848:3,3,3,4;625/8275706644636230598656:0,0,0,0,3;625/459761480257568366592:0,0,0,3,3;-1/11352135315001688064:0,0,2,3,3;625/51084608917507596288:0,0,3,3,3;-25/11352135315001688064:0,0,3,3,4;-1/630674184166760448:0,2,3,3,3;625/5676067657500844032:0,3,3,3,3;-25/630674184166760448:0,3,3,3,4;-1/140149818703724544:2,3,3,3,3;625/1261348368333520896:3,3,3,3,3;-25/140149818703724544:3,3,3,3,4"
compact_certificate_declaration theorem product_26_checked :
    mulShort n_c0_0 n_c1_5=product_26 := by
  decide +kernel
compact_certificate_declaration theorem product_26_value (v : ℕ→ℂ) :
    eval v product_26=eval v n_c0_0*eval v n_c1_5 := by
  rw [←product_26_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_27 : Poly := rational_polynomial% "-55625/5190734026063872:0;-3/48062352093184:2;-1875/192249408372736:3;-75/48062352093184:4;625/16171132927352832:0,0;-5/1297683506515968:0,2;-625/2919787889660928:0,3;-125/1297683506515968:0,4;1/144187056279552:2,3;3125/1730244675354624:3,3;25/144187056279552:3,4;33125/34056405945005064192:0,0,0;-1/26278091006948352:0,0,2;45625/1892022552500281344:0,0,3;-25/26278091006948352:0,0,4;5/23358303117287424:0,2,3;625/13139045503474176:0,3,3;125/23358303117287424:0,3,4;1/576748225118208:2,3,3;625/7786101039095808:3,3,3;25/576748225118208:3,3,4;-3125/344821110193176274944:0,0,0,0;-3125/51084608917507596288:0,0,0,3;1/210224728055586816:0,0,2,3;11875/34056405945005064192:0,0,3,3;25/210224728055586816:0,0,3,4;7/105112364027793408:0,2,3,3;-4375/3784045105000562688:0,3,3,3;175/105112364027793408:0,3,3,4;1/46716606234574848:2,3,3,3;625/210224728055586816:3,3,3,3;25/46716606234574848:3,3,3,4;-3125/8275706644636230598656:0,0,0,0,3;-4375/919522960515136733184:0,0,0,3,3;1/3784045105000562688:0,0,2,3,3;-3125/102169217835015192576:0,0,3,3,3;25/3784045105000562688:0,0,3,3,4;1/420449456111173632:0,2,3,3,3;-625/3784045105000562688:0,3,3,3,3;25/420449456111173632:0,3,3,3,4"
compact_certificate_declaration theorem product_27_checked :
    mulShort n_c0_1 n_c1_4=product_27 := by
  decide +kernel
compact_certificate_declaration theorem product_27_value (v : ℕ→ℂ) :
    eval v product_27=eval v n_c0_1*eval v n_c1_4 := by
  rw [←product_27_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_28 : Poly := rational_polynomial% "-151875/384498816745472:;23125/1730244675354624:0;-21/96124704186368:2;-625/33926366183424:3;-525/96124704186368:4;-81875/840898912222347264:0,0;-23/3893050519547904:0,2;-184375/280299637407449088:0,3;-575/3893050519547904:0,4;-1/432561168838656:2,3;79375/31144404156383232:3,3;-25/432561168838656:3,4;-183125/102169217835015192576:0,0,0;-31/630674184166760448:0,0,2;-86875/2522696736667041792:0,0,3;-775/630674184166760448:0,0,4;-155/280299637407449088:0,2,3;-4375/74196962843148288:0,3,3;-3875/280299637407449088:0,3,4;35/10381468052127744:2,3,3;-49375/280299637407449088:3,3,3;875/10381468052127744:3,3,4;81875/4137853322318115299328:0,0,0,0;-1/8514101486251266048:0,0,0,2;21875/306507653505045577728:0,0,0,3;-25/8514101486251266048:0,0,0,4;-53/5676067657500844032:0,0,2,3;625/1032012301363789824:0,0,3,3;-1325/5676067657500844032:0,0,3,4;-7/210224728055586816:0,2,3,3;625/145540196346175488:0,3,3,3;-175/210224728055586816:0,3,3,4;7/140149818703724544:2,3,3,3;-625/97026797564116992:3,3,3,3;175/140149818703724544:3,3,3,4;625/6206779983477172948992:0,0,0,0,0;45625/49654239867817383591936:0,0,0,0,3;-19/613015307010091155456:0,0,0,2,3;625/459761480257568366592:0,0,0,3,3;-475/613015307010091155456:0,0,0,3,4;-19/68112811890010128384:0,0,2,3,3;625/7859170602693476352:0,0,3,3,3;-475/68112811890010128384:0,0,3,3,4;7/7568090210001125376:0,2,3,3,3;625/5676067657500844032:0,3,3,3,3;175/7568090210001125376:0,3,3,3,4;-5/840898912222347264:2,3,3,3,3;3125/7568090210001125376:3,3,3,3,3;-125/840898912222347264:3,3,3,3,4;625/148962719603452150775808:0,0,0,0,0,3;625/74481359801726075387904:0,0,0,0,3,3;-1/919522960515136733184:0,0,0,2,3,3;-625/2758568881545410199552:0,0,0,3,3,3;-25/919522960515136733184:0,0,0,3,3,4;-625/919522960515136733184:0,0,3,3,3,3;1/11352135315001688064:0,2,3,3,3,3;-625/68112811890010128384:0,3,3,3,3,3;25/11352135315001688064:0,3,3,3,3,4"
compact_certificate_declaration theorem product_28_checked :
    mulShort n_c0_2 n_c1_3=product_28 := by
  decide +kernel
compact_certificate_declaration theorem product_28_value (v : ℕ→ℂ) :
    eval v product_28=eval v n_c0_2*eval v n_c1_3 := by
  rw [←product_28_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_29 : Poly := rational_polynomial% "21875/7786101039095808:0;-14375/140149818703724544:0,0;-1/1730244675354624:0,2;-625/8244106982572032:0,3;-25/1730244675354624:0,4;11875/6385576114688449536:0,0,0;1/32342265854705664:0,0,2;4375/5676067657500844032:0,0,3;25/32342265854705664:0,0,4;-1/4122053491286016:0,2,3;-38125/1261348368333520896:0,3,3;-25/4122053491286016:0,3,4;4375/919522960515136733184:0,0,0,0;1/2128525371562816512:0,0,0,2;3125/17028202972502532096:0,0,0,3;25/2128525371562816512:0,0,0,4;41/11352135315001688064:0,0,2,3;625/1964792650673369088:0,0,3,3;1025/11352135315001688064:0,0,3,4;-31/1261348368333520896:0,2,3,3;3125/5676067657500844032:0,3,3,3;-775/1261348368333520896:0,3,3,4;-4375/27930509925647278270464:0,0,0,0,0;-625/376168483847101390848:0,0,0,0,3;1/51084608917507596288:0,0,0,2,3;625/689642220386352549888:0,0,0,3,3;25/51084608917507596288:0,0,0,3,4;1/8514101486251266048:0,0,2,3,3;625/76626913376261394432:0,0,3,3,3;25/8514101486251266048:0,0,3,3,4;-1/1892022552500281344:0,2,3,3,3;625/17028202972502532096:0,3,3,3,3;-25/1892022552500281344:0,3,3,3,4;-4375/670332238215534678491136:0,0,0,0,0,3;-3125/37240679900863037693952:0,0,0,0,3,3;-625/2758568881545410199552:0,0,0,3,3,3"
compact_certificate_declaration theorem product_29_checked :
    mulShort n_c0_3 n_c1_2=product_29 := by
  decide +kernel
compact_certificate_declaration theorem product_29_value (v : ℕ→ℂ) :
    eval v product_29=eval v n_c0_3*eval v n_c1_2 := by
  rw [←product_29_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_30 : Poly := rational_polynomial% "-19375/7786101039095808:0;108125/1261348368333520896:0,0;1/1297683506515968:0,2;41875/70074909351862272:0,3;25/1297683506515968:0,4;-625/399098507168028096:0,0,0;1/105112364027793408:0,0,2;-6875/1032012301363789824:0,0,3;25/105112364027793408:0,0,4;5/70074909351862272:0,2,3;-25625/1261348368333520896:0,3,3;125/70074909351862272:0,3,4;-38125/8275706644636230598656:0,0,0,0;44375/919522960515136733184:0,0,0,3;-1/5676067657500844032:0,0,2,3;-21875/34056405945005064192:0,0,3,3;-25/5676067657500844032:0,0,3,4;-1/105112364027793408:0,2,3,3;-625/258003075340947456:0,3,3,3;-25/105112364027793408:0,3,3,4;625/13965254962823639135232:0,0,0,0,0;3125/2864667684681772130304:0,0,0,0,3;119375/8275706644636230598656:0,0,0,3,3;-5/51084608917507596288:0,0,2,3,3;11875/459761480257568366592:0,0,3,3,3;-125/51084608917507596288:0,0,3,3,4;-5/5676067657500844032:0,2,3,3,3;625/7859170602693476352:0,3,3,3,3;-125/5676067657500844032:0,3,3,3,4;-3125/1005498357323302017736704:0,0,0,0,0,3;-625/20313098127743475105792:0,0,0,0,3,3;625/6206779983477172948992:0,0,0,3,3,3;3125/2758568881545410199552:0,0,3,3,3,3;-625/3016495071969906053210112:0,0,0,0,0,3,3;-625/167583059553883669622784:0,0,0,0,3,3,3;-625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem product_30_checked :
    mulShort n_c0_4 n_c1_1=product_30 := by
  decide +kernel
compact_certificate_declaration theorem product_30_value (v : ℕ→ℂ) :
    eval v product_30=eval v n_c0_4*eval v n_c1_1 := by
  rw [←product_30_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_31 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,3;0/1:0,3,3;0/1:0,0,0,3;0/1:0,0,3,3;0/1:0,3,3,3"
compact_certificate_declaration theorem product_31_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_5 n_c1_0=product_31 := by
  decide +kernel
compact_certificate_declaration theorem product_31_value (v : ℕ→ℂ) :
    eval v product_31=eval v n_c0_5*eval v n_c1_0 := by
  rw [←product_31_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_35 : Poly := rational_polynomial% "0/1:0;0/1:2;0/1:3;0/1:4;0/1:0,0;0/1:0,2;0/1:0,3;0/1:0,4;0/1:2,3;0/1:3,3;0/1:3,4;0/1:0,0,0;0/1:0,0,3;0/1:0,3,3;0/1:0,0,0,3;0/1:0,0,3,3;0/1:0,3,3,3"
compact_certificate_declaration theorem partial_sum_35_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_31 [([],(0:ℚ))])=partial_sum_35 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_35_value (v : ℕ→ℂ) :
    eval v partial_sum_35=eval v product_31+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_35_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_36 : Poly := rational_polynomial% "-19375/7786101039095808:0;0/1:2;0/1:3;0/1:4;108125/1261348368333520896:0,0;1/1297683506515968:0,2;41875/70074909351862272:0,3;25/1297683506515968:0,4;0/1:2,3;0/1:3,3;0/1:3,4;-625/399098507168028096:0,0,0;1/105112364027793408:0,0,2;-6875/1032012301363789824:0,0,3;25/105112364027793408:0,0,4;5/70074909351862272:0,2,3;-25625/1261348368333520896:0,3,3;125/70074909351862272:0,3,4;-38125/8275706644636230598656:0,0,0,0;44375/919522960515136733184:0,0,0,3;-1/5676067657500844032:0,0,2,3;-21875/34056405945005064192:0,0,3,3;-25/5676067657500844032:0,0,3,4;-1/105112364027793408:0,2,3,3;-625/258003075340947456:0,3,3,3;-25/105112364027793408:0,3,3,4;625/13965254962823639135232:0,0,0,0,0;3125/2864667684681772130304:0,0,0,0,3;119375/8275706644636230598656:0,0,0,3,3;-5/51084608917507596288:0,0,2,3,3;11875/459761480257568366592:0,0,3,3,3;-125/51084608917507596288:0,0,3,3,4;-5/5676067657500844032:0,2,3,3,3;625/7859170602693476352:0,3,3,3,3;-125/5676067657500844032:0,3,3,3,4;-3125/1005498357323302017736704:0,0,0,0,0,3;-625/20313098127743475105792:0,0,0,0,3,3;625/6206779983477172948992:0,0,0,3,3,3;3125/2758568881545410199552:0,0,3,3,3,3;-625/3016495071969906053210112:0,0,0,0,0,3,3;-625/167583059553883669622784:0,0,0,0,3,3,3;-625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_36_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_30 partial_sum_35)=partial_sum_36 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_36_value (v : ℕ→ℂ) :
    eval v partial_sum_36=eval v product_30+eval v partial_sum_35 := by
  rw [←partial_sum_36_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_37 : Poly := rational_polynomial% "625/1946525259773952:0;0/1:2;0/1:3;0/1:4;-625/37098481421574144:0,0;1/5190734026063872:0,2;625/1197861698322432:0,3;25/5190734026063872:0,4;0/1:2,3;0/1:3,3;0/1:3,4;625/2128525371562816512:0,0,0;1/24732320947716096:0,0,2;-66875/11352135315001688064:0,0,3;25/24732320947716096:0,0,4;-1/5839575779321856:0,2,3;-625/12366160473858048:0,3,3;-25/5839575779321856:0,3,4;625/4137853322318115299328:0,0,0,0;1/2128525371562816512:0,0,0,2;19375/83592996410466975744:0,0,0,3;25/2128525371562816512:0,0,0,4;1/291080392692350976:0,0,2,3;-33125/102169217835015192576:0,0,3,3;25/291080392692350976:0,0,3,4;-43/1261348368333520896:0,2,3,3;-625/333886332794167296:0,3,3,3;-1075/1261348368333520896:0,3,3,4;-3125/27930509925647278270464:0,0,0,0,0;-625/1095314114731265814528:0,0,0,0,3;1/51084608917507596288:0,0,0,2,3;126875/8275706644636230598656:0,0,0,3,3;25/51084608917507596288:0,0,0,3,4;1/51084608917507596288:0,0,2,3,3;15625/459761480257568366592:0,0,3,3,3;25/51084608917507596288:0,0,3,3,4;-1/709508457187605504:0,2,3,3,3;11875/102169217835015192576:0,3,3,3,3;-25/709508457187605504:0,3,3,3,4;-19375/2010996714646604035473408:0,0,0,0,0,3;-25625/223444079405178226163712:0,0,0,0,3,3;-3125/24827119933908691795968:0,0,0,3,3,3;3125/2758568881545410199552:0,0,3,3,3,3;-625/3016495071969906053210112:0,0,0,0,0,3,3;-625/167583059553883669622784:0,0,0,0,3,3,3;-625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_37_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_29 partial_sum_36)=partial_sum_37 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_37_value (v : ℕ→ℂ) :
    eval v partial_sum_37=eval v product_29+eval v partial_sum_36 := by
  rw [←partial_sum_37_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_38 : Poly := rational_polynomial% "-151875/384498816745472:;19375/1415654734381056:0;-21/96124704186368:2;-625/33926366183424:3;-525/96124704186368:4;-288125/2522696736667041792:0,0;-89/15572202078191616:0,2;-38125/280299637407449088:0,3;-2225/15572202078191616:0,4;-1/432561168838656:2,3;79375/31144404156383232:3,3;-25/432561168838656:3,4;-153125/102169217835015192576:0,0,0;-1/114668033484865536:0,0,2;-915625/22704270630003376128:0,0,3;-25/114668033484865536:0,0,4;-203/280299637407449088:0,2,3;-625/5707458680242176:0,3,3;-5075/280299637407449088:0,3,4;35/10381468052127744:2,3,3;-49375/280299637407449088:3,3,3;875/10381468052127744:3,3,4;625/31347373653925115904:0,0,0,0;1/2838033828750422016:0,0,0,2;139375/459761480257568366592:0,0,0,3;25/2838033828750422016:0,0,0,4;-67/11352135315001688064:0,0,2,3;14375/51084608917507596288:0,0,3,3;-1675/11352135315001688064:0,0,3,4;-5/74196962843148288:0,2,3,3;625/258003075340947456:0,3,3,3;-125/74196962843148288:0,3,3,4;7/140149818703724544:2,3,3,3;-625/97026797564116992:3,3,3,3;175/140149818703724544:3,3,3,4;-625/55861019851294556540928:0,0,0,0,0;51875/148962719603452150775808:0,0,0,0,3;-7/613015307010091155456:0,0,0,2,3;625/37446636401068916736:0,0,0,3,3;-175/613015307010091155456:0,0,0,3,4;-53/204338435670030385152:0,0,2,3,3;104375/919522960515136733184:0,0,3,3,3;-1325/204338435670030385152:0,0,3,3,4;-1/2064024602727579648:0,2,3,3,3;23125/102169217835015192576:0,3,3,3,3;-25/2064024602727579648:0,3,3,3,4;-5/840898912222347264:2,3,3,3,3;3125/7568090210001125376:3,3,3,3,3;-125/840898912222347264:3,3,3,3,4;-21875/4021993429293208070946816:0,0,0,0,0,3;-11875/111722039702589113081856:0,0,0,0,3,3;-1/919522960515136733184:0,0,0,2,3,3;-4375/12413559966954345897984:0,0,0,3,3,3;-25/919522960515136733184:0,0,0,3,3,4;625/1379284440772705099776:0,0,3,3,3,3;1/11352135315001688064:0,2,3,3,3,3;-625/68112811890010128384:0,3,3,3,3,3;25/11352135315001688064:0,3,3,3,3,4;-625/3016495071969906053210112:0,0,0,0,0,3,3;-625/167583059553883669622784:0,0,0,0,3,3,3;-625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_38_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_28 partial_sum_37)=partial_sum_38 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_38_value (v : ℕ→ℂ) :
    eval v partial_sum_38=eval v product_28+eval v partial_sum_37 := by
  rw [←partial_sum_38_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_39 : Poly := rational_polynomial% "-151875/384498816745472:;23125/7786101039095808:0;-27/96124704186368:2;-625/22182624043008:3;-675/96124704186368:4;-190625/2522696736667041792:0,0;-149/15572202078191616:0,2;-98125/280299637407449088:0,3;-3725/15572202078191616:0,4;1/216280584419328:2,3;135625/31144404156383232:3,3;25/216280584419328:3,4;-26875/51084608917507596288:0,0,0;-59/1261348368333520896:0,0,2;-368125/22704270630003376128:0,0,3;-1475/1261348368333520896:0,0,4;-1/1960137324527616:0,2,3;-78125/1261348368333520896:0,3,3;-25/1960137324527616:0,3,4;53/10381468052127744:2,3,3;-26875/280299637407449088:3,3,3;1325/10381468052127744:3,3,4;625/57470185032196045824:0,0,0,0;1/2838033828750422016:0,0,0,2;55625/229880740128784183296:0,0,0,3;25/2838033828750422016:0,0,0,4;-1/873241178077052928:0,0,2,3;64375/102169217835015192576:0,0,3,3;-25/873241178077052928:0,0,3,4;-1/1261348368333520896:0,2,3,3;14375/11352135315001688064:0,3,3,3;-25/1261348368333520896:0,3,3,4;5/70074909351862272:2,3,3,3;-4375/1261348368333520896:3,3,3,3;125/70074909351862272:3,3,3,4;-625/55861019851294556540928:0,0,0,0,0;-4375/148962719603452150775808:0,0,0,0,3;-7/613015307010091155456:0,0,0,2,3;49375/4137853322318115299328:0,0,0,3,3;-175/613015307010091155456:0,0,0,3,4;1/204338435670030385152:0,0,2,3,3;38125/459761480257568366592:0,0,3,3,3;25/204338435670030385152:0,0,3,3,4;43/22704270630003376128:0,2,3,3,3;3125/51084608917507596288:0,3,3,3,3;1075/22704270630003376128:0,3,3,3,4;-5/840898912222347264:2,3,3,3,3;3125/7568090210001125376:3,3,3,3,3;-125/840898912222347264:3,3,3,3,4;-21875/4021993429293208070946816:0,0,0,0,0,3;-11875/111722039702589113081856:0,0,0,0,3,3;-1/919522960515136733184:0,0,0,2,3,3;-4375/12413559966954345897984:0,0,0,3,3,3;-25/919522960515136733184:0,0,0,3,3,4;625/1379284440772705099776:0,0,3,3,3,3;1/11352135315001688064:0,2,3,3,3,3;-625/68112811890010128384:0,3,3,3,3,3;25/11352135315001688064:0,3,3,3,3,4;-625/3016495071969906053210112:0,0,0,0,0,3,3;-625/167583059553883669622784:0,0,0,0,3,3,3;-625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_39_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_27 partial_sum_38)=partial_sum_39 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_39_value (v : ℕ→ℂ) :
    eval v partial_sum_39=eval v product_27+eval v partial_sum_38 := by
  rw [←partial_sum_39_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_40 : Poly := rational_polynomial% "-16875/34954437885952:;45625/7786101039095808:0;-63/192249408372736:2;-4375/288374112559104:3;-1575/192249408372736:4;-168125/2522696736667041792:0,0;-67/7786101039095808:0,2;21875/280299637407449088:0,3;-1675/7786101039095808:0,4;23/1730244675354624:2,3;18125/2831309468762112:3,3;575/1730244675354624:3,4;-625/714470054790316032:0,0,0;-35/1261348368333520896:0,0,2;-566875/22704270630003376128:0,0,3;-875/1261348368333520896:0,0,4;-7/25481785218859008:0,2,3;-4375/39417136510422528:0,3,3;-175/25481785218859008:0,3,4;5/798574465548288:2,3,3;-45625/280299637407449088:3,3,3;125/798574465548288:3,3,4;4375/344821110193176274944:0,0,0,0;1/2838033828750422016:0,0,0,2;18125/70732535424241287168:0,0,0,3;25/2838033828750422016:0,0,0,4;-7/2838033828750422016:0,0,2,3;49375/102169217835015192576:0,0,3,3;-175/2838033828750422016:0,0,3,4;-31/1261348368333520896:0,2,3,3;625/1419016914375211008:0,3,3,3;-775/1261348368333520896:0,3,3,4;-5/140149818703724544:2,3,3,3;-625/1261348368333520896:3,3,3,3;-125/140149818703724544:3,3,3,4;-625/55861019851294556540928:0,0,0,0,0;625/13542065418495650070528:0,0,0,0,3;-7/613015307010091155456:0,0,0,2,3;625/47021060480887673856:0,0,0,3,3;-175/613015307010091155456:0,0,0,3,4;-1/12019907980590022656:0,0,2,3,3;21875/229880740128784183296:0,0,3,3,3;-25/12019907980590022656:0,0,3,3,4;7/22704270630003376128:0,2,3,3,3;4375/25542304458753798144:0,3,3,3,3;175/22704270630003376128:0,3,3,3,4;-1/76445355656577024:2,3,3,3,3;625/688008200909193216:3,3,3,3,3;-25/76445355656577024:3,3,3,3,4;-21875/4021993429293208070946816:0,0,0,0,0,3;-11875/111722039702589113081856:0,0,0,0,3,3;-1/919522960515136733184:0,0,0,2,3,3;-4375/12413559966954345897984:0,0,0,3,3,3;-25/919522960515136733184:0,0,0,3,3,4;625/1379284440772705099776:0,0,3,3,3,3;1/11352135315001688064:0,2,3,3,3,3;-625/68112811890010128384:0,3,3,3,3,3;25/11352135315001688064:0,3,3,3,3,4;-625/3016495071969906053210112:0,0,0,0,0,3,3;-625/167583059553883669622784:0,0,0,0,3,3,3;-625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_40_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_26 partial_sum_39)=partial_sum_40 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_40_value (v : ℕ→ℂ) :
    eval v partial_sum_40=eval v product_26+eval v partial_sum_39 := by
  rw [←partial_sum_40_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_41 : Poly := rational_polynomial% "-16875/34954437885952:;45625/7786101039095808:0;-63/192249408372736:2;-4375/288374112559104:3;-1575/192249408372736:4;-168125/2522696736667041792:0,0;-67/7786101039095808:0,2;21875/280299637407449088:0,3;-1675/7786101039095808:0,4;23/1730244675354624:2,3;18125/2831309468762112:3,3;575/1730244675354624:3,4;-625/714470054790316032:0,0,0;-35/1261348368333520896:0,0,2;-566875/22704270630003376128:0,0,3;-875/1261348368333520896:0,0,4;-7/25481785218859008:0,2,3;-4375/39417136510422528:0,3,3;-175/25481785218859008:0,3,4;5/798574465548288:2,3,3;-45625/280299637407449088:3,3,3;125/798574465548288:3,3,4;4375/344821110193176274944:0,0,0,0;1/2838033828750422016:0,0,0,2;18125/70732535424241287168:0,0,0,3;25/2838033828750422016:0,0,0,4;-7/2838033828750422016:0,0,2,3;49375/102169217835015192576:0,0,3,3;-175/2838033828750422016:0,0,3,4;-31/1261348368333520896:0,2,3,3;625/1419016914375211008:0,3,3,3;-775/1261348368333520896:0,3,3,4;-5/140149818703724544:2,3,3,3;-625/1261348368333520896:3,3,3,3;-125/140149818703724544:3,3,3,4;-625/55861019851294556540928:0,0,0,0,0;625/13542065418495650070528:0,0,0,0,3;-7/613015307010091155456:0,0,0,2,3;625/47021060480887673856:0,0,0,3,3;-175/613015307010091155456:0,0,0,3,4;-1/12019907980590022656:0,0,2,3,3;21875/229880740128784183296:0,0,3,3,3;-25/12019907980590022656:0,0,3,3,4;7/22704270630003376128:0,2,3,3,3;4375/25542304458753798144:0,3,3,3,3;175/22704270630003376128:0,3,3,3,4;-1/76445355656577024:2,3,3,3,3;625/688008200909193216:3,3,3,3,3;-25/76445355656577024:3,3,3,3,4;-21875/4021993429293208070946816:0,0,0,0,0,3;-11875/111722039702589113081856:0,0,0,0,3,3;-1/919522960515136733184:0,0,0,2,3,3;-4375/12413559966954345897984:0,0,0,3,3,3;-25/919522960515136733184:0,0,0,3,3,4;625/1379284440772705099776:0,0,3,3,3,3;1/11352135315001688064:0,2,3,3,3,3;-625/68112811890010128384:0,3,3,3,3,3;25/11352135315001688064:0,3,3,3,3,4;-625/3016495071969906053210112:0,0,0,0,0,3,3;-625/167583059553883669622784:0,0,0,0,3,3,3;-625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_41_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_40 product_1)=partial_sum_41 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_41_value (v : ℕ→ℂ) :
    eval v partial_sum_41=eval v partial_sum_40+eval v product_1 := by
  rw [←partial_sum_41_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_42 : Poly := rational_polynomial% "-16875/34954437885952:;45625/7786101039095808:0;-63/192249408372736:2;-4375/288374112559104:3;-1575/192249408372736:4;-168125/2522696736667041792:0,0;-67/7786101039095808:0,2;21875/280299637407449088:0,3;-1675/7786101039095808:0,4;23/1730244675354624:2,3;18125/2831309468762112:3,3;575/1730244675354624:3,4;-625/714470054790316032:0,0,0;-35/1261348368333520896:0,0,2;-566875/22704270630003376128:0,0,3;-875/1261348368333520896:0,0,4;-7/25481785218859008:0,2,3;-4375/39417136510422528:0,3,3;-175/25481785218859008:0,3,4;5/798574465548288:2,3,3;-45625/280299637407449088:3,3,3;125/798574465548288:3,3,4;4375/344821110193176274944:0,0,0,0;1/2838033828750422016:0,0,0,2;18125/70732535424241287168:0,0,0,3;25/2838033828750422016:0,0,0,4;-7/2838033828750422016:0,0,2,3;49375/102169217835015192576:0,0,3,3;-175/2838033828750422016:0,0,3,4;-31/1261348368333520896:0,2,3,3;625/1419016914375211008:0,3,3,3;-775/1261348368333520896:0,3,3,4;-5/140149818703724544:2,3,3,3;-625/1261348368333520896:3,3,3,3;-125/140149818703724544:3,3,3,4;-625/55861019851294556540928:0,0,0,0,0;625/13542065418495650070528:0,0,0,0,3;-7/613015307010091155456:0,0,0,2,3;625/47021060480887673856:0,0,0,3,3;-175/613015307010091155456:0,0,0,3,4;-1/12019907980590022656:0,0,2,3,3;21875/229880740128784183296:0,0,3,3,3;-25/12019907980590022656:0,0,3,3,4;7/22704270630003376128:0,2,3,3,3;4375/25542304458753798144:0,3,3,3,3;175/22704270630003376128:0,3,3,3,4;-1/76445355656577024:2,3,3,3,3;625/688008200909193216:3,3,3,3,3;-25/76445355656577024:3,3,3,3,4;-21875/4021993429293208070946816:0,0,0,0,0,3;-11875/111722039702589113081856:0,0,0,0,3,3;-1/919522960515136733184:0,0,0,2,3,3;-4375/12413559966954345897984:0,0,0,3,3,3;-25/919522960515136733184:0,0,0,3,3,4;625/1379284440772705099776:0,0,3,3,3,3;1/11352135315001688064:0,2,3,3,3,3;-625/68112811890010128384:0,3,3,3,3,3;25/11352135315001688064:0,3,3,3,3,4;-625/3016495071969906053210112:0,0,0,0,0,3,3;-625/167583059553883669622784:0,0,0,0,3,3,3;-625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_42_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_41 product_1)=partial_sum_42 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_42_value (v : ℕ→ℂ) :
    eval v partial_sum_42=eval v partial_sum_41+eval v product_1 := by
  rw [←partial_sum_42_checked, eval_add]
compact_certificate_declaration noncomputable def product_32 : Poly := rational_polynomial% "65625/384498816745472:;68125/31144404156383232:0;-18125/32490150014992384:1;63/192249408372736:2;81875/3460489350709248:3;1575/192249408372736:4;-60625/2522696736667041792:0,0;-15625/2631702151214383104:0,1;67/7786101039095808:0,2;3125/5190734026063872:0,3;1675/7786101039095808:0,4;-3125/292411350134931456:1,3;-23/1730244675354624:2,3;-78125/31144404156383232:3,3;-575/1730244675354624:3,4;-71875/68112811890010128384:0,0,0;625/13322992140522814464:0,0,1;35/1261348368333520896:0,0,2;195625/22704270630003376128:0,0,3;875/1261348368333520896:0,0,4;11875/15790212907286298624:0,1,3;7/25481785218859008:0,2,3;-4375/2522696736667041792:0,3,3;175/25481785218859008:0,3,4;625/82240692225449472:1,3,3;-5/798574465548288:2,3,3;-625/3185223152357376:3,3,3;-125/798574465548288:3,3,4;-625/4137853322318115299328:0,0,0,0;625/1438883151176463962112:0,0,0,1;-1/2838033828750422016:0,0,0,2;625/76626913376261394432:0,0,0,3;-25/2838033828750422016:0,0,0,4;-26875/1918510868235285282816:0,0,1,3;7/2838033828750422016:0,0,2,3;-3125/3929585301346738176:0,0,3,3;175/2838033828750422016:0,0,3,4;3125/426335748496730062848:0,1,3,3;31/1261348368333520896:0,2,3,3;-81875/22704270630003376128:0,3,3,3;775/1261348368333520896:0,3,3,4;3125/23685319360929447936:1,3,3,3;5/140149818703724544:2,3,3,3;625/31144404156383232:3,3,3,3;125/140149818703724544:3,3,3,4;3125/27930509925647278270464:0,0,0,0,0;3125/1432333842340886065152:0,0,0,0,3;-23125/103599586884705405272064:0,0,0,1,3;7/613015307010091155456:0,0,0,2,3;-11875/4137853322318115299328:0,0,0,3,3;175/613015307010091155456:0,0,0,3,4;-4375/1438883151176463962112:0,0,1,3,3;1/12019907980590022656:0,0,2,3,3;-33125/167185992820933951488:0,0,3,3,3;25/12019907980590022656:0,0,3,3,4;-625/142111916165576687616:0,1,3,3,3;-7/22704270630003376128:0,2,3,3,3;-30625/102169217835015192576:0,3,3,3,3;-175/22704270630003376128:0,3,3,3,4;-625/71055958082788343808:1,3,3,3,3;1/76445355656577024:2,3,3,3,3;625/2522696736667041792:3,3,3,3,3;25/76445355656577024:3,3,3,3,4;19375/2010996714646604035473408:0,0,0,0,0,3;3125/17188006108090632781824:0,0,0,0,3,3;-3125/310798760654116215816192:0,0,0,1,3,3;1/919522960515136733184:0,0,0,2,3,3;11875/49654239867817383591936:0,0,0,3,3,3;25/919522960515136733184:0,0,0,3,3,4;-625/5755532604705855848448:0,0,1,3,3,3;-3125/501557978462801854464:0,0,3,3,3,3;-625/3837021736470570565632:0,1,3,3,3,3;-1/11352135315001688064:0,2,3,3,3,3;-625/68112811890010128384:0,3,3,3,3,3;-25/11352135315001688064:0,3,3,3,3,4;-625/22704270630003376128:3,3,3,3,3,3;625/3016495071969906053210112:0,0,0,0,0,3,3;625/167583059553883669622784:0,0,0,0,3,3,3;625/37240679900863037693952:0,0,0,3,3,3,3"
compact_certificate_declaration theorem product_32_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_3 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_4 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_5 n_c7_0) [([],(0:ℚ))])))=product_32 := by
  decide +kernel
compact_certificate_declaration theorem product_32_value (v : ℕ→ℂ) :
    eval v product_32=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_3 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_4 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_5 n_c7_0) [([],(0:ℚ))]))) := by
  rw [←product_32_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_43 : Poly := rational_polynomial% "-1875/6007794011648:;250625/31144404156383232:0;-18125/32490150014992384:1;29375/3460489350709248:3;-38125/420449456111173632:0,0;-15625/2631702151214383104:0,1;190625/280299637407449088:0,3;-3125/292411350134931456:1,3;60625/15572202078191616:3,3;-394375/204338435670030385152:0,0,0;625/13322992140522814464:0,0,1;-625/38222677828288512:0,0,3;11875/15790212907286298624:0,1,3;-21875/194053595128233984:0,3,3;625/82240692225449472:1,3,3;-100625/280299637407449088:3,3,3;51875/4137853322318115299328:0,0,0,0;625/1438883151176463962112:0,0,0,1;243125/919522960515136733184:0,0,0,3;-26875/1918510868235285282816:0,0,1,3;-625/2003317996765003776:0,0,3,3;3125/426335748496730062848:0,1,3,3;-71875/22704270630003376128:0,3,3,3;3125/23685319360929447936:1,3,3,3;49375/2522696736667041792:3,3,3,3;625/6206779983477172948992:0,0,0,0,0;36875/16551413289272461197312:0,0,0,0,3;-23125/103599586884705405272064:0,0,0,1,3;14375/1379284440772705099776:0,0,0,3,3;-4375/1438883151176463962112:0,0,1,3,3;-63125/613015307010091155456:0,0,3,3,3;-625/142111916165576687616:0,1,3,3,3;-4375/34056405945005064192:0,3,3,3,3;-625/71055958082788343808:1,3,3,3,3;4375/3784045105000562688:3,3,3,3,3;625/148962719603452150775808:0,0,0,0,0,3;625/8275706644636230598656:0,0,0,0,3,3;-3125/310798760654116215816192:0,0,0,1,3,3;-625/5517137763090820399104:0,0,0,3,3,3;-625/5755532604705855848448:0,0,1,3,3,3;-625/108179171825310203904:0,0,3,3,3,3;-625/3837021736470570565632:0,1,3,3,3,3;-625/34056405945005064192:0,3,3,3,3,3;-625/22704270630003376128:3,3,3,3,3,3"
compact_certificate_declaration theorem partial_sum_43_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_42 product_32)=partial_sum_43 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_43_value (v : ℕ→ℂ) :
    eval v partial_sum_43=eval v partial_sum_42+eval v product_32 := by
  rw [←partial_sum_43_checked, eval_add]
compact_certificate_declaration noncomputable def product_33 : Poly := rational_polynomial% "1875/6007794011648:;-250625/31144404156383232:0;18125/32490150014992384:1;-29375/3460489350709248:3;38125/420449456111173632:0,0;15625/2631702151214383104:0,1;-190625/280299637407449088:0,3;3125/292411350134931456:1,3;-60625/15572202078191616:3,3;394375/204338435670030385152:0,0,0;-625/13322992140522814464:0,0,1;625/38222677828288512:0,0,3;-11875/15790212907286298624:0,1,3;21875/194053595128233984:0,3,3;-625/82240692225449472:1,3,3;100625/280299637407449088:3,3,3;-51875/4137853322318115299328:0,0,0,0;-625/1438883151176463962112:0,0,0,1;-243125/919522960515136733184:0,0,0,3;26875/1918510868235285282816:0,0,1,3;625/2003317996765003776:0,0,3,3;-3125/426335748496730062848:0,1,3,3;71875/22704270630003376128:0,3,3,3;-3125/23685319360929447936:1,3,3,3;-49375/2522696736667041792:3,3,3,3;-625/6206779983477172948992:0,0,0,0,0;-36875/16551413289272461197312:0,0,0,0,3;23125/103599586884705405272064:0,0,0,1,3;-14375/1379284440772705099776:0,0,0,3,3;4375/1438883151176463962112:0,0,1,3,3;63125/613015307010091155456:0,0,3,3,3;625/142111916165576687616:0,1,3,3,3;4375/34056405945005064192:0,3,3,3,3;625/71055958082788343808:1,3,3,3,3;-4375/3784045105000562688:3,3,3,3,3;-625/148962719603452150775808:0,0,0,0,0,3;-625/8275706644636230598656:0,0,0,0,3,3;3125/310798760654116215816192:0,0,0,1,3,3;625/5517137763090820399104:0,0,0,3,3,3;625/5755532604705855848448:0,0,1,3,3,3;625/108179171825310203904:0,0,3,3,3,3;625/3837021736470570565632:0,1,3,3,3,3;625/34056405945005064192:0,3,3,3,3,3;625/22704270630003376128:3,3,3,3,3,3"
compact_certificate_declaration theorem product_33_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_2 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_3 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_4 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_5 n_c9_0) [([],(0:ℚ))]))))=product_33 := by
  decide +kernel
compact_certificate_declaration theorem product_33_value (v : ℕ→ℂ) :
    eval v product_33=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_2 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_3 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_4 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_5 n_c9_0) [([],(0:ℚ))])))) := by
  rw [←product_33_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_44 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_44_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_43 product_33)=partial_sum_44 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_44_value (v : ℕ→ℂ) :
    eval v partial_sum_44=eval v partial_sum_43+eval v product_33 := by
  rw [←partial_sum_44_checked, eval_add]
compact_certificate_declaration noncomputable def e5 : Poly := partial_sum_44
compact_certificate_declaration theorem checked_5 : checkZero e5=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_5 (y z w a b : ℂ) :
    (certificate y z w a b)[5]?=some 0 := by
  change some (((((((((c0_0 y z w a b)*(c1_5 y z w a b))+(((c0_1 y z w a b)*(c1_4 y z w a b))+(((c0_2 y z w a b)*(c1_3 y z w a b))+(((c0_3 y z w a b)*(c1_2 y z w a b))+(((c0_4 y z w a b)*(c1_1 y z w a b))+(((c0_5 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_3 y z w a b)*(c7_2 y z w a b))+(((c6_4 y z w a b)*(c7_1 y z w a b))+(((c6_5 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_2 y z w a b)*(c9_3 y z w a b))+(((c8_3 y z w a b)*(c9_2 y z w a b))+(((c8_4 y z w a b)*(c9_1 y z w a b))+(((c8_5 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e5 checked_5
  simp only [e5, eval_add, eval_mul, eval_scale, eval_pow, product_26_value, product_27_value, product_28_value, product_29_value, product_30_value, product_31_value, partial_sum_35_value, partial_sum_36_value, partial_sum_37_value, partial_sum_38_value, partial_sum_39_value, partial_sum_40_value, product_1_value, partial_sum_41_value, partial_sum_42_value, product_32_value, partial_sum_43_value, product_33_value, partial_sum_44_value, n_c0_0_value y z w a b 0, n_c0_1_value y z w a b 0, n_c0_2_value y z w a b 0, n_c0_3_value y z w a b 0, n_c0_4_value y z w a b 0, n_c0_5_value y z w a b 0, n_c1_0_value y z w a b 0, n_c1_1_value y z w a b 0, n_c1_2_value y z w a b 0, n_c1_3_value y z w a b 0, n_c1_4_value y z w a b 0, n_c1_5_value y z w a b 0, n_c6_3_value y z w a b 0, n_c6_4_value y z w a b 0, n_c6_5_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_2_value y z w a b 0, n_c8_3_value y z w a b 0, n_c8_4_value y z w a b 0, n_c8_5_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_5
compact_certificate_declaration noncomputable def product_34 : Poly := rational_polynomial% "-55625/20762936104255488:0;-3/192249408372736:2;-1875/768997633490944:3;-75/192249408372736:4;625/64684531709411328:0,0;-5/5190734026063872:0,2;-625/11679151558643712:0,3;-125/5190734026063872:0,4;1/576748225118208:2,3;3125/6920978701418496:3,3;25/576748225118208:3,4;33125/136225623780020256768:0,0,0;-1/105112364027793408:0,0,2;45625/7568090210001125376:0,0,3;-25/105112364027793408:0,0,4;5/93433212469149696:0,2,3;625/52556182013896704:0,3,3;125/93433212469149696:0,3,4;1/2306992900472832:2,3,3;625/31144404156383232:3,3,3;25/2306992900472832:3,3,4;-3125/1379284440772705099776:0,0,0,0;-3125/204338435670030385152:0,0,0,3;1/840898912222347264:0,0,2,3;11875/136225623780020256768:0,0,3,3;25/840898912222347264:0,0,3,4;7/420449456111173632:0,2,3,3;-4375/15136180420002250752:0,3,3,3;175/420449456111173632:0,3,3,4;1/186866424938299392:2,3,3,3;625/840898912222347264:3,3,3,3;25/186866424938299392:3,3,3,4;-3125/33102826578544922394624:0,0,0,0,3;-4375/3678091842060546932736:0,0,0,3,3;1/15136180420002250752:0,0,2,3,3;-3125/408676871340060770304:0,0,3,3,3;25/15136180420002250752:0,0,3,3,4;1/1681797824444694528:0,2,3,3,3;-625/15136180420002250752:0,3,3,3,3;25/1681797824444694528:0,3,3,3,4"
compact_certificate_declaration theorem product_34_checked :
    mulShort n_c0_1 n_c1_5=product_34 := by
  decide +kernel
compact_certificate_declaration theorem product_34_value (v : ℕ→ℂ) :
    eval v product_34=eval v n_c0_1*eval v n_c1_5 := by
  rw [←product_34_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_35 : Poly := rational_polynomial% "-50625/768997633490944:;51875/20762936104255488:0;-7/192249408372736:2;-38125/6920978701418496:3;-175/192249408372736:4;-66875/2522696736667041792:0,0;-1/1197861698322432:0,2;3125/560599274814898176:0,3;-25/1197861698322432:0,4;-1/576748225118208:2,3;625/2831309468762112:3,3;-25/576748225118208:3,4;-19375/102169217835015192576:0,0,0;-1/210224728055586816:0,0,2;-153125/22704270630003376128:0,0,3;-25/210224728055586816:0,0,4;-5/43123021139607552:0,2,3;-3125/296787851372593152:0,3,3;-125/43123021139607552:0,3,4;31/62288808312766464:2,3,3;-11875/560599274814898176:3,3,3;775/62288808312766464:3,3,4;625/153253826752522788864:0,0,0,0;625/19156728344065348608:0,0,0,3;-19/15136180420002250752:0,0,2,3;-14375/136225623780020256768:0,0,3,3;-475/15136180420002250752:0,0,3,4;-5/420449456111173632:0,2,3,3;3125/7568090210001125376:0,3,3,3;-125/420449456111173632:0,3,3,4;5/186866424938299392:2,3,3,3;-3125/1681797824444694528:3,3,3,3;125/186866424938299392:3,3,3,4;625/3678091842060546932736:0,0,0,0,3;625/334371985641867902976:0,0,0,3,3;-1/22704270630003376128:0,0,2,3,3;3125/408676871340060770304:0,0,3,3,3;-25/22704270630003376128:0,0,3,3,4;-1/2522696736667041792:0,2,3,3,3;625/15136180420002250752:0,3,3,3,3;-25/2522696736667041792:0,3,3,3,4"
compact_certificate_declaration theorem product_35_checked :
    mulShort n_c0_2 n_c1_4=product_35 := by
  decide +kernel
compact_certificate_declaration theorem product_35_value (v : ℕ→ℂ) :
    eval v product_35=eval v n_c0_2*eval v n_c1_4 := by
  rw [←product_35_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_36 : Poly := rational_polynomial% "65625/768997633490944:;-344375/124577616625532928:0;-27/1537995266981888:2;-6875/1258359763894272:3;-675/1537995266981888:4;146875/3363595648889389056:0,0;1/1153496450236416:0,2;18125/140149818703724544:0,3;25/1153496450236416:0,4;-31/4613985800945664:2,3;-51875/62288808312766464:3,3;-775/4613985800945664:3,4;18125/48079631922360090624:0,0,0;61/3363595648889389056:0,0,2;3125/873241178077052928:0,0,3;1525/3363595648889389056:0,0,4;25/560599274814898176:0,2,3;625/124577616625532928:0,3,3;625/560599274814898176:0,3,4;-59/124577616625532928:2,3,3;4375/86246042279215104:3,3,3;-1475/124577616625532928:3,3,4;-30625/7356183684121093865472:0,0,0,0;1/17028202972502532096:0,0,0,2;-26875/817353742680121540608:0,0,0,3;25/17028202972502532096:0,0,0,4;47/90817082520013504512:0,0,2,3;-4375/31436682410773905408:0,0,3,3;1175/90817082520013504512:0,0,3,4;-1/280299637407449088:0,2,3,3;-625/15136180420002250752:0,3,3,3;-25/280299637407449088:0,3,3,4;1/86246042279215104:2,3,3,3;625/1261348368333520896:3,3,3,3;25/86246042279215104:3,3,3,4;-4375/223444079405178226163712:0,0,0,0,0;-45625/198616959471269534367744:0,0,0,0,3;1/408676871340060770304:0,0,0,2,3;-3125/5517137763090820399104:0,0,0,3,3;25/408676871340060770304:0,0,0,3,4;-1/136225623780020256768:0,0,2,3,3;-625/90817082520013504512:0,0,3,3,3;-25/136225623780020256768:0,0,3,3,4;-1/5045393473334083584:0,2,3,3,3;-625/136225623780020256768:0,3,3,3,3;-25/5045393473334083584:0,3,3,3,4;1/1681797824444694528:2,3,3,3,3;-625/15136180420002250752:3,3,3,3,3;25/1681797824444694528:3,3,3,3,4;-4375/5362657905724277427929088:0,0,0,0,0,3;-625/198616959471269534367744:0,0,0,0,3,3;4375/66205653157089844789248:0,0,0,3,3,3;625/2452061228040364621824:0,0,3,3,3,3"
compact_certificate_declaration theorem product_36_checked :
    mulShort n_c0_3 n_c1_3=product_36 := by
  decide +kernel
compact_certificate_declaration theorem product_36_value (v : ℕ→ℂ) :
    eval v product_36=eval v n_c0_3*eval v n_c1_3 := by
  rw [←product_36_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_37 : Poly := rational_polynomial% "-19375/31144404156383232:0;108125/5045393473334083584:0,0;1/5190734026063872:0,2;625/7786101039095808:0,3;25/5190734026063872:0,4;-625/1596394028672112384:0,0,0;1/420449456111173632:0,0,2;625/873241178077052928:0,0,3;25/420449456111173632:0,0,4;1/25481785218859008:0,2,3;19375/5045393473334083584:0,3,3;25/25481785218859008:0,3,4;-38125/33102826578544922394624:0,0,0,0;-115625/3678091842060546932736:0,0,0,3;5/22704270630003376128:0,0,2,3;-33125/408676871340060770304:0,0,3,3;125/22704270630003376128:0,0,3,4;5/2522696736667041792:0,2,3,3;-625/3492964712308211712:0,3,3,3;125/2522696736667041792:0,3,3,4;625/55861019851294556540928:0,0,0,0,0;14375/99308479735634767183872:0,0,0,0,3;625/5517137763090820399104:0,0,0,3,3;-3125/1226030614020182310912:0,0,3,3,3;625/1340664476431069356982272:0,0,0,0,0,3;625/74481359801726075387904:0,0,0,0,3,3;625/16551413289272461197312:0,0,0,3,3,3"
compact_certificate_declaration theorem product_37_checked :
    mulShort n_c0_4 n_c1_2=product_37 := by
  decide +kernel
compact_certificate_declaration theorem product_37_value (v : ℕ→ℂ) :
    eval v product_37=eval v n_c0_4*eval v n_c1_2 := by
  rw [←product_37_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_38 : Poly := rational_polynomial% "625/3664047547809792:0;-101875/5045393473334083584:0,0;-1/15572202078191616:0,2;-3125/93433212469149696:0,3;-25/15572202078191616:0,4;4375/17028202972502532096:0,0,0;-1/1261348368333520896:0,0,2;11875/5676067657500844032:0,0,3;-25/1261348368333520896:0,0,4;625/5045393473334083584:0,3,3;625/1379284440772705099776:0,0,0,0;-3125/282930141696965148672:0,0,0,3;1/11352135315001688064:0,0,2,3;625/7568090210001125376:0,0,3,3;25/11352135315001688064:0,0,3,4;1/1261348368333520896:0,2,3,3;625/3784045105000562688:0,3,3,3;25/1261348368333520896:0,3,3,4;-625/16551413289272461197312:0,0,0,0,3;-4375/2546371275272686338048:0,0,0,3,3;-23125/3678091842060546932736:0,0,3,3,3;-625/446888158810356452327424:0,0,0,0,3,3;-625/24827119933908691795968:0,0,0,3,3,3;-625/5517137763090820399104:0,0,3,3,3,3"
compact_certificate_declaration theorem product_38_checked :
    mulShort n_c0_5 n_c1_1=product_38 := by
  decide +kernel
compact_certificate_declaration theorem product_38_value (v : ℕ→ℂ) :
    eval v product_38=eval v n_c0_5*eval v n_c1_1 := by
  rw [←product_38_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_39 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:3;0/1:0,0;0/1:0,3;0/1:3,3;0/1:0,0,0;0/1:0,0,3;0/1:0,3,3"
compact_certificate_declaration theorem product_39_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_6 n_c1_0=product_39 := by
  decide +kernel
compact_certificate_declaration theorem product_39_value (v : ℕ→ℂ) :
    eval v product_39=eval v n_c0_6*eval v n_c1_0 := by
  rw [←product_39_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_45 : Poly := rational_polynomial% "0/1:0;0/1:3;0/1:0,0;0/1:0,3;0/1:3,3;0/1:0,0,0;0/1:0,0,3;0/1:0,3,3"
compact_certificate_declaration theorem partial_sum_45_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_39 [([],(0:ℚ))])=partial_sum_45 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_45_value (v : ℕ→ℂ) :
    eval v partial_sum_45=eval v product_39+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_45_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_46 : Poly := rational_polynomial% "625/3664047547809792:0;0/1:3;-101875/5045393473334083584:0,0;-1/15572202078191616:0,2;-3125/93433212469149696:0,3;-25/15572202078191616:0,4;0/1:3,3;4375/17028202972502532096:0,0,0;-1/1261348368333520896:0,0,2;11875/5676067657500844032:0,0,3;-25/1261348368333520896:0,0,4;625/5045393473334083584:0,3,3;625/1379284440772705099776:0,0,0,0;-3125/282930141696965148672:0,0,0,3;1/11352135315001688064:0,0,2,3;625/7568090210001125376:0,0,3,3;25/11352135315001688064:0,0,3,4;1/1261348368333520896:0,2,3,3;625/3784045105000562688:0,3,3,3;25/1261348368333520896:0,3,3,4;-625/16551413289272461197312:0,0,0,0,3;-4375/2546371275272686338048:0,0,0,3,3;-23125/3678091842060546932736:0,0,3,3,3;-625/446888158810356452327424:0,0,0,0,3,3;-625/24827119933908691795968:0,0,0,3,3,3;-625/5517137763090820399104:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_46_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_38 partial_sum_45)=partial_sum_46 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_46_value (v : ℕ→ℂ) :
    eval v partial_sum_46=eval v product_38+eval v partial_sum_45 := by
  rw [←partial_sum_46_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_47 : Poly := rational_polynomial% "-3125/6920978701418496:0;0/1:3;3125/2522696736667041792:0,0;1/7786101039095808:0,2;4375/93433212469149696:0,3;25/7786101039095808:0,4;0/1:3,3;-625/4644055356137054208:0,0,0;1/630674184166760448:0,0,2;625/222590888529444864:0,0,3;25/630674184166760448:0,0,4;1/25481785218859008:0,2,3;625/157668546041690112:0,3,3;25/25481785218859008:0,3,4;-23125/33102826578544922394624:0,0,0,0;-78125/1839045921030273466368:0,0,0,3;7/22704270630003376128:0,0,2,3;625/408676871340060770304:0,0,3,3;175/22704270630003376128:0,0,3,4;7/2522696736667041792:0,2,3,3;-625/45408541260006752256:0,3,3,3;175/2522696736667041792:0,3,3,4;625/55861019851294556540928:0,0,0,0,0;625/5841675278566751010816:0,0,0,0,3;-3125/1947225092855583670272:0,0,0,3,3;-625/70732535424241287168:0,0,3,3,3;625/1340664476431069356982272:0,0,0,0,0,3;3125/446888158810356452327424:0,0,0,0,3,3;625/49654239867817383591936:0,0,0,3,3,3;-625/5517137763090820399104:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_47_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_37 partial_sum_46)=partial_sum_47 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_47_value (v : ℕ→ℂ) :
    eval v partial_sum_47=eval v product_37+eval v partial_sum_46 := by
  rw [←partial_sum_47_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_48 : Poly := rational_polynomial% "65625/768997633490944:;-400625/124577616625532928:0;-27/1537995266981888:2;-6875/1258359763894272:3;-675/1537995266981888:4;453125/10090786946668167168:0,0;31/31144404156383232:0,2;49375/280299637407449088:0,3;775/31144404156383232:0,4;-31/4613985800945664:2,3;-51875/62288808312766464:3,3;-775/4613985800945664:3,4;198125/817353742680121540608:0,0,0;199/10090786946668167168:0,0,2;18125/2838033828750422016:0,0,3;4975/10090786946668167168:0,0,4;47/560599274814898176:0,2,3;90625/10090786946668167168:0,3,3;1175/560599274814898176:0,3,4;-59/124577616625532928:2,3,3;4375/86246042279215104:3,3,3;-1475/124577616625532928:3,3,4;-321875/66205653157089844789248:0,0,0,0;1/17028202972502532096:0,0,0,2;-554375/7356183684121093865472:0,0,0,3;25/17028202972502532096:0,0,0,4;25/30272360840004501504:0,0,2,3;-3125/22704270630003376128:0,0,3,3;625/30272360840004501504:0,0,3,4;-1/1261348368333520896:0,2,3,3;-625/11352135315001688064:0,3,3,3;-25/1261348368333520896:0,3,3,4;1/86246042279215104:2,3,3,3;625/1261348368333520896:3,3,3,3;25/86246042279215104:3,3,3,4;-625/74481359801726075387904:0,0,0,0,0;-625/5092742550545372676096:0,0,0,0,3;1/408676871340060770304:0,0,0,2,3;-71875/33102826578544922394624:0,0,0,3,3;25/408676871340060770304:0,0,0,3,4;-1/136225623780020256768:0,0,2,3,3;-115625/7356183684121093865472:0,0,3,3,3;-25/136225623780020256768:0,0,3,3,4;-1/5045393473334083584:0,2,3,3,3;-625/136225623780020256768:0,3,3,3,3;-25/5045393473334083584:0,3,3,3,4;1/1681797824444694528:2,3,3,3,3;-625/15136180420002250752:3,3,3,3,3;25/1681797824444694528:3,3,3,3,4;-625/1787552635241425809309696:0,0,0,0,0,3;625/162504785021947800846336:0,0,0,0,3,3;15625/198616959471269534367744:0,0,0,3,3,3;3125/22068551052363281596416:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_48_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_36 partial_sum_47)=partial_sum_48 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_48_value (v : ℕ→ℂ) :
    eval v partial_sum_48=eval v product_36+eval v partial_sum_47 := by
  rw [←partial_sum_48_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_49 : Poly := rational_polynomial% "1875/96124704186368:;-625/871172144234496:0;-83/1537995266981888:2;-16875/1537995266981888:3;-2075/1537995266981888:4;625/33975713625145344:0,0;5/31144404156383232:0,2;101875/560599274814898176:0,3;125/31144404156383232:0,4;-1/118307328229376:2,3;-38125/62288808312766464:3,3;-25/118307328229376:3,4;14375/272451247560040513536:0,0,0;151/10090786946668167168:0,0,2;-625/1746482356154105856:0,0,3;3775/10090786946668167168:0,0,4;-1/31144404156383232:0,2,3;-15625/10090786946668167168:0,3,3;-25/31144404156383232:0,3,4;1/41525872208510976:2,3,3;33125/1121198549629796352:3,3,3;25/41525872208510976:3,3,4;-51875/66205653157089844789248:0,0,0,0;1/17028202972502532096:0,0,0,2;-314375/7356183684121093865472:0,0,0,3;25/17028202972502532096:0,0,0,4;-1/2328643141538807808:0,0,2,3;-33125/136225623780020256768:0,0,3,3;-25/2328643141538807808:0,0,3,4;-1/78834273020845056:0,2,3,3;625/1746482356154105856:0,3,3,3;-25/78834273020845056:0,3,3,4;43/1121198549629796352:2,3,3,3;-625/458672133939462144:3,3,3,3;1075/1121198549629796352:3,3,3,4;-625/74481359801726075387904:0,0,0,0,0;3125/66205653157089844789248:0,0,0,0,3;1/408676871340060770304:0,0,0,2,3;-625/2068926661159057649664:0,0,0,3,3;25/408676871340060770304:0,0,0,3,4;-7/136225623780020256768:0,0,2,3,3;-59375/7356183684121093865472:0,0,3,3,3;-175/136225623780020256768:0,0,3,3,4;-1/1681797824444694528:0,2,3,3,3;625/17028202972502532096:0,3,3,3,3;-25/1681797824444694528:0,3,3,3,4;1/1681797824444694528:2,3,3,3,3;-625/15136180420002250752:3,3,3,3,3;25/1681797824444694528:3,3,3,3,4;-625/1787552635241425809309696:0,0,0,0,0,3;625/162504785021947800846336:0,0,0,0,3,3;15625/198616959471269534367744:0,0,0,3,3,3;3125/22068551052363281596416:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_49_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_35 partial_sum_48)=partial_sum_49 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_49_value (v : ℕ→ℂ) :
    eval v partial_sum_49=eval v product_35+eval v partial_sum_48 := by
  rw [←partial_sum_49_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_50 : Poly := rational_polynomial% "1875/96124704186368:;-423125/124577616625532928:0;-107/1537995266981888:2;-1875/139817751543808:3;-2675/1537995266981888:4;94375/3363595648889389056:0,0;-25/31144404156383232:0,2;71875/560599274814898176:0,3;-625/31144404156383232:0,4;-31/4613985800945664:2,3;-625/3893050519547904:3,3;-775/4613985800945664:3,4;26875/90817082520013504512:0,0,0;5/917344267878924288:0,0,2;64375/11352135315001688064:0,0,3;125/917344267878924288:0,0,4;1/46716606234574848:0,2,3;104375/10090786946668167168:0,3,3;25/46716606234574848:0,3,4;19/41525872208510976:2,3,3;55625/1121198549629796352:3,3,3;475/41525872208510976:3,3,4;-11875/3894450185711167340544:0,0,0,0;1/17028202972502532096:0,0,0,2;-426875/7356183684121093865472:0,0,0,3;25/17028202972502532096:0,0,0,4;23/30272360840004501504:0,0,2,3;-625/4006635993530007552:0,0,3,3;575/30272360840004501504:0,0,3,4;5/1261348368333520896:0,2,3,3;3125/45408541260006752256:0,3,3,3;125/1261348368333520896:0,3,3,4;49/1121198549629796352:2,3,3,3;-3125/5045393473334083584:3,3,3,3;1225/1121198549629796352:3,3,3,4;-625/74481359801726075387904:0,0,0,0,0;-3125/66205653157089844789248:0,0,0,0,3;1/408676871340060770304:0,0,0,2,3;-49375/33102826578544922394624:0,0,0,3,3;25/408676871340060770304:0,0,0,3,4;1/68112811890010128384:0,0,2,3,3;-115625/7356183684121093865472:0,0,3,3,3;25/68112811890010128384:0,0,3,3,4;-625/136225623780020256768:0,3,3,3,3;1/1681797824444694528:2,3,3,3,3;-625/15136180420002250752:3,3,3,3,3;25/1681797824444694528:3,3,3,3,4;-625/1787552635241425809309696:0,0,0,0,0,3;625/162504785021947800846336:0,0,0,0,3,3;15625/198616959471269534367744:0,0,0,3,3,3;3125/22068551052363281596416:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_50_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_34 partial_sum_49)=partial_sum_50 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_50_value (v : ℕ→ℂ) :
    eval v partial_sum_50=eval v product_34+eval v partial_sum_49 := by
  rw [←partial_sum_50_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_51 : Poly := rational_polynomial% "1875/96124704186368:;-423125/124577616625532928:0;-107/1537995266981888:2;-1875/139817751543808:3;-2675/1537995266981888:4;94375/3363595648889389056:0,0;-25/31144404156383232:0,2;71875/560599274814898176:0,3;-625/31144404156383232:0,4;-31/4613985800945664:2,3;-625/3893050519547904:3,3;-775/4613985800945664:3,4;26875/90817082520013504512:0,0,0;5/917344267878924288:0,0,2;64375/11352135315001688064:0,0,3;125/917344267878924288:0,0,4;1/46716606234574848:0,2,3;104375/10090786946668167168:0,3,3;25/46716606234574848:0,3,4;19/41525872208510976:2,3,3;55625/1121198549629796352:3,3,3;475/41525872208510976:3,3,4;-11875/3894450185711167340544:0,0,0,0;1/17028202972502532096:0,0,0,2;-426875/7356183684121093865472:0,0,0,3;25/17028202972502532096:0,0,0,4;23/30272360840004501504:0,0,2,3;-625/4006635993530007552:0,0,3,3;575/30272360840004501504:0,0,3,4;5/1261348368333520896:0,2,3,3;3125/45408541260006752256:0,3,3,3;125/1261348368333520896:0,3,3,4;49/1121198549629796352:2,3,3,3;-3125/5045393473334083584:3,3,3,3;1225/1121198549629796352:3,3,3,4;-625/74481359801726075387904:0,0,0,0,0;-3125/66205653157089844789248:0,0,0,0,3;1/408676871340060770304:0,0,0,2,3;-49375/33102826578544922394624:0,0,0,3,3;25/408676871340060770304:0,0,0,3,4;1/68112811890010128384:0,0,2,3,3;-115625/7356183684121093865472:0,0,3,3,3;25/68112811890010128384:0,0,3,3,4;-625/136225623780020256768:0,3,3,3,3;1/1681797824444694528:2,3,3,3,3;-625/15136180420002250752:3,3,3,3,3;25/1681797824444694528:3,3,3,3,4;-625/1787552635241425809309696:0,0,0,0,0,3;625/162504785021947800846336:0,0,0,0,3,3;15625/198616959471269534367744:0,0,0,3,3,3;3125/22068551052363281596416:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_51_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_50 product_1)=partial_sum_51 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_51_value (v : ℕ→ℂ) :
    eval v partial_sum_51=eval v partial_sum_50+eval v product_1 := by
  rw [←partial_sum_51_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_52 : Poly := rational_polynomial% "1875/96124704186368:;-423125/124577616625532928:0;-107/1537995266981888:2;-1875/139817751543808:3;-2675/1537995266981888:4;94375/3363595648889389056:0,0;-25/31144404156383232:0,2;71875/560599274814898176:0,3;-625/31144404156383232:0,4;-31/4613985800945664:2,3;-625/3893050519547904:3,3;-775/4613985800945664:3,4;26875/90817082520013504512:0,0,0;5/917344267878924288:0,0,2;64375/11352135315001688064:0,0,3;125/917344267878924288:0,0,4;1/46716606234574848:0,2,3;104375/10090786946668167168:0,3,3;25/46716606234574848:0,3,4;19/41525872208510976:2,3,3;55625/1121198549629796352:3,3,3;475/41525872208510976:3,3,4;-11875/3894450185711167340544:0,0,0,0;1/17028202972502532096:0,0,0,2;-426875/7356183684121093865472:0,0,0,3;25/17028202972502532096:0,0,0,4;23/30272360840004501504:0,0,2,3;-625/4006635993530007552:0,0,3,3;575/30272360840004501504:0,0,3,4;5/1261348368333520896:0,2,3,3;3125/45408541260006752256:0,3,3,3;125/1261348368333520896:0,3,3,4;49/1121198549629796352:2,3,3,3;-3125/5045393473334083584:3,3,3,3;1225/1121198549629796352:3,3,3,4;-625/74481359801726075387904:0,0,0,0,0;-3125/66205653157089844789248:0,0,0,0,3;1/408676871340060770304:0,0,0,2,3;-49375/33102826578544922394624:0,0,0,3,3;25/408676871340060770304:0,0,0,3,4;1/68112811890010128384:0,0,2,3,3;-115625/7356183684121093865472:0,0,3,3,3;25/68112811890010128384:0,0,3,3,4;-625/136225623780020256768:0,3,3,3,3;1/1681797824444694528:2,3,3,3,3;-625/15136180420002250752:3,3,3,3,3;25/1681797824444694528:3,3,3,3,4;-625/1787552635241425809309696:0,0,0,0,0,3;625/162504785021947800846336:0,0,0,0,3,3;15625/198616959471269534367744:0,0,0,3,3,3;3125/22068551052363281596416:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_52_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_51 product_1)=partial_sum_52 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_52_value (v : ℕ→ℂ) :
    eval v partial_sum_52=eval v partial_sum_51+eval v product_1 := by
  rw [←partial_sum_52_checked, eval_add]
compact_certificate_declaration noncomputable def product_40 : Poly := rational_polynomial% "18125/768997633490944:;15625/124577616625532928:0;-625/19993938470764544:1;107/1537995266981888:2;21875/1730244675354624:3;2675/1537995266981888:4;625/420449456111173632:0,0;3125/3508936201619177472:0,1;25/31144404156383232:0,2;625/13841957402836992:0,3;625/31144404156383232:0,4;625/212662800098131968:1,3;31/4613985800945664:2,3;66875/124577616625532928:3,3;775/4613985800945664:3,4;36875/817353742680121540608:0,0,0;71875/1705342993986920251392:0,0,1;-5/917344267878924288:0,0,2;111875/90817082520013504512:0,0,3;-125/917344267878924288:0,0,4;-23125/189482554887435583488:0,1,3;-1/46716606234574848:0,2,3;-3125/152890711313154048:0,3,3;-25/46716606234574848:0,3,4;625/956982600441593856:1,3,3;-19/41525872208510976:2,3,3;-111875/1121198549629796352:3,3,3;-475/41525872208510976:3,3,4;-29375/33102826578544922394624:0,0,0,0;625/1918510868235285282816:0,0,0,1;-1/17028202972502532096:0,0,0,2;-625/432716687301240815616:0,0,0,3;-25/17028202972502532096:0,0,0,4;26875/15348086945882282262528:0,0,1,3;-23/30272360840004501504:0,0,2,3;113125/408676871340060770304:0,0,3,3;-575/30272360840004501504:0,0,3,4;-33125/852671496993460125696:0,1,3,3;-5/1261348368333520896:0,2,3,3;-625/946011276250140672:0,3,3,3;-125/1261348368333520896:0,3,3,4;-625/17225686807948689408:1,3,3,3;-49/1121198549629796352:2,3,3,3;-38125/10090786946668167168:3,3,3,3;-1225/1121198549629796352:3,3,3,4;-625/55861019851294556540928:0,0,0,0,0;-79375/198616959471269534367744:0,0,0,0,3;15625/414398347538821621088256:0,0,0,1,3;-1/408676871340060770304:0,0,0,2,3;-71875/66205653157089844789248:0,0,0,3,3;-25/408676871340060770304:0,0,0,3,4;19375/46044260837646846787584:0,0,1,3,3;-1/68112811890010128384:0,0,2,3,3;113125/3678091842060546932736:0,0,3,3,3;-25/68112811890010128384:0,0,3,3,4;625/1705342993986920251392:0,1,3,3,3;25625/272451247560040513536:0,3,3,3,3;-625/189482554887435583488:1,3,3,3,3;-1/1681797824444694528:2,3,3,3,3;625/30272360840004501504:3,3,3,3,3;-25/1681797824444694528:3,3,3,3,4;-625/1340664476431069356982272:0,0,0,0,0,3;-29375/1787552635241425809309696:0,0,0,0,3,3;625/621597521308232431632384:0,0,0,1,3,3;-11875/198616959471269534367744:0,0,0,3,3,3;625/34533195628235135090688:0,0,1,3,3,3;19375/22068551052363281596416:0,0,3,3,3,3;625/7674043472941141131264:0,1,3,3,3,3;3125/817353742680121540608:0,3,3,3,3,3"
compact_certificate_declaration theorem product_40_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_4 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_5 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_6 n_c7_0) [([],(0:ℚ))])))=product_40 := by
  decide +kernel
compact_certificate_declaration theorem product_40_value (v : ℕ→ℂ) :
    eval v product_40=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_4 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_5 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_6 n_c7_0) [([],(0:ℚ))]))) := by
  rw [←product_40_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_53 : Poly := rational_polynomial% "33125/768997633490944:;-101875/31144404156383232:0;-625/19993938470764544:1;-625/814232788402176:3;33125/1121198549629796352:0,0;3125/3508936201619177472:0,1;194375/1121198549629796352:0,3;625/212662800098131968:1,3;15625/41525872208510976:3,3;139375/408676871340060770304:0,0,0;71875/1705342993986920251392:0,0,1;36875/5342181324706676736:0,0,3;-23125/189482554887435583488:0,1,3;-101875/10090786946668167168:0,3,3;625/956982600441593856:1,3,3;-3125/62288808312766464:3,3,3;-86875/22068551052363281596416:0,0,0,0;625/1918510868235285282816:0,0,0,1;-109375/1839045921030273466368:0,0,0,3;26875/15348086945882282262528:0,0,1,3;49375/408676871340060770304:0,0,3,3;-33125/852671496993460125696:0,1,3,3;-26875/45408541260006752256:0,3,3,3;-625/17225686807948689408:1,3,3,3;-44375/10090786946668167168:3,3,3,3;-4375/223444079405178226163712:0,0,0,0,0;-44375/99308479735634767183872:0,0,0,0,3;15625/414398347538821621088256:0,0,0,1,3;-4375/1697580850181790892032:0,0,0,3,3;19375/46044260837646846787584:0,0,1,3,3;36875/2452061228040364621824:0,0,3,3,3;625/1705342993986920251392:0,1,3,3,3;625/6985929424616423424:0,3,3,3,3;-625/189482554887435583488:1,3,3,3,3;-625/30272360840004501504:3,3,3,3,3;-4375/5362657905724277427929088:0,0,0,0,0,3;-625/49654239867817383591936:0,0,0,0,3,3;625/621597521308232431632384:0,0,0,1,3,3;625/33102826578544922394624:0,0,0,3,3,3;625/34533195628235135090688:0,0,1,3,3,3;625/613015307010091155456:0,0,3,3,3,3;625/7674043472941141131264:0,1,3,3,3,3;3125/817353742680121540608:0,3,3,3,3,3"
compact_certificate_declaration theorem partial_sum_53_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_52 product_40)=partial_sum_53 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_53_value (v : ℕ→ℂ) :
    eval v partial_sum_53=eval v partial_sum_52+eval v product_40 := by
  rw [←partial_sum_53_checked, eval_add]
compact_certificate_declaration noncomputable def product_41 : Poly := rational_polynomial% "-33125/768997633490944:;101875/31144404156383232:0;625/19993938470764544:1;625/814232788402176:3;-33125/1121198549629796352:0,0;-3125/3508936201619177472:0,1;-194375/1121198549629796352:0,3;-625/212662800098131968:1,3;-15625/41525872208510976:3,3;-139375/408676871340060770304:0,0,0;-71875/1705342993986920251392:0,0,1;-36875/5342181324706676736:0,0,3;23125/189482554887435583488:0,1,3;101875/10090786946668167168:0,3,3;-625/956982600441593856:1,3,3;3125/62288808312766464:3,3,3;86875/22068551052363281596416:0,0,0,0;-625/1918510868235285282816:0,0,0,1;109375/1839045921030273466368:0,0,0,3;-26875/15348086945882282262528:0,0,1,3;-49375/408676871340060770304:0,0,3,3;33125/852671496993460125696:0,1,3,3;26875/45408541260006752256:0,3,3,3;625/17225686807948689408:1,3,3,3;44375/10090786946668167168:3,3,3,3;4375/223444079405178226163712:0,0,0,0,0;44375/99308479735634767183872:0,0,0,0,3;-15625/414398347538821621088256:0,0,0,1,3;4375/1697580850181790892032:0,0,0,3,3;-19375/46044260837646846787584:0,0,1,3,3;-36875/2452061228040364621824:0,0,3,3,3;-625/1705342993986920251392:0,1,3,3,3;-625/6985929424616423424:0,3,3,3,3;625/189482554887435583488:1,3,3,3,3;625/30272360840004501504:3,3,3,3,3;4375/5362657905724277427929088:0,0,0,0,0,3;625/49654239867817383591936:0,0,0,0,3,3;-625/621597521308232431632384:0,0,0,1,3,3;-625/33102826578544922394624:0,0,0,3,3,3;-625/34533195628235135090688:0,0,1,3,3,3;-625/613015307010091155456:0,0,3,3,3,3;-625/7674043472941141131264:0,1,3,3,3,3;-3125/817353742680121540608:0,3,3,3,3,3"
compact_certificate_declaration theorem product_41_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_3 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_4 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_5 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_6 n_c9_0) [([],(0:ℚ))]))))=product_41 := by
  decide +kernel
compact_certificate_declaration theorem product_41_value (v : ℕ→ℂ) :
    eval v product_41=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_3 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_4 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_5 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_6 n_c9_0) [([],(0:ℚ))])))) := by
  rw [←product_41_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_54 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_54_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_53 product_41)=partial_sum_54 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_54_value (v : ℕ→ℂ) :
    eval v partial_sum_54=eval v partial_sum_53+eval v product_41 := by
  rw [←partial_sum_54_checked, eval_add]
compact_certificate_declaration noncomputable def e6 : Poly := partial_sum_54
compact_certificate_declaration theorem checked_6 : checkZero e6=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_6 (y z w a b : ℂ) :
    (certificate y z w a b)[6]?=some 0 := by
  change some (((((((((c0_1 y z w a b)*(c1_5 y z w a b))+(((c0_2 y z w a b)*(c1_4 y z w a b))+(((c0_3 y z w a b)*(c1_3 y z w a b))+(((c0_4 y z w a b)*(c1_2 y z w a b))+(((c0_5 y z w a b)*(c1_1 y z w a b))+(((c0_6 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_4 y z w a b)*(c7_2 y z w a b))+(((c6_5 y z w a b)*(c7_1 y z w a b))+(((c6_6 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_3 y z w a b)*(c9_3 y z w a b))+(((c8_4 y z w a b)*(c9_2 y z w a b))+(((c8_5 y z w a b)*(c9_1 y z w a b))+(((c8_6 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e6 checked_6
  simp only [e6, eval_add, eval_mul, eval_scale, eval_pow, product_34_value, product_35_value, product_36_value, product_37_value, product_38_value, product_39_value, partial_sum_45_value, partial_sum_46_value, partial_sum_47_value, partial_sum_48_value, partial_sum_49_value, partial_sum_50_value, product_1_value, partial_sum_51_value, partial_sum_52_value, product_40_value, partial_sum_53_value, product_41_value, partial_sum_54_value, n_c0_1_value y z w a b 0, n_c0_2_value y z w a b 0, n_c0_3_value y z w a b 0, n_c0_4_value y z w a b 0, n_c0_5_value y z w a b 0, n_c0_6_value y z w a b 0, n_c1_0_value y z w a b 0, n_c1_1_value y z w a b 0, n_c1_2_value y z w a b 0, n_c1_3_value y z w a b 0, n_c1_4_value y z w a b 0, n_c1_5_value y z w a b 0, n_c6_4_value y z w a b 0, n_c6_5_value y z w a b 0, n_c6_6_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_3_value y z w a b 0, n_c8_4_value y z w a b 0, n_c8_5_value y z w a b 0, n_c8_6_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_6
compact_certificate_declaration noncomputable def product_42 : Poly := rational_polynomial% "-50625/3075990533963776:;51875/83051744417021952:0;-7/768997633490944:2;-38125/27683914805673984:3;-175/768997633490944:4;-66875/10090786946668167168:0,0;-1/4791446793289728:0,2;3125/2242397099259592704:0,3;-25/4791446793289728:0,4;-1/2306992900472832:2,3;625/11325237875048448:3,3;-25/2306992900472832:3,4;-19375/408676871340060770304:0,0,0;-1/840898912222347264:0,0,2;-153125/90817082520013504512:0,0,3;-25/840898912222347264:0,0,4;-5/172492084558430208:0,2,3;-3125/1187151405490372608:0,3,3;-125/172492084558430208:0,3,4;31/249155233251065856:2,3,3;-11875/2242397099259592704:3,3,3;775/249155233251065856:3,3,4;625/613015307010091155456:0,0,0,0;625/76626913376261394432:0,0,0,3;-19/60544721680009003008:0,0,2,3;-14375/544902495120081027072:0,0,3,3;-475/60544721680009003008:0,0,3,4;-5/1681797824444694528:0,2,3,3;3125/30272360840004501504:0,3,3,3;-125/1681797824444694528:0,3,3,4;5/747465699753197568:2,3,3,3;-3125/6727191297778778112:3,3,3,3;125/747465699753197568:3,3,3,4;625/14712367368242187730944:0,0,0,0,3;625/1337487942567471611904:0,0,0,3,3;-1/90817082520013504512:0,0,2,3,3;3125/1634707485360243081216:0,0,3,3,3;-25/90817082520013504512:0,0,3,3,4;-1/10090786946668167168:0,2,3,3,3;625/60544721680009003008:0,3,3,3,3;-25/10090786946668167168:0,3,3,3,4"
compact_certificate_declaration theorem product_42_checked :
    mulShort n_c0_2 n_c1_5=product_42 := by
  decide +kernel
compact_certificate_declaration theorem product_42_value (v : ℕ→ℂ) :
    eval v product_42=eval v n_c0_2*eval v n_c1_5 := by
  rw [←product_42_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_43 : Poly := rational_polynomial% "21875/1537995266981888:;-14375/27683914805673984:0;-9/3075990533963776:2;-625/1628465576804352:3;-225/3075990533963776:4;11875/1261348368333520896:0,0;1/6388595724386304:0,2;4375/1121198549629796352:0,3;25/6388595724386304:0,4;-1/814232788402176:2,3;-38125/249155233251065856:3,3;-25/814232788402176:3,4;4375/181634165040027009024:0,0,0;1/420449456111173632:0,0,2;3125/3363595648889389056:0,0,3;25/420449456111173632:0,0,4;41/2242397099259592704:0,2,3;625/388107190256467968:0,3,3;1025/2242397099259592704:0,3,4;-31/249155233251065856:2,3,3;3125/1121198549629796352:3,3,3;-775/249155233251065856:3,3,4;-4375/5517137763090820399104:0,0,0,0;-625/74304885698192867328:0,0,0,3;1/10090786946668167168:0,0,2,3;625/136225623780020256768:0,0,3,3;25/10090786946668167168:0,0,3,4;1/1681797824444694528:0,2,3,3;625/15136180420002250752:0,3,3,3;25/1681797824444694528:0,3,3,4;-1/373732849876598784:2,3,3,3;625/3363595648889389056:3,3,3,3;-25/373732849876598784:3,3,3,4;-4375/132411306314179689578496:0,0,0,0,3;-3125/7356183684121093865472:0,0,0,3,3;-625/544902495120081027072:0,0,3,3,3"
compact_certificate_declaration theorem product_43_checked :
    mulShort n_c0_3 n_c1_4=product_43 := by
  decide +kernel
compact_certificate_declaration theorem product_43_value (v : ℕ→ℂ) :
    eval v product_43=eval v n_c0_3*eval v n_c1_4 := by
  rw [←product_43_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_44 : Poly := rational_polynomial% "-58125/3075990533963776:;285625/498310466502131712:0;9/1537995266981888:2;86875/27683914805673984:3;225/1537995266981888:4;-21875/2374302810980745216:0,0;1/10381468052127744:0,2;3125/407708563501744128:0,3;25/10381468052127744:0,4;3/3075990533963776:2,3;4375/166103488834043904:3,3;75/3075990533963776:3,4;-274375/3269414970720486162432:0,0,0;1/3363595648889389056:0,0,2;-11875/27943717698465693696:0,0,3;25/3363595648889389056:0,0,4;5/560599274814898176:0,2,3;-3125/1121198549629796352:0,3,3;125/560599274814898176:0,3,4;1/62288808312766464:2,3,3;-21875/2242397099259592704:3,3,3;25/62288808312766464:3,3,4;51875/264822612628359379156992:0,0,0,0;51875/29424734736484375461888:0,0,0,3;5/181634165040027009024:0,0,2,3;15625/544902495120081027072:0,0,3,3;125/181634165040027009024:0,0,3,4;-3125/363268330080054018048:0,3,3,3;-5/2242397099259592704:2,3,3,3;625/3104857522051743744:3,3,3,3;-125/2242397099259592704:3,3,3,4;625/446888158810356452327424:0,0,0,0,0;15625/794467837885078137470976:0,0,0,0,3;3125/29424734736484375461888:0,0,0,3,3;625/891658628378314407936:0,0,3,3,3;3125/1089804990240162054144:0,3,3,3,3;625/10725315811448554855858176:0,0,0,0,0,3;625/1191701756827617206206464:0,0,0,0,3,3;-625/132411306314179689578496:0,0,0,3,3,3;-625/14712367368242187730944:0,0,3,3,3,3"
compact_certificate_declaration theorem product_44_checked :
    mulShort n_c0_4 n_c1_3=product_44 := by
  decide +kernel
compact_certificate_declaration theorem product_44_value (v : ℕ→ℂ) :
    eval v product_44=eval v n_c0_4*eval v n_c1_3 := by
  rw [←product_44_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_45 : Poly := rational_polynomial% "625/14656190191239168:0;-101875/20181573893336334336:0,0;-1/62288808312766464:0,2;-625/172492084558430208:0,3;-25/62288808312766464:0,4;4375/68112811890010128384:0,0,0;-1/5045393473334083584:0,0,2;-625/16512196821820637184:0,0,3;-25/5045393473334083584:0,0,4;-1/560599274814898176:0,2,3;-625/1681797824444694528:0,3,3;-25/560599274814898176:0,3,4;625/5517137763090820399104:0,0,0,0;64375/14712367368242187730944:0,0,0,3;26875/1634707485360243081216:0,0,3,3;625/198616959471269534367744:0,0,0,0,3;625/11034275526181640798208:0,0,0,3,3;625/2452061228040364621824:0,0,3,3,3"
compact_certificate_declaration theorem product_45_checked :
    mulShort n_c0_5 n_c1_2=product_45 := by
  decide +kernel
compact_certificate_declaration theorem product_45_value (v : ℕ→ℂ) :
    eval v product_45=eval v n_c0_5*eval v n_c1_2 := by
  rw [←product_45_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_46 : Poly := rational_polynomial% "-18125/249155233251065856:0;70625/20181573893336334336:0,0;26875/2242397099259592704:0,3;-625/34056405945005064192:0,0,0;-18125/45408541260006752256:0,0,3;625/20181573893336334336:0,3,3;-625/33102826578544922394624:0,0,0,0;625/668743971283735805952:0,0,0,3;-11875/1634707485360243081216:0,0,3,3;-3125/60544721680009003008:0,3,3,3;625/297925439206904301551616:0,0,0,0,3;625/5092742550545372676096:0,0,0,3,3;625/668743971283735805952:0,0,3,3,3"
compact_certificate_declaration theorem product_46_checked :
    mulShort n_c0_6 n_c1_1=product_46 := by
  decide +kernel
compact_certificate_declaration theorem product_46_value (v : ℕ→ℂ) :
    eval v product_46=eval v n_c0_6*eval v n_c1_1 := by
  rw [←product_46_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_47 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:3;0/1:0,3;0/1:3,3"
compact_certificate_declaration theorem product_47_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_7 n_c1_0=product_47 := by
  decide +kernel
compact_certificate_declaration theorem product_47_value (v : ℕ→ℂ) :
    eval v product_47=eval v n_c0_7*eval v n_c1_0 := by
  rw [←product_47_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_55 : Poly := rational_polynomial% "0/1:0;0/1:3;0/1:0,3;0/1:3,3"
compact_certificate_declaration theorem partial_sum_55_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_47 [([],(0:ℚ))])=partial_sum_55 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_55_value (v : ℕ→ℂ) :
    eval v partial_sum_55=eval v product_47+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_55_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_56 : Poly := rational_polynomial% "-18125/249155233251065856:0;0/1:3;70625/20181573893336334336:0,0;26875/2242397099259592704:0,3;0/1:3,3;-625/34056405945005064192:0,0,0;-18125/45408541260006752256:0,0,3;625/20181573893336334336:0,3,3;-625/33102826578544922394624:0,0,0,0;625/668743971283735805952:0,0,0,3;-11875/1634707485360243081216:0,0,3,3;-3125/60544721680009003008:0,3,3,3;625/297925439206904301551616:0,0,0,0,3;625/5092742550545372676096:0,0,0,3,3;625/668743971283735805952:0,0,3,3,3"
compact_certificate_declaration theorem partial_sum_56_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_46 partial_sum_55)=partial_sum_56 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_56_value (v : ℕ→ℂ) :
    eval v partial_sum_56=eval v product_46+eval v partial_sum_55 := by
  rw [←partial_sum_56_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_57 : Poly := rational_polynomial% "-625/20762936104255488:0;0/1:3;-15625/10090786946668167168:0,0;-1/62288808312766464:0,2;3125/373732849876598784:0,3;-25/62288808312766464:0,4;0/1:3,3;3125/68112811890010128384:0,0,0;-1/5045393473334083584:0,0,2;-79375/181634165040027009024:0,0,3;-25/5045393473334083584:0,0,4;-1/560599274814898176:0,2,3;-625/1834688535757848576:0,3,3;-25/560599274814898176:0,3,4;3125/33102826578544922394624:0,0,0,0;78125/14712367368242187730944:0,0,0,3;625/68112811890010128384:0,0,3,3;-3125/60544721680009003008:0,3,3,3;3125/595850878413808603103232:0,0,0,0,3;11875/66205653157089844789248:0,0,0,3,3;4375/3678091842060546932736:0,0,3,3,3"
compact_certificate_declaration theorem partial_sum_57_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_45 partial_sum_56)=partial_sum_57 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_57_value (v : ℕ→ℂ) :
    eval v partial_sum_57=eval v product_45+eval v partial_sum_56 := by
  rw [←partial_sum_57_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_58 : Poly := rational_polynomial% "-58125/3075990533963776:;270625/498310466502131712:0;9/1537995266981888:2;86875/27683914805673984:3;225/1537995266981888:4;-434375/40363147786672668672:0,0;5/62288808312766464:0,2;71875/4484794198519185408:0,3;125/62288808312766464:0,4;3/3075990533963776:2,3;4375/166103488834043904:3,3;75/3075990533963776:3,4;-124375/3269414970720486162432:0,0,0;1/10090786946668167168:0,0,2;-104375/121089443360018006016:0,0,3;25/10090786946668167168:0,0,4;1/140149818703724544:0,2,3;-63125/20181573893336334336:0,3,3;25/140149818703724544:0,3,4;1/62288808312766464:2,3,3;-21875/2242397099259592704:3,3,3;25/62288808312766464:3,3,4;25625/88274204209453126385664:0,0,0,0;23125/3269414970720486162432:0,0,0,3;5/181634165040027009024:0,0,2,3;625/16512196821820637184:0,0,3,3;125/181634165040027009024:0,0,3,4;-21875/363268330080054018048:0,3,3,3;-5/2242397099259592704:2,3,3,3;625/3104857522051743744:3,3,3,3;-125/2242397099259592704:3,3,3,4;625/446888158810356452327424:0,0,0,0,0;59375/2383403513655234412412928:0,0,0,0,3;6875/24074782966214489014272:0,0,0,3,3;55625/29424734736484375461888:0,0,3,3,3;3125/1089804990240162054144:0,3,3,3,3;625/10725315811448554855858176:0,0,0,0,0,3;625/1191701756827617206206464:0,0,0,0,3,3;-625/132411306314179689578496:0,0,0,3,3,3;-625/14712367368242187730944:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_58_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_44 partial_sum_57)=partial_sum_58 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_58_value (v : ℕ→ℂ) :
    eval v partial_sum_58=eval v product_44+eval v partial_sum_57 := by
  rw [←partial_sum_58_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_59 : Poly := rational_polynomial% "-14375/3075990533963776:;11875/498310466502131712:0;9/3075990533963776:2;38125/13841957402836992:3;225/3075990533963776:4;-18125/13454382595557556224:0,0;59/249155233251065856:0,2;625/31362197192441856:0,3;1475/249155233251065856:0,4;-7/27683914805673984:2,3;-63125/498310466502131712:3,3;-175/27683914805673984:3,4;-45625/3269414970720486162432:0,0,0;25/10090786946668167168:0,0,2;625/9314572566155231232:0,0,3;625/10090786946668167168:0,0,4;19/747465699753197568:0,2,3;-30625/20181573893336334336:0,3,3;475/747465699753197568:0,3,4;-1/9227971601891328:2,3,3;-15625/2242397099259592704:3,3,3;-25/9227971601891328:3,3,4;-44375/88274204209453126385664:0,0,0,0;-4375/3269414970720486162432:0,0,0,3;23/181634165040027009024:0,0,2,3;23125/544902495120081027072:0,0,3,3;575/181634165040027009024:0,0,3,4;1/1681797824444694528:0,2,3,3;-625/33024393643641274368:0,3,3,3;25/1681797824444694528:0,3,3,4;-1/203854281750872064:2,3,3,3;15625/40363147786672668672:3,3,3,3;-25/203854281750872064:3,3,3,4;625/446888158810356452327424:0,0,0,0,0;-19375/2383403513655234412412928:0,0,0,0,3;-36875/264822612628359379156992:0,0,0,3,3;21875/29424734736484375461888:0,0,3,3,3;3125/1089804990240162054144:0,3,3,3,3;625/10725315811448554855858176:0,0,0,0,0,3;625/1191701756827617206206464:0,0,0,0,3,3;-625/132411306314179689578496:0,0,0,3,3,3;-625/14712367368242187730944:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_59_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_43 partial_sum_58)=partial_sum_59 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_59_value (v : ℕ→ℂ) :
    eval v partial_sum_59=eval v product_43+eval v partial_sum_58 := by
  rw [←partial_sum_59_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_60 : Poly := rational_polynomial% "-625/29576832057344:;29375/45300951500193792:0;-19/3075990533963776:2;38125/27683914805673984:3;-475/3075990533963776:4;-321875/40363147786672668672:0,0;7/249155233251065856:0,2;625/29312380382478336:0,3;175/249155233251065856:0,4;-19/27683914805673984:2,3;-11875/166103488834043904:3,3;-475/27683914805673984:3,4;-66875/1089804990240162054144:0,0,0;1/776214380512935936:0,0,2;-588125/363268330080054018048:0,0,3;25/776214380512935936:0,0,4;-1/280299637407449088:0,2,3;-41875/10090786946668167168:0,3,3;-25/280299637407449088:0,3,4;1/62288808312766464:2,3,3;-625/50963570437718016:3,3,3;25/62288808312766464:3,3,4;45625/88274204209453126385664:0,0,0,0;66875/9808244912161458487296:0,0,0,3;-1/5342181324706676736:0,0,2,3;4375/272451247560040513536:0,0,3,3;-25/5342181324706676736:0,0,3,4;-1/420449456111173632:0,2,3,3;30625/363268330080054018048:0,3,3,3;-25/420449456111173632:0,3,3,4;1/560599274814898176:2,3,3,3;-3125/40363147786672668672:3,3,3,3;25/560599274814898176:3,3,3,4;625/446888158810356452327424:0,0,0,0,0;81875/2383403513655234412412928:0,0,0,0,3;86875/264822612628359379156992:0,0,0,3,3;-1/90817082520013504512:0,0,2,3,3;78125/29424734736484375461888:0,0,3,3,3;-25/90817082520013504512:0,0,3,3,4;-1/10090786946668167168:0,2,3,3,3;14375/1089804990240162054144:0,3,3,3,3;-25/10090786946668167168:0,3,3,3,4;625/10725315811448554855858176:0,0,0,0,0,3;625/1191701756827617206206464:0,0,0,0,3,3;-625/132411306314179689578496:0,0,0,3,3,3;-625/14712367368242187730944:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_60_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_42 partial_sum_59)=partial_sum_60 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_60_value (v : ℕ→ℂ) :
    eval v partial_sum_60=eval v product_42+eval v partial_sum_59 := by
  rw [←partial_sum_60_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_61 : Poly := rational_polynomial% "-625/29576832057344:;29375/45300951500193792:0;-19/3075990533963776:2;38125/27683914805673984:3;-475/3075990533963776:4;-321875/40363147786672668672:0,0;7/249155233251065856:0,2;625/29312380382478336:0,3;175/249155233251065856:0,4;-19/27683914805673984:2,3;-11875/166103488834043904:3,3;-475/27683914805673984:3,4;-66875/1089804990240162054144:0,0,0;1/776214380512935936:0,0,2;-588125/363268330080054018048:0,0,3;25/776214380512935936:0,0,4;-1/280299637407449088:0,2,3;-41875/10090786946668167168:0,3,3;-25/280299637407449088:0,3,4;1/62288808312766464:2,3,3;-625/50963570437718016:3,3,3;25/62288808312766464:3,3,4;45625/88274204209453126385664:0,0,0,0;66875/9808244912161458487296:0,0,0,3;-1/5342181324706676736:0,0,2,3;4375/272451247560040513536:0,0,3,3;-25/5342181324706676736:0,0,3,4;-1/420449456111173632:0,2,3,3;30625/363268330080054018048:0,3,3,3;-25/420449456111173632:0,3,3,4;1/560599274814898176:2,3,3,3;-3125/40363147786672668672:3,3,3,3;25/560599274814898176:3,3,3,4;625/446888158810356452327424:0,0,0,0,0;81875/2383403513655234412412928:0,0,0,0,3;86875/264822612628359379156992:0,0,0,3,3;-1/90817082520013504512:0,0,2,3,3;78125/29424734736484375461888:0,0,3,3,3;-25/90817082520013504512:0,0,3,3,4;-1/10090786946668167168:0,2,3,3,3;14375/1089804990240162054144:0,3,3,3,3;-25/10090786946668167168:0,3,3,3,4;625/10725315811448554855858176:0,0,0,0,0,3;625/1191701756827617206206464:0,0,0,0,3,3;-625/132411306314179689578496:0,0,0,3,3,3;-625/14712367368242187730944:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_61_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_60 product_1)=partial_sum_61 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_61_value (v : ℕ→ℂ) :
    eval v partial_sum_61=eval v partial_sum_60+eval v product_1 := by
  rw [←partial_sum_61_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_62 : Poly := rational_polynomial% "-625/29576832057344:;29375/45300951500193792:0;-19/3075990533963776:2;38125/27683914805673984:3;-475/3075990533963776:4;-321875/40363147786672668672:0,0;7/249155233251065856:0,2;625/29312380382478336:0,3;175/249155233251065856:0,4;-19/27683914805673984:2,3;-11875/166103488834043904:3,3;-475/27683914805673984:3,4;-66875/1089804990240162054144:0,0,0;1/776214380512935936:0,0,2;-588125/363268330080054018048:0,0,3;25/776214380512935936:0,0,4;-1/280299637407449088:0,2,3;-41875/10090786946668167168:0,3,3;-25/280299637407449088:0,3,4;1/62288808312766464:2,3,3;-625/50963570437718016:3,3,3;25/62288808312766464:3,3,4;45625/88274204209453126385664:0,0,0,0;66875/9808244912161458487296:0,0,0,3;-1/5342181324706676736:0,0,2,3;4375/272451247560040513536:0,0,3,3;-25/5342181324706676736:0,0,3,4;-1/420449456111173632:0,2,3,3;30625/363268330080054018048:0,3,3,3;-25/420449456111173632:0,3,3,4;1/560599274814898176:2,3,3,3;-3125/40363147786672668672:3,3,3,3;25/560599274814898176:3,3,3,4;625/446888158810356452327424:0,0,0,0,0;81875/2383403513655234412412928:0,0,0,0,3;86875/264822612628359379156992:0,0,0,3,3;-1/90817082520013504512:0,0,2,3,3;78125/29424734736484375461888:0,0,3,3,3;-25/90817082520013504512:0,0,3,3,4;-1/10090786946668167168:0,2,3,3,3;14375/1089804990240162054144:0,3,3,3,3;-25/10090786946668167168:0,3,3,3,4;625/10725315811448554855858176:0,0,0,0,0,3;625/1191701756827617206206464:0,0,0,0,3,3;-625/132411306314179689578496:0,0,0,3,3,3;-625/14712367368242187730944:0,0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_62_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_61 product_1)=partial_sum_62 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_62_value (v : ℕ→ℂ) :
    eval v partial_sum_62=eval v partial_sum_61+eval v product_1 := by
  rw [←partial_sum_62_checked, eval_add]
compact_certificate_declaration noncomputable def product_48 : Poly := rational_polynomial% "-625/559271006175232:;625/29312380382478336:0;-3125/1039684800479756288:1;19/3075990533963776:2;625/768997633490944:3;475/3075990533963776:4;6875/3669377071515697152:0,0;625/1315851075607191552:0,1;-7/249155233251065856:0,2;3125/172492084558430208:0,3;-175/249155233251065856:0,4;-3125/3119054401439268864:1,3;19/27683914805673984:2,3;26875/249155233251065856:3,3;475/27683914805673984:3,4;625/14793732899187720192:0,0,0;4375/2273790658649227001856:0,0,1;-1/776214380512935936:0,0,2;-30625/363268330080054018048:0,0,3;-25/776214380512935936:0,0,4;625/11842659680464723968:0,1,3;1/280299637407449088:0,2,3;3125/5045393473334083584:0,3,3;25/280299637407449088:0,3,4;-625/84214468838860259328:1,3,3;-1/62288808312766464:2,3,3;15625/4484794198519185408:3,3,3;-25/62288808312766464:3,3,4;625/2068926661159057649664:0,0,0,0;-625/11511065209411711696896:0,0,0,1;18125/14712367368242187730944:0,0,0,3;-38125/61392347783529129050112:0,0,1,3;1/5342181324706676736:0,0,2,3;-139375/3269414970720486162432:0,0,3,3;25/5342181324706676736:0,0,3,4;625/3410685987973840502784:0,1,3,3;1/420449456111173632:0,2,3,3;-4375/181634165040027009024:0,3,3,3;25/420449456111173632:0,3,3,4;3125/252643406516580777984:1,3,3,3;-1/560599274814898176:2,3,3,3;26875/40363147786672668672:3,3,3,3;-25/560599274814898176:3,3,3,4;4375/183338731819633416339456:0,0,0,0,3;-625/276265565025881080725504:0,0,0,1,3;18125/264822612628359379156992:0,0,0,3,3;-3125/92088521675293693575168:0,0,1,3,3;1/90817082520013504512:0,0,2,3,3;-41875/14712367368242187730944:0,0,3,3,3;25/90817082520013504512:0,0,3,3,4;-625/10232057963921521508352:0,1,3,3,3;1/10090786946668167168:0,2,3,3,3;-625/64106175896480120832:0,3,3,3,3;25/10090786946668167168:0,3,3,3,4;625/1136895329324613500928:1,3,3,3,3;4375/121089443360018006016:3,3,3,3,3;625/1191701756827617206206464:0,0,0,0,3,3;625/132411306314179689578496:0,0,0,3,3,3;-625/14712367368242187730944:0,0,3,3,3,3;-625/1634707485360243081216:0,3,3,3,3,3"
compact_certificate_declaration theorem product_48_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_5 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_6 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_7 n_c7_0) [([],(0:ℚ))])))=product_48 := by
  decide +kernel
compact_certificate_declaration theorem product_48_value (v : ℕ→ℂ) :
    eval v product_48=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_5 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_6 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_7 n_c7_0) [([],(0:ℚ))]))) := by
  rw [←product_48_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_63 : Poly := rational_polynomial% "-136875/6151981067927552:;55625/83051744417021952:0;-3125/1039684800479756288:1;60625/27683914805673984:3;-123125/20181573893336334336:0,0;625/1315851075607191552:0,1;176875/4484794198519185408:0,3;-3125/3119054401439268864:1,3;18125/498310466502131712:3,3;-15625/817353742680121540608:0,0,0;4375/2273790658649227001856:0,0,1;-3125/1834688535757848576:0,0,3;625/11842659680464723968:0,1,3;-11875/3363595648889389056:0,3,3;-625/84214468838860259328:1,3,3;-4375/498310466502131712:3,3,3;216875/264822612628359379156992:0,0,0,0;-625/11511065209411711696896:0,0,0,1;236875/29424734736484375461888:0,0,0,3;-38125/61392347783529129050112:0,0,1,3;-86875/3269414970720486162432:0,0,3,3;625/3410685987973840502784:0,1,3,3;21875/363268330080054018048:0,3,3,3;3125/252643406516580777984:1,3,3,3;11875/20181573893336334336:3,3,3,3;625/446888158810356452327424:0,0,0,0,0;23125/397233918942539068735488:0,0,0,0,3;-625/276265565025881080725504:0,0,0,1,3;4375/11034275526181640798208:0,0,0,3,3;-3125/92088521675293693575168:0,0,1,3,3;-625/3269414970720486162432:0,0,3,3,3;-625/10232057963921521508352:0,1,3,3,3;625/181634165040027009024:0,3,3,3,3;625/1136895329324613500928:1,3,3,3,3;4375/121089443360018006016:3,3,3,3,3;625/10725315811448554855858176:0,0,0,0,0,3;625/595850878413808603103232:0,0,0,0,3,3;-625/7356183684121093865472:0,0,3,3,3,3;-625/1634707485360243081216:0,3,3,3,3,3"
compact_certificate_declaration theorem partial_sum_63_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_62 product_48)=partial_sum_63 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_63_value (v : ℕ→ℂ) :
    eval v partial_sum_63=eval v partial_sum_62+eval v product_48 := by
  rw [←partial_sum_63_checked, eval_add]
compact_certificate_declaration noncomputable def product_49 : Poly := rational_polynomial% "136875/6151981067927552:;-55625/83051744417021952:0;3125/1039684800479756288:1;-60625/27683914805673984:3;123125/20181573893336334336:0,0;-625/1315851075607191552:0,1;-176875/4484794198519185408:0,3;3125/3119054401439268864:1,3;-18125/498310466502131712:3,3;15625/817353742680121540608:0,0,0;-4375/2273790658649227001856:0,0,1;3125/1834688535757848576:0,0,3;-625/11842659680464723968:0,1,3;11875/3363595648889389056:0,3,3;625/84214468838860259328:1,3,3;4375/498310466502131712:3,3,3;-216875/264822612628359379156992:0,0,0,0;625/11511065209411711696896:0,0,0,1;-236875/29424734736484375461888:0,0,0,3;38125/61392347783529129050112:0,0,1,3;86875/3269414970720486162432:0,0,3,3;-625/3410685987973840502784:0,1,3,3;-21875/363268330080054018048:0,3,3,3;-3125/252643406516580777984:1,3,3,3;-11875/20181573893336334336:3,3,3,3;-625/446888158810356452327424:0,0,0,0,0;-23125/397233918942539068735488:0,0,0,0,3;625/276265565025881080725504:0,0,0,1,3;-4375/11034275526181640798208:0,0,0,3,3;3125/92088521675293693575168:0,0,1,3,3;625/3269414970720486162432:0,0,3,3,3;625/10232057963921521508352:0,1,3,3,3;-625/181634165040027009024:0,3,3,3,3;-625/1136895329324613500928:1,3,3,3,3;-4375/121089443360018006016:3,3,3,3,3;-625/10725315811448554855858176:0,0,0,0,0,3;-625/595850878413808603103232:0,0,0,0,3,3;625/7356183684121093865472:0,0,3,3,3,3;625/1634707485360243081216:0,3,3,3,3,3"
compact_certificate_declaration theorem product_49_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_4 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_5 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_6 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_7 n_c9_0) [([],(0:ℚ))]))))=product_49 := by
  decide +kernel
compact_certificate_declaration theorem product_49_value (v : ℕ→ℂ) :
    eval v product_49=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_4 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_5 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_6 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_7 n_c9_0) [([],(0:ℚ))])))) := by
  rw [←product_49_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_64 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_64_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_63 product_49)=partial_sum_64 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_64_value (v : ℕ→ℂ) :
    eval v partial_sum_64=eval v partial_sum_63+eval v product_49 := by
  rw [←partial_sum_64_checked, eval_add]
compact_certificate_declaration noncomputable def e7 : Poly := partial_sum_64
compact_certificate_declaration theorem checked_7 : checkZero e7=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_7 (y z w a b : ℂ) :
    (certificate y z w a b)[7]?=some 0 := by
  change some (((((((((c0_2 y z w a b)*(c1_5 y z w a b))+(((c0_3 y z w a b)*(c1_4 y z w a b))+(((c0_4 y z w a b)*(c1_3 y z w a b))+(((c0_5 y z w a b)*(c1_2 y z w a b))+(((c0_6 y z w a b)*(c1_1 y z w a b))+(((c0_7 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_5 y z w a b)*(c7_2 y z w a b))+(((c6_6 y z w a b)*(c7_1 y z w a b))+(((c6_7 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_4 y z w a b)*(c9_3 y z w a b))+(((c8_5 y z w a b)*(c9_2 y z w a b))+(((c8_6 y z w a b)*(c9_1 y z w a b))+(((c8_7 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e7 checked_7
  simp only [e7, eval_add, eval_mul, eval_scale, eval_pow, product_42_value, product_43_value, product_44_value, product_45_value, product_46_value, product_47_value, partial_sum_55_value, partial_sum_56_value, partial_sum_57_value, partial_sum_58_value, partial_sum_59_value, partial_sum_60_value, product_1_value, partial_sum_61_value, partial_sum_62_value, product_48_value, partial_sum_63_value, product_49_value, partial_sum_64_value, n_c0_2_value y z w a b 0, n_c0_3_value y z w a b 0, n_c0_4_value y z w a b 0, n_c0_5_value y z w a b 0, n_c0_6_value y z w a b 0, n_c0_7_value y z w a b 0, n_c1_0_value y z w a b 0, n_c1_1_value y z w a b 0, n_c1_2_value y z w a b 0, n_c1_3_value y z w a b 0, n_c1_4_value y z w a b 0, n_c1_5_value y z w a b 0, n_c6_5_value y z w a b 0, n_c6_6_value y z w a b 0, n_c6_7_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_4_value y z w a b 0, n_c8_5_value y z w a b 0, n_c8_6_value y z w a b 0, n_c8_7_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_7
compact_certificate_declaration noncomputable def product_50 : Poly := rational_polynomial% "21875/6151981067927552:;-14375/110735659222695936:0;-9/12303962135855104:2;-625/6513862307217408:3;-225/12303962135855104:4;11875/5045393473334083584:0,0;1/25554382897545216:0,2;4375/4484794198519185408:0,3;25/25554382897545216:0,4;-1/3256931153608704:2,3;-38125/996620933004263424:3,3;-25/3256931153608704:3,4;4375/726536660160108036096:0,0,0;1/1681797824444694528:0,0,2;3125/13454382595557556224:0,0,3;25/1681797824444694528:0,0,4;41/8969588397038370816:0,2,3;625/1552428761025871872:0,3,3;1025/8969588397038370816:0,3,4;-31/996620933004263424:2,3,3;3125/4484794198519185408:3,3,3;-775/996620933004263424:3,3,4;-4375/22068551052363281596416:0,0,0,0;-625/297219542792771469312:0,0,0,3;1/40363147786672668672:0,0,2,3;625/544902495120081027072:0,0,3,3;25/40363147786672668672:0,0,3,4;1/6727191297778778112:0,2,3,3;625/60544721680009003008:0,3,3,3;25/6727191297778778112:0,3,3,4;-1/1494931399506395136:2,3,3,3;625/13454382595557556224:3,3,3,3;-25/1494931399506395136:3,3,3,4;-4375/529645225256718758313984:0,0,0,0,3;-3125/29424734736484375461888:0,0,0,3,3;-625/2179609980480324108288:0,0,3,3,3"
compact_certificate_declaration theorem product_50_checked :
    mulShort n_c0_3 n_c1_5=product_50 := by
  decide +kernel
compact_certificate_declaration theorem product_50_value (v : ℕ→ℂ) :
    eval v product_50=eval v n_c0_3*eval v n_c1_5 := by
  rw [←product_50_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_51 : Poly := rational_polynomial% "-19375/6151981067927552:;108125/996620933004263424:0;3/3075990533963776:2;625/1537995266981888:3;75/3075990533963776:4;-625/315337092083380224:0,0;1/83051744417021952:0,2;625/172492084558430208:0,3;25/83051744417021952:0,4;1/5033439055577088:2,3;19375/996620933004263424:3,3;25/5033439055577088:3,4;-38125/6538829941440972324864:0,0,0;-115625/726536660160108036096:0,0,3;5/4484794198519185408:0,2,3;-33125/80726295573345337344:0,3,3;125/4484794198519185408:0,3,4;5/498310466502131712:2,3,3;-625/689968338233720832:3,3,3;125/498310466502131712:3,3,4;625/11034275526181640798208:0,0,0,0;14375/19616489824322916974592:0,0,0,3;625/1089804990240162054144:0,0,3,3;-3125/242178886720036012032:0,3,3,3;625/264822612628359379156992:0,0,0,0,3;625/14712367368242187730944:0,0,0,3,3;625/3269414970720486162432:0,0,3,3,3"
compact_certificate_declaration theorem product_51_checked :
    mulShort n_c0_4 n_c1_4=product_51 := by
  decide +kernel
compact_certificate_declaration theorem product_51_value (v : ℕ→ℂ) :
    eval v product_51=eval v n_c0_4*eval v n_c1_4 := by
  rw [←product_51_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_52 : Poly := rational_polynomial% "1875/1447524957159424:;-36875/249155233251065856:0;-3/6151981067927552:2;-4375/27683914805673984:3;-75/6151981067927552:4;19375/14677508286062788608:0,0;-1/124577616625532928:0,2;625/153326297385271296:0,3;-25/124577616625532928:0,4;-1/27683914805673984:2,3;-14375/1993241866008526848:3,3;-25/27683914805673984:3,4;3125/272451247560040513536:0,0,0;-1/40363147786672668672:0,0,2;3125/55887435396931387392:0,0,3;-25/40363147786672668672:0,0,4;625/1261348368333520896:0,3,3;1/498310466502131712:2,3,3;625/1494931399506395136:3,3,3;25/498310466502131712:3,3,4;625/44137102104726563192832:0,0,0,0;60625/117698938945937501847552:0,0,0,3;-625/544902495120081027072:0,0,3,3;-15625/1453073320320216072192:0,3,3,3;625/1588935675770156274941952:0,0,0,0,3;625/176548408418906252771328:0,0,0,3,3;-625/19616489824322916974592:0,0,3,3,3;-625/2179609980480324108288:0,3,3,3,3"
compact_certificate_declaration theorem product_52_checked :
    mulShort n_c0_5 n_c1_3=product_52 := by
  decide +kernel
compact_certificate_declaration theorem product_52_value (v : ℕ→ℂ) :
    eval v product_52=eval v n_c0_5*eval v n_c1_3 := by
  rw [←product_52_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_53 : Poly := rational_polynomial% "-18125/996620933004263424:0;70625/80726295573345337344:0,0;4375/4484794198519185408:0,3;-625/136225623780020256768:0,0,0;-625/242178886720036012032:0,0,3;3125/26908765191115112448:0,3,3;-625/132411306314179689578496:0,0,0,0;-625/2263441133575721189376:0,0,0,3;-625/297219542792771469312:0,0,3,3"
compact_certificate_declaration theorem product_53_checked :
    mulShort n_c0_6 n_c1_2=product_53 := by
  decide +kernel
compact_certificate_declaration theorem product_53_value (v : ℕ→ℂ) :
    eval v product_53=eval v n_c0_6*eval v n_c1_2 := by
  rw [←product_53_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_54 : Poly := rational_polynomial% "625/62288808312766464:0;-625/3363595648889389056:0,0;-625/344984169116860416:0,3;625/40363147786672668672:0,0,3;625/20181573893336334336:0,3,3;625/1089804990240162054144:0,0,3,3;625/121089443360018006016:0,3,3,3"
compact_certificate_declaration theorem product_54_checked :
    mulShort n_c0_7 n_c1_1=product_54 := by
  decide +kernel
compact_certificate_declaration theorem product_54_value (v : ℕ→ℂ) :
    eval v product_54=eval v n_c0_7*eval v n_c1_1 := by
  rw [←product_54_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_55 : Poly := rational_polynomial% "0/1:;0/1:0;0/1:3"
compact_certificate_declaration theorem product_55_checked :
    SmallLevelSparseRationalPolynomialCheck.mul n_c0_8 n_c1_0=product_55 := by
  decide +kernel
compact_certificate_declaration theorem product_55_value (v : ℕ→ℂ) :
    eval v product_55=eval v n_c0_8*eval v n_c1_0 := by
  rw [←product_55_checked, eval_mul]
compact_certificate_declaration noncomputable def partial_sum_65 : Poly := rational_polynomial% "0/1:0;0/1:3"
compact_certificate_declaration theorem partial_sum_65_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_55 [([],(0:ℚ))])=partial_sum_65 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_65_value (v : ℕ→ℂ) :
    eval v partial_sum_65=eval v product_55+eval v [([],(0:ℚ))] := by
  rw [←partial_sum_65_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_66 : Poly := rational_polynomial% "625/62288808312766464:0;0/1:3;-625/3363595648889389056:0,0;-625/344984169116860416:0,3;625/40363147786672668672:0,0,3;625/20181573893336334336:0,3,3;625/1089804990240162054144:0,0,3,3;625/121089443360018006016:0,3,3,3"
compact_certificate_declaration theorem partial_sum_66_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_54 partial_sum_65)=partial_sum_66 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_66_value (v : ℕ→ℂ) :
    eval v partial_sum_66=eval v product_54+eval v partial_sum_65 := by
  rw [←partial_sum_66_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_67 : Poly := rational_polynomial% "-625/76663148692635648:0;0/1:3;55625/80726295573345337344:0,0;-625/747465699753197568:0,3;-625/136225623780020256768:0,0,0;3125/242178886720036012032:0,0,3;11875/80726295573345337344:0,3,3;-625/132411306314179689578496:0,0,0,0;-625/2263441133575721189376:0,0,0,3;-625/408676871340060770304:0,0,3,3;625/121089443360018006016:0,3,3,3"
compact_certificate_declaration theorem partial_sum_67_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_53 partial_sum_66)=partial_sum_67 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_67_value (v : ℕ→ℂ) :
    eval v partial_sum_67=eval v product_53+eval v partial_sum_66 := by
  rw [←partial_sum_67_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_68 : Poly := rational_polynomial% "1875/1447524957159424:;-51875/332206977668087808:0;-3/6151981067927552:2;-4375/27683914805673984:3;-75/6151981067927552:4;108125/53817530382230224896:0,0;-1/124577616625532928:0,2;19375/5979725598025580544:0,3;-25/124577616625532928:0,4;-1/27683914805673984:2,3;-14375/1993241866008526848:3,3;-25/27683914805673984:3,4;625/90817082520013504512:0,0,0;-1/40363147786672668672:0,0,2;3125/45408541260006752256:0,0,3;-25/40363147786672668672:0,0,4;51875/80726295573345337344:0,3,3;1/498310466502131712:2,3,3;625/1494931399506395136:3,3,3;25/498310466502131712:3,3,4;625/66205653157089844789248:0,0,0,0;3125/13077659882881944649728:0,0,0,3;-4375/1634707485360243081216:0,0,3,3;-625/111774870793862774784:0,3,3,3;625/1588935675770156274941952:0,0,0,0,3;625/176548408418906252771328:0,0,0,3,3;-625/19616489824322916974592:0,0,3,3,3;-625/2179609980480324108288:0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_68_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_52 partial_sum_67)=partial_sum_68 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_68_value (v : ℕ→ℂ) :
    eval v partial_sum_68=eval v product_52+eval v partial_sum_67 := by
  rw [←partial_sum_68_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_69 : Poly := rational_polynomial% "-45625/24607924271710208:;-11875/249155233251065856:0;3/6151981067927552:2;625/2516719527788544:3;75/6151981067927552:4;4375/161452591146690674688:0,0;1/249155233251065856:0,2;123125/17939176794076741632:0,3;25/249155233251065856:0,4;1/6151981067927552:2,3;625/51108765795090432:3,3;25/6151981067927552:3,4;625/594439085585542938624:0,0,0;-1/40363147786672668672:0,0,2;-21875/242178886720036012032:0,0,3;-25/40363147786672668672:0,0,4;5/4484794198519185408:0,2,3;3125/13454382595557556224:0,3,3;125/4484794198519185408:0,3,4;1/83051744417021952:2,3,3;-4375/8969588397038370816:3,3,3;25/83051744417021952:3,3,4;4375/66205653157089844789248:0,0,0,0;38125/39232979648645833949184:0,0,0,3;-625/297219542792771469312:0,0,3,3;-26875/1453073320320216072192:0,3,3,3;4375/1588935675770156274941952:0,0,0,0,3;625/13580646801454327136256:0,0,0,3,3;3125/19616489824322916974592:0,0,3,3,3;-625/2179609980480324108288:0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_69_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_51 partial_sum_68)=partial_sum_69 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_69_value (v : ℕ→ℂ) :
    eval v partial_sum_69=eval v product_51+eval v partial_sum_68 := by
  rw [←partial_sum_69_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_70 : Poly := rational_polynomial% "41875/24607924271710208:;-176875/996620933004263424:0;-3/12303962135855104:2;1875/12303962135855104:3;-75/12303962135855104:4;128125/53817530382230224896:0,0;43/996620933004263424:0,2;15625/1993241866008526848:0,3;1075/996620933004263424:0,4;-1/6920978701418496:2,3;-51875/1993241866008526848:3,3;-25/6920978701418496:3,4;23125/3269414970720486162432:0,0,0;23/40363147786672668672:0,0,2;3125/22016262429094182912:0,0,3;575/40363147786672668672:0,0,4;1/175874282294870016:0,2,3;25625/40363147786672668672:0,3,3;25/175874282294870016:0,3,4;-19/996620933004263424:2,3,3;625/2989862799012790272:3,3,3;-475/996620933004263424:3,3,4;-4375/33102826578544922394624:0,0,0,0;-44375/39232979648645833949184:0,0,0,3;1/40363147786672668672:0,0,2,3;-3125/3269414970720486162432:0,0,3,3;25/40363147786672668672:0,0,3,4;1/6727191297778778112:0,2,3,3;-11875/1453073320320216072192:0,3,3,3;25/6727191297778778112:0,3,3,4;-1/1494931399506395136:2,3,3,3;625/13454382595557556224:3,3,3,3;-25/1494931399506395136:3,3,3,4;-4375/794467837885078137470976:0,0,0,0,3;-625/10385200495229779574784:0,0,0,3,3;-625/4904122456080729243648:0,0,3,3,3;-625/2179609980480324108288:0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_70_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_50 partial_sum_69)=partial_sum_70 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_70_value (v : ℕ→ℂ) :
    eval v partial_sum_70=eval v product_50+eval v partial_sum_69 := by
  rw [←partial_sum_70_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_71 : Poly := rational_polynomial% "41875/24607924271710208:;-176875/996620933004263424:0;-3/12303962135855104:2;1875/12303962135855104:3;-75/12303962135855104:4;128125/53817530382230224896:0,0;43/996620933004263424:0,2;15625/1993241866008526848:0,3;1075/996620933004263424:0,4;-1/6920978701418496:2,3;-51875/1993241866008526848:3,3;-25/6920978701418496:3,4;23125/3269414970720486162432:0,0,0;23/40363147786672668672:0,0,2;3125/22016262429094182912:0,0,3;575/40363147786672668672:0,0,4;1/175874282294870016:0,2,3;25625/40363147786672668672:0,3,3;25/175874282294870016:0,3,4;-19/996620933004263424:2,3,3;625/2989862799012790272:3,3,3;-475/996620933004263424:3,3,4;-4375/33102826578544922394624:0,0,0,0;-44375/39232979648645833949184:0,0,0,3;1/40363147786672668672:0,0,2,3;-3125/3269414970720486162432:0,0,3,3;25/40363147786672668672:0,0,3,4;1/6727191297778778112:0,2,3,3;-11875/1453073320320216072192:0,3,3,3;25/6727191297778778112:0,3,3,4;-1/1494931399506395136:2,3,3,3;625/13454382595557556224:3,3,3,3;-25/1494931399506395136:3,3,3,4;-4375/794467837885078137470976:0,0,0,0,3;-625/10385200495229779574784:0,0,0,3,3;-625/4904122456080729243648:0,0,3,3,3;-625/2179609980480324108288:0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_71_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_70 product_1)=partial_sum_71 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_71_value (v : ℕ→ℂ) :
    eval v partial_sum_71=eval v partial_sum_70+eval v product_1 := by
  rw [←partial_sum_71_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_72 : Poly := rational_polynomial% "41875/24607924271710208:;-176875/996620933004263424:0;-3/12303962135855104:2;1875/12303962135855104:3;-75/12303962135855104:4;128125/53817530382230224896:0,0;43/996620933004263424:0,2;15625/1993241866008526848:0,3;1075/996620933004263424:0,4;-1/6920978701418496:2,3;-51875/1993241866008526848:3,3;-25/6920978701418496:3,4;23125/3269414970720486162432:0,0,0;23/40363147786672668672:0,0,2;3125/22016262429094182912:0,0,3;575/40363147786672668672:0,0,4;1/175874282294870016:0,2,3;25625/40363147786672668672:0,3,3;25/175874282294870016:0,3,4;-19/996620933004263424:2,3,3;625/2989862799012790272:3,3,3;-475/996620933004263424:3,3,4;-4375/33102826578544922394624:0,0,0,0;-44375/39232979648645833949184:0,0,0,3;1/40363147786672668672:0,0,2,3;-3125/3269414970720486162432:0,0,3,3;25/40363147786672668672:0,0,3,4;1/6727191297778778112:0,2,3,3;-11875/1453073320320216072192:0,3,3,3;25/6727191297778778112:0,3,3,4;-1/1494931399506395136:2,3,3,3;625/13454382595557556224:3,3,3,3;-25/1494931399506395136:3,3,3,4;-4375/794467837885078137470976:0,0,0,0,3;-625/10385200495229779574784:0,0,0,3,3;-625/4904122456080729243648:0,0,3,3,3;-625/2179609980480324108288:0,3,3,3,3"
compact_certificate_declaration theorem partial_sum_72_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_71 product_1)=partial_sum_72 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_72_value (v : ℕ→ℂ) :
    eval v partial_sum_72=eval v partial_sum_71+eval v product_1 := by
  rw [←partial_sum_72_checked, eval_add]
compact_certificate_declaration noncomputable def product_56 : Poly := rational_polynomial% "-11875/24607924271710208:;-33125/1993241866008526848:0;625/519842400239878144:1;3/12303962135855104:2;625/12303962135855104:3;75/12303962135855104:4;-11875/53817530382230224896:0,0;-625/42107234419430129664:0,1;-43/996620933004263424:0,2;-15625/2989862799012790272:0,3;-1075/996620933004263424:0,4;3125/18714326408635613184:1,3;1/6920978701418496:2,3;21875/1993241866008526848:3,3;25/6920978701418496:3,4;-4375/1453073320320216072192:0,0,0;-625/1705342993986920251392:0,0,1;-23/40363147786672668672:0,0,2;-14375/363268330080054018048:0,0,3;-575/40363147786672668672:0,0,4;-625/126321703258290388992:0,1,3;-1/175874282294870016:0,2,3;-79375/161452591146690674688:0,3,3;-25/175874282294870016:0,3,4;-625/42107234419430129664:1,3,3;19/996620933004263424:2,3,3;-3125/2242397099259592704:3,3,3;475/996620933004263424:3,3,4;-3125/132411306314179689578496:0,0,0,0;625/4526882267151442378752:0,0,0,3;-3125/122784695567058258100224:0,0,1,3;-1/40363147786672668672:0,0,2,3;625/96159263844720181248:0,0,3,3;-25/40363147786672668672:0,0,3,4;-3125/6821371975947681005568:0,1,3,3;-1/6727191297778778112:0,2,3,3;625/55887435396931387392:0,3,3,3;-25/6727191297778778112:0,3,3,4;-3125/1515860439099484667904:1,3,3,3;1/1494931399506395136:2,3,3,3;-625/3669377071515697152:3,3,3,3;25/1494931399506395136:3,3,3,4;-625/529645225256718758313984:0,0,0,0,3;625/176548408418906252771328:0,0,0,3,3;3125/9808244912161458487296:0,0,3,3,3;3125/2179609980480324108288:0,3,3,3,3;-625/242178886720036012032:3,3,3,3,3"
compact_certificate_declaration theorem product_56_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_6 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_7 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_8 n_c7_0) [([],(0:ℚ))])))=product_56 := by
  decide +kernel
compact_certificate_declaration theorem product_56_value (v : ℕ→ℂ) :
    eval v product_56=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_6 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_7 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_8 n_c7_0) [([],(0:ℚ))]))) := by
  rw [←product_56_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_73 : Poly := rational_polynomial% "1875/1537995266981888:;-386875/1993241866008526848:0;625/519842400239878144:1;625/3075990533963776:3;19375/8969588397038370816:0,0;-625/42107234419430129664:0,1;15625/5979725598025580544:0,3;3125/18714326408635613184:1,3;-625/41525872208510976:3,3;3125/769274110757761449984:0,0,0;-625/1705342993986920251392:0,0,1;4375/42737450597653413888:0,0,3;-625/126321703258290388992:0,1,3;23125/161452591146690674688:0,3,3;-625/42107234419430129664:1,3,3;-625/527622846884610048:3,3,3;-625/4012463827702414835712:0,0,0,0;-625/629406090619986640896:0,0,0,3;-3125/122784695567058258100224:0,0,1,3;18125/3269414970720486162432:0,0,3,3;-3125/6821371975947681005568:0,1,3,3;4375/1453073320320216072192:0,3,3,3;-3125/1515860439099484667904:1,3,3,3;-625/5045393473334083584:3,3,3,3;-625/93466804457068016173056:0,0,0,0,3;-625/11034275526181640798208:0,0,0,3,3;625/3269414970720486162432:0,0,3,3,3;625/544902495120081027072:0,3,3,3,3;-625/242178886720036012032:3,3,3,3,3"
compact_certificate_declaration theorem partial_sum_73_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_72 product_56)=partial_sum_73 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_73_value (v : ℕ→ℂ) :
    eval v partial_sum_73=eval v partial_sum_72+eval v product_56 := by
  rw [←partial_sum_73_checked, eval_add]
compact_certificate_declaration noncomputable def product_57 : Poly := rational_polynomial% "-1875/1537995266981888:;386875/1993241866008526848:0;-625/519842400239878144:1;-625/3075990533963776:3;-19375/8969588397038370816:0,0;625/42107234419430129664:0,1;-15625/5979725598025580544:0,3;-3125/18714326408635613184:1,3;625/41525872208510976:3,3;-3125/769274110757761449984:0,0,0;625/1705342993986920251392:0,0,1;-4375/42737450597653413888:0,0,3;625/126321703258290388992:0,1,3;-23125/161452591146690674688:0,3,3;625/42107234419430129664:1,3,3;625/527622846884610048:3,3,3;625/4012463827702414835712:0,0,0,0;625/629406090619986640896:0,0,0,3;3125/122784695567058258100224:0,0,1,3;-18125/3269414970720486162432:0,0,3,3;3125/6821371975947681005568:0,1,3,3;-4375/1453073320320216072192:0,3,3,3;3125/1515860439099484667904:1,3,3,3;625/5045393473334083584:3,3,3,3;625/93466804457068016173056:0,0,0,0,3;625/11034275526181640798208:0,0,0,3,3;-625/3269414970720486162432:0,0,3,3,3;-625/544902495120081027072:0,3,3,3,3;625/242178886720036012032:3,3,3,3,3"
compact_certificate_declaration theorem product_57_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_5 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_6 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_7 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_8 n_c9_0) [([],(0:ℚ))]))))=product_57 := by
  decide +kernel
compact_certificate_declaration theorem product_57_value (v : ℕ→ℂ) :
    eval v product_57=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_5 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_6 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_7 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_8 n_c9_0) [([],(0:ℚ))])))) := by
  rw [←product_57_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_74 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_74_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_73 product_57)=partial_sum_74 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_74_value (v : ℕ→ℂ) :
    eval v partial_sum_74=eval v partial_sum_73+eval v product_57 := by
  rw [←partial_sum_74_checked, eval_add]
compact_certificate_declaration noncomputable def e8 : Poly := partial_sum_74
compact_certificate_declaration theorem checked_8 : checkZero e8=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_8 (y z w a b : ℂ) :
    (certificate y z w a b)[8]?=some 0 := by
  change some (((((((((c0_3 y z w a b)*(c1_5 y z w a b))+(((c0_4 y z w a b)*(c1_4 y z w a b))+(((c0_5 y z w a b)*(c1_3 y z w a b))+(((c0_6 y z w a b)*(c1_2 y z w a b))+(((c0_7 y z w a b)*(c1_1 y z w a b))+(((c0_8 y z w a b)*(c1_0 y z w a b))+0))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_6 y z w a b)*(c7_2 y z w a b))+(((c6_7 y z w a b)*(c7_1 y z w a b))+(((c6_8 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_5 y z w a b)*(c9_3 y z w a b))+(((c8_6 y z w a b)*(c9_2 y z w a b))+(((c8_7 y z w a b)*(c9_1 y z w a b))+(((c8_8 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e8 checked_8
  simp only [e8, eval_add, eval_mul, eval_scale, eval_pow, product_50_value, product_51_value, product_52_value, product_53_value, product_54_value, product_55_value, partial_sum_65_value, partial_sum_66_value, partial_sum_67_value, partial_sum_68_value, partial_sum_69_value, partial_sum_70_value, product_1_value, partial_sum_71_value, partial_sum_72_value, product_56_value, partial_sum_73_value, product_57_value, partial_sum_74_value, n_c0_3_value y z w a b 0, n_c0_4_value y z w a b 0, n_c0_5_value y z w a b 0, n_c0_6_value y z w a b 0, n_c0_7_value y z w a b 0, n_c0_8_value y z w a b 0, n_c1_0_value y z w a b 0, n_c1_1_value y z w a b 0, n_c1_2_value y z w a b 0, n_c1_3_value y z w a b 0, n_c1_4_value y z w a b 0, n_c1_5_value y z w a b 0, n_c6_6_value y z w a b 0, n_c6_7_value y z w a b 0, n_c6_8_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_5_value y z w a b 0, n_c8_6_value y z w a b 0, n_c8_7_value y z w a b 0, n_c8_8_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_8
compact_certificate_declaration noncomputable def product_58 : Poly := rational_polynomial% "-19375/24607924271710208:;108125/3986483732017053696:0;3/12303962135855104:2;625/6151981067927552:3;75/12303962135855104:4;-625/1261348368333520896:0,0;1/332206977668087808:0,2;625/689968338233720832:0,3;25/332206977668087808:0,4;1/20133756222308352:2,3;19375/3986483732017053696:3,3;25/20133756222308352:3,4;-38125/26155319765763889299456:0,0,0;-115625/2906146640640432144384:0,0,3;5/17939176794076741632:0,2,3;-33125/322905182293381349376:0,3,3;125/17939176794076741632:0,3,4;5/1993241866008526848:2,3,3;-625/2759873352934883328:3,3,3;125/1993241866008526848:3,3,4;625/44137102104726563192832:0,0,0,0;14375/78465959297291667898368:0,0,0,3;625/4359219960960648216576:0,0,3,3;-3125/968715546880144048128:0,3,3,3;625/1059290450513437516627968:0,0,0,0,3;625/58849469472968750923776:0,0,0,3,3;625/13077659882881944649728:0,0,3,3,3"
compact_certificate_declaration theorem product_58_checked :
    mulShort n_c0_4 n_c1_5=product_58 := by
  decide +kernel
compact_certificate_declaration theorem product_58_value (v : ℕ→ℂ) :
    eval v product_58=eval v n_c0_4*eval v n_c1_5 := by
  rw [←product_58_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_59 : Poly := rational_polynomial% "625/2895049914318848:;-101875/3986483732017053696:0;-1/12303962135855104:2;-625/34072510530060288:3;-25/12303962135855104:4;4375/13454382595557556224:0,0;-1/996620933004263424:0,2;-625/3261668508013953024:0,3;-25/996620933004263424:0,4;-1/110735659222695936:2,3;-625/332206977668087808:3,3;-25/110735659222695936:3,4;625/1089804990240162054144:0,0,0;64375/2906146640640432144384:0,0,3;26875/322905182293381349376:0,3,3;625/39232979648645833949184:0,0,0,3;625/2179609980480324108288:0,0,3,3;625/484357773440072024064:0,3,3,3"
compact_certificate_declaration theorem product_59_checked :
    mulShort n_c0_5 n_c1_4=product_59 := by
  decide +kernel
compact_certificate_declaration theorem product_59_value (v : ℕ→ℂ) :
    eval v product_59=eval v n_c0_5*eval v n_c1_4 := by
  rw [←product_59_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_60 : Poly := rational_polynomial% "-54375/98431697086840832:;96875/3986483732017053696:0;44375/885885273781567488:3;-19375/645810364586762698752:0,0;-625/664413955336175616:0,3;19375/7972967464034107392:3,3;-3125/4359219960960648216576:0,0,0;-625/176130099432753463296:0,0,3;-625/13454382595557556224:0,3,3;-3125/23918902392102322176:3,3,3;-625/1059290450513437516627968:0,0,0,0;-625/21399807081079545790464:0,0,0,3;625/13077659882881944649728:0,0,3,3;625/264195149149130194944:0,3,3,3"
compact_certificate_declaration theorem product_60_checked :
    mulShort n_c0_6 n_c1_3=product_60 := by
  decide +kernel
compact_certificate_declaration theorem product_60_value (v : ℕ→ℂ) :
    eval v product_60=eval v n_c0_6*eval v n_c1_3 := by
  rw [←product_60_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_61 : Poly := rational_polynomial% "625/249155233251065856:0;-625/13454382595557556224:0,0;-3125/17939176794076741632:0,3;-625/484357773440072024064:0,0,3;-625/53817530382230224896:0,3,3"
compact_certificate_declaration theorem product_61_checked :
    mulShort n_c0_7 n_c1_2=product_61 := by
  decide +kernel
compact_certificate_declaration theorem product_61_value (v : ℕ→ℂ) :
    eval v product_61=eval v n_c0_7*eval v n_c1_2 := by
  rw [←product_61_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_62 : Poly := rational_polynomial% "-625/996620933004263424:0;625/80726295573345337344:0,0;625/4484794198519185408:0,3;-625/726536660160108036096:0,0,3;-625/80726295573345337344:0,3,3"
compact_certificate_declaration theorem product_62_checked :
    mulShort n_c0_8 n_c1_1=product_62 := by
  decide +kernel
compact_certificate_declaration theorem product_62_value (v : ℕ→ℂ) :
    eval v product_62=eval v n_c0_8*eval v n_c1_1 := by
  rw [←product_62_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_75 : Poly := rational_polynomial% "625/332206977668087808:0;-3125/80726295573345337344:0,0;-625/17939176794076741632:0,3;-3125/1453073320320216072192:0,0,3;-3125/161452591146690674688:0,3,3"
compact_certificate_declaration theorem partial_sum_75_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_61 product_62)=partial_sum_75 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_75_value (v : ℕ→ℂ) :
    eval v partial_sum_75=eval v product_61+eval v product_62 := by
  rw [←partial_sum_75_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_76 : Poly := rational_polynomial% "-54375/98431697086840832:;104375/3986483732017053696:0;44375/885885273781567488:3;-44375/645810364586762698752:0,0;-4375/4484794198519185408:0,3;19375/7972967464034107392:3,3;-3125/4359219960960648216576:0,0,0;-33125/5812293281280864288768:0,0,3;-625/9497211243922980864:0,3,3;-3125/23918902392102322176:3,3,3;-625/1059290450513437516627968:0,0,0,0;-625/21399807081079545790464:0,0,0,3;625/13077659882881944649728:0,0,3,3;625/264195149149130194944:0,3,3,3"
compact_certificate_declaration theorem partial_sum_76_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_60 partial_sum_75)=partial_sum_76 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_76_value (v : ℕ→ℂ) :
    eval v partial_sum_76=eval v product_60+eval v partial_sum_75 := by
  rw [←partial_sum_76_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_77 : Poly := rational_polynomial% "-33125/98431697086840832:;625/996620933004263424:0;-1/12303962135855104:2;3125/98431697086840832:3;-25/12303962135855104:4;165625/645810364586762698752:0,0;-1/996620933004263424:0,2;-41875/35878353588153483264:0,3;-25/996620933004263424:0,4;-1/110735659222695936:2,3;4375/7972967464034107392:3,3;-25/110735659222695936:3,4;-625/4359219960960648216576:0,0,0;625/37988844975691923456:0,0,3;625/35878353588153483264:0,3,3;-3125/23918902392102322176:3,3,3;-625/1059290450513437516627968:0,0,0,0;-3125/235397877891875003695104:0,0,0,3;4375/13077659882881944649728:0,0,3,3;625/170949802390613655552:0,3,3,3"
compact_certificate_declaration theorem partial_sum_77_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_59 partial_sum_76)=partial_sum_77 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_77_value (v : ℕ→ℂ) :
    eval v partial_sum_77=eval v product_59+eval v partial_sum_76 := by
  rw [←partial_sum_77_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_78 : Poly := rational_polynomial% "-110625/98431697086840832:;36875/1328827910672351232:0;1/6151981067927552:2;13125/98431697086840832:3;25/6151981067927552:4;-11875/49677720352827899904:0,0;1/498310466502131712:0,2;-3125/11959451196051161088:0,3;25/498310466502131712:0,4;1/24607924271710208:2,3;14375/2657655821344702464:3,3;25/24607924271710208:3,4;-41875/26155319765763889299456:0,0,0;-135625/5812293281280864288768:0,0,3;5/17939176794076741632:0,2,3;-625/7338754143031394304:0,3,3;125/17939176794076741632:0,3,4;5/1993241866008526848:2,3,3;-25625/71756707176306966528:3,3,3;125/1993241866008526848:3,3,4;14375/1059290450513437516627968:0,0,0,0;625/3678091842060546932736:0,0,0,3;3125/6538829941440972324864:0,0,3,3;625/1453073320320216072192:0,3,3,3;625/1059290450513437516627968:0,0,0,0,3;625/58849469472968750923776:0,0,0,3,3;625/13077659882881944649728:0,0,3,3,3"
compact_certificate_declaration theorem partial_sum_78_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_58 partial_sum_77)=partial_sum_78 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_78_value (v : ℕ→ℂ) :
    eval v partial_sum_78=eval v product_58+eval v partial_sum_77 := by
  rw [←partial_sum_78_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_79 : Poly := rational_polynomial% "-110625/98431697086840832:;36875/1328827910672351232:0;1/6151981067927552:2;13125/98431697086840832:3;25/6151981067927552:4;-11875/49677720352827899904:0,0;1/498310466502131712:0,2;-3125/11959451196051161088:0,3;25/498310466502131712:0,4;1/24607924271710208:2,3;14375/2657655821344702464:3,3;25/24607924271710208:3,4;-41875/26155319765763889299456:0,0,0;-135625/5812293281280864288768:0,0,3;5/17939176794076741632:0,2,3;-625/7338754143031394304:0,3,3;125/17939176794076741632:0,3,4;5/1993241866008526848:2,3,3;-25625/71756707176306966528:3,3,3;125/1993241866008526848:3,3,4;14375/1059290450513437516627968:0,0,0,0;625/3678091842060546932736:0,0,0,3;3125/6538829941440972324864:0,0,3,3;625/1453073320320216072192:0,3,3,3;625/1059290450513437516627968:0,0,0,0,3;625/58849469472968750923776:0,0,0,3,3;625/13077659882881944649728:0,0,3,3,3"
compact_certificate_declaration theorem partial_sum_79_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_78 product_1)=partial_sum_79 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_79_value (v : ℕ→ℂ) :
    eval v partial_sum_79=eval v partial_sum_78+eval v product_1 := by
  rw [←partial_sum_79_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_80 : Poly := rational_polynomial% "-110625/98431697086840832:;36875/1328827910672351232:0;1/6151981067927552:2;13125/98431697086840832:3;25/6151981067927552:4;-11875/49677720352827899904:0,0;1/498310466502131712:0,2;-3125/11959451196051161088:0,3;25/498310466502131712:0,4;1/24607924271710208:2,3;14375/2657655821344702464:3,3;25/24607924271710208:3,4;-41875/26155319765763889299456:0,0,0;-135625/5812293281280864288768:0,0,3;5/17939176794076741632:0,2,3;-625/7338754143031394304:0,3,3;125/17939176794076741632:0,3,4;5/1993241866008526848:2,3,3;-25625/71756707176306966528:3,3,3;125/1993241866008526848:3,3,4;14375/1059290450513437516627968:0,0,0,0;625/3678091842060546932736:0,0,0,3;3125/6538829941440972324864:0,0,3,3;625/1453073320320216072192:0,3,3,3;625/1059290450513437516627968:0,0,0,0,3;625/58849469472968750923776:0,0,0,3,3;625/13077659882881944649728:0,0,3,3,3"
compact_certificate_declaration theorem partial_sum_80_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_79 product_1)=partial_sum_80 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_80_value (v : ℕ→ℂ) :
    eval v partial_sum_80=eval v partial_sum_79+eval v product_1 := by
  rw [←partial_sum_80_checked, eval_add]
compact_certificate_declaration noncomputable def product_63 : Poly := rational_polynomial% "-625/5790099828637696:;625/498310466502131712:0;-625/4158739201919025152:1;-1/6151981067927552:2;-625/17370299485913088:3;-25/6151981067927552:4;-625/16559240117609299968:0,0;-1/498310466502131712:0,2;-625/3986483732017053696:0,3;-25/498310466502131712:0,4;-1/24607924271710208:2,3;-11875/7972967464034107392:3,3;-25/24607924271710208:3,4;-625/726536660160108036096:0,0,0;625/27285487903790724022272:0,0,1;-625/49677720352827899904:0,0,3;625/1515860439099484667904:0,1,3;-5/17939176794076741632:0,2,3;-4375/322905182293381349376:0,3,3;-125/17939176794076741632:0,3,4;625/336857875355441037312:1,3,3;-5/1993241866008526848:2,3,3;19375/71756707176306966528:3,3,3;-125/1993241866008526848:3,3,4;-4375/117698938945937501847552:0,0,0,3;-3125/6538829941440972324864:0,0,3,3;625/1453073320320216072192:0,3,3,3;625/40363147786672668672:3,3,3,3"
compact_certificate_declaration theorem product_63_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_7 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_8 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_9 n_c7_0) [([],(0:ℚ))])))=product_63 := by
  decide +kernel
compact_certificate_declaration theorem product_63_value (v : ℕ→ℂ) :
    eval v product_63=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_7 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_8 n_c7_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_9 n_c7_0) [([],(0:ℚ))]))) := by
  rw [←product_63_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_81 : Poly := rational_polynomial% "-60625/49215848543420416:;115625/3986483732017053696:0;-625/4158739201919025152:1;14375/147647545630261248:3;-625/2258078197855813632:0,0;-625/1494931399506395136:0,3;15625/3986483732017053696:3,3;-64375/26155319765763889299456:0,0,0;625/27285487903790724022272:0,0,1;-104375/2906146640640432144384:0,0,3;625/1515860439099484667904:0,1,3;-625/6331474162615320576:0,3,3;625/336857875355441037312:1,3,3;-3125/35878353588153483264:3,3,3;14375/1059290450513437516627968:0,0,0,0;15625/117698938945937501847552:0,0,0,3;625/726536660160108036096:0,3,3,3;625/40363147786672668672:3,3,3,3;625/1059290450513437516627968:0,0,0,0,3;625/58849469472968750923776:0,0,0,3,3;625/13077659882881944649728:0,0,3,3,3"
compact_certificate_declaration theorem partial_sum_81_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_80 product_63)=partial_sum_81 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_81_value (v : ℕ→ℂ) :
    eval v partial_sum_81=eval v partial_sum_80+eval v product_63 := by
  rw [←partial_sum_81_checked, eval_add]
compact_certificate_declaration noncomputable def product_64 : Poly := rational_polynomial% "60625/49215848543420416:;-115625/3986483732017053696:0;625/4158739201919025152:1;-14375/147647545630261248:3;625/2258078197855813632:0,0;625/1494931399506395136:0,3;-15625/3986483732017053696:3,3;64375/26155319765763889299456:0,0,0;-625/27285487903790724022272:0,0,1;104375/2906146640640432144384:0,0,3;-625/1515860439099484667904:0,1,3;625/6331474162615320576:0,3,3;-625/336857875355441037312:1,3,3;3125/35878353588153483264:3,3,3;-14375/1059290450513437516627968:0,0,0,0;-15625/117698938945937501847552:0,0,0,3;-625/726536660160108036096:0,3,3,3;-625/40363147786672668672:3,3,3,3;-625/1059290450513437516627968:0,0,0,0,3;-625/58849469472968750923776:0,0,0,3,3;-625/13077659882881944649728:0,0,3,3,3"
compact_certificate_declaration theorem product_64_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_6 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_7 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_8 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_9 n_c9_0) [([],(0:ℚ))]))))=product_64 := by
  decide +kernel
compact_certificate_declaration theorem product_64_value (v : ℕ→ℂ) :
    eval v product_64=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_6 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_7 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_8 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_9 n_c9_0) [([],(0:ℚ))])))) := by
  rw [←product_64_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_82 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_82_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_81 product_64)=partial_sum_82 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_82_value (v : ℕ→ℂ) :
    eval v partial_sum_82=eval v partial_sum_81+eval v product_64 := by
  rw [←partial_sum_82_checked, eval_add]
compact_certificate_declaration noncomputable def e9 : Poly := partial_sum_82
compact_certificate_declaration theorem checked_9 : checkZero e9=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_9 (y z w a b : ℂ) :
    (certificate y z w a b)[9]?=some 0 := by
  change some (((((((((c0_4 y z w a b)*(c1_5 y z w a b))+(((c0_5 y z w a b)*(c1_4 y z w a b))+(((c0_6 y z w a b)*(c1_3 y z w a b))+(((c0_7 y z w a b)*(c1_2 y z w a b))+((c0_8 y z w a b)*(c1_1 y z w a b))))))+((-1)*0))+((-1)*0))+((-1)*(((c6_7 y z w a b)*(c7_2 y z w a b))+(((c6_8 y z w a b)*(c7_1 y z w a b))+(((c6_9 y z w a b)*(c7_0 y z w a b))+0)))))+((-1)*(((c8_6 y z w a b)*(c9_3 y z w a b))+(((c8_7 y z w a b)*(c9_2 y z w a b))+(((c8_8 y z w a b)*(c9_1 y z w a b))+(((c8_9 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e9 checked_9
  simp only [e9, eval_add, eval_mul, eval_scale, eval_pow, product_58_value, product_59_value, product_60_value, product_61_value, product_62_value, partial_sum_75_value, partial_sum_76_value, partial_sum_77_value, partial_sum_78_value, product_1_value, partial_sum_79_value, partial_sum_80_value, product_63_value, partial_sum_81_value, product_64_value, partial_sum_82_value, n_c0_4_value y z w a b 0, n_c0_5_value y z w a b 0, n_c0_6_value y z w a b 0, n_c0_7_value y z w a b 0, n_c0_8_value y z w a b 0, n_c1_1_value y z w a b 0, n_c1_2_value y z w a b 0, n_c1_3_value y z w a b 0, n_c1_4_value y z w a b 0, n_c1_5_value y z w a b 0, n_c6_7_value y z w a b 0, n_c6_8_value y z w a b 0, n_c6_9_value y z w a b 0, n_c7_0_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_6_value y z w a b 0, n_c8_7_value y z w a b 0, n_c8_8_value y z w a b 0, n_c8_9_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_9
compact_certificate_declaration noncomputable def product_65 : Poly := rational_polynomial% "625/11580199657275392:;-101875/15945934928068214784:0;-1/49215848543420416:2;-625/136290042120241152:3;-25/49215848543420416:4;4375/53817530382230224896:0,0;-1/3986483732017053696:0,2;-625/13046674032055812096:0,3;-25/3986483732017053696:0,4;-1/442942636890783744:2,3;-625/1328827910672351232:3,3;-25/442942636890783744:3,4;625/4359219960960648216576:0,0,0;64375/11624586562561728577536:0,0,3;26875/1291620729173525397504:0,3,3;625/156931918594583335796736:0,0,0,3;625/8718439921921296433152:0,0,3,3;625/1937431093760288096256:0,3,3,3"
compact_certificate_declaration theorem product_65_checked :
    mulShort n_c0_5 n_c1_5=product_65 := by
  decide +kernel
compact_certificate_declaration theorem product_65_value (v : ℕ→ℂ) :
    eval v product_65=eval v n_c0_5*eval v n_c1_5 := by
  rw [←product_65_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_66 : Poly := rational_polynomial% "-18125/196863394173681664:;70625/15945934928068214784:0;4375/885885273781567488:3;-625/26908765191115112448:0,0;-625/47837804784204644352:0,3;3125/5315311642689404928:3,3;-625/26155319765763889299456:0,0,0;-625/447099483175451099136:0,0,3;-625/58710033144251154432:0,3,3"
compact_certificate_declaration theorem product_66_checked :
    mulShort n_c0_6 n_c1_4=product_66 := by
  decide +kernel
compact_certificate_declaration theorem product_66_value (v : ℕ→ℂ) :
    eval v product_66=eval v n_c0_6*eval v n_c1_4 := by
  rw [←product_66_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_67 : Poly := rational_polynomial% "1875/24607924271710208:;-4375/3986483732017053696:0;-14375/1771770547563134976:3;-625/107635060764460449792:0,0;-625/71756707176306966528:0,3;-625/3986483732017053696:3,3;-625/3874862187520576192512:0,0,3;625/47837804784204644352:3,3,3"
compact_certificate_declaration theorem product_67_checked :
    mulShort n_c0_7 n_c1_3=product_67 := by
  decide +kernel
compact_certificate_declaration theorem product_67_value (v : ℕ→ℂ) :
    eval v product_67=eval v n_c0_7*eval v n_c1_3 := by
  rw [←product_67_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_68 : Poly := rational_polynomial% "-625/3986483732017053696:0;625/322905182293381349376:0,0;625/35878353588153483264:0,3"
compact_certificate_declaration theorem product_68_checked :
    mulShort n_c0_8 n_c1_2=product_68 := by
  decide +kernel
compact_certificate_declaration theorem product_68_value (v : ℕ→ℂ) :
    eval v product_68=eval v n_c0_8*eval v n_c1_2 := by
  rw [←product_68_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_83 : Poly := rational_polynomial% "1875/24607924271710208:;-625/498310466502131712:0;-14375/1771770547563134976:3;-625/161452591146690674688:0,0;625/71756707176306966528:0,3;-625/3986483732017053696:3,3;-625/3874862187520576192512:0,0,3;625/47837804784204644352:3,3,3"
compact_certificate_declaration theorem partial_sum_83_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_67 product_68)=partial_sum_83 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_83_value (v : ℕ→ℂ) :
    eval v partial_sum_83=eval v product_67+eval v product_68 := by
  rw [←partial_sum_83_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_84 : Poly := rational_polynomial% "-3125/196863394173681664:;625/196863394173681664:0;-625/196863394173681664:3;-4375/161452591146690674688:0,0;-625/143513414352613933056:0,3;625/1449630448006201344:3,3;-625/26155319765763889299456:0,0,0;-18125/11624586562561728577536:0,0,3;-625/58710033144251154432:0,3,3;625/47837804784204644352:3,3,3"
compact_certificate_declaration theorem partial_sum_84_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_66 partial_sum_83)=partial_sum_84 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_84_value (v : ℕ→ℂ) :
    eval v partial_sum_84=eval v product_66+eval v partial_sum_83 := by
  rw [←partial_sum_84_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_85 : Poly := rational_polynomial% "1875/49215848543420416:;-25625/7972967464034107392:0;-1/49215848543420416:2;-625/80535024889233408:3;-25/49215848543420416:4;4375/80726295573345337344:0,0;-1/3986483732017053696:0,2;-625/11959451196051161088:0,3;-25/3986483732017053696:0,4;-1/442942636890783744:2,3;-625/15945934928068214784:3,3;-25/442942636890783744:3,4;3125/26155319765763889299456:0,0,0;23125/5812293281280864288768:0,0,3;4375/430540243057841799168:0,3,3;625/47837804784204644352:3,3,3;625/156931918594583335796736:0,0,0,3;625/8718439921921296433152:0,0,3,3;625/1937431093760288096256:0,3,3,3"
compact_certificate_declaration theorem partial_sum_85_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_65 partial_sum_84)=partial_sum_85 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_85_value (v : ℕ→ℂ) :
    eval v partial_sum_85=eval v product_65+eval v partial_sum_84 := by
  rw [←partial_sum_85_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_86 : Poly := rational_polynomial% "1875/49215848543420416:;-25625/7972967464034107392:0;-1/49215848543420416:2;-625/80535024889233408:3;-25/49215848543420416:4;4375/80726295573345337344:0,0;-1/3986483732017053696:0,2;-625/11959451196051161088:0,3;-25/3986483732017053696:0,4;-1/442942636890783744:2,3;-625/15945934928068214784:3,3;-25/442942636890783744:3,4;3125/26155319765763889299456:0,0,0;23125/5812293281280864288768:0,0,3;4375/430540243057841799168:0,3,3;625/47837804784204644352:3,3,3;625/156931918594583335796736:0,0,0,3;625/8718439921921296433152:0,0,3,3;625/1937431093760288096256:0,3,3,3"
compact_certificate_declaration theorem partial_sum_86_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_85 product_1)=partial_sum_86 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_86_value (v : ℕ→ℂ) :
    eval v partial_sum_86=eval v partial_sum_85+eval v product_1 := by
  rw [←partial_sum_86_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_87 : Poly := rational_polynomial% "1875/49215848543420416:;-25625/7972967464034107392:0;-1/49215848543420416:2;-625/80535024889233408:3;-25/49215848543420416:4;4375/80726295573345337344:0,0;-1/3986483732017053696:0,2;-625/11959451196051161088:0,3;-25/3986483732017053696:0,4;-1/442942636890783744:2,3;-625/15945934928068214784:3,3;-25/442942636890783744:3,4;3125/26155319765763889299456:0,0,0;23125/5812293281280864288768:0,0,3;4375/430540243057841799168:0,3,3;625/47837804784204644352:3,3,3;625/156931918594583335796736:0,0,0,3;625/8718439921921296433152:0,0,3,3;625/1937431093760288096256:0,3,3,3"
compact_certificate_declaration theorem partial_sum_87_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_86 product_1)=partial_sum_87 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_87_value (v : ℕ→ℂ) :
    eval v partial_sum_87=eval v partial_sum_86+eval v product_1 := by
  rw [←partial_sum_87_checked, eval_add]
compact_certificate_declaration noncomputable def product_69 : Poly := rational_polynomial% "625/24607924271710208:;625/2657655821344702464:0;1/49215848543420416:2;625/161070049778466816:3;25/49215848543420416:4;1/3986483732017053696:0,2;-625/35878353588153483264:0,3;25/3986483732017053696:0,4;1/442942636890783744:2,3;-625/3986483732017053696:3,3;25/442942636890783744:3,4;625/52310639531527778598912:0,0,0;-625/3874862187520576192512:0,0,3;-625/107635060764460449792:0,3,3;-4375/143513414352613933056:3,3,3"
compact_certificate_declaration theorem product_69_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_8 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.mul n_c6_9 n_c7_1))=product_69 := by
  decide +kernel
compact_certificate_declaration theorem product_69_value (v : ℕ→ℂ) :
    eval v product_69=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c6_8 n_c7_2) (SmallLevelSparseRationalPolynomialCheck.mul n_c6_9 n_c7_1)) := by
  rw [←product_69_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_88 : Poly := rational_polynomial% "3125/49215848543420416:;-11875/3986483732017053696:0;-625/161070049778466816:3;4375/80726295573345337344:0,0;-625/8969588397038370816:0,3;-3125/15945934928068214784:3,3;625/4755512684684343508992:0,0,0;44375/11624586562561728577536:0,0,3;625/143513414352613933056:0,3,3;-625/35878353588153483264:3,3,3;625/156931918594583335796736:0,0,0,3;625/8718439921921296433152:0,0,3,3;625/1937431093760288096256:0,3,3,3"
compact_certificate_declaration theorem partial_sum_88_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_87 product_69)=partial_sum_88 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_88_value (v : ℕ→ℂ) :
    eval v partial_sum_88=eval v partial_sum_87+eval v product_69 := by
  rw [←partial_sum_88_checked, eval_add]
compact_certificate_declaration noncomputable def product_70 : Poly := rational_polynomial% "-3125/49215848543420416:;11875/3986483732017053696:0;625/161070049778466816:3;-4375/80726295573345337344:0,0;625/8969588397038370816:0,3;3125/15945934928068214784:3,3;-625/4755512684684343508992:0,0,0;-44375/11624586562561728577536:0,0,3;-625/143513414352613933056:0,3,3;625/35878353588153483264:3,3,3;-625/156931918594583335796736:0,0,0,3;-625/8718439921921296433152:0,0,3,3;-625/1937431093760288096256:0,3,3,3"
compact_certificate_declaration theorem product_70_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_7 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_8 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_9 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_10 n_c9_0) [([],(0:ℚ))]))))=product_70 := by
  decide +kernel
compact_certificate_declaration theorem product_70_value (v : ℕ→ℂ) :
    eval v product_70=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_7 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_8 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_9 n_c9_1) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_10 n_c9_0) [([],(0:ℚ))])))) := by
  rw [←product_70_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_89 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_89_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_88 product_70)=partial_sum_89 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_89_value (v : ℕ→ℂ) :
    eval v partial_sum_89=eval v partial_sum_88+eval v product_70 := by
  rw [←partial_sum_89_checked, eval_add]
compact_certificate_declaration noncomputable def e10 : Poly := partial_sum_89
compact_certificate_declaration theorem checked_10 : checkZero e10=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_10 (y z w a b : ℂ) :
    (certificate y z w a b)[10]?=some 0 := by
  change some (((((((((c0_5 y z w a b)*(c1_5 y z w a b))+(((c0_6 y z w a b)*(c1_4 y z w a b))+(((c0_7 y z w a b)*(c1_3 y z w a b))+((c0_8 y z w a b)*(c1_2 y z w a b)))))+((-1)*0))+((-1)*0))+((-1)*(((c6_8 y z w a b)*(c7_2 y z w a b))+((c6_9 y z w a b)*(c7_1 y z w a b)))))+((-1)*(((c8_7 y z w a b)*(c9_3 y z w a b))+(((c8_8 y z w a b)*(c9_2 y z w a b))+(((c8_9 y z w a b)*(c9_1 y z w a b))+(((c8_10 y z w a b)*(c9_0 y z w a b))+0))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e10 checked_10
  simp only [e10, eval_add, eval_mul, eval_scale, eval_pow, product_65_value, product_66_value, product_67_value, product_68_value, partial_sum_83_value, partial_sum_84_value, partial_sum_85_value, product_1_value, partial_sum_86_value, partial_sum_87_value, product_69_value, partial_sum_88_value, product_70_value, partial_sum_89_value, n_c0_5_value y z w a b 0, n_c0_6_value y z w a b 0, n_c0_7_value y z w a b 0, n_c0_8_value y z w a b 0, n_c1_2_value y z w a b 0, n_c1_3_value y z w a b 0, n_c1_4_value y z w a b 0, n_c1_5_value y z w a b 0, n_c6_8_value y z w a b 0, n_c6_9_value y z w a b 0, n_c7_1_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_10_value y z w a b 0, n_c8_7_value y z w a b 0, n_c8_8_value y z w a b 0, n_c8_9_value y z w a b 0, n_c9_0_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_10
compact_certificate_declaration noncomputable def product_71 : Poly := rational_polynomial% "-18125/787453576694726656:;70625/63783739712272859136:0;4375/3543541095126269952:3;-625/107635060764460449792:0,0;-625/191351219136818577408:0,3;3125/21261246570757619712:3,3;-625/104621279063055557197824:0,0,0;-625/1788397932701804396544:0,0,3;-625/234840132577004617728:0,3,3"
compact_certificate_declaration theorem product_71_checked :
    mulShort n_c0_6 n_c1_5=product_71 := by
  decide +kernel
compact_certificate_declaration theorem product_71_value (v : ℕ→ℂ) :
    eval v product_71=eval v n_c0_6*eval v n_c1_5 := by
  rw [←product_71_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_72 : Poly := rational_polynomial% "625/49215848543420416:;-625/2657655821344702464:0;-3125/3543541095126269952:3;-625/95675609568409288704:0,3;-625/10630623285378809856:3,3"
compact_certificate_declaration theorem product_72_checked :
    mulShort n_c0_7 n_c1_4=product_72 := by
  decide +kernel
compact_certificate_declaration theorem product_72_value (v : ℕ→ℂ) :
    eval v product_72=eval v n_c0_7*eval v n_c1_4 := by
  rw [←product_72_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_73 : Poly := rational_polynomial% "-1875/393726788347363328:;625/15945934928068214784:0;625/885885273781567488:3;625/2583241458347050795008:0,0;-625/31891869856136429568:3,3"
compact_certificate_declaration theorem product_73_checked :
    mulShort n_c0_8 n_c1_3=product_73 := by
  decide +kernel
compact_certificate_declaration theorem product_73_value (v : ℕ→ℂ) :
    eval v product_73=eval v n_c0_8*eval v n_c1_3 := by
  rw [←product_73_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_90 : Poly := rational_polynomial% "3125/393726788347363328:;-3125/15945934928068214784:0;-625/3543541095126269952:3;625/2583241458347050795008:0,0;-625/95675609568409288704:0,3;-625/7972967464034107392:3,3"
compact_certificate_declaration theorem partial_sum_90_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_72 product_73)=partial_sum_90 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_90_value (v : ℕ→ℂ) :
    eval v partial_sum_90=eval v product_72+eval v product_73 := by
  rw [←partial_sum_90_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_91 : Poly := rational_polynomial% "-11875/787453576694726656:;19375/21261246570757619712:0;625/590590182521044992:3;-14375/2583241458347050795008:0,0;-625/63783739712272859136:0,3;4375/63783739712272859136:3,3;-625/104621279063055557197824:0,0,0;-625/1788397932701804396544:0,0,3;-625/234840132577004617728:0,3,3"
compact_certificate_declaration theorem partial_sum_91_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_71 partial_sum_90)=partial_sum_91 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_91_value (v : ℕ→ℂ) :
    eval v partial_sum_91=eval v product_71+eval v partial_sum_90 := by
  rw [←partial_sum_91_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_92 : Poly := rational_polynomial% "-11875/787453576694726656:;19375/21261246570757619712:0;625/590590182521044992:3;-14375/2583241458347050795008:0,0;-625/63783739712272859136:0,3;4375/63783739712272859136:3,3;-625/104621279063055557197824:0,0,0;-625/1788397932701804396544:0,0,3;-625/234840132577004617728:0,3,3"
compact_certificate_declaration theorem partial_sum_92_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_91 product_1)=partial_sum_92 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_92_value (v : ℕ→ℂ) :
    eval v partial_sum_92=eval v partial_sum_91+eval v product_1 := by
  rw [←partial_sum_92_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_93 : Poly := rational_polynomial% "-11875/787453576694726656:;19375/21261246570757619712:0;625/590590182521044992:3;-14375/2583241458347050795008:0,0;-625/63783739712272859136:0,3;4375/63783739712272859136:3,3;-625/104621279063055557197824:0,0,0;-625/1788397932701804396544:0,0,3;-625/234840132577004617728:0,3,3"
compact_certificate_declaration theorem partial_sum_93_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_92 product_1)=partial_sum_93 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_93_value (v : ℕ→ℂ) :
    eval v partial_sum_93=eval v partial_sum_92+eval v product_1 := by
  rw [←partial_sum_93_checked, eval_add]
compact_certificate_declaration noncomputable def product_74 : Poly := rational_polynomial% "-625/393726788347363328:;625/2583241458347050795008:0,0;625/143513414352613933056:0,3;625/31891869856136429568:3,3"
compact_certificate_declaration theorem product_74_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.mul n_c6_9 n_c7_2)=product_74 := by
  decide +kernel
compact_certificate_declaration theorem product_74_value (v : ℕ→ℂ) :
    eval v product_74=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.mul n_c6_9 n_c7_2) := by
  rw [←product_74_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_94 : Poly := rational_polynomial% "-13125/787453576694726656:;19375/21261246570757619712:0;625/590590182521044992:3;-625/117420066288502308864:0,0;-3125/574053657410455732224:0,3;625/7087082190252539904:3,3;-625/104621279063055557197824:0,0,0;-625/1788397932701804396544:0,0,3;-625/234840132577004617728:0,3,3"
compact_certificate_declaration theorem partial_sum_94_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_93 product_74)=partial_sum_94 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_94_value (v : ℕ→ℂ) :
    eval v partial_sum_94=eval v partial_sum_93+eval v product_74 := by
  rw [←partial_sum_94_checked, eval_add]
compact_certificate_declaration noncomputable def product_75 : Poly := rational_polynomial% "13125/787453576694726656:;-19375/21261246570757619712:0;-625/590590182521044992:3;625/117420066288502308864:0,0;3125/574053657410455732224:0,3;-625/7087082190252539904:3,3;625/104621279063055557197824:0,0,0;625/1788397932701804396544:0,0,3;625/234840132577004617728:0,3,3"
compact_certificate_declaration theorem product_75_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_8 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_9 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.mul n_c8_10 n_c9_1)))=product_75 := by
  decide +kernel
compact_certificate_declaration theorem product_75_value (v : ℕ→ℂ) :
    eval v product_75=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_8 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_9 n_c9_2) (SmallLevelSparseRationalPolynomialCheck.mul n_c8_10 n_c9_1))) := by
  rw [←product_75_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_95 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_95_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_94 product_75)=partial_sum_95 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_95_value (v : ℕ→ℂ) :
    eval v partial_sum_95=eval v partial_sum_94+eval v product_75 := by
  rw [←partial_sum_95_checked, eval_add]
compact_certificate_declaration noncomputable def e11 : Poly := partial_sum_95
compact_certificate_declaration theorem checked_11 : checkZero e11=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_11 (y z w a b : ℂ) :
    (certificate y z w a b)[11]?=some 0 := by
  change some (((((((((c0_6 y z w a b)*(c1_5 y z w a b))+(((c0_7 y z w a b)*(c1_4 y z w a b))+((c0_8 y z w a b)*(c1_3 y z w a b))))+((-1)*0))+((-1)*0))+((-1)*((c6_9 y z w a b)*(c7_2 y z w a b))))+((-1)*(((c8_8 y z w a b)*(c9_3 y z w a b))+(((c8_9 y z w a b)*(c9_2 y z w a b))+((c8_10 y z w a b)*(c9_1 y z w a b))))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e11 checked_11
  simp only [e11, eval_add, eval_mul, eval_scale, eval_pow, product_71_value, product_72_value, product_73_value, partial_sum_90_value, partial_sum_91_value, product_1_value, partial_sum_92_value, partial_sum_93_value, product_74_value, partial_sum_94_value, product_75_value, partial_sum_95_value, n_c0_6_value y z w a b 0, n_c0_7_value y z w a b 0, n_c0_8_value y z w a b 0, n_c1_3_value y z w a b 0, n_c1_4_value y z w a b 0, n_c1_5_value y z w a b 0, n_c6_9_value y z w a b 0, n_c7_2_value y z w a b 0, n_c8_10_value y z w a b 0, n_c8_8_value y z w a b 0, n_c8_9_value y z w a b 0, n_c9_1_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_11
compact_certificate_declaration noncomputable def product_76 : Poly := rational_polynomial% "625/196863394173681664:;-625/10630623285378809856:0;-3125/14174164380505079808:3;-625/382702438273637154816:0,3;-625/42522493141515239424:3,3"
compact_certificate_declaration theorem product_76_checked :
    mulShort n_c0_7 n_c1_5=product_76 := by
  decide +kernel
compact_certificate_declaration theorem product_76_value (v : ℕ→ℂ) :
    eval v product_76=eval v n_c0_7*eval v n_c1_5 := by
  rw [←product_76_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_77 : Poly := rational_polynomial% "-625/787453576694726656:;625/63783739712272859136:0;625/7087082190252539904:3"
compact_certificate_declaration theorem product_77_checked :
    mulShort n_c0_8 n_c1_4=product_77 := by
  decide +kernel
compact_certificate_declaration theorem product_77_value (v : ℕ→ℂ) :
    eval v product_77=eval v n_c0_8*eval v n_c1_4 := by
  rw [←product_77_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_96 : Poly := rational_polynomial% "1875/787453576694726656:;-3125/63783739712272859136:0;-625/4724721460168359936:3;-625/382702438273637154816:0,3;-625/42522493141515239424:3,3"
compact_certificate_declaration theorem partial_sum_96_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_76 product_77)=partial_sum_96 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_96_value (v : ℕ→ℂ) :
    eval v partial_sum_96=eval v product_76+eval v product_77 := by
  rw [←partial_sum_96_checked, eval_add]
compact_certificate_declaration noncomputable def partial_sum_97 : Poly := rational_polynomial% "1875/787453576694726656:;-3125/63783739712272859136:0;-625/4724721460168359936:3;-625/382702438273637154816:0,3;-625/42522493141515239424:3,3"
compact_certificate_declaration theorem partial_sum_97_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_96 product_1)=partial_sum_97 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_97_value (v : ℕ→ℂ) :
    eval v partial_sum_97=eval v partial_sum_96+eval v product_1 := by
  rw [←partial_sum_97_checked, eval_add]
compact_certificate_declaration noncomputable def product_78 : Poly := rational_polynomial% "-1875/787453576694726656:;3125/63783739712272859136:0;625/4724721460168359936:3;625/382702438273637154816:0,3;625/42522493141515239424:3,3"
compact_certificate_declaration theorem product_78_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_9 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.mul n_c8_10 n_c9_2))=product_78 := by
  decide +kernel
compact_certificate_declaration theorem product_78_value (v : ℕ→ℂ) :
    eval v product_78=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.add (SmallLevelSparseRationalPolynomialCheck.mul n_c8_9 n_c9_3) (SmallLevelSparseRationalPolynomialCheck.mul n_c8_10 n_c9_2)) := by
  rw [←product_78_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_98 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_98_checked :
    (SmallLevelSparseRationalPolynomialCheck.add partial_sum_97 product_78)=partial_sum_98 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_98_value (v : ℕ→ℂ) :
    eval v partial_sum_98=eval v partial_sum_97+eval v product_78 := by
  rw [←partial_sum_98_checked, eval_add]
compact_certificate_declaration noncomputable def e12 : Poly := partial_sum_98
compact_certificate_declaration theorem checked_12 : checkZero e12=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_12 (y z w a b : ℂ) :
    (certificate y z w a b)[12]?=some 0 := by
  change some (((((((c0_7 y z w a b)*(c1_5 y z w a b))+((c0_8 y z w a b)*(c1_4 y z w a b)))+((-1)*0))+((-1)*(((c8_9 y z w a b)*(c9_3 y z w a b))+((c8_10 y z w a b)*(c9_2 y z w a b)))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e12 checked_12
  simp only [e12, eval_add, eval_mul, eval_scale, eval_pow, product_76_value, product_77_value, partial_sum_96_value, product_1_value, partial_sum_97_value, product_78_value, partial_sum_98_value, n_c0_7_value y z w a b 0, n_c0_8_value y z w a b 0, n_c1_4_value y z w a b 0, n_c1_5_value y z w a b 0, n_c8_10_value y z w a b 0, n_c8_9_value y z w a b 0, n_c9_2_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_12
compact_certificate_declaration noncomputable def product_79 : Poly := rational_polynomial% "-625/3149814306778906624:;625/255134958849091436544:0;625/28348328761010159616:3"
compact_certificate_declaration theorem product_79_checked :
    mulShort n_c0_8 n_c1_5=product_79 := by
  decide +kernel
compact_certificate_declaration theorem product_79_value (v : ℕ→ℂ) :
    eval v product_79=eval v n_c0_8*eval v n_c1_5 := by
  rw [←product_79_checked, eval_mulShort]
compact_certificate_declaration noncomputable def product_80 : Poly := rational_polynomial% "625/3149814306778906624:;-625/255134958849091436544:0;-625/28348328761010159616:3"
compact_certificate_declaration theorem product_80_checked :
    mulShort (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))]) (SmallLevelSparseRationalPolynomialCheck.mul n_c8_10 n_c9_3)=product_80 := by
  decide +kernel
compact_certificate_declaration theorem product_80_value (v : ℕ→ℂ) :
    eval v product_80=eval v (SmallLevelSparseRationalPolynomialCheck.scale [] (-1) [([],(1:ℚ))])*eval v (SmallLevelSparseRationalPolynomialCheck.mul n_c8_10 n_c9_3) := by
  rw [←product_80_checked, eval_mulShort]
compact_certificate_declaration noncomputable def partial_sum_99 : Poly := rational_polynomial% ""
compact_certificate_declaration theorem partial_sum_99_checked :
    (SmallLevelSparseRationalPolynomialCheck.add product_79 product_80)=partial_sum_99 := by
  decide +kernel
compact_certificate_declaration theorem partial_sum_99_value (v : ℕ→ℂ) :
    eval v partial_sum_99=eval v product_79+eval v product_80 := by
  rw [←partial_sum_99_checked, eval_add]
compact_certificate_declaration noncomputable def e13 : Poly := partial_sum_99
compact_certificate_declaration theorem checked_13 : checkZero e13=true := by
  decide +kernel
compact_certificate_declaration theorem coefficient_13 (y z w a b : ℂ) :
    (certificate y z w a b)[13]?=some 0 := by
  change some (((((c0_8 y z w a b)*(c1_5 y z w a b))+((-1)*((c8_10 y z w a b)*(c9_3 y z w a b))))))=some (0:ℂ)
  apply congrArg some
  have h := eval_of_checkZero (vars y z w a b 0) e13 checked_13
  simp only [e13, eval_add, eval_mul, eval_scale, eval_pow, product_79_value, product_80_value, partial_sum_99_value, n_c0_8_value y z w a b 0, n_c1_5_value y z w a b 0, n_c8_10_value y z w a b 0, n_c9_3_value y z w a b 0] at h
  simpa only [sub_eq_add_neg, eval, monomialValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Rat.cast_natCast, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, one_mul, mul_one, zero_add, add_zero, zero_mul, mul_zero, neg_one_mul] using h
#print axioms coefficient_13
end SmallLevelTwentySixMMPPariSyzygy6Column5

}
