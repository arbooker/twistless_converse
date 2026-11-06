module
public import QuantitativeArithmeticRationalRecurrenceV1
public import SmallLevelThirtyFourUnitMMMInhomogeneousTheoryV4
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticCompact34MMMRecurrence
open QuantitativeArithmeticRationalRecurrence
open SmallLevelThirtyFourUnitMMMInhomogeneous
def instruction0 : List (Coefficient × ℕ) :=
  [((.rat (1)), 19)]
def instruction1 : List (Coefficient × ℕ) :=
  [((.rat (1)), 47)]
def instruction2 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.param 3) 2)), 59), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.param 3) 2))), 546)]
def instruction3 : List (Coefficient × ℕ) :=
  [((.rat (1)), 10), ((.neg (.mul (.rat (-1)) (.param 0))), 548)]
def instruction4 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 4), ((.rat (1)), 549)]
def instruction5 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 22), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 549)]
def instruction6 : List (Coefficient × ℕ) :=
  [((.rat (1)), 26), ((.neg (.param 2)), 548)]
def instruction7 : List (Coefficient × ℕ) :=
  [((.rat (1)), 28), ((.neg (.mul (.mul (.pow (.invParam 1) 2) (.invParam 2)) (.pow (.invParam 3) 2))), 552)]
def instruction8 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.pow (.invParam 3) 2)), 40), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 549)]
def instruction9 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.param 0)), 44), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 548)]
def instruction10 : List (Coefficient × ℕ) :=
  [((.param 2), 27), ((.mul (.rat (-1)) (.param 2)), 555)]
def instruction11 : List (Coefficient × ℕ) :=
  [((.rat (1)), 7), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 556)]
def instruction12 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 1), ((.rat (1)), 557)]
def instruction13 : List (Coefficient × ℕ) :=
  [((.invParam 2), 25), ((.mul (.rat (-1)) (.invParam 2)), 556)]
def instruction14 : List (Coefficient × ℕ) :=
  [((.rat (1)), 29), ((.neg (.mul (.param 2) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 559)]
def instruction15 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 33), ((.rat (1)), 555)]
def instruction16 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.param 0)), 51), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.param 0))), 551)]
def instruction17 : List (Coefficient × ℕ) :=
  [((.rat (1)), 60), ((.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))), 559)]
def instruction18 : List (Coefficient × ℕ) :=
  [((.rat (1)), 62), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 555)]
def instruction19 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0)), 23), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0))), 564)]
def instruction20 : List (Coefficient × ℕ) :=
  [((.rat (1)), 76), ((.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))), 561)]
def instruction21 : List (Coefficient × ℕ) :=
  [((.rat (1)), 79), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 3) 2)) (.pow (.invParam 1) 2))), 562)]
def instruction22 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.pow (.invParam 3) 2)), 31), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 567)]
def instruction23 : List (Coefficient × ℕ) :=
  [((.rat (1)), 81), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 559)]
def instruction24 : List (Coefficient × ℕ) :=
  [((.rat (1)), 88)]
def instruction25 : List (Coefficient × ℕ) :=
  [((.rat (1)), 101), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 548)]
def instruction26 : List (Coefficient × ℕ) :=
  [((.rat (1)), 95), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.invParam 0))), 571)]
def instruction27 : List (Coefficient × ℕ) :=
  [((.rat (1)), 74), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2))), 572)]
def instruction28 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 100), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 573)]
def instruction29 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 104), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 561)]
def instruction30 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)), 105), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2))), 554)]
def instruction31 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.pow (.invParam 1) 2) (.invParam 2)) (.param 0)), 110), ((.mul (.rat (-1)) (.mul (.mul (.pow (.invParam 1) 2) (.invParam 2)) (.param 0))), 552)]
def instruction32 : List (Coefficient × ℕ) :=
  [((.rat (1)), 111), ((.neg (.mul (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.invParam 2)) (.pow (.invParam 3) 2))), 556)]
def instruction33 : List (Coefficient × ℕ) :=
  [((.rat (1)), 112), ((.neg (.mul (.param 0) (.mul (.mul (.pow (.invParam 1) 2) (.invParam 2)) (.pow (.invParam 3) 2)))), 552)]
def instruction34 : List (Coefficient × ℕ) :=
  [((.rat (1)), 113), ((.neg (.mul (.mul (.invParam 0) (.invParam 2)) (.pow (.invParam 3) 2))), 556)]
def instruction35 : List (Coefficient × ℕ) :=
  [((.rat (1)), 114), ((.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.invParam 2))), 556)]
def instruction36 : List (Coefficient × ℕ) :=
  [((.rat (1)), 115), ((.neg (.mul (.param 0) (.mul (.invParam 2) (.pow (.invParam 3) 2)))), 552)]
def instruction37 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.invParam 2) (.pow (.invParam 3) 2)) (.mul (.param 0) (.pow (.param 1) 2))), 123), ((.mul (.rat (-1)) (.mul (.mul (.invParam 2) (.pow (.invParam 3) 2)) (.mul (.param 0) (.pow (.param 1) 2)))), 558)]
def instruction38 : List (Coefficient × ℕ) :=
  [((.rat (1)), 127), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 2) (.pow (.invParam 3) 2)))), 558)]
def instruction39 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.invParam 2) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 129), ((.mul (.rat (-1)) (.mul (.mul (.invParam 2) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 557)]
def instruction40 : List (Coefficient × ℕ) :=
  [((.rat (1)), 148), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 552)]
def instruction41 : List (Coefficient × ℕ) :=
  [((.rat (1)), 149), ((.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))), 559)]
def instruction42 : List (Coefficient × ℕ) :=
  [((.rat (1)), 150), ((.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))), 549)]
def instruction43 : List (Coefficient × ℕ) :=
  [((.rat (1)), 155), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 1) 2))), 548)]
def instruction44 : List (Coefficient × ℕ) :=
  [((.rat (1)), 50), ((.neg (.mul (.rat (-1)) (.invParam 0))), 589)]
def instruction45 : List (Coefficient × ℕ) :=
  [((.rat (1)), 133), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))), 590)]
def instruction46 : List (Coefficient × ℕ) :=
  [((.rat (1)), 156), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))), 581)]
def instruction47 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 172), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 547)]
def instruction48 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 176), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 561)]
def instruction49 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 179), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 590)]
def instruction50 : List (Coefficient × ℕ) :=
  [((.rat (1)), 180), ((.neg (.mul (.mul (.pow (.invParam 1) 2) (.invParam 2)) (.pow (.invParam 3) 2))), 556)]
def instruction51 : List (Coefficient × ℕ) :=
  [((.rat (1)), 181), ((.neg (.mul (.mul (.pow (.invParam 1) 2) (.invParam 2)) (.pow (.invParam 3) 2))), 556)]
def instruction52 : List (Coefficient × ℕ) :=
  [((.rat (1)), 184), ((.neg (.mul (.param 0) (.mul (.mul (.pow (.invParam 1) 2) (.invParam 2)) (.pow (.invParam 3) 2)))), 552)]
def instruction53 : List (Coefficient × ℕ) :=
  [((.rat (1)), 185), ((.neg (.mul (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.invParam 2)) (.pow (.invParam 3) 2))), 556)]
def instruction54 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.pow (.invParam 3) 2)), 0)]
def instruction55 : List (Coefficient × ℕ) :=
  [((.rat (1)), 2)]
def instruction56 : List (Coefficient × ℕ) :=
  [((.rat (1)), 3)]
def instruction57 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.pow (.invParam 3) 2)), 5)]
def instruction58 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.param 0)), 6)]
def instruction59 : List (Coefficient × ℕ) :=
  [((.rat (1)), 8)]
def instruction60 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.mul (.param 0) (.pow (.param 3) 2))), 9), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.mul (.param 0) (.pow (.param 3) 2)))), 601)]
def instruction61 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 11)]
def instruction62 : List (Coefficient × ℕ) :=
  [((.rat (1)), 12), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2)) (.pow (.invParam 1) 2))), 601)]
def instruction63 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)), 13)]
def instruction64 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0)), 14)]
def instruction65 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 15)]
def instruction66 : List (Coefficient × ℕ) :=
  [((.rat (1)), 16)]
def instruction67 : List (Coefficient × ℕ) :=
  [((.rat (1)), 17)]
def instruction68 : List (Coefficient × ℕ) :=
  [((.rat (1)), 18)]
def instruction69 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.param 1) 2)), 20), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.param 1) 2))), 605)]
def instruction70 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.param 0)), 21), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 601)]
def instruction71 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)), 24)]
def instruction72 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)) (.param 2)), 30)]
def instruction73 : List (Coefficient × ℕ) :=
  [((.rat (1)), 32)]
def instruction74 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 34)]
def instruction75 : List (Coefficient × ℕ) :=
  [((.rat (1)), 35)]
def instruction76 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0)), 36)]
def instruction77 : List (Coefficient × ℕ) :=
  [((.rat (1)), 37), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2))), 601)]
def instruction78 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0)), 38), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.param 3) 2)) (.invParam 0))) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0))), 602)]
def instruction79 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 39)]
def instruction80 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 3) 2)), 41)]
def instruction81 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.param 0)), 42)]
def instruction82 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 43), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 606)]
def instruction83 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.param 3) 2)), 45), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.param 3) 2))), 604)]
def instruction84 : List (Coefficient × ℕ) :=
  [((.rat (1)), 46)]
def instruction85 : List (Coefficient × ℕ) :=
  [((.rat (1)), 48)]
def instruction86 : List (Coefficient × ℕ) :=
  [((.rat (1)), 49)]
def instruction87 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 52)]
def instruction88 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0)), 53)]
def instruction89 : List (Coefficient × ℕ) :=
  [((.rat (1)), 54)]
def instruction90 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)) (.pow (.param 3) 2)), 55)]
def instruction91 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.param 0)), 56)]
def instruction92 : List (Coefficient × ℕ) :=
  [((.rat (1)), 57)]
def instruction93 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.mul (.param 0) (.pow (.param 3) 2))), 58), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.mul (.param 0) (.pow (.param 3) 2)))), 612)]
def instruction94 : List (Coefficient × ℕ) :=
  [((.rat (1)), 61)]
def instruction95 : List (Coefficient × ℕ) :=
  [((.rat (1)), 63)]
def instruction96 : List (Coefficient × ℕ) :=
  [((.rat (1)), 64)]
def instruction97 : List (Coefficient × ℕ) :=
  [((.rat (1)), 65)]
def instruction98 : List (Coefficient × ℕ) :=
  [((.rat (1)), 66)]
def instruction99 : List (Coefficient × ℕ) :=
  [((.rat (1)), 67)]
def instruction100 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)) (.pow (.param 3) 2)), 68)]
def instruction101 : List (Coefficient × ℕ) :=
  [((.rat (1)), 69)]
def instruction102 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 70)]
def instruction103 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 71)]
def instruction104 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.param 0)), 72)]
def instruction105 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)), 73)]
def instruction106 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)) (.param 0)), 75)]
def instruction107 : List (Coefficient × ℕ) :=
  [((.rat (1)), 77)]
def instruction108 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 78)]
def instruction109 : List (Coefficient × ℕ) :=
  [((.rat (1)), 80), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))), 634)]
def instruction110 : List (Coefficient × ℕ) :=
  [((.rat (1)), 82), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 648)]
def instruction111 : List (Coefficient × ℕ) :=
  [((.rat (1)), 83), ((.neg (.mul (.rat (-1)) (.pow (.param 3) 2))), 625)]
def instruction112 : List (Coefficient × ℕ) :=
  [((.rat (1)), 84), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 641)]
def instruction113 : List (Coefficient × ℕ) :=
  [((.rat (1)), 85), ((.neg (.mul (.mul (.mul (.param 0) (.pow (.param 1) 2)) (.param 2)) (.pow (.invParam 3) 2))), 628)]
def instruction114 : List (Coefficient × ℕ) :=
  [((.rat (1)), 86), ((.neg (.mul (.rat (-1)) (.param 0))), 656)]
def instruction115 : List (Coefficient × ℕ) :=
  [((.mul (.param 0) (.pow (.param 1) 2)), 87), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.mul (.param 0) (.pow (.param 1) 2))), 619), ((.mul (.rat (-1)) (.mul (.param 0) (.pow (.param 1) 2))), 621)]
def instruction116 : List (Coefficient × ℕ) :=
  [((.rat (1)), 89), ((.neg (.mul (.rat (-1)) (.invParam 0))), 655)]
def instruction117 : List (Coefficient × ℕ) :=
  [((.rat (1)), 90), ((.neg (.mul (.param 2) (.pow (.param 3) 2))), 605)]
def instruction118 : List (Coefficient × ℕ) :=
  [((.rat (1)), 91), ((.neg (.param 2)), 634)]
def instruction119 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 3) 2) (.param 2)), 92)]
def instruction120 : List (Coefficient × ℕ) :=
  [((.rat (1)), 93), ((.neg (.mul (.param 2) (.pow (.invParam 3) 2))), 637)]
def instruction121 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.param 1) 2) (.pow (.param 3) 2)), 94), ((.mul (.rat (-1)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 654), ((.mul (.neg (.mul (.invParam 2) (.pow (.invParam 3) 2))) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 664)]
def instruction122 : List (Coefficient × ℕ) :=
  [((.rat (1)), 96)]
def instruction123 : List (Coefficient × ℕ) :=
  [((.rat (1)), 97), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 1) 2))), 620), ((.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))), 660)]
def instruction124 : List (Coefficient × ℕ) :=
  [((.rat (1)), 98)]
def instruction125 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)), 99)]
def instruction126 : List (Coefficient × ℕ) :=
  [((.param 0), 102), ((.mul (.rat (-1)) (.param 0)), 612), ((.mul (.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.invParam 0))) (.param 0)), 652)]
def instruction127 : List (Coefficient × ℕ) :=
  [((.mul (.param 0) (.pow (.param 1) 2)), 103), ((.mul (.rat (-1)) (.mul (.param 0) (.pow (.param 1) 2))), 614), ((.mul (.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.param 0) (.pow (.param 1) 2))), 650)]
def instruction128 : List (Coefficient × ℕ) :=
  [((.rat (1)), 106), ((.neg (.mul (.param 2) (.pow (.invParam 3) 2))), 606)]
def instruction129 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 1) 2) (.invParam 2)), 107)]
def instruction130 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.param 1) 2) (.param 2)), 108), ((.mul (.rat (-1)) (.mul (.pow (.param 1) 2) (.param 2))), 625)]
def instruction131 : List (Coefficient × ℕ) :=
  [((.rat (1)), 109), ((.neg (.mul (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.param 3) 2)) (.invParam 0))), 619)]
def instruction132 : List (Coefficient × ℕ) :=
  [((.rat (1)), 116)]
def instruction133 : List (Coefficient × ℕ) :=
  [((.rat (1)), 117), ((.neg (.mul (.mul (.param 0) (.param 2)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 629)]
def instruction134 : List (Coefficient × ℕ) :=
  [((.rat (1)), 118)]
def instruction135 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.invParam 0) (.pow (.invParam 3) 2)) (.param 2)), 119)]
def instruction136 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.pow (.invParam 1) 2) (.invParam 2)) (.mul (.param 0) (.pow (.param 3) 2))), 120)]
def instruction137 : List (Coefficient × ℕ) :=
  [((.rat (1)), 121), ((.neg (.mul (.mul (.pow (.param 1) 2) (.pow (.param 3) 2)) (.mul (.invParam 0) (.invParam 2)))), 674)]
def instruction138 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.invParam 2)) (.pow (.param 3) 2)), 122)]
def instruction139 : List (Coefficient × ℕ) :=
  [((.rat (1)), 124), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 645)]
def instruction140 : List (Coefficient × ℕ) :=
  [((.rat (1)), 125)]
def instruction141 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)), 126), ((.mul (.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.param 3) 2))) (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2))), 632)]
def instruction142 : List (Coefficient × ℕ) :=
  [((.rat (1)), 128), ((.neg (.mul (.pow (.param 3) 2) (.mul (.pow (.invParam 1) 2) (.invParam 2)))), 681)]
def instruction143 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 3) 2) (.param 2)), 130), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 1) 2))) (.mul (.pow (.invParam 3) 2) (.param 2))), 684)]
def instruction144 : List (Coefficient × ℕ) :=
  [((.rat (1)), 131)]
def instruction145 : List (Coefficient × ℕ) :=
  [((.rat (1)), 132), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 3) 2)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 604)]
def instruction146 : List (Coefficient × ℕ) :=
  [((.rat (1)), 134)]
def instruction147 : List (Coefficient × ℕ) :=
  [((.rat (1)), 135)]
def instruction148 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)) (.pow (.param 3) 2)), 136)]
def instruction149 : List (Coefficient × ℕ) :=
  [((.rat (1)), 137)]
def instruction150 : List (Coefficient × ℕ) :=
  [((.rat (1)), 138)]
def instruction151 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 139)]
def instruction152 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.param 0)), 140)]
def instruction153 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 141)]
def instruction154 : List (Coefficient × ℕ) :=
  [((.rat (1)), 142)]
def instruction155 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)) (.pow (.param 3) 2)), 143)]
def instruction156 : List (Coefficient × ℕ) :=
  [((.rat (1)), 144)]
def instruction157 : List (Coefficient × ℕ) :=
  [((.rat (1)), 145), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 638)]
def instruction158 : List (Coefficient × ℕ) :=
  [((.rat (1)), 146), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 3) 2))), 645)]
def instruction159 : List (Coefficient × ℕ) :=
  [((.rat (1)), 147)]
def instruction160 : List (Coefficient × ℕ) :=
  [((.rat (1)), 151)]
def instruction161 : List (Coefficient × ℕ) :=
  [((.rat (1)), 152)]
def instruction162 : List (Coefficient × ℕ) :=
  [((.rat (1)), 153)]
def instruction163 : List (Coefficient × ℕ) :=
  [((.rat (1)), 154), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 606)]
def instruction164 : List (Coefficient × ℕ) :=
  [((.rat (1)), 157), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2)) (.pow (.invParam 1) 2))), 611)]
def instruction165 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 3) 2) (.param 2)), 158), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 1) 2))) (.mul (.pow (.invParam 3) 2) (.param 2))), 678)]
def instruction166 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 3) 2)), 159)]
def instruction167 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)) (.param 0)), 160)]
def instruction168 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 161)]
def instruction169 : List (Coefficient × ℕ) :=
  [((.rat (1)), 162)]
def instruction170 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 163)]
def instruction171 : List (Coefficient × ℕ) :=
  [((.param 0), 164), ((.mul (.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))) (.param 0)), 667), ((.mul (.rat (-1)) (.param 0)), 714)]
def instruction172 : List (Coefficient × ℕ) :=
  [((.rat (1)), 165)]
def instruction173 : List (Coefficient × ℕ) :=
  [((.rat (1)), 166), ((.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))), 696)]
def instruction174 : List (Coefficient × ℕ) :=
  [((.rat (1)), 167)]
def instruction175 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 168)]
def instruction176 : List (Coefficient × ℕ) :=
  [((.rat (1)), 169)]
def instruction177 : List (Coefficient × ℕ) :=
  [((.rat (1)), 170)]
def instruction178 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 171), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 696)]
def instruction179 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)), 173)]
def instruction180 : List (Coefficient × ℕ) :=
  [((.rat (1)), 174)]
def instruction181 : List (Coefficient × ℕ) :=
  [((.rat (1)), 175)]
def instruction182 : List (Coefficient × ℕ) :=
  [((.rat (1)), 177)]
def instruction183 : List (Coefficient × ℕ) :=
  [((.rat (1)), 178)]
def instruction184 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0)), 182), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.param 0))), 709)]
def instruction185 : List (Coefficient × ℕ) :=
  [((.rat (1)), 183), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 616)]
def instruction186 : List (Coefficient × ℕ) :=
  [((.rat (1)), 186), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 639), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 672)]
def instruction187 : List (Coefficient × ℕ) :=
  [((.rat (1)), 187), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 610)]
def instruction188 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.pow (.invParam 1) 2)), 188)]
def instruction189 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.invParam 2)) (.pow (.param 1) 2)), 189), ((.mul (.rat (-1)) (.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.invParam 2)) (.pow (.param 1) 2))), 663), ((.mul (.rat (-1)) (.mul (.mul (.mul (.rat (-1)) (.invParam 0)) (.invParam 2)) (.pow (.param 1) 2))), 664)]
def instruction190 : List (Coefficient × ℕ) :=
  [((.rat (1)), 192), ((.neg (.mul (.param 0) (.mul (.invParam 2) (.pow (.invParam 3) 2)))), 552), ((.neg (.mul (.param 0) (.mul (.invParam 2) (.pow (.invParam 3) 2)))), 558)]
def instruction191 : List (Coefficient × ℕ) :=
  [((.rat (1)), 193), ((.neg (.mul (.param 0) (.mul (.invParam 2) (.pow (.invParam 3) 2)))), 552), ((.neg (.mul (.param 0) (.mul (.invParam 2) (.pow (.invParam 3) 2)))), 557)]
def instruction192 : List (Coefficient × ℕ) :=
  [((.rat (1)), 196), ((.neg (.mul (.param 0) (.invParam 2))), 552), ((.neg (.mul (.param 0) (.invParam 2))), 557)]
def instruction193 : List (Coefficient × ℕ) :=
  [((.rat (1)), 197), ((.neg (.mul (.param 0) (.invParam 2))), 552), ((.neg (.mul (.param 0) (.invParam 2))), 558)]
def instruction194 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.param 1) 2) (.pow (.param 3) 2)), 259), ((.mul (.rat (-1)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 579), ((.mul (.rat (-1)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 731), ((.mul (.neg (.invParam 0)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 733)]
def instruction195 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2)), 202), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 659), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 666), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 689), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 711), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 2)) (.pow (.invParam 3) 2))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 740)]
def instruction196 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.param 1) 2) (.pow (.param 3) 2)), 262), ((.mul (.neg (.invParam 0)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 565), ((.mul (.rat (-1)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 686), ((.mul (.rat (-1)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 721)]
def instruction197 : List (Coefficient × ℕ) :=
  [((.param 0), 264), ((.mul (.rat (-1)) (.param 0)), 569), ((.mul (.rat (-1)) (.param 0)), 729)]
def instruction198 : List (Coefficient × ℕ) :=
  [((.pow (.param 3) 2), 268), ((.mul (.rat (-1)) (.pow (.param 3) 2)), 554), ((.mul (.neg (.invParam 0)) (.pow (.param 3) 2)), 673), ((.mul (.rat (-1)) (.pow (.param 3) 2)), 692)]
def instruction199 : List (Coefficient × ℕ) :=
  [((.param 0), 275), ((.mul (.rat (-1)) (.param 0)), 584)]
def instruction200 : List (Coefficient × ℕ) :=
  [((.rat (1)), 283), ((.neg (.invParam 0)), 546)]
def instruction201 : List (Coefficient × ℕ) :=
  [((.rat (1)), 310), ((.rat (-1)), 546)]
def instruction202 : List (Coefficient × ℕ) :=
  [((.rat (1)), 316), ((.rat (-1)), 549), ((.neg (.invParam 0)), 741)]
def instruction203 : List (Coefficient × ℕ) :=
  [((.param 0), 317), ((.mul (.rat (-1)) (.param 0)), 563)]
def instruction204 : List (Coefficient × ℕ) :=
  [((.param 0), 319), ((.mul (.rat (-1)) (.param 0)), 564)]
def instruction205 : List (Coefficient × ℕ) :=
  [((.param 0), 320), ((.mul (.rat (-1)) (.param 0)), 641), ((.mul (.rat (-1)) (.param 0)), 738), ((.param 0), 741)]
def instruction206 : List (Coefficient × ℕ) :=
  [((.rat (1)), 331), ((.neg (.invParam 0)), 575)]
def instruction207 : List (Coefficient × ℕ) :=
  [((.rat (1)), 333), ((.neg (.invParam 0)), 586)]
def instruction208 : List (Coefficient × ℕ) :=
  [((.rat (1)), 334), ((.neg (.invParam 0)), 573)]
def instruction209 : List (Coefficient × ℕ) :=
  [((.rat (1)), 335), ((.neg (.invParam 0)), 594)]
def instruction210 : List (Coefficient × ℕ) :=
  [((.rat (1)), 337), ((.neg (.invParam 0)), 589)]
def instruction211 : List (Coefficient × ℕ) :=
  [((.rat (1)), 338), ((.neg (.invParam 0)), 591)]
def instruction212 : List (Coefficient × ℕ) :=
  [((.rat (1)), 339), ((.neg (.invParam 0)), 596)]
def instruction213 : List (Coefficient × ℕ) :=
  [((.rat (1)), 340), ((.neg (.invParam 0)), 597)]
def instruction214 : List (Coefficient × ℕ) :=
  [((.rat (1)), 341), ((.neg (.invParam 0)), 592)]
def instruction215 : List (Coefficient × ℕ) :=
  [((.rat (1)), 342), ((.neg (.invParam 0)), 567)]
def instruction216 : List (Coefficient × ℕ) :=
  [((.rat (1)), 344), ((.neg (.invParam 0)), 569)]
def instruction217 : List (Coefficient × ℕ) :=
  [((.rat (1)), 345), ((.neg (.invParam 0)), 560)]
def instruction218 : List (Coefficient × ℕ) :=
  [((.rat (1)), 347), ((.neg (.invParam 0)), 570)]
def instruction219 : List (Coefficient × ℕ) :=
  [((.param 0), 360), ((.mul (.rat (-1)) (.param 0)), 651), ((.mul (.rat (-1)) (.param 0)), 739), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.param 0)), 741)]
def instruction220 : List (Coefficient × ℕ) :=
  [((.param 0), 361), ((.mul (.rat (-1)) (.param 0)), 572)]
def instruction221 : List (Coefficient × ℕ) :=
  [((.param 0), 363), ((.mul (.rat (-1)) (.param 0)), 566)]
def instruction222 : List (Coefficient × ℕ) :=
  [((.rat (1)), 369), ((.rat (-1)), 562)]
def instruction223 : List (Coefficient × ℕ) :=
  [((.rat (1)), 394), ((.neg (.invParam 0)), 562)]
def instruction224 : List (Coefficient × ℕ) :=
  [((.param 0), 401), ((.mul (.rat (-1)) (.param 0)), 585)]
def instruction225 : List (Coefficient × ℕ) :=
  [((.param 0), 409), ((.mul (.rat (-1)) (.param 0)), 594), ((.mul (.rat (-1)) (.param 0)), 630)]
def instruction226 : List (Coefficient × ℕ) :=
  [((.rat (1)), 413), ((.rat (-1)), 598), ((.neg (.invParam 0)), 730)]
def instruction227 : List (Coefficient × ℕ) :=
  [((.rat (1)), 430), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 549), ((.neg (.pow (.invParam 1) 2)), 555), ((.rat (-1)), 561)]
def instruction228 : List (Coefficient × ℕ) :=
  [((.rat (1)), 418), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 584), ((.neg (.pow (.invParam 1) 2)), 643), ((.rat (-1)), 729), ((.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))), 773)]
def instruction229 : List (Coefficient × ℕ) :=
  [((.rat (1)), 431), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 564), ((.neg (.pow (.invParam 1) 2)), 662), ((.rat (-1)), 719), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 735)]
def instruction230 : List (Coefficient × ℕ) :=
  [((.mul (.rat ((-1/2))) (.mul (.param 0) (.pow (.param 1) 2))), 453), ((.mul (.rat (-1)) (.mul (.rat ((-1/2))) (.mul (.param 0) (.pow (.param 1) 2)))), 651), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.mul (.rat ((-1/2))) (.mul (.param 0) (.pow (.param 1) 2)))), 683), ((.mul (.rat (-1)) (.mul (.rat ((-1/2))) (.mul (.param 0) (.pow (.param 1) 2)))), 691), ((.mul (.neg (.add (.pow (.invParam 1) 2) (.rat (1)))) (.mul (.rat ((-1/2))) (.mul (.param 0) (.pow (.param 1) 2)))), 740), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.mul (.rat ((-1/2))) (.mul (.param 0) (.pow (.param 1) 2)))), 741), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat ((-1/2))) (.mul (.param 0) (.pow (.param 1) 2)))), 744)]
def instruction231 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.mul (.pow (.param 1) 2) (.param 2))), 272), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.mul (.pow (.param 1) 2) (.param 2)))), 608), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.mul (.pow (.param 1) 2) (.param 2)))), 678), ((.mul (.neg (.invParam 0)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.mul (.pow (.param 1) 2) (.param 2)))), 680), ((.mul (.neg (.mul (.mul (.rat (-1)) (.pow (.param 3) 2)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.invParam 2)))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.mul (.pow (.param 1) 2) (.param 2)))), 711), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.mul (.pow (.param 1) 2) (.param 2)))), 776)]
def instruction232 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 2)) (.mul (.param 0) (.pow (.param 3) 2))), 289), ((.mul (.neg (.invParam 0)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.mul (.param 0) (.pow (.param 3) 2)))), 659), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.mul (.param 0) (.pow (.param 3) 2)))), 676), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.mul (.param 0) (.pow (.param 3) 2)))), 689), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 2)) (.pow (.invParam 3) 2))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.mul (.param 0) (.pow (.param 3) 2)))), 741), ((.mul (.neg (.mul (.param 2) (.pow (.invParam 3) 2))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.mul (.param 0) (.pow (.param 3) 2)))), 776)]
def instruction233 : List (Coefficient × ℕ) :=
  [((.param 0), 302), ((.mul (.rat (-1)) (.param 0)), 740), ((.mul (.rat (-1)) (.param 0)), 776)]
def instruction234 : List (Coefficient × ℕ) :=
  [((.rat (1)), 211), ((.rat (-1)), 676), ((.rat (-1)), 681), ((.rat (-1)), 777), ((.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 778), ((.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 779)]
def instruction235 : List (Coefficient × ℕ) :=
  [((.rat (1)), 218), ((.rat (-1)), 549), ((.rat (-1)), 550), ((.rat (-1)), 555), ((.rat (-1)), 559), ((.rat (-1)), 561), ((.rat (-1)), 573), ((.rat (-1)), 623), ((.rat (-1)), 637), ((.rat (-1)), 667), ((.rat (-1)), 696), ((.neg (.param 0)), 735), ((.neg (.param 0)), 740), ((.rat (-1)), 741), ((.rat (-1)), 778), ((.rat (-1)), 779)]
def instruction236 : List (Coefficient × ℕ) :=
  [((.rat (1)), 228), ((.rat (-1)), 548), ((.neg (.invParam 0)), 549), ((.neg (.invParam 0)), 550), ((.rat (-1)), 552), ((.neg (.invParam 0)), 555), ((.neg (.invParam 0)), 556), ((.neg (.invParam 0)), 561), ((.neg (.invParam 0)), 573), ((.neg (.invParam 0)), 623), ((.rat (-1)), 629), ((.neg (.invParam 0)), 637), ((.rat (-1)), 645), ((.rat (-1)), 648), ((.neg (.invParam 0)), 667), ((.rat (-1)), 677), ((.rat (-1)), 683), ((.neg (.invParam 0)), 696), ((.rat (-2)), 735), ((.rat (-3)), 740), ((.neg (.invParam 0)), 741), ((.rat (-1)), 742), ((.rat (-1)), 744), ((.rat (-1)), 748), ((.rat (-1)), 754), ((.neg (.invParam 0)), 778), ((.neg (.invParam 0)), 779), ((.neg (.add (.mul (.rat (2)) (.invParam 0)) (.rat (-1)))), 781)]
def instruction237 : List (Coefficient × ℕ) :=
  [((.rat (1)), 424), ((.rat (-1)), 617), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 659), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 676), ((.rat (-1)), 777), ((.neg (.mul (.mul (.param 2) (.param 4)) (.mul (.mul (.invParam 0) (.invParam 1)) (.pow (.invParam 3) 2)))), 778), ((.neg (.pow (.invParam 1) 2)), 780)]
def instruction238 : List (Coefficient × ℕ) :=
  [((.rat (1)), 433), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 659), ((.rat (-1)), 679), ((.neg (.pow (.invParam 1) 2)), 689), ((.rat (-1)), 711), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 2)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 740), ((.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 741), ((.neg (.add (.mul (.param 2) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.mul (.mul (.rat (-1)) (.param 2)) (.pow (.invParam 3) 2)))), 776)]
def instruction239 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2)), 382), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 665), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 783), ((.mul (.neg (.invParam 0)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 784)]
def instruction240 : List (Coefficient × ℕ) :=
  [((.rat (1)), 400), ((.neg (.invParam 0)), 665), ((.rat (-1)), 674), ((.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 785)]
def instruction241 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 443), ((.rat (1)), 676), ((.mul (.neg (.pow (.invParam 1) 2)) (.rat (-1))), 681), ((.rat (1)), 763), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.rat (-1))), 778), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))) (.rat (-1))), 779), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.rat (-1))), 780), ((.rat (1)), 786)]
def instruction242 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2)), 217), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 560), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 586), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 665), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 674), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 679), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 715), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 2)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 740), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 784), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 2)) (.pow (.invParam 3) 2))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 785), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 3) 2))), 787)]
def instruction243 : List (Coefficient × ℕ) :=
  [((.rat (1)), 276), ((.rat (-1)), 679), ((.neg (.invParam 0)), 715), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 2)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 740), ((.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 788)]
def instruction244 : List (Coefficient × ℕ) :=
  [((.rat (1)), 238), ((.rat (-1)), 617), ((.rat (-1)), 618), ((.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 629), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 659), ((.neg (.mul (.mul (.rat (-1)) (.param 2)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 740), ((.rat (-1)), 753), ((.rat (-1)), 763), ((.rat (-1)), 783), ((.rat (1)), 784), ((.rat (-1)), 786), ((.rat (1)), 787), ((.rat (-1)), 789)]
def instruction245 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 478), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.rat (-1))), 572), ((.mul (.neg (.pow (.invParam 1) 2)) (.rat (-1))), 703), ((.rat (1)), 714), ((.mul (.neg (.invParam 0)) (.rat (-1))), 717), ((.mul (.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.rat (-1))), 735), ((.rat (1)), 764)]
def instruction246 : List (Coefficient × ℕ) :=
  [((.rat (1)), 479), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 550), ((.rat (-1)), 559), ((.neg (.pow (.invParam 1) 2)), 573)]
def instruction247 : List (Coefficient × ℕ) :=
  [((.rat (1)), 489), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 585), ((.rat (-1)), 630), ((.neg (.pow (.invParam 1) 2)), 649), ((.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))), 792)]
def instruction248 : List (Coefficient × ℕ) :=
  [((.rat (1)), 190), ((.neg (.mul (.mul (.invParam 0) (.invParam 2)) (.pow (.invParam 3) 2))), 556), ((.neg (.mul (.mul (.invParam 0) (.invParam 2)) (.pow (.invParam 3) 2))), 664), ((.rat (-1)), 768)]
def instruction249 : List (Coefficient × ℕ) :=
  [((.rat (1)), 191), ((.neg (.mul (.mul (.invParam 0) (.invParam 2)) (.pow (.invParam 3) 2))), 556), ((.neg (.mul (.mul (.invParam 0) (.invParam 2)) (.pow (.invParam 3) 2))), 663), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 735), ((.rat (-1)), 747)]
def instruction250 : List (Coefficient × ℕ) :=
  [((.rat (1)), 194), ((.neg (.mul (.invParam 0) (.invParam 2))), 556), ((.neg (.mul (.invParam 0) (.invParam 2))), 663), ((.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))), 735), ((.rat (-1)), 748), ((.neg (.invParam 0)), 776)]
def instruction251 : List (Coefficient × ℕ) :=
  [((.rat (1)), 195), ((.neg (.mul (.invParam 0) (.invParam 2))), 556), ((.neg (.mul (.invParam 0) (.invParam 2))), 664), ((.rat (-1)), 744), ((.neg (.mul (.rat (-1)) (.invParam 0))), 776)]
def instruction252 : List (Coefficient × ℕ) :=
  [((.mul (.invParam 2) (.mul (.param 0) (.pow (.param 1) 2))), 198), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.mul (.invParam 2) (.mul (.param 0) (.pow (.param 1) 2)))), 710), ((.mul (.rat (-1)) (.mul (.invParam 2) (.mul (.param 0) (.pow (.param 1) 2)))), 777), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.mul (.invParam 2) (.mul (.param 0) (.pow (.param 1) 2)))), 781), ((.mul (.rat (-1)) (.mul (.invParam 2) (.mul (.param 0) (.pow (.param 1) 2)))), 783)]
def instruction253 : List (Coefficient × ℕ) :=
  [((.mul (.invParam 2) (.pow (.param 1) 2)), 199), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.mul (.invParam 2) (.pow (.param 1) 2))), 690), ((.mul (.rat (-1)) (.mul (.invParam 2) (.pow (.param 1) 2))), 780), ((.mul (.rat (-1)) (.mul (.invParam 2) (.pow (.param 1) 2))), 790)]
def instruction254 : List (Coefficient × ℕ) :=
  [((.rat (1)), 200), ((.rat (-1)), 677), ((.neg (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.invParam 2)))), 689), ((.neg (.mul (.rat (-1)) (.invParam 0))), 741), ((.neg (.invParam 0)), 776), ((.neg (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.invParam 2)))), 787)]
def instruction255 : List (Coefficient × ℕ) :=
  [((.rat (1)), 201), ((.neg (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.invParam 2)))), 711), ((.neg (.mul (.rat (-1)) (.invParam 0))), 776), ((.rat (-1)), 782), ((.neg (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.invParam 2)))), 784)]
def instruction256 : List (Coefficient × ℕ) :=
  [((.mul (.param 0) (.pow (.param 3) 2)), 260), ((.mul (.neg (.invParam 0)) (.mul (.param 0) (.pow (.param 3) 2))), 686), ((.mul (.rat (-1)) (.mul (.param 0) (.pow (.param 3) 2))), 720), ((.mul (.rat (-1)) (.mul (.param 0) (.pow (.param 3) 2))), 733), ((.mul (.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.mul (.param 0) (.pow (.param 3) 2))), 740)]
def instruction257 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.param 1) 2) (.pow (.param 3) 2)), 261), ((.mul (.rat (-1)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 627), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 3) 2))) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 657), ((.mul (.rat (-1)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 685), ((.mul (.neg (.invParam 0)) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 717), ((.mul (.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.mul (.pow (.param 1) 2) (.pow (.param 3) 2))), 778)]
def instruction258 : List (Coefficient × ℕ) :=
  [((.rat (1)), 207), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.invParam 2)))), 560), ((.rat (-1)), 572), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.invParam 2)))), 663), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.invParam 2)))), 715), ((.rat (1)), 735), ((.rat (-1)), 769), ((.rat (-1)), 782), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.invParam 2)))), 784), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 788), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.invParam 0))), 802), ((.rat (-1)), 803)]
def instruction259 : List (Coefficient × ℕ) :=
  [((.rat (1)), 208), ((.rat (-1)), 564), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.invParam 2)))), 586), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.invParam 2)))), 664), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.invParam 2)))), 665), ((.rat (-1)), 677), ((.rat (-1)), 746), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 785), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.invParam 2)))), 787), ((.neg (.mul (.pow (.param 1) 2) (.invParam 0))), 802), ((.rat (1)), 803)]
def instruction260 : List (Coefficient × ℕ) :=
  [((.param 0), 266), ((.mul (.rat (-1)) (.param 0)), 619), ((.mul (.rat (-1)) (.param 0)), 675), ((.mul (.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.invParam 2)))) (.param 0)), 676), ((.mul (.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))) (.param 0)), 778), ((.mul (.neg (.pow (.invParam 3) 2)) (.param 0)), 802)]
def instruction261 : List (Coefficient × ℕ) :=
  [((.param 0), 269), ((.mul (.rat (-1)) (.param 0)), 611), ((.mul (.rat (-1)) (.param 0)), 660), ((.mul (.neg (.pow (.invParam 3) 2)) (.param 0)), 781), ((.mul (.neg (.invParam 0)) (.param 0)), 798)]
def instruction262 : List (Coefficient × ℕ) :=
  [((.param 0), 271), ((.mul (.rat (-1)) (.param 0)), 662), ((.mul (.rat (-1)) (.param 0)), 672), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 3) 2))) (.param 0)), 782), ((.mul (.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))) (.param 0)), 802), ((.mul (.neg (.pow (.invParam 3) 2)) (.param 0)), 803)]
def instruction263 : List (Coefficient × ℕ) :=
  [((.param 0), 273), ((.mul (.rat (-1)) (.param 0)), 712), ((.mul (.rat (-1)) (.param 0)), 716)]
def instruction264 : List (Coefficient × ℕ) :=
  [((.param 0), 277), ((.mul (.rat (-1)) (.param 0)), 688), ((.mul (.rat (-1)) (.param 0)), 710), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.param 0)), 779), ((.mul (.neg (.mul (.pow (.param 3) 2) (.pow (.invParam 1) 2))) (.param 0)), 798)]
def instruction265 : List (Coefficient × ℕ) :=
  [((.rat (1)), 278), ((.rat (-1)), 673), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 744), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 776)]
def instruction266 : List (Coefficient × ℕ) :=
  [((.rat (1)), 279)]
def instruction267 : List (Coefficient × ℕ) :=
  [((.rat (1)), 280), ((.rat (-1)), 699), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 751), ((.neg (.add (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2)))), 776), ((.neg (.invParam 0)), 798)]
def instruction268 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2))), 281), ((.mul (.neg (.invParam 0)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 638), ((.mul (.rat (-1)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 695), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 735), ((.mul (.rat (-1)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 802), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 803)]
def instruction269 : List (Coefficient × ℕ) :=
  [((.rat (1)), 212), ((.neg (.invParam 2)), 556), ((.neg (.invParam 2)), 659), ((.neg (.invParam 2)), 666), ((.neg (.invParam 2)), 689), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 3) 2))), 740), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 741), ((.neg (.pow (.invParam 3) 2)), 776), ((.rat (-1)), 778), ((.rat (-1)), 809), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))), 810), ((.rat (-1)), 814)]
def instruction270 : List (Coefficient × ℕ) :=
  [((.rat (1)), 282), ((.neg (.invParam 0)), 613), ((.neg (.pow (.invParam 1) 2)), 712)]
def instruction271 : List (Coefficient × ℕ) :=
  [((.rat (1)), 285), ((.neg (.invParam 0)), 602), ((.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))), 624), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 742)]
def instruction272 : List (Coefficient × ℕ) :=
  [((.rat (1)), 287), ((.neg (.invParam 0)), 642), ((.neg (.pow (.invParam 3) 2)), 748), ((.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))), 776), ((.rat (-1)), 808)]
def instruction273 : List (Coefficient × ℕ) :=
  [((.rat (1)), 288), ((.neg (.invParam 0)), 644), ((.rat (-1)), 680), ((.neg (.pow (.invParam 1) 2)), 754), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2)) (.mul (.pow (.invParam 1) 2) (.invParam 2)))), 777), ((.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))), 781)]
def instruction274 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2))), 291), ((.mul (.rat (-1)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 701), ((.mul (.neg (.invParam 0)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 788), ((.mul (.rat (-1)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 792)]
def instruction275 : List (Coefficient × ℕ) :=
  [((.rat (1)), 292)]
def instruction276 : List (Coefficient × ℕ) :=
  [((.rat (1)), 294)]
def instruction277 : List (Coefficient × ℕ) :=
  [((.param 0), 295), ((.mul (.rat (-1)) (.param 0)), 635), ((.mul (.rat (-1)) (.param 0)), 765), ((.mul (.neg (.add (.pow (.invParam 1) 2) (.param 0))) (.param 0)), 776)]
def instruction278 : List (Coefficient × ℕ) :=
  [((.rat (1)), 296), ((.rat (-1)), 745)]
def instruction279 : List (Coefficient × ℕ) :=
  [((.rat (1)), 297), ((.rat (-1)), 766)]
def instruction280 : List (Coefficient × ℕ) :=
  [((.rat (1)), 299)]
def instruction281 : List (Coefficient × ℕ) :=
  [((.rat (1)), 300)]
def instruction282 : List (Coefficient × ℕ) :=
  [((.param 0), 301), ((.mul (.rat (-1)) (.param 0)), 793)]
def instruction283 : List (Coefficient × ℕ) :=
  [((.rat (1)), 303)]
def instruction284 : List (Coefficient × ℕ) :=
  [((.rat (1)), 304), ((.rat (-1)), 798), ((.neg (.invParam 0)), 815)]
def instruction285 : List (Coefficient × ℕ) :=
  [((.rat (1)), 305)]
def instruction286 : List (Coefficient × ℕ) :=
  [((.rat (1)), 308), ((.rat (-1)), 613), ((.neg (.mul (.param 0) (.pow (.invParam 1) 2))), 712)]
def instruction287 : List (Coefficient × ℕ) :=
  [((.param 0), 309), ((.mul (.rat (-1)) (.param 0)), 614), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.param 0)), 673), ((.mul (.rat (-1)) (.param 0)), 737), ((.mul (.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.param 0)), 744), ((.mul (.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))) (.param 0)), 776)]
def instruction288 : List (Coefficient × ℕ) :=
  [((.param 0), 313), ((.mul (.rat (-1)) (.param 0)), 601)]
def instruction289 : List (Coefficient × ℕ) :=
  [((.rat (1)), 314), ((.rat (-1)), 602), ((.neg (.pow (.invParam 3) 2)), 624), ((.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 742)]
def instruction290 : List (Coefficient × ℕ) :=
  [((.rat (1)), 315), ((.rat (-1)), 625), ((.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 778)]
def instruction291 : List (Coefficient × ℕ) :=
  [((.rat (1)), 321), ((.rat (-1)), 642), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 748), ((.neg (.pow (.invParam 3) 2)), 776)]
def instruction292 : List (Coefficient × ℕ) :=
  [((.rat (1)), 322)]
def instruction293 : List (Coefficient × ℕ) :=
  [((.rat (1)), 323), ((.rat (-1)), 643)]
def instruction294 : List (Coefficient × ℕ) :=
  [((.rat (1)), 324), ((.rat (-1)), 644), ((.neg (.mul (.param 0) (.pow (.invParam 1) 2))), 754), ((.neg (.invParam 0)), 773), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 1) 2))), 781)]
def instruction295 : List (Coefficient × ℕ) :=
  [((.rat (1)), 325)]
def instruction296 : List (Coefficient × ℕ) :=
  [((.rat (1)), 326)]
def instruction297 : List (Coefficient × ℕ) :=
  [((.rat (1)), 327)]
def instruction298 : List (Coefficient × ℕ) :=
  [((.rat (1)), 329), ((.neg (.invParam 0)), 726)]
def instruction299 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2))), 330), ((.mul (.rat (-1)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 647), ((.mul (.neg (.invParam 0)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 702), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 740)]
def instruction300 : List (Coefficient × ℕ) :=
  [((.rat (1)), 332), ((.neg (.invParam 0)), 704)]
def instruction301 : List (Coefficient × ℕ) :=
  [((.rat (1)), 346), ((.neg (.invParam 0)), 660), ((.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))), 781)]
def instruction302 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2))), 348), ((.mul (.neg (.invParam 0)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 608), ((.mul (.rat (-1)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 646)]
def instruction303 : List (Coefficient × ℕ) :=
  [((.rat (1)), 355)]
def instruction304 : List (Coefficient × ℕ) :=
  [((.rat (1)), 356), ((.rat (-1)), 624), ((.neg (.mul (.param 0) (.pow (.invParam 1) 2))), 742), ((.neg (.invParam 0)), 792)]
def instruction305 : List (Coefficient × ℕ) :=
  [((.rat (1)), 358)]
def instruction306 : List (Coefficient × ℕ) :=
  [((.rat (1)), 359), ((.rat (-1)), 650), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 744), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 776)]
def instruction307 : List (Coefficient × ℕ) :=
  [((.param 0), 364), ((.mul (.rat (-1)) (.param 0)), 653), ((.mul (.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))) (.param 0)), 779), ((.mul (.rat (-1)) (.param 0)), 833)]
def instruction308 : List (Coefficient × ℕ) :=
  [((.rat (1)), 365), ((.rat (-1)), 603), ((.neg (.pow (.invParam 3) 2)), 644), ((.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 754), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 781)]
def instruction309 : List (Coefficient × ℕ) :=
  [((.param 0), 366), ((.mul (.rat (-1)) (.param 0)), 600), ((.mul (.neg (.pow (.invParam 3) 2)) (.param 0)), 740)]
def instruction310 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 307), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 612), ((.mul (.neg (.invParam 0)) (.mul (.rat (-1)) (.invParam 0))), 672), ((.mul (.neg (.pow (.invParam 3) 2)) (.mul (.rat (-1)) (.invParam 0))), 782), ((.mul (.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.invParam 0))), 802), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 855)]
def instruction311 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.pow (.param 0) 2)), 370), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.pow (.param 0) 2))), 668), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.mul (.rat (-1)) (.pow (.param 0) 2))), 698), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.pow (.param 0) 2))), 736), ((.mul (.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.mul (.rat (-1)) (.pow (.param 0) 2))), 748), ((.mul (.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))) (.mul (.rat (-1)) (.pow (.param 0) 2))), 776), ((.mul (.neg (.invParam 0)) (.mul (.rat (-1)) (.pow (.param 0) 2))), 836)]
def instruction312 : List (Coefficient × ℕ) :=
  [((.rat (1)), 371), ((.rat (-1)), 669), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 781)]
def instruction313 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 372), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 633), ((.mul (.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.invParam 0))), 802), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 834)]
def instruction314 : List (Coefficient × ℕ) :=
  [((.rat (1)), 374)]
def instruction315 : List (Coefficient × ℕ) :=
  [((.rat (1)), 378)]
def instruction316 : List (Coefficient × ℕ) :=
  [((.rat (1)), 379)]
def instruction317 : List (Coefficient × ℕ) :=
  [((.rat (1)), 380)]
def instruction318 : List (Coefficient × ℕ) :=
  [((.rat (1)), 381), ((.rat (-1)), 750)]
def instruction319 : List (Coefficient × ℕ) :=
  [((.param 0), 384), ((.mul (.rat (-1)) (.param 0)), 636), ((.mul (.rat (-1)) (.param 0)), 751), ((.mul (.neg (.add (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.param 0)))) (.param 0)), 776)]
def instruction320 : List (Coefficient × ℕ) :=
  [((.rat (1)), 385)]
def instruction321 : List (Coefficient × ℕ) :=
  [((.rat (1)), 386)]
def instruction322 : List (Coefficient × ℕ) :=
  [((.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2))), 387), ((.mul (.rat (-1)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 694), ((.mul (.rat (-1)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 773), ((.mul (.neg (.invParam 0)) (.mul (.pow (.invParam 3) 2) (.mul (.param 0) (.pow (.param 1) 2)))), 785)]
def instruction323 : List (Coefficient × ℕ) :=
  [((.rat (1)), 389), ((.neg (.invParam 0)), 624), ((.rat (-1)), 682), ((.neg (.pow (.invParam 1) 2)), 742), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2)) (.mul (.pow (.invParam 1) 2) (.invParam 2)))), 780)]
def instruction324 : List (Coefficient × ℕ) :=
  [((.rat (1)), 390), ((.neg (.invParam 0)), 650), ((.neg (.pow (.invParam 3) 2)), 744), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 776), ((.rat (-1)), 814)]
def instruction325 : List (Coefficient × ℕ) :=
  [((.rat (1)), 392), ((.neg (.invParam 0)), 603), ((.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))), 644), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 754), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 781)]
def instruction326 : List (Coefficient × ℕ) :=
  [((.rat (1)), 395), ((.neg (.invParam 0)), 669), ((.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 781)]
def instruction327 : List (Coefficient × ℕ) :=
  [((.rat (1)), 396), ((.neg (.invParam 0)), 670), ((.rat (-1)), 697), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 765), ((.neg (.add (.mul (.invParam 0) (.pow (.invParam 3) 2)) (.mul (.pow (.param 1) 2) (.pow (.invParam 3) 2)))), 776), ((.rat (-1)), 799)]
def instruction328 : List (Coefficient × ℕ) :=
  [((.rat (1)), 397)]
def instruction329 : List (Coefficient × ℕ) :=
  [((.rat (1)), 398), ((.rat (-1)), 698), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 748), ((.neg (.pow (.invParam 3) 2)), 776)]
def instruction330 : List (Coefficient × ℕ) :=
  [((.param 0), 399), ((.mul (.rat (-1)) (.param 0)), 657), ((.mul (.rat (-1)) (.param 0)), 690), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.param 0)), 778), ((.mul (.neg (.mul (.mul (.param 0) (.pow (.param 3) 2)) (.pow (.invParam 1) 2))) (.param 0)), 799)]
def instruction331 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 247), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 547), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 567), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 577), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 589), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 606), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 608), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 610), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 624), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 634), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 638), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 639), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 644), ((.mul (.neg (.mul (.pow (.param 3) 2) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 672), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 680), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 682), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 690), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 702), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 710), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 735), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 738), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 739), ((.mul (.neg (.mul (.mul (.rat (2)) (.param 0)) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 740), ((.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 741), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 742), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 751), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 754), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 765), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 773), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2)) (.mul (.pow (.invParam 1) 2) (.invParam 2)))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 777), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2)) (.mul (.pow (.invParam 1) 2) (.invParam 2)))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 780), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 781), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 782), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 785), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 788), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 792), ((.mul (.neg (.mul (.pow (.param 3) 2) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 798), ((.mul (.neg (.mul (.mul (.param 0) (.pow (.param 3) 2)) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 799), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 810), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 823), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 865), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.pow (.invParam 3) 2)) (.pow (.param 1) 2))), 876)]
def instruction332 : List (Coefficient × ℕ) :=
  [((.param 0), 403), ((.mul (.rat (-1)) (.param 0)), 620), ((.mul (.neg (.invParam 0)) (.param 0)), 660), ((.mul (.rat (-1)) (.param 0)), 726), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.param 0)), 781), ((.mul (.neg (.mul (.pow (.param 1) 2) (.pow (.invParam 3) 2))) (.param 0)), 876)]
def instruction333 : List (Coefficient × ℕ) :=
  [((.param 0), 405), ((.mul (.rat (-1)) (.param 0)), 704), ((.mul (.rat (-1)) (.param 0)), 799)]
def instruction334 : List (Coefficient × ℕ) :=
  [((.param 0), 408), ((.mul (.rat (-1)) (.param 0)), 607), ((.mul (.rat (-1)) (.param 0)), 706), ((.mul (.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))) (.param 0)), 779), ((.mul (.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.param 0)), 782), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))) (.param 0)), 802)]
def instruction335 : List (Coefficient × ℕ) :=
  [((.pow (.param 1) 2), 417), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.pow (.param 1) 2)), 672), ((.mul (.rat (-1)) (.pow (.param 1) 2)), 686), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))) (.pow (.param 1) 2)), 782), ((.mul (.neg (.mul (.mul (.param 1) (.param 4)) (.pow (.invParam 3) 2))) (.pow (.param 1) 2)), 802), ((.mul (.rat (-1)) (.pow (.param 1) 2)), 857), ((.mul (.neg (.mul (.rat (-1)) (.pow (.param 0) 2))) (.pow (.param 1) 2)), 859)]
def instruction336 : List (Coefficient × ℕ) :=
  [((.pow (.param 1) 2), 456), ((.mul (.rat (-1)) (.pow (.param 1) 2)), 652), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.pow (.param 1) 2)), 704), ((.mul (.rat (-1)) (.pow (.param 1) 2)), 723), ((.mul (.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.pow (.param 1) 2)), 779), ((.mul (.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.pow (.param 1) 2)), 782), ((.mul (.rat (-1)) (.pow (.param 1) 2)), 798), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))) (.pow (.param 1) 2)), 802)]
def instruction337 : List (Coefficient × ℕ) :=
  [((.pow (.param 1) 2), 463), ((.mul (.rat (-1)) (.pow (.param 1) 2)), 627), ((.mul (.rat (-1)) (.pow (.param 1) 2)), 640), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 3) 2))) (.pow (.param 1) 2)), 657), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.pow (.param 1) 2)), 660), ((.mul (.rat (-1)) (.pow (.param 1) 2)), 670), ((.mul (.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.pow (.param 1) 2)), 677), ((.mul (.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.pow (.param 1) 2)), 778), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))) (.pow (.param 1) 2)), 781), ((.mul (.neg (.param 0)) (.pow (.param 1) 2)), 799), ((.mul (.neg (.pow (.invParam 3) 2)) (.pow (.param 1) 2)), 802)]
def instruction338 : List (Coefficient × ℕ) :=
  [((.rat (1)), 480), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 600), ((.rat (-1)), 658), ((.neg (.pow (.invParam 1) 2)), 709), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))), 740), ((.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 776)]
def instruction339 : List (Coefficient × ℕ) :=
  [((.rat (1)), 495), ((.rat (-1)), 550), ((.rat (-1)), 616), ((.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))), 623), ((.neg (.pow (.invParam 3) 2)), 696), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 735), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 3) 2))), 803), ((.rat (-1)), 873), ((.rat (-1)), 883)]
def instruction340 : List (Coefficient × ℕ) :=
  [((.rat (1)), 429), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 601), ((.neg (.pow (.invParam 1) 2)), 626), ((.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 637), ((.rat (-1)), 718), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 740), ((.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 741), ((.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))), 776), ((.rat (-1)), 844), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 876), ((.rat (1)), 885)]
def instruction341 : List (Coefficient × ℕ) :=
  [((.rat (1)), 502), ((.neg (.pow (.invParam 3) 2)), 549), ((.rat (-1)), 670), ((.rat (-1)), 672), ((.rat (-1)), 726), ((.rat (-1)), 776), ((.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))), 781), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 782), ((.neg (.param 0)), 799), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))), 802), ((.neg (.mul (.pow (.param 1) 2) (.pow (.invParam 3) 2))), 876)]
def instruction342 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 504), ((.rat (1)), 703), ((.rat (1)), 712), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 735), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))) (.rat (-1))), 742), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 744), ((.rat (1)), 760), ((.mul (.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.rat (-1))), 776), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))) (.rat (-1))), 803), ((.rat (1)), 830)]
def instruction343 : List (Coefficient × ℕ) :=
  [((.rat (1)), 487), ((.rat (-1)), 724), ((.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 735), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 803), ((.rat (-1)), 815), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 879), ((.neg (.pow (.invParam 1) 2)), 888)]
def instruction344 : List (Coefficient × ℕ) :=
  [((.rat (1)), 362), ((.rat (-1)), 652), ((.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 782), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 802), ((.neg (.invParam 0)), 889)]
def instruction345 : List (Coefficient × ℕ) :=
  [((.rat (1)), 512), ((.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))), 677), ((.rat (-1)), 699), ((.rat (-1)), 707), ((.neg (.pow (.invParam 3) 2)), 735), ((.rat (-1)), 748), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 751), ((.neg (.add (.add (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.invParam 0)) (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2)))), 776), ((.neg (.mul (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.param 5)) (.mul (.invParam 0) (.invParam 3)))), 802), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 803), ((.rat (-1)), 866), ((.rat (1)), 882), ((.neg (.mul (.rat (-1)) (.invParam 0))), 888)]
def instruction346 : List (Coefficient × ℕ) :=
  [((.rat (1)), 349), ((.neg (.invParam 0)), 716), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 810), ((.rat (-1)), 891)]
def instruction347 : List (Coefficient × ℕ) :=
  [((.rat (1)), 528), ((.rat (-1)), 620), ((.neg (.invParam 0)), 660), ((.rat (-1)), 662), ((.rat (-1)), 740), ((.neg (.pow (.invParam 3) 2)), 748), ((.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))), 754), ((.rat (-1)), 757), ((.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))), 776), ((.neg (.add (.mul (.invParam 0) (.pow (.invParam 3) 2)) (.mul (.param 5) (.invParam 3)))), 781), ((.neg (.pow (.invParam 3) 2)), 803), ((.rat (1)), 887)]
def instruction348 : List (Coefficient × ℕ) :=
  [((.rat (1)), 416), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 611), ((.rat (-1)), 685), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.mul (.invParam 0) (.invParam 1)))), 798), ((.neg (.pow (.invParam 1) 2)), 822), ((.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))), 883), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 887), ((.rat (-1)), 893)]
def instruction349 : List (Coefficient × ℕ) :=
  [((.param 0), 318), ((.mul (.rat (-1)) (.param 0)), 640), ((.mul (.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.param 0)), 677), ((.mul (.neg (.pow (.invParam 3) 2)) (.param 0)), 802), ((.mul (.rat (-1)) (.param 0)), 894)]
def instruction350 : List (Coefficient × ℕ) :=
  [((.rat (1)), 203), ((.neg (.mul (.invParam 0) (.invParam 2))), 556), ((.rat (-1)), 645), ((.rat (-1)), 649), ((.neg (.mul (.invParam 0) (.invParam 2))), 659), ((.neg (.mul (.invParam 0) (.invParam 2))), 689), ((.neg (.mul (.invParam 0) (.invParam 2))), 711), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 741), ((.rat (-1)), 870)]
def instruction351 : List (Coefficient × ℕ) :=
  [((.rat (1)), 204), ((.neg (.mul (.invParam 0) (.invParam 2))), 556), ((.rat (-1)), 643), ((.rat (-1)), 648), ((.neg (.mul (.invParam 0) (.invParam 2))), 666), ((.neg (.mul (.invParam 0) (.invParam 2))), 689), ((.neg (.mul (.invParam 0) (.invParam 2))), 711), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 740), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 741), ((.neg (.invParam 0)), 781), ((.rat (-1)), 818)]
def instruction352 : List (Coefficient × ℕ) :=
  [((.rat (1)), 205), ((.neg (.mul (.param 0) (.invParam 2))), 552), ((.rat (-1)), 650), ((.rat (-1)), 667), ((.neg (.mul (.param 0) (.invParam 2))), 676), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 744), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 776), ((.neg (.mul (.param 0) (.invParam 2))), 777), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 778), ((.neg (.mul (.param 0) (.invParam 2))), 780), ((.neg (.param 0)), 803), ((.rat (-1)), 848)]
def instruction353 : List (Coefficient × ℕ) :=
  [((.rat (1)), 206), ((.neg (.mul (.param 0) (.invParam 2))), 552), ((.rat (-1)), 642), ((.neg (.mul (.param 0) (.invParam 2))), 681), ((.rat (-1)), 696), ((.neg (.param 0)), 735), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 748), ((.neg (.pow (.invParam 3) 2)), 776), ((.neg (.mul (.param 0) (.invParam 2))), 777), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 779), ((.neg (.mul (.param 0) (.invParam 2))), 780), ((.neg (.mul (.rat (-1)) (.param 0))), 803), ((.rat (-1)), 845)]
def instruction354 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2)), 209), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 546), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 558), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 750), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 753), ((.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2)), 784), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 786), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 790), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 868)]
def instruction355 : List (Coefficient × ℕ) :=
  [((.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2)), 210), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 557), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 562), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 763), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 766), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 781), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 783), ((.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2)), 787), ((.mul (.rat (-1)) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 789), ((.mul (.neg (.mul (.param 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.mul (.rat (-1)) (.invParam 2)) (.pow (.param 1) 2))), 820)]
def instruction356 : List (Coefficient × ℕ) :=
  [((.rat (1)), 214), ((.rat (-1)), 623), ((.neg (.mul (.pow (.param 1) 2) (.invParam 2))), 664), ((.neg (.mul (.pow (.param 1) 2) (.invParam 2))), 665), ((.neg (.mul (.pow (.param 1) 2) (.invParam 2))), 679), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 3) 2))), 740), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))), 785), ((.neg (.mul (.pow (.param 1) 2) (.invParam 2))), 787), ((.neg (.mul (.rat (-1)) (.param 0))), 803), ((.rat (-1)), 879), ((.rat (-1)), 901)]
def instruction357 : List (Coefficient × ℕ) :=
  [((.rat (1)), 215), ((.rat (-1)), 637), ((.neg (.mul (.pow (.param 1) 2) (.invParam 2))), 663), ((.neg (.mul (.pow (.param 1) 2) (.invParam 2))), 674), ((.neg (.mul (.pow (.param 1) 2) (.invParam 2))), 715), ((.neg (.mul (.rat (-1)) (.param 0))), 735), ((.neg (.param 0)), 740), ((.neg (.mul (.pow (.param 1) 2) (.invParam 2))), 784), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))), 788), ((.neg (.param 0)), 803), ((.rat (-1)), 807), ((.rat (-1)), 900)]
def instruction358 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 227), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 548), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 551), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 552), ((.rat (1)), 589), ((.rat (1)), 606), ((.rat (1)), 608), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 629), ((.rat (1)), 634), ((.rat (1)), 644), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 645), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 648), ((.rat (1)), 664), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 677), ((.rat (1)), 682), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 683), ((.rat (1)), 690), ((.rat (1)), 739), ((.mul (.neg (.mul (.mul (.rat (2)) (.param 0)) (.pow (.invParam 1) 2))) (.rat (-1))), 740), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 742), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 744), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 748), ((.rat (1)), 751), ((.mul (.neg (.mul (.mul (.rat (2)) (.param 0)) (.pow (.invParam 1) 2))) (.rat (-1))), 754), ((.mul (.neg (.add (.add (.mul (.rat (-1)) (.pow (.invParam 1) 2)) (.rat (-1))) (.mul (.rat (-1)) (.param 0)))) (.rat (-1))), 776), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 3) 2)) (.mul (.pow (.invParam 1) 2) (.invParam 2)))) (.rat (-1))), 780), ((.mul (.neg (.add (.pow (.invParam 1) 2) (.mul (.mul (.rat (-2)) (.param 0)) (.pow (.invParam 1) 2)))) (.rat (-1))), 781), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 782), ((.rat (1)), 785), ((.rat (1)), 792), ((.mul (.neg (.mul (.mul (.param 0) (.pow (.param 3) 2)) (.pow (.invParam 1) 2))) (.rat (-1))), 799), ((.rat (1)), 802), ((.mul (.neg (.add (.mul (.mul (.rat (2)) (.param 0)) (.pow (.invParam 1) 2)) (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 2)) (.pow (.invParam 1) 2)))) (.rat (-1))), 803), ((.rat (1)), 810), ((.rat (1)), 823), ((.mul (.neg (.mul (.mul (.rat (-1)) (.pow (.param 3) 2)) (.pow (.invParam 1) 2))) (.rat (-1))), 877), ((.mul (.neg (.mul (.pow (.param 3) 2) (.pow (.invParam 1) 2))) (.rat (-1))), 881)]
def instruction359 : List (Coefficient × ℕ) :=
  [((.rat (1)), 222), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 550), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 555), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 556), ((.rat (-1)), 557), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 559), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 561), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 573), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 623), ((.rat (-1)), 628), ((.rat (-1)), 636), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 637), ((.rat (-1)), 647), ((.rat (-1)), 651), ((.rat (-1)), 657), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 667), ((.rat (-1)), 678), ((.rat (-1)), 687), ((.rat (-1)), 695), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 696), ((.rat (-1)), 701), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 3) 2)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.invParam 2)))), 711), ((.neg (.pow (.invParam 1) 2)), 735), ((.neg (.pow (.invParam 1) 2)), 740), ((.neg (.mul (.rat (2)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 741), ((.rat (-1)), 761), ((.neg (.mul (.rat (2)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 778), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 779), ((.neg (.mul (.rat (2)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 781), ((.rat (-1)), 796), ((.rat (-1)), 801), ((.neg (.mul (.pow (.param 1) 2) (.invParam 0))), 802), ((.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))), 803), ((.neg (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 814), ((.neg (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 820), ((.rat (1)), 823), ((.rat (-1)), 840), ((.neg (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 845), ((.rat (-1)), 869), ((.neg (.mul (.pow (.param 3) 2) (.pow (.invParam 1) 2))), 877), ((.neg (.add (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.mul (.mul (.rat (-1)) (.pow (.param 3) 2)) (.pow (.invParam 1) 2)))), 881), ((.rat (-1)), 904)]
def instruction360 : List (Coefficient × ℕ) :=
  [((.param 0), 270), ((.mul (.rat (-1)) (.param 0)), 621), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))) (.param 0)), 661), ((.mul (.rat (-1)) (.param 0)), 743), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))) (.param 0)), 773), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.param 0)), 802)]
def instruction361 : List (Coefficient × ℕ) :=
  [((.rat (1)), 274), ((.rat (-1)), 719), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 735), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 803)]
def instruction362 : List (Coefficient × ℕ) :=
  [((.rat (1)), 284), ((.neg (.invParam 0)), 605), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 735), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 803)]
def instruction363 : List (Coefficient × ℕ) :=
  [((.rat (1)), 336), ((.neg (.invParam 0)), 708), ((.neg (.pow (.invParam 3) 2)), 735), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 803)]
def instruction364 : List (Coefficient × ℕ) :=
  [((.rat (1)), 343), ((.neg (.invParam 0)), 655), ((.neg (.pow (.invParam 3) 2)), 803)]
def instruction365 : List (Coefficient × ℕ) :=
  [((.rat (1)), 352), ((.neg (.invParam 0)), 813), ((.rat (-1)), 845)]
def instruction366 : List (Coefficient × ℕ) :=
  [((.param 0), 377), ((.mul (.rat (-1)) (.param 0)), 774), ((.param 0), 837), ((.mul (.neg (.invParam 0)) (.param 0)), 882)]
def instruction367 : List (Coefficient × ℕ) :=
  [((.rat (1)), 393), ((.neg (.invParam 0)), 654), ((.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 667), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 803)]
def instruction368 : List (Coefficient × ℕ) :=
  [((.rat (1)), 402), ((.rat (-1)), 714), ((.neg (.invParam 0)), 717), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 803)]
def instruction369 : List (Coefficient × ℕ) :=
  [((.param 0), 404), ((.mul (.rat (-1)) (.param 0)), 727), ((.mul (.rat (-1)) (.param 0)), 771), ((.mul (.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.param 0)), 782), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))) (.param 0)), 792), ((.mul (.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.param 0)), 802), ((.mul (.neg (.pow (.invParam 3) 2)) (.param 0)), 904)]
def instruction370 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.param 0)), 414), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 580), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.mul (.rat (-1)) (.param 0))), 615), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.param 0))), 712), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.param 0))), 735), ((.mul (.neg (.mul (.param 4) (.mul (.invParam 1) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.param 0))), 803), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 835), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 858)]
def instruction371 : List (Coefficient × ℕ) :=
  [((.rat (1)), 423), ((.rat (-1)), 565), ((.rat (-1)), 750), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 808), ((.neg (.mul (.rat (-1)) (.param 0))), 900), ((.neg (.pow (.invParam 1) 2)), 903)]
def instruction372 : List (Coefficient × ℕ) :=
  [((.rat (1)), 376), ((.rat (-1)), 857), ((.neg (.mul (.rat (-1)) (.pow (.param 0) 2))), 859), ((.rat (1)), 900), ((.neg (.invParam 0)), 917)]
def instruction373 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.invParam 0)), 426), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 743), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.mul (.rat (-1)) (.invParam 0))), 745), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))) (.mul (.rat (-1)) (.invParam 0))), 773), ((.mul (.neg (.mul (.mul (.param 0) (.param 4)) (.invParam 1))) (.mul (.rat (-1)) (.invParam 0))), 868), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 882), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.invParam 0))), 899), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.invParam 0))), 912)]
def instruction374 : List (Coefficient × ℕ) :=
  [((.rat (1)), 427), ((.neg (.pow (.invParam 1) 2)), 704), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 798), ((.rat (-1)), 806), ((.rat (-1)), 902), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))), 904)]
def instruction375 : List (Coefficient × ℕ) :=
  [((.rat (1)), 428), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 546), ((.neg (.pow (.invParam 1) 2)), 591), ((.rat (-1)), 713), ((.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 735), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 803), ((.rat (-1)), 899)]
def instruction376 : List (Coefficient × ℕ) :=
  [((.rat (1)), 432), ((.rat (-1)), 568), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 642), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))), 748), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))), 776), ((.neg (.pow (.invParam 1) 2)), 868)]
def instruction377 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.param 0)), 444), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.param 0))), 661), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 791), ((.mul (.neg (.pow (.invParam 3) 2)) (.mul (.rat (-1)) (.param 0))), 802), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 809), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))) (.mul (.rat (-1)) (.param 0))), 810), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 896), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.mul (.rat (-1)) (.param 0))), 901), ((.mul (.neg (.add (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.mul (.mul (.mul (.rat (-1)) (.param 1)) (.param 4)) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.param 0))), 904), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 914)]
def instruction378 : List (Coefficient × ℕ) :=
  [((.rat (1)), 445), ((.rat (-1)), 575), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 750), ((.neg (.pow (.invParam 1) 2)), 808), ((.rat (-1)), 845), ((.neg (.mul (.mul (.param 0) (.param 4)) (.invParam 1))), 900)]
def instruction379 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.param 0)), 450), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 588), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 649), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.param 0))), 760), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.mul (.rat (-1)) (.param 0))), 769), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 826), ((.mul (.neg (.mul (.param 4) (.invParam 1))) (.mul (.rat (-1)) (.param 0))), 879), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))) (.mul (.rat (-1)) (.param 0))), 888), ((.mul (.rat (-1)) (.param 0)), 889), ((.mul (.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.param 0))), 904)]
def instruction380 : List (Coefficient × ℕ) :=
  [((.rat (1)), 451), ((.rat (-1)), 706), ((.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 782), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 802), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 873), ((.rat (-1)), 881)]
def instruction381 : List (Coefficient × ℕ) :=
  [((.rat (1)), 452), ((.rat (-1)), 594), ((.rat (-1)), 650), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 744), ((.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))), 776), ((.neg (.pow (.invParam 1) 2)), 815), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 820), ((.neg (.mul (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 1)) (.param 4)) (.pow (.invParam 3) 2))), 904)]
def instruction382 : List (Coefficient × ℕ) :=
  [((.rat (1)), 454), ((.rat (-1)), 708), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 726), ((.rat (-1)), 734), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 735), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 3) 2))), 803), ((.neg (.pow (.invParam 1) 2)), 807), ((.neg (.pow (.invParam 1) 2)), 834), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 1) 2))), 859), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 1)) (.param 4)) (.pow (.invParam 3) 2))), 876), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 900)]
def instruction383 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.param 0)), 455), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 572), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.mul (.rat (-1)) (.param 0))), 703), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 722), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.param 0))), 735), ((.mul (.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.mul (.rat (-1)) (.param 0))), 754), ((.mul (.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.param 0))), 781), ((.mul (.neg (.mul (.param 4) (.mul (.invParam 1) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.param 0))), 803), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 829), ((.mul (.rat (-1)) (.param 0)), 853), ((.mul (.neg (.pow (.param 0) 2)) (.mul (.rat (-1)) (.param 0))), 856), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.param 0))), 861), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))) (.mul (.rat (-1)) (.param 0))), 877), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.param 0))), 881), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 901), ((.mul (.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.mul (.rat (-1)) (.param 0))), 902), ((.mul (.neg (.add (.mul (.invParam 0) (.pow (.invParam 3) 2)) (.mul (.pow (.param 1) 2) (.pow (.invParam 3) 2)))) (.mul (.rat (-1)) (.param 0))), 904)]
def instruction384 : List (Coefficient × ℕ) :=
  [((.rat (1)), 464), ((.rat (-1)), 655), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 716), ((.rat (-1)), 728), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 803), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 1)) (.param 4)) (.pow (.invParam 3) 2))), 810), ((.neg (.pow (.invParam 1) 2)), 855), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 1) 2))), 856), ((.neg (.pow (.invParam 1) 2)), 879), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 901), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 904)]
def instruction385 : List (Coefficient × ℕ) :=
  [((.rat (1)), 475), ((.rat (-1)), 762), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 805), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 807), ((.rat (-1)), 818), ((.neg (.pow (.invParam 1) 2)), 893)]
def instruction386 : List (Coefficient × ℕ) :=
  [((.rat (1)), 482), ((.neg (.pow (.invParam 1) 2)), 660), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 670), ((.neg (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))), 781), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 4)) (.invParam 1))), 799), ((.rat (-1)), 880), ((.rat (-1)), 903)]
def instruction387 : List (Coefficient × ℕ) :=
  [((.rat (1)), 488), ((.rat (-1)), 604), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 698), ((.neg (.mul (.param 0) (.pow (.invParam 3) 2))), 740), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))), 748), ((.rat (-1)), 767), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))), 776), ((.neg (.pow (.invParam 1) 2)), 845)]
def instruction388 : List (Coefficient × ℕ) :=
  [((.rat (1)), 491), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 583), ((.rat (-1)), 593), ((.neg (.pow (.invParam 1) 2)), 878)]
def instruction389 : List (Coefficient × ℕ) :=
  [((.rat (1)), 493), ((.rat (-1)), 686), ((.rat (-1)), 734), ((.neg (.pow (.invParam 3) 2)), 773), ((.rat (-1)), 788), ((.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))), 802), ((.neg (.pow (.invParam 1) 2)), 807), ((.rat (-1)), 932)]
def instruction390 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 496), ((.rat (1)), 603), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 644), ((.rat (1)), 717), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 738), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 3) 2))) (.rat (-1))), 741), ((.rat (1)), 752), ((.mul (.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.rat (-1))), 754), ((.rat (1)), 765), ((.rat (-1)), 775), ((.mul (.neg (.add (.add (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)) (.param 0))) (.rat (-1))), 776), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 0)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.rat (-1))), 781), ((.mul (.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))) (.rat (-1))), 803), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))) (.rat (-1))), 810), ((.rat (1)), 874), ((.rat (1)), 897), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 919), ((.rat (-1)), 931)]
def instruction391 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 500), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 547), ((.rat (1)), 610), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))) (.rat (-1))), 644), ((.rat (1)), 669), ((.mul (.neg (.mul (.param 0) (.pow (.invParam 1) 2))) (.rat (-1))), 740), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 5)) (.mul (.pow (.invParam 1) 2) (.invParam 3)))) (.rat (-1))), 754), ((.rat (1)), 755), ((.mul (.neg (.add (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)) (.mul (.mul (.param 0) (.param 5)) (.mul (.pow (.invParam 1) 2) (.invParam 3))))) (.rat (-1))), 781), ((.rat (1)), 889), ((.rat (1)), 914), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 923)]
def instruction392 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 435), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.rat (-1))), 804), ((.rat (1)), 812), ((.mul (.neg (.pow (.invParam 1) 2)) (.rat (-1))), 830), ((.rat (1)), 870), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.rat (-1))), 879), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 927), ((.rat (1)), 937)]
def instruction393 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 501), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 551), ((.rat (1)), 611), ((.rat (1)), 633), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))) (.rat (-1))), 645), ((.rat (1)), 683), ((.mul (.neg (.invParam 0)) (.rat (-1))), 798), ((.mul (.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.rat (-1))), 802), ((.rat (1)), 827), ((.rat (-1)), 881), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 903), ((.rat (1)), 909)]
def instruction394 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 219), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 549), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 550), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 555), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 556), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 559), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 561), ((.rat (1)), 564), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 573), ((.rat (1)), 584), ((.rat (1)), 600), ((.rat (1)), 620), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 623), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 637), ((.mul (.neg (.invParam 0)) (.rat (-1))), 660), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 667), ((.rat (1)), 692), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 696), ((.rat (1)), 707), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 735), ((.mul (.neg (.mul (.rat (2)) (.pow (.invParam 3) 2))) (.rat (-1))), 740), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 741), ((.rat (1)), 769), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 776), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 779), ((.rat (1)), 780), ((.mul (.neg (.mul (.rat (2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.rat (-1))), 781), ((.rat (1)), 818), ((.rat (1)), 822), ((.rat (1)), 830), ((.rat (1)), 843), ((.rat (1)), 847), ((.rat (-1)), 848), ((.rat (1)), 861), ((.rat (1)), 867), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 873), ((.rat (-1)), 877), ((.rat (-1)), 879), ((.rat (1)), 881), ((.rat (-1)), 883), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 887), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 892), ((.rat (-1)), 899), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 902), ((.mul (.neg (.add (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.mul (.mul (.param 0) (.pow (.param 1) 2)) (.pow (.invParam 3) 2)))) (.rat (-1))), 904), ((.rat (1)), 909), ((.rat (-1)), 939)]
def instruction395 : List (Coefficient × ℕ) :=
  [((.rat (1)), 534), ((.rat (-1)), 548), ((.rat (-1)), 601), ((.neg (.pow (.invParam 3) 2)), 742), ((.rat (-1)), 811), ((.rat (-1)), 847), ((.neg (.mul (.rat (-1)) (.invParam 0))), 881), ((.rat (1)), 940)]
def instruction396 : List (Coefficient × ℕ) :=
  [((.rat (1)), 425), ((.rat (-1)), 609), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 745), ((.neg (.pow (.invParam 1) 2)), 768), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 821), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 859), ((.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))), 868), ((.neg (.mul (.param 4) (.mul (.invParam 0) (.invParam 1)))), 885), ((.neg (.mul (.param 4) (.invParam 1))), 898), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 0) 3) (.pow (.invParam 1) 2)))), 900), ((.neg (.mul (.mul (.mul (.param 0) (.param 1)) (.param 4)) (.pow (.invParam 3) 2))), 904), ((.rat (-1)), 941)]
def instruction397 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 437), ((.rat (1)), 757), ((.rat (1)), 816), ((.mul (.neg (.pow (.invParam 1) 2)) (.rat (-1))), 844), ((.rat (1)), 871), ((.mul (.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.rat (-1))), 876), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))) (.rat (-1))), 885), ((.rat (-1)), 887), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.rat (-1))), 909), ((.rat (-1)), 915), ((.mul (.neg (.mul (.param 4) (.invParam 1))) (.rat (-1))), 939)]
def instruction398 : List (Coefficient × ℕ) :=
  [((.rat (1)), 353), ((.rat (-1)), 828), ((.neg (.param 0)), 852), ((.rat (1)), 883), ((.neg (.mul (.rat (-1)) (.param 0))), 927), ((.neg (.invParam 0)), 943)]
def instruction399 : List (Coefficient × ℕ) :=
  [((.rat (1)), 438), ((.rat (-1)), 807), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 887), ((.rat (-1)), 935), ((.neg (.pow (.invParam 1) 2)), 939)]
def instruction400 : List (Coefficient × ℕ) :=
  [((.mul (.rat (-1)) (.param 0)), 448), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 587), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.param 0))), 804), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 825), ((.mul (.rat (-1)) (.mul (.rat (-1)) (.param 0))), 849), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.mul (.rat (-1)) (.param 0))), 870), ((.mul (.neg (.pow (.invParam 1) 2)) (.mul (.rat (-1)) (.param 0))), 879), ((.mul (.neg (.param 0)) (.mul (.rat (-1)) (.param 0))), 901), ((.mul (.neg (.mul (.mul (.param 0) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))) (.mul (.rat (-1)) (.param 0))), 904), ((.mul (.rat (-1)) (.param 0)), 929), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.mul (.rat (-1)) (.param 0))), 940)]
def instruction401 : List (Coefficient × ℕ) :=
  [((.rat (1)), 503), ((.rat (-1)), 702), ((.neg (.mul (.param 0) (.pow (.invParam 1) 2))), 740), ((.rat (-1)), 806), ((.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))), 823), ((.rat (-1)), 853), ((.neg (.mul (.rat (-1)) (.pow (.param 0) 2))), 856), ((.neg (.mul (.mul (.param 3) (.param 5)) (.pow (.invParam 1) 2))), 877), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 3)) (.param 5)) (.pow (.invParam 1) 2))), 881), ((.rat (1)), 901), ((.neg (.add (.pow (.invParam 3) 2) (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2)))), 904), ((.rat (-1)), 930)]
def instruction402 : List (Coefficient × ℕ) :=
  [((.rat (1)), 505), ((.rat (-1)), 575), ((.rat (-1)), 713), ((.neg (.mul (.param 0) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 735), ((.neg (.pow (.invParam 3) 2)), 751), ((.neg (.add (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2))) (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 3) 2)))), 776), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.mul (.pow (.invParam 1) 2) (.pow (.invParam 3) 2)))), 803), ((.rat (-1)), 823), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 3) 2)) (.pow (.invParam 1) 2))), 877), ((.neg (.mul (.pow (.param 3) 2) (.pow (.invParam 1) 2))), 881), ((.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))), 904), ((.rat (-1)), 919)]
def instruction403 : List (Coefficient × ℕ) :=
  [((.rat (1)), 506), ((.rat (-1)), 561), ((.neg (.pow (.invParam 3) 2)), 573), ((.rat (-1)), 704), ((.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))), 779), ((.rat (-1)), 855), ((.neg (.mul (.rat (-1)) (.param 0))), 856), ((.rat (-1)), 877), ((.rat (1)), 881), ((.neg (.mul (.rat (-1)) (.invParam 0))), 901), ((.neg (.mul (.mul (.rat (-1)) (.pow (.param 1) 2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 904)]
def instruction404 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 220), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 549), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 550), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 555), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 556), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 559), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 561), ((.rat (1)), 572), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 573), ((.rat (1)), 585), ((.rat (1)), 601), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 623), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 637), ((.rat (1)), 656), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 667), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 696), ((.rat (1)), 705), ((.rat (1)), 712), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 735), ((.mul (.neg (.pow (.invParam 3) 2)) (.rat (-1))), 740), ((.mul (.neg (.mul (.rat (2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.rat (-1))), 741), ((.rat (1)), 746), ((.mul (.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.rat (-1))), 776), ((.rat (1)), 777), ((.mul (.neg (.mul (.invParam 0) (.pow (.invParam 3) 2))) (.rat (-1))), 778), ((.mul (.neg (.mul (.rat (2)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.rat (-1))), 781), ((.rat (-1)), 807), ((.rat (1)), 821), ((.rat (1)), 827), ((.rat (1)), 846), ((.rat (1)), 866), ((.rat (1)), 870), ((.rat (-1)), 881), ((.rat (-1)), 882), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 885), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 888), ((.rat (1)), 893), ((.rat (-1)), 898), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.rat (-1))), 903), ((.mul (.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.param 1) 2)) (.pow (.invParam 3) 2))) (.rat (-1))), 904), ((.rat (1)), 910), ((.rat (1)), 911), ((.rat (-1)), 949)]
def instruction405 : List (Coefficient × ℕ) :=
  [((.rat (1)), 420), ((.rat (-1)), 675), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 1) 2) (.invParam 2)))), 676), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 699), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 1)) (.param 4)) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 751), ((.neg (.add (.mul (.param 4) (.mul (.mul (.invParam 0) (.invParam 1)) (.pow (.invParam 3) 2))) (.mul (.mul (.param 1) (.param 4)) (.pow (.invParam 3) 2)))), 776), ((.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))), 778), ((.neg (.pow (.invParam 1) 2)), 846), ((.rat (-1)), 861), ((.rat (1)), 877), ((.rat (-1)), 881), ((.neg (.mul (.rat (-1)) (.invParam 0))), 902), ((.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))), 904), ((.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))), 950)]
def instruction406 : List (Coefficient × ℕ) :=
  [((.rat (-1)), 439), ((.rat (1)), 759), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))) (.rat (-1))), 760), ((.rat (1)), 769), ((.rat (-1)), 879), ((.mul (.neg (.mul (.param 4) (.invParam 1))) (.rat (-1))), 888), ((.rat (1)), 908), ((.mul (.neg (.pow (.invParam 1) 2)) (.rat (-1))), 910), ((.rat (-1)), 947), ((.mul (.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))) (.rat (-1))), 949)]
def instruction407 : List (Coefficient × ℕ) :=
  [((.rat (1)), 440), ((.rat (-1)), 888), ((.neg (.pow (.invParam 1) 2)), 892), ((.rat (-1)), 906), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 949)]
def instruction408 : List (Coefficient × ℕ) :=
  [((.rat (1)), 484), ((.rat (-1)), 671), ((.neg (.pow (.invParam 1) 2)), 747), ((.neg (.mul (.invParam 0) (.pow (.invParam 1) 2))), 770), ((.neg (.mul (.rat (-1)) (.pow (.invParam 1) 2))), 820), ((.rat (-1)), 824), ((.neg (.mul (.rat (-1)) (.mul (.invParam 0) (.pow (.invParam 1) 2)))), 856), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 867), ((.neg (.param 0)), 868), ((.neg (.mul (.param 4) (.mul (.invParam 0) (.invParam 1)))), 892), ((.neg (.mul (.param 4) (.invParam 1))), 899), ((.neg (.mul (.rat (-1)) (.mul (.pow (.invParam 0) 3) (.pow (.invParam 1) 2)))), 901), ((.neg (.add (.mul (.rat (-1)) (.mul (.pow (.invParam 0) 3) (.pow (.invParam 3) 2))) (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 3) 2)))), 904), ((.neg (.mul (.rat (-1)) (.invParam 0))), 949)]
def instruction409 : List (Coefficient × ℕ) :=
  [((.param 0), 511), ((.mul (.rat (-1)) (.param 0)), 588), ((.mul (.rat (-1)) (.param 0)), 636), ((.mul (.neg (.pow (.invParam 3) 2)) (.param 0)), 651), ((.mul (.neg (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2))) (.param 0)), 741), ((.mul (.rat (-1)) (.param 0)), 764), ((.mul (.neg (.mul (.rat (-1)) (.mul (.mul (.invParam 0) (.pow (.invParam 1) 2)) (.pow (.invParam 3) 2)))) (.param 0)), 776), ((.param 0), 791), ((.mul (.rat (-1)) (.param 0)), 812), ((.mul (.rat (-1)) (.param 0)), 835), ((.mul (.neg (.mul (.mul (.rat (-1)) (.param 5)) (.invParam 3))) (.param 0)), 863), ((.mul (.neg (.mul (.param 5) (.invParam 3))) (.param 0)), 876), ((.mul (.neg (.mul (.pow (.param 3) 2) (.mul (.invParam 0) (.pow (.invParam 1) 2)))) (.param 0)), 881), ((.param 0), 896), ((.mul (.neg (.mul (.pow (.param 1) 2) (.mul (.invParam 0) (.pow (.invParam 3) 2)))) (.param 0)), 904), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.param 0)), 916), ((.mul (.neg (.mul (.rat (-1)) (.invParam 0))) (.param 0)), 927), ((.param 0), 938)]
def instruction410 : List (Coefficient × ℕ) :=
  [((.rat (1)), 419), ((.rat (-1)), 616), ((.neg (.mul (.mul (.rat (-1)) (.param 4)) (.invParam 1))), 673), ((.neg (.mul (.mul (.mul (.rat (-1)) (.param 0)) (.param 4)) (.mul (.invParam 1) (.pow (.invParam 3) 2)))), 744), ((.rat (-1)), 749), ((.neg (.mul (.param 4) (.mul (.invParam 1) (.pow (.invParam 3) 2)))), 776), ((.neg (.pow (.invParam 1) 2)), 848), ((.neg (.mul (.mul (.rat (-1)) (.param 0)) (.pow (.invParam 3) 2))), 904), ((.neg (.mul (.rat (-1)) (.param 0))), 955)]
def instructions (i : ℕ) : List (Coefficient × ℕ) :=
  if i < 411 then
    if i < 205 then
      if i < 102 then
        if i < 51 then
          if i < 25 then
            if i < 12 then
              if i < 6 then
                if i < 3 then
                  if i < 1 then
                    instruction0
                  else
                    if i < 2 then
                      instruction1
                    else
                      instruction2
                else
                  if i < 4 then
                    instruction3
                  else
                    if i < 5 then
                      instruction4
                    else
                      instruction5
              else
                if i < 9 then
                  if i < 7 then
                    instruction6
                  else
                    if i < 8 then
                      instruction7
                    else
                      instruction8
                else
                  if i < 10 then
                    instruction9
                  else
                    if i < 11 then
                      instruction10
                    else
                      instruction11
            else
              if i < 18 then
                if i < 15 then
                  if i < 13 then
                    instruction12
                  else
                    if i < 14 then
                      instruction13
                    else
                      instruction14
                else
                  if i < 16 then
                    instruction15
                  else
                    if i < 17 then
                      instruction16
                    else
                      instruction17
              else
                if i < 21 then
                  if i < 19 then
                    instruction18
                  else
                    if i < 20 then
                      instruction19
                    else
                      instruction20
                else
                  if i < 23 then
                    if i < 22 then
                      instruction21
                    else
                      instruction22
                  else
                    if i < 24 then
                      instruction23
                    else
                      instruction24
          else
            if i < 38 then
              if i < 31 then
                if i < 28 then
                  if i < 26 then
                    instruction25
                  else
                    if i < 27 then
                      instruction26
                    else
                      instruction27
                else
                  if i < 29 then
                    instruction28
                  else
                    if i < 30 then
                      instruction29
                    else
                      instruction30
              else
                if i < 34 then
                  if i < 32 then
                    instruction31
                  else
                    if i < 33 then
                      instruction32
                    else
                      instruction33
                else
                  if i < 36 then
                    if i < 35 then
                      instruction34
                    else
                      instruction35
                  else
                    if i < 37 then
                      instruction36
                    else
                      instruction37
            else
              if i < 44 then
                if i < 41 then
                  if i < 39 then
                    instruction38
                  else
                    if i < 40 then
                      instruction39
                    else
                      instruction40
                else
                  if i < 42 then
                    instruction41
                  else
                    if i < 43 then
                      instruction42
                    else
                      instruction43
              else
                if i < 47 then
                  if i < 45 then
                    instruction44
                  else
                    if i < 46 then
                      instruction45
                    else
                      instruction46
                else
                  if i < 49 then
                    if i < 48 then
                      instruction47
                    else
                      instruction48
                  else
                    if i < 50 then
                      instruction49
                    else
                      instruction50
        else
          if i < 76 then
            if i < 63 then
              if i < 57 then
                if i < 54 then
                  if i < 52 then
                    instruction51
                  else
                    if i < 53 then
                      instruction52
                    else
                      instruction53
                else
                  if i < 55 then
                    instruction54
                  else
                    if i < 56 then
                      instruction55
                    else
                      instruction56
              else
                if i < 60 then
                  if i < 58 then
                    instruction57
                  else
                    if i < 59 then
                      instruction58
                    else
                      instruction59
                else
                  if i < 61 then
                    instruction60
                  else
                    if i < 62 then
                      instruction61
                    else
                      instruction62
            else
              if i < 69 then
                if i < 66 then
                  if i < 64 then
                    instruction63
                  else
                    if i < 65 then
                      instruction64
                    else
                      instruction65
                else
                  if i < 67 then
                    instruction66
                  else
                    if i < 68 then
                      instruction67
                    else
                      instruction68
              else
                if i < 72 then
                  if i < 70 then
                    instruction69
                  else
                    if i < 71 then
                      instruction70
                    else
                      instruction71
                else
                  if i < 74 then
                    if i < 73 then
                      instruction72
                    else
                      instruction73
                  else
                    if i < 75 then
                      instruction74
                    else
                      instruction75
          else
            if i < 89 then
              if i < 82 then
                if i < 79 then
                  if i < 77 then
                    instruction76
                  else
                    if i < 78 then
                      instruction77
                    else
                      instruction78
                else
                  if i < 80 then
                    instruction79
                  else
                    if i < 81 then
                      instruction80
                    else
                      instruction81
              else
                if i < 85 then
                  if i < 83 then
                    instruction82
                  else
                    if i < 84 then
                      instruction83
                    else
                      instruction84
                else
                  if i < 87 then
                    if i < 86 then
                      instruction85
                    else
                      instruction86
                  else
                    if i < 88 then
                      instruction87
                    else
                      instruction88
            else
              if i < 95 then
                if i < 92 then
                  if i < 90 then
                    instruction89
                  else
                    if i < 91 then
                      instruction90
                    else
                      instruction91
                else
                  if i < 93 then
                    instruction92
                  else
                    if i < 94 then
                      instruction93
                    else
                      instruction94
              else
                if i < 98 then
                  if i < 96 then
                    instruction95
                  else
                    if i < 97 then
                      instruction96
                    else
                      instruction97
                else
                  if i < 100 then
                    if i < 99 then
                      instruction98
                    else
                      instruction99
                  else
                    if i < 101 then
                      instruction100
                    else
                      instruction101
      else
        if i < 153 then
          if i < 127 then
            if i < 114 then
              if i < 108 then
                if i < 105 then
                  if i < 103 then
                    instruction102
                  else
                    if i < 104 then
                      instruction103
                    else
                      instruction104
                else
                  if i < 106 then
                    instruction105
                  else
                    if i < 107 then
                      instruction106
                    else
                      instruction107
              else
                if i < 111 then
                  if i < 109 then
                    instruction108
                  else
                    if i < 110 then
                      instruction109
                    else
                      instruction110
                else
                  if i < 112 then
                    instruction111
                  else
                    if i < 113 then
                      instruction112
                    else
                      instruction113
            else
              if i < 120 then
                if i < 117 then
                  if i < 115 then
                    instruction114
                  else
                    if i < 116 then
                      instruction115
                    else
                      instruction116
                else
                  if i < 118 then
                    instruction117
                  else
                    if i < 119 then
                      instruction118
                    else
                      instruction119
              else
                if i < 123 then
                  if i < 121 then
                    instruction120
                  else
                    if i < 122 then
                      instruction121
                    else
                      instruction122
                else
                  if i < 125 then
                    if i < 124 then
                      instruction123
                    else
                      instruction124
                  else
                    if i < 126 then
                      instruction125
                    else
                      instruction126
          else
            if i < 140 then
              if i < 133 then
                if i < 130 then
                  if i < 128 then
                    instruction127
                  else
                    if i < 129 then
                      instruction128
                    else
                      instruction129
                else
                  if i < 131 then
                    instruction130
                  else
                    if i < 132 then
                      instruction131
                    else
                      instruction132
              else
                if i < 136 then
                  if i < 134 then
                    instruction133
                  else
                    if i < 135 then
                      instruction134
                    else
                      instruction135
                else
                  if i < 138 then
                    if i < 137 then
                      instruction136
                    else
                      instruction137
                  else
                    if i < 139 then
                      instruction138
                    else
                      instruction139
            else
              if i < 146 then
                if i < 143 then
                  if i < 141 then
                    instruction140
                  else
                    if i < 142 then
                      instruction141
                    else
                      instruction142
                else
                  if i < 144 then
                    instruction143
                  else
                    if i < 145 then
                      instruction144
                    else
                      instruction145
              else
                if i < 149 then
                  if i < 147 then
                    instruction146
                  else
                    if i < 148 then
                      instruction147
                    else
                      instruction148
                else
                  if i < 151 then
                    if i < 150 then
                      instruction149
                    else
                      instruction150
                  else
                    if i < 152 then
                      instruction151
                    else
                      instruction152
        else
          if i < 179 then
            if i < 166 then
              if i < 159 then
                if i < 156 then
                  if i < 154 then
                    instruction153
                  else
                    if i < 155 then
                      instruction154
                    else
                      instruction155
                else
                  if i < 157 then
                    instruction156
                  else
                    if i < 158 then
                      instruction157
                    else
                      instruction158
              else
                if i < 162 then
                  if i < 160 then
                    instruction159
                  else
                    if i < 161 then
                      instruction160
                    else
                      instruction161
                else
                  if i < 164 then
                    if i < 163 then
                      instruction162
                    else
                      instruction163
                  else
                    if i < 165 then
                      instruction164
                    else
                      instruction165
            else
              if i < 172 then
                if i < 169 then
                  if i < 167 then
                    instruction166
                  else
                    if i < 168 then
                      instruction167
                    else
                      instruction168
                else
                  if i < 170 then
                    instruction169
                  else
                    if i < 171 then
                      instruction170
                    else
                      instruction171
              else
                if i < 175 then
                  if i < 173 then
                    instruction172
                  else
                    if i < 174 then
                      instruction173
                    else
                      instruction174
                else
                  if i < 177 then
                    if i < 176 then
                      instruction175
                    else
                      instruction176
                  else
                    if i < 178 then
                      instruction177
                    else
                      instruction178
          else
            if i < 192 then
              if i < 185 then
                if i < 182 then
                  if i < 180 then
                    instruction179
                  else
                    if i < 181 then
                      instruction180
                    else
                      instruction181
                else
                  if i < 183 then
                    instruction182
                  else
                    if i < 184 then
                      instruction183
                    else
                      instruction184
              else
                if i < 188 then
                  if i < 186 then
                    instruction185
                  else
                    if i < 187 then
                      instruction186
                    else
                      instruction187
                else
                  if i < 190 then
                    if i < 189 then
                      instruction188
                    else
                      instruction189
                  else
                    if i < 191 then
                      instruction190
                    else
                      instruction191
            else
              if i < 198 then
                if i < 195 then
                  if i < 193 then
                    instruction192
                  else
                    if i < 194 then
                      instruction193
                    else
                      instruction194
                else
                  if i < 196 then
                    instruction195
                  else
                    if i < 197 then
                      instruction196
                    else
                      instruction197
              else
                if i < 201 then
                  if i < 199 then
                    instruction198
                  else
                    if i < 200 then
                      instruction199
                    else
                      instruction200
                else
                  if i < 203 then
                    if i < 202 then
                      instruction201
                    else
                      instruction202
                  else
                    if i < 204 then
                      instruction203
                    else
                      instruction204
    else
      if i < 308 then
        if i < 256 then
          if i < 230 then
            if i < 217 then
              if i < 211 then
                if i < 208 then
                  if i < 206 then
                    instruction205
                  else
                    if i < 207 then
                      instruction206
                    else
                      instruction207
                else
                  if i < 209 then
                    instruction208
                  else
                    if i < 210 then
                      instruction209
                    else
                      instruction210
              else
                if i < 214 then
                  if i < 212 then
                    instruction211
                  else
                    if i < 213 then
                      instruction212
                    else
                      instruction213
                else
                  if i < 215 then
                    instruction214
                  else
                    if i < 216 then
                      instruction215
                    else
                      instruction216
            else
              if i < 223 then
                if i < 220 then
                  if i < 218 then
                    instruction217
                  else
                    if i < 219 then
                      instruction218
                    else
                      instruction219
                else
                  if i < 221 then
                    instruction220
                  else
                    if i < 222 then
                      instruction221
                    else
                      instruction222
              else
                if i < 226 then
                  if i < 224 then
                    instruction223
                  else
                    if i < 225 then
                      instruction224
                    else
                      instruction225
                else
                  if i < 228 then
                    if i < 227 then
                      instruction226
                    else
                      instruction227
                  else
                    if i < 229 then
                      instruction228
                    else
                      instruction229
          else
            if i < 243 then
              if i < 236 then
                if i < 233 then
                  if i < 231 then
                    instruction230
                  else
                    if i < 232 then
                      instruction231
                    else
                      instruction232
                else
                  if i < 234 then
                    instruction233
                  else
                    if i < 235 then
                      instruction234
                    else
                      instruction235
              else
                if i < 239 then
                  if i < 237 then
                    instruction236
                  else
                    if i < 238 then
                      instruction237
                    else
                      instruction238
                else
                  if i < 241 then
                    if i < 240 then
                      instruction239
                    else
                      instruction240
                  else
                    if i < 242 then
                      instruction241
                    else
                      instruction242
            else
              if i < 249 then
                if i < 246 then
                  if i < 244 then
                    instruction243
                  else
                    if i < 245 then
                      instruction244
                    else
                      instruction245
                else
                  if i < 247 then
                    instruction246
                  else
                    if i < 248 then
                      instruction247
                    else
                      instruction248
              else
                if i < 252 then
                  if i < 250 then
                    instruction249
                  else
                    if i < 251 then
                      instruction250
                    else
                      instruction251
                else
                  if i < 254 then
                    if i < 253 then
                      instruction252
                    else
                      instruction253
                  else
                    if i < 255 then
                      instruction254
                    else
                      instruction255
        else
          if i < 282 then
            if i < 269 then
              if i < 262 then
                if i < 259 then
                  if i < 257 then
                    instruction256
                  else
                    if i < 258 then
                      instruction257
                    else
                      instruction258
                else
                  if i < 260 then
                    instruction259
                  else
                    if i < 261 then
                      instruction260
                    else
                      instruction261
              else
                if i < 265 then
                  if i < 263 then
                    instruction262
                  else
                    if i < 264 then
                      instruction263
                    else
                      instruction264
                else
                  if i < 267 then
                    if i < 266 then
                      instruction265
                    else
                      instruction266
                  else
                    if i < 268 then
                      instruction267
                    else
                      instruction268
            else
              if i < 275 then
                if i < 272 then
                  if i < 270 then
                    instruction269
                  else
                    if i < 271 then
                      instruction270
                    else
                      instruction271
                else
                  if i < 273 then
                    instruction272
                  else
                    if i < 274 then
                      instruction273
                    else
                      instruction274
              else
                if i < 278 then
                  if i < 276 then
                    instruction275
                  else
                    if i < 277 then
                      instruction276
                    else
                      instruction277
                else
                  if i < 280 then
                    if i < 279 then
                      instruction278
                    else
                      instruction279
                  else
                    if i < 281 then
                      instruction280
                    else
                      instruction281
          else
            if i < 295 then
              if i < 288 then
                if i < 285 then
                  if i < 283 then
                    instruction282
                  else
                    if i < 284 then
                      instruction283
                    else
                      instruction284
                else
                  if i < 286 then
                    instruction285
                  else
                    if i < 287 then
                      instruction286
                    else
                      instruction287
              else
                if i < 291 then
                  if i < 289 then
                    instruction288
                  else
                    if i < 290 then
                      instruction289
                    else
                      instruction290
                else
                  if i < 293 then
                    if i < 292 then
                      instruction291
                    else
                      instruction292
                  else
                    if i < 294 then
                      instruction293
                    else
                      instruction294
            else
              if i < 301 then
                if i < 298 then
                  if i < 296 then
                    instruction295
                  else
                    if i < 297 then
                      instruction296
                    else
                      instruction297
                else
                  if i < 299 then
                    instruction298
                  else
                    if i < 300 then
                      instruction299
                    else
                      instruction300
              else
                if i < 304 then
                  if i < 302 then
                    instruction301
                  else
                    if i < 303 then
                      instruction302
                    else
                      instruction303
                else
                  if i < 306 then
                    if i < 305 then
                      instruction304
                    else
                      instruction305
                  else
                    if i < 307 then
                      instruction306
                    else
                      instruction307
      else
        if i < 359 then
          if i < 333 then
            if i < 320 then
              if i < 314 then
                if i < 311 then
                  if i < 309 then
                    instruction308
                  else
                    if i < 310 then
                      instruction309
                    else
                      instruction310
                else
                  if i < 312 then
                    instruction311
                  else
                    if i < 313 then
                      instruction312
                    else
                      instruction313
              else
                if i < 317 then
                  if i < 315 then
                    instruction314
                  else
                    if i < 316 then
                      instruction315
                    else
                      instruction316
                else
                  if i < 318 then
                    instruction317
                  else
                    if i < 319 then
                      instruction318
                    else
                      instruction319
            else
              if i < 326 then
                if i < 323 then
                  if i < 321 then
                    instruction320
                  else
                    if i < 322 then
                      instruction321
                    else
                      instruction322
                else
                  if i < 324 then
                    instruction323
                  else
                    if i < 325 then
                      instruction324
                    else
                      instruction325
              else
                if i < 329 then
                  if i < 327 then
                    instruction326
                  else
                    if i < 328 then
                      instruction327
                    else
                      instruction328
                else
                  if i < 331 then
                    if i < 330 then
                      instruction329
                    else
                      instruction330
                  else
                    if i < 332 then
                      instruction331
                    else
                      instruction332
          else
            if i < 346 then
              if i < 339 then
                if i < 336 then
                  if i < 334 then
                    instruction333
                  else
                    if i < 335 then
                      instruction334
                    else
                      instruction335
                else
                  if i < 337 then
                    instruction336
                  else
                    if i < 338 then
                      instruction337
                    else
                      instruction338
              else
                if i < 342 then
                  if i < 340 then
                    instruction339
                  else
                    if i < 341 then
                      instruction340
                    else
                      instruction341
                else
                  if i < 344 then
                    if i < 343 then
                      instruction342
                    else
                      instruction343
                  else
                    if i < 345 then
                      instruction344
                    else
                      instruction345
            else
              if i < 352 then
                if i < 349 then
                  if i < 347 then
                    instruction346
                  else
                    if i < 348 then
                      instruction347
                    else
                      instruction348
                else
                  if i < 350 then
                    instruction349
                  else
                    if i < 351 then
                      instruction350
                    else
                      instruction351
              else
                if i < 355 then
                  if i < 353 then
                    instruction352
                  else
                    if i < 354 then
                      instruction353
                    else
                      instruction354
                else
                  if i < 357 then
                    if i < 356 then
                      instruction355
                    else
                      instruction356
                  else
                    if i < 358 then
                      instruction357
                    else
                      instruction358
        else
          if i < 385 then
            if i < 372 then
              if i < 365 then
                if i < 362 then
                  if i < 360 then
                    instruction359
                  else
                    if i < 361 then
                      instruction360
                    else
                      instruction361
                else
                  if i < 363 then
                    instruction362
                  else
                    if i < 364 then
                      instruction363
                    else
                      instruction364
              else
                if i < 368 then
                  if i < 366 then
                    instruction365
                  else
                    if i < 367 then
                      instruction366
                    else
                      instruction367
                else
                  if i < 370 then
                    if i < 369 then
                      instruction368
                    else
                      instruction369
                  else
                    if i < 371 then
                      instruction370
                    else
                      instruction371
            else
              if i < 378 then
                if i < 375 then
                  if i < 373 then
                    instruction372
                  else
                    if i < 374 then
                      instruction373
                    else
                      instruction374
                else
                  if i < 376 then
                    instruction375
                  else
                    if i < 377 then
                      instruction376
                    else
                      instruction377
              else
                if i < 381 then
                  if i < 379 then
                    instruction378
                  else
                    if i < 380 then
                      instruction379
                    else
                      instruction380
                else
                  if i < 383 then
                    if i < 382 then
                      instruction381
                    else
                      instruction382
                  else
                    if i < 384 then
                      instruction383
                    else
                      instruction384
          else
            if i < 398 then
              if i < 391 then
                if i < 388 then
                  if i < 386 then
                    instruction385
                  else
                    if i < 387 then
                      instruction386
                    else
                      instruction387
                else
                  if i < 389 then
                    instruction388
                  else
                    if i < 390 then
                      instruction389
                    else
                      instruction390
              else
                if i < 394 then
                  if i < 392 then
                    instruction391
                  else
                    if i < 393 then
                      instruction392
                    else
                      instruction393
                else
                  if i < 396 then
                    if i < 395 then
                      instruction394
                    else
                      instruction395
                  else
                    if i < 397 then
                      instruction396
                    else
                      instruction397
            else
              if i < 404 then
                if i < 401 then
                  if i < 399 then
                    instruction398
                  else
                    if i < 400 then
                      instruction399
                    else
                      instruction400
                else
                  if i < 402 then
                    instruction401
                  else
                    if i < 403 then
                      instruction402
                    else
                      instruction403
              else
                if i < 407 then
                  if i < 405 then
                    instruction404
                  else
                    if i < 406 then
                      instruction405
                    else
                      instruction406
                else
                  if i < 409 then
                    if i < 408 then
                      instruction407
                    else
                      instruction408
                  else
                    if i < 410 then
                      instruction409
                    else
                      instruction410
  else []
def rows (X Y Z W a b : ℂ) (i : ℕ) (r : Fin 546 → ℂ) : ℂ :=
  if i < 411 then
    if i < 205 then
      if i < 102 then
        if i < 51 then
          if i < 25 then
            if i < 12 then
              if i < 6 then
                if i < 3 then
                  if i < 1 then
                    rhsPivot0 X Y Z W a b r
                  else
                    if i < 2 then
                      rhsPivot1 X Y Z W a b r
                    else
                      rhsPivot2 X Y Z W a b r
                else
                  if i < 4 then
                    rhsPivot3 X Y Z W a b r
                  else
                    if i < 5 then
                      rhsPivot4 X Y Z W a b r
                    else
                      rhsPivot5 X Y Z W a b r
              else
                if i < 9 then
                  if i < 7 then
                    rhsPivot6 X Y Z W a b r
                  else
                    if i < 8 then
                      rhsPivot7 X Y Z W a b r
                    else
                      rhsPivot8 X Y Z W a b r
                else
                  if i < 10 then
                    rhsPivot9 X Y Z W a b r
                  else
                    if i < 11 then
                      rhsPivot10 X Y Z W a b r
                    else
                      rhsPivot11 X Y Z W a b r
            else
              if i < 18 then
                if i < 15 then
                  if i < 13 then
                    rhsPivot12 X Y Z W a b r
                  else
                    if i < 14 then
                      rhsPivot13 X Y Z W a b r
                    else
                      rhsPivot14 X Y Z W a b r
                else
                  if i < 16 then
                    rhsPivot15 X Y Z W a b r
                  else
                    if i < 17 then
                      rhsPivot16 X Y Z W a b r
                    else
                      rhsPivot17 X Y Z W a b r
              else
                if i < 21 then
                  if i < 19 then
                    rhsPivot18 X Y Z W a b r
                  else
                    if i < 20 then
                      rhsPivot19 X Y Z W a b r
                    else
                      rhsPivot20 X Y Z W a b r
                else
                  if i < 23 then
                    if i < 22 then
                      rhsPivot21 X Y Z W a b r
                    else
                      rhsPivot22 X Y Z W a b r
                  else
                    if i < 24 then
                      rhsPivot23 X Y Z W a b r
                    else
                      rhsPivot24 X Y Z W a b r
          else
            if i < 38 then
              if i < 31 then
                if i < 28 then
                  if i < 26 then
                    rhsPivot25 X Y Z W a b r
                  else
                    if i < 27 then
                      rhsPivot26 X Y Z W a b r
                    else
                      rhsPivot27 X Y Z W a b r
                else
                  if i < 29 then
                    rhsPivot28 X Y Z W a b r
                  else
                    if i < 30 then
                      rhsPivot29 X Y Z W a b r
                    else
                      rhsPivot30 X Y Z W a b r
              else
                if i < 34 then
                  if i < 32 then
                    rhsPivot31 X Y Z W a b r
                  else
                    if i < 33 then
                      rhsPivot32 X Y Z W a b r
                    else
                      rhsPivot33 X Y Z W a b r
                else
                  if i < 36 then
                    if i < 35 then
                      rhsPivot34 X Y Z W a b r
                    else
                      rhsPivot35 X Y Z W a b r
                  else
                    if i < 37 then
                      rhsPivot36 X Y Z W a b r
                    else
                      rhsPivot37 X Y Z W a b r
            else
              if i < 44 then
                if i < 41 then
                  if i < 39 then
                    rhsPivot38 X Y Z W a b r
                  else
                    if i < 40 then
                      rhsPivot39 X Y Z W a b r
                    else
                      rhsPivot40 X Y Z W a b r
                else
                  if i < 42 then
                    rhsPivot41 X Y Z W a b r
                  else
                    if i < 43 then
                      rhsPivot42 X Y Z W a b r
                    else
                      rhsPivot43 X Y Z W a b r
              else
                if i < 47 then
                  if i < 45 then
                    rhsPivot44 X Y Z W a b r
                  else
                    if i < 46 then
                      rhsPivot45 X Y Z W a b r
                    else
                      rhsPivot46 X Y Z W a b r
                else
                  if i < 49 then
                    if i < 48 then
                      rhsPivot47 X Y Z W a b r
                    else
                      rhsPivot48 X Y Z W a b r
                  else
                    if i < 50 then
                      rhsPivot49 X Y Z W a b r
                    else
                      rhsPivot50 X Y Z W a b r
        else
          if i < 76 then
            if i < 63 then
              if i < 57 then
                if i < 54 then
                  if i < 52 then
                    rhsPivot51 X Y Z W a b r
                  else
                    if i < 53 then
                      rhsPivot52 X Y Z W a b r
                    else
                      rhsPivot53 X Y Z W a b r
                else
                  if i < 55 then
                    rhsPivot54 X Y Z W a b r
                  else
                    if i < 56 then
                      rhsPivot55 X Y Z W a b r
                    else
                      rhsPivot56 X Y Z W a b r
              else
                if i < 60 then
                  if i < 58 then
                    rhsPivot57 X Y Z W a b r
                  else
                    if i < 59 then
                      rhsPivot58 X Y Z W a b r
                    else
                      rhsPivot59 X Y Z W a b r
                else
                  if i < 61 then
                    rhsPivot60 X Y Z W a b r
                  else
                    if i < 62 then
                      rhsPivot61 X Y Z W a b r
                    else
                      rhsPivot62 X Y Z W a b r
            else
              if i < 69 then
                if i < 66 then
                  if i < 64 then
                    rhsPivot63 X Y Z W a b r
                  else
                    if i < 65 then
                      rhsPivot64 X Y Z W a b r
                    else
                      rhsPivot65 X Y Z W a b r
                else
                  if i < 67 then
                    rhsPivot66 X Y Z W a b r
                  else
                    if i < 68 then
                      rhsPivot67 X Y Z W a b r
                    else
                      rhsPivot68 X Y Z W a b r
              else
                if i < 72 then
                  if i < 70 then
                    rhsPivot69 X Y Z W a b r
                  else
                    if i < 71 then
                      rhsPivot70 X Y Z W a b r
                    else
                      rhsPivot71 X Y Z W a b r
                else
                  if i < 74 then
                    if i < 73 then
                      rhsPivot72 X Y Z W a b r
                    else
                      rhsPivot73 X Y Z W a b r
                  else
                    if i < 75 then
                      rhsPivot74 X Y Z W a b r
                    else
                      rhsPivot75 X Y Z W a b r
          else
            if i < 89 then
              if i < 82 then
                if i < 79 then
                  if i < 77 then
                    rhsPivot76 X Y Z W a b r
                  else
                    if i < 78 then
                      rhsPivot77 X Y Z W a b r
                    else
                      rhsPivot78 X Y Z W a b r
                else
                  if i < 80 then
                    rhsPivot79 X Y Z W a b r
                  else
                    if i < 81 then
                      rhsPivot80 X Y Z W a b r
                    else
                      rhsPivot81 X Y Z W a b r
              else
                if i < 85 then
                  if i < 83 then
                    rhsPivot82 X Y Z W a b r
                  else
                    if i < 84 then
                      rhsPivot83 X Y Z W a b r
                    else
                      rhsPivot84 X Y Z W a b r
                else
                  if i < 87 then
                    if i < 86 then
                      rhsPivot85 X Y Z W a b r
                    else
                      rhsPivot86 X Y Z W a b r
                  else
                    if i < 88 then
                      rhsPivot87 X Y Z W a b r
                    else
                      rhsPivot88 X Y Z W a b r
            else
              if i < 95 then
                if i < 92 then
                  if i < 90 then
                    rhsPivot89 X Y Z W a b r
                  else
                    if i < 91 then
                      rhsPivot90 X Y Z W a b r
                    else
                      rhsPivot91 X Y Z W a b r
                else
                  if i < 93 then
                    rhsPivot92 X Y Z W a b r
                  else
                    if i < 94 then
                      rhsPivot93 X Y Z W a b r
                    else
                      rhsPivot94 X Y Z W a b r
              else
                if i < 98 then
                  if i < 96 then
                    rhsPivot95 X Y Z W a b r
                  else
                    if i < 97 then
                      rhsPivot96 X Y Z W a b r
                    else
                      rhsPivot97 X Y Z W a b r
                else
                  if i < 100 then
                    if i < 99 then
                      rhsPivot98 X Y Z W a b r
                    else
                      rhsPivot99 X Y Z W a b r
                  else
                    if i < 101 then
                      rhsPivot100 X Y Z W a b r
                    else
                      rhsPivot101 X Y Z W a b r
      else
        if i < 153 then
          if i < 127 then
            if i < 114 then
              if i < 108 then
                if i < 105 then
                  if i < 103 then
                    rhsPivot102 X Y Z W a b r
                  else
                    if i < 104 then
                      rhsPivot103 X Y Z W a b r
                    else
                      rhsPivot104 X Y Z W a b r
                else
                  if i < 106 then
                    rhsPivot105 X Y Z W a b r
                  else
                    if i < 107 then
                      rhsPivot106 X Y Z W a b r
                    else
                      rhsPivot107 X Y Z W a b r
              else
                if i < 111 then
                  if i < 109 then
                    rhsPivot108 X Y Z W a b r
                  else
                    if i < 110 then
                      rhsPivot109 X Y Z W a b r
                    else
                      rhsPivot110 X Y Z W a b r
                else
                  if i < 112 then
                    rhsPivot111 X Y Z W a b r
                  else
                    if i < 113 then
                      rhsPivot112 X Y Z W a b r
                    else
                      rhsPivot113 X Y Z W a b r
            else
              if i < 120 then
                if i < 117 then
                  if i < 115 then
                    rhsPivot114 X Y Z W a b r
                  else
                    if i < 116 then
                      rhsPivot115 X Y Z W a b r
                    else
                      rhsPivot116 X Y Z W a b r
                else
                  if i < 118 then
                    rhsPivot117 X Y Z W a b r
                  else
                    if i < 119 then
                      rhsPivot118 X Y Z W a b r
                    else
                      rhsPivot119 X Y Z W a b r
              else
                if i < 123 then
                  if i < 121 then
                    rhsPivot120 X Y Z W a b r
                  else
                    if i < 122 then
                      rhsPivot121 X Y Z W a b r
                    else
                      rhsPivot122 X Y Z W a b r
                else
                  if i < 125 then
                    if i < 124 then
                      rhsPivot123 X Y Z W a b r
                    else
                      rhsPivot124 X Y Z W a b r
                  else
                    if i < 126 then
                      rhsPivot125 X Y Z W a b r
                    else
                      rhsPivot126 X Y Z W a b r
          else
            if i < 140 then
              if i < 133 then
                if i < 130 then
                  if i < 128 then
                    rhsPivot127 X Y Z W a b r
                  else
                    if i < 129 then
                      rhsPivot128 X Y Z W a b r
                    else
                      rhsPivot129 X Y Z W a b r
                else
                  if i < 131 then
                    rhsPivot130 X Y Z W a b r
                  else
                    if i < 132 then
                      rhsPivot131 X Y Z W a b r
                    else
                      rhsPivot132 X Y Z W a b r
              else
                if i < 136 then
                  if i < 134 then
                    rhsPivot133 X Y Z W a b r
                  else
                    if i < 135 then
                      rhsPivot134 X Y Z W a b r
                    else
                      rhsPivot135 X Y Z W a b r
                else
                  if i < 138 then
                    if i < 137 then
                      rhsPivot136 X Y Z W a b r
                    else
                      rhsPivot137 X Y Z W a b r
                  else
                    if i < 139 then
                      rhsPivot138 X Y Z W a b r
                    else
                      rhsPivot139 X Y Z W a b r
            else
              if i < 146 then
                if i < 143 then
                  if i < 141 then
                    rhsPivot140 X Y Z W a b r
                  else
                    if i < 142 then
                      rhsPivot141 X Y Z W a b r
                    else
                      rhsPivot142 X Y Z W a b r
                else
                  if i < 144 then
                    rhsPivot143 X Y Z W a b r
                  else
                    if i < 145 then
                      rhsPivot144 X Y Z W a b r
                    else
                      rhsPivot145 X Y Z W a b r
              else
                if i < 149 then
                  if i < 147 then
                    rhsPivot146 X Y Z W a b r
                  else
                    if i < 148 then
                      rhsPivot147 X Y Z W a b r
                    else
                      rhsPivot148 X Y Z W a b r
                else
                  if i < 151 then
                    if i < 150 then
                      rhsPivot149 X Y Z W a b r
                    else
                      rhsPivot150 X Y Z W a b r
                  else
                    if i < 152 then
                      rhsPivot151 X Y Z W a b r
                    else
                      rhsPivot152 X Y Z W a b r
        else
          if i < 179 then
            if i < 166 then
              if i < 159 then
                if i < 156 then
                  if i < 154 then
                    rhsPivot153 X Y Z W a b r
                  else
                    if i < 155 then
                      rhsPivot154 X Y Z W a b r
                    else
                      rhsPivot155 X Y Z W a b r
                else
                  if i < 157 then
                    rhsPivot156 X Y Z W a b r
                  else
                    if i < 158 then
                      rhsPivot157 X Y Z W a b r
                    else
                      rhsPivot158 X Y Z W a b r
              else
                if i < 162 then
                  if i < 160 then
                    rhsPivot159 X Y Z W a b r
                  else
                    if i < 161 then
                      rhsPivot160 X Y Z W a b r
                    else
                      rhsPivot161 X Y Z W a b r
                else
                  if i < 164 then
                    if i < 163 then
                      rhsPivot162 X Y Z W a b r
                    else
                      rhsPivot163 X Y Z W a b r
                  else
                    if i < 165 then
                      rhsPivot164 X Y Z W a b r
                    else
                      rhsPivot165 X Y Z W a b r
            else
              if i < 172 then
                if i < 169 then
                  if i < 167 then
                    rhsPivot166 X Y Z W a b r
                  else
                    if i < 168 then
                      rhsPivot167 X Y Z W a b r
                    else
                      rhsPivot168 X Y Z W a b r
                else
                  if i < 170 then
                    rhsPivot169 X Y Z W a b r
                  else
                    if i < 171 then
                      rhsPivot170 X Y Z W a b r
                    else
                      rhsPivot171 X Y Z W a b r
              else
                if i < 175 then
                  if i < 173 then
                    rhsPivot172 X Y Z W a b r
                  else
                    if i < 174 then
                      rhsPivot173 X Y Z W a b r
                    else
                      rhsPivot174 X Y Z W a b r
                else
                  if i < 177 then
                    if i < 176 then
                      rhsPivot175 X Y Z W a b r
                    else
                      rhsPivot176 X Y Z W a b r
                  else
                    if i < 178 then
                      rhsPivot177 X Y Z W a b r
                    else
                      rhsPivot178 X Y Z W a b r
          else
            if i < 192 then
              if i < 185 then
                if i < 182 then
                  if i < 180 then
                    rhsPivot179 X Y Z W a b r
                  else
                    if i < 181 then
                      rhsPivot180 X Y Z W a b r
                    else
                      rhsPivot181 X Y Z W a b r
                else
                  if i < 183 then
                    rhsPivot182 X Y Z W a b r
                  else
                    if i < 184 then
                      rhsPivot183 X Y Z W a b r
                    else
                      rhsPivot184 X Y Z W a b r
              else
                if i < 188 then
                  if i < 186 then
                    rhsPivot185 X Y Z W a b r
                  else
                    if i < 187 then
                      rhsPivot186 X Y Z W a b r
                    else
                      rhsPivot187 X Y Z W a b r
                else
                  if i < 190 then
                    if i < 189 then
                      rhsPivot188 X Y Z W a b r
                    else
                      rhsPivot189 X Y Z W a b r
                  else
                    if i < 191 then
                      rhsPivot190 X Y Z W a b r
                    else
                      rhsPivot191 X Y Z W a b r
            else
              if i < 198 then
                if i < 195 then
                  if i < 193 then
                    rhsPivot192 X Y Z W a b r
                  else
                    if i < 194 then
                      rhsPivot193 X Y Z W a b r
                    else
                      rhsPivot194 X Y Z W a b r
                else
                  if i < 196 then
                    rhsPivot195 X Y Z W a b r
                  else
                    if i < 197 then
                      rhsPivot196 X Y Z W a b r
                    else
                      rhsPivot197 X Y Z W a b r
              else
                if i < 201 then
                  if i < 199 then
                    rhsPivot198 X Y Z W a b r
                  else
                    if i < 200 then
                      rhsPivot199 X Y Z W a b r
                    else
                      rhsPivot200 X Y Z W a b r
                else
                  if i < 203 then
                    if i < 202 then
                      rhsPivot201 X Y Z W a b r
                    else
                      rhsPivot202 X Y Z W a b r
                  else
                    if i < 204 then
                      rhsPivot203 X Y Z W a b r
                    else
                      rhsPivot204 X Y Z W a b r
    else
      if i < 308 then
        if i < 256 then
          if i < 230 then
            if i < 217 then
              if i < 211 then
                if i < 208 then
                  if i < 206 then
                    rhsPivot205 X Y Z W a b r
                  else
                    if i < 207 then
                      rhsPivot206 X Y Z W a b r
                    else
                      rhsPivot207 X Y Z W a b r
                else
                  if i < 209 then
                    rhsPivot208 X Y Z W a b r
                  else
                    if i < 210 then
                      rhsPivot209 X Y Z W a b r
                    else
                      rhsPivot210 X Y Z W a b r
              else
                if i < 214 then
                  if i < 212 then
                    rhsPivot211 X Y Z W a b r
                  else
                    if i < 213 then
                      rhsPivot212 X Y Z W a b r
                    else
                      rhsPivot213 X Y Z W a b r
                else
                  if i < 215 then
                    rhsPivot214 X Y Z W a b r
                  else
                    if i < 216 then
                      rhsPivot215 X Y Z W a b r
                    else
                      rhsPivot216 X Y Z W a b r
            else
              if i < 223 then
                if i < 220 then
                  if i < 218 then
                    rhsPivot217 X Y Z W a b r
                  else
                    if i < 219 then
                      rhsPivot218 X Y Z W a b r
                    else
                      rhsPivot219 X Y Z W a b r
                else
                  if i < 221 then
                    rhsPivot220 X Y Z W a b r
                  else
                    if i < 222 then
                      rhsPivot221 X Y Z W a b r
                    else
                      rhsPivot222 X Y Z W a b r
              else
                if i < 226 then
                  if i < 224 then
                    rhsPivot223 X Y Z W a b r
                  else
                    if i < 225 then
                      rhsPivot224 X Y Z W a b r
                    else
                      rhsPivot225 X Y Z W a b r
                else
                  if i < 228 then
                    if i < 227 then
                      rhsPivot226 X Y Z W a b r
                    else
                      rhsPivot227 X Y Z W a b r
                  else
                    if i < 229 then
                      rhsPivot228 X Y Z W a b r
                    else
                      rhsPivot229 X Y Z W a b r
          else
            if i < 243 then
              if i < 236 then
                if i < 233 then
                  if i < 231 then
                    rhsPivot230 X Y Z W a b r
                  else
                    if i < 232 then
                      rhsPivot231 X Y Z W a b r
                    else
                      rhsPivot232 X Y Z W a b r
                else
                  if i < 234 then
                    rhsPivot233 X Y Z W a b r
                  else
                    if i < 235 then
                      rhsPivot234 X Y Z W a b r
                    else
                      rhsPivot235 X Y Z W a b r
              else
                if i < 239 then
                  if i < 237 then
                    rhsPivot236 X Y Z W a b r
                  else
                    if i < 238 then
                      rhsPivot237 X Y Z W a b r
                    else
                      rhsPivot238 X Y Z W a b r
                else
                  if i < 241 then
                    if i < 240 then
                      rhsPivot239 X Y Z W a b r
                    else
                      rhsPivot240 X Y Z W a b r
                  else
                    if i < 242 then
                      rhsPivot241 X Y Z W a b r
                    else
                      rhsPivot242 X Y Z W a b r
            else
              if i < 249 then
                if i < 246 then
                  if i < 244 then
                    rhsPivot243 X Y Z W a b r
                  else
                    if i < 245 then
                      rhsPivot244 X Y Z W a b r
                    else
                      rhsPivot245 X Y Z W a b r
                else
                  if i < 247 then
                    rhsPivot246 X Y Z W a b r
                  else
                    if i < 248 then
                      rhsPivot247 X Y Z W a b r
                    else
                      rhsPivot248 X Y Z W a b r
              else
                if i < 252 then
                  if i < 250 then
                    rhsPivot249 X Y Z W a b r
                  else
                    if i < 251 then
                      rhsPivot250 X Y Z W a b r
                    else
                      rhsPivot251 X Y Z W a b r
                else
                  if i < 254 then
                    if i < 253 then
                      rhsPivot252 X Y Z W a b r
                    else
                      rhsPivot253 X Y Z W a b r
                  else
                    if i < 255 then
                      rhsPivot254 X Y Z W a b r
                    else
                      rhsPivot255 X Y Z W a b r
        else
          if i < 282 then
            if i < 269 then
              if i < 262 then
                if i < 259 then
                  if i < 257 then
                    rhsPivot256 X Y Z W a b r
                  else
                    if i < 258 then
                      rhsPivot257 X Y Z W a b r
                    else
                      rhsPivot258 X Y Z W a b r
                else
                  if i < 260 then
                    rhsPivot259 X Y Z W a b r
                  else
                    if i < 261 then
                      rhsPivot260 X Y Z W a b r
                    else
                      rhsPivot261 X Y Z W a b r
              else
                if i < 265 then
                  if i < 263 then
                    rhsPivot262 X Y Z W a b r
                  else
                    if i < 264 then
                      rhsPivot263 X Y Z W a b r
                    else
                      rhsPivot264 X Y Z W a b r
                else
                  if i < 267 then
                    if i < 266 then
                      rhsPivot265 X Y Z W a b r
                    else
                      rhsPivot266 X Y Z W a b r
                  else
                    if i < 268 then
                      rhsPivot267 X Y Z W a b r
                    else
                      rhsPivot268 X Y Z W a b r
            else
              if i < 275 then
                if i < 272 then
                  if i < 270 then
                    rhsPivot269 X Y Z W a b r
                  else
                    if i < 271 then
                      rhsPivot270 X Y Z W a b r
                    else
                      rhsPivot271 X Y Z W a b r
                else
                  if i < 273 then
                    rhsPivot272 X Y Z W a b r
                  else
                    if i < 274 then
                      rhsPivot273 X Y Z W a b r
                    else
                      rhsPivot274 X Y Z W a b r
              else
                if i < 278 then
                  if i < 276 then
                    rhsPivot275 X Y Z W a b r
                  else
                    if i < 277 then
                      rhsPivot276 X Y Z W a b r
                    else
                      rhsPivot277 X Y Z W a b r
                else
                  if i < 280 then
                    if i < 279 then
                      rhsPivot278 X Y Z W a b r
                    else
                      rhsPivot279 X Y Z W a b r
                  else
                    if i < 281 then
                      rhsPivot280 X Y Z W a b r
                    else
                      rhsPivot281 X Y Z W a b r
          else
            if i < 295 then
              if i < 288 then
                if i < 285 then
                  if i < 283 then
                    rhsPivot282 X Y Z W a b r
                  else
                    if i < 284 then
                      rhsPivot283 X Y Z W a b r
                    else
                      rhsPivot284 X Y Z W a b r
                else
                  if i < 286 then
                    rhsPivot285 X Y Z W a b r
                  else
                    if i < 287 then
                      rhsPivot286 X Y Z W a b r
                    else
                      rhsPivot287 X Y Z W a b r
              else
                if i < 291 then
                  if i < 289 then
                    rhsPivot288 X Y Z W a b r
                  else
                    if i < 290 then
                      rhsPivot289 X Y Z W a b r
                    else
                      rhsPivot290 X Y Z W a b r
                else
                  if i < 293 then
                    if i < 292 then
                      rhsPivot291 X Y Z W a b r
                    else
                      rhsPivot292 X Y Z W a b r
                  else
                    if i < 294 then
                      rhsPivot293 X Y Z W a b r
                    else
                      rhsPivot294 X Y Z W a b r
            else
              if i < 301 then
                if i < 298 then
                  if i < 296 then
                    rhsPivot295 X Y Z W a b r
                  else
                    if i < 297 then
                      rhsPivot296 X Y Z W a b r
                    else
                      rhsPivot297 X Y Z W a b r
                else
                  if i < 299 then
                    rhsPivot298 X Y Z W a b r
                  else
                    if i < 300 then
                      rhsPivot299 X Y Z W a b r
                    else
                      rhsPivot300 X Y Z W a b r
              else
                if i < 304 then
                  if i < 302 then
                    rhsPivot301 X Y Z W a b r
                  else
                    if i < 303 then
                      rhsPivot302 X Y Z W a b r
                    else
                      rhsPivot303 X Y Z W a b r
                else
                  if i < 306 then
                    if i < 305 then
                      rhsPivot304 X Y Z W a b r
                    else
                      rhsPivot305 X Y Z W a b r
                  else
                    if i < 307 then
                      rhsPivot306 X Y Z W a b r
                    else
                      rhsPivot307 X Y Z W a b r
      else
        if i < 359 then
          if i < 333 then
            if i < 320 then
              if i < 314 then
                if i < 311 then
                  if i < 309 then
                    rhsPivot308 X Y Z W a b r
                  else
                    if i < 310 then
                      rhsPivot309 X Y Z W a b r
                    else
                      rhsPivot310 X Y Z W a b r
                else
                  if i < 312 then
                    rhsPivot311 X Y Z W a b r
                  else
                    if i < 313 then
                      rhsPivot312 X Y Z W a b r
                    else
                      rhsPivot313 X Y Z W a b r
              else
                if i < 317 then
                  if i < 315 then
                    rhsPivot314 X Y Z W a b r
                  else
                    if i < 316 then
                      rhsPivot315 X Y Z W a b r
                    else
                      rhsPivot316 X Y Z W a b r
                else
                  if i < 318 then
                    rhsPivot317 X Y Z W a b r
                  else
                    if i < 319 then
                      rhsPivot318 X Y Z W a b r
                    else
                      rhsPivot319 X Y Z W a b r
            else
              if i < 326 then
                if i < 323 then
                  if i < 321 then
                    rhsPivot320 X Y Z W a b r
                  else
                    if i < 322 then
                      rhsPivot321 X Y Z W a b r
                    else
                      rhsPivot322 X Y Z W a b r
                else
                  if i < 324 then
                    rhsPivot323 X Y Z W a b r
                  else
                    if i < 325 then
                      rhsPivot324 X Y Z W a b r
                    else
                      rhsPivot325 X Y Z W a b r
              else
                if i < 329 then
                  if i < 327 then
                    rhsPivot326 X Y Z W a b r
                  else
                    if i < 328 then
                      rhsPivot327 X Y Z W a b r
                    else
                      rhsPivot328 X Y Z W a b r
                else
                  if i < 331 then
                    if i < 330 then
                      rhsPivot329 X Y Z W a b r
                    else
                      rhsPivot330 X Y Z W a b r
                  else
                    if i < 332 then
                      rhsPivot331 X Y Z W a b r
                    else
                      rhsPivot332 X Y Z W a b r
          else
            if i < 346 then
              if i < 339 then
                if i < 336 then
                  if i < 334 then
                    rhsPivot333 X Y Z W a b r
                  else
                    if i < 335 then
                      rhsPivot334 X Y Z W a b r
                    else
                      rhsPivot335 X Y Z W a b r
                else
                  if i < 337 then
                    rhsPivot336 X Y Z W a b r
                  else
                    if i < 338 then
                      rhsPivot337 X Y Z W a b r
                    else
                      rhsPivot338 X Y Z W a b r
              else
                if i < 342 then
                  if i < 340 then
                    rhsPivot339 X Y Z W a b r
                  else
                    if i < 341 then
                      rhsPivot340 X Y Z W a b r
                    else
                      rhsPivot341 X Y Z W a b r
                else
                  if i < 344 then
                    if i < 343 then
                      rhsPivot342 X Y Z W a b r
                    else
                      rhsPivot343 X Y Z W a b r
                  else
                    if i < 345 then
                      rhsPivot344 X Y Z W a b r
                    else
                      rhsPivot345 X Y Z W a b r
            else
              if i < 352 then
                if i < 349 then
                  if i < 347 then
                    rhsPivot346 X Y Z W a b r
                  else
                    if i < 348 then
                      rhsPivot347 X Y Z W a b r
                    else
                      rhsPivot348 X Y Z W a b r
                else
                  if i < 350 then
                    rhsPivot349 X Y Z W a b r
                  else
                    if i < 351 then
                      rhsPivot350 X Y Z W a b r
                    else
                      rhsPivot351 X Y Z W a b r
              else
                if i < 355 then
                  if i < 353 then
                    rhsPivot352 X Y Z W a b r
                  else
                    if i < 354 then
                      rhsPivot353 X Y Z W a b r
                    else
                      rhsPivot354 X Y Z W a b r
                else
                  if i < 357 then
                    if i < 356 then
                      rhsPivot355 X Y Z W a b r
                    else
                      rhsPivot356 X Y Z W a b r
                  else
                    if i < 358 then
                      rhsPivot357 X Y Z W a b r
                    else
                      rhsPivot358 X Y Z W a b r
        else
          if i < 385 then
            if i < 372 then
              if i < 365 then
                if i < 362 then
                  if i < 360 then
                    rhsPivot359 X Y Z W a b r
                  else
                    if i < 361 then
                      rhsPivot360 X Y Z W a b r
                    else
                      rhsPivot361 X Y Z W a b r
                else
                  if i < 363 then
                    rhsPivot362 X Y Z W a b r
                  else
                    if i < 364 then
                      rhsPivot363 X Y Z W a b r
                    else
                      rhsPivot364 X Y Z W a b r
              else
                if i < 368 then
                  if i < 366 then
                    rhsPivot365 X Y Z W a b r
                  else
                    if i < 367 then
                      rhsPivot366 X Y Z W a b r
                    else
                      rhsPivot367 X Y Z W a b r
                else
                  if i < 370 then
                    if i < 369 then
                      rhsPivot368 X Y Z W a b r
                    else
                      rhsPivot369 X Y Z W a b r
                  else
                    if i < 371 then
                      rhsPivot370 X Y Z W a b r
                    else
                      rhsPivot371 X Y Z W a b r
            else
              if i < 378 then
                if i < 375 then
                  if i < 373 then
                    rhsPivot372 X Y Z W a b r
                  else
                    if i < 374 then
                      rhsPivot373 X Y Z W a b r
                    else
                      rhsPivot374 X Y Z W a b r
                else
                  if i < 376 then
                    rhsPivot375 X Y Z W a b r
                  else
                    if i < 377 then
                      rhsPivot376 X Y Z W a b r
                    else
                      rhsPivot377 X Y Z W a b r
              else
                if i < 381 then
                  if i < 379 then
                    rhsPivot378 X Y Z W a b r
                  else
                    if i < 380 then
                      rhsPivot379 X Y Z W a b r
                    else
                      rhsPivot380 X Y Z W a b r
                else
                  if i < 383 then
                    if i < 382 then
                      rhsPivot381 X Y Z W a b r
                    else
                      rhsPivot382 X Y Z W a b r
                  else
                    if i < 384 then
                      rhsPivot383 X Y Z W a b r
                    else
                      rhsPivot384 X Y Z W a b r
          else
            if i < 398 then
              if i < 391 then
                if i < 388 then
                  if i < 386 then
                    rhsPivot385 X Y Z W a b r
                  else
                    if i < 387 then
                      rhsPivot386 X Y Z W a b r
                    else
                      rhsPivot387 X Y Z W a b r
                else
                  if i < 389 then
                    rhsPivot388 X Y Z W a b r
                  else
                    if i < 390 then
                      rhsPivot389 X Y Z W a b r
                    else
                      rhsPivot390 X Y Z W a b r
              else
                if i < 394 then
                  if i < 392 then
                    rhsPivot391 X Y Z W a b r
                  else
                    if i < 393 then
                      rhsPivot392 X Y Z W a b r
                    else
                      rhsPivot393 X Y Z W a b r
                else
                  if i < 396 then
                    if i < 395 then
                      rhsPivot394 X Y Z W a b r
                    else
                      rhsPivot395 X Y Z W a b r
                  else
                    if i < 397 then
                      rhsPivot396 X Y Z W a b r
                    else
                      rhsPivot397 X Y Z W a b r
            else
              if i < 404 then
                if i < 401 then
                  if i < 399 then
                    rhsPivot398 X Y Z W a b r
                  else
                    if i < 400 then
                      rhsPivot399 X Y Z W a b r
                    else
                      rhsPivot400 X Y Z W a b r
                else
                  if i < 402 then
                    rhsPivot401 X Y Z W a b r
                  else
                    if i < 403 then
                      rhsPivot402 X Y Z W a b r
                    else
                      rhsPivot403 X Y Z W a b r
              else
                if i < 407 then
                  if i < 405 then
                    rhsPivot404 X Y Z W a b r
                  else
                    if i < 406 then
                      rhsPivot405 X Y Z W a b r
                    else
                      rhsPivot406 X Y Z W a b r
                else
                  if i < 409 then
                    if i < 408 then
                      rhsPivot407 X Y Z W a b r
                    else
                      rhsPivot408 X Y Z W a b r
                  else
                    if i < 410 then
                      rhsPivot409 X Y Z W a b r
                    else
                      rhsPivot410 X Y Z W a b r
  else 0
theorem before (i : Fin 411) :
    (instructions i.val).all (fun t => decide (t.2 < 546+i.val))=true := by
  fin_cases i <;> rfl
#print axioms before
theorem recurrence (X Y Z W a b : ℂ) (r : Fin 546 → ℂ) (i : Fin 411) :
    rows X Y Z W a b i.val r = ((instructions i.val).map fun t =>
      t.1.eval ![X,Y,Z,W,a,b] * (if t.2<546 then r (Fin.ofNat 546 t.2)
        else rows X Y Z W a b (t.2-546) r)).sum := by
  fin_cases i
  · change rhsPivot0 X Y Z W a b r = ((1:ℚ):ℂ)*(r 19) + ((0:ℂ))
    unfold rhsPivot0
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot1 X Y Z W a b r = ((1:ℚ):ℂ)*(r 47) + ((0:ℂ))
    unfold rhsPivot1
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot2 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(W^2))*(r 59) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*X⁻¹)*(W^2)))*(rhsPivot0 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot2
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot3 X Y Z W a b r = ((1:ℚ):ℂ)*(r 10) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot2 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot3
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot4 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 4) + (((1:ℚ):ℂ)*(rhsPivot3 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot4
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot5 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 22) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot3 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot5
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot6 X Y Z W a b r = ((1:ℚ):ℂ)*(r 26) + ((-Z)*(rhsPivot2 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot6
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot7 X Y Z W a b r = ((1:ℚ):ℂ)*(r 28) + ((-(((Y⁻¹^2)*Z⁻¹)*(W⁻¹^2)))*(rhsPivot6 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot7
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot8 X Y Z W a b r = (((-1:ℚ):ℂ)*(W⁻¹^2))*(r 40) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot3 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot8
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot9 X Y Z W a b r = (((-1:ℚ):ℂ)*X)*(r 44) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot2 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot9
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot10 X Y Z W a b r = Z*(r 27) + ((((-1:ℚ):ℂ)*Z)*(rhsPivot9 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot10
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot11 X Y Z W a b r = ((1:ℚ):ℂ)*(r 7) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot10 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot11
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot12 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 1) + (((1:ℚ):ℂ)*(rhsPivot11 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot12
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot13 X Y Z W a b r = Z⁻¹*(r 25) + ((((-1:ℚ):ℂ)*Z⁻¹)*(rhsPivot10 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot13
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot14 X Y Z W a b r = ((1:ℚ):ℂ)*(r 29) + ((-(Z*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot13 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot14
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot15 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 33) + (((1:ℚ):ℂ)*(rhsPivot9 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot15
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot16 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*X)*(r 51) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*X))*(rhsPivot5 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot16
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot17 X Y Z W a b r = ((1:ℚ):ℂ)*(r 60) + ((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*(rhsPivot13 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot17
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot18 X Y Z W a b r = ((1:ℚ):ℂ)*(r 62) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*(rhsPivot9 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot18
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot19 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*X)*(r 23) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(Y⁻¹^2))*X))*(rhsPivot18 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot19
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot20 X Y Z W a b r = ((1:ℚ):ℂ)*(r 76) + ((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*(rhsPivot15 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot20
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot21 X Y Z W a b r = ((1:ℚ):ℂ)*(r 79) + ((-((((-1:ℚ):ℂ)*(W^2))*(Y⁻¹^2)))*(rhsPivot16 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot21
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot22 X Y Z W a b r = (((-1:ℚ):ℂ)*(W⁻¹^2))*(r 31) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot21 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot22
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot23 X Y Z W a b r = ((1:ℚ):ℂ)*(r 81) + ((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot13 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot23
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot24 X Y Z W a b r = ((1:ℚ):ℂ)*(r 88) + ((0:ℂ))
    unfold rhsPivot24
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot25 X Y Z W a b r = ((1:ℚ):ℂ)*(r 101) + ((-((((-1:ℚ):ℂ)*X)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot2 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot25
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot26 X Y Z W a b r = ((1:ℚ):ℂ)*(r 95) + ((-((((-1:ℚ):ℂ)*(Y^2))*X⁻¹))*(rhsPivot25 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot26
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot27 X Y Z W a b r = ((1:ℚ):ℂ)*(r 74) + ((-((((-1:ℚ):ℂ)*X)*(W^2)))*(rhsPivot26 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot27
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot28 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2))*(r 100) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot27 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot28
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot29 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2))*(r 104) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot15 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot29
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot30 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(r 105) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2)))*(rhsPivot8 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot30
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot31 X Y Z W a b r = (((Y⁻¹^2)*Z⁻¹)*X)*(r 110) + ((((-1:ℚ):ℂ)*(((Y⁻¹^2)*Z⁻¹)*X))*(rhsPivot6 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot31
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot32 X Y Z W a b r = ((1:ℚ):ℂ)*(r 111) + ((-(((X⁻¹*(Y⁻¹^2))*Z⁻¹)*(W⁻¹^2)))*(rhsPivot10 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot32
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot33 X Y Z W a b r = ((1:ℚ):ℂ)*(r 112) + ((-(X*(((Y⁻¹^2)*Z⁻¹)*(W⁻¹^2))))*(rhsPivot6 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot33
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot34 X Y Z W a b r = ((1:ℚ):ℂ)*(r 113) + ((-((X⁻¹*Z⁻¹)*(W⁻¹^2)))*(rhsPivot10 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot34
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot35 X Y Z W a b r = ((1:ℚ):ℂ)*(r 114) + ((-((X⁻¹*(Y⁻¹^2))*Z⁻¹))*(rhsPivot10 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot35
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot36 X Y Z W a b r = ((1:ℚ):ℂ)*(r 115) + ((-(X*(Z⁻¹*(W⁻¹^2))))*(rhsPivot6 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot36
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot37 X Y Z W a b r = ((Z⁻¹*(W⁻¹^2))*(X*(Y^2)))*(r 123) + ((((-1:ℚ):ℂ)*((Z⁻¹*(W⁻¹^2))*(X*(Y^2))))*(rhsPivot12 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot37
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot38 X Y Z W a b r = ((1:ℚ):ℂ)*(r 127) + ((-((Y^2)*(Z⁻¹*(W⁻¹^2))))*(rhsPivot12 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot38
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot39 X Y Z W a b r = ((Z⁻¹*(W⁻¹^2))*(Y^2))*(r 129) + ((((-1:ℚ):ℂ)*((Z⁻¹*(W⁻¹^2))*(Y^2)))*(rhsPivot11 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot39
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot40 X Y Z W a b r = ((1:ℚ):ℂ)*(r 148) + ((-((((-1:ℚ):ℂ)*X)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot6 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot40
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot41 X Y Z W a b r = ((1:ℚ):ℂ)*(r 149) + ((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*(rhsPivot13 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot41
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot42 X Y Z W a b r = ((1:ℚ):ℂ)*(r 150) + ((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*(rhsPivot3 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot42
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot43 X Y Z W a b r = ((1:ℚ):ℂ)*(r 155) + ((-((((-1:ℚ):ℂ)*X)*(Y⁻¹^2)))*(rhsPivot2 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot43
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot44 X Y Z W a b r = ((1:ℚ):ℂ)*(r 50) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot43 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot44
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot45 X Y Z W a b r = ((1:ℚ):ℂ)*(r 133) + ((-(((((-1:ℚ):ℂ)*X)*(Y^2))*(W⁻¹^2)))*(rhsPivot44 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot45
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot46 X Y Z W a b r = ((1:ℚ):ℂ)*(r 156) + ((-(((((-1:ℚ):ℂ)*X)*(Y^2))*(W⁻¹^2)))*(rhsPivot35 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot46
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot47 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2))*(r 172) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot1 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot47
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot48 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2))*(r 176) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot15 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot48
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot49 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2))*(r 179) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot44 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot49
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot50 X Y Z W a b r = ((1:ℚ):ℂ)*(r 180) + ((-(((Y⁻¹^2)*Z⁻¹)*(W⁻¹^2)))*(rhsPivot10 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot50
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot51 X Y Z W a b r = ((1:ℚ):ℂ)*(r 181) + ((-(((Y⁻¹^2)*Z⁻¹)*(W⁻¹^2)))*(rhsPivot10 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot51
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot52 X Y Z W a b r = ((1:ℚ):ℂ)*(r 184) + ((-(X*(((Y⁻¹^2)*Z⁻¹)*(W⁻¹^2))))*(rhsPivot6 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot52
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot53 X Y Z W a b r = ((1:ℚ):ℂ)*(r 185) + ((-(((X⁻¹*(Y⁻¹^2))*Z⁻¹)*(W⁻¹^2)))*(rhsPivot10 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot53
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot54 X Y Z W a b r = (((-1:ℚ):ℂ)*(W⁻¹^2))*(r 0) + ((0:ℂ))
    unfold rhsPivot54
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot55 X Y Z W a b r = ((1:ℚ):ℂ)*(r 2) + ((0:ℂ))
    unfold rhsPivot55
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot56 X Y Z W a b r = ((1:ℚ):ℂ)*(r 3) + ((0:ℂ))
    unfold rhsPivot56
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot57 X Y Z W a b r = (((-1:ℚ):ℂ)*(W⁻¹^2))*(r 5) + ((0:ℂ))
    unfold rhsPivot57
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot58 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*X)*(r 6) + ((0:ℂ))
    unfold rhsPivot58
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot59 X Y Z W a b r = ((1:ℚ):ℂ)*(r 8) + ((0:ℂ))
    unfold rhsPivot59
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot60 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*(X*(W^2)))*(r 9) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(Y⁻¹^2))*(X*(W^2))))*(rhsPivot55 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot60
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot61 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(W⁻¹^2))*(r 11) + ((0:ℂ))
    unfold rhsPivot61
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot62 X Y Z W a b r = ((1:ℚ):ℂ)*(r 12) + ((-(((((-1:ℚ):ℂ)*X)*(W^2))*(Y⁻¹^2)))*(rhsPivot55 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot62
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot63 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(r 13) + ((0:ℂ))
    unfold rhsPivot63
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot64 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*X)*(r 14) + ((0:ℂ))
    unfold rhsPivot64
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot65 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 15) + ((0:ℂ))
    unfold rhsPivot65
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot66 X Y Z W a b r = ((1:ℚ):ℂ)*(r 16) + ((0:ℂ))
    unfold rhsPivot66
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot67 X Y Z W a b r = ((1:ℚ):ℂ)*(r 17) + ((0:ℂ))
    unfold rhsPivot67
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot68 X Y Z W a b r = ((1:ℚ):ℂ)*(r 18) + ((0:ℂ))
    unfold rhsPivot68
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot69 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(Y^2))*(r 20) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*X⁻¹)*(Y^2)))*(rhsPivot59 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot69
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot70 X Y Z W a b r = (((-1:ℚ):ℂ)*X)*(r 21) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot55 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot70
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot71 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(r 24) + ((0:ℂ))
    unfold rhsPivot71
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot72 X Y Z W a b r = (((Y⁻¹^2)*(W⁻¹^2))*Z)*(r 30) + ((0:ℂ))
    unfold rhsPivot72
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot73 X Y Z W a b r = ((1:ℚ):ℂ)*(r 32) + ((0:ℂ))
    unfold rhsPivot73
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot74 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 34) + ((0:ℂ))
    unfold rhsPivot74
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot75 X Y Z W a b r = ((1:ℚ):ℂ)*(r 35) + ((0:ℂ))
    unfold rhsPivot75
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot76 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*X)*(r 36) + ((0:ℂ))
    unfold rhsPivot76
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot77 X Y Z W a b r = ((1:ℚ):ℂ)*(r 37) + ((-((((-1:ℚ):ℂ)*X)*(W^2)))*(rhsPivot55 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot77
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot78 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*X)*(r 38) + (((-(((((-1:ℚ):ℂ)*(Y^2))*(W^2))*X⁻¹))*((((-1:ℚ):ℂ)*(Y⁻¹^2))*X))*(rhsPivot56 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot78
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot79 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(W⁻¹^2))*(r 39) + ((0:ℂ))
    unfold rhsPivot79
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot80 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(W⁻¹^2))*(r 41) + ((0:ℂ))
    unfold rhsPivot80
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot81 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*X)*(r 42) + ((0:ℂ))
    unfold rhsPivot81
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot82 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 43) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot60 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot82
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot83 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(W^2))*(r 45) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*X⁻¹)*(W^2)))*(rhsPivot58 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot83
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot84 X Y Z W a b r = ((1:ℚ):ℂ)*(r 46) + ((0:ℂ))
    unfold rhsPivot84
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot85 X Y Z W a b r = ((1:ℚ):ℂ)*(r 48) + ((0:ℂ))
    unfold rhsPivot85
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot86 X Y Z W a b r = ((1:ℚ):ℂ)*(r 49) + ((0:ℂ))
    unfold rhsPivot86
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot87 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(W⁻¹^2))*(Y^2))*(r 52) + ((0:ℂ))
    unfold rhsPivot87
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot88 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*X)*(r 53) + ((0:ℂ))
    unfold rhsPivot88
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot89 X Y Z W a b r = ((1:ℚ):ℂ)*(r 54) + ((0:ℂ))
    unfold rhsPivot89
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot90 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(W^2))*(r 55) + ((0:ℂ))
    unfold rhsPivot90
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot91 X Y Z W a b r = (((-1:ℚ):ℂ)*X)*(r 56) + ((0:ℂ))
    unfold rhsPivot91
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot92 X Y Z W a b r = ((1:ℚ):ℂ)*(r 57) + ((0:ℂ))
    unfold rhsPivot92
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot93 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*(X*(W^2)))*(r 58) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(Y⁻¹^2))*(X*(W^2))))*(rhsPivot66 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot93
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot94 X Y Z W a b r = ((1:ℚ):ℂ)*(r 61) + ((0:ℂ))
    unfold rhsPivot94
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot95 X Y Z W a b r = ((1:ℚ):ℂ)*(r 63) + ((0:ℂ))
    unfold rhsPivot95
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot96 X Y Z W a b r = ((1:ℚ):ℂ)*(r 64) + ((0:ℂ))
    unfold rhsPivot96
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot97 X Y Z W a b r = ((1:ℚ):ℂ)*(r 65) + ((0:ℂ))
    unfold rhsPivot97
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot98 X Y Z W a b r = ((1:ℚ):ℂ)*(r 66) + ((0:ℂ))
    unfold rhsPivot98
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot99 X Y Z W a b r = ((1:ℚ):ℂ)*(r 67) + ((0:ℂ))
    unfold rhsPivot99
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot100 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(W^2))*(r 68) + ((0:ℂ))
    unfold rhsPivot100
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot101 X Y Z W a b r = ((1:ℚ):ℂ)*(r 69) + ((0:ℂ))
    unfold rhsPivot101
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot102 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 70) + ((0:ℂ))
    unfold rhsPivot102
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot103 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(W⁻¹^2))*(Y^2))*(r 71) + ((0:ℂ))
    unfold rhsPivot103
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot104 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*X)*(r 72) + ((0:ℂ))
    unfold rhsPivot104
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot105 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(r 73) + ((0:ℂ))
    unfold rhsPivot105
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot106 X Y Z W a b r = (((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2))*X)*(r 75) + ((0:ℂ))
    unfold rhsPivot106
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot107 X Y Z W a b r = ((1:ℚ):ℂ)*(r 77) + ((0:ℂ))
    unfold rhsPivot107
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot108 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2))*(r 78) + ((0:ℂ))
    unfold rhsPivot108
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot109 X Y Z W a b r = ((1:ℚ):ℂ)*(r 80) + ((-((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2)))*(rhsPivot88 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot109
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot110 X Y Z W a b r = ((1:ℚ):ℂ)*(r 82) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot102 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot110
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot111 X Y Z W a b r = ((1:ℚ):ℂ)*(r 83) + ((-(((-1:ℚ):ℂ)*(W^2)))*(rhsPivot79 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot111
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot112 X Y Z W a b r = ((1:ℚ):ℂ)*(r 84) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot95 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot112
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot113 X Y Z W a b r = ((1:ℚ):ℂ)*(r 85) + ((-(((X*(Y^2))*Z)*(W⁻¹^2)))*(rhsPivot82 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot113
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot114 X Y Z W a b r = ((1:ℚ):ℂ)*(r 86) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot110 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot114
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot115 X Y Z W a b r = (X*(Y^2))*(r 87) + (((-(((-1:ℚ):ℂ)*X⁻¹))*(X*(Y^2)))*(rhsPivot73 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(X*(Y^2)))*(rhsPivot75 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot115
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot116 X Y Z W a b r = ((1:ℚ):ℂ)*(r 89) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot109 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot116
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot117 X Y Z W a b r = ((1:ℚ):ℂ)*(r 90) + ((-(Z*(W^2)))*(rhsPivot59 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot117
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot118 X Y Z W a b r = ((1:ℚ):ℂ)*(r 91) + ((-Z)*(rhsPivot88 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot118
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot119 X Y Z W a b r = ((W⁻¹^2)*Z)*(r 92) + ((0:ℂ))
    unfold rhsPivot119
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot120 X Y Z W a b r = ((1:ℚ):ℂ)*(r 93) + ((-(Z*(W⁻¹^2)))*(rhsPivot91 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot120
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot121 X Y Z W a b r = ((Y^2)*(W^2))*(r 94) + ((((-1:ℚ):ℂ)*((Y^2)*(W^2)))*(rhsPivot108 X Y Z W a b r) + (((-(Z⁻¹*(W⁻¹^2)))*((Y^2)*(W^2)))*(rhsPivot118 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot121
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot122 X Y Z W a b r = ((1:ℚ):ℂ)*(r 96) + ((0:ℂ))
    unfold rhsPivot122
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot123 X Y Z W a b r = ((1:ℚ):ℂ)*(r 97) + ((-((((-1:ℚ):ℂ)*X)*(Y⁻¹^2)))*(rhsPivot74 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(rhsPivot114 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot123
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot124 X Y Z W a b r = ((1:ℚ):ℂ)*(r 98) + ((0:ℂ))
    unfold rhsPivot124
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot125 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(r 99) + ((0:ℂ))
    unfold rhsPivot125
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot126 X Y Z W a b r = X*(r 102) + ((((-1:ℚ):ℂ)*X)*(rhsPivot66 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*(Y^2))*X⁻¹))*X)*(rhsPivot106 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot126
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot127 X Y Z W a b r = (X*(Y^2))*(r 103) + ((((-1:ℚ):ℂ)*(X*(Y^2)))*(rhsPivot68 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(X*(Y^2)))*(rhsPivot104 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot127
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot128 X Y Z W a b r = ((1:ℚ):ℂ)*(r 106) + ((-(Z*(W⁻¹^2)))*(rhsPivot60 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot128
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot129 X Y Z W a b r = ((Y⁻¹^2)*Z⁻¹)*(r 107) + ((0:ℂ))
    unfold rhsPivot129
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot130 X Y Z W a b r = ((Y^2)*Z)*(r 108) + ((((-1:ℚ):ℂ)*((Y^2)*Z))*(rhsPivot79 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot130
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot131 X Y Z W a b r = ((1:ℚ):ℂ)*(r 109) + ((-(((((-1:ℚ):ℂ)*(Y^2))*(W^2))*X⁻¹))*(rhsPivot73 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot131
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot132 X Y Z W a b r = ((1:ℚ):ℂ)*(r 116) + ((0:ℂ))
    unfold rhsPivot132
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot133 X Y Z W a b r = ((1:ℚ):ℂ)*(r 117) + ((-((X*Z)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot83 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot133
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot134 X Y Z W a b r = ((1:ℚ):ℂ)*(r 118) + ((0:ℂ))
    unfold rhsPivot134
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot135 X Y Z W a b r = ((X⁻¹*(W⁻¹^2))*Z)*(r 119) + ((0:ℂ))
    unfold rhsPivot135
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot136 X Y Z W a b r = (((Y⁻¹^2)*Z⁻¹)*(X*(W^2)))*(r 120) + ((0:ℂ))
    unfold rhsPivot136
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot137 X Y Z W a b r = ((1:ℚ):ℂ)*(r 121) + ((-(((Y^2)*(W^2))*(X⁻¹*Z⁻¹)))*(rhsPivot128 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot137
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot138 X Y Z W a b r = (((X⁻¹*(Y⁻¹^2))*Z⁻¹)*(W^2))*(r 122) + ((0:ℂ))
    unfold rhsPivot138
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot139 X Y Z W a b r = ((1:ℚ):ℂ)*(r 124) + ((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot99 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot139
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot140 X Y Z W a b r = ((1:ℚ):ℂ)*(r 125) + ((0:ℂ))
    unfold rhsPivot140
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot141 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(r 126) + (((-((((-1:ℚ):ℂ)*(Y^2))*(W^2)))*((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2)))*(rhsPivot86 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot141
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot142 X Y Z W a b r = ((1:ℚ):ℂ)*(r 128) + ((-((W^2)*((Y⁻¹^2)*Z⁻¹)))*(rhsPivot135 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot142
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot143 X Y Z W a b r = ((W⁻¹^2)*Z)*(r 130) + (((-((((-1:ℚ):ℂ)*X)*(Y^2)))*((W⁻¹^2)*Z))*(rhsPivot138 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot143
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot144 X Y Z W a b r = ((1:ℚ):ℂ)*(r 131) + ((0:ℂ))
    unfold rhsPivot144
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot145 X Y Z W a b r = ((1:ℚ):ℂ)*(r 132) + ((-((((-1:ℚ):ℂ)*(W^2))*(X⁻¹*(Y⁻¹^2))))*(rhsPivot58 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot145
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot146 X Y Z W a b r = ((1:ℚ):ℂ)*(r 134) + ((0:ℂ))
    unfold rhsPivot146
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot147 X Y Z W a b r = ((1:ℚ):ℂ)*(r 135) + ((0:ℂ))
    unfold rhsPivot147
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot148 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(W^2))*(r 136) + ((0:ℂ))
    unfold rhsPivot148
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot149 X Y Z W a b r = ((1:ℚ):ℂ)*(r 137) + ((0:ℂ))
    unfold rhsPivot149
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot150 X Y Z W a b r = ((1:ℚ):ℂ)*(r 138) + ((0:ℂ))
    unfold rhsPivot150
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot151 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(W⁻¹^2))*(Y^2))*(r 139) + ((0:ℂ))
    unfold rhsPivot151
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot152 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*X)*(r 140) + ((0:ℂ))
    unfold rhsPivot152
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot153 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(W⁻¹^2))*(Y^2))*(r 141) + ((0:ℂ))
    unfold rhsPivot153
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot154 X Y Z W a b r = ((1:ℚ):ℂ)*(r 142) + ((0:ℂ))
    unfold rhsPivot154
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot155 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(W^2))*(r 143) + ((0:ℂ))
    unfold rhsPivot155
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot156 X Y Z W a b r = ((1:ℚ):ℂ)*(r 144) + ((0:ℂ))
    unfold rhsPivot156
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot157 X Y Z W a b r = ((1:ℚ):ℂ)*(r 145) + ((-((((-1:ℚ):ℂ)*(Y^2))*(X⁻¹*(W⁻¹^2))))*(rhsPivot92 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot157
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot158 X Y Z W a b r = ((1:ℚ):ℂ)*(r 146) + ((-((((-1:ℚ):ℂ)*X)*(W⁻¹^2)))*(rhsPivot99 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot158
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot159 X Y Z W a b r = ((1:ℚ):ℂ)*(r 147) + ((0:ℂ))
    unfold rhsPivot159
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot160 X Y Z W a b r = ((1:ℚ):ℂ)*(r 151) + ((0:ℂ))
    unfold rhsPivot160
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot161 X Y Z W a b r = ((1:ℚ):ℂ)*(r 152) + ((0:ℂ))
    unfold rhsPivot161
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot162 X Y Z W a b r = ((1:ℚ):ℂ)*(r 153) + ((0:ℂ))
    unfold rhsPivot162
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot163 X Y Z W a b r = ((1:ℚ):ℂ)*(r 154) + ((-((((-1:ℚ):ℂ)*(Y^2))*(X⁻¹*(W⁻¹^2))))*(rhsPivot60 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot163
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot164 X Y Z W a b r = ((1:ℚ):ℂ)*(r 157) + ((-(((((-1:ℚ):ℂ)*X)*(W^2))*(Y⁻¹^2)))*(rhsPivot65 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot164
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot165 X Y Z W a b r = ((W⁻¹^2)*Z)*(r 158) + (((-((((-1:ℚ):ℂ)*X)*(Y^2)))*((W⁻¹^2)*Z))*(rhsPivot132 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot165
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot166 X Y Z W a b r = ((((-1:ℚ):ℂ)*X⁻¹)*(W⁻¹^2))*(r 159) + ((0:ℂ))
    unfold rhsPivot166
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot167 X Y Z W a b r = (((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2))*X)*(r 160) + ((0:ℂ))
    unfold rhsPivot167
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot168 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 161) + ((0:ℂ))
    unfold rhsPivot168
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot169 X Y Z W a b r = ((1:ℚ):ℂ)*(r 162) + ((0:ℂ))
    unfold rhsPivot169
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot170 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2))*(r 163) + ((0:ℂ))
    unfold rhsPivot170
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot171 X Y Z W a b r = X*(r 164) + (((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*X)*(rhsPivot121 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot168 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot171
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot172 X Y Z W a b r = ((1:ℚ):ℂ)*(r 165) + ((0:ℂ))
    unfold rhsPivot172
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot173 X Y Z W a b r = ((1:ℚ):ℂ)*(r 166) + ((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*(rhsPivot150 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot173
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot174 X Y Z W a b r = ((1:ℚ):ℂ)*(r 167) + ((0:ℂ))
    unfold rhsPivot174
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot175 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2))*(r 168) + ((0:ℂ))
    unfold rhsPivot175
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot176 X Y Z W a b r = ((1:ℚ):ℂ)*(r 169) + ((0:ℂ))
    unfold rhsPivot176
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot177 X Y Z W a b r = ((1:ℚ):ℂ)*(r 170) + ((0:ℂ))
    unfold rhsPivot177
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot178 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2))*(r 171) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot150 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot178
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot179 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*(Y⁻¹^2))*(W⁻¹^2))*(r 173) + ((0:ℂ))
    unfold rhsPivot179
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot180 X Y Z W a b r = ((1:ℚ):ℂ)*(r 174) + ((0:ℂ))
    unfold rhsPivot180
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot181 X Y Z W a b r = ((1:ℚ):ℂ)*(r 175) + ((0:ℂ))
    unfold rhsPivot181
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot182 X Y Z W a b r = ((1:ℚ):ℂ)*(r 177) + ((0:ℂ))
    unfold rhsPivot182
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot183 X Y Z W a b r = ((1:ℚ):ℂ)*(r 178) + ((0:ℂ))
    unfold rhsPivot183
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot184 X Y Z W a b r = ((((-1:ℚ):ℂ)*(Y⁻¹^2))*X)*(r 182) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(Y⁻¹^2))*X))*(rhsPivot163 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot184
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot185 X Y Z W a b r = ((1:ℚ):ℂ)*(r 183) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot70 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot185
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot186 X Y Z W a b r = ((1:ℚ):ℂ)*(r 186) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*(rhsPivot93 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot126 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot186
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot187 X Y Z W a b r = ((1:ℚ):ℂ)*(r 187) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot64 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot187
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot188 X Y Z W a b r = (((-1:ℚ):ℂ)*(Y⁻¹^2))*(r 188) + ((0:ℂ))
    unfold rhsPivot188
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot189 X Y Z W a b r = (((((-1:ℚ):ℂ)*X⁻¹)*Z⁻¹)*(Y^2))*(r 189) + ((((-1:ℚ):ℂ)*(((((-1:ℚ):ℂ)*X⁻¹)*Z⁻¹)*(Y^2)))*(rhsPivot117 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((((-1:ℚ):ℂ)*X⁻¹)*Z⁻¹)*(Y^2)))*(rhsPivot118 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot189
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot190 X Y Z W a b r = ((1:ℚ):ℂ)*(r 192) + ((-(X*(Z⁻¹*(W⁻¹^2))))*(rhsPivot6 X Y Z W a b r) + ((-(X*(Z⁻¹*(W⁻¹^2))))*(rhsPivot12 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot190
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot191 X Y Z W a b r = ((1:ℚ):ℂ)*(r 193) + ((-(X*(Z⁻¹*(W⁻¹^2))))*(rhsPivot6 X Y Z W a b r) + ((-(X*(Z⁻¹*(W⁻¹^2))))*(rhsPivot11 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot191
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot192 X Y Z W a b r = ((1:ℚ):ℂ)*(r 196) + ((-(X*Z⁻¹))*(rhsPivot6 X Y Z W a b r) + ((-(X*Z⁻¹))*(rhsPivot11 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot192
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot193 X Y Z W a b r = ((1:ℚ):ℂ)*(r 197) + ((-(X*Z⁻¹))*(rhsPivot6 X Y Z W a b r) + ((-(X*Z⁻¹))*(rhsPivot12 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot193
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot194 X Y Z W a b r = ((Y^2)*(W^2))*(r 259) + ((((-1:ℚ):ℂ)*((Y^2)*(W^2)))*(rhsPivot33 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((Y^2)*(W^2)))*(rhsPivot185 X Y Z W a b r) + (((-X⁻¹)*((Y^2)*(W^2)))*(rhsPivot187 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot194
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot195 X Y Z W a b r = ((((-1:ℚ):ℂ)*Z⁻¹)*(W^2))*(r 202) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot113 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot120 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot143 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot165 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*Z)*(W⁻¹^2)))*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot194 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot195
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot196 X Y Z W a b r = ((Y^2)*(W^2))*(r 262) + (((-X⁻¹)*((Y^2)*(W^2)))*(rhsPivot19 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((Y^2)*(W^2)))*(rhsPivot140 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((Y^2)*(W^2)))*(rhsPivot175 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot196
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot197 X Y Z W a b r = X*(r 264) + ((((-1:ℚ):ℂ)*X)*(rhsPivot23 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot183 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot197
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot198 X Y Z W a b r = (W^2)*(r 268) + ((((-1:ℚ):ℂ)*(W^2))*(rhsPivot8 X Y Z W a b r) + (((-X⁻¹)*(W^2))*(rhsPivot127 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(W^2))*(rhsPivot146 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot198
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot199 X Y Z W a b r = X*(r 275) + ((((-1:ℚ):ℂ)*X)*(rhsPivot38 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot199
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot200 X Y Z W a b r = ((1:ℚ):ℂ)*(r 283) + ((-X⁻¹)*(rhsPivot0 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot200
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot201 X Y Z W a b r = ((1:ℚ):ℂ)*(r 310) + (((-1:ℚ):ℂ)*(rhsPivot0 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot201
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot202 X Y Z W a b r = ((1:ℚ):ℂ)*(r 316) + (((-1:ℚ):ℂ)*(rhsPivot3 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot195 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot202
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot203 X Y Z W a b r = X*(r 317) + ((((-1:ℚ):ℂ)*X)*(rhsPivot17 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot203
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot204 X Y Z W a b r = X*(r 319) + ((((-1:ℚ):ℂ)*X)*(rhsPivot18 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot204
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot205 X Y Z W a b r = X*(r 320) + ((((-1:ℚ):ℂ)*X)*(rhsPivot95 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot192 X Y Z W a b r) + (X*(rhsPivot195 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot205
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot206 X Y Z W a b r = ((1:ℚ):ℂ)*(r 331) + ((-X⁻¹)*(rhsPivot29 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot206
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot207 X Y Z W a b r = ((1:ℚ):ℂ)*(r 333) + ((-X⁻¹)*(rhsPivot40 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot207
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot208 X Y Z W a b r = ((1:ℚ):ℂ)*(r 334) + ((-X⁻¹)*(rhsPivot27 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot208
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot209 X Y Z W a b r = ((1:ℚ):ℂ)*(r 335) + ((-X⁻¹)*(rhsPivot48 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot209
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot210 X Y Z W a b r = ((1:ℚ):ℂ)*(r 337) + ((-X⁻¹)*(rhsPivot43 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot210
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot211 X Y Z W a b r = ((1:ℚ):ℂ)*(r 338) + ((-X⁻¹)*(rhsPivot45 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot211
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot212 X Y Z W a b r = ((1:ℚ):ℂ)*(r 339) + ((-X⁻¹)*(rhsPivot50 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot212
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot213 X Y Z W a b r = ((1:ℚ):ℂ)*(r 340) + ((-X⁻¹)*(rhsPivot51 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot213
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot214 X Y Z W a b r = ((1:ℚ):ℂ)*(r 341) + ((-X⁻¹)*(rhsPivot46 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot214
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot215 X Y Z W a b r = ((1:ℚ):ℂ)*(r 342) + ((-X⁻¹)*(rhsPivot21 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot215
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot216 X Y Z W a b r = ((1:ℚ):ℂ)*(r 344) + ((-X⁻¹)*(rhsPivot23 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot216
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot217 X Y Z W a b r = ((1:ℚ):ℂ)*(r 345) + ((-X⁻¹)*(rhsPivot14 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot217
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot218 X Y Z W a b r = ((1:ℚ):ℂ)*(r 347) + ((-X⁻¹)*(rhsPivot24 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot218
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot219 X Y Z W a b r = X*(r 360) + ((((-1:ℚ):ℂ)*X)*(rhsPivot105 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot193 X Y Z W a b r) + (((-(X⁻¹*(Y⁻¹^2)))*X)*(rhsPivot195 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot219
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot220 X Y Z W a b r = X*(r 361) + ((((-1:ℚ):ℂ)*X)*(rhsPivot26 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot220
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot221 X Y Z W a b r = X*(r 363) + ((((-1:ℚ):ℂ)*X)*(rhsPivot20 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot221
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot222 X Y Z W a b r = ((1:ℚ):ℂ)*(r 369) + (((-1:ℚ):ℂ)*(rhsPivot16 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot222
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot223 X Y Z W a b r = ((1:ℚ):ℂ)*(r 394) + ((-X⁻¹)*(rhsPivot16 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot223
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot224 X Y Z W a b r = X*(r 401) + ((((-1:ℚ):ℂ)*X)*(rhsPivot39 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot224
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot225 X Y Z W a b r = X*(r 409) + ((((-1:ℚ):ℂ)*X)*(rhsPivot48 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot84 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot225
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot226 X Y Z W a b r = ((1:ℚ):ℂ)*(r 413) + (((-1:ℚ):ℂ)*(rhsPivot52 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot184 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot226
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot227 X Y Z W a b r = ((1:ℚ):ℂ)*(r 430) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot3 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot9 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot15 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot227
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot228 X Y Z W a b r = ((1:ℚ):ℂ)*(r 418) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot38 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot97 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot183 X Y Z W a b r) + ((-(X⁻¹*(W⁻¹^2)))*(rhsPivot227 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot228
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot229 X Y Z W a b r = ((1:ℚ):ℂ)*(r 431) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot18 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot116 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot173 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot189 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot229
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot230 X Y Z W a b r = ((((-1/2):ℚ):ℂ)*(X*(Y^2)))*(r 453) + ((((-1:ℚ):ℂ)*((((-1/2):ℚ):ℂ)*(X*(Y^2))))*(rhsPivot105 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*((((-1/2):ℚ):ℂ)*(X*(Y^2))))*(rhsPivot137 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1/2):ℚ):ℂ)*(X*(Y^2))))*(rhsPivot145 X Y Z W a b r) + (((-((Y⁻¹^2)+((1:ℚ):ℂ)))*((((-1/2):ℚ):ℂ)*(X*(Y^2))))*(rhsPivot194 X Y Z W a b r) + (((-(X⁻¹*(Y⁻¹^2)))*((((-1/2):ℚ):ℂ)*(X*(Y^2))))*(rhsPivot195 X Y Z W a b r) + (((-(Y⁻¹^2))*((((-1/2):ℚ):ℂ)*(X*(Y^2))))*(rhsPivot198 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot230
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot231 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*((Y^2)*Z))*(r 272) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*((Y^2)*Z)))*(rhsPivot62 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*((Y^2)*Z)))*(rhsPivot132 X Y Z W a b r) + (((-X⁻¹)*((((-1:ℚ):ℂ)*(W⁻¹^2))*((Y^2)*Z)))*(rhsPivot134 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*(W^2))*((X⁻¹*(Y⁻¹^2))*Z⁻¹)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*((Y^2)*Z)))*(rhsPivot165 X Y Z W a b r) + (((-(X⁻¹*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*((Y^2)*Z)))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot231
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot232 X Y Z W a b r = ((((-1:ℚ):ℂ)*Z⁻¹)*(X*(W^2)))*(r 289) + (((-X⁻¹)*((((-1:ℚ):ℂ)*Z⁻¹)*(X*(W^2))))*(rhsPivot113 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(X*(W^2))))*(rhsPivot130 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(X*(W^2))))*(rhsPivot143 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*Z)*(W⁻¹^2)))*((((-1:ℚ):ℂ)*Z⁻¹)*(X*(W^2))))*(rhsPivot195 X Y Z W a b r) + (((-(Z*(W⁻¹^2)))*((((-1:ℚ):ℂ)*Z⁻¹)*(X*(W^2))))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot232
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot233 X Y Z W a b r = X*(r 302) + ((((-1:ℚ):ℂ)*X)*(rhsPivot194 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot230 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot233
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot234 X Y Z W a b r = ((1:ℚ):ℂ)*(r 211) + (((-1:ℚ):ℂ)*(rhsPivot130 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot135 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot231 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*Z)*(X⁻¹*(W⁻¹^2))))*(rhsPivot232 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*Z)*(X⁻¹*(W⁻¹^2))))*(rhsPivot233 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot234
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot235 X Y Z W a b r = ((1:ℚ):ℂ)*(r 218) + (((-1:ℚ):ℂ)*(rhsPivot3 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot4 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot9 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot13 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot15 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot27 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot77 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot91 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot121 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot150 X Y Z W a b r) + ((-X)*(rhsPivot189 X Y Z W a b r) + ((-X)*(rhsPivot194 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot195 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot232 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot233 X Y Z W a b r) + ((0:ℂ)))))))))))))))))
    unfold rhsPivot235
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot236 X Y Z W a b r = ((1:ℚ):ℂ)*(r 228) + (((-1:ℚ):ℂ)*(rhsPivot2 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot3 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot4 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot6 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot9 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot10 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot15 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot27 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot77 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot83 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot91 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot99 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot102 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot121 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot131 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot137 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot150 X Y Z W a b r) + (((-2:ℚ):ℂ)*(rhsPivot189 X Y Z W a b r) + (((-3:ℚ):ℂ)*(rhsPivot194 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot195 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot196 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot198 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot202 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot208 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot232 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot233 X Y Z W a b r) + ((-((((2:ℚ):ℂ)*X⁻¹)+((-1:ℚ):ℂ)))*(rhsPivot235 X Y Z W a b r) + ((0:ℂ)))))))))))))))))))))))))))))
    unfold rhsPivot236
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot237 X Y Z W a b r = ((1:ℚ):ℂ)*(r 424) + (((-1:ℚ):ℂ)*(rhsPivot71 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot113 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot130 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot231 X Y Z W a b r) + ((-((Z*a)*((X⁻¹*Y⁻¹)*(W⁻¹^2))))*(rhsPivot232 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot234 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot237
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot238 X Y Z W a b r = ((1:ℚ):ℂ)*(r 433) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot113 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot133 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot143 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot165 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*Z)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot194 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*Z)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot195 X Y Z W a b r) + ((-((Z*((Y⁻¹^2)*(W⁻¹^2)))+((((-1:ℚ):ℂ)*Z)*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot238
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot239 X Y Z W a b r = ((((-1:ℚ):ℂ)*Z⁻¹)*(W^2))*(r 382) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot119 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot237 X Y Z W a b r) + (((-X⁻¹)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot238 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot239
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot240 X Y Z W a b r = ((1:ℚ):ℂ)*(r 400) + ((-X⁻¹)*(rhsPivot119 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot128 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*Z)*(X⁻¹*(W⁻¹^2))))*(rhsPivot239 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot240
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot241 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 443) + (((1:ℚ):ℂ)*(rhsPivot130 X Y Z W a b r) + (((-(Y⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot135 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot217 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*Z)*(X⁻¹*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot232 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*Z)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot233 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*((-1:ℚ):ℂ))*(rhsPivot234 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot240 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot241
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot242 X Y Z W a b r = ((((-1:ℚ):ℂ)*Z⁻¹)*(W^2))*(r 217) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot14 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot40 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot119 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot128 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot133 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot169 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*Z)*((Y⁻¹^2)*(W⁻¹^2))))*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot194 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot238 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*Z)*(W⁻¹^2)))*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot239 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(W^2)))*(rhsPivot241 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot242
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot243 X Y Z W a b r = ((1:ℚ):ℂ)*(r 276) + (((-1:ℚ):ℂ)*(rhsPivot133 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot169 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*Z)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot194 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*Z)*(X⁻¹*(W⁻¹^2))))*(rhsPivot242 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot243
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot244 X Y Z W a b r = ((1:ℚ):ℂ)*(r 238) + (((-1:ℚ):ℂ)*(rhsPivot71 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot72 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*Z)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot83 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot113 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*Z)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot194 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot207 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot217 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot237 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot238 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot240 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot241 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot243 X Y Z W a b r) + ((0:ℂ))))))))))))))
    unfold rhsPivot244
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot245 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 478) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*((-1:ℚ):ℂ))*(rhsPivot26 X Y Z W a b r) + (((-(Y⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot157 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot168 X Y Z W a b r) + (((-X⁻¹)*((-1:ℚ):ℂ))*(rhsPivot171 X Y Z W a b r) + (((-((Y⁻¹^2)*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot189 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot218 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot245
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot246 X Y Z W a b r = ((1:ℚ):ℂ)*(r 479) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot4 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot13 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot27 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot246
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot247 X Y Z W a b r = ((1:ℚ):ℂ)*(r 489) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot39 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot84 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot103 X Y Z W a b r) + ((-(X⁻¹*(W⁻¹^2)))*(rhsPivot246 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot247
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot248 X Y Z W a b r = ((1:ℚ):ℂ)*(r 190) + ((-((X⁻¹*Z⁻¹)*(W⁻¹^2)))*(rhsPivot10 X Y Z W a b r) + ((-((X⁻¹*Z⁻¹)*(W⁻¹^2)))*(rhsPivot118 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot222 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot248
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot249 X Y Z W a b r = ((1:ℚ):ℂ)*(r 191) + ((-((X⁻¹*Z⁻¹)*(W⁻¹^2)))*(rhsPivot10 X Y Z W a b r) + ((-((X⁻¹*Z⁻¹)*(W⁻¹^2)))*(rhsPivot117 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot189 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot201 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot249
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot250 X Y Z W a b r = ((1:ℚ):ℂ)*(r 194) + ((-(X⁻¹*Z⁻¹))*(rhsPivot10 X Y Z W a b r) + ((-(X⁻¹*Z⁻¹))*(rhsPivot117 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(rhsPivot189 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot202 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot250
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot251 X Y Z W a b r = ((1:ℚ):ℂ)*(r 195) + ((-(X⁻¹*Z⁻¹))*(rhsPivot10 X Y Z W a b r) + ((-(X⁻¹*Z⁻¹))*(rhsPivot118 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot198 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot251
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot252 X Y Z W a b r = (Z⁻¹*(X*(Y^2)))*(r 198) + (((-(Z*(X⁻¹*(W⁻¹^2))))*(Z⁻¹*(X*(Y^2))))*(rhsPivot164 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Z⁻¹*(X*(Y^2))))*(rhsPivot231 X Y Z W a b r) + (((-(Z*(X⁻¹*(W⁻¹^2))))*(Z⁻¹*(X*(Y^2))))*(rhsPivot235 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Z⁻¹*(X*(Y^2))))*(rhsPivot237 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot252
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot253 X Y Z W a b r = (Z⁻¹*(Y^2))*(r 199) + (((-(Z*(X⁻¹*(W⁻¹^2))))*(Z⁻¹*(Y^2)))*(rhsPivot144 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Z⁻¹*(Y^2)))*(rhsPivot234 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Z⁻¹*(Y^2)))*(rhsPivot244 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot253
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot254 X Y Z W a b r = ((1:ℚ):ℂ)*(r 200) + (((-1:ℚ):ℂ)*(rhsPivot131 X Y Z W a b r) + ((-((W^2)*(X⁻¹*Z⁻¹)))*(rhsPivot143 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot195 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot230 X Y Z W a b r) + ((-((W^2)*(X⁻¹*Z⁻¹)))*(rhsPivot241 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot254
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot255 X Y Z W a b r = ((1:ℚ):ℂ)*(r 201) + ((-((W^2)*(X⁻¹*Z⁻¹)))*(rhsPivot165 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot230 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot236 X Y Z W a b r) + ((-((W^2)*(X⁻¹*Z⁻¹)))*(rhsPivot238 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot255
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot256 X Y Z W a b r = (X*(W^2))*(r 260) + (((-X⁻¹)*(X*(W^2)))*(rhsPivot140 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(X*(W^2)))*(rhsPivot174 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(X*(W^2)))*(rhsPivot187 X Y Z W a b r) + (((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(X*(W^2)))*(rhsPivot194 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot256
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot257 X Y Z W a b r = ((Y^2)*(W^2))*(r 261) + ((((-1:ℚ):ℂ)*((Y^2)*(W^2)))*(rhsPivot81 X Y Z W a b r) + (((-(X*(W⁻¹^2)))*((Y^2)*(W^2)))*(rhsPivot111 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((Y^2)*(W^2)))*(rhsPivot139 X Y Z W a b r) + (((-X⁻¹)*((Y^2)*(W^2)))*(rhsPivot171 X Y Z W a b r) + (((-((Y⁻¹^2)*(W⁻¹^2)))*((Y^2)*(W^2)))*(rhsPivot232 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot257
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot258 X Y Z W a b r = ((1:ℚ):ℂ)*(r 207) + ((-((Y^2)*(X⁻¹*Z⁻¹)))*(rhsPivot14 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot26 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*Z⁻¹)))*(rhsPivot117 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*Z⁻¹)))*(rhsPivot169 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot189 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot223 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot236 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*Z⁻¹)))*(rhsPivot238 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*(X⁻¹*(W⁻¹^2))))*(rhsPivot242 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*X⁻¹))*(rhsPivot256 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot257 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot258
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot259 X Y Z W a b r = ((1:ℚ):ℂ)*(r 208) + (((-1:ℚ):ℂ)*(rhsPivot18 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*Z⁻¹)))*(rhsPivot40 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*Z⁻¹)))*(rhsPivot118 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*Z⁻¹)))*(rhsPivot119 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot131 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot200 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*(X⁻¹*(W⁻¹^2))))*(rhsPivot239 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*Z⁻¹)))*(rhsPivot241 X Y Z W a b r) + ((-((Y^2)*X⁻¹))*(rhsPivot256 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot257 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot259
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot260 X Y Z W a b r = X*(r 266) + ((((-1:ℚ):ℂ)*X)*(rhsPivot73 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot129 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*Z⁻¹)))*X)*(rhsPivot130 X Y Z W a b r) + (((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*X)*(rhsPivot232 X Y Z W a b r) + (((-(W⁻¹^2))*X)*(rhsPivot256 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot260
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot261 X Y Z W a b r = X*(r 269) + ((((-1:ℚ):ℂ)*X)*(rhsPivot65 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot114 X Y Z W a b r) + (((-(W⁻¹^2))*X)*(rhsPivot235 X Y Z W a b r) + (((-X⁻¹)*X)*(rhsPivot252 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot261
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot262 X Y Z W a b r = X*(r 271) + ((((-1:ℚ):ℂ)*X)*(rhsPivot116 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot126 X Y Z W a b r) + (((-(X*(W⁻¹^2)))*X)*(rhsPivot236 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2)))*X)*(rhsPivot256 X Y Z W a b r) + (((-(W⁻¹^2))*X)*(rhsPivot257 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot262
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot263 X Y Z W a b r = X*(r 273) + ((((-1:ℚ):ℂ)*X)*(rhsPivot166 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot170 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot263
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot264 X Y Z W a b r = X*(r 277) + ((((-1:ℚ):ℂ)*X)*(rhsPivot142 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot164 X Y Z W a b r) + (((-(X⁻¹*(Y⁻¹^2)))*X)*(rhsPivot233 X Y Z W a b r) + (((-((W^2)*(Y⁻¹^2)))*X)*(rhsPivot252 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot264
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot265 X Y Z W a b r = ((1:ℚ):ℂ)*(r 278) + (((-1:ℚ):ℂ)*(rhsPivot127 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot198 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot265
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot266 X Y Z W a b r = ((1:ℚ):ℂ)*(r 279) + ((0:ℂ))
    unfold rhsPivot266
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot267 X Y Z W a b r = ((1:ℚ):ℂ)*(r 280) + (((-1:ℚ):ℂ)*(rhsPivot153 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*(W⁻¹^2))))*(rhsPivot205 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2)))+((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot252 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot267
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot268 X Y Z W a b r = ((W⁻¹^2)*(X*(Y^2)))*(r 281) + (((-X⁻¹)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot92 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot149 X Y Z W a b r) + (((-(Y⁻¹^2))*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot189 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot256 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot257 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot268
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot269 X Y Z W a b r = ((1:ℚ):ℂ)*(r 212) + ((-Z⁻¹)*(rhsPivot10 X Y Z W a b r) + ((-Z⁻¹)*(rhsPivot113 X Y Z W a b r) + ((-Z⁻¹)*(rhsPivot120 X Y Z W a b r) + ((-Z⁻¹)*(rhsPivot143 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*(W⁻¹^2)))*(rhsPivot194 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot195 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot230 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot232 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot263 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*(Y^2))*(W⁻¹^2)))*(rhsPivot264 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot268 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot269
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot270 X Y Z W a b r = ((1:ℚ):ℂ)*(r 282) + ((-X⁻¹)*(rhsPivot67 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot166 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot270
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot271 X Y Z W a b r = ((1:ℚ):ℂ)*(r 285) + ((-X⁻¹)*(rhsPivot56 X Y Z W a b r) + ((-(X⁻¹*(W⁻¹^2)))*(rhsPivot78 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot196 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot271
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot272 X Y Z W a b r = ((1:ℚ):ℂ)*(r 287) + ((-X⁻¹)*(rhsPivot96 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot202 X Y Z W a b r) + ((-(X⁻¹*(W⁻¹^2)))*(rhsPivot230 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot262 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot272
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot273 X Y Z W a b r = ((1:ℚ):ℂ)*(r 288) + ((-X⁻¹)*(rhsPivot98 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot134 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot208 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*(W^2))*((Y⁻¹^2)*Z⁻¹)))*(rhsPivot231 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(rhsPivot235 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot273
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot274 X Y Z W a b r = ((W⁻¹^2)*(X*(Y^2)))*(r 291) + ((((-1:ℚ):ℂ)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot155 X Y Z W a b r) + (((-X⁻¹)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot242 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot246 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot274
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot275 X Y Z W a b r = ((1:ℚ):ℂ)*(r 292) + ((0:ℂ))
    unfold rhsPivot275
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot276 X Y Z W a b r = ((1:ℚ):ℂ)*(r 294) + ((0:ℂ))
    unfold rhsPivot276
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot277 X Y Z W a b r = X*(r 295) + ((((-1:ℚ):ℂ)*X)*(rhsPivot89 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot219 X Y Z W a b r) + (((-((Y⁻¹^2)+X))*X)*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot277
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot278 X Y Z W a b r = ((1:ℚ):ℂ)*(r 296) + (((-1:ℚ):ℂ)*(rhsPivot199 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot278
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot279 X Y Z W a b r = ((1:ℚ):ℂ)*(r 297) + (((-1:ℚ):ℂ)*(rhsPivot220 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot279
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot280 X Y Z W a b r = ((1:ℚ):ℂ)*(r 299) + ((0:ℂ))
    unfold rhsPivot280
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot281 X Y Z W a b r = ((1:ℚ):ℂ)*(r 300) + ((0:ℂ))
    unfold rhsPivot281
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot282 X Y Z W a b r = X*(r 301) + ((((-1:ℚ):ℂ)*X)*(rhsPivot247 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot282
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot283 X Y Z W a b r = ((1:ℚ):ℂ)*(r 303) + ((0:ℂ))
    unfold rhsPivot283
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot284 X Y Z W a b r = ((1:ℚ):ℂ)*(r 304) + (((-1:ℚ):ℂ)*(rhsPivot252 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot269 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot284
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot285 X Y Z W a b r = ((1:ℚ):ℂ)*(r 305) + ((0:ℂ))
    unfold rhsPivot285
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot286 X Y Z W a b r = ((1:ℚ):ℂ)*(r 308) + (((-1:ℚ):ℂ)*(rhsPivot67 X Y Z W a b r) + ((-(X*(Y⁻¹^2)))*(rhsPivot166 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot286
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot287 X Y Z W a b r = X*(r 309) + ((((-1:ℚ):ℂ)*X)*(rhsPivot68 X Y Z W a b r) + (((-(X⁻¹*(Y⁻¹^2)))*X)*(rhsPivot127 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot191 X Y Z W a b r) + (((-((Y⁻¹^2)*(W⁻¹^2)))*X)*(rhsPivot198 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*X)*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot287
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot288 X Y Z W a b r = X*(r 313) + ((((-1:ℚ):ℂ)*X)*(rhsPivot55 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot288
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot289 X Y Z W a b r = ((1:ℚ):ℂ)*(r 314) + (((-1:ℚ):ℂ)*(rhsPivot56 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot78 X Y Z W a b r) + ((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot196 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot289
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot290 X Y Z W a b r = ((1:ℚ):ℂ)*(r 315) + (((-1:ℚ):ℂ)*(rhsPivot79 X Y Z W a b r) + ((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot232 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot290
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot291 X Y Z W a b r = ((1:ℚ):ℂ)*(r 321) + (((-1:ℚ):ℂ)*(rhsPivot96 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot202 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot291
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot292 X Y Z W a b r = ((1:ℚ):ℂ)*(r 322) + ((0:ℂ))
    unfold rhsPivot292
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot293 X Y Z W a b r = ((1:ℚ):ℂ)*(r 323) + (((-1:ℚ):ℂ)*(rhsPivot97 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot293
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot294 X Y Z W a b r = ((1:ℚ):ℂ)*(r 324) + (((-1:ℚ):ℂ)*(rhsPivot98 X Y Z W a b r) + ((-(X*(Y⁻¹^2)))*(rhsPivot208 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot227 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*(Y⁻¹^2)))*(rhsPivot235 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot294
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot295 X Y Z W a b r = ((1:ℚ):ℂ)*(r 325) + ((0:ℂ))
    unfold rhsPivot295
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot296 X Y Z W a b r = ((1:ℚ):ℂ)*(r 326) + ((0:ℂ))
    unfold rhsPivot296
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot297 X Y Z W a b r = ((1:ℚ):ℂ)*(r 327) + ((0:ℂ))
    unfold rhsPivot297
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot298 X Y Z W a b r = ((1:ℚ):ℂ)*(r 329) + ((-X⁻¹)*(rhsPivot180 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot298
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot299 X Y Z W a b r = ((W⁻¹^2)*(X*(Y^2)))*(r 330) + ((((-1:ℚ):ℂ)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot101 X Y Z W a b r) + (((-X⁻¹)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot156 X Y Z W a b r) + (((-(Y⁻¹^2))*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot194 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot299
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot300 X Y Z W a b r = ((1:ℚ):ℂ)*(r 332) + ((-X⁻¹)*(rhsPivot158 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot300
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot301 X Y Z W a b r = ((1:ℚ):ℂ)*(r 346) + ((-X⁻¹)*(rhsPivot114 X Y Z W a b r) + ((-(X⁻¹*(W⁻¹^2)))*(rhsPivot235 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot301
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot302 X Y Z W a b r = ((W⁻¹^2)*(X*(Y^2)))*(r 348) + (((-X⁻¹)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot62 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot100 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot302
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot303 X Y Z W a b r = ((1:ℚ):ℂ)*(r 355) + ((0:ℂ))
    unfold rhsPivot303
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot304 X Y Z W a b r = ((1:ℚ):ℂ)*(r 356) + (((-1:ℚ):ℂ)*(rhsPivot78 X Y Z W a b r) + ((-(X*(Y⁻¹^2)))*(rhsPivot196 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot246 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot304
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot305 X Y Z W a b r = ((1:ℚ):ℂ)*(r 358) + ((0:ℂ))
    unfold rhsPivot305
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot306 X Y Z W a b r = ((1:ℚ):ℂ)*(r 359) + (((-1:ℚ):ℂ)*(rhsPivot104 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot198 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot306
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot307 X Y Z W a b r = X*(r 364) + ((((-1:ℚ):ℂ)*X)*(rhsPivot107 X Y Z W a b r) + (((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*X)*(rhsPivot233 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot287 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot307
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot308 X Y Z W a b r = ((1:ℚ):ℂ)*(r 365) + (((-1:ℚ):ℂ)*(rhsPivot57 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot98 X Y Z W a b r) + ((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot208 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot235 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot308
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot309 X Y Z W a b r = X*(r 366) + ((((-1:ℚ):ℂ)*X)*(rhsPivot54 X Y Z W a b r) + (((-(W⁻¹^2))*X)*(rhsPivot194 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot309
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot310 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 307) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot66 X Y Z W a b r) + (((-X⁻¹)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot126 X Y Z W a b r) + (((-(W⁻¹^2))*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot236 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*(Y^2))*(X⁻¹*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot256 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot309 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot310
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot311 X Y Z W a b r = (((-1:ℚ):ℂ)*(X^2))*(r 370) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*(X^2)))*(rhsPivot122 X Y Z W a b r) + (((-(X⁻¹*(Y⁻¹^2)))*(((-1:ℚ):ℂ)*(X^2)))*(rhsPivot152 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*(X^2)))*(rhsPivot190 X Y Z W a b r) + (((-((Y⁻¹^2)*(W⁻¹^2)))*(((-1:ℚ):ℂ)*(X^2)))*(rhsPivot202 X Y Z W a b r) + (((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*(((-1:ℚ):ℂ)*(X^2)))*(rhsPivot230 X Y Z W a b r) + (((-X⁻¹)*(((-1:ℚ):ℂ)*(X^2)))*(rhsPivot290 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot311
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot312 X Y Z W a b r = ((1:ℚ):ℂ)*(r 371) + (((-1:ℚ):ℂ)*(rhsPivot123 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot235 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot312
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot313 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 372) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot87 X Y Z W a b r) + (((-((Y^2)*(X⁻¹*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot256 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot288 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot313
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot314 X Y Z W a b r = ((1:ℚ):ℂ)*(r 374) + ((0:ℂ))
    unfold rhsPivot314
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot315 X Y Z W a b r = ((1:ℚ):ℂ)*(r 378) + ((0:ℂ))
    unfold rhsPivot315
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot316 X Y Z W a b r = ((1:ℚ):ℂ)*(r 379) + ((0:ℂ))
    unfold rhsPivot316
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot317 X Y Z W a b r = ((1:ℚ):ℂ)*(r 380) + ((0:ℂ))
    unfold rhsPivot317
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot318 X Y Z W a b r = ((1:ℚ):ℂ)*(r 381) + (((-1:ℚ):ℂ)*(rhsPivot204 X Y Z W a b r) + ((0:ℂ)))
    unfold rhsPivot318
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot319 X Y Z W a b r = X*(r 384) + ((((-1:ℚ):ℂ)*X)*(rhsPivot90 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot205 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*(Y⁻¹^2))+(((-1:ℚ):ℂ)*X)))*X)*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot319
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot320 X Y Z W a b r = ((1:ℚ):ℂ)*(r 385) + ((0:ℂ))
    unfold rhsPivot320
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot321 X Y Z W a b r = ((1:ℚ):ℂ)*(r 386) + ((0:ℂ))
    unfold rhsPivot321
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot322 X Y Z W a b r = ((W⁻¹^2)*(X*(Y^2)))*(r 387) + ((((-1:ℚ):ℂ)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot148 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot227 X Y Z W a b r) + (((-X⁻¹)*((W⁻¹^2)*(X*(Y^2))))*(rhsPivot239 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot322
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot323 X Y Z W a b r = ((1:ℚ):ℂ)*(r 389) + ((-X⁻¹)*(rhsPivot78 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot136 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot196 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*(W^2))*((Y⁻¹^2)*Z⁻¹)))*(rhsPivot234 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot323
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot324 X Y Z W a b r = ((1:ℚ):ℂ)*(r 390) + ((-X⁻¹)*(rhsPivot104 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot198 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot268 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot324
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot325 X Y Z W a b r = ((1:ℚ):ℂ)*(r 392) + ((-X⁻¹)*(rhsPivot57 X Y Z W a b r) + ((-(X⁻¹*(W⁻¹^2)))*(rhsPivot98 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot208 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot235 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot325
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot326 X Y Z W a b r = ((1:ℚ):ℂ)*(r 395) + ((-X⁻¹)*(rhsPivot123 X Y Z W a b r) + ((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot235 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot326
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot327 X Y Z W a b r = ((1:ℚ):ℂ)*(r 396) + ((-X⁻¹)*(rhsPivot124 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot151 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*(W⁻¹^2))))*(rhsPivot219 X Y Z W a b r) + ((-((X⁻¹*(W⁻¹^2))+((Y^2)*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot253 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot327
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot328 X Y Z W a b r = ((1:ℚ):ℂ)*(r 397) + ((0:ℂ))
    unfold rhsPivot328
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot329 X Y Z W a b r = ((1:ℚ):ℂ)*(r 398) + (((-1:ℚ):ℂ)*(rhsPivot152 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot202 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot329
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot330 X Y Z W a b r = X*(r 399) + ((((-1:ℚ):ℂ)*X)*(rhsPivot111 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot144 X Y Z W a b r) + (((-(X⁻¹*(Y⁻¹^2)))*X)*(rhsPivot232 X Y Z W a b r) + (((-((X*(W^2))*(Y⁻¹^2)))*X)*(rhsPivot253 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot330
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot331 X Y Z W a b r = ((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2))*(r 247) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot1 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot21 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot31 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot43 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot60 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot62 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot64 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot78 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot88 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot92 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot93 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot98 X Y Z W a b r) + (((-((W^2)*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot126 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot134 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot136 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot144 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot156 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot164 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot189 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot192 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot193 X Y Z W a b r) + (((-((((2:ℚ):ℂ)*X)*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot194 X Y Z W a b r) + (((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2))*(rhsPivot195 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot196 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot205 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot208 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot219 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot227 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*(W^2))*((Y⁻¹^2)*Z⁻¹)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot231 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*(W^2))*((Y⁻¹^2)*Z⁻¹)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot234 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*X)*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot235 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot236 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot239 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot242 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot246 X Y Z W a b r) + (((-((W^2)*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot252 X Y Z W a b r) + (((-((X*(W^2))*(Y⁻¹^2)))*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot253 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot264 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot277 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot319 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*(W⁻¹^2))*(Y^2)))*(rhsPivot330 X Y Z W a b r) + ((0:ℂ)))))))))))))))))))))))))))))))))))))))))))
    unfold rhsPivot331
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot332 X Y Z W a b r = X*(r 403) + ((((-1:ℚ):ℂ)*X)*(rhsPivot74 X Y Z W a b r) + (((-X⁻¹)*X)*(rhsPivot114 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot180 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*X)*(rhsPivot235 X Y Z W a b r) + (((-((Y^2)*(W⁻¹^2)))*X)*(rhsPivot330 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot332
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot333 X Y Z W a b r = X*(r 405) + ((((-1:ℚ):ℂ)*X)*(rhsPivot158 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot253 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot333
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot334 X Y Z W a b r = X*(r 408) + ((((-1:ℚ):ℂ)*X)*(rhsPivot61 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot160 X Y Z W a b r) + (((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*X)*(rhsPivot233 X Y Z W a b r) + (((-(X*((Y⁻¹^2)*(W⁻¹^2))))*X)*(rhsPivot236 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*X)*(rhsPivot256 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot334
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot335 X Y Z W a b r = (Y^2)*(r 417) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(Y^2))*(rhsPivot126 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Y^2))*(rhsPivot140 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*a)*(Y⁻¹*(W⁻¹^2))))*(Y^2))*(rhsPivot236 X Y Z W a b r) + (((-((Y*a)*(W⁻¹^2)))*(Y^2))*(rhsPivot256 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Y^2))*(rhsPivot311 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(X^2)))*(Y^2))*(rhsPivot313 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot335
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot336 X Y Z W a b r = (Y^2)*(r 456) + ((((-1:ℚ):ℂ)*(Y^2))*(rhsPivot106 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(Y^2))*(rhsPivot158 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Y^2))*(rhsPivot177 X Y Z W a b r) + (((-((Y⁻¹^2)*(W⁻¹^2)))*(Y^2))*(rhsPivot233 X Y Z W a b r) + (((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(Y^2))*(rhsPivot236 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Y^2))*(rhsPivot252 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(Y^2))*(rhsPivot256 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot336
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot337 X Y Z W a b r = (Y^2)*(r 463) + ((((-1:ℚ):ℂ)*(Y^2))*(rhsPivot81 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Y^2))*(rhsPivot94 X Y Z W a b r) + (((-(X*(W⁻¹^2)))*(Y^2))*(rhsPivot111 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(Y^2))*(rhsPivot114 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(Y^2))*(rhsPivot124 X Y Z W a b r) + (((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(Y^2))*(rhsPivot131 X Y Z W a b r) + (((-((Y⁻¹^2)*(W⁻¹^2)))*(Y^2))*(rhsPivot232 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*(Y⁻¹*(W⁻¹^2))))*(Y^2))*(rhsPivot235 X Y Z W a b r) + (((-X)*(Y^2))*(rhsPivot253 X Y Z W a b r) + (((-(W⁻¹^2))*(Y^2))*(rhsPivot256 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot337
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot338 X Y Z W a b r = ((1:ℚ):ℂ)*(r 480) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot54 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot112 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot163 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*(Y⁻¹*(W⁻¹^2))))*(rhsPivot194 X Y Z W a b r) + ((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot230 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot338
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot339 X Y Z W a b r = ((1:ℚ):ℂ)*(r 495) + (((-1:ℚ):ℂ)*(rhsPivot4 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot70 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*b)*W⁻¹))*(rhsPivot77 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot150 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot189 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*(W⁻¹^2)))*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot327 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot337 X Y Z W a b r) + ((0:ℂ))))))))))
    unfold rhsPivot339
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot340 X Y Z W a b r = ((1:ℚ):ℂ)*(r 429) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot55 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot80 X Y Z W a b r) + ((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot91 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot172 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot194 X Y Z W a b r) + ((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot195 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot298 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*(X⁻¹*(W⁻¹^2))))*(rhsPivot330 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot339 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot340
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot341 X Y Z W a b r = ((1:ℚ):ℂ)*(r 502) + ((-(W⁻¹^2))*(rhsPivot3 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot124 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot126 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot180 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot230 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*b)*W⁻¹))*(rhsPivot235 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot236 X Y Z W a b r) + ((-X)*(rhsPivot253 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2)))*(rhsPivot256 X Y Z W a b r) + ((-((Y^2)*(W⁻¹^2)))*(rhsPivot330 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot341
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot342 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 504) + (((1:ℚ):ℂ)*(rhsPivot157 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot166 X Y Z W a b r) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot189 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*b)*W⁻¹))*((-1:ℚ):ℂ))*(rhsPivot196 X Y Z W a b r) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot198 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot214 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot230 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot257 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot284 X Y Z W a b r) + ((0:ℂ)))))))))))
    unfold rhsPivot342
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot343 X Y Z W a b r = ((1:ℚ):ℂ)*(r 487) + (((-1:ℚ):ℂ)*(rhsPivot178 X Y Z W a b r) + ((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot189 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot269 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot333 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot342 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot343
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot344 X Y Z W a b r = ((1:ℚ):ℂ)*(r 362) + (((-1:ℚ):ℂ)*(rhsPivot106 X Y Z W a b r) + ((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot236 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot256 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot343 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot344
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot345 X Y Z W a b r = ((1:ℚ):ℂ)*(r 512) + ((-((((-1:ℚ):ℂ)*b)*W⁻¹))*(rhsPivot131 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot153 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot161 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot189 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot202 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*(W⁻¹^2))))*(rhsPivot205 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2)))+X⁻¹)+((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*(Y^2))*b)*(X⁻¹*W⁻¹)))*(rhsPivot256 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot320 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot336 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot342 X Y Z W a b r) + ((0:ℂ))))))))))))))
    unfold rhsPivot345
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot346 X Y Z W a b r = ((1:ℚ):ℂ)*(r 349) + ((-X⁻¹)*(rhsPivot170 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*(W⁻¹^2))))*(rhsPivot264 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot345 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot346
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot347 X Y Z W a b r = ((1:ℚ):ℂ)*(r 528) + (((-1:ℚ):ℂ)*(rhsPivot74 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot114 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot116 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot194 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot202 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*b)*W⁻¹))*(rhsPivot208 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot211 X Y Z W a b r) + ((-(X⁻¹*(W⁻¹^2)))*(rhsPivot230 X Y Z W a b r) + ((-((X⁻¹*(W⁻¹^2))+(b*W⁻¹)))*(rhsPivot235 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot257 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot341 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot347
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot348 X Y Z W a b r = ((1:ℚ):ℂ)*(r 416) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot65 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot139 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*(X⁻¹*Y⁻¹)))*(rhsPivot252 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot276 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(rhsPivot337 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot341 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot347 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot348
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot349 X Y Z W a b r = X*(r 318) + ((((-1:ℚ):ℂ)*X)*(rhsPivot94 X Y Z W a b r) + (((-(X*((Y⁻¹^2)*(W⁻¹^2))))*X)*(rhsPivot131 X Y Z W a b r) + (((-(W⁻¹^2))*X)*(rhsPivot256 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot348 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot349
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot350 X Y Z W a b r = ((1:ℚ):ℂ)*(r 203) + ((-(X⁻¹*Z⁻¹))*(rhsPivot10 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot99 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot103 X Y Z W a b r) + ((-(X⁻¹*Z⁻¹))*(rhsPivot113 X Y Z W a b r) + ((-(X⁻¹*Z⁻¹))*(rhsPivot143 X Y Z W a b r) + ((-(X⁻¹*Z⁻¹))*(rhsPivot165 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*(rhsPivot195 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot324 X Y Z W a b r) + ((0:ℂ))))))))))
    unfold rhsPivot350
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot351 X Y Z W a b r = ((1:ℚ):ℂ)*(r 204) + ((-(X⁻¹*Z⁻¹))*(rhsPivot10 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot97 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot102 X Y Z W a b r) + ((-(X⁻¹*Z⁻¹))*(rhsPivot120 X Y Z W a b r) + ((-(X⁻¹*Z⁻¹))*(rhsPivot143 X Y Z W a b r) + ((-(X⁻¹*Z⁻¹))*(rhsPivot165 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot194 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*(rhsPivot195 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot235 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot272 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot351
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot352 X Y Z W a b r = ((1:ℚ):ℂ)*(r 205) + ((-(X*Z⁻¹))*(rhsPivot6 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot104 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot121 X Y Z W a b r) + ((-(X*Z⁻¹))*(rhsPivot130 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot198 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot230 X Y Z W a b r) + ((-(X*Z⁻¹))*(rhsPivot231 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot232 X Y Z W a b r) + ((-(X*Z⁻¹))*(rhsPivot234 X Y Z W a b r) + ((-X)*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot302 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot352
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot353 X Y Z W a b r = ((1:ℚ):ℂ)*(r 206) + ((-(X*Z⁻¹))*(rhsPivot6 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot96 X Y Z W a b r) + ((-(X*Z⁻¹))*(rhsPivot135 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot150 X Y Z W a b r) + ((-X)*(rhsPivot189 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot202 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot230 X Y Z W a b r) + ((-(X*Z⁻¹))*(rhsPivot231 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot233 X Y Z W a b r) + ((-(X*Z⁻¹))*(rhsPivot234 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot299 X Y Z W a b r) + ((0:ℂ))))))))))))))
    unfold rhsPivot353
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot354 X Y Z W a b r = ((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2))*(r 209) + (((-(Z*(X⁻¹*(Y⁻¹^2))))*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot0 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot12 X Y Z W a b r) + (((-(Z*(X⁻¹*(Y⁻¹^2))))*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot204 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot207 X Y Z W a b r) + (((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2))*(rhsPivot238 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot240 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot244 X Y Z W a b r) + (((-(Z*(X⁻¹*(Y⁻¹^2))))*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot322 X Y Z W a b r) + ((0:ℂ))))))))))
    unfold rhsPivot354
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot355 X Y Z W a b r = ((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2))*(r 210) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot11 X Y Z W a b r) + (((-(Z*(X⁻¹*(Y⁻¹^2))))*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot16 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot217 X Y Z W a b r) + (((-(Z*(X⁻¹*(Y⁻¹^2))))*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot220 X Y Z W a b r) + (((-(Z*(X⁻¹*(Y⁻¹^2))))*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot235 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot237 X Y Z W a b r) + (((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2))*(rhsPivot241 X Y Z W a b r) + ((((-1:ℚ):ℂ)*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot243 X Y Z W a b r) + (((-(Z*(X⁻¹*(Y⁻¹^2))))*((((-1:ℚ):ℂ)*Z⁻¹)*(Y^2)))*(rhsPivot274 X Y Z W a b r) + ((0:ℂ)))))))))))
    unfold rhsPivot355
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot356 X Y Z W a b r = ((1:ℚ):ℂ)*(r 214) + (((-1:ℚ):ℂ)*(rhsPivot77 X Y Z W a b r) + ((-((Y^2)*Z⁻¹))*(rhsPivot118 X Y Z W a b r) + ((-((Y^2)*Z⁻¹))*(rhsPivot119 X Y Z W a b r) + ((-((Y^2)*Z⁻¹))*(rhsPivot133 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*(W⁻¹^2)))*(rhsPivot194 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2)))*(rhsPivot239 X Y Z W a b r) + ((-((Y^2)*Z⁻¹))*(rhsPivot241 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot333 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot355 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot356
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot357 X Y Z W a b r = ((1:ℚ):ℂ)*(r 215) + (((-1:ℚ):ℂ)*(rhsPivot91 X Y Z W a b r) + ((-((Y^2)*Z⁻¹))*(rhsPivot117 X Y Z W a b r) + ((-((Y^2)*Z⁻¹))*(rhsPivot128 X Y Z W a b r) + ((-((Y^2)*Z⁻¹))*(rhsPivot169 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot189 X Y Z W a b r) + ((-X)*(rhsPivot194 X Y Z W a b r) + ((-((Y^2)*Z⁻¹))*(rhsPivot238 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2)))*(rhsPivot242 X Y Z W a b r) + ((-X)*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot261 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot354 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot357
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot358 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 227) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot2 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot5 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot6 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot43 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot60 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot62 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot83 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot88 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot98 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot99 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot102 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot118 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot131 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot136 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot137 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot144 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot193 X Y Z W a b r) + (((-((((2:ℚ):ℂ)*X)*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot194 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot196 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot198 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot202 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot205 X Y Z W a b r) + (((-((((2:ℚ):ℂ)*X)*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot208 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*(Y⁻¹^2))+((-1:ℚ):ℂ))+(((-1:ℚ):ℂ)*X)))*((-1:ℚ):ℂ))*(rhsPivot230 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*(W^2))*((Y⁻¹^2)*Z⁻¹)))*((-1:ℚ):ℂ))*(rhsPivot234 X Y Z W a b r) + (((-((Y⁻¹^2)+((((-2:ℚ):ℂ)*X)*(Y⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot235 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot236 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot239 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot246 X Y Z W a b r) + (((-((X*(W^2))*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot253 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot256 X Y Z W a b r) + (((-(((((2:ℚ):ℂ)*X)*(Y⁻¹^2))+(((((-1:ℚ):ℂ)*X)*Z)*(Y⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot257 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot264 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot277 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*(W^2))*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot331 X Y Z W a b r) + (((-((W^2)*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot335 X Y Z W a b r) + ((0:ℂ))))))))))))))))))))))))))))))))))))))
    unfold rhsPivot358
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot359 X Y Z W a b r = ((1:ℚ):ℂ)*(r 222) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot4 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot9 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot10 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot11 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot13 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot15 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot27 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot77 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot82 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot90 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot91 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot101 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot105 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot111 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot121 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot132 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot141 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot149 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot150 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot155 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(W^2))*((X⁻¹*(Y⁻¹^2))*Z⁻¹)))*(rhsPivot165 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot189 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot194 X Y Z W a b r) + ((-(((2:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot195 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot215 X Y Z W a b r) + ((-(((2:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot232 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot233 X Y Z W a b r) + ((-(((2:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot235 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot250 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot255 X Y Z W a b r) + ((-((Y^2)*X⁻¹))*(rhsPivot256 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(rhsPivot257 X Y Z W a b r) + ((-((W^2)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot268 X Y Z W a b r) + ((-((W^2)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot274 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot277 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot294 X Y Z W a b r) + ((-((W^2)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot299 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot323 X Y Z W a b r) + ((-((W^2)*(Y⁻¹^2)))*(rhsPivot331 X Y Z W a b r) + ((-(((W^2)*(X⁻¹*(Y⁻¹^2)))+((((-1:ℚ):ℂ)*(W^2))*(Y⁻¹^2))))*(rhsPivot335 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot358 X Y Z W a b r) + ((0:ℂ)))))))))))))))))))))))))))))))))))))))))))
    unfold rhsPivot359
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot360 X Y Z W a b r = X*(r 270) + ((((-1:ℚ):ℂ)*X)*(rhsPivot75 X Y Z W a b r) + (((-(X⁻¹*(Y⁻¹^2)))*X)*(rhsPivot115 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot197 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*X)*(rhsPivot227 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*X)*(rhsPivot256 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot360
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot361 X Y Z W a b r = ((1:ℚ):ℂ)*(r 274) + (((-1:ℚ):ℂ)*(rhsPivot173 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot189 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot257 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot361
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot362 X Y Z W a b r = ((1:ℚ):ℂ)*(r 284) + ((-X⁻¹)*(rhsPivot59 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot189 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot257 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot362
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot363 X Y Z W a b r = ((1:ℚ):ℂ)*(r 336) + ((-X⁻¹)*(rhsPivot162 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot189 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot257 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot363
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot364 X Y Z W a b r = ((1:ℚ):ℂ)*(r 343) + ((-X⁻¹)*(rhsPivot109 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot257 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot364
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot365 X Y Z W a b r = ((1:ℚ):ℂ)*(r 352) + ((-X⁻¹)*(rhsPivot267 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot299 X Y Z W a b r) + ((0:ℂ))))
    unfold rhsPivot365
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot366 X Y Z W a b r = X*(r 377) + ((((-1:ℚ):ℂ)*X)*(rhsPivot228 X Y Z W a b r) + (X*(rhsPivot291 X Y Z W a b r) + (((-X⁻¹)*X)*(rhsPivot336 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot366
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot367 X Y Z W a b r = ((1:ℚ):ℂ)*(r 393) + ((-X⁻¹)*(rhsPivot108 X Y Z W a b r) + ((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot121 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot257 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot367
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot368 X Y Z W a b r = ((1:ℚ):ℂ)*(r 402) + (((-1:ℚ):ℂ)*(rhsPivot168 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot171 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot257 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot368
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot369 X Y Z W a b r = X*(r 404) + ((((-1:ℚ):ℂ)*X)*(rhsPivot181 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot225 X Y Z W a b r) + (((-((Y⁻¹^2)*(W⁻¹^2)))*X)*(rhsPivot236 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*X)*(rhsPivot246 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*X)*(rhsPivot256 X Y Z W a b r) + (((-(W⁻¹^2))*X)*(rhsPivot358 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot369
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot370 X Y Z W a b r = (((-1:ℚ):ℂ)*X)*(r 414) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot34 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(((-1:ℚ):ℂ)*X))*(rhsPivot69 X Y Z W a b r) + (((-(Y⁻¹^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot166 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*(Y⁻¹*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot189 X Y Z W a b r) + (((-(a*(Y⁻¹*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot257 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot289 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot312 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot370
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot371 X Y Z W a b r = ((1:ℚ):ℂ)*(r 423) + (((-1:ℚ):ℂ)*(rhsPivot19 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot204 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot262 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot354 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot357 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot371
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot372 X Y Z W a b r = ((1:ℚ):ℂ)*(r 376) + (((-1:ℚ):ℂ)*(rhsPivot311 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X^2)))*(rhsPivot313 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot354 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot371 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot372
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot373 X Y Z W a b r = (((-1:ℚ):ℂ)*X⁻¹)*(r 426) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot197 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot199 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot227 X Y Z W a b r) + (((-((X*a)*Y⁻¹))*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot322 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot336 X Y Z W a b r) + (((-(Y⁻¹^2))*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot353 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot366 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot373
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot374 X Y Z W a b r = ((1:ℚ):ℂ)*(r 427) + ((-(Y⁻¹^2))*(rhsPivot158 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot252 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot260 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot356 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2)))*(rhsPivot358 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot374
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot375 X Y Z W a b r = ((1:ℚ):ℂ)*(r 428) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot0 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot45 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot167 X Y Z W a b r) + ((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot189 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot353 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot375
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot376 X Y Z W a b r = ((1:ℚ):ℂ)*(r 432) + (((-1:ℚ):ℂ)*(rhsPivot22 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot96 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*a)*(Y⁻¹*(W⁻¹^2))))*(rhsPivot202 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*(Y⁻¹*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot322 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot376
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot377 X Y Z W a b r = (((-1:ℚ):ℂ)*X)*(r 444) + (((-(Y⁻¹^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot115 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot245 X Y Z W a b r) + (((-(W⁻¹^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot256 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot263 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*(Y^2))*(W⁻¹^2)))*(((-1:ℚ):ℂ)*X))*(rhsPivot264 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot350 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(((-1:ℚ):ℂ)*X))*(rhsPivot355 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*(Y^2))*(X⁻¹*(W⁻¹^2)))+(((((-1:ℚ):ℂ)*Y)*a)*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot358 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot368 X Y Z W a b r) + ((0:ℂ)))))))))))
    unfold rhsPivot377
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot378 X Y Z W a b r = ((1:ℚ):ℂ)*(r 445) + (((-1:ℚ):ℂ)*(rhsPivot29 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot204 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot262 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot299 X Y Z W a b r) + ((-((X*a)*Y⁻¹))*(rhsPivot354 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot378
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot379 X Y Z W a b r = (((-1:ℚ):ℂ)*X)*(r 450) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot42 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot103 X Y Z W a b r) + (((-(Y⁻¹^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot214 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(((-1:ℚ):ℂ)*X))*(rhsPivot223 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot280 X Y Z W a b r) + (((-(a*Y⁻¹))*(((-1:ℚ):ℂ)*X))*(rhsPivot333 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(((-1:ℚ):ℂ)*X))*(rhsPivot342 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot343 X Y Z W a b r) + (((-((Y^2)*(X⁻¹*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot358 X Y Z W a b r) + ((0:ℂ)))))))))))
    unfold rhsPivot379
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot380 X Y Z W a b r = ((1:ℚ):ℂ)*(r 451) + (((-1:ℚ):ℂ)*(rhsPivot160 X Y Z W a b r) + ((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot236 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot256 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot327 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot335 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot380
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot381 X Y Z W a b r = ((1:ℚ):ℂ)*(r 452) + (((-1:ℚ):ℂ)*(rhsPivot48 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot104 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot198 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*(rhsPivot230 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot269 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot274 X Y Z W a b r) + ((-((((((-1:ℚ):ℂ)*X)*Y)*a)*(W⁻¹^2)))*(rhsPivot358 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot381
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot382 X Y Z W a b r = ((1:ℚ):ℂ)*(r 454) + (((-1:ℚ):ℂ)*(rhsPivot162 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot180 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot188 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot189 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*(W⁻¹^2)))*(rhsPivot257 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot261 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot288 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*(Y⁻¹^2)))*(rhsPivot313 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*Y)*a)*(W⁻¹^2)))*(rhsPivot330 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot354 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot382
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot383 X Y Z W a b r = (((-1:ℚ):ℂ)*X)*(r 455) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot26 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(((-1:ℚ):ℂ)*X))*(rhsPivot157 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot176 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*(Y⁻¹*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot189 X Y Z W a b r) + (((-((Y⁻¹^2)*(W⁻¹^2)))*(((-1:ℚ):ℂ)*X))*(rhsPivot208 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot235 X Y Z W a b r) + (((-(a*(Y⁻¹*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot257 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot283 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot307 X Y Z W a b r) + (((-(X^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot310 X Y Z W a b r) + (((-(Y⁻¹^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot315 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(((-1:ℚ):ℂ)*X))*(rhsPivot331 X Y Z W a b r) + (((-(Y⁻¹^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot335 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot355 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot356 X Y Z W a b r) + (((-((X⁻¹*(W⁻¹^2))+((Y^2)*(W⁻¹^2))))*(((-1:ℚ):ℂ)*X))*(rhsPivot358 X Y Z W a b r) + ((0:ℂ))))))))))))))))))
    unfold rhsPivot383
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot384 X Y Z W a b r = ((1:ℚ):ℂ)*(r 464) + (((-1:ℚ):ℂ)*(rhsPivot109 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot170 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot182 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot257 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*Y)*a)*(W⁻¹^2)))*(rhsPivot264 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot309 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*(Y⁻¹^2)))*(rhsPivot310 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot333 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot355 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*(rhsPivot358 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot384
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot385 X Y Z W a b r = ((1:ℚ):ℂ)*(r 475) + (((-1:ℚ):ℂ)*(rhsPivot216 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot259 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot261 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot272 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot347 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot385
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot386 X Y Z W a b r = ((1:ℚ):ℂ)*(r 482) + ((-(Y⁻¹^2))*(rhsPivot114 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot124 X Y Z W a b r) + ((-((Y⁻¹^2)*(W⁻¹^2)))*(rhsPivot235 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*a)*Y⁻¹))*(rhsPivot253 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot334 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot357 X Y Z W a b r) + ((0:ℂ))))))))
    unfold rhsPivot386
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot387 X Y Z W a b r = ((1:ℚ):ℂ)*(r 488) + (((-1:ℚ):ℂ)*(rhsPivot58 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot152 X Y Z W a b r) + ((-(X*(W⁻¹^2)))*(rhsPivot194 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*a)*(Y⁻¹*(W⁻¹^2))))*(rhsPivot202 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot221 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*(Y⁻¹*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot299 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot387
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot388 X Y Z W a b r = ((1:ℚ):ℂ)*(r 491) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot37 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot47 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot332 X Y Z W a b r) + ((0:ℂ)))))
    unfold rhsPivot388
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot389 X Y Z W a b r = ((1:ℚ):ℂ)*(r 493) + (((-1:ℚ):ℂ)*(rhsPivot140 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot188 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot227 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot242 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*b)*W⁻¹))*(rhsPivot256 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot261 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot386 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot389
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot390 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 496) + (((1:ℚ):ℂ)*(rhsPivot57 X Y Z W a b r) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot98 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot171 X Y Z W a b r) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot192 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot195 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot206 X Y Z W a b r) + (((-(X*((Y⁻¹^2)*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot208 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot219 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot229 X Y Z W a b r) + (((-(((Y⁻¹^2)+(W⁻¹^2))+X))*((-1:ℚ):ℂ))*(rhsPivot230 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*X)*((Y⁻¹^2)*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot235 X Y Z W a b r) + (((-(X*((Y⁻¹^2)*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot257 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*b)*W⁻¹))*((-1:ℚ):ℂ))*(rhsPivot264 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot328 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot351 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot373 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot385 X Y Z W a b r) + ((0:ℂ)))))))))))))))))))
    unfold rhsPivot390
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot391 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 500) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot1 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot64 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*b)*W⁻¹))*((-1:ℚ):ℂ))*(rhsPivot98 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot123 X Y Z W a b r) + (((-(X*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot194 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*b)*((Y⁻¹^2)*W⁻¹)))*((-1:ℚ):ℂ))*(rhsPivot208 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot209 X Y Z W a b r) + (((-(((Y⁻¹^2)*(W⁻¹^2))+((X*b)*((Y⁻¹^2)*W⁻¹))))*((-1:ℚ):ℂ))*(rhsPivot235 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot343 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot368 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot377 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot391
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot392 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 435) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*((-1:ℚ):ℂ))*(rhsPivot258 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot266 X Y Z W a b r) + (((-(Y⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot284 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot324 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*((-1:ℚ):ℂ))*(rhsPivot333 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot381 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot391 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot392
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot393 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 501) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot5 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot65 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot87 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*b)*W⁻¹))*((-1:ℚ):ℂ))*(rhsPivot99 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot137 X Y Z W a b r) + (((-X⁻¹)*((-1:ℚ):ℂ))*(rhsPivot252 X Y Z W a b r) + (((-((Y^2)*(X⁻¹*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot256 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot281 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot335 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot357 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot363 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot393
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot394 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 219) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot3 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot4 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot9 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot10 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot13 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot15 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot18 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot27 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot38 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot54 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot74 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot77 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot91 X Y Z W a b r) + (((-X⁻¹)*((-1:ℚ):ℂ))*(rhsPivot114 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot121 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot146 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot150 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot161 X Y Z W a b r) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot189 X Y Z W a b r) + (((-(((2:ℚ):ℂ)*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot194 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot195 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot223 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot230 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot233 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot234 X Y Z W a b r) + (((-(((2:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot235 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot272 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot276 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot284 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot297 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot301 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot302 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot315 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot321 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot327 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot331 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot333 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot335 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot337 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot341 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot346 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot353 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot356 X Y Z W a b r) + (((-(((Y^2)*(X⁻¹*(W⁻¹^2)))+((X*(Y^2))*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot358 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot363 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot393 X Y Z W a b r) + ((0:ℂ))))))))))))))))))))))))))))))))))))))))))))))))
    unfold rhsPivot394
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot395 X Y Z W a b r = ((1:ℚ):ℂ)*(r 534) + (((-1:ℚ):ℂ)*(rhsPivot2 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot55 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot196 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot265 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot301 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot335 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot394 X Y Z W a b r) + ((0:ℂ)))))))))
    unfold rhsPivot395
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot396 X Y Z W a b r = ((1:ℚ):ℂ)*(r 425) + (((-1:ℚ):ℂ)*(rhsPivot63 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot199 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot222 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot275 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot313 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(rhsPivot322 X Y Z W a b r) + ((-(a*(X⁻¹*Y⁻¹)))*(rhsPivot339 X Y Z W a b r) + ((-(a*Y⁻¹))*(rhsPivot352 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*((X⁻¹^3)*(Y⁻¹^2))))*(rhsPivot354 X Y Z W a b r) + ((-(((X*Y)*a)*(W⁻¹^2)))*(rhsPivot358 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot395 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot396
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot397 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 437) + (((1:ℚ):ℂ)*(rhsPivot211 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot270 X Y Z W a b r) + (((-(Y⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot298 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot325 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot330 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot339 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot341 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*((-1:ℚ):ℂ))*(rhsPivot363 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot369 X Y Z W a b r) + (((-(a*Y⁻¹))*((-1:ℚ):ℂ))*(rhsPivot393 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot397
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot398 X Y Z W a b r = ((1:ℚ):ℂ)*(r 353) + (((-1:ℚ):ℂ)*(rhsPivot282 X Y Z W a b r) + ((-X)*(rhsPivot306 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot337 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot381 X Y Z W a b r) + ((-X⁻¹)*(rhsPivot397 X Y Z W a b r) + ((0:ℂ)))))))
    unfold rhsPivot398
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot399 X Y Z W a b r = ((1:ℚ):ℂ)*(r 438) + (((-1:ℚ):ℂ)*(rhsPivot261 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot341 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot389 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot393 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot399
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot400 X Y Z W a b r = (((-1:ℚ):ℂ)*X)*(r 448) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot41 X Y Z W a b r) + (((-(Y⁻¹^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot258 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot279 X Y Z W a b r) + ((((-1:ℚ):ℂ)*(((-1:ℚ):ℂ)*X))*(rhsPivot303 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(((-1:ℚ):ℂ)*X))*(rhsPivot324 X Y Z W a b r) + (((-(Y⁻¹^2))*(((-1:ℚ):ℂ)*X))*(rhsPivot333 X Y Z W a b r) + (((-X)*(((-1:ℚ):ℂ)*X))*(rhsPivot355 X Y Z W a b r) + (((-((X*(Y^2))*(W⁻¹^2)))*(((-1:ℚ):ℂ)*X))*(rhsPivot358 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot383 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*(((-1:ℚ):ℂ)*X))*(rhsPivot394 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot400
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot401 X Y Z W a b r = ((1:ℚ):ℂ)*(r 503) + (((-1:ℚ):ℂ)*(rhsPivot156 X Y Z W a b r) + ((-(X*(Y⁻¹^2)))*(rhsPivot194 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot260 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*b)*W⁻¹))*(rhsPivot277 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot307 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X^2)))*(rhsPivot310 X Y Z W a b r) + ((-((W*b)*(Y⁻¹^2)))*(rhsPivot331 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*W)*b)*(Y⁻¹^2)))*(rhsPivot335 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot355 X Y Z W a b r) + ((-((W⁻¹^2)+((((-1:ℚ):ℂ)*(Y^2))*(W⁻¹^2))))*(rhsPivot358 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot384 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot401
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot402 X Y Z W a b r = ((1:ℚ):ℂ)*(r 505) + (((-1:ℚ):ℂ)*(rhsPivot29 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot167 X Y Z W a b r) + ((-(X*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot189 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot205 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*((Y⁻¹^2)*(W⁻¹^2)))+((((-1:ℚ):ℂ)*X)*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*((Y⁻¹^2)*(W⁻¹^2))))*(rhsPivot257 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot277 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(W^2))*(Y⁻¹^2)))*(rhsPivot331 X Y Z W a b r) + ((-((W^2)*(Y⁻¹^2)))*(rhsPivot335 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*b)*W⁻¹))*(rhsPivot358 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot373 X Y Z W a b r) + ((0:ℂ)))))))))))))
    unfold rhsPivot402
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot403 X Y Z W a b r = ((1:ℚ):ℂ)*(r 506) + (((-1:ℚ):ℂ)*(rhsPivot15 X Y Z W a b r) + ((-(W⁻¹^2))*(rhsPivot27 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot158 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*b)*W⁻¹))*(rhsPivot233 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot309 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot310 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot331 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot335 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot355 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*(Y^2))*(X⁻¹*(W⁻¹^2))))*(rhsPivot358 X Y Z W a b r) + ((0:ℂ))))))))))))
    unfold rhsPivot403
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot404 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 220) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot3 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot4 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot9 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot10 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot13 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot15 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot26 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot27 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot39 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot55 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot77 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot91 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot110 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot121 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot150 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot159 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot166 X Y Z W a b r) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot189 X Y Z W a b r) + (((-(W⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot194 X Y Z W a b r) + (((-(((2:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot195 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot200 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot230 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot231 X Y Z W a b r) + (((-(X⁻¹*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot232 X Y Z W a b r) + (((-(((2:ℚ):ℂ)*(X⁻¹*(W⁻¹^2))))*((-1:ℚ):ℂ))*(rhsPivot235 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot261 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot275 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot281 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot300 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot320 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot324 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot335 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot336 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot339 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot342 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot347 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot352 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*((-1:ℚ):ℂ))*(rhsPivot357 X Y Z W a b r) + (((-(((((-1:ℚ):ℂ)*X)*(Y^2))*(W⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot358 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot364 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot365 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot403 X Y Z W a b r) + ((0:ℂ))))))))))))))))))))))))))))))))))))))))))))
    unfold rhsPivot404
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot405 X Y Z W a b r = ((1:ℚ):ℂ)*(r 420) + (((-1:ℚ):ℂ)*(rhsPivot129 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*((Y⁻¹^2)*Z⁻¹)))*(rhsPivot130 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot153 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*Y)*a)*(X⁻¹*(W⁻¹^2))))*(rhsPivot205 X Y Z W a b r) + ((-((a*((X⁻¹*Y⁻¹)*(W⁻¹^2)))+((Y*a)*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + ((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*(rhsPivot232 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot300 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot315 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot331 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot335 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot356 X Y Z W a b r) + ((-((Y^2)*(X⁻¹*(W⁻¹^2))))*(rhsPivot358 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(rhsPivot404 X Y Z W a b r) + ((0:ℂ)))))))))))))))
    unfold rhsPivot405
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot406 X Y Z W a b r = ((-1:ℚ):ℂ)*(r 439) + (((1:ℚ):ℂ)*(rhsPivot213 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*((-1:ℚ):ℂ))*(rhsPivot214 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot223 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot333 X Y Z W a b r) + (((-(a*Y⁻¹))*((-1:ℚ):ℂ))*(rhsPivot342 X Y Z W a b r) + (((1:ℚ):ℂ)*(rhsPivot362 X Y Z W a b r) + (((-(Y⁻¹^2))*((-1:ℚ):ℂ))*(rhsPivot364 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot401 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*((-1:ℚ):ℂ))*(rhsPivot403 X Y Z W a b r) + ((0:ℂ)))))))))))
    unfold rhsPivot406
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot407 X Y Z W a b r = ((1:ℚ):ℂ)*(r 440) + (((-1:ℚ):ℂ)*(rhsPivot342 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot346 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot360 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot403 X Y Z W a b r) + ((0:ℂ))))))
    unfold rhsPivot407
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot408 X Y Z W a b r = ((1:ℚ):ℂ)*(r 484) + (((-1:ℚ):ℂ)*(rhsPivot125 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot201 X Y Z W a b r) + ((-(X⁻¹*(Y⁻¹^2)))*(rhsPivot224 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(Y⁻¹^2)))*(rhsPivot274 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot278 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*(X⁻¹*(Y⁻¹^2))))*(rhsPivot310 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot321 X Y Z W a b r) + ((-X)*(rhsPivot322 X Y Z W a b r) + ((-(a*(X⁻¹*Y⁻¹)))*(rhsPivot346 X Y Z W a b r) + ((-(a*Y⁻¹))*(rhsPivot353 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*((X⁻¹^3)*(Y⁻¹^2))))*(rhsPivot355 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*((X⁻¹^3)*(W⁻¹^2)))+((((-1:ℚ):ℂ)*X)*(W⁻¹^2))))*(rhsPivot358 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X⁻¹))*(rhsPivot403 X Y Z W a b r) + ((0:ℂ)))))))))))))))
    unfold rhsPivot408
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot409 X Y Z W a b r = X*(r 511) + ((((-1:ℚ):ℂ)*X)*(rhsPivot42 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot90 X Y Z W a b r) + (((-(W⁻¹^2))*X)*(rhsPivot105 X Y Z W a b r) + (((-((X⁻¹*(Y⁻¹^2))*(W⁻¹^2)))*X)*(rhsPivot195 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot218 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*((X⁻¹*(Y⁻¹^2))*(W⁻¹^2))))*X)*(rhsPivot230 X Y Z W a b r) + (X*(rhsPivot245 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot266 X Y Z W a b r) + ((((-1:ℚ):ℂ)*X)*(rhsPivot289 X Y Z W a b r) + (((-((((-1:ℚ):ℂ)*b)*W⁻¹))*X)*(rhsPivot317 X Y Z W a b r) + (((-(b*W⁻¹))*X)*(rhsPivot330 X Y Z W a b r) + (((-((W^2)*(X⁻¹*(Y⁻¹^2))))*X)*(rhsPivot335 X Y Z W a b r) + (X*(rhsPivot350 X Y Z W a b r) + (((-((Y^2)*(X⁻¹*(W⁻¹^2))))*X)*(rhsPivot358 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*X)*(rhsPivot370 X Y Z W a b r) + (((-(((-1:ℚ):ℂ)*X⁻¹))*X)*(rhsPivot381 X Y Z W a b r) + (X*(rhsPivot392 X Y Z W a b r) + ((0:ℂ)))))))))))))))))))
    unfold rhsPivot409
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
  · change rhsPivot410 X Y Z W a b r = ((1:ℚ):ℂ)*(r 419) + (((-1:ℚ):ℂ)*(rhsPivot70 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*a)*Y⁻¹))*(rhsPivot127 X Y Z W a b r) + ((-(((((-1:ℚ):ℂ)*X)*a)*(Y⁻¹*(W⁻¹^2))))*(rhsPivot198 X Y Z W a b r) + (((-1:ℚ):ℂ)*(rhsPivot203 X Y Z W a b r) + ((-(a*(Y⁻¹*(W⁻¹^2))))*(rhsPivot230 X Y Z W a b r) + ((-(Y⁻¹^2))*(rhsPivot302 X Y Z W a b r) + ((-((((-1:ℚ):ℂ)*X)*(W⁻¹^2)))*(rhsPivot358 X Y Z W a b r) + ((-(((-1:ℚ):ℂ)*X))*(rhsPivot409 X Y Z W a b r) + ((0:ℂ))))))))))
    unfold rhsPivot410
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, neg_inv, inv_pow]
    ring
#print axioms recurrence
end QuantitativeArithmeticCompact34MMMRecurrence
