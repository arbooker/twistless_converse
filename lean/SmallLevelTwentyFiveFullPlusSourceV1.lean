module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentTheoryV4

/-! Input rows alone, without importing the large elimination tables. The
original leading-row source has this same definition; keeping the small input
interface separate prevents certificate consumers from loading the elimination
proof merely to obtain its input rows. -/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace SmallLevelTwentyFiveFullPlusSource
open QuantitativeArithmeticSevenLaurentRows
def gaugeCoordinates : List ℕ := [34,52,58,76,116,162,166,172,174,186,216,234,264,278,282,332,342,348,354,365,386,396,402,408,410,426,444,474,572,576,580,598,606,624,626,634,642,646,648,664,694,696,706,718,724,732,740,772,778,786,792,794,796,824,834,838,842,848,864,876,878,888,902,914,944,992,998,1016]
def source (i : ℕ) : Poly := if i<4450 then QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent.source i else [(1,gaugeCoordinates.getD (i-4450) 0,(0,0,0,0,0,0,0))]
end SmallLevelTwentyFiveFullPlusSource
end
