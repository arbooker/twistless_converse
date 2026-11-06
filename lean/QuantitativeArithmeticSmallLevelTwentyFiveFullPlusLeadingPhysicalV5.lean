module
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import QuantitativeArithmeticKernelRangeCommandsV4

public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModelTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveCuspPlusLaurentTheoryV4
public meta import QuantitativeArithmeticFiniteRangeCommandsV4

public import QuantitativeArithmeticSmallLevelTwentyFiveFullPlusLeadingTriangularDataV5

set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
section
/-! ## QuantitativeArithmeticCompact25SharedLeadingDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section

/-! Shared data for the data table of the level-25 elimination certificate. -/
namespace QuantitativeArithmeticSmallLevelTwentyFive.FullPlusLeading
open QuantitativeArithmeticSevenLaurentRows

compact_certificate def gaugeCoordinates : List ℕ := [34,52,58,76,116,162,166,172,174,186,216,234,264,278,282,332,342,348,354,365,386,396,402,408,410,426,444,474,572,576,580,598,606,624,626,634,642,646,648,664,694,696,706,718,724,732,740,772,778,786,792,794,796,824,834,838,842,848,864,876,878,888,902,914,944,992,998,1016]

compact_certificate def source (i : ℕ) : Poly := if i<4450 then QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent.source i else [(1,gaugeCoordinates.getD (i-4450) 0,(0,0,0,0,0,0,0))]

compact_certificate def normal (i : ℕ) : Poly := match i/16 with
  | 0 => normalPart0 (i%16)
  | 1 => normalPart1 (i%16)
  | 2 => normalPart2 (i%16)
  | 3 => normalPart3 (i%16)
  | 4 => normalPart4 (i%16)
  | 5 => normalPart5 (i%16)
  | 6 => normalPart6 (i%16)
  | 7 => normalPart7 (i%16)
  | 8 => normalPart8 (i%16)
  | 9 => normalPart9 (i%16)
  | 10 => normalPart10 (i%16)
  | 11 => normalPart11 (i%16)
  | 12 => normalPart12 (i%16)
  | 13 => normalPart13 (i%16)
  | 14 => normalPart14 (i%16)
  | 15 => normalPart15 (i%16)
  | 16 => normalPart16 (i%16)
  | 17 => normalPart17 (i%16)
  | 18 => normalPart18 (i%16)
  | 19 => normalPart19 (i%16)
  | 20 => normalPart20 (i%16)
  | 21 => normalPart21 (i%16)
  | 22 => normalPart22 (i%16)
  | 23 => normalPart23 (i%16)
  | 24 => normalPart24 (i%16)
  | 25 => normalPart25 (i%16)
  | 26 => normalPart26 (i%16)
  | 27 => normalPart27 (i%16)
  | 28 => normalPart28 (i%16)
  | 29 => normalPart29 (i%16)
  | 30 => normalPart30 (i%16)
  | 31 => normalPart31 (i%16)
  | 32 => normalPart32 (i%16)
  | 33 => normalPart33 (i%16)
  | 34 => normalPart34 (i%16)
  | 35 => normalPart35 (i%16)
  | 36 => normalPart36 (i%16)
  | 37 => normalPart37 (i%16)
  | 38 => normalPart38 (i%16)
  | 39 => normalPart39 (i%16)
  | 40 => normalPart40 (i%16)
  | 41 => normalPart41 (i%16)
  | 42 => normalPart42 (i%16)
  | 43 => normalPart43 (i%16)
  | 44 => normalPart44 (i%16)
  | 45 => normalPart45 (i%16)
  | 46 => normalPart46 (i%16)
  | 47 => normalPart47 (i%16)
  | 48 => normalPart48 (i%16)
  | 49 => normalPart49 (i%16)
  | 50 => normalPart50 (i%16)
  | 51 => normalPart51 (i%16)
  | 52 => normalPart52 (i%16)
  | 53 => normalPart53 (i%16)
  | 54 => normalPart54 (i%16)
  | 55 => normalPart55 (i%16)
  | 56 => normalPart56 (i%16)
  | 57 => normalPart57 (i%16)
  | 58 => normalPart58 (i%16)
  | 59 => normalPart59 (i%16)
  | 60 => normalPart60 (i%16)
  | 61 => normalPart61 (i%16)
  | 62 => normalPart62 (i%16)
  | 63 => normalPart63 (i%16)
  | 64 => normalPart64 (i%16)
  | 65 => normalPart65 (i%16)
  | _ => []

compact_certificate def operations (i : ℕ) : Poly := match i/16 with
  | 0 => operationsPart0 (i%16)
  | 1 => operationsPart1 (i%16)
  | 2 => operationsPart2 (i%16)
  | 3 => operationsPart3 (i%16)
  | 4 => operationsPart4 (i%16)
  | 5 => operationsPart5 (i%16)
  | 6 => operationsPart6 (i%16)
  | 7 => operationsPart7 (i%16)
  | 8 => operationsPart8 (i%16)
  | 9 => operationsPart9 (i%16)
  | 10 => operationsPart10 (i%16)
  | 11 => operationsPart11 (i%16)
  | 12 => operationsPart12 (i%16)
  | 13 => operationsPart13 (i%16)
  | 14 => operationsPart14 (i%16)
  | 15 => operationsPart15 (i%16)
  | 16 => operationsPart16 (i%16)
  | 17 => operationsPart17 (i%16)
  | 18 => operationsPart18 (i%16)
  | 19 => operationsPart19 (i%16)
  | 20 => operationsPart20 (i%16)
  | 21 => operationsPart21 (i%16)
  | 22 => operationsPart22 (i%16)
  | 23 => operationsPart23 (i%16)
  | 24 => operationsPart24 (i%16)
  | 25 => operationsPart25 (i%16)
  | 26 => operationsPart26 (i%16)
  | 27 => operationsPart27 (i%16)
  | 28 => operationsPart28 (i%16)
  | 29 => operationsPart29 (i%16)
  | 30 => operationsPart30 (i%16)
  | 31 => operationsPart31 (i%16)
  | 32 => operationsPart32 (i%16)
  | 33 => operationsPart33 (i%16)
  | 34 => operationsPart34 (i%16)
  | 35 => operationsPart35 (i%16)
  | 36 => operationsPart36 (i%16)
  | 37 => operationsPart37 (i%16)
  | 38 => operationsPart38 (i%16)
  | 39 => operationsPart39 (i%16)
  | 40 => operationsPart40 (i%16)
  | 41 => operationsPart41 (i%16)
  | 42 => operationsPart42 (i%16)
  | 43 => operationsPart43 (i%16)
  | 44 => operationsPart44 (i%16)
  | 45 => operationsPart45 (i%16)
  | 46 => operationsPart46 (i%16)
  | 47 => operationsPart47 (i%16)
  | 48 => operationsPart48 (i%16)
  | 49 => operationsPart49 (i%16)
  | 50 => operationsPart50 (i%16)
  | 51 => operationsPart51 (i%16)
  | 52 => operationsPart52 (i%16)
  | 53 => operationsPart53 (i%16)
  | 54 => operationsPart54 (i%16)
  | 55 => operationsPart55 (i%16)
  | 56 => operationsPart56 (i%16)
  | 57 => operationsPart57 (i%16)
  | 58 => operationsPart58 (i%16)
  | 59 => operationsPart59 (i%16)
  | 60 => operationsPart60 (i%16)
  | 61 => operationsPart61 (i%16)
  | 62 => operationsPart62 (i%16)
  | 63 => operationsPart63 (i%16)
  | 64 => operationsPart64 (i%16)
  | 65 => operationsPart65 (i%16)
  | _ => []

compact_certificate def triTail (i : ℕ) : Poly := match i/16 with
  | 0 => triTailPart0 (i%16)
  | 1 => triTailPart1 (i%16)
  | 2 => triTailPart2 (i%16)
  | 3 => triTailPart3 (i%16)
  | 4 => triTailPart4 (i%16)
  | 5 => triTailPart5 (i%16)
  | 6 => triTailPart6 (i%16)
  | 7 => triTailPart7 (i%16)
  | 8 => triTailPart8 (i%16)
  | 9 => triTailPart9 (i%16)
  | 10 => triTailPart10 (i%16)
  | 11 => triTailPart11 (i%16)
  | 12 => triTailPart12 (i%16)
  | 13 => triTailPart13 (i%16)
  | 14 => triTailPart14 (i%16)
  | 15 => triTailPart15 (i%16)
  | 16 => triTailPart16 (i%16)
  | 17 => triTailPart17 (i%16)
  | 18 => triTailPart18 (i%16)
  | 19 => triTailPart19 (i%16)
  | 20 => triTailPart20 (i%16)
  | 21 => triTailPart21 (i%16)
  | 22 => triTailPart22 (i%16)
  | 23 => triTailPart23 (i%16)
  | 24 => triTailPart24 (i%16)
  | 25 => triTailPart25 (i%16)
  | 26 => triTailPart26 (i%16)
  | 27 => triTailPart27 (i%16)
  | 28 => triTailPart28 (i%16)
  | 29 => triTailPart29 (i%16)
  | 30 => triTailPart30 (i%16)
  | 31 => triTailPart31 (i%16)
  | 32 => triTailPart32 (i%16)
  | 33 => triTailPart33 (i%16)
  | 34 => triTailPart34 (i%16)
  | 35 => triTailPart35 (i%16)
  | 36 => triTailPart36 (i%16)
  | 37 => triTailPart37 (i%16)
  | 38 => triTailPart38 (i%16)
  | 39 => triTailPart39 (i%16)
  | 40 => triTailPart40 (i%16)
  | 41 => triTailPart41 (i%16)
  | 42 => triTailPart42 (i%16)
  | 43 => triTailPart43 (i%16)
  | 44 => triTailPart44 (i%16)
  | 45 => triTailPart45 (i%16)
  | 46 => triTailPart46 (i%16)
  | 47 => triTailPart47 (i%16)
  | 48 => triTailPart48 (i%16)
  | 49 => triTailPart49 (i%16)
  | 50 => triTailPart50 (i%16)
  | 51 => triTailPart51 (i%16)
  | 52 => triTailPart52 (i%16)
  | 53 => triTailPart53 (i%16)
  | 54 => triTailPart54 (i%16)
  | 55 => triTailPart55 (i%16)
  | 56 => triTailPart56 (i%16)
  | 57 => triTailPart57 (i%16)
  | 58 => triTailPart58 (i%16)
  | 59 => triTailPart59 (i%16)
  | 60 => triTailPart60 (i%16)
  | 61 => triTailPart61 (i%16)
  | 62 => triTailPart62 (i%16)
  | 63 => triTailPart63 (i%16)
  | 64 => triTailPart64 (i%16)
  | 65 => triTailPart65 (i%16)
  | _ => []

compact_certificate def coordinates : List ℕ := [546,39,966,1029,518,0,525,550,1,2,3,4,6,7,12,14,528,21,42,532,1008,504,543,1036,28,84,548,969,963,1022,1038,1043,522,1044,1046,1047,1048,1049,500,524,526,81,1011,87,502,507,34,52,58,76,116,162,166,172,174,186,216,234,264,789,278,282,332,342,348,612,354,365,386,396,402,408,758,410,426,444,474,572,576,580,598,606,324,624,626,634,642,646,648,687,664,691,857,694,696,699,873,706,718,724,732,740,772,193,778,786,261,792,794,796,824,834,838,842,848,864,876,878,888,726,363,902,914,944,419,992,292,998,1016,970,972,973,975,978,980,984,987,483,497,1015,534,537,539,540,542,544,545,547,549,552,553,555,558,560,564,567,574,917,588,595,938,945,948,952,954,957,959,960,962,24,30,33,35,36,38,40,1034,1035,529,530,531,1026,1032,1033,5,9,10,15,18,20,25,105,210,875,45,49,50,60,63,70,75,90,98,100,126,140,147,150,175,805,825,225,245,900,903,910,924,420,950,450,490,462,990,1000,1001,1005,968,964,965,967,1014,510,1020,1025,1030,1040,1041,1045,570,600,476,480,516,520,29,469,511,514,517,519,56,26,27,82,1010,1009,44,994,1006,41,48,66,72,77,78,80,83,85,86,88,91,93,96,102,112,455,133,486,492,495,1002,498,501,46,503,505,506,508,513,22,1028,43,51,54,996,999,1004,1007,1012,1017,1023,1024,533,536,581,1021,13,515,535,16,350,349,698,704,346,280,700,176,874,252,798,651,569,777,253,267,273,389,921,399,19,437,481,422,628,701,352,707,343,364,686,728,322,840,212,208,636,204,882,168,315,735,192,770,385,665,714,336,182,868,527,378,11,554,120,870,170,561,563,156,180,930,880,583,73,608,613,99,117,657,139,171,173,351,181,723,199,201,741,747,231,783,259,787,263,791,271,797,807,819,299,303,831,309,313,317,321,323,849,353,359,890,911,393,937,421,949,438,439,457,997,473,894,489,491,1031,1039,523,356,368,374,376,736,760,428,262,788,94,466,148,157,164,866,872,178,886,893,214,314,682,341,344,654,244,586,596,816,774,276,614,355,695,710,340,370,680,725,325,749,301,400,650,209,844,206,852,828,228,861,189,456,384,270,780,693,357,720,330,200,850,104,312,742,308,130,906,144,74,609,441,538,23,750,559,565,566,568,47,414,55,585,591,300,196,601,607,610,615,616,101,627,633,109,111,641,645,121,123,129,131,658,661,137,663,141,143,145,671,675,153,169,177,179,183,711,205,737,215,219,854,233,759,761,237,765,243,247,773,775,251,257,785,265,793,269,799,275,277,803,285,811,813,815,817,829,307,858,339,867,871,347,877,879,887,369,375,377,379,387,913,392,919,927,405,933,935,417,423,434,435,961,440,442,443,445,447,448,451,977,461,465,467,238,847,479,482,484,485,487,1013,496,1027,982,703,709,712,713,715,729,388,739,856,390,394,602,752,188,406,427,784,436,89,266,808,118,826,134,836,224,512,1042,184,194,898,202,916,229,230,932,584,592,611,622,623,640,644,298,674,326,688,17,248,57,908,138,912,618,125,128,762,782,372,124,211,411,812,660,810,240,690,830,305,345,106,114,936,920,154,896,766,287,763,678,288,684,460,119,380,721,108,132,571,822,577,579,1018,692,521,593,71,603,79,605,801,619,582,107,637,113,647,655,659,151,677,681,683,161,371,689,167,191,800,432,931,203,413,904,733,217,846,468,743,745,221,223,250,329,753,757,235,239,767,769,779,255,795,809,827,835,841,853,859,335,863,883,889,367,899,381,907,915,397,923,925,401,403,415,941,947,425,955,258,971,453,463,989,475,1003,918,459,1019,499,1037,358,260,32,679,470,833,160,865,185,575,454,625,744,594,804,279,291,901,310,673,942,334,697,638,256,61,62,286,716,928,122,934,146,754,404,398,306,734,656,198,748,207,939,361,722,818,293,617,976,666,424,274,64,814,464,272,412,587,430,213,837,620,855,195,885,705,165,320,304,246,891,590,702,135,294,860,790,670,37,599,635,127,155,281,851,391,429,431,995,477,730,220,820,190,940,290,395,110,845,755,905,985,65,95,115,685,295,895,869,652,318,226,573,254,884,922,297,382,366,946,768,708,986,676,236,541,551,31,557,897,59,668,881,69,597,249,649,669,92,621,97,149,159,327,187,197,929,771,283,311,839,331,337,909,409,951,981,983,991,993,333,509,218,319,746,446,764,802,103,632,284,494,478,832,958,316,328,604,158,458,727,892,926,776,719,493,296,639,578,142,562,471,988,268,53,631,667,289,823,407,241,953,662,362,136,556,416,731,242,67,821,452,751,222,974,472,643,433,338,589,781,862,653,488,738,717,806,449,232,956,152,302,163,843,373,68,979,383,227,418,943,629,8,360,630,672,756]

compact_certificate def coordinate (i : ℕ) : ℕ := coordinates.getD i 0

compact_certificate def positions : List ℕ := [5,8,9,10,11,184,12,13,1045,185,186,362,14,306,15,187,309,670,188,330,189,17,289,501,169,190,251,252,24,244,170,930,805,171,46,172,173,881,174,1,175,259,18,291,256,194,283,507,260,195,196,292,47,997,293,509,250,672,48,933,197,828,829,198,855,905,261,1012,1038,936,199,719,262,374,497,200,49,263,264,721,265,41,253,266,25,267,268,43,269,641,201,270,941,271,437,906,272,943,202,377,203,519,273,971,490,191,693,726,709,522,900,523,274,728,694,907,50,378,644,706,364,526,833,527,682,677,204,884,678,528,494,529,710,276,646,876,1007,532,674,380,205,534,992,535,496,536,835,206,439,944,207,732,1033,539,697,885,369,440,981,945,809,736,51,1035,441,869,52,739,349,540,366,381,53,382,54,208,317,541,444,542,370,384,358,543,651,811,55,947,636,479,896,740,352,103,652,866,513,948,842,386,488,387,654,744,347,545,474,844,345,472,192,683,344,862,447,547,56,748,965,548,894,753,1016,754,648,211,914,1041,477,656,657,390,1031,550,57,759,927,553,612,760,688,1003,1011,555,453,212,872,556,671,938,755,559,319,324,916,764,827,560,791,392,804,106,435,394,58,562,642,325,996,564,482,396,858,326,854,566,458,567,60,818,315,886,61,951,973,569,830,700,703,1000,898,819,126,849,877,909,989,919,666,400,512,469,1034,401,871,691,839,575,493,403,821,952,491,404,448,350,978,405,913,966,870,406,342,407,82,467,668,946,979,756,487,954,62,963,824,772,357,955,1021,577,463,450,63,338,451,692,314,580,64,311,310,383,336,409,66,460,428,485,803,410,1046,846,1006,120,339,67,921,776,429,584,464,737,681,1037,430,585,431,586,361,587,707,778,920,1040,481,354,68,588,629,327,632,888,590,413,633,899,69,781,838,329,470,784,70,785,837,593,637,1002,71,957,73,684,859,745,508,786,1009,596,1042,124,217,415,333,597,853,789,74,638,434,889,861,890,742,1020,598,599,640,331,417,418,601,499,602,603,75,604,968,605,606,1030,219,607,1014,793,813,275,480,419,982,799,705,609,221,794,857,610,438,611,750,245,807,994,1018,421,76,796,240,892,975,614,241,332,615,137,616,617,277,618,1026,423,220,424,278,988,974,279,620,138,281,801,38,282,44,284,21,285,286,45,287,964,231,246,649,288,247,307,242,248,4,249,243,717,32,427,39,6,40,360,16,178,179,180,19,302,140,308,303,141,500,142,143,928,144,22,145,146,0,147,26,148,7,929,149,150,363,151,1008,931,152,503,153,367,993,368,154,504,505,155,506,322,238,711,77,915,156,812,78,713,991,714,79,304,725,373,659,510,454,860,158,1022,874,511,660,718,816,159,455,937,80,882,239,514,634,720,980,722,81,515,375,498,516,661,65,376,459,517,518,850,676,724,864,942,662,663,83,814,84,520,334,1044,1047,998,972,521,85,883,346,727,826,990,664,524,86,1019,665,525,87,729,88,939,471,321,912,1025,452,730,841,379,530,731,686,531,1005,533,90,355,852,999,934,940,880,537,1048,822,667,538,926,733,702,806,465,734,449,735,704,908,340,89,669,738,689,91,716,484,93,461,94,825,312,95,316,335,875,623,313,868,97,337,924,624,462,544,625,626,356,627,831,1028,98,987,486,708,847,385,99,466,119,983,341,628,893,1010,100,747,840,351,432,546,1027,630,101,388,492,751,815,752,967,389,843,468,502,1015,635,757,836,902,1049,758,72,551,433,552,679,701,969,554,699,761,923,762,353,950,102,557,457,558,986,323,104,763,483,1023,680,391,639,561,105,393,436,59,879,395,107,563,108,765,109,397,320,565,741,723,970,568,817,209,1029,398,643,766,687,570,685,571,856,572,456,573,848,399,895,1013,712,1001,110,210,645,767,476,574,690,402,976,808,111,768,647,863,112,953,343,769,113,1036,473,901,749,613,114,408,489,887,475,770,549,865,631,92,576,771,878,478,1024,773,115,810,442,578,359,911,365,579,443,96,318,193,116,581,117,582,372,935,348,774,917,867,445,583,118,775,411,873,984,446,422,910,698,932,653,777,213,820,121,214,746,903,495,779,673,956,215,412,675,589,122,780,655,157,798,591,696,328,918,782,216,783,985,592,832,949,371,743,658,594,834,595,695,414,160,845,897,787,823,1043,123,161,922,788,162,416,218,958,163,1004,164,790,1032,165,977,166,167,600,168,28,227,228,2,229,226,27,129,792,130,131,1017,132,851,608,133,1039,134,959,622,960,135,904,925,136,995,795,222,961,125,962,257,891,294,420,127,295,223,224,280,797,296,225,258,297,20,255,254,42,298,619,230,139,128,299,715,800,232,305,29,300,301,233,181,621,290,3,234,425,182,183,176,177,23,802,30,426,235,236,650,31,33,237,34,35,36,37]

compact_certificate def position (i : ℕ) : ℕ := positions.getD i 0

end QuantitativeArithmeticSmallLevelTwentyFive.FullPlusLeading
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveFullPlusLeadingPhysicalV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FullPlusLeading
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate theorem all_physical_flag : ∀ i : Fin 4450,
    CuspPlusLaurent.physicalFlag (AuxPlusLaurent.actual i.val)=true := by
  let P : ℕ → Prop := fun i => CuspPlusLaurent.physicalFlag (AuxPlusLaurent.actual i)=true
  have hFin : ∀ i : Fin 4450, P i.val := kernel_range% P 4450 block 64
  have h : ∀ i<4450, P (i+0) := fun i hi => hFin ⟨i,hi⟩
  intro i
  exact h i.val i.isLt

compact_certificate theorem source_physical (i : Fin 4450) : AuxPlusLaurent.actual i.val=
    .physical (CuspPlusLaurent.physicalPart (AuxPlusLaurent.actual i.val)) :=
  CuspPlusLaurent.physicalPart_eq _ (all_physical_flag i)

compact_certificate theorem gauge_coordinate (i : Fin 68) : gaugeCoordinates.getD i.val 0=
    (AuxPlusLaurent.freeCoordinate i).val := by
  revert i
  decide +kernel

#print axioms all_physical_flag
#print axioms source_physical
#print axioms gauge_coordinate
end QuantitativeArithmeticSmallLevelTwentyFive.FullPlusLeading
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveFullPlusLeadingPoleRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FullPlusLeading
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector

/- The 4518 source equations follow from the original positive-phase
hypotheses and the canonical gauge, with a simple weight pole allowed. -/
compact_certificate theorem original_pole_rows_allowed
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=1) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge AuxPlusLaurent.basis
      AuxPlusLaurent.freeCoordinate m f z (gridVector 1050 (2*m) f z))
    (s : ℂ) (v : Fin 1050 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ,0<n → (s+n)≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hweight : ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)) :
    ∀ i<4518, eval (primeParameter 2 m s) (primeParameter 3 m s)
      (primeParameter 5 m s) (primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
      (periodicVector v) (source i)=0 := by
  intro i hi
  by_cases hip : i<4450
  · have hr := source_physical ⟨i,hip⟩
    have hp := AuxPlusLaurent.all_actual_source ⟨i,by omega⟩
    have hq := AuxPlusLaurent.all_actual_tail ⟨i,by omega⟩
    rw [hr] at hp hq
    have hl := physical_leading_pole_allowed AuxPlusLaurent.basis AuxPlusLaurent.freeCoordinate
      AuxPlusLaurent.basis_periodic (CuspPlusLaurent.physicalPart (AuxPlusLaurent.actual i)) 1
      (AuxPlusLaurent.source i) (AuxPlusLaurent.tail i) hp hq
      (AuxPlusLaurent.all_source_zero ⟨i,by omega⟩) (AuxPlusLaurent.all_tail_zero ⟨i,by omega⟩)
      hm hf ε hε hlaw (by simpa using hχ) BG G hG hGF s v hv hshift hweight
    have hn (p : ℕ) (hp0 : p≠0) : primeParameter p m s≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp0))
    have he := eval_rawSourcePoly
      (.physical (CuspPlusLaurent.physicalPart (AuxPlusLaurent.actual i))) hf ε s 1
      (by simpa using hχ) v
    rw [← eval_normalizedPoly _ _ _ _ _ _ _ _ (hn 2 (by decide)) (hn 3 (by decide))
      (hn 5 (by decide)) (hn 7 (by decide)),hp] at he
    simpa only [source,ite_eq_left hip,sourceLeading] using he.trans hl
  · have hj : i-4450<68 := by omega
    have hg := continued_free_zero AuxPlusLaurent.basis AuxPlusLaurent.freeCoordinate
      AuxPlusLaurent.basis_free_coordinate m f BG G hG hGF
    have hfree : v (AuxPlusLaurent.freeCoordinate ⟨i-4450,hj⟩)=0 := by
      classical
      have h := hv.2 (fun _ t => if t=AuxPlusLaurent.freeCoordinate ⟨i-4450,hj⟩ then 1 else 0)
        (fun _ => 0) (fun _ => analyticAt_const) analyticAt_const (by
          filter_upwards [] with z
          simp [hg])
      simpa using h
    simp only [source,ite_eq_right hip,eval,monomial,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,Rat.cast_one,zpow_zero,pow_zero,mul_one,one_mul,add_zero]
    rw [gauge_coordinate ⟨i-4450,hj⟩,periodicVector_fin]
    exact hfree

#print axioms original_pole_rows_allowed
end QuantitativeArithmeticSmallLevelTwentyFive.FullPlusLeading
end
end
end

