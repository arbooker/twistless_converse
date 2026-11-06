module

public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenFourthFlatIntegerTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenFourthNormalizedSourceModelV1
public import QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamilyTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily.Plus. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenFourthPlusNormalizerDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily.Plus
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages (primeRate primeRate_analytic primeRate_nonzero)
def normalizerData : ℕ → ℚ × (ℤ × ℤ × ℤ × ℤ)
  | 0 => ((2/4782969:ℚ),(0,6,0,0))
  | 1 => ((16/1:ℚ),(0,0,0,0))
  | 2 => ((5000/531441:ℚ),(0,4,0,0))
  | 3 => ((-8/531441:ℚ),(0,4,0,0))
  | 4 => ((1/38263752:ℚ),(2,6,0,0))
  | 5 => ((64/4100625:ℚ),(0,2,2,0))
  | 6 => ((1/282429536481:ℚ),(0,6,0,0))
  | 7 => ((8/332150625:ℚ),(0,4,2,0))
  | 8 => ((-1/16:ℚ),(2,0,0,0))
  | 9 => ((2/4782969:ℚ),(0,6,0,0))
  | 10 => ((128/531441:ℚ),(0,4,0,0))
  | 11 => ((5000/6561:ℚ),(0,2,0,0))
  | 12 => ((-1/129140163:ℚ),(0,6,0,0))
  | 13 => ((-625/28697814:ℚ),(2,4,0,0))
  | 14 => ((2/129140163:ℚ),(0,6,0,0))
  | 15 => ((-8/8968066875:ℚ),(0,4,2,0))
  | 16 => ((-1/2066242608:ℚ),(2,6,0,0))
  | 17 => ((625/26244:ℚ),(2,2,0,0))
  | 18 => ((8/531441:ℚ),(0,4,0,0))
  | 19 => ((1/9565938:ℚ),(2,6,0,0))
  | 20 => ((128/332150625:ℚ),(0,4,2,0))
  | 21 => ((1/282429536481:ℚ),(0,6,0,0))
  | 22 => ((-8/4100625:ℚ),(0,2,2,0))
  | 23 => ((-1/1062882:ℚ),(2,4,0,0))
  | 24 => ((2/4782969:ℚ),(0,6,0,0))
  | 25 => ((-1/4782969:ℚ),(0,6,0,0))
  | 26 => ((-1/4782969:ℚ),(0,6,0,0))
  | 27 => ((1/76527504:ℚ),(2,6,0,0))
  | 28 => ((-128/332150625:ℚ),(0,4,2,0))
  | 29 => ((-2/2989355625:ℚ),(0,6,2,0))
  | 30 => ((-1/8201250:ℚ),(2,2,2,0))
  | 31 => ((1/282429536481:ℚ),(0,6,0,0))
  | 32 => ((-1/5978711250:ℚ),(2,6,2,0))
  | 33 => ((4/332150625:ℚ),(0,4,2,0))
  | 34 => ((-1/1062882:ℚ),(2,4,0,0))
  | 35 => ((-2/4782969:ℚ),(0,6,0,0))
  | 36 => ((128/531441:ℚ),(0,4,0,0))
  | 37 => ((1/4782969:ℚ),(0,6,0,0))
  | 38 => ((-1/14946778125:ℚ),(0,6,2,0))
  | 39 => ((1/72301961339136:ℚ),(2,6,0,0))
  | 40 => ((-1/332150625:ℚ),(0,4,2,0))
  | 41 => ((-1/4782969:ℚ),(0,6,0,0))
  | 42 => ((128/531441:ℚ),(0,4,0,0))
  | 43 => ((2/4782969:ℚ),(0,6,0,0))
  | 44 => ((-1/1062882:ℚ),(2,4,0,0))
  | 45 => ((-128/14946778125:ℚ),(0,6,2,0))
  | 46 => ((-4/332150625:ℚ),(0,4,2,0))
  | 47 => ((1/282429536481:ℚ),(0,6,0,0))
  | 48 => ((-1/8201250:ℚ),(2,2,2,0))
  | 49 => ((-128/332150625:ℚ),(0,4,2,0))
  | 50 => ((-1/76527504:ℚ),(2,6,0,0))
  | 51 => ((2/129140163:ℚ),(0,6,0,0))
  | 52 => ((-1/16:ℚ),(2,0,0,0))
  | 53 => ((-1/17936133750:ℚ),(2,4,2,0))
  | 54 => ((-2/403563009375:ℚ),(0,6,2,0))
  | 55 => ((-1/2066242608:ℚ),(2,6,0,0))
  | 56 => ((5000/6561:ℚ),(0,2,0,0))
  | 57 => ((128/531441:ℚ),(0,4,0,0))
  | 58 => ((-1/16:ℚ),(2,0,0,0))
  | 59 => ((-8/332150625:ℚ),(0,4,2,0))
  | 60 => ((-1/664301250:ℚ),(2,4,2,0))
  | 61 => ((-64/4100625:ℚ),(0,2,2,0))
  | 62 => ((-1/38263752:ℚ),(2,6,0,0))
  | 63 => ((-8/531441:ℚ),(0,4,0,0))
  | 64 => ((-128/4782969:ℚ),(0,6,0,0))
  | 65 => ((-1/645700815000:ℚ),(2,6,2,0))
  | 66 => ((-1/76527504:ℚ),(2,6,0,0))
  | 67 => ((16/1:ℚ),(0,0,0,0))
  | 68 => ((16/1:ℚ),(0,0,0,0))
  | 69 => ((-8/8968066875:ℚ),(0,4,2,0))
  | 70 => ((-1/161425203750:ℚ),(2,6,2,0))
  | 71 => ((-2/129140163:ℚ),(0,6,0,0))
  | 72 => ((-1/17936133750:ℚ),(2,4,2,0))
  | 73 => ((-1/4782969:ℚ),(0,6,0,0))
  | 74 => ((1/4782969:ℚ),(0,6,0,0))
  | 75 => ((16/1:ℚ),(0,0,0,0))
  | 76 => ((-1/1062882:ℚ),(2,4,0,0))
  | 77 => ((-8/4100625:ℚ),(0,2,2,0))
  | 78 => ((-128/332150625:ℚ),(0,4,2,0))
  | 79 => ((-1/9565938:ℚ),(2,6,0,0))
  | 80 => ((8/531441:ℚ),(0,4,0,0))
  | 81 => ((-625/26244:ℚ),(2,2,0,0))
  | 82 => ((-1/332150625:ℚ),(0,4,2,0))
  | 83 => ((-1/2582803260000:ℚ),(2,6,2,0))
  | 84 => ((-625/531441:ℚ),(0,4,0,0))
  | 85 => ((1/1:ℚ),(0,0,0,0))
  | 86 => ((-1/8857350000:ℚ),(2,3,2,0))
  | 87 => ((-2/553584375:ℚ),(0,3,2,0))
  | 88 => ((8/4100625:ℚ),(0,4,2,0))
  | 89 => ((-8/4100625:ℚ),(0,3,2,0))
  | 90 => ((-1/303750:ℚ),(2,3,2,0))
  | 91 => ((-64/4100625:ℚ),(0,3,2,0))
  | 92 => ((-64/4100625:ℚ),(0,3,2,0))
  | 93 => ((1/13122:ℚ),(2,4,0,0))
  | 94 => ((-8/151875:ℚ),(0,3,2,0))
  | 95 => ((625/354294:ℚ),(2,6,0,0))
  | 96 => ((625/354294:ℚ),(2,6,0,0))
  | 97 => ((-1/1250:ℚ),(2,3,2,0))
  | 98 => ((-1/1250:ℚ),(2,3,2,0))
  | 99 => ((8/6561:ℚ),(0,4,0,0))
  | 100 => ((64/759375:ℚ),(0,2,2,0))
  | 101 => ((64/759375:ℚ),(0,2,2,0))
  | 102 => ((1/972:ℚ),(2,2,0,0))
  | 103 => ((1/972:ℚ),(2,2,0,0))
  | 104 => ((1250/177147:ℚ),(0,6,0,0))
  | 105 => ((1250/177147:ℚ),(0,6,0,0))
  | 106 => ((-2/625:ℚ),(0,3,2,0))
  | 107 => ((-2/625:ℚ),(0,3,2,0))
  | 108 => ((-64/6561:ℚ),(0,3,0,0))
  | 109 => ((-64/6561:ℚ),(0,3,0,0))
  | 110 => ((-125/26244:ℚ),(2,3,0,0))
  | 111 => ((-125/26244:ℚ),(2,3,0,0))
  | 112 => ((5000/6561:ℚ),(0,4,0,0))
  | 113 => ((5000/6561:ℚ),(0,4,0,0))
  | 114 => ((1/151875:ℚ),(0,2,2,0))
  | 115 => ((1/151875:ℚ),(0,2,2,0))
  | 116 => ((625/177147:ℚ),(0,6,0,0))
  | 117 => ((625/177147:ℚ),(0,6,0,0))
  | 118 => ((-1/625:ℚ),(0,3,2,0))
  | 119 => ((-1/625:ℚ),(0,3,2,0))
  | 120 => ((1/6561:ℚ),(0,2,0,0))
  | 121 => ((-8/50625:ℚ),(0,1,2,0))
  | 122 => ((-8/50625:ℚ),(0,1,2,0))
  | 123 => ((-1/1250:ℚ),(2,3,2,0))
  | 124 => ((-1/1250:ℚ),(2,3,2,0))
  | 125 => ((2/1594323:ℚ),(0,6,0,0))
  | 126 => ((2/1594323:ℚ),(0,6,0,0))
  | 127 => ((-64/50625:ℚ),(0,1,2,0))
  | 128 => ((-64/50625:ℚ),(0,1,2,0))
  | 129 => ((-1/162:ℚ),(2,1,0,0))
  | 130 => ((-1/162:ℚ),(2,1,0,0))
  | 131 => ((-8/625:ℚ),(0,3,2,0))
  | 132 => ((-8/625:ℚ),(0,3,2,0))
  | 133 => ((16/1594323:ℚ),(0,6,0,0))
  | 134 => ((-16/1594323:ℚ),(0,5,0,0))
  | 135 => ((-625/3188646:ℚ),(2,5,0,0))
  | 136 => ((625/3188646:ℚ),(2,6,0,0))
  | 137 => ((-1/11250:ℚ),(2,3,2,0))
  | 138 => ((-8/81:ℚ),(0,1,0,0))
  | 139 => ((-8/81:ℚ),(0,1,0,0))
  | 140 => ((-64/3125:ℚ),(0,3,2,0))
  | 141 => ((-64/3125:ℚ),(0,3,2,0))
  | 142 => ((1/4:ℚ),(2,0,0,0))
  | 143 => ((1/4:ℚ),(2,0,0,0))
  | 144 => ((-1250/1594323:ℚ),(0,5,0,0))
  | 145 => ((1250/1594323:ℚ),(0,6,0,0))
  | 146 => ((-2/5625:ℚ),(0,3,2,0))
  | 147 => ((2/5625:ℚ),(0,2,2,0))
  | 148 => ((-64/81:ℚ),(0,1,0,0))
  | 149 => ((-64/81:ℚ),(0,1,0,0))
  | 150 => ((625/324:ℚ),(2,4,0,0))
  | 151 => ((625/324:ℚ),(2,4,0,0))
  | 152 => ((8/1:ℚ),(0,0,0,0))
  | 153 => ((8/1:ℚ),(0,0,0,0))
  | 154 => ((1/144:ℚ),(2,2,0,0))
  | 155 => ((-1/144:ℚ),(2,3,0,0))
  | 156 => ((5000/81:ℚ),(0,4,0,0))
  | 157 => ((5000/81:ℚ),(0,4,0,0))
  | 158 => ((128/1:ℚ),(0,0,0,0))
  | 159 => ((128/1:ℚ),(0,0,0,0))
  | 160 => ((-2/9:ℚ),(0,3,0,0))
  | 161 => ((1/390625:ℚ),(0,0,2,0))
  | 162 => ((-1/354294:ℚ),(2,3,0,0))
  | 163 => ((-2/177147:ℚ),(0,3,0,0))
  | 164 => ((-1/13122:ℚ),(2,3,2,0))
  | 165 => ((1/13122:ℚ),(2,4,0,0))
  | 166 => ((-8/6561:ℚ),(0,3,0,0))
  | 167 => ((-8/6561:ℚ),(0,3,2,0))
  | 168 => ((1/1679616:ℚ),(2,2,0,0))
  | 169 => ((-1/50625:ℚ),(0,1,2,0))
  | 170 => ((-1/50625:ℚ),(0,1,2,0))
  | 171 => ((-1/1594323:ℚ),(0,5,0,0))
  | 172 => ((1/1594323:ℚ),(0,6,0,0))
  | 173 => ((-1/625:ℚ),(0,3,2,0))
  | 174 => ((-1/625:ℚ),(0,3,2,0))
  | 175 => ((-1/81:ℚ),(0,1,0,0))
  | 176 => ((-1/81:ℚ),(0,1,0,0))
  | 177 => ((625/1594323:ℚ),(0,6,0,0))
  | 178 => ((625/1594323:ℚ),(0,6,0,0))
  | 179 => ((-1/5625:ℚ),(0,3,2,0))
  | 180 => ((-1/5625:ℚ),(0,3,2,0))
  | 181 => ((625/81:ℚ),(0,4,0,0))
  | 182 => ((625/81:ℚ),(0,4,0,0))
  | 183 => ((-1/9:ℚ),(0,3,0,0))
  | 184 => ((1/9:ℚ),(0,2,0,0))
  | 185 => ((-1/76527504:ℚ),(2,6,0,0))
  | 186 => ((-1/76527504:ℚ),(2,6,0,0))
  | 187 => ((-2/3125:ℚ),(0,0,2,0))
  | 188 => ((-2/3125:ℚ),(0,0,2,0))
  | 189 => ((-1/36450000:ℚ),(2,4,2,0))
  | 190 => ((-16/3125:ℚ),(0,0,2,0))
  | 191 => ((-16/3125:ℚ),(0,0,2,0))
  | 192 => ((-2/2278125:ℚ),(0,4,2,0))
  | 193 => ((1/100000000:ℚ),(2,0,2,0))
  | 194 => ((-1/177147:ℚ),(0,3,0,0))
  | 195 => ((1/6561:ℚ),(0,4,2,0))
  | 196 => ((-8/81:ℚ),(0,1,0,0))
  | 197 => ((1/656100000000:ℚ),(2,2,2,0))
  | 198 => ((1/110324037687890625:ℚ),(2,6,2,0))
  | 199 => ((1/16815125390625:ℚ),(0,4,2,0))
  | 200 => ((1/16815125390625:ℚ),(2,4,2,0))
  | 201 => ((1/2562890625:ℚ),(1,2,2,0))
  | 202 => ((1/282429536481:ℚ),(2,6,0,0))
  | 203 => ((1/43046721:ℚ),(1,4,0,0))
  | 204 => ((1/2562890625:ℚ),(0,2,2,0))
  | 205 => ((1/282429536481:ℚ),(2,6,0,0))
  | 206 => ((1/16815125390625:ℚ),(2,4,2,0))
  | 207 => ((1/16815125390625:ℚ),(0,4,2,0))
  | 208 => ((1/282429536481:ℚ),(2,6,0,0))
  | 209 => ((1/390625:ℚ),(0,0,2,0))
  | 210 => ((1/110324037687890625:ℚ),(2,6,2,0))
  | 211 => ((1/43046721:ℚ),(0,4,0,0))
  | 212 => ((1/282429536481:ℚ),(1,6,0,0))
  | 213 => ((1/2562890625:ℚ),(2,2,2,0))
  | 214 => ((1/6561:ℚ),(2,2,0,0))
  | 215 => ((1/16815125390625:ℚ),(0,4,2,0))
  | 216 => ((1/390625:ℚ),(1,0,2,0))
  | 217 => ((1/282429536481:ℚ),(1,6,0,0))
  | 218 => ((1/16815125390625:ℚ),(0,4,2,0))
  | 219 => ((1/43046721:ℚ),(1,4,0,0))
  | 220 => ((1/2562890625:ℚ),(1,2,2,0))
  | 221 => ((1/282429536481:ℚ),(2,6,0,0))
  | 222 => ((1/16815125390625:ℚ),(1,4,2,0))
  | 223 => ((1/43046721:ℚ),(2,4,0,0))
  | 224 => ((1/16815125390625:ℚ),(0,4,2,0))
  | 225 => ((1/282429536481:ℚ),(0,6,0,0))
  | 226 => ((1/390625:ℚ),(1,0,2,0))
  | 227 => ((1/110324037687890625:ℚ),(2,6,2,0))
  | 228 => ((1/16815125390625:ℚ),(0,4,2,0))
  | 229 => ((1/16815125390625:ℚ),(0,4,2,0))
  | 230 => ((1/282429536481:ℚ),(2,6,0,0))
  | 231 => ((1/110324037687890625:ℚ),(2,6,2,0))
  | 232 => ((1/282429536481:ℚ),(0,6,0,0))
  | 233 => ((1/72301961339136:ℚ),(2,6,1,0))
  | 234 => ((1/282429536481:ℚ),(0,6,0,0))
  | 235 => ((1/11019960576:ℚ),(2,4,1,0))
  | 236 => ((1/282429536481:ℚ),(0,6,1,0))
  | 237 => ((1/43046721:ℚ),(0,4,1,0))
  | 238 => ((1/43046721:ℚ),(0,4,2,0))
  | 239 => ((-8/15752961:ℚ),(0,2,0,2))
  | 240 => ((19208/6561:ℚ),(0,2,0,0))
  | 241 => ((-1/326653399296:ℚ),(2,4,0,2))
  | 242 => ((-4/1275989841:ℚ),(0,4,0,2))
  | 243 => ((-1/2551979682:ℚ),(2,4,0,2))
  | 244 => ((-64/15752961:ℚ),(0,2,0,2))
  | 245 => ((-1/1275989841:ℚ),(0,4,0,2))
  | 246 => ((-1/11483908569:ℚ),(0,6,0,2))
  | 247 => ((2401/26244:ℚ),(2,2,0,0))
  | 248 => ((-2/2170458719541:ℚ),(0,6,0,2))
  | 249 => ((-8/15752961:ℚ),(0,2,0,2))
  | 250 => ((-1/2480524250904:ℚ),(2,6,0,2))
  | 251 => ((-1/31505922:ℚ),(2,2,0,2))
  | 252 => ((-8/2170458719541:ℚ),(0,6,0,2))
  | 253 => ((-128/1275989841:ℚ),(0,4,0,2))
  | 254 => ((-2/2977309629:ℚ),(0,3,0,2))
  | 255 => ((-1/31505922:ℚ),(2,3,0,2))
  | 256 => ((-128/583443:ℚ),(0,3,0,2))
  | 257 => ((-128/583443:ℚ),(0,3,0,2))
  | 258 => ((2401/354294:ℚ),(2,6,0,0))
  | 259 => ((-8/16807:ℚ),(0,3,0,2))
  | 260 => ((2401/13122:ℚ),(2,4,0,0))
  | 261 => ((2401/13122:ℚ),(2,4,0,0))
  | 262 => ((9604/6561:ℚ),(0,4,0,0))
  | 263 => ((-1/2401:ℚ),(0,3,0,2))
  | 264 => ((-1/2401:ℚ),(0,3,0,2))
  | 265 => ((2401/177147:ℚ),(0,6,0,0))
  | 266 => ((2401/177147:ℚ),(0,6,0,0))
  | 267 => ((2401/6561:ℚ),(0,4,0,0))
  | 268 => ((-1/4802:ℚ),(2,3,0,2))
  | 269 => ((-4/2401:ℚ),(0,3,0,2))
  | 270 => ((-4/2401:ℚ),(0,3,0,2))
  | 271 => ((-1/2420208:ℚ),(2,3,0,2))
  | 272 => ((-128/2401:ℚ),(0,3,0,2))
  | 273 => ((-8/151263:ℚ),(0,3,0,2))
  | 274 => ((-8/151263:ℚ),(0,3,0,2))
  | 275 => ((2401/162:ℚ),(2,4,0,0))
  | 276 => ((-1/2401:ℚ),(0,3,0,2))
  | 277 => ((-1/21609:ℚ),(0,3,0,2))
  | 278 => ((2401/1594323:ℚ),(0,6,0,0))
  | 279 => ((1/1628150074335205281:ℚ),(2,6,0,2))
  | 280 => ((1/248155780267521:ℚ),(2,4,0,2))
  | 281 => ((1/37822859361:ℚ),(0,2,0,2))
  | 282 => ((1/37822859361:ℚ),(0,2,0,2))
  | 283 => ((1/5764801:ℚ),(1,0,0,2))
  | 284 => ((1/37822859361:ℚ),(1,2,0,2))
  | 285 => ((1/37822859361:ℚ),(2,2,0,2))
  | 286 => ((-8/50242099989375:ℚ),(0,6,2,2))
  | 287 => ((-1/7177442855625:ℚ),(0,6,2,2))
  | 288 => ((-1/4019367999150000:ℚ),(2,6,2,2))
  | 289 => ((-128/35887214278125:ℚ),(0,6,2,2))
  | 290 => ((-1/19691201250:ℚ),(2,3,2,2))
  | 291 => ((2401/221433750:ℚ),(2,6,2,0))
  | 292 => ((-5000/2977309629:ℚ),(0,3,0,2))
  | 293 => ((19208/553584375:ℚ),(0,6,2,0))
  | 294 => ((9604/4100625:ℚ),(0,4,2,0))
  | 295 => ((19208/50625:ℚ),(0,4,2,0))
  | 296 => ((-1/31505922:ℚ),(2,3,2,2))
  | 297 => ((2401/50625:ℚ),(0,4,2,0))
  | 298 => ((1/635996122787189562890625:ℚ),(1,6,2,2))
  | 299 => ((1/63527879748485376:ℚ),(2,4,2,2))
  | 300 => ((8/91125:ℚ),(0,2,2,0))
  | 301 => ((250/729:ℚ),(0,2,0,0))
  | 302 => ((125/5832:ℚ),(2,2,0,0))
  | 303 => ((-2/91125:ℚ),(0,2,2,0))
  | 304 => ((-8/91125:ℚ),(0,2,2,0))
  | 305 => ((-125/5832:ℚ),(2,2,0,0))
  | 306 => ((125/78732:ℚ),(2,6,0,0))
  | 307 => ((125/78732:ℚ),(2,6,0,0))
  | 308 => ((-1/500:ℚ),(2,3,2,0))
  | 309 => ((-1/500:ℚ),(2,3,2,0))
  | 310 => ((8/151875:ℚ),(0,2,2,0))
  | 311 => ((8/151875:ℚ),(0,2,2,0))
  | 312 => ((250/19683:ℚ),(0,6,0,0))
  | 313 => ((250/19683:ℚ),(0,6,0,0))
  | 314 => ((-2/125:ℚ),(0,3,2,0))
  | 315 => ((-2/125:ℚ),(0,3,2,0))
  | 316 => ((-16/125:ℚ),(0,3,2,0))
  | 317 => ((-1/500:ℚ),(2,3,2,0))
  | 318 => ((125/708588:ℚ),(2,6,0,0))
  | 319 => ((1/1000000:ℚ),(2,0,2,0))
  | 320 => ((1/387420489:ℚ),(2,6,0,0))
  | 321 => ((1/387420489:ℚ),(2,6,0,0))
  | 322 => ((1/15625:ℚ),(0,0,2,0))
  | 323 => ((1/387420489:ℚ),(1,6,0,0))
  | 324 => ((1/11390625:ℚ),(2,2,2,0))
  | 325 => ((1/15625:ℚ),(1,0,2,0))
  | 326 => ((1/387420489:ℚ),(2,6,0,0))
  | 327 => ((686/729:ℚ),(0,2,0,0))
  | 328 => ((-8/250047:ℚ),(0,2,0,2))
  | 329 => ((-2/250047:ℚ),(0,2,0,2))
  | 330 => ((-16/83349:ℚ),(0,3,0,2))
  | 331 => ((-16/83349:ℚ),(0,3,0,2))
  | 332 => ((343/78732:ℚ),(2,6,0,0))
  | 333 => ((-16/343:ℚ),(0,3,0,2))
  | 334 => ((343/8748:ℚ),(2,4,0,0))
  | 335 => ((343/8748:ℚ),(2,4,0,0))
  | 336 => ((-1/343:ℚ),(0,3,0,2))
  | 337 => ((-1/343:ℚ),(0,3,0,2))
  | 338 => ((343/19683:ℚ),(0,6,0,0))
  | 339 => ((-16/343:ℚ),(0,3,0,2))
  | _ => (0,(0,0,0,0))
def normalizer (x y z w : ℂ) (i : ℕ) : ℂ :=
  let d := normalizerData i
  (d.1:ℂ)*x^d.2.1*y^d.2.2.1*z^d.2.2.2.1*w^d.2.2.2.2

theorem physical_normalizer_analytic (i m : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z => normalizer (primeRate 2 m z) (primeRate 3 m z)
      (primeRate 5 m z) (primeRate 7 m z) i) s := by
  have h2 := (primeRate_analytic 2 m s).zpow (primeRate_nonzero 2 m s) (n:=(normalizerData i).2.1)
  have h3 := (primeRate_analytic 3 m s).zpow (primeRate_nonzero 3 m s) (n:=(normalizerData i).2.2.1)
  have h5 := (primeRate_analytic 5 m s).zpow (primeRate_nonzero 5 m s) (n:=(normalizerData i).2.2.2.1)
  have h7 := (primeRate_analytic 7 m s).zpow (primeRate_nonzero 7 m s) (n:=(normalizerData i).2.2.2.2)
  exact (((analyticAt_const.mul h2).mul h3).mul h5).mul h7
#print axioms physical_normalizer_analytic
end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily.Plus
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenFourthPlusInputBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily.Plus

theorem binding_input_lookup0 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 0=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input0 := rfl
theorem binding_source_lookup0 : selected ⟨0,by decide⟩=sourceRaw0 := rfl
theorem binding_depth_lookup0 : depth ⟨0,by decide⟩=4 := rfl
theorem binding_normalizer_lookup0 : normalizerData 0=((2/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup1 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 1=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input1 := rfl
theorem binding_source_lookup1 : selected ⟨1,by decide⟩=sourceRaw1 := rfl
theorem binding_depth_lookup1 : depth ⟨1,by decide⟩=4 := rfl
theorem binding_normalizer_lookup1 : normalizerData 1=((16/1:ℚ),(0,0,0,0)) := rfl
theorem binding_input_lookup2 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 2=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input2 := rfl
theorem binding_source_lookup2 : selected ⟨2,by decide⟩=sourceRaw3 := rfl
theorem binding_depth_lookup2 : depth ⟨2,by decide⟩=4 := rfl
theorem binding_normalizer_lookup2 : normalizerData 2=((5000/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup3 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 3=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input3 := rfl
theorem binding_source_lookup3 : selected ⟨3,by decide⟩=sourceRaw9 := rfl
theorem binding_depth_lookup3 : depth ⟨3,by decide⟩=4 := rfl
theorem binding_normalizer_lookup3 : normalizerData 3=((-8/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup4 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 4=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input4 := rfl
theorem binding_source_lookup4 : selected ⟨4,by decide⟩=sourceRaw10 := rfl
theorem binding_depth_lookup4 : depth ⟨4,by decide⟩=4 := rfl
theorem binding_normalizer_lookup4 : normalizerData 4=((1/38263752:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup5 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 5=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input5 := rfl
theorem binding_source_lookup5 : selected ⟨5,by decide⟩=sourceRaw11 := rfl
theorem binding_depth_lookup5 : depth ⟨5,by decide⟩=4 := rfl
theorem binding_normalizer_lookup5 : normalizerData 5=((64/4100625:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup6 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 6=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input6 := rfl
theorem binding_source_lookup6 : selected ⟨6,by decide⟩=sourceRaw14 := rfl
theorem binding_depth_lookup6 : depth ⟨6,by decide⟩=4 := rfl
theorem binding_normalizer_lookup6 : normalizerData 6=((1/282429536481:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup7 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 7=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input7 := rfl
theorem binding_source_lookup7 : selected ⟨7,by decide⟩=sourceRaw16 := rfl
theorem binding_depth_lookup7 : depth ⟨7,by decide⟩=4 := rfl
theorem binding_normalizer_lookup7 : normalizerData 7=((8/332150625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup8 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 8=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input8 := rfl
theorem binding_source_lookup8 : selected ⟨8,by decide⟩=sourceRaw18 := rfl
theorem binding_depth_lookup8 : depth ⟨8,by decide⟩=4 := rfl
theorem binding_normalizer_lookup8 : normalizerData 8=((-1/16:ℚ),(2,0,0,0)) := rfl
theorem binding_input_lookup9 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 9=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input9 := rfl
theorem binding_source_lookup9 : selected ⟨9,by decide⟩=sourceRaw19 := rfl
theorem binding_depth_lookup9 : depth ⟨9,by decide⟩=4 := rfl
theorem binding_normalizer_lookup9 : normalizerData 9=((2/4782969:ℚ),(0,6,0,0)) := rfl

theorem input_binding_block00 (i : Fin 340) (hlo : 0 ≤ i.val) (hhi : i.val < 10) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 0 ≤ i at hlo
  change i < 10 at hhi
  interval_cases i
  · rw [binding_input_lookup0,binding_source_lookup0,binding_depth_lookup0]
    simpa only [normalizer,binding_normalizer_lookup0,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input0 x y z w v hx hy hz hw
  · rw [binding_input_lookup1,binding_source_lookup1,binding_depth_lookup1]
    simpa only [normalizer,binding_normalizer_lookup1,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input1 x y z w v hx hy hz hw
  · rw [binding_input_lookup2,binding_source_lookup2,binding_depth_lookup2]
    simpa only [normalizer,binding_normalizer_lookup2,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input2 x y z w v hx hy hz hw
  · rw [binding_input_lookup3,binding_source_lookup3,binding_depth_lookup3]
    simpa only [normalizer,binding_normalizer_lookup3,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input3 x y z w v hx hy hz hw
  · rw [binding_input_lookup4,binding_source_lookup4,binding_depth_lookup4]
    simpa only [normalizer,binding_normalizer_lookup4,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input4 x y z w v hx hy hz hw
  · rw [binding_input_lookup5,binding_source_lookup5,binding_depth_lookup5]
    simpa only [normalizer,binding_normalizer_lookup5,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input5 x y z w v hx hy hz hw
  · rw [binding_input_lookup6,binding_source_lookup6,binding_depth_lookup6]
    simpa only [normalizer,binding_normalizer_lookup6,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input6 x y z w v hx hy hz hw
  · rw [binding_input_lookup7,binding_source_lookup7,binding_depth_lookup7]
    simpa only [normalizer,binding_normalizer_lookup7,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input7 x y z w v hx hy hz hw
  · rw [binding_input_lookup8,binding_source_lookup8,binding_depth_lookup8]
    simpa only [normalizer,binding_normalizer_lookup8,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input8 x y z w v hx hy hz hw
  · rw [binding_input_lookup9,binding_source_lookup9,binding_depth_lookup9]
    simpa only [normalizer,binding_normalizer_lookup9,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input9 x y z w v hx hy hz hw
#print axioms input_binding_block00

theorem binding_input_lookup10 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 10=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input10 := rfl
theorem binding_source_lookup10 : selected ⟨10,by decide⟩=sourceRaw20 := rfl
theorem binding_depth_lookup10 : depth ⟨10,by decide⟩=4 := rfl
theorem binding_normalizer_lookup10 : normalizerData 10=((128/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup11 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 11=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input11 := rfl
theorem binding_source_lookup11 : selected ⟨11,by decide⟩=sourceRaw22 := rfl
theorem binding_depth_lookup11 : depth ⟨11,by decide⟩=4 := rfl
theorem binding_normalizer_lookup11 : normalizerData 11=((5000/6561:ℚ),(0,2,0,0)) := rfl
theorem binding_input_lookup12 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 12=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input12 := rfl
theorem binding_source_lookup12 : selected ⟨12,by decide⟩=sourceRaw24 := rfl
theorem binding_depth_lookup12 : depth ⟨12,by decide⟩=4 := rfl
theorem binding_normalizer_lookup12 : normalizerData 12=((-1/129140163:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup13 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 13=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input13 := rfl
theorem binding_source_lookup13 : selected ⟨13,by decide⟩=sourceRaw26 := rfl
theorem binding_depth_lookup13 : depth ⟨13,by decide⟩=4 := rfl
theorem binding_normalizer_lookup13 : normalizerData 13=((-625/28697814:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup14 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 14=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input14 := rfl
theorem binding_source_lookup14 : selected ⟨14,by decide⟩=sourceRaw27 := rfl
theorem binding_depth_lookup14 : depth ⟨14,by decide⟩=4 := rfl
theorem binding_normalizer_lookup14 : normalizerData 14=((2/129140163:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup15 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 15=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input15 := rfl
theorem binding_source_lookup15 : selected ⟨15,by decide⟩=sourceRaw30 := rfl
theorem binding_depth_lookup15 : depth ⟨15,by decide⟩=4 := rfl
theorem binding_normalizer_lookup15 : normalizerData 15=((-8/8968066875:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup16 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 16=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input16 := rfl
theorem binding_source_lookup16 : selected ⟨16,by decide⟩=sourceRaw31 := rfl
theorem binding_depth_lookup16 : depth ⟨16,by decide⟩=4 := rfl
theorem binding_normalizer_lookup16 : normalizerData 16=((-1/2066242608:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup17 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 17=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input17 := rfl
theorem binding_source_lookup17 : selected ⟨17,by decide⟩=sourceRaw38 := rfl
theorem binding_depth_lookup17 : depth ⟨17,by decide⟩=4 := rfl
theorem binding_normalizer_lookup17 : normalizerData 17=((625/26244:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup18 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 18=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input18 := rfl
theorem binding_source_lookup18 : selected ⟨18,by decide⟩=sourceRaw40 := rfl
theorem binding_depth_lookup18 : depth ⟨18,by decide⟩=4 := rfl
theorem binding_normalizer_lookup18 : normalizerData 18=((8/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup19 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 19=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input19 := rfl
theorem binding_source_lookup19 : selected ⟨19,by decide⟩=sourceRaw41 := rfl
theorem binding_depth_lookup19 : depth ⟨19,by decide⟩=4 := rfl
theorem binding_normalizer_lookup19 : normalizerData 19=((1/9565938:ℚ),(2,6,0,0)) := rfl

theorem input_binding_block01 (i : Fin 340) (hlo : 10 ≤ i.val) (hhi : i.val < 20) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 10 ≤ i at hlo
  change i < 20 at hhi
  interval_cases i
  · rw [binding_input_lookup10,binding_source_lookup10,binding_depth_lookup10]
    simpa only [normalizer,binding_normalizer_lookup10,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input10 x y z w v hx hy hz hw
  · rw [binding_input_lookup11,binding_source_lookup11,binding_depth_lookup11]
    simpa only [normalizer,binding_normalizer_lookup11,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input11 x y z w v hx hy hz hw
  · rw [binding_input_lookup12,binding_source_lookup12,binding_depth_lookup12]
    simpa only [normalizer,binding_normalizer_lookup12,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input12 x y z w v hx hy hz hw
  · rw [binding_input_lookup13,binding_source_lookup13,binding_depth_lookup13]
    simpa only [normalizer,binding_normalizer_lookup13,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input13 x y z w v hx hy hz hw
  · rw [binding_input_lookup14,binding_source_lookup14,binding_depth_lookup14]
    simpa only [normalizer,binding_normalizer_lookup14,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input14 x y z w v hx hy hz hw
  · rw [binding_input_lookup15,binding_source_lookup15,binding_depth_lookup15]
    simpa only [normalizer,binding_normalizer_lookup15,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input15 x y z w v hx hy hz hw
  · rw [binding_input_lookup16,binding_source_lookup16,binding_depth_lookup16]
    simpa only [normalizer,binding_normalizer_lookup16,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input16 x y z w v hx hy hz hw
  · rw [binding_input_lookup17,binding_source_lookup17,binding_depth_lookup17]
    simpa only [normalizer,binding_normalizer_lookup17,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input17 x y z w v hx hy hz hw
  · rw [binding_input_lookup18,binding_source_lookup18,binding_depth_lookup18]
    simpa only [normalizer,binding_normalizer_lookup18,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input18 x y z w v hx hy hz hw
  · rw [binding_input_lookup19,binding_source_lookup19,binding_depth_lookup19]
    simpa only [normalizer,binding_normalizer_lookup19,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input19 x y z w v hx hy hz hw
#print axioms input_binding_block01

theorem binding_input_lookup20 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 20=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input20 := rfl
theorem binding_source_lookup20 : selected ⟨20,by decide⟩=sourceRaw42 := rfl
theorem binding_depth_lookup20 : depth ⟨20,by decide⟩=4 := rfl
theorem binding_normalizer_lookup20 : normalizerData 20=((128/332150625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup21 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 21=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input21 := rfl
theorem binding_source_lookup21 : selected ⟨21,by decide⟩=sourceRaw45 := rfl
theorem binding_depth_lookup21 : depth ⟨21,by decide⟩=4 := rfl
theorem binding_normalizer_lookup21 : normalizerData 21=((1/282429536481:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup22 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 22=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input22 := rfl
theorem binding_source_lookup22 : selected ⟨22,by decide⟩=sourceRaw47 := rfl
theorem binding_depth_lookup22 : depth ⟨22,by decide⟩=4 := rfl
theorem binding_normalizer_lookup22 : normalizerData 22=((-8/4100625:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup23 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 23=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input23 := rfl
theorem binding_source_lookup23 : selected ⟨23,by decide⟩=sourceRaw49 := rfl
theorem binding_depth_lookup23 : depth ⟨23,by decide⟩=4 := rfl
theorem binding_normalizer_lookup23 : normalizerData 23=((-1/1062882:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup24 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 24=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input24 := rfl
theorem binding_source_lookup24 : selected ⟨24,by decide⟩=sourceRaw50 := rfl
theorem binding_depth_lookup24 : depth ⟨24,by decide⟩=4 := rfl
theorem binding_normalizer_lookup24 : normalizerData 24=((2/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup25 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 25=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input25 := rfl
theorem binding_source_lookup25 : selected ⟨25,by decide⟩=sourceRaw51 := rfl
theorem binding_depth_lookup25 : depth ⟨25,by decide⟩=4 := rfl
theorem binding_normalizer_lookup25 : normalizerData 25=((-1/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup26 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 26=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input26 := rfl
theorem binding_source_lookup26 : selected ⟨26,by decide⟩=sourceRaw52 := rfl
theorem binding_depth_lookup26 : depth ⟨26,by decide⟩=4 := rfl
theorem binding_normalizer_lookup26 : normalizerData 26=((-1/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup27 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 27=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input27 := rfl
theorem binding_source_lookup27 : selected ⟨27,by decide⟩=sourceRaw68 := rfl
theorem binding_depth_lookup27 : depth ⟨27,by decide⟩=4 := rfl
theorem binding_normalizer_lookup27 : normalizerData 27=((1/76527504:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup28 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 28=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input28 := rfl
theorem binding_source_lookup28 : selected ⟨28,by decide⟩=sourceRaw69 := rfl
theorem binding_depth_lookup28 : depth ⟨28,by decide⟩=4 := rfl
theorem binding_normalizer_lookup28 : normalizerData 28=((-128/332150625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup29 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 29=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input29 := rfl
theorem binding_source_lookup29 : selected ⟨29,by decide⟩=sourceRaw70 := rfl
theorem binding_depth_lookup29 : depth ⟨29,by decide⟩=4 := rfl
theorem binding_normalizer_lookup29 : normalizerData 29=((-2/2989355625:ℚ),(0,6,2,0)) := rfl

theorem input_binding_block02 (i : Fin 340) (hlo : 20 ≤ i.val) (hhi : i.val < 30) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 20 ≤ i at hlo
  change i < 30 at hhi
  interval_cases i
  · rw [binding_input_lookup20,binding_source_lookup20,binding_depth_lookup20]
    simpa only [normalizer,binding_normalizer_lookup20,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input20 x y z w v hx hy hz hw
  · rw [binding_input_lookup21,binding_source_lookup21,binding_depth_lookup21]
    simpa only [normalizer,binding_normalizer_lookup21,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input21 x y z w v hx hy hz hw
  · rw [binding_input_lookup22,binding_source_lookup22,binding_depth_lookup22]
    simpa only [normalizer,binding_normalizer_lookup22,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input22 x y z w v hx hy hz hw
  · rw [binding_input_lookup23,binding_source_lookup23,binding_depth_lookup23]
    simpa only [normalizer,binding_normalizer_lookup23,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input23 x y z w v hx hy hz hw
  · rw [binding_input_lookup24,binding_source_lookup24,binding_depth_lookup24]
    simpa only [normalizer,binding_normalizer_lookup24,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input24 x y z w v hx hy hz hw
  · rw [binding_input_lookup25,binding_source_lookup25,binding_depth_lookup25]
    simpa only [normalizer,binding_normalizer_lookup25,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input25 x y z w v hx hy hz hw
  · rw [binding_input_lookup26,binding_source_lookup26,binding_depth_lookup26]
    simpa only [normalizer,binding_normalizer_lookup26,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input26 x y z w v hx hy hz hw
  · rw [binding_input_lookup27,binding_source_lookup27,binding_depth_lookup27]
    simpa only [normalizer,binding_normalizer_lookup27,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input27 x y z w v hx hy hz hw
  · rw [binding_input_lookup28,binding_source_lookup28,binding_depth_lookup28]
    simpa only [normalizer,binding_normalizer_lookup28,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input28 x y z w v hx hy hz hw
  · rw [binding_input_lookup29,binding_source_lookup29,binding_depth_lookup29]
    simpa only [normalizer,binding_normalizer_lookup29,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input29 x y z w v hx hy hz hw
#print axioms input_binding_block02

theorem binding_input_lookup30 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 30=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input30 := rfl
theorem binding_source_lookup30 : selected ⟨30,by decide⟩=sourceRaw71 := rfl
theorem binding_depth_lookup30 : depth ⟨30,by decide⟩=4 := rfl
theorem binding_normalizer_lookup30 : normalizerData 30=((-1/8201250:ℚ),(2,2,2,0)) := rfl
theorem binding_input_lookup31 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 31=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input31 := rfl
theorem binding_source_lookup31 : selected ⟨31,by decide⟩=sourceRaw72 := rfl
theorem binding_depth_lookup31 : depth ⟨31,by decide⟩=4 := rfl
theorem binding_normalizer_lookup31 : normalizerData 31=((1/282429536481:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup32 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 32=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input32 := rfl
theorem binding_source_lookup32 : selected ⟨32,by decide⟩=sourceRaw73 := rfl
theorem binding_depth_lookup32 : depth ⟨32,by decide⟩=4 := rfl
theorem binding_normalizer_lookup32 : normalizerData 32=((-1/5978711250:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup33 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 33=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input33 := rfl
theorem binding_source_lookup33 : selected ⟨33,by decide⟩=sourceRaw74 := rfl
theorem binding_depth_lookup33 : depth ⟨33,by decide⟩=4 := rfl
theorem binding_normalizer_lookup33 : normalizerData 33=((4/332150625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup34 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 34=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input34 := rfl
theorem binding_source_lookup34 : selected ⟨34,by decide⟩=sourceRaw76 := rfl
theorem binding_depth_lookup34 : depth ⟨34,by decide⟩=4 := rfl
theorem binding_normalizer_lookup34 : normalizerData 34=((-1/1062882:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup35 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 35=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input35 := rfl
theorem binding_source_lookup35 : selected ⟨35,by decide⟩=sourceRaw77 := rfl
theorem binding_depth_lookup35 : depth ⟨35,by decide⟩=4 := rfl
theorem binding_normalizer_lookup35 : normalizerData 35=((-2/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup36 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 36=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input36 := rfl
theorem binding_source_lookup36 : selected ⟨36,by decide⟩=sourceRaw78 := rfl
theorem binding_depth_lookup36 : depth ⟨36,by decide⟩=4 := rfl
theorem binding_normalizer_lookup36 : normalizerData 36=((128/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup37 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 37=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input37 := rfl
theorem binding_source_lookup37 : selected ⟨37,by decide⟩=sourceRaw82 := rfl
theorem binding_depth_lookup37 : depth ⟨37,by decide⟩=4 := rfl
theorem binding_normalizer_lookup37 : normalizerData 37=((1/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup38 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 38=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input38 := rfl
theorem binding_source_lookup38 : selected ⟨38,by decide⟩=sourceRaw83 := rfl
theorem binding_depth_lookup38 : depth ⟨38,by decide⟩=4 := rfl
theorem binding_normalizer_lookup38 : normalizerData 38=((-1/14946778125:ℚ),(0,6,2,0)) := rfl
theorem binding_input_lookup39 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 39=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input39 := rfl
theorem binding_source_lookup39 : selected ⟨39,by decide⟩=sourceRaw84 := rfl
theorem binding_depth_lookup39 : depth ⟨39,by decide⟩=4 := rfl
theorem binding_normalizer_lookup39 : normalizerData 39=((1/72301961339136:ℚ),(2,6,0,0)) := rfl

theorem input_binding_block03 (i : Fin 340) (hlo : 30 ≤ i.val) (hhi : i.val < 40) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 30 ≤ i at hlo
  change i < 40 at hhi
  interval_cases i
  · rw [binding_input_lookup30,binding_source_lookup30,binding_depth_lookup30]
    simpa only [normalizer,binding_normalizer_lookup30,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input30 x y z w v hx hy hz hw
  · rw [binding_input_lookup31,binding_source_lookup31,binding_depth_lookup31]
    simpa only [normalizer,binding_normalizer_lookup31,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input31 x y z w v hx hy hz hw
  · rw [binding_input_lookup32,binding_source_lookup32,binding_depth_lookup32]
    simpa only [normalizer,binding_normalizer_lookup32,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input32 x y z w v hx hy hz hw
  · rw [binding_input_lookup33,binding_source_lookup33,binding_depth_lookup33]
    simpa only [normalizer,binding_normalizer_lookup33,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input33 x y z w v hx hy hz hw
  · rw [binding_input_lookup34,binding_source_lookup34,binding_depth_lookup34]
    simpa only [normalizer,binding_normalizer_lookup34,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input34 x y z w v hx hy hz hw
  · rw [binding_input_lookup35,binding_source_lookup35,binding_depth_lookup35]
    simpa only [normalizer,binding_normalizer_lookup35,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input35 x y z w v hx hy hz hw
  · rw [binding_input_lookup36,binding_source_lookup36,binding_depth_lookup36]
    simpa only [normalizer,binding_normalizer_lookup36,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input36 x y z w v hx hy hz hw
  · rw [binding_input_lookup37,binding_source_lookup37,binding_depth_lookup37]
    simpa only [normalizer,binding_normalizer_lookup37,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input37 x y z w v hx hy hz hw
  · rw [binding_input_lookup38,binding_source_lookup38,binding_depth_lookup38]
    simpa only [normalizer,binding_normalizer_lookup38,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input38 x y z w v hx hy hz hw
  · rw [binding_input_lookup39,binding_source_lookup39,binding_depth_lookup39]
    simpa only [normalizer,binding_normalizer_lookup39,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input39 x y z w v hx hy hz hw
#print axioms input_binding_block03

theorem binding_input_lookup40 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 40=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input40 := rfl
theorem binding_source_lookup40 : selected ⟨40,by decide⟩=sourceRaw85 := rfl
theorem binding_depth_lookup40 : depth ⟨40,by decide⟩=4 := rfl
theorem binding_normalizer_lookup40 : normalizerData 40=((-1/332150625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup41 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 41=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input41 := rfl
theorem binding_source_lookup41 : selected ⟨41,by decide⟩=sourceRaw86 := rfl
theorem binding_depth_lookup41 : depth ⟨41,by decide⟩=4 := rfl
theorem binding_normalizer_lookup41 : normalizerData 41=((-1/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup42 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 42=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input42 := rfl
theorem binding_source_lookup42 : selected ⟨42,by decide⟩=sourceRaw105 := rfl
theorem binding_depth_lookup42 : depth ⟨42,by decide⟩=4 := rfl
theorem binding_normalizer_lookup42 : normalizerData 42=((128/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup43 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 43=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input43 := rfl
theorem binding_source_lookup43 : selected ⟨43,by decide⟩=sourceRaw106 := rfl
theorem binding_depth_lookup43 : depth ⟨43,by decide⟩=4 := rfl
theorem binding_normalizer_lookup43 : normalizerData 43=((2/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup44 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 44=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input44 := rfl
theorem binding_source_lookup44 : selected ⟨44,by decide⟩=sourceRaw107 := rfl
theorem binding_depth_lookup44 : depth ⟨44,by decide⟩=4 := rfl
theorem binding_normalizer_lookup44 : normalizerData 44=((-1/1062882:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup45 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 45=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input45 := rfl
theorem binding_source_lookup45 : selected ⟨45,by decide⟩=sourceRaw108 := rfl
theorem binding_depth_lookup45 : depth ⟨45,by decide⟩=4 := rfl
theorem binding_normalizer_lookup45 : normalizerData 45=((-128/14946778125:ℚ),(0,6,2,0)) := rfl
theorem binding_input_lookup46 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 46=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input46 := rfl
theorem binding_source_lookup46 : selected ⟨46,by decide⟩=sourceRaw109 := rfl
theorem binding_depth_lookup46 : depth ⟨46,by decide⟩=4 := rfl
theorem binding_normalizer_lookup46 : normalizerData 46=((-4/332150625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup47 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 47=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input47 := rfl
theorem binding_source_lookup47 : selected ⟨47,by decide⟩=sourceRaw111 := rfl
theorem binding_depth_lookup47 : depth ⟨47,by decide⟩=4 := rfl
theorem binding_normalizer_lookup47 : normalizerData 47=((1/282429536481:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup48 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 48=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input48 := rfl
theorem binding_source_lookup48 : selected ⟨48,by decide⟩=sourceRaw112 := rfl
theorem binding_depth_lookup48 : depth ⟨48,by decide⟩=4 := rfl
theorem binding_normalizer_lookup48 : normalizerData 48=((-1/8201250:ℚ),(2,2,2,0)) := rfl
theorem binding_input_lookup49 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 49=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input49 := rfl
theorem binding_source_lookup49 : selected ⟨49,by decide⟩=sourceRaw114 := rfl
theorem binding_depth_lookup49 : depth ⟨49,by decide⟩=4 := rfl
theorem binding_normalizer_lookup49 : normalizerData 49=((-128/332150625:ℚ),(0,4,2,0)) := rfl

theorem input_binding_block04 (i : Fin 340) (hlo : 40 ≤ i.val) (hhi : i.val < 50) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 40 ≤ i at hlo
  change i < 50 at hhi
  interval_cases i
  · rw [binding_input_lookup40,binding_source_lookup40,binding_depth_lookup40]
    simpa only [normalizer,binding_normalizer_lookup40,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input40 x y z w v hx hy hz hw
  · rw [binding_input_lookup41,binding_source_lookup41,binding_depth_lookup41]
    simpa only [normalizer,binding_normalizer_lookup41,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input41 x y z w v hx hy hz hw
  · rw [binding_input_lookup42,binding_source_lookup42,binding_depth_lookup42]
    simpa only [normalizer,binding_normalizer_lookup42,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input42 x y z w v hx hy hz hw
  · rw [binding_input_lookup43,binding_source_lookup43,binding_depth_lookup43]
    simpa only [normalizer,binding_normalizer_lookup43,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input43 x y z w v hx hy hz hw
  · rw [binding_input_lookup44,binding_source_lookup44,binding_depth_lookup44]
    simpa only [normalizer,binding_normalizer_lookup44,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input44 x y z w v hx hy hz hw
  · rw [binding_input_lookup45,binding_source_lookup45,binding_depth_lookup45]
    simpa only [normalizer,binding_normalizer_lookup45,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input45 x y z w v hx hy hz hw
  · rw [binding_input_lookup46,binding_source_lookup46,binding_depth_lookup46]
    simpa only [normalizer,binding_normalizer_lookup46,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input46 x y z w v hx hy hz hw
  · rw [binding_input_lookup47,binding_source_lookup47,binding_depth_lookup47]
    simpa only [normalizer,binding_normalizer_lookup47,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input47 x y z w v hx hy hz hw
  · rw [binding_input_lookup48,binding_source_lookup48,binding_depth_lookup48]
    simpa only [normalizer,binding_normalizer_lookup48,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input48 x y z w v hx hy hz hw
  · rw [binding_input_lookup49,binding_source_lookup49,binding_depth_lookup49]
    simpa only [normalizer,binding_normalizer_lookup49,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input49 x y z w v hx hy hz hw
#print axioms input_binding_block04

theorem binding_input_lookup50 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 50=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input50 := rfl
theorem binding_source_lookup50 : selected ⟨50,by decide⟩=sourceRaw115 := rfl
theorem binding_depth_lookup50 : depth ⟨50,by decide⟩=4 := rfl
theorem binding_normalizer_lookup50 : normalizerData 50=((-1/76527504:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup51 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 51=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input51 := rfl
theorem binding_source_lookup51 : selected ⟨51,by decide⟩=sourceRaw118 := rfl
theorem binding_depth_lookup51 : depth ⟨51,by decide⟩=4 := rfl
theorem binding_normalizer_lookup51 : normalizerData 51=((2/129140163:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup52 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 52=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input52 := rfl
theorem binding_source_lookup52 : selected ⟨52,by decide⟩=sourceRaw122 := rfl
theorem binding_depth_lookup52 : depth ⟨52,by decide⟩=4 := rfl
theorem binding_normalizer_lookup52 : normalizerData 52=((-1/16:ℚ),(2,0,0,0)) := rfl
theorem binding_input_lookup53 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 53=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input53 := rfl
theorem binding_source_lookup53 : selected ⟨53,by decide⟩=sourceRaw145 := rfl
theorem binding_depth_lookup53 : depth ⟨53,by decide⟩=4 := rfl
theorem binding_normalizer_lookup53 : normalizerData 53=((-1/17936133750:ℚ),(2,4,2,0)) := rfl
theorem binding_input_lookup54 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 54=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input54 := rfl
theorem binding_source_lookup54 : selected ⟨54,by decide⟩=sourceRaw146 := rfl
theorem binding_depth_lookup54 : depth ⟨54,by decide⟩=4 := rfl
theorem binding_normalizer_lookup54 : normalizerData 54=((-2/403563009375:ℚ),(0,6,2,0)) := rfl
theorem binding_input_lookup55 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 55=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input55 := rfl
theorem binding_source_lookup55 : selected ⟨55,by decide⟩=sourceRaw147 := rfl
theorem binding_depth_lookup55 : depth ⟨55,by decide⟩=4 := rfl
theorem binding_normalizer_lookup55 : normalizerData 55=((-1/2066242608:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup56 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 56=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input56 := rfl
theorem binding_source_lookup56 : selected ⟨56,by decide⟩=sourceRaw151 := rfl
theorem binding_depth_lookup56 : depth ⟨56,by decide⟩=4 := rfl
theorem binding_normalizer_lookup56 : normalizerData 56=((5000/6561:ℚ),(0,2,0,0)) := rfl
theorem binding_input_lookup57 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 57=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input57 := rfl
theorem binding_source_lookup57 : selected ⟨57,by decide⟩=sourceRaw153 := rfl
theorem binding_depth_lookup57 : depth ⟨57,by decide⟩=4 := rfl
theorem binding_normalizer_lookup57 : normalizerData 57=((128/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup58 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 58=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input58 := rfl
theorem binding_source_lookup58 : selected ⟨58,by decide⟩=sourceRaw155 := rfl
theorem binding_depth_lookup58 : depth ⟨58,by decide⟩=4 := rfl
theorem binding_normalizer_lookup58 : normalizerData 58=((-1/16:ℚ),(2,0,0,0)) := rfl
theorem binding_input_lookup59 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 59=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input59 := rfl
theorem binding_source_lookup59 : selected ⟨59,by decide⟩=sourceRaw157 := rfl
theorem binding_depth_lookup59 : depth ⟨59,by decide⟩=4 := rfl
theorem binding_normalizer_lookup59 : normalizerData 59=((-8/332150625:ℚ),(0,4,2,0)) := rfl

theorem input_binding_block05 (i : Fin 340) (hlo : 50 ≤ i.val) (hhi : i.val < 60) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 50 ≤ i at hlo
  change i < 60 at hhi
  interval_cases i
  · rw [binding_input_lookup50,binding_source_lookup50,binding_depth_lookup50]
    simpa only [normalizer,binding_normalizer_lookup50,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input50 x y z w v hx hy hz hw
  · rw [binding_input_lookup51,binding_source_lookup51,binding_depth_lookup51]
    simpa only [normalizer,binding_normalizer_lookup51,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input51 x y z w v hx hy hz hw
  · rw [binding_input_lookup52,binding_source_lookup52,binding_depth_lookup52]
    simpa only [normalizer,binding_normalizer_lookup52,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input52 x y z w v hx hy hz hw
  · rw [binding_input_lookup53,binding_source_lookup53,binding_depth_lookup53]
    simpa only [normalizer,binding_normalizer_lookup53,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input53 x y z w v hx hy hz hw
  · rw [binding_input_lookup54,binding_source_lookup54,binding_depth_lookup54]
    simpa only [normalizer,binding_normalizer_lookup54,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input54 x y z w v hx hy hz hw
  · rw [binding_input_lookup55,binding_source_lookup55,binding_depth_lookup55]
    simpa only [normalizer,binding_normalizer_lookup55,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input55 x y z w v hx hy hz hw
  · rw [binding_input_lookup56,binding_source_lookup56,binding_depth_lookup56]
    simpa only [normalizer,binding_normalizer_lookup56,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input56 x y z w v hx hy hz hw
  · rw [binding_input_lookup57,binding_source_lookup57,binding_depth_lookup57]
    simpa only [normalizer,binding_normalizer_lookup57,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input57 x y z w v hx hy hz hw
  · rw [binding_input_lookup58,binding_source_lookup58,binding_depth_lookup58]
    simpa only [normalizer,binding_normalizer_lookup58,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input58 x y z w v hx hy hz hw
  · rw [binding_input_lookup59,binding_source_lookup59,binding_depth_lookup59]
    simpa only [normalizer,binding_normalizer_lookup59,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input59 x y z w v hx hy hz hw
#print axioms input_binding_block05

theorem binding_input_lookup60 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 60=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input60 := rfl
theorem binding_source_lookup60 : selected ⟨60,by decide⟩=sourceRaw160 := rfl
theorem binding_depth_lookup60 : depth ⟨60,by decide⟩=4 := rfl
theorem binding_normalizer_lookup60 : normalizerData 60=((-1/664301250:ℚ),(2,4,2,0)) := rfl
theorem binding_input_lookup61 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 61=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input61 := rfl
theorem binding_source_lookup61 : selected ⟨61,by decide⟩=sourceRaw162 := rfl
theorem binding_depth_lookup61 : depth ⟨61,by decide⟩=4 := rfl
theorem binding_normalizer_lookup61 : normalizerData 61=((-64/4100625:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup62 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 62=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input62 := rfl
theorem binding_source_lookup62 : selected ⟨62,by decide⟩=sourceRaw163 := rfl
theorem binding_depth_lookup62 : depth ⟨62,by decide⟩=4 := rfl
theorem binding_normalizer_lookup62 : normalizerData 62=((-1/38263752:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup63 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 63=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input63 := rfl
theorem binding_source_lookup63 : selected ⟨63,by decide⟩=sourceRaw164 := rfl
theorem binding_depth_lookup63 : depth ⟨63,by decide⟩=4 := rfl
theorem binding_normalizer_lookup63 : normalizerData 63=((-8/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup64 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 64=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input64 := rfl
theorem binding_source_lookup64 : selected ⟨64,by decide⟩=sourceRaw165 := rfl
theorem binding_depth_lookup64 : depth ⟨64,by decide⟩=4 := rfl
theorem binding_normalizer_lookup64 : normalizerData 64=((-128/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup65 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 65=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input65 := rfl
theorem binding_source_lookup65 : selected ⟨65,by decide⟩=sourceRaw177 := rfl
theorem binding_depth_lookup65 : depth ⟨65,by decide⟩=4 := rfl
theorem binding_normalizer_lookup65 : normalizerData 65=((-1/645700815000:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup66 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 66=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input66 := rfl
theorem binding_source_lookup66 : selected ⟨66,by decide⟩=sourceRaw186 := rfl
theorem binding_depth_lookup66 : depth ⟨66,by decide⟩=4 := rfl
theorem binding_normalizer_lookup66 : normalizerData 66=((-1/76527504:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup67 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 67=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input67 := rfl
theorem binding_source_lookup67 : selected ⟨67,by decide⟩=sourceRaw187 := rfl
theorem binding_depth_lookup67 : depth ⟨67,by decide⟩=4 := rfl
theorem binding_normalizer_lookup67 : normalizerData 67=((16/1:ℚ),(0,0,0,0)) := rfl
theorem binding_input_lookup68 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 68=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input68 := rfl
theorem binding_source_lookup68 : selected ⟨68,by decide⟩=sourceRaw189 := rfl
theorem binding_depth_lookup68 : depth ⟨68,by decide⟩=4 := rfl
theorem binding_normalizer_lookup68 : normalizerData 68=((16/1:ℚ),(0,0,0,0)) := rfl
theorem binding_input_lookup69 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 69=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input69 := rfl
theorem binding_source_lookup69 : selected ⟨69,by decide⟩=sourceRaw191 := rfl
theorem binding_depth_lookup69 : depth ⟨69,by decide⟩=4 := rfl
theorem binding_normalizer_lookup69 : normalizerData 69=((-8/8968066875:ℚ),(0,4,2,0)) := rfl

theorem input_binding_block06 (i : Fin 340) (hlo : 60 ≤ i.val) (hhi : i.val < 70) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 60 ≤ i at hlo
  change i < 70 at hhi
  interval_cases i
  · rw [binding_input_lookup60,binding_source_lookup60,binding_depth_lookup60]
    simpa only [normalizer,binding_normalizer_lookup60,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input60 x y z w v hx hy hz hw
  · rw [binding_input_lookup61,binding_source_lookup61,binding_depth_lookup61]
    simpa only [normalizer,binding_normalizer_lookup61,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input61 x y z w v hx hy hz hw
  · rw [binding_input_lookup62,binding_source_lookup62,binding_depth_lookup62]
    simpa only [normalizer,binding_normalizer_lookup62,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input62 x y z w v hx hy hz hw
  · rw [binding_input_lookup63,binding_source_lookup63,binding_depth_lookup63]
    simpa only [normalizer,binding_normalizer_lookup63,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input63 x y z w v hx hy hz hw
  · rw [binding_input_lookup64,binding_source_lookup64,binding_depth_lookup64]
    simpa only [normalizer,binding_normalizer_lookup64,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input64 x y z w v hx hy hz hw
  · rw [binding_input_lookup65,binding_source_lookup65,binding_depth_lookup65]
    simpa only [normalizer,binding_normalizer_lookup65,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input65 x y z w v hx hy hz hw
  · rw [binding_input_lookup66,binding_source_lookup66,binding_depth_lookup66]
    simpa only [normalizer,binding_normalizer_lookup66,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input66 x y z w v hx hy hz hw
  · rw [binding_input_lookup67,binding_source_lookup67,binding_depth_lookup67]
    simpa only [normalizer,binding_normalizer_lookup67,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input67 x y z w v hx hy hz hw
  · rw [binding_input_lookup68,binding_source_lookup68,binding_depth_lookup68]
    simpa only [normalizer,binding_normalizer_lookup68,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input68 x y z w v hx hy hz hw
  · rw [binding_input_lookup69,binding_source_lookup69,binding_depth_lookup69]
    simpa only [normalizer,binding_normalizer_lookup69,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input69 x y z w v hx hy hz hw
#print axioms input_binding_block06

theorem binding_input_lookup70 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 70=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input70 := rfl
theorem binding_source_lookup70 : selected ⟨70,by decide⟩=sourceRaw192 := rfl
theorem binding_depth_lookup70 : depth ⟨70,by decide⟩=4 := rfl
theorem binding_normalizer_lookup70 : normalizerData 70=((-1/161425203750:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup71 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 71=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input71 := rfl
theorem binding_source_lookup71 : selected ⟨71,by decide⟩=sourceRaw194 := rfl
theorem binding_depth_lookup71 : depth ⟨71,by decide⟩=4 := rfl
theorem binding_normalizer_lookup71 : normalizerData 71=((-2/129140163:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup72 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 72=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input72 := rfl
theorem binding_source_lookup72 : selected ⟨72,by decide⟩=sourceRaw212 := rfl
theorem binding_depth_lookup72 : depth ⟨72,by decide⟩=4 := rfl
theorem binding_normalizer_lookup72 : normalizerData 72=((-1/17936133750:ℚ),(2,4,2,0)) := rfl
theorem binding_input_lookup73 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 73=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input73 := rfl
theorem binding_source_lookup73 : selected ⟨73,by decide⟩=sourceRaw234 := rfl
theorem binding_depth_lookup73 : depth ⟨73,by decide⟩=4 := rfl
theorem binding_normalizer_lookup73 : normalizerData 73=((-1/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup74 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 74=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input74 := rfl
theorem binding_source_lookup74 : selected ⟨74,by decide⟩=sourceRaw249 := rfl
theorem binding_depth_lookup74 : depth ⟨74,by decide⟩=4 := rfl
theorem binding_normalizer_lookup74 : normalizerData 74=((1/4782969:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup75 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 75=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input75 := rfl
theorem binding_source_lookup75 : selected ⟨75,by decide⟩=sourceRaw307 := rfl
theorem binding_depth_lookup75 : depth ⟨75,by decide⟩=4 := rfl
theorem binding_normalizer_lookup75 : normalizerData 75=((16/1:ℚ),(0,0,0,0)) := rfl
theorem binding_input_lookup76 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 76=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input76 := rfl
theorem binding_source_lookup76 : selected ⟨76,by decide⟩=sourceRaw309 := rfl
theorem binding_depth_lookup76 : depth ⟨76,by decide⟩=4 := rfl
theorem binding_normalizer_lookup76 : normalizerData 76=((-1/1062882:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup77 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 77=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input77 := rfl
theorem binding_source_lookup77 : selected ⟨77,by decide⟩=sourceRaw311 := rfl
theorem binding_depth_lookup77 : depth ⟨77,by decide⟩=4 := rfl
theorem binding_normalizer_lookup77 : normalizerData 77=((-8/4100625:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup78 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 78=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input78 := rfl
theorem binding_source_lookup78 : selected ⟨78,by decide⟩=sourceRaw316 := rfl
theorem binding_depth_lookup78 : depth ⟨78,by decide⟩=4 := rfl
theorem binding_normalizer_lookup78 : normalizerData 78=((-128/332150625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup79 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 79=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input79 := rfl
theorem binding_source_lookup79 : selected ⟨79,by decide⟩=sourceRaw317 := rfl
theorem binding_depth_lookup79 : depth ⟨79,by decide⟩=4 := rfl
theorem binding_normalizer_lookup79 : normalizerData 79=((-1/9565938:ℚ),(2,6,0,0)) := rfl

theorem input_binding_block07 (i : Fin 340) (hlo : 70 ≤ i.val) (hhi : i.val < 80) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 70 ≤ i at hlo
  change i < 80 at hhi
  interval_cases i
  · rw [binding_input_lookup70,binding_source_lookup70,binding_depth_lookup70]
    simpa only [normalizer,binding_normalizer_lookup70,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input70 x y z w v hx hy hz hw
  · rw [binding_input_lookup71,binding_source_lookup71,binding_depth_lookup71]
    simpa only [normalizer,binding_normalizer_lookup71,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input71 x y z w v hx hy hz hw
  · rw [binding_input_lookup72,binding_source_lookup72,binding_depth_lookup72]
    simpa only [normalizer,binding_normalizer_lookup72,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input72 x y z w v hx hy hz hw
  · rw [binding_input_lookup73,binding_source_lookup73,binding_depth_lookup73]
    simpa only [normalizer,binding_normalizer_lookup73,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input73 x y z w v hx hy hz hw
  · rw [binding_input_lookup74,binding_source_lookup74,binding_depth_lookup74]
    simpa only [normalizer,binding_normalizer_lookup74,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input74 x y z w v hx hy hz hw
  · rw [binding_input_lookup75,binding_source_lookup75,binding_depth_lookup75]
    simpa only [normalizer,binding_normalizer_lookup75,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input75 x y z w v hx hy hz hw
  · rw [binding_input_lookup76,binding_source_lookup76,binding_depth_lookup76]
    simpa only [normalizer,binding_normalizer_lookup76,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input76 x y z w v hx hy hz hw
  · rw [binding_input_lookup77,binding_source_lookup77,binding_depth_lookup77]
    simpa only [normalizer,binding_normalizer_lookup77,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input77 x y z w v hx hy hz hw
  · rw [binding_input_lookup78,binding_source_lookup78,binding_depth_lookup78]
    simpa only [normalizer,binding_normalizer_lookup78,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input78 x y z w v hx hy hz hw
  · rw [binding_input_lookup79,binding_source_lookup79,binding_depth_lookup79]
    simpa only [normalizer,binding_normalizer_lookup79,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input79 x y z w v hx hy hz hw
#print axioms input_binding_block07

theorem binding_input_lookup80 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 80=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input80 := rfl
theorem binding_source_lookup80 : selected ⟨80,by decide⟩=sourceRaw318 := rfl
theorem binding_depth_lookup80 : depth ⟨80,by decide⟩=4 := rfl
theorem binding_normalizer_lookup80 : normalizerData 80=((8/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup81 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 81=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input81 := rfl
theorem binding_source_lookup81 : selected ⟨81,by decide⟩=sourceRaw320 := rfl
theorem binding_depth_lookup81 : depth ⟨81,by decide⟩=4 := rfl
theorem binding_normalizer_lookup81 : normalizerData 81=((-625/26244:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup82 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 82=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input82 := rfl
theorem binding_source_lookup82 : selected ⟨82,by decide⟩=sourceRaw367 := rfl
theorem binding_depth_lookup82 : depth ⟨82,by decide⟩=4 := rfl
theorem binding_normalizer_lookup82 : normalizerData 82=((-1/332150625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup83 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 83=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input83 := rfl
theorem binding_source_lookup83 : selected ⟨83,by decide⟩=sourceRaw404 := rfl
theorem binding_depth_lookup83 : depth ⟨83,by decide⟩=4 := rfl
theorem binding_normalizer_lookup83 : normalizerData 83=((-1/2582803260000:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup84 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 84=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input84 := rfl
theorem binding_source_lookup84 : selected ⟨84,by decide⟩=sourceRaw509 := rfl
theorem binding_depth_lookup84 : depth ⟨84,by decide⟩=4 := rfl
theorem binding_normalizer_lookup84 : normalizerData 84=((-625/531441:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup85 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 85=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input85 := rfl
theorem binding_source_lookup85 : selected ⟨85,by decide⟩=sourceRaw568 := rfl
theorem binding_depth_lookup85 : depth ⟨85,by decide⟩=4 := rfl
theorem binding_normalizer_lookup85 : normalizerData 85=((1/1:ℚ),(0,0,0,0)) := rfl
theorem binding_input_lookup86 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 86=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input86 := rfl
theorem binding_source_lookup86 : selected ⟨86,by decide⟩=sourceRaw569 := rfl
theorem binding_depth_lookup86 : depth ⟨86,by decide⟩=4 := rfl
theorem binding_normalizer_lookup86 : normalizerData 86=((-1/8857350000:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup87 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 87=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input87 := rfl
theorem binding_source_lookup87 : selected ⟨87,by decide⟩=sourceRaw571 := rfl
theorem binding_depth_lookup87 : depth ⟨87,by decide⟩=4 := rfl
theorem binding_normalizer_lookup87 : normalizerData 87=((-2/553584375:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup88 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 88=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input88 := rfl
theorem binding_source_lookup88 : selected ⟨88,by decide⟩=sourceRaw579 := rfl
theorem binding_depth_lookup88 : depth ⟨88,by decide⟩=4 := rfl
theorem binding_normalizer_lookup88 : normalizerData 88=((8/4100625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup89 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 89=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input89 := rfl
theorem binding_source_lookup89 : selected ⟨89,by decide⟩=sourceRaw580 := rfl
theorem binding_depth_lookup89 : depth ⟨89,by decide⟩=4 := rfl
theorem binding_normalizer_lookup89 : normalizerData 89=((-8/4100625:ℚ),(0,3,2,0)) := rfl

theorem input_binding_block08 (i : Fin 340) (hlo : 80 ≤ i.val) (hhi : i.val < 90) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 80 ≤ i at hlo
  change i < 90 at hhi
  interval_cases i
  · rw [binding_input_lookup80,binding_source_lookup80,binding_depth_lookup80]
    simpa only [normalizer,binding_normalizer_lookup80,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input80 x y z w v hx hy hz hw
  · rw [binding_input_lookup81,binding_source_lookup81,binding_depth_lookup81]
    simpa only [normalizer,binding_normalizer_lookup81,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input81 x y z w v hx hy hz hw
  · rw [binding_input_lookup82,binding_source_lookup82,binding_depth_lookup82]
    simpa only [normalizer,binding_normalizer_lookup82,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input82 x y z w v hx hy hz hw
  · rw [binding_input_lookup83,binding_source_lookup83,binding_depth_lookup83]
    simpa only [normalizer,binding_normalizer_lookup83,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input83 x y z w v hx hy hz hw
  · rw [binding_input_lookup84,binding_source_lookup84,binding_depth_lookup84]
    simpa only [normalizer,binding_normalizer_lookup84,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input84 x y z w v hx hy hz hw
  · rw [binding_input_lookup85,binding_source_lookup85,binding_depth_lookup85]
    simpa only [normalizer,binding_normalizer_lookup85,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input85 x y z w v hx hy hz hw
  · rw [binding_input_lookup86,binding_source_lookup86,binding_depth_lookup86]
    simpa only [normalizer,binding_normalizer_lookup86,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input86 x y z w v hx hy hz hw
  · rw [binding_input_lookup87,binding_source_lookup87,binding_depth_lookup87]
    simpa only [normalizer,binding_normalizer_lookup87,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input87 x y z w v hx hy hz hw
  · rw [binding_input_lookup88,binding_source_lookup88,binding_depth_lookup88]
    simpa only [normalizer,binding_normalizer_lookup88,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input88 x y z w v hx hy hz hw
  · rw [binding_input_lookup89,binding_source_lookup89,binding_depth_lookup89]
    simpa only [normalizer,binding_normalizer_lookup89,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input89 x y z w v hx hy hz hw
#print axioms input_binding_block08

theorem binding_input_lookup90 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 90=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input90 := rfl
theorem binding_source_lookup90 : selected ⟨90,by decide⟩=sourceRaw582 := rfl
theorem binding_depth_lookup90 : depth ⟨90,by decide⟩=4 := rfl
theorem binding_normalizer_lookup90 : normalizerData 90=((-1/303750:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup91 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 91=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input91 := rfl
theorem binding_source_lookup91 : selected ⟨91,by decide⟩=sourceRaw585 := rfl
theorem binding_depth_lookup91 : depth ⟨91,by decide⟩=4 := rfl
theorem binding_normalizer_lookup91 : normalizerData 91=((-64/4100625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup92 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 92=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input92 := rfl
theorem binding_source_lookup92 : selected ⟨92,by decide⟩=sourceRaw586 := rfl
theorem binding_depth_lookup92 : depth ⟨92,by decide⟩=4 := rfl
theorem binding_normalizer_lookup92 : normalizerData 92=((-64/4100625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup93 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 93=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input93 := rfl
theorem binding_source_lookup93 : selected ⟨93,by decide⟩=sourceRaw587 := rfl
theorem binding_depth_lookup93 : depth ⟨93,by decide⟩=4 := rfl
theorem binding_normalizer_lookup93 : normalizerData 93=((1/13122:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup94 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 94=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input94 := rfl
theorem binding_source_lookup94 : selected ⟨94,by decide⟩=sourceRaw590 := rfl
theorem binding_depth_lookup94 : depth ⟨94,by decide⟩=4 := rfl
theorem binding_normalizer_lookup94 : normalizerData 94=((-8/151875:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup95 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 95=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input95 := rfl
theorem binding_source_lookup95 : selected ⟨95,by decide⟩=sourceRaw593 := rfl
theorem binding_depth_lookup95 : depth ⟨95,by decide⟩=4 := rfl
theorem binding_normalizer_lookup95 : normalizerData 95=((625/354294:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup96 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 96=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input96 := rfl
theorem binding_source_lookup96 : selected ⟨96,by decide⟩=sourceRaw594 := rfl
theorem binding_depth_lookup96 : depth ⟨96,by decide⟩=4 := rfl
theorem binding_normalizer_lookup96 : normalizerData 96=((625/354294:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup97 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 97=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input97 := rfl
theorem binding_source_lookup97 : selected ⟨97,by decide⟩=sourceRaw595 := rfl
theorem binding_depth_lookup97 : depth ⟨97,by decide⟩=4 := rfl
theorem binding_normalizer_lookup97 : normalizerData 97=((-1/1250:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup98 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 98=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input98 := rfl
theorem binding_source_lookup98 : selected ⟨98,by decide⟩=sourceRaw596 := rfl
theorem binding_depth_lookup98 : depth ⟨98,by decide⟩=4 := rfl
theorem binding_normalizer_lookup98 : normalizerData 98=((-1/1250:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup99 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 99=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input99 := rfl
theorem binding_source_lookup99 : selected ⟨99,by decide⟩=sourceRaw598 := rfl
theorem binding_depth_lookup99 : depth ⟨99,by decide⟩=4 := rfl
theorem binding_normalizer_lookup99 : normalizerData 99=((8/6561:ℚ),(0,4,0,0)) := rfl

theorem input_binding_block09 (i : Fin 340) (hlo : 90 ≤ i.val) (hhi : i.val < 100) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 90 ≤ i at hlo
  change i < 100 at hhi
  interval_cases i
  · rw [binding_input_lookup90,binding_source_lookup90,binding_depth_lookup90]
    simpa only [normalizer,binding_normalizer_lookup90,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input90 x y z w v hx hy hz hw
  · rw [binding_input_lookup91,binding_source_lookup91,binding_depth_lookup91]
    simpa only [normalizer,binding_normalizer_lookup91,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input91 x y z w v hx hy hz hw
  · rw [binding_input_lookup92,binding_source_lookup92,binding_depth_lookup92]
    simpa only [normalizer,binding_normalizer_lookup92,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input92 x y z w v hx hy hz hw
  · rw [binding_input_lookup93,binding_source_lookup93,binding_depth_lookup93]
    simpa only [normalizer,binding_normalizer_lookup93,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input93 x y z w v hx hy hz hw
  · rw [binding_input_lookup94,binding_source_lookup94,binding_depth_lookup94]
    simpa only [normalizer,binding_normalizer_lookup94,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input94 x y z w v hx hy hz hw
  · rw [binding_input_lookup95,binding_source_lookup95,binding_depth_lookup95]
    simpa only [normalizer,binding_normalizer_lookup95,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input95 x y z w v hx hy hz hw
  · rw [binding_input_lookup96,binding_source_lookup96,binding_depth_lookup96]
    simpa only [normalizer,binding_normalizer_lookup96,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input96 x y z w v hx hy hz hw
  · rw [binding_input_lookup97,binding_source_lookup97,binding_depth_lookup97]
    simpa only [normalizer,binding_normalizer_lookup97,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input97 x y z w v hx hy hz hw
  · rw [binding_input_lookup98,binding_source_lookup98,binding_depth_lookup98]
    simpa only [normalizer,binding_normalizer_lookup98,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input98 x y z w v hx hy hz hw
  · rw [binding_input_lookup99,binding_source_lookup99,binding_depth_lookup99]
    simpa only [normalizer,binding_normalizer_lookup99,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input99 x y z w v hx hy hz hw
#print axioms input_binding_block09

theorem binding_input_lookup100 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 100=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input100 := rfl
theorem binding_source_lookup100 : selected ⟨100,by decide⟩=sourceRaw599 := rfl
theorem binding_depth_lookup100 : depth ⟨100,by decide⟩=4 := rfl
theorem binding_normalizer_lookup100 : normalizerData 100=((64/759375:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup101 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 101=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input101 := rfl
theorem binding_source_lookup101 : selected ⟨101,by decide⟩=sourceRaw600 := rfl
theorem binding_depth_lookup101 : depth ⟨101,by decide⟩=4 := rfl
theorem binding_normalizer_lookup101 : normalizerData 101=((64/759375:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup102 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 102=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input102 := rfl
theorem binding_source_lookup102 : selected ⟨102,by decide⟩=sourceRaw601 := rfl
theorem binding_depth_lookup102 : depth ⟨102,by decide⟩=4 := rfl
theorem binding_normalizer_lookup102 : normalizerData 102=((1/972:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup103 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 103=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input103 := rfl
theorem binding_source_lookup103 : selected ⟨103,by decide⟩=sourceRaw602 := rfl
theorem binding_depth_lookup103 : depth ⟨103,by decide⟩=4 := rfl
theorem binding_normalizer_lookup103 : normalizerData 103=((1/972:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup104 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 104=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input104 := rfl
theorem binding_source_lookup104 : selected ⟨104,by decide⟩=sourceRaw603 := rfl
theorem binding_depth_lookup104 : depth ⟨104,by decide⟩=4 := rfl
theorem binding_normalizer_lookup104 : normalizerData 104=((1250/177147:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup105 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 105=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input105 := rfl
theorem binding_source_lookup105 : selected ⟨105,by decide⟩=sourceRaw604 := rfl
theorem binding_depth_lookup105 : depth ⟨105,by decide⟩=4 := rfl
theorem binding_normalizer_lookup105 : normalizerData 105=((1250/177147:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup106 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 106=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input106 := rfl
theorem binding_source_lookup106 : selected ⟨106,by decide⟩=sourceRaw605 := rfl
theorem binding_depth_lookup106 : depth ⟨106,by decide⟩=4 := rfl
theorem binding_normalizer_lookup106 : normalizerData 106=((-2/625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup107 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 107=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input107 := rfl
theorem binding_source_lookup107 : selected ⟨107,by decide⟩=sourceRaw606 := rfl
theorem binding_depth_lookup107 : depth ⟨107,by decide⟩=4 := rfl
theorem binding_normalizer_lookup107 : normalizerData 107=((-2/625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup108 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 108=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input108 := rfl
theorem binding_source_lookup108 : selected ⟨108,by decide⟩=sourceRaw607 := rfl
theorem binding_depth_lookup108 : depth ⟨108,by decide⟩=4 := rfl
theorem binding_normalizer_lookup108 : normalizerData 108=((-64/6561:ℚ),(0,3,0,0)) := rfl
theorem binding_input_lookup109 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 109=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input109 := rfl
theorem binding_source_lookup109 : selected ⟨109,by decide⟩=sourceRaw608 := rfl
theorem binding_depth_lookup109 : depth ⟨109,by decide⟩=4 := rfl
theorem binding_normalizer_lookup109 : normalizerData 109=((-64/6561:ℚ),(0,3,0,0)) := rfl

theorem input_binding_block10 (i : Fin 340) (hlo : 100 ≤ i.val) (hhi : i.val < 110) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 100 ≤ i at hlo
  change i < 110 at hhi
  interval_cases i
  · rw [binding_input_lookup100,binding_source_lookup100,binding_depth_lookup100]
    simpa only [normalizer,binding_normalizer_lookup100,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input100 x y z w v hx hy hz hw
  · rw [binding_input_lookup101,binding_source_lookup101,binding_depth_lookup101]
    simpa only [normalizer,binding_normalizer_lookup101,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input101 x y z w v hx hy hz hw
  · rw [binding_input_lookup102,binding_source_lookup102,binding_depth_lookup102]
    simpa only [normalizer,binding_normalizer_lookup102,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input102 x y z w v hx hy hz hw
  · rw [binding_input_lookup103,binding_source_lookup103,binding_depth_lookup103]
    simpa only [normalizer,binding_normalizer_lookup103,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input103 x y z w v hx hy hz hw
  · rw [binding_input_lookup104,binding_source_lookup104,binding_depth_lookup104]
    simpa only [normalizer,binding_normalizer_lookup104,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input104 x y z w v hx hy hz hw
  · rw [binding_input_lookup105,binding_source_lookup105,binding_depth_lookup105]
    simpa only [normalizer,binding_normalizer_lookup105,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input105 x y z w v hx hy hz hw
  · rw [binding_input_lookup106,binding_source_lookup106,binding_depth_lookup106]
    simpa only [normalizer,binding_normalizer_lookup106,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input106 x y z w v hx hy hz hw
  · rw [binding_input_lookup107,binding_source_lookup107,binding_depth_lookup107]
    simpa only [normalizer,binding_normalizer_lookup107,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input107 x y z w v hx hy hz hw
  · rw [binding_input_lookup108,binding_source_lookup108,binding_depth_lookup108]
    simpa only [normalizer,binding_normalizer_lookup108,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input108 x y z w v hx hy hz hw
  · rw [binding_input_lookup109,binding_source_lookup109,binding_depth_lookup109]
    simpa only [normalizer,binding_normalizer_lookup109,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input109 x y z w v hx hy hz hw
#print axioms input_binding_block10

theorem binding_input_lookup110 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 110=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input110 := rfl
theorem binding_source_lookup110 : selected ⟨110,by decide⟩=sourceRaw609 := rfl
theorem binding_depth_lookup110 : depth ⟨110,by decide⟩=4 := rfl
theorem binding_normalizer_lookup110 : normalizerData 110=((-125/26244:ℚ),(2,3,0,0)) := rfl
theorem binding_input_lookup111 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 111=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input111 := rfl
theorem binding_source_lookup111 : selected ⟨111,by decide⟩=sourceRaw610 := rfl
theorem binding_depth_lookup111 : depth ⟨111,by decide⟩=4 := rfl
theorem binding_normalizer_lookup111 : normalizerData 111=((-125/26244:ℚ),(2,3,0,0)) := rfl
theorem binding_input_lookup112 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 112=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input112 := rfl
theorem binding_source_lookup112 : selected ⟨112,by decide⟩=sourceRaw619 := rfl
theorem binding_depth_lookup112 : depth ⟨112,by decide⟩=4 := rfl
theorem binding_normalizer_lookup112 : normalizerData 112=((5000/6561:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup113 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 113=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input113 := rfl
theorem binding_source_lookup113 : selected ⟨113,by decide⟩=sourceRaw620 := rfl
theorem binding_depth_lookup113 : depth ⟨113,by decide⟩=4 := rfl
theorem binding_normalizer_lookup113 : normalizerData 113=((5000/6561:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup114 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 114=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input114 := rfl
theorem binding_source_lookup114 : selected ⟨114,by decide⟩=sourceRaw648 := rfl
theorem binding_depth_lookup114 : depth ⟨114,by decide⟩=4 := rfl
theorem binding_normalizer_lookup114 : normalizerData 114=((1/151875:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup115 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 115=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input115 := rfl
theorem binding_source_lookup115 : selected ⟨115,by decide⟩=sourceRaw649 := rfl
theorem binding_depth_lookup115 : depth ⟨115,by decide⟩=4 := rfl
theorem binding_normalizer_lookup115 : normalizerData 115=((1/151875:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup116 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 116=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input116 := rfl
theorem binding_source_lookup116 : selected ⟨116,by decide⟩=sourceRaw652 := rfl
theorem binding_depth_lookup116 : depth ⟨116,by decide⟩=4 := rfl
theorem binding_normalizer_lookup116 : normalizerData 116=((625/177147:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup117 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 117=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input117 := rfl
theorem binding_source_lookup117 : selected ⟨117,by decide⟩=sourceRaw653 := rfl
theorem binding_depth_lookup117 : depth ⟨117,by decide⟩=4 := rfl
theorem binding_normalizer_lookup117 : normalizerData 117=((625/177147:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup118 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 118=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input118 := rfl
theorem binding_source_lookup118 : selected ⟨118,by decide⟩=sourceRaw654 := rfl
theorem binding_depth_lookup118 : depth ⟨118,by decide⟩=4 := rfl
theorem binding_normalizer_lookup118 : normalizerData 118=((-1/625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup119 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 119=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input119 := rfl
theorem binding_source_lookup119 : selected ⟨119,by decide⟩=sourceRaw655 := rfl
theorem binding_depth_lookup119 : depth ⟨119,by decide⟩=4 := rfl
theorem binding_normalizer_lookup119 : normalizerData 119=((-1/625:ℚ),(0,3,2,0)) := rfl

theorem input_binding_block11 (i : Fin 340) (hlo : 110 ≤ i.val) (hhi : i.val < 120) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 110 ≤ i at hlo
  change i < 120 at hhi
  interval_cases i
  · rw [binding_input_lookup110,binding_source_lookup110,binding_depth_lookup110]
    simpa only [normalizer,binding_normalizer_lookup110,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input110 x y z w v hx hy hz hw
  · rw [binding_input_lookup111,binding_source_lookup111,binding_depth_lookup111]
    simpa only [normalizer,binding_normalizer_lookup111,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input111 x y z w v hx hy hz hw
  · rw [binding_input_lookup112,binding_source_lookup112,binding_depth_lookup112]
    simpa only [normalizer,binding_normalizer_lookup112,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input112 x y z w v hx hy hz hw
  · rw [binding_input_lookup113,binding_source_lookup113,binding_depth_lookup113]
    simpa only [normalizer,binding_normalizer_lookup113,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input113 x y z w v hx hy hz hw
  · rw [binding_input_lookup114,binding_source_lookup114,binding_depth_lookup114]
    simpa only [normalizer,binding_normalizer_lookup114,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input114 x y z w v hx hy hz hw
  · rw [binding_input_lookup115,binding_source_lookup115,binding_depth_lookup115]
    simpa only [normalizer,binding_normalizer_lookup115,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input115 x y z w v hx hy hz hw
  · rw [binding_input_lookup116,binding_source_lookup116,binding_depth_lookup116]
    simpa only [normalizer,binding_normalizer_lookup116,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input116 x y z w v hx hy hz hw
  · rw [binding_input_lookup117,binding_source_lookup117,binding_depth_lookup117]
    simpa only [normalizer,binding_normalizer_lookup117,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input117 x y z w v hx hy hz hw
  · rw [binding_input_lookup118,binding_source_lookup118,binding_depth_lookup118]
    simpa only [normalizer,binding_normalizer_lookup118,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input118 x y z w v hx hy hz hw
  · rw [binding_input_lookup119,binding_source_lookup119,binding_depth_lookup119]
    simpa only [normalizer,binding_normalizer_lookup119,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input119 x y z w v hx hy hz hw
#print axioms input_binding_block11

theorem binding_input_lookup120 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 120=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input120 := rfl
theorem binding_source_lookup120 : selected ⟨120,by decide⟩=sourceRaw666 := rfl
theorem binding_depth_lookup120 : depth ⟨120,by decide⟩=4 := rfl
theorem binding_normalizer_lookup120 : normalizerData 120=((1/6561:ℚ),(0,2,0,0)) := rfl
theorem binding_input_lookup121 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 121=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input121 := rfl
theorem binding_source_lookup121 : selected ⟨121,by decide⟩=sourceRaw677 := rfl
theorem binding_depth_lookup121 : depth ⟨121,by decide⟩=4 := rfl
theorem binding_normalizer_lookup121 : normalizerData 121=((-8/50625:ℚ),(0,1,2,0)) := rfl
theorem binding_input_lookup122 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 122=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input122 := rfl
theorem binding_source_lookup122 : selected ⟨122,by decide⟩=sourceRaw678 := rfl
theorem binding_depth_lookup122 : depth ⟨122,by decide⟩=4 := rfl
theorem binding_normalizer_lookup122 : normalizerData 122=((-8/50625:ℚ),(0,1,2,0)) := rfl
theorem binding_input_lookup123 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 123=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input123 := rfl
theorem binding_source_lookup123 : selected ⟨123,by decide⟩=sourceRaw679 := rfl
theorem binding_depth_lookup123 : depth ⟨123,by decide⟩=4 := rfl
theorem binding_normalizer_lookup123 : normalizerData 123=((-1/1250:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup124 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 124=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input124 := rfl
theorem binding_source_lookup124 : selected ⟨124,by decide⟩=sourceRaw680 := rfl
theorem binding_depth_lookup124 : depth ⟨124,by decide⟩=4 := rfl
theorem binding_normalizer_lookup124 : normalizerData 124=((-1/1250:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup125 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 125=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input125 := rfl
theorem binding_source_lookup125 : selected ⟨125,by decide⟩=sourceRaw681 := rfl
theorem binding_depth_lookup125 : depth ⟨125,by decide⟩=4 := rfl
theorem binding_normalizer_lookup125 : normalizerData 125=((2/1594323:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup126 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 126=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input126 := rfl
theorem binding_source_lookup126 : selected ⟨126,by decide⟩=sourceRaw682 := rfl
theorem binding_depth_lookup126 : depth ⟨126,by decide⟩=4 := rfl
theorem binding_normalizer_lookup126 : normalizerData 126=((2/1594323:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup127 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 127=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input127 := rfl
theorem binding_source_lookup127 : selected ⟨127,by decide⟩=sourceRaw683 := rfl
theorem binding_depth_lookup127 : depth ⟨127,by decide⟩=4 := rfl
theorem binding_normalizer_lookup127 : normalizerData 127=((-64/50625:ℚ),(0,1,2,0)) := rfl
theorem binding_input_lookup128 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 128=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input128 := rfl
theorem binding_source_lookup128 : selected ⟨128,by decide⟩=sourceRaw684 := rfl
theorem binding_depth_lookup128 : depth ⟨128,by decide⟩=4 := rfl
theorem binding_normalizer_lookup128 : normalizerData 128=((-64/50625:ℚ),(0,1,2,0)) := rfl
theorem binding_input_lookup129 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 129=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input129 := rfl
theorem binding_source_lookup129 : selected ⟨129,by decide⟩=sourceRaw685 := rfl
theorem binding_depth_lookup129 : depth ⟨129,by decide⟩=4 := rfl
theorem binding_normalizer_lookup129 : normalizerData 129=((-1/162:ℚ),(2,1,0,0)) := rfl

theorem input_binding_block12 (i : Fin 340) (hlo : 120 ≤ i.val) (hhi : i.val < 130) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 120 ≤ i at hlo
  change i < 130 at hhi
  interval_cases i
  · rw [binding_input_lookup120,binding_source_lookup120,binding_depth_lookup120]
    simpa only [normalizer,binding_normalizer_lookup120,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input120 x y z w v hx hy hz hw
  · rw [binding_input_lookup121,binding_source_lookup121,binding_depth_lookup121]
    simpa only [normalizer,binding_normalizer_lookup121,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input121 x y z w v hx hy hz hw
  · rw [binding_input_lookup122,binding_source_lookup122,binding_depth_lookup122]
    simpa only [normalizer,binding_normalizer_lookup122,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input122 x y z w v hx hy hz hw
  · rw [binding_input_lookup123,binding_source_lookup123,binding_depth_lookup123]
    simpa only [normalizer,binding_normalizer_lookup123,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input123 x y z w v hx hy hz hw
  · rw [binding_input_lookup124,binding_source_lookup124,binding_depth_lookup124]
    simpa only [normalizer,binding_normalizer_lookup124,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input124 x y z w v hx hy hz hw
  · rw [binding_input_lookup125,binding_source_lookup125,binding_depth_lookup125]
    simpa only [normalizer,binding_normalizer_lookup125,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input125 x y z w v hx hy hz hw
  · rw [binding_input_lookup126,binding_source_lookup126,binding_depth_lookup126]
    simpa only [normalizer,binding_normalizer_lookup126,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input126 x y z w v hx hy hz hw
  · rw [binding_input_lookup127,binding_source_lookup127,binding_depth_lookup127]
    simpa only [normalizer,binding_normalizer_lookup127,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input127 x y z w v hx hy hz hw
  · rw [binding_input_lookup128,binding_source_lookup128,binding_depth_lookup128]
    simpa only [normalizer,binding_normalizer_lookup128,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input128 x y z w v hx hy hz hw
  · rw [binding_input_lookup129,binding_source_lookup129,binding_depth_lookup129]
    simpa only [normalizer,binding_normalizer_lookup129,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input129 x y z w v hx hy hz hw
#print axioms input_binding_block12

theorem binding_input_lookup130 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 130=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input130 := rfl
theorem binding_source_lookup130 : selected ⟨130,by decide⟩=sourceRaw686 := rfl
theorem binding_depth_lookup130 : depth ⟨130,by decide⟩=4 := rfl
theorem binding_normalizer_lookup130 : normalizerData 130=((-1/162:ℚ),(2,1,0,0)) := rfl
theorem binding_input_lookup131 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 131=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input131 := rfl
theorem binding_source_lookup131 : selected ⟨131,by decide⟩=sourceRaw687 := rfl
theorem binding_depth_lookup131 : depth ⟨131,by decide⟩=4 := rfl
theorem binding_normalizer_lookup131 : normalizerData 131=((-8/625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup132 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 132=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input132 := rfl
theorem binding_source_lookup132 : selected ⟨132,by decide⟩=sourceRaw688 := rfl
theorem binding_depth_lookup132 : depth ⟨132,by decide⟩=4 := rfl
theorem binding_normalizer_lookup132 : normalizerData 132=((-8/625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup133 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 133=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input133 := rfl
theorem binding_source_lookup133 : selected ⟨133,by decide⟩=sourceRaw689 := rfl
theorem binding_depth_lookup133 : depth ⟨133,by decide⟩=4 := rfl
theorem binding_normalizer_lookup133 : normalizerData 133=((16/1594323:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup134 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 134=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input134 := rfl
theorem binding_source_lookup134 : selected ⟨134,by decide⟩=sourceRaw690 := rfl
theorem binding_depth_lookup134 : depth ⟨134,by decide⟩=4 := rfl
theorem binding_normalizer_lookup134 : normalizerData 134=((-16/1594323:ℚ),(0,5,0,0)) := rfl
theorem binding_input_lookup135 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 135=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input135 := rfl
theorem binding_source_lookup135 : selected ⟨135,by decide⟩=sourceRaw691 := rfl
theorem binding_depth_lookup135 : depth ⟨135,by decide⟩=4 := rfl
theorem binding_normalizer_lookup135 : normalizerData 135=((-625/3188646:ℚ),(2,5,0,0)) := rfl
theorem binding_input_lookup136 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 136=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input136 := rfl
theorem binding_source_lookup136 : selected ⟨136,by decide⟩=sourceRaw692 := rfl
theorem binding_depth_lookup136 : depth ⟨136,by decide⟩=4 := rfl
theorem binding_normalizer_lookup136 : normalizerData 136=((625/3188646:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup137 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 137=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input137 := rfl
theorem binding_source_lookup137 : selected ⟨137,by decide⟩=sourceRaw693 := rfl
theorem binding_depth_lookup137 : depth ⟨137,by decide⟩=4 := rfl
theorem binding_normalizer_lookup137 : normalizerData 137=((-1/11250:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup138 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 138=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input138 := rfl
theorem binding_source_lookup138 : selected ⟨138,by decide⟩=sourceRaw695 := rfl
theorem binding_depth_lookup138 : depth ⟨138,by decide⟩=4 := rfl
theorem binding_normalizer_lookup138 : normalizerData 138=((-8/81:ℚ),(0,1,0,0)) := rfl
theorem binding_input_lookup139 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 139=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input139 := rfl
theorem binding_source_lookup139 : selected ⟨139,by decide⟩=sourceRaw696 := rfl
theorem binding_depth_lookup139 : depth ⟨139,by decide⟩=4 := rfl
theorem binding_normalizer_lookup139 : normalizerData 139=((-8/81:ℚ),(0,1,0,0)) := rfl

theorem input_binding_block13 (i : Fin 340) (hlo : 130 ≤ i.val) (hhi : i.val < 140) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 130 ≤ i at hlo
  change i < 140 at hhi
  interval_cases i
  · rw [binding_input_lookup130,binding_source_lookup130,binding_depth_lookup130]
    simpa only [normalizer,binding_normalizer_lookup130,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input130 x y z w v hx hy hz hw
  · rw [binding_input_lookup131,binding_source_lookup131,binding_depth_lookup131]
    simpa only [normalizer,binding_normalizer_lookup131,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input131 x y z w v hx hy hz hw
  · rw [binding_input_lookup132,binding_source_lookup132,binding_depth_lookup132]
    simpa only [normalizer,binding_normalizer_lookup132,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input132 x y z w v hx hy hz hw
  · rw [binding_input_lookup133,binding_source_lookup133,binding_depth_lookup133]
    simpa only [normalizer,binding_normalizer_lookup133,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input133 x y z w v hx hy hz hw
  · rw [binding_input_lookup134,binding_source_lookup134,binding_depth_lookup134]
    simpa only [normalizer,binding_normalizer_lookup134,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input134 x y z w v hx hy hz hw
  · rw [binding_input_lookup135,binding_source_lookup135,binding_depth_lookup135]
    simpa only [normalizer,binding_normalizer_lookup135,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input135 x y z w v hx hy hz hw
  · rw [binding_input_lookup136,binding_source_lookup136,binding_depth_lookup136]
    simpa only [normalizer,binding_normalizer_lookup136,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input136 x y z w v hx hy hz hw
  · rw [binding_input_lookup137,binding_source_lookup137,binding_depth_lookup137]
    simpa only [normalizer,binding_normalizer_lookup137,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input137 x y z w v hx hy hz hw
  · rw [binding_input_lookup138,binding_source_lookup138,binding_depth_lookup138]
    simpa only [normalizer,binding_normalizer_lookup138,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input138 x y z w v hx hy hz hw
  · rw [binding_input_lookup139,binding_source_lookup139,binding_depth_lookup139]
    simpa only [normalizer,binding_normalizer_lookup139,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input139 x y z w v hx hy hz hw
#print axioms input_binding_block13

theorem binding_input_lookup140 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 140=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input140 := rfl
theorem binding_source_lookup140 : selected ⟨140,by decide⟩=sourceRaw697 := rfl
theorem binding_depth_lookup140 : depth ⟨140,by decide⟩=4 := rfl
theorem binding_normalizer_lookup140 : normalizerData 140=((-64/3125:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup141 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 141=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input141 := rfl
theorem binding_source_lookup141 : selected ⟨141,by decide⟩=sourceRaw698 := rfl
theorem binding_depth_lookup141 : depth ⟨141,by decide⟩=4 := rfl
theorem binding_normalizer_lookup141 : normalizerData 141=((-64/3125:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup142 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 142=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input142 := rfl
theorem binding_source_lookup142 : selected ⟨142,by decide⟩=sourceRaw699 := rfl
theorem binding_depth_lookup142 : depth ⟨142,by decide⟩=4 := rfl
theorem binding_normalizer_lookup142 : normalizerData 142=((1/4:ℚ),(2,0,0,0)) := rfl
theorem binding_input_lookup143 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 143=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input143 := rfl
theorem binding_source_lookup143 : selected ⟨143,by decide⟩=sourceRaw700 := rfl
theorem binding_depth_lookup143 : depth ⟨143,by decide⟩=4 := rfl
theorem binding_normalizer_lookup143 : normalizerData 143=((1/4:ℚ),(2,0,0,0)) := rfl
theorem binding_input_lookup144 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 144=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input144 := rfl
theorem binding_source_lookup144 : selected ⟨144,by decide⟩=sourceRaw701 := rfl
theorem binding_depth_lookup144 : depth ⟨144,by decide⟩=4 := rfl
theorem binding_normalizer_lookup144 : normalizerData 144=((-1250/1594323:ℚ),(0,5,0,0)) := rfl
theorem binding_input_lookup145 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 145=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input145 := rfl
theorem binding_source_lookup145 : selected ⟨145,by decide⟩=sourceRaw702 := rfl
theorem binding_depth_lookup145 : depth ⟨145,by decide⟩=4 := rfl
theorem binding_normalizer_lookup145 : normalizerData 145=((1250/1594323:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup146 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 146=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input146 := rfl
theorem binding_source_lookup146 : selected ⟨146,by decide⟩=sourceRaw703 := rfl
theorem binding_depth_lookup146 : depth ⟨146,by decide⟩=4 := rfl
theorem binding_normalizer_lookup146 : normalizerData 146=((-2/5625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup147 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 147=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input147 := rfl
theorem binding_source_lookup147 : selected ⟨147,by decide⟩=sourceRaw704 := rfl
theorem binding_depth_lookup147 : depth ⟨147,by decide⟩=4 := rfl
theorem binding_normalizer_lookup147 : normalizerData 147=((2/5625:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup148 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 148=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input148 := rfl
theorem binding_source_lookup148 : selected ⟨148,by decide⟩=sourceRaw705 := rfl
theorem binding_depth_lookup148 : depth ⟨148,by decide⟩=4 := rfl
theorem binding_normalizer_lookup148 : normalizerData 148=((-64/81:ℚ),(0,1,0,0)) := rfl
theorem binding_input_lookup149 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 149=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input149 := rfl
theorem binding_source_lookup149 : selected ⟨149,by decide⟩=sourceRaw706 := rfl
theorem binding_depth_lookup149 : depth ⟨149,by decide⟩=4 := rfl
theorem binding_normalizer_lookup149 : normalizerData 149=((-64/81:ℚ),(0,1,0,0)) := rfl

theorem input_binding_block14 (i : Fin 340) (hlo : 140 ≤ i.val) (hhi : i.val < 150) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 140 ≤ i at hlo
  change i < 150 at hhi
  interval_cases i
  · rw [binding_input_lookup140,binding_source_lookup140,binding_depth_lookup140]
    simpa only [normalizer,binding_normalizer_lookup140,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input140 x y z w v hx hy hz hw
  · rw [binding_input_lookup141,binding_source_lookup141,binding_depth_lookup141]
    simpa only [normalizer,binding_normalizer_lookup141,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input141 x y z w v hx hy hz hw
  · rw [binding_input_lookup142,binding_source_lookup142,binding_depth_lookup142]
    simpa only [normalizer,binding_normalizer_lookup142,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input142 x y z w v hx hy hz hw
  · rw [binding_input_lookup143,binding_source_lookup143,binding_depth_lookup143]
    simpa only [normalizer,binding_normalizer_lookup143,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input143 x y z w v hx hy hz hw
  · rw [binding_input_lookup144,binding_source_lookup144,binding_depth_lookup144]
    simpa only [normalizer,binding_normalizer_lookup144,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input144 x y z w v hx hy hz hw
  · rw [binding_input_lookup145,binding_source_lookup145,binding_depth_lookup145]
    simpa only [normalizer,binding_normalizer_lookup145,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input145 x y z w v hx hy hz hw
  · rw [binding_input_lookup146,binding_source_lookup146,binding_depth_lookup146]
    simpa only [normalizer,binding_normalizer_lookup146,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input146 x y z w v hx hy hz hw
  · rw [binding_input_lookup147,binding_source_lookup147,binding_depth_lookup147]
    simpa only [normalizer,binding_normalizer_lookup147,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input147 x y z w v hx hy hz hw
  · rw [binding_input_lookup148,binding_source_lookup148,binding_depth_lookup148]
    simpa only [normalizer,binding_normalizer_lookup148,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input148 x y z w v hx hy hz hw
  · rw [binding_input_lookup149,binding_source_lookup149,binding_depth_lookup149]
    simpa only [normalizer,binding_normalizer_lookup149,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input149 x y z w v hx hy hz hw
#print axioms input_binding_block14

theorem binding_input_lookup150 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 150=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input150 := rfl
theorem binding_source_lookup150 : selected ⟨150,by decide⟩=sourceRaw707 := rfl
theorem binding_depth_lookup150 : depth ⟨150,by decide⟩=4 := rfl
theorem binding_normalizer_lookup150 : normalizerData 150=((625/324:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup151 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 151=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input151 := rfl
theorem binding_source_lookup151 : selected ⟨151,by decide⟩=sourceRaw708 := rfl
theorem binding_depth_lookup151 : depth ⟨151,by decide⟩=4 := rfl
theorem binding_normalizer_lookup151 : normalizerData 151=((625/324:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup152 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 152=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input152 := rfl
theorem binding_source_lookup152 : selected ⟨152,by decide⟩=sourceRaw709 := rfl
theorem binding_depth_lookup152 : depth ⟨152,by decide⟩=4 := rfl
theorem binding_normalizer_lookup152 : normalizerData 152=((8/1:ℚ),(0,0,0,0)) := rfl
theorem binding_input_lookup153 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 153=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input153 := rfl
theorem binding_source_lookup153 : selected ⟨153,by decide⟩=sourceRaw710 := rfl
theorem binding_depth_lookup153 : depth ⟨153,by decide⟩=4 := rfl
theorem binding_normalizer_lookup153 : normalizerData 153=((8/1:ℚ),(0,0,0,0)) := rfl
theorem binding_input_lookup154 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 154=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input154 := rfl
theorem binding_source_lookup154 : selected ⟨154,by decide⟩=sourceRaw715 := rfl
theorem binding_depth_lookup154 : depth ⟨154,by decide⟩=4 := rfl
theorem binding_normalizer_lookup154 : normalizerData 154=((1/144:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup155 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 155=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input155 := rfl
theorem binding_source_lookup155 : selected ⟨155,by decide⟩=sourceRaw716 := rfl
theorem binding_depth_lookup155 : depth ⟨155,by decide⟩=4 := rfl
theorem binding_normalizer_lookup155 : normalizerData 155=((-1/144:ℚ),(2,3,0,0)) := rfl
theorem binding_input_lookup156 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 156=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input156 := rfl
theorem binding_source_lookup156 : selected ⟨156,by decide⟩=sourceRaw717 := rfl
theorem binding_depth_lookup156 : depth ⟨156,by decide⟩=4 := rfl
theorem binding_normalizer_lookup156 : normalizerData 156=((5000/81:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup157 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 157=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input157 := rfl
theorem binding_source_lookup157 : selected ⟨157,by decide⟩=sourceRaw718 := rfl
theorem binding_depth_lookup157 : depth ⟨157,by decide⟩=4 := rfl
theorem binding_normalizer_lookup157 : normalizerData 157=((5000/81:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup158 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 158=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input158 := rfl
theorem binding_source_lookup158 : selected ⟨158,by decide⟩=sourceRaw719 := rfl
theorem binding_depth_lookup158 : depth ⟨158,by decide⟩=4 := rfl
theorem binding_normalizer_lookup158 : normalizerData 158=((128/1:ℚ),(0,0,0,0)) := rfl
theorem binding_input_lookup159 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 159=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input159 := rfl
theorem binding_source_lookup159 : selected ⟨159,by decide⟩=sourceRaw720 := rfl
theorem binding_depth_lookup159 : depth ⟨159,by decide⟩=4 := rfl
theorem binding_normalizer_lookup159 : normalizerData 159=((128/1:ℚ),(0,0,0,0)) := rfl

theorem input_binding_block15 (i : Fin 340) (hlo : 150 ≤ i.val) (hhi : i.val < 160) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 150 ≤ i at hlo
  change i < 160 at hhi
  interval_cases i
  · rw [binding_input_lookup150,binding_source_lookup150,binding_depth_lookup150]
    simpa only [normalizer,binding_normalizer_lookup150,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input150 x y z w v hx hy hz hw
  · rw [binding_input_lookup151,binding_source_lookup151,binding_depth_lookup151]
    simpa only [normalizer,binding_normalizer_lookup151,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input151 x y z w v hx hy hz hw
  · rw [binding_input_lookup152,binding_source_lookup152,binding_depth_lookup152]
    simpa only [normalizer,binding_normalizer_lookup152,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input152 x y z w v hx hy hz hw
  · rw [binding_input_lookup153,binding_source_lookup153,binding_depth_lookup153]
    simpa only [normalizer,binding_normalizer_lookup153,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input153 x y z w v hx hy hz hw
  · rw [binding_input_lookup154,binding_source_lookup154,binding_depth_lookup154]
    simpa only [normalizer,binding_normalizer_lookup154,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input154 x y z w v hx hy hz hw
  · rw [binding_input_lookup155,binding_source_lookup155,binding_depth_lookup155]
    simpa only [normalizer,binding_normalizer_lookup155,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input155 x y z w v hx hy hz hw
  · rw [binding_input_lookup156,binding_source_lookup156,binding_depth_lookup156]
    simpa only [normalizer,binding_normalizer_lookup156,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input156 x y z w v hx hy hz hw
  · rw [binding_input_lookup157,binding_source_lookup157,binding_depth_lookup157]
    simpa only [normalizer,binding_normalizer_lookup157,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input157 x y z w v hx hy hz hw
  · rw [binding_input_lookup158,binding_source_lookup158,binding_depth_lookup158]
    simpa only [normalizer,binding_normalizer_lookup158,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input158 x y z w v hx hy hz hw
  · rw [binding_input_lookup159,binding_source_lookup159,binding_depth_lookup159]
    simpa only [normalizer,binding_normalizer_lookup159,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input159 x y z w v hx hy hz hw
#print axioms input_binding_block15

theorem binding_input_lookup160 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 160=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input160 := rfl
theorem binding_source_lookup160 : selected ⟨160,by decide⟩=sourceRaw723 := rfl
theorem binding_depth_lookup160 : depth ⟨160,by decide⟩=4 := rfl
theorem binding_normalizer_lookup160 : normalizerData 160=((-2/9:ℚ),(0,3,0,0)) := rfl
theorem binding_input_lookup161 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 161=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input161 := rfl
theorem binding_source_lookup161 : selected ⟨161,by decide⟩=sourceRaw739 := rfl
theorem binding_depth_lookup161 : depth ⟨161,by decide⟩=4 := rfl
theorem binding_normalizer_lookup161 : normalizerData 161=((1/390625:ℚ),(0,0,2,0)) := rfl
theorem binding_input_lookup162 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 162=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input162 := rfl
theorem binding_source_lookup162 : selected ⟨162,by decide⟩=sourceRaw740 := rfl
theorem binding_depth_lookup162 : depth ⟨162,by decide⟩=4 := rfl
theorem binding_normalizer_lookup162 : normalizerData 162=((-1/354294:ℚ),(2,3,0,0)) := rfl
theorem binding_input_lookup163 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 163=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input163 := rfl
theorem binding_source_lookup163 : selected ⟨163,by decide⟩=sourceRaw742 := rfl
theorem binding_depth_lookup163 : depth ⟨163,by decide⟩=4 := rfl
theorem binding_normalizer_lookup163 : normalizerData 163=((-2/177147:ℚ),(0,3,0,0)) := rfl
theorem binding_input_lookup164 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 164=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input164 := rfl
theorem binding_source_lookup164 : selected ⟨164,by decide⟩=sourceRaw744 := rfl
theorem binding_depth_lookup164 : depth ⟨164,by decide⟩=4 := rfl
theorem binding_normalizer_lookup164 : normalizerData 164=((-1/13122:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup165 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 165=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input165 := rfl
theorem binding_source_lookup165 : selected ⟨165,by decide⟩=sourceRaw745 := rfl
theorem binding_depth_lookup165 : depth ⟨165,by decide⟩=4 := rfl
theorem binding_normalizer_lookup165 : normalizerData 165=((1/13122:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup166 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 166=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input166 := rfl
theorem binding_source_lookup166 : selected ⟨166,by decide⟩=sourceRaw748 := rfl
theorem binding_depth_lookup166 : depth ⟨166,by decide⟩=4 := rfl
theorem binding_normalizer_lookup166 : normalizerData 166=((-8/6561:ℚ),(0,3,0,0)) := rfl
theorem binding_input_lookup167 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 167=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input167 := rfl
theorem binding_source_lookup167 : selected ⟨167,by decide⟩=sourceRaw749 := rfl
theorem binding_depth_lookup167 : depth ⟨167,by decide⟩=4 := rfl
theorem binding_normalizer_lookup167 : normalizerData 167=((-8/6561:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup168 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 168=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input168 := rfl
theorem binding_source_lookup168 : selected ⟨168,by decide⟩=sourceRaw764 := rfl
theorem binding_depth_lookup168 : depth ⟨168,by decide⟩=4 := rfl
theorem binding_normalizer_lookup168 : normalizerData 168=((1/1679616:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup169 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 169=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input169 := rfl
theorem binding_source_lookup169 : selected ⟨169,by decide⟩=sourceRaw767 := rfl
theorem binding_depth_lookup169 : depth ⟨169,by decide⟩=4 := rfl
theorem binding_normalizer_lookup169 : normalizerData 169=((-1/50625:ℚ),(0,1,2,0)) := rfl

theorem input_binding_block16 (i : Fin 340) (hlo : 160 ≤ i.val) (hhi : i.val < 170) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 160 ≤ i at hlo
  change i < 170 at hhi
  interval_cases i
  · rw [binding_input_lookup160,binding_source_lookup160,binding_depth_lookup160]
    simpa only [normalizer,binding_normalizer_lookup160,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input160 x y z w v hx hy hz hw
  · rw [binding_input_lookup161,binding_source_lookup161,binding_depth_lookup161]
    simpa only [normalizer,binding_normalizer_lookup161,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input161 x y z w v hx hy hz hw
  · rw [binding_input_lookup162,binding_source_lookup162,binding_depth_lookup162]
    simpa only [normalizer,binding_normalizer_lookup162,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input162 x y z w v hx hy hz hw
  · rw [binding_input_lookup163,binding_source_lookup163,binding_depth_lookup163]
    simpa only [normalizer,binding_normalizer_lookup163,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input163 x y z w v hx hy hz hw
  · rw [binding_input_lookup164,binding_source_lookup164,binding_depth_lookup164]
    simpa only [normalizer,binding_normalizer_lookup164,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input164 x y z w v hx hy hz hw
  · rw [binding_input_lookup165,binding_source_lookup165,binding_depth_lookup165]
    simpa only [normalizer,binding_normalizer_lookup165,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input165 x y z w v hx hy hz hw
  · rw [binding_input_lookup166,binding_source_lookup166,binding_depth_lookup166]
    simpa only [normalizer,binding_normalizer_lookup166,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input166 x y z w v hx hy hz hw
  · rw [binding_input_lookup167,binding_source_lookup167,binding_depth_lookup167]
    simpa only [normalizer,binding_normalizer_lookup167,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input167 x y z w v hx hy hz hw
  · rw [binding_input_lookup168,binding_source_lookup168,binding_depth_lookup168]
    simpa only [normalizer,binding_normalizer_lookup168,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input168 x y z w v hx hy hz hw
  · rw [binding_input_lookup169,binding_source_lookup169,binding_depth_lookup169]
    simpa only [normalizer,binding_normalizer_lookup169,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input169 x y z w v hx hy hz hw
#print axioms input_binding_block16

theorem binding_input_lookup170 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 170=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input170 := rfl
theorem binding_source_lookup170 : selected ⟨170,by decide⟩=sourceRaw768 := rfl
theorem binding_depth_lookup170 : depth ⟨170,by decide⟩=4 := rfl
theorem binding_normalizer_lookup170 : normalizerData 170=((-1/50625:ℚ),(0,1,2,0)) := rfl
theorem binding_input_lookup171 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 171=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input171 := rfl
theorem binding_source_lookup171 : selected ⟨171,by decide⟩=sourceRaw769 := rfl
theorem binding_depth_lookup171 : depth ⟨171,by decide⟩=4 := rfl
theorem binding_normalizer_lookup171 : normalizerData 171=((-1/1594323:ℚ),(0,5,0,0)) := rfl
theorem binding_input_lookup172 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 172=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input172 := rfl
theorem binding_source_lookup172 : selected ⟨172,by decide⟩=sourceRaw770 := rfl
theorem binding_depth_lookup172 : depth ⟨172,by decide⟩=4 := rfl
theorem binding_normalizer_lookup172 : normalizerData 172=((1/1594323:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup173 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 173=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input173 := rfl
theorem binding_source_lookup173 : selected ⟨173,by decide⟩=sourceRaw771 := rfl
theorem binding_depth_lookup173 : depth ⟨173,by decide⟩=4 := rfl
theorem binding_normalizer_lookup173 : normalizerData 173=((-1/625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup174 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 174=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input174 := rfl
theorem binding_source_lookup174 : selected ⟨174,by decide⟩=sourceRaw772 := rfl
theorem binding_depth_lookup174 : depth ⟨174,by decide⟩=4 := rfl
theorem binding_normalizer_lookup174 : normalizerData 174=((-1/625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup175 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 175=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input175 := rfl
theorem binding_source_lookup175 : selected ⟨175,by decide⟩=sourceRaw773 := rfl
theorem binding_depth_lookup175 : depth ⟨175,by decide⟩=4 := rfl
theorem binding_normalizer_lookup175 : normalizerData 175=((-1/81:ℚ),(0,1,0,0)) := rfl
theorem binding_input_lookup176 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 176=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input176 := rfl
theorem binding_source_lookup176 : selected ⟨176,by decide⟩=sourceRaw774 := rfl
theorem binding_depth_lookup176 : depth ⟨176,by decide⟩=4 := rfl
theorem binding_normalizer_lookup176 : normalizerData 176=((-1/81:ℚ),(0,1,0,0)) := rfl
theorem binding_input_lookup177 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 177=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input177 := rfl
theorem binding_source_lookup177 : selected ⟨177,by decide⟩=sourceRaw775 := rfl
theorem binding_depth_lookup177 : depth ⟨177,by decide⟩=4 := rfl
theorem binding_normalizer_lookup177 : normalizerData 177=((625/1594323:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup178 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 178=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input178 := rfl
theorem binding_source_lookup178 : selected ⟨178,by decide⟩=sourceRaw776 := rfl
theorem binding_depth_lookup178 : depth ⟨178,by decide⟩=4 := rfl
theorem binding_normalizer_lookup178 : normalizerData 178=((625/1594323:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup179 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 179=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input179 := rfl
theorem binding_source_lookup179 : selected ⟨179,by decide⟩=sourceRaw777 := rfl
theorem binding_depth_lookup179 : depth ⟨179,by decide⟩=4 := rfl
theorem binding_normalizer_lookup179 : normalizerData 179=((-1/5625:ℚ),(0,3,2,0)) := rfl

theorem input_binding_block17 (i : Fin 340) (hlo : 170 ≤ i.val) (hhi : i.val < 180) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 170 ≤ i at hlo
  change i < 180 at hhi
  interval_cases i
  · rw [binding_input_lookup170,binding_source_lookup170,binding_depth_lookup170]
    simpa only [normalizer,binding_normalizer_lookup170,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input170 x y z w v hx hy hz hw
  · rw [binding_input_lookup171,binding_source_lookup171,binding_depth_lookup171]
    simpa only [normalizer,binding_normalizer_lookup171,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input171 x y z w v hx hy hz hw
  · rw [binding_input_lookup172,binding_source_lookup172,binding_depth_lookup172]
    simpa only [normalizer,binding_normalizer_lookup172,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input172 x y z w v hx hy hz hw
  · rw [binding_input_lookup173,binding_source_lookup173,binding_depth_lookup173]
    simpa only [normalizer,binding_normalizer_lookup173,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input173 x y z w v hx hy hz hw
  · rw [binding_input_lookup174,binding_source_lookup174,binding_depth_lookup174]
    simpa only [normalizer,binding_normalizer_lookup174,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input174 x y z w v hx hy hz hw
  · rw [binding_input_lookup175,binding_source_lookup175,binding_depth_lookup175]
    simpa only [normalizer,binding_normalizer_lookup175,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input175 x y z w v hx hy hz hw
  · rw [binding_input_lookup176,binding_source_lookup176,binding_depth_lookup176]
    simpa only [normalizer,binding_normalizer_lookup176,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input176 x y z w v hx hy hz hw
  · rw [binding_input_lookup177,binding_source_lookup177,binding_depth_lookup177]
    simpa only [normalizer,binding_normalizer_lookup177,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input177 x y z w v hx hy hz hw
  · rw [binding_input_lookup178,binding_source_lookup178,binding_depth_lookup178]
    simpa only [normalizer,binding_normalizer_lookup178,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input178 x y z w v hx hy hz hw
  · rw [binding_input_lookup179,binding_source_lookup179,binding_depth_lookup179]
    simpa only [normalizer,binding_normalizer_lookup179,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input179 x y z w v hx hy hz hw
#print axioms input_binding_block17

theorem binding_input_lookup180 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 180=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input180 := rfl
theorem binding_source_lookup180 : selected ⟨180,by decide⟩=sourceRaw778 := rfl
theorem binding_depth_lookup180 : depth ⟨180,by decide⟩=4 := rfl
theorem binding_normalizer_lookup180 : normalizerData 180=((-1/5625:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup181 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 181=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input181 := rfl
theorem binding_source_lookup181 : selected ⟨181,by decide⟩=sourceRaw781 := rfl
theorem binding_depth_lookup181 : depth ⟨181,by decide⟩=4 := rfl
theorem binding_normalizer_lookup181 : normalizerData 181=((625/81:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup182 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 182=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input182 := rfl
theorem binding_source_lookup182 : selected ⟨182,by decide⟩=sourceRaw782 := rfl
theorem binding_depth_lookup182 : depth ⟨182,by decide⟩=4 := rfl
theorem binding_normalizer_lookup182 : normalizerData 182=((625/81:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup183 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 183=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input183 := rfl
theorem binding_source_lookup183 : selected ⟨183,by decide⟩=sourceRaw783 := rfl
theorem binding_depth_lookup183 : depth ⟨183,by decide⟩=4 := rfl
theorem binding_normalizer_lookup183 : normalizerData 183=((-1/9:ℚ),(0,3,0,0)) := rfl
theorem binding_input_lookup184 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 184=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input184 := rfl
theorem binding_source_lookup184 : selected ⟨184,by decide⟩=sourceRaw784 := rfl
theorem binding_depth_lookup184 : depth ⟨184,by decide⟩=4 := rfl
theorem binding_normalizer_lookup184 : normalizerData 184=((1/9:ℚ),(0,2,0,0)) := rfl
theorem binding_input_lookup185 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 185=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input185 := rfl
theorem binding_source_lookup185 : selected ⟨185,by decide⟩=sourceRaw798 := rfl
theorem binding_depth_lookup185 : depth ⟨185,by decide⟩=4 := rfl
theorem binding_normalizer_lookup185 : normalizerData 185=((-1/76527504:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup186 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 186=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input186 := rfl
theorem binding_source_lookup186 : selected ⟨186,by decide⟩=sourceRaw799 := rfl
theorem binding_depth_lookup186 : depth ⟨186,by decide⟩=4 := rfl
theorem binding_normalizer_lookup186 : normalizerData 186=((-1/76527504:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup187 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 187=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input187 := rfl
theorem binding_source_lookup187 : selected ⟨187,by decide⟩=sourceRaw800 := rfl
theorem binding_depth_lookup187 : depth ⟨187,by decide⟩=4 := rfl
theorem binding_normalizer_lookup187 : normalizerData 187=((-2/3125:ℚ),(0,0,2,0)) := rfl
theorem binding_input_lookup188 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 188=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input188 := rfl
theorem binding_source_lookup188 : selected ⟨188,by decide⟩=sourceRaw801 := rfl
theorem binding_depth_lookup188 : depth ⟨188,by decide⟩=4 := rfl
theorem binding_normalizer_lookup188 : normalizerData 188=((-2/3125:ℚ),(0,0,2,0)) := rfl
theorem binding_input_lookup189 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 189=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input189 := rfl
theorem binding_source_lookup189 : selected ⟨189,by decide⟩=sourceRaw803 := rfl
theorem binding_depth_lookup189 : depth ⟨189,by decide⟩=4 := rfl
theorem binding_normalizer_lookup189 : normalizerData 189=((-1/36450000:ℚ),(2,4,2,0)) := rfl

theorem input_binding_block18 (i : Fin 340) (hlo : 180 ≤ i.val) (hhi : i.val < 190) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 180 ≤ i at hlo
  change i < 190 at hhi
  interval_cases i
  · rw [binding_input_lookup180,binding_source_lookup180,binding_depth_lookup180]
    simpa only [normalizer,binding_normalizer_lookup180,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input180 x y z w v hx hy hz hw
  · rw [binding_input_lookup181,binding_source_lookup181,binding_depth_lookup181]
    simpa only [normalizer,binding_normalizer_lookup181,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input181 x y z w v hx hy hz hw
  · rw [binding_input_lookup182,binding_source_lookup182,binding_depth_lookup182]
    simpa only [normalizer,binding_normalizer_lookup182,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input182 x y z w v hx hy hz hw
  · rw [binding_input_lookup183,binding_source_lookup183,binding_depth_lookup183]
    simpa only [normalizer,binding_normalizer_lookup183,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input183 x y z w v hx hy hz hw
  · rw [binding_input_lookup184,binding_source_lookup184,binding_depth_lookup184]
    simpa only [normalizer,binding_normalizer_lookup184,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input184 x y z w v hx hy hz hw
  · rw [binding_input_lookup185,binding_source_lookup185,binding_depth_lookup185]
    simpa only [normalizer,binding_normalizer_lookup185,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input185 x y z w v hx hy hz hw
  · rw [binding_input_lookup186,binding_source_lookup186,binding_depth_lookup186]
    simpa only [normalizer,binding_normalizer_lookup186,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input186 x y z w v hx hy hz hw
  · rw [binding_input_lookup187,binding_source_lookup187,binding_depth_lookup187]
    simpa only [normalizer,binding_normalizer_lookup187,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input187 x y z w v hx hy hz hw
  · rw [binding_input_lookup188,binding_source_lookup188,binding_depth_lookup188]
    simpa only [normalizer,binding_normalizer_lookup188,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input188 x y z w v hx hy hz hw
  · rw [binding_input_lookup189,binding_source_lookup189,binding_depth_lookup189]
    simpa only [normalizer,binding_normalizer_lookup189,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input189 x y z w v hx hy hz hw
#print axioms input_binding_block18

theorem binding_input_lookup190 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 190=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input190 := rfl
theorem binding_source_lookup190 : selected ⟨190,by decide⟩=sourceRaw806 := rfl
theorem binding_depth_lookup190 : depth ⟨190,by decide⟩=4 := rfl
theorem binding_normalizer_lookup190 : normalizerData 190=((-16/3125:ℚ),(0,0,2,0)) := rfl
theorem binding_input_lookup191 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 191=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input191 := rfl
theorem binding_source_lookup191 : selected ⟨191,by decide⟩=sourceRaw807 := rfl
theorem binding_depth_lookup191 : depth ⟨191,by decide⟩=4 := rfl
theorem binding_normalizer_lookup191 : normalizerData 191=((-16/3125:ℚ),(0,0,2,0)) := rfl
theorem binding_input_lookup192 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 192=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input192 := rfl
theorem binding_source_lookup192 : selected ⟨192,by decide⟩=sourceRaw811 := rfl
theorem binding_depth_lookup192 : depth ⟨192,by decide⟩=4 := rfl
theorem binding_normalizer_lookup192 : normalizerData 192=((-2/2278125:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup193 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 193=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input193 := rfl
theorem binding_source_lookup193 : selected ⟨193,by decide⟩=sourceRaw844 := rfl
theorem binding_depth_lookup193 : depth ⟨193,by decide⟩=4 := rfl
theorem binding_normalizer_lookup193 : normalizerData 193=((1/100000000:ℚ),(2,0,2,0)) := rfl
theorem binding_input_lookup194 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 194=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input194 := rfl
theorem binding_source_lookup194 : selected ⟨194,by decide⟩=sourceRaw845 := rfl
theorem binding_depth_lookup194 : depth ⟨194,by decide⟩=4 := rfl
theorem binding_normalizer_lookup194 : normalizerData 194=((-1/177147:ℚ),(0,3,0,0)) := rfl
theorem binding_input_lookup195 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 195=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input195 := rfl
theorem binding_source_lookup195 : selected ⟨195,by decide⟩=sourceRaw848 := rfl
theorem binding_depth_lookup195 : depth ⟨195,by decide⟩=4 := rfl
theorem binding_normalizer_lookup195 : normalizerData 195=((1/6561:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup196 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 196=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input196 := rfl
theorem binding_source_lookup196 : selected ⟨196,by decide⟩=sourceRaw862 := rfl
theorem binding_depth_lookup196 : depth ⟨196,by decide⟩=4 := rfl
theorem binding_normalizer_lookup196 : normalizerData 196=((-8/81:ℚ),(0,1,0,0)) := rfl
theorem binding_input_lookup197 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 197=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input197 := rfl
theorem binding_source_lookup197 : selected ⟨197,by decide⟩=sourceRaw916 := rfl
theorem binding_depth_lookup197 : depth ⟨197,by decide⟩=4 := rfl
theorem binding_normalizer_lookup197 : normalizerData 197=((1/656100000000:ℚ),(2,2,2,0)) := rfl
theorem binding_input_lookup198 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 198=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input198 := rfl
theorem binding_source_lookup198 : selected ⟨198,by decide⟩=sourceRaw970 := rfl
theorem binding_depth_lookup198 : depth ⟨198,by decide⟩=4 := rfl
theorem binding_normalizer_lookup198 : normalizerData 198=((1/110324037687890625:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup199 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 199=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input199 := rfl
theorem binding_source_lookup199 : selected ⟨199,by decide⟩=sourceRaw971 := rfl
theorem binding_depth_lookup199 : depth ⟨199,by decide⟩=4 := rfl
theorem binding_normalizer_lookup199 : normalizerData 199=((1/16815125390625:ℚ),(0,4,2,0)) := rfl

theorem input_binding_block19 (i : Fin 340) (hlo : 190 ≤ i.val) (hhi : i.val < 200) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 190 ≤ i at hlo
  change i < 200 at hhi
  interval_cases i
  · rw [binding_input_lookup190,binding_source_lookup190,binding_depth_lookup190]
    simpa only [normalizer,binding_normalizer_lookup190,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input190 x y z w v hx hy hz hw
  · rw [binding_input_lookup191,binding_source_lookup191,binding_depth_lookup191]
    simpa only [normalizer,binding_normalizer_lookup191,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input191 x y z w v hx hy hz hw
  · rw [binding_input_lookup192,binding_source_lookup192,binding_depth_lookup192]
    simpa only [normalizer,binding_normalizer_lookup192,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input192 x y z w v hx hy hz hw
  · rw [binding_input_lookup193,binding_source_lookup193,binding_depth_lookup193]
    simpa only [normalizer,binding_normalizer_lookup193,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input193 x y z w v hx hy hz hw
  · rw [binding_input_lookup194,binding_source_lookup194,binding_depth_lookup194]
    simpa only [normalizer,binding_normalizer_lookup194,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input194 x y z w v hx hy hz hw
  · rw [binding_input_lookup195,binding_source_lookup195,binding_depth_lookup195]
    simpa only [normalizer,binding_normalizer_lookup195,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input195 x y z w v hx hy hz hw
  · rw [binding_input_lookup196,binding_source_lookup196,binding_depth_lookup196]
    simpa only [normalizer,binding_normalizer_lookup196,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input196 x y z w v hx hy hz hw
  · rw [binding_input_lookup197,binding_source_lookup197,binding_depth_lookup197]
    simpa only [normalizer,binding_normalizer_lookup197,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input197 x y z w v hx hy hz hw
  · rw [binding_input_lookup198,binding_source_lookup198,binding_depth_lookup198]
    simpa only [normalizer,binding_normalizer_lookup198,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input198 x y z w v hx hy hz hw
  · rw [binding_input_lookup199,binding_source_lookup199,binding_depth_lookup199]
    simpa only [normalizer,binding_normalizer_lookup199,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input199 x y z w v hx hy hz hw
#print axioms input_binding_block19

theorem binding_input_lookup200 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 200=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input200 := rfl
theorem binding_source_lookup200 : selected ⟨200,by decide⟩=sourceRaw974 := rfl
theorem binding_depth_lookup200 : depth ⟨200,by decide⟩=4 := rfl
theorem binding_normalizer_lookup200 : normalizerData 200=((1/16815125390625:ℚ),(2,4,2,0)) := rfl
theorem binding_input_lookup201 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 201=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input201 := rfl
theorem binding_source_lookup201 : selected ⟨201,by decide⟩=sourceRaw977 := rfl
theorem binding_depth_lookup201 : depth ⟨201,by decide⟩=4 := rfl
theorem binding_normalizer_lookup201 : normalizerData 201=((1/2562890625:ℚ),(1,2,2,0)) := rfl
theorem binding_input_lookup202 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 202=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input202 := rfl
theorem binding_source_lookup202 : selected ⟨202,by decide⟩=sourceRaw978 := rfl
theorem binding_depth_lookup202 : depth ⟨202,by decide⟩=4 := rfl
theorem binding_normalizer_lookup202 : normalizerData 202=((1/282429536481:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup203 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 203=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input203 := rfl
theorem binding_source_lookup203 : selected ⟨203,by decide⟩=sourceRaw983 := rfl
theorem binding_depth_lookup203 : depth ⟨203,by decide⟩=4 := rfl
theorem binding_normalizer_lookup203 : normalizerData 203=((1/43046721:ℚ),(1,4,0,0)) := rfl
theorem binding_input_lookup204 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 204=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input204 := rfl
theorem binding_source_lookup204 : selected ⟨204,by decide⟩=sourceRaw986 := rfl
theorem binding_depth_lookup204 : depth ⟨204,by decide⟩=4 := rfl
theorem binding_normalizer_lookup204 : normalizerData 204=((1/2562890625:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup205 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 205=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input205 := rfl
theorem binding_source_lookup205 : selected ⟨205,by decide⟩=sourceRaw988 := rfl
theorem binding_depth_lookup205 : depth ⟨205,by decide⟩=4 := rfl
theorem binding_normalizer_lookup205 : normalizerData 205=((1/282429536481:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup206 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 206=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input206 := rfl
theorem binding_source_lookup206 : selected ⟨206,by decide⟩=sourceRaw989 := rfl
theorem binding_depth_lookup206 : depth ⟨206,by decide⟩=4 := rfl
theorem binding_normalizer_lookup206 : normalizerData 206=((1/16815125390625:ℚ),(2,4,2,0)) := rfl
theorem binding_input_lookup207 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 207=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input207 := rfl
theorem binding_source_lookup207 : selected ⟨207,by decide⟩=sourceRaw992 := rfl
theorem binding_depth_lookup207 : depth ⟨207,by decide⟩=4 := rfl
theorem binding_normalizer_lookup207 : normalizerData 207=((1/16815125390625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup208 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 208=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input208 := rfl
theorem binding_source_lookup208 : selected ⟨208,by decide⟩=sourceRaw993 := rfl
theorem binding_depth_lookup208 : depth ⟨208,by decide⟩=4 := rfl
theorem binding_normalizer_lookup208 : normalizerData 208=((1/282429536481:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup209 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 209=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input209 := rfl
theorem binding_source_lookup209 : selected ⟨209,by decide⟩=sourceRaw995 := rfl
theorem binding_depth_lookup209 : depth ⟨209,by decide⟩=4 := rfl
theorem binding_normalizer_lookup209 : normalizerData 209=((1/390625:ℚ),(0,0,2,0)) := rfl

theorem input_binding_block20 (i : Fin 340) (hlo : 200 ≤ i.val) (hhi : i.val < 210) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 200 ≤ i at hlo
  change i < 210 at hhi
  interval_cases i
  · rw [binding_input_lookup200,binding_source_lookup200,binding_depth_lookup200]
    simpa only [normalizer,binding_normalizer_lookup200,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input200 x y z w v hx hy hz hw
  · rw [binding_input_lookup201,binding_source_lookup201,binding_depth_lookup201]
    simpa only [normalizer,binding_normalizer_lookup201,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input201 x y z w v hx hy hz hw
  · rw [binding_input_lookup202,binding_source_lookup202,binding_depth_lookup202]
    simpa only [normalizer,binding_normalizer_lookup202,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input202 x y z w v hx hy hz hw
  · rw [binding_input_lookup203,binding_source_lookup203,binding_depth_lookup203]
    simpa only [normalizer,binding_normalizer_lookup203,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input203 x y z w v hx hy hz hw
  · rw [binding_input_lookup204,binding_source_lookup204,binding_depth_lookup204]
    simpa only [normalizer,binding_normalizer_lookup204,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input204 x y z w v hx hy hz hw
  · rw [binding_input_lookup205,binding_source_lookup205,binding_depth_lookup205]
    simpa only [normalizer,binding_normalizer_lookup205,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input205 x y z w v hx hy hz hw
  · rw [binding_input_lookup206,binding_source_lookup206,binding_depth_lookup206]
    simpa only [normalizer,binding_normalizer_lookup206,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input206 x y z w v hx hy hz hw
  · rw [binding_input_lookup207,binding_source_lookup207,binding_depth_lookup207]
    simpa only [normalizer,binding_normalizer_lookup207,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input207 x y z w v hx hy hz hw
  · rw [binding_input_lookup208,binding_source_lookup208,binding_depth_lookup208]
    simpa only [normalizer,binding_normalizer_lookup208,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input208 x y z w v hx hy hz hw
  · rw [binding_input_lookup209,binding_source_lookup209,binding_depth_lookup209]
    simpa only [normalizer,binding_normalizer_lookup209,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input209 x y z w v hx hy hz hw
#print axioms input_binding_block20

theorem binding_input_lookup210 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 210=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input210 := rfl
theorem binding_source_lookup210 : selected ⟨210,by decide⟩=sourceRaw996 := rfl
theorem binding_depth_lookup210 : depth ⟨210,by decide⟩=4 := rfl
theorem binding_normalizer_lookup210 : normalizerData 210=((1/110324037687890625:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup211 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 211=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input211 := rfl
theorem binding_source_lookup211 : selected ⟨211,by decide⟩=sourceRaw998 := rfl
theorem binding_depth_lookup211 : depth ⟨211,by decide⟩=4 := rfl
theorem binding_normalizer_lookup211 : normalizerData 211=((1/43046721:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup212 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 212=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input212 := rfl
theorem binding_source_lookup212 : selected ⟨212,by decide⟩=sourceRaw1003 := rfl
theorem binding_depth_lookup212 : depth ⟨212,by decide⟩=4 := rfl
theorem binding_normalizer_lookup212 : normalizerData 212=((1/282429536481:ℚ),(1,6,0,0)) := rfl
theorem binding_input_lookup213 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 213=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input213 := rfl
theorem binding_source_lookup213 : selected ⟨213,by decide⟩=sourceRaw1004 := rfl
theorem binding_depth_lookup213 : depth ⟨213,by decide⟩=4 := rfl
theorem binding_normalizer_lookup213 : normalizerData 213=((1/2562890625:ℚ),(2,2,2,0)) := rfl
theorem binding_input_lookup214 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 214=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input214 := rfl
theorem binding_source_lookup214 : selected ⟨214,by decide⟩=sourceRaw1013 := rfl
theorem binding_depth_lookup214 : depth ⟨214,by decide⟩=4 := rfl
theorem binding_normalizer_lookup214 : normalizerData 214=((1/6561:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup215 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 215=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input215 := rfl
theorem binding_source_lookup215 : selected ⟨215,by decide⟩=sourceRaw1019 := rfl
theorem binding_depth_lookup215 : depth ⟨215,by decide⟩=4 := rfl
theorem binding_normalizer_lookup215 : normalizerData 215=((1/16815125390625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup216 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 216=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input216 := rfl
theorem binding_source_lookup216 : selected ⟨216,by decide⟩=sourceRaw1022 := rfl
theorem binding_depth_lookup216 : depth ⟨216,by decide⟩=4 := rfl
theorem binding_normalizer_lookup216 : normalizerData 216=((1/390625:ℚ),(1,0,2,0)) := rfl
theorem binding_input_lookup217 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 217=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input217 := rfl
theorem binding_source_lookup217 : selected ⟨217,by decide⟩=sourceRaw1023 := rfl
theorem binding_depth_lookup217 : depth ⟨217,by decide⟩=4 := rfl
theorem binding_normalizer_lookup217 : normalizerData 217=((1/282429536481:ℚ),(1,6,0,0)) := rfl
theorem binding_input_lookup218 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 218=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input218 := rfl
theorem binding_source_lookup218 : selected ⟨218,by decide⟩=sourceRaw1025 := rfl
theorem binding_depth_lookup218 : depth ⟨218,by decide⟩=4 := rfl
theorem binding_normalizer_lookup218 : normalizerData 218=((1/16815125390625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup219 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 219=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input219 := rfl
theorem binding_source_lookup219 : selected ⟨219,by decide⟩=sourceRaw1028 := rfl
theorem binding_depth_lookup219 : depth ⟨219,by decide⟩=4 := rfl
theorem binding_normalizer_lookup219 : normalizerData 219=((1/43046721:ℚ),(1,4,0,0)) := rfl

theorem input_binding_block21 (i : Fin 340) (hlo : 210 ≤ i.val) (hhi : i.val < 220) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 210 ≤ i at hlo
  change i < 220 at hhi
  interval_cases i
  · rw [binding_input_lookup210,binding_source_lookup210,binding_depth_lookup210]
    simpa only [normalizer,binding_normalizer_lookup210,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input210 x y z w v hx hy hz hw
  · rw [binding_input_lookup211,binding_source_lookup211,binding_depth_lookup211]
    simpa only [normalizer,binding_normalizer_lookup211,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input211 x y z w v hx hy hz hw
  · rw [binding_input_lookup212,binding_source_lookup212,binding_depth_lookup212]
    simpa only [normalizer,binding_normalizer_lookup212,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input212 x y z w v hx hy hz hw
  · rw [binding_input_lookup213,binding_source_lookup213,binding_depth_lookup213]
    simpa only [normalizer,binding_normalizer_lookup213,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input213 x y z w v hx hy hz hw
  · rw [binding_input_lookup214,binding_source_lookup214,binding_depth_lookup214]
    simpa only [normalizer,binding_normalizer_lookup214,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input214 x y z w v hx hy hz hw
  · rw [binding_input_lookup215,binding_source_lookup215,binding_depth_lookup215]
    simpa only [normalizer,binding_normalizer_lookup215,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input215 x y z w v hx hy hz hw
  · rw [binding_input_lookup216,binding_source_lookup216,binding_depth_lookup216]
    simpa only [normalizer,binding_normalizer_lookup216,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input216 x y z w v hx hy hz hw
  · rw [binding_input_lookup217,binding_source_lookup217,binding_depth_lookup217]
    simpa only [normalizer,binding_normalizer_lookup217,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input217 x y z w v hx hy hz hw
  · rw [binding_input_lookup218,binding_source_lookup218,binding_depth_lookup218]
    simpa only [normalizer,binding_normalizer_lookup218,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input218 x y z w v hx hy hz hw
  · rw [binding_input_lookup219,binding_source_lookup219,binding_depth_lookup219]
    simpa only [normalizer,binding_normalizer_lookup219,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input219 x y z w v hx hy hz hw
#print axioms input_binding_block21

theorem binding_input_lookup220 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 220=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input220 := rfl
theorem binding_source_lookup220 : selected ⟨220,by decide⟩=sourceRaw1031 := rfl
theorem binding_depth_lookup220 : depth ⟨220,by decide⟩=4 := rfl
theorem binding_normalizer_lookup220 : normalizerData 220=((1/2562890625:ℚ),(1,2,2,0)) := rfl
theorem binding_input_lookup221 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 221=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input221 := rfl
theorem binding_source_lookup221 : selected ⟨221,by decide⟩=sourceRaw1033 := rfl
theorem binding_depth_lookup221 : depth ⟨221,by decide⟩=4 := rfl
theorem binding_normalizer_lookup221 : normalizerData 221=((1/282429536481:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup222 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 222=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input222 := rfl
theorem binding_source_lookup222 : selected ⟨222,by decide⟩=sourceRaw1034 := rfl
theorem binding_depth_lookup222 : depth ⟨222,by decide⟩=4 := rfl
theorem binding_normalizer_lookup222 : normalizerData 222=((1/16815125390625:ℚ),(1,4,2,0)) := rfl
theorem binding_input_lookup223 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 223=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input223 := rfl
theorem binding_source_lookup223 : selected ⟨223,by decide⟩=sourceRaw1043 := rfl
theorem binding_depth_lookup223 : depth ⟨223,by decide⟩=4 := rfl
theorem binding_normalizer_lookup223 : normalizerData 223=((1/43046721:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup224 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 224=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input224 := rfl
theorem binding_source_lookup224 : selected ⟨224,by decide⟩=sourceRaw1046 := rfl
theorem binding_depth_lookup224 : depth ⟨224,by decide⟩=4 := rfl
theorem binding_normalizer_lookup224 : normalizerData 224=((1/16815125390625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup225 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 225=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input225 := rfl
theorem binding_source_lookup225 : selected ⟨225,by decide⟩=sourceRaw1048 := rfl
theorem binding_depth_lookup225 : depth ⟨225,by decide⟩=4 := rfl
theorem binding_normalizer_lookup225 : normalizerData 225=((1/282429536481:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup226 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 226=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input226 := rfl
theorem binding_source_lookup226 : selected ⟨226,by decide⟩=sourceRaw1049 := rfl
theorem binding_depth_lookup226 : depth ⟨226,by decide⟩=4 := rfl
theorem binding_normalizer_lookup226 : normalizerData 226=((1/390625:ℚ),(1,0,2,0)) := rfl
theorem binding_input_lookup227 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 227=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input227 := rfl
theorem binding_source_lookup227 : selected ⟨227,by decide⟩=sourceRaw1050 := rfl
theorem binding_depth_lookup227 : depth ⟨227,by decide⟩=4 := rfl
theorem binding_normalizer_lookup227 : normalizerData 227=((1/110324037687890625:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup228 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 228=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input228 := rfl
theorem binding_source_lookup228 : selected ⟨228,by decide⟩=sourceRaw1052 := rfl
theorem binding_depth_lookup228 : depth ⟨228,by decide⟩=4 := rfl
theorem binding_normalizer_lookup228 : normalizerData 228=((1/16815125390625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup229 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 229=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input229 := rfl
theorem binding_source_lookup229 : selected ⟨229,by decide⟩=sourceRaw1064 := rfl
theorem binding_depth_lookup229 : depth ⟨229,by decide⟩=4 := rfl
theorem binding_normalizer_lookup229 : normalizerData 229=((1/16815125390625:ℚ),(0,4,2,0)) := rfl

theorem input_binding_block22 (i : Fin 340) (hlo : 220 ≤ i.val) (hhi : i.val < 230) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 220 ≤ i at hlo
  change i < 230 at hhi
  interval_cases i
  · rw [binding_input_lookup220,binding_source_lookup220,binding_depth_lookup220]
    simpa only [normalizer,binding_normalizer_lookup220,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input220 x y z w v hx hy hz hw
  · rw [binding_input_lookup221,binding_source_lookup221,binding_depth_lookup221]
    simpa only [normalizer,binding_normalizer_lookup221,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input221 x y z w v hx hy hz hw
  · rw [binding_input_lookup222,binding_source_lookup222,binding_depth_lookup222]
    simpa only [normalizer,binding_normalizer_lookup222,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input222 x y z w v hx hy hz hw
  · rw [binding_input_lookup223,binding_source_lookup223,binding_depth_lookup223]
    simpa only [normalizer,binding_normalizer_lookup223,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input223 x y z w v hx hy hz hw
  · rw [binding_input_lookup224,binding_source_lookup224,binding_depth_lookup224]
    simpa only [normalizer,binding_normalizer_lookup224,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input224 x y z w v hx hy hz hw
  · rw [binding_input_lookup225,binding_source_lookup225,binding_depth_lookup225]
    simpa only [normalizer,binding_normalizer_lookup225,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input225 x y z w v hx hy hz hw
  · rw [binding_input_lookup226,binding_source_lookup226,binding_depth_lookup226]
    simpa only [normalizer,binding_normalizer_lookup226,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input226 x y z w v hx hy hz hw
  · rw [binding_input_lookup227,binding_source_lookup227,binding_depth_lookup227]
    simpa only [normalizer,binding_normalizer_lookup227,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input227 x y z w v hx hy hz hw
  · rw [binding_input_lookup228,binding_source_lookup228,binding_depth_lookup228]
    simpa only [normalizer,binding_normalizer_lookup228,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input228 x y z w v hx hy hz hw
  · rw [binding_input_lookup229,binding_source_lookup229,binding_depth_lookup229]
    simpa only [normalizer,binding_normalizer_lookup229,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input229 x y z w v hx hy hz hw
#print axioms input_binding_block22

theorem binding_input_lookup230 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 230=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input230 := rfl
theorem binding_source_lookup230 : selected ⟨230,by decide⟩=sourceRaw1068 := rfl
theorem binding_depth_lookup230 : depth ⟨230,by decide⟩=4 := rfl
theorem binding_normalizer_lookup230 : normalizerData 230=((1/282429536481:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup231 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 231=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input231 := rfl
theorem binding_source_lookup231 : selected ⟨231,by decide⟩=sourceRaw1077 := rfl
theorem binding_depth_lookup231 : depth ⟨231,by decide⟩=4 := rfl
theorem binding_normalizer_lookup231 : normalizerData 231=((1/110324037687890625:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup232 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 232=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input232 := rfl
theorem binding_source_lookup232 : selected ⟨232,by decide⟩=sourceRaw1078 := rfl
theorem binding_depth_lookup232 : depth ⟨232,by decide⟩=4 := rfl
theorem binding_normalizer_lookup232 : normalizerData 232=((1/282429536481:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup233 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 233=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input233 := rfl
theorem binding_source_lookup233 : selected ⟨233,by decide⟩=sourceRaw1194 := rfl
theorem binding_depth_lookup233 : depth ⟨233,by decide⟩=4 := rfl
theorem binding_normalizer_lookup233 : normalizerData 233=((1/72301961339136:ℚ),(2,6,1,0)) := rfl
theorem binding_input_lookup234 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 234=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input234 := rfl
theorem binding_source_lookup234 : selected ⟨234,by decide⟩=sourceRaw1195 := rfl
theorem binding_depth_lookup234 : depth ⟨234,by decide⟩=4 := rfl
theorem binding_normalizer_lookup234 : normalizerData 234=((1/282429536481:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup235 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 235=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input235 := rfl
theorem binding_source_lookup235 : selected ⟨235,by decide⟩=sourceRaw1196 := rfl
theorem binding_depth_lookup235 : depth ⟨235,by decide⟩=4 := rfl
theorem binding_normalizer_lookup235 : normalizerData 235=((1/11019960576:ℚ),(2,4,1,0)) := rfl
theorem binding_input_lookup236 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 236=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input236 := rfl
theorem binding_source_lookup236 : selected ⟨236,by decide⟩=sourceRaw1197 := rfl
theorem binding_depth_lookup236 : depth ⟨236,by decide⟩=4 := rfl
theorem binding_normalizer_lookup236 : normalizerData 236=((1/282429536481:ℚ),(0,6,1,0)) := rfl
theorem binding_input_lookup237 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 237=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input237 := rfl
theorem binding_source_lookup237 : selected ⟨237,by decide⟩=sourceRaw1199 := rfl
theorem binding_depth_lookup237 : depth ⟨237,by decide⟩=4 := rfl
theorem binding_normalizer_lookup237 : normalizerData 237=((1/43046721:ℚ),(0,4,1,0)) := rfl
theorem binding_input_lookup238 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 238=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input238 := rfl
theorem binding_source_lookup238 : selected ⟨238,by decide⟩=sourceRaw1205 := rfl
theorem binding_depth_lookup238 : depth ⟨238,by decide⟩=4 := rfl
theorem binding_normalizer_lookup238 : normalizerData 238=((1/43046721:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup239 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 239=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input239 := rfl
theorem binding_source_lookup239 : selected ⟨239,by decide⟩=sourceRaw1261 := rfl
theorem binding_depth_lookup239 : depth ⟨239,by decide⟩=4 := rfl
theorem binding_normalizer_lookup239 : normalizerData 239=((-8/15752961:ℚ),(0,2,0,2)) := rfl

theorem input_binding_block23 (i : Fin 340) (hlo : 230 ≤ i.val) (hhi : i.val < 240) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 230 ≤ i at hlo
  change i < 240 at hhi
  interval_cases i
  · rw [binding_input_lookup230,binding_source_lookup230,binding_depth_lookup230]
    simpa only [normalizer,binding_normalizer_lookup230,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input230 x y z w v hx hy hz hw
  · rw [binding_input_lookup231,binding_source_lookup231,binding_depth_lookup231]
    simpa only [normalizer,binding_normalizer_lookup231,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input231 x y z w v hx hy hz hw
  · rw [binding_input_lookup232,binding_source_lookup232,binding_depth_lookup232]
    simpa only [normalizer,binding_normalizer_lookup232,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input232 x y z w v hx hy hz hw
  · rw [binding_input_lookup233,binding_source_lookup233,binding_depth_lookup233]
    simpa only [normalizer,binding_normalizer_lookup233,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input233 x y z w v hx hy hz hw
  · rw [binding_input_lookup234,binding_source_lookup234,binding_depth_lookup234]
    simpa only [normalizer,binding_normalizer_lookup234,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input234 x y z w v hx hy hz hw
  · rw [binding_input_lookup235,binding_source_lookup235,binding_depth_lookup235]
    simpa only [normalizer,binding_normalizer_lookup235,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input235 x y z w v hx hy hz hw
  · rw [binding_input_lookup236,binding_source_lookup236,binding_depth_lookup236]
    simpa only [normalizer,binding_normalizer_lookup236,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input236 x y z w v hx hy hz hw
  · rw [binding_input_lookup237,binding_source_lookup237,binding_depth_lookup237]
    simpa only [normalizer,binding_normalizer_lookup237,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input237 x y z w v hx hy hz hw
  · rw [binding_input_lookup238,binding_source_lookup238,binding_depth_lookup238]
    simpa only [normalizer,binding_normalizer_lookup238,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input238 x y z w v hx hy hz hw
  · rw [binding_input_lookup239,binding_source_lookup239,binding_depth_lookup239]
    simpa only [normalizer,binding_normalizer_lookup239,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input239 x y z w v hx hy hz hw
#print axioms input_binding_block23

theorem binding_input_lookup240 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 240=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input240 := rfl
theorem binding_source_lookup240 : selected ⟨240,by decide⟩=sourceRaw1284 := rfl
theorem binding_depth_lookup240 : depth ⟨240,by decide⟩=4 := rfl
theorem binding_normalizer_lookup240 : normalizerData 240=((19208/6561:ℚ),(0,2,0,0)) := rfl
theorem binding_input_lookup241 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 241=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input241 := rfl
theorem binding_source_lookup241 : selected ⟨241,by decide⟩=sourceRaw1299 := rfl
theorem binding_depth_lookup241 : depth ⟨241,by decide⟩=4 := rfl
theorem binding_normalizer_lookup241 : normalizerData 241=((-1/326653399296:ℚ),(2,4,0,2)) := rfl
theorem binding_input_lookup242 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 242=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input242 := rfl
theorem binding_source_lookup242 : selected ⟨242,by decide⟩=sourceRaw1321 := rfl
theorem binding_depth_lookup242 : depth ⟨242,by decide⟩=4 := rfl
theorem binding_normalizer_lookup242 : normalizerData 242=((-4/1275989841:ℚ),(0,4,0,2)) := rfl
theorem binding_input_lookup243 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 243=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input243 := rfl
theorem binding_source_lookup243 : selected ⟨243,by decide⟩=sourceRaw1324 := rfl
theorem binding_depth_lookup243 : depth ⟨243,by decide⟩=4 := rfl
theorem binding_normalizer_lookup243 : normalizerData 243=((-1/2551979682:ℚ),(2,4,0,2)) := rfl
theorem binding_input_lookup244 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 244=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input244 := rfl
theorem binding_source_lookup244 : selected ⟨244,by decide⟩=sourceRaw1326 := rfl
theorem binding_depth_lookup244 : depth ⟨244,by decide⟩=4 := rfl
theorem binding_normalizer_lookup244 : normalizerData 244=((-64/15752961:ℚ),(0,2,0,2)) := rfl
theorem binding_input_lookup245 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 245=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input245 := rfl
theorem binding_source_lookup245 : selected ⟨245,by decide⟩=sourceRaw1336 := rfl
theorem binding_depth_lookup245 : depth ⟨245,by decide⟩=4 := rfl
theorem binding_normalizer_lookup245 : normalizerData 245=((-1/1275989841:ℚ),(0,4,0,2)) := rfl
theorem binding_input_lookup246 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 246=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input246 := rfl
theorem binding_source_lookup246 : selected ⟨246,by decide⟩=sourceRaw1338 := rfl
theorem binding_depth_lookup246 : depth ⟨246,by decide⟩=4 := rfl
theorem binding_normalizer_lookup246 : normalizerData 246=((-1/11483908569:ℚ),(0,6,0,2)) := rfl
theorem binding_input_lookup247 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 247=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input247 := rfl
theorem binding_source_lookup247 : selected ⟨247,by decide⟩=sourceRaw1357 := rfl
theorem binding_depth_lookup247 : depth ⟨247,by decide⟩=4 := rfl
theorem binding_normalizer_lookup247 : normalizerData 247=((2401/26244:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup248 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 248=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input248 := rfl
theorem binding_source_lookup248 : selected ⟨248,by decide⟩=sourceRaw1395 := rfl
theorem binding_depth_lookup248 : depth ⟨248,by decide⟩=4 := rfl
theorem binding_normalizer_lookup248 : normalizerData 248=((-2/2170458719541:ℚ),(0,6,0,2)) := rfl
theorem binding_input_lookup249 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 249=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input249 := rfl
theorem binding_source_lookup249 : selected ⟨249,by decide⟩=sourceRaw1413 := rfl
theorem binding_depth_lookup249 : depth ⟨249,by decide⟩=4 := rfl
theorem binding_normalizer_lookup249 : normalizerData 249=((-8/15752961:ℚ),(0,2,0,2)) := rfl

theorem input_binding_block24 (i : Fin 340) (hlo : 240 ≤ i.val) (hhi : i.val < 250) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 240 ≤ i at hlo
  change i < 250 at hhi
  interval_cases i
  · rw [binding_input_lookup240,binding_source_lookup240,binding_depth_lookup240]
    simpa only [normalizer,binding_normalizer_lookup240,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input240 x y z w v hx hy hz hw
  · rw [binding_input_lookup241,binding_source_lookup241,binding_depth_lookup241]
    simpa only [normalizer,binding_normalizer_lookup241,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input241 x y z w v hx hy hz hw
  · rw [binding_input_lookup242,binding_source_lookup242,binding_depth_lookup242]
    simpa only [normalizer,binding_normalizer_lookup242,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input242 x y z w v hx hy hz hw
  · rw [binding_input_lookup243,binding_source_lookup243,binding_depth_lookup243]
    simpa only [normalizer,binding_normalizer_lookup243,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input243 x y z w v hx hy hz hw
  · rw [binding_input_lookup244,binding_source_lookup244,binding_depth_lookup244]
    simpa only [normalizer,binding_normalizer_lookup244,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input244 x y z w v hx hy hz hw
  · rw [binding_input_lookup245,binding_source_lookup245,binding_depth_lookup245]
    simpa only [normalizer,binding_normalizer_lookup245,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input245 x y z w v hx hy hz hw
  · rw [binding_input_lookup246,binding_source_lookup246,binding_depth_lookup246]
    simpa only [normalizer,binding_normalizer_lookup246,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input246 x y z w v hx hy hz hw
  · rw [binding_input_lookup247,binding_source_lookup247,binding_depth_lookup247]
    simpa only [normalizer,binding_normalizer_lookup247,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input247 x y z w v hx hy hz hw
  · rw [binding_input_lookup248,binding_source_lookup248,binding_depth_lookup248]
    simpa only [normalizer,binding_normalizer_lookup248,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input248 x y z w v hx hy hz hw
  · rw [binding_input_lookup249,binding_source_lookup249,binding_depth_lookup249]
    simpa only [normalizer,binding_normalizer_lookup249,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input249 x y z w v hx hy hz hw
#print axioms input_binding_block24

theorem binding_input_lookup250 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 250=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input250 := rfl
theorem binding_source_lookup250 : selected ⟨250,by decide⟩=sourceRaw1429 := rfl
theorem binding_depth_lookup250 : depth ⟨250,by decide⟩=4 := rfl
theorem binding_normalizer_lookup250 : normalizerData 250=((-1/2480524250904:ℚ),(2,6,0,2)) := rfl
theorem binding_input_lookup251 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 251=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input251 := rfl
theorem binding_source_lookup251 : selected ⟨251,by decide⟩=sourceRaw1446 := rfl
theorem binding_depth_lookup251 : depth ⟨251,by decide⟩=4 := rfl
theorem binding_normalizer_lookup251 : normalizerData 251=((-1/31505922:ℚ),(2,2,0,2)) := rfl
theorem binding_input_lookup252 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 252=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input252 := rfl
theorem binding_source_lookup252 : selected ⟨252,by decide⟩=sourceRaw1447 := rfl
theorem binding_depth_lookup252 : depth ⟨252,by decide⟩=4 := rfl
theorem binding_normalizer_lookup252 : normalizerData 252=((-8/2170458719541:ℚ),(0,6,0,2)) := rfl
theorem binding_input_lookup253 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 253=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input253 := rfl
theorem binding_source_lookup253 : selected ⟨253,by decide⟩=sourceRaw1566 := rfl
theorem binding_depth_lookup253 : depth ⟨253,by decide⟩=4 := rfl
theorem binding_normalizer_lookup253 : normalizerData 253=((-128/1275989841:ℚ),(0,4,0,2)) := rfl
theorem binding_input_lookup254 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 254=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input254 := rfl
theorem binding_source_lookup254 : selected ⟨254,by decide⟩=sourceRaw1833 := rfl
theorem binding_depth_lookup254 : depth ⟨254,by decide⟩=4 := rfl
theorem binding_normalizer_lookup254 : normalizerData 254=((-2/2977309629:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup255 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 255=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input255 := rfl
theorem binding_source_lookup255 : selected ⟨255,by decide⟩=sourceRaw1835 := rfl
theorem binding_depth_lookup255 : depth ⟨255,by decide⟩=4 := rfl
theorem binding_normalizer_lookup255 : normalizerData 255=((-1/31505922:ℚ),(2,3,0,2)) := rfl
theorem binding_input_lookup256 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 256=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input256 := rfl
theorem binding_source_lookup256 : selected ⟨256,by decide⟩=sourceRaw1857 := rfl
theorem binding_depth_lookup256 : depth ⟨256,by decide⟩=4 := rfl
theorem binding_normalizer_lookup256 : normalizerData 256=((-128/583443:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup257 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 257=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input257 := rfl
theorem binding_source_lookup257 : selected ⟨257,by decide⟩=sourceRaw1858 := rfl
theorem binding_depth_lookup257 : depth ⟨257,by decide⟩=4 := rfl
theorem binding_normalizer_lookup257 : normalizerData 257=((-128/583443:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup258 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 258=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input258 := rfl
theorem binding_source_lookup258 : selected ⟨258,by decide⟩=sourceRaw1861 := rfl
theorem binding_depth_lookup258 : depth ⟨258,by decide⟩=4 := rfl
theorem binding_normalizer_lookup258 : normalizerData 258=((2401/354294:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup259 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 259=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input259 := rfl
theorem binding_source_lookup259 : selected ⟨259,by decide⟩=sourceRaw1863 := rfl
theorem binding_depth_lookup259 : depth ⟨259,by decide⟩=4 := rfl
theorem binding_normalizer_lookup259 : normalizerData 259=((-8/16807:ℚ),(0,3,0,2)) := rfl

theorem input_binding_block25 (i : Fin 340) (hlo : 250 ≤ i.val) (hhi : i.val < 260) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 250 ≤ i at hlo
  change i < 260 at hhi
  interval_cases i
  · rw [binding_input_lookup250,binding_source_lookup250,binding_depth_lookup250]
    simpa only [normalizer,binding_normalizer_lookup250,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input250 x y z w v hx hy hz hw
  · rw [binding_input_lookup251,binding_source_lookup251,binding_depth_lookup251]
    simpa only [normalizer,binding_normalizer_lookup251,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input251 x y z w v hx hy hz hw
  · rw [binding_input_lookup252,binding_source_lookup252,binding_depth_lookup252]
    simpa only [normalizer,binding_normalizer_lookup252,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input252 x y z w v hx hy hz hw
  · rw [binding_input_lookup253,binding_source_lookup253,binding_depth_lookup253]
    simpa only [normalizer,binding_normalizer_lookup253,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input253 x y z w v hx hy hz hw
  · rw [binding_input_lookup254,binding_source_lookup254,binding_depth_lookup254]
    simpa only [normalizer,binding_normalizer_lookup254,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input254 x y z w v hx hy hz hw
  · rw [binding_input_lookup255,binding_source_lookup255,binding_depth_lookup255]
    simpa only [normalizer,binding_normalizer_lookup255,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input255 x y z w v hx hy hz hw
  · rw [binding_input_lookup256,binding_source_lookup256,binding_depth_lookup256]
    simpa only [normalizer,binding_normalizer_lookup256,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input256 x y z w v hx hy hz hw
  · rw [binding_input_lookup257,binding_source_lookup257,binding_depth_lookup257]
    simpa only [normalizer,binding_normalizer_lookup257,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input257 x y z w v hx hy hz hw
  · rw [binding_input_lookup258,binding_source_lookup258,binding_depth_lookup258]
    simpa only [normalizer,binding_normalizer_lookup258,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input258 x y z w v hx hy hz hw
  · rw [binding_input_lookup259,binding_source_lookup259,binding_depth_lookup259]
    simpa only [normalizer,binding_normalizer_lookup259,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input259 x y z w v hx hy hz hw
#print axioms input_binding_block25

theorem binding_input_lookup260 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 260=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input260 := rfl
theorem binding_source_lookup260 : selected ⟨260,by decide⟩=sourceRaw1875 := rfl
theorem binding_depth_lookup260 : depth ⟨260,by decide⟩=4 := rfl
theorem binding_normalizer_lookup260 : normalizerData 260=((2401/13122:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup261 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 261=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input261 := rfl
theorem binding_source_lookup261 : selected ⟨261,by decide⟩=sourceRaw1876 := rfl
theorem binding_depth_lookup261 : depth ⟨261,by decide⟩=4 := rfl
theorem binding_normalizer_lookup261 : normalizerData 261=((2401/13122:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup262 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 262=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input262 := rfl
theorem binding_source_lookup262 : selected ⟨262,by decide⟩=sourceRaw1884 := rfl
theorem binding_depth_lookup262 : depth ⟨262,by decide⟩=4 := rfl
theorem binding_normalizer_lookup262 : normalizerData 262=((9604/6561:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup263 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 263=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input263 := rfl
theorem binding_source_lookup263 : selected ⟨263,by decide⟩=sourceRaw1914 := rfl
theorem binding_depth_lookup263 : depth ⟨263,by decide⟩=4 := rfl
theorem binding_normalizer_lookup263 : normalizerData 263=((-1/2401:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup264 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 264=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input264 := rfl
theorem binding_source_lookup264 : selected ⟨264,by decide⟩=sourceRaw1915 := rfl
theorem binding_depth_lookup264 : depth ⟨264,by decide⟩=4 := rfl
theorem binding_normalizer_lookup264 : normalizerData 264=((-1/2401:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup265 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 265=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input265 := rfl
theorem binding_source_lookup265 : selected ⟨265,by decide⟩=sourceRaw1916 := rfl
theorem binding_depth_lookup265 : depth ⟨265,by decide⟩=4 := rfl
theorem binding_normalizer_lookup265 : normalizerData 265=((2401/177147:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup266 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 266=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input266 := rfl
theorem binding_source_lookup266 : selected ⟨266,by decide⟩=sourceRaw1917 := rfl
theorem binding_depth_lookup266 : depth ⟨266,by decide⟩=4 := rfl
theorem binding_normalizer_lookup266 : normalizerData 266=((2401/177147:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup267 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 267=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input267 := rfl
theorem binding_source_lookup267 : selected ⟨267,by decide⟩=sourceRaw1921 := rfl
theorem binding_depth_lookup267 : depth ⟨267,by decide⟩=4 := rfl
theorem binding_normalizer_lookup267 : normalizerData 267=((2401/6561:ℚ),(0,4,0,0)) := rfl
theorem binding_input_lookup268 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 268=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input268 := rfl
theorem binding_source_lookup268 : selected ⟨268,by decide⟩=sourceRaw1942 := rfl
theorem binding_depth_lookup268 : depth ⟨268,by decide⟩=4 := rfl
theorem binding_normalizer_lookup268 : normalizerData 268=((-1/4802:ℚ),(2,3,0,2)) := rfl
theorem binding_input_lookup269 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 269=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input269 := rfl
theorem binding_source_lookup269 : selected ⟨269,by decide⟩=sourceRaw1947 := rfl
theorem binding_depth_lookup269 : depth ⟨269,by decide⟩=4 := rfl
theorem binding_normalizer_lookup269 : normalizerData 269=((-4/2401:ℚ),(0,3,0,2)) := rfl

theorem input_binding_block26 (i : Fin 340) (hlo : 260 ≤ i.val) (hhi : i.val < 270) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 260 ≤ i at hlo
  change i < 270 at hhi
  interval_cases i
  · rw [binding_input_lookup260,binding_source_lookup260,binding_depth_lookup260]
    simpa only [normalizer,binding_normalizer_lookup260,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input260 x y z w v hx hy hz hw
  · rw [binding_input_lookup261,binding_source_lookup261,binding_depth_lookup261]
    simpa only [normalizer,binding_normalizer_lookup261,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input261 x y z w v hx hy hz hw
  · rw [binding_input_lookup262,binding_source_lookup262,binding_depth_lookup262]
    simpa only [normalizer,binding_normalizer_lookup262,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input262 x y z w v hx hy hz hw
  · rw [binding_input_lookup263,binding_source_lookup263,binding_depth_lookup263]
    simpa only [normalizer,binding_normalizer_lookup263,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input263 x y z w v hx hy hz hw
  · rw [binding_input_lookup264,binding_source_lookup264,binding_depth_lookup264]
    simpa only [normalizer,binding_normalizer_lookup264,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input264 x y z w v hx hy hz hw
  · rw [binding_input_lookup265,binding_source_lookup265,binding_depth_lookup265]
    simpa only [normalizer,binding_normalizer_lookup265,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input265 x y z w v hx hy hz hw
  · rw [binding_input_lookup266,binding_source_lookup266,binding_depth_lookup266]
    simpa only [normalizer,binding_normalizer_lookup266,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input266 x y z w v hx hy hz hw
  · rw [binding_input_lookup267,binding_source_lookup267,binding_depth_lookup267]
    simpa only [normalizer,binding_normalizer_lookup267,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input267 x y z w v hx hy hz hw
  · rw [binding_input_lookup268,binding_source_lookup268,binding_depth_lookup268]
    simpa only [normalizer,binding_normalizer_lookup268,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input268 x y z w v hx hy hz hw
  · rw [binding_input_lookup269,binding_source_lookup269,binding_depth_lookup269]
    simpa only [normalizer,binding_normalizer_lookup269,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input269 x y z w v hx hy hz hw
#print axioms input_binding_block26

theorem binding_input_lookup270 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 270=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input270 := rfl
theorem binding_source_lookup270 : selected ⟨270,by decide⟩=sourceRaw1948 := rfl
theorem binding_depth_lookup270 : depth ⟨270,by decide⟩=4 := rfl
theorem binding_normalizer_lookup270 : normalizerData 270=((-4/2401:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup271 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 271=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input271 := rfl
theorem binding_source_lookup271 : selected ⟨271,by decide⟩=sourceRaw1952 := rfl
theorem binding_depth_lookup271 : depth ⟨271,by decide⟩=4 := rfl
theorem binding_normalizer_lookup271 : normalizerData 271=((-1/2420208:ℚ),(2,3,0,2)) := rfl
theorem binding_input_lookup272 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 272=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input272 := rfl
theorem binding_source_lookup272 : selected ⟨272,by decide⟩=sourceRaw1956 := rfl
theorem binding_depth_lookup272 : depth ⟨272,by decide⟩=4 := rfl
theorem binding_normalizer_lookup272 : normalizerData 272=((-128/2401:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup273 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 273=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input273 := rfl
theorem binding_source_lookup273 : selected ⟨273,by decide⟩=sourceRaw1961 := rfl
theorem binding_depth_lookup273 : depth ⟨273,by decide⟩=4 := rfl
theorem binding_normalizer_lookup273 : normalizerData 273=((-8/151263:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup274 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 274=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input274 := rfl
theorem binding_source_lookup274 : selected ⟨274,by decide⟩=sourceRaw1962 := rfl
theorem binding_depth_lookup274 : depth ⟨274,by decide⟩=4 := rfl
theorem binding_normalizer_lookup274 : normalizerData 274=((-8/151263:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup275 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 275=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input275 := rfl
theorem binding_source_lookup275 : selected ⟨275,by decide⟩=sourceRaw1974 := rfl
theorem binding_depth_lookup275 : depth ⟨275,by decide⟩=4 := rfl
theorem binding_normalizer_lookup275 : normalizerData 275=((2401/162:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup276 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 276=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input276 := rfl
theorem binding_source_lookup276 : selected ⟨276,by decide⟩=sourceRaw2009 := rfl
theorem binding_depth_lookup276 : depth ⟨276,by decide⟩=4 := rfl
theorem binding_normalizer_lookup276 : normalizerData 276=((-1/2401:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup277 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 277=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input277 := rfl
theorem binding_source_lookup277 : selected ⟨277,by decide⟩=sourceRaw2013 := rfl
theorem binding_depth_lookup277 : depth ⟨277,by decide⟩=4 := rfl
theorem binding_normalizer_lookup277 : normalizerData 277=((-1/21609:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup278 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 278=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input278 := rfl
theorem binding_source_lookup278 : selected ⟨278,by decide⟩=sourceRaw2014 := rfl
theorem binding_depth_lookup278 : depth ⟨278,by decide⟩=4 := rfl
theorem binding_normalizer_lookup278 : normalizerData 278=((2401/1594323:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup279 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 279=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input279 := rfl
theorem binding_source_lookup279 : selected ⟨279,by decide⟩=sourceRaw2232 := rfl
theorem binding_depth_lookup279 : depth ⟨279,by decide⟩=4 := rfl
theorem binding_normalizer_lookup279 : normalizerData 279=((1/1628150074335205281:ℚ),(2,6,0,2)) := rfl

theorem input_binding_block27 (i : Fin 340) (hlo : 270 ≤ i.val) (hhi : i.val < 280) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 270 ≤ i at hlo
  change i < 280 at hhi
  interval_cases i
  · rw [binding_input_lookup270,binding_source_lookup270,binding_depth_lookup270]
    simpa only [normalizer,binding_normalizer_lookup270,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input270 x y z w v hx hy hz hw
  · rw [binding_input_lookup271,binding_source_lookup271,binding_depth_lookup271]
    simpa only [normalizer,binding_normalizer_lookup271,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input271 x y z w v hx hy hz hw
  · rw [binding_input_lookup272,binding_source_lookup272,binding_depth_lookup272]
    simpa only [normalizer,binding_normalizer_lookup272,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input272 x y z w v hx hy hz hw
  · rw [binding_input_lookup273,binding_source_lookup273,binding_depth_lookup273]
    simpa only [normalizer,binding_normalizer_lookup273,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input273 x y z w v hx hy hz hw
  · rw [binding_input_lookup274,binding_source_lookup274,binding_depth_lookup274]
    simpa only [normalizer,binding_normalizer_lookup274,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input274 x y z w v hx hy hz hw
  · rw [binding_input_lookup275,binding_source_lookup275,binding_depth_lookup275]
    simpa only [normalizer,binding_normalizer_lookup275,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input275 x y z w v hx hy hz hw
  · rw [binding_input_lookup276,binding_source_lookup276,binding_depth_lookup276]
    simpa only [normalizer,binding_normalizer_lookup276,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input276 x y z w v hx hy hz hw
  · rw [binding_input_lookup277,binding_source_lookup277,binding_depth_lookup277]
    simpa only [normalizer,binding_normalizer_lookup277,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input277 x y z w v hx hy hz hw
  · rw [binding_input_lookup278,binding_source_lookup278,binding_depth_lookup278]
    simpa only [normalizer,binding_normalizer_lookup278,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input278 x y z w v hx hy hz hw
  · rw [binding_input_lookup279,binding_source_lookup279,binding_depth_lookup279]
    simpa only [normalizer,binding_normalizer_lookup279,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input279 x y z w v hx hy hz hw
#print axioms input_binding_block27

theorem binding_input_lookup280 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 280=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input280 := rfl
theorem binding_source_lookup280 : selected ⟨280,by decide⟩=sourceRaw2236 := rfl
theorem binding_depth_lookup280 : depth ⟨280,by decide⟩=4 := rfl
theorem binding_normalizer_lookup280 : normalizerData 280=((1/248155780267521:ℚ),(2,4,0,2)) := rfl
theorem binding_input_lookup281 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 281=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input281 := rfl
theorem binding_source_lookup281 : selected ⟨281,by decide⟩=sourceRaw2239 := rfl
theorem binding_depth_lookup281 : depth ⟨281,by decide⟩=4 := rfl
theorem binding_normalizer_lookup281 : normalizerData 281=((1/37822859361:ℚ),(0,2,0,2)) := rfl
theorem binding_input_lookup282 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 282=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input282 := rfl
theorem binding_source_lookup282 : selected ⟨282,by decide⟩=sourceRaw2266 := rfl
theorem binding_depth_lookup282 : depth ⟨282,by decide⟩=4 := rfl
theorem binding_normalizer_lookup282 : normalizerData 282=((1/37822859361:ℚ),(0,2,0,2)) := rfl
theorem binding_input_lookup283 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 283=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input283 := rfl
theorem binding_source_lookup283 : selected ⟨283,by decide⟩=sourceRaw2284 := rfl
theorem binding_depth_lookup283 : depth ⟨283,by decide⟩=4 := rfl
theorem binding_normalizer_lookup283 : normalizerData 283=((1/5764801:ℚ),(1,0,0,2)) := rfl
theorem binding_input_lookup284 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 284=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input284 := rfl
theorem binding_source_lookup284 : selected ⟨284,by decide⟩=sourceRaw2329 := rfl
theorem binding_depth_lookup284 : depth ⟨284,by decide⟩=4 := rfl
theorem binding_normalizer_lookup284 : normalizerData 284=((1/37822859361:ℚ),(1,2,0,2)) := rfl
theorem binding_input_lookup285 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 285=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input285 := rfl
theorem binding_source_lookup285 : selected ⟨285,by decide⟩=sourceRaw2347 := rfl
theorem binding_depth_lookup285 : depth ⟨285,by decide⟩=4 := rfl
theorem binding_normalizer_lookup285 : normalizerData 285=((1/37822859361:ℚ),(2,2,0,2)) := rfl
theorem binding_input_lookup286 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 286=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input286 := rfl
theorem binding_source_lookup286 : selected ⟨286,by decide⟩=sourceRaw2637 := rfl
theorem binding_depth_lookup286 : depth ⟨286,by decide⟩=4 := rfl
theorem binding_normalizer_lookup286 : normalizerData 286=((-8/50242099989375:ℚ),(0,6,2,2)) := rfl
theorem binding_input_lookup287 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 287=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input287 := rfl
theorem binding_source_lookup287 : selected ⟨287,by decide⟩=sourceRaw2644 := rfl
theorem binding_depth_lookup287 : depth ⟨287,by decide⟩=4 := rfl
theorem binding_normalizer_lookup287 : normalizerData 287=((-1/7177442855625:ℚ),(0,6,2,2)) := rfl
theorem binding_input_lookup288 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 288=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input288 := rfl
theorem binding_source_lookup288 : selected ⟨288,by decide⟩=sourceRaw2651 := rfl
theorem binding_depth_lookup288 : depth ⟨288,by decide⟩=4 := rfl
theorem binding_normalizer_lookup288 : normalizerData 288=((-1/4019367999150000:ℚ),(2,6,2,2)) := rfl
theorem binding_input_lookup289 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 289=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input289 := rfl
theorem binding_source_lookup289 : selected ⟨289,by decide⟩=sourceRaw2654 := rfl
theorem binding_depth_lookup289 : depth ⟨289,by decide⟩=4 := rfl
theorem binding_normalizer_lookup289 : normalizerData 289=((-128/35887214278125:ℚ),(0,6,2,2)) := rfl

theorem input_binding_block28 (i : Fin 340) (hlo : 280 ≤ i.val) (hhi : i.val < 290) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 280 ≤ i at hlo
  change i < 290 at hhi
  interval_cases i
  · rw [binding_input_lookup280,binding_source_lookup280,binding_depth_lookup280]
    simpa only [normalizer,binding_normalizer_lookup280,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input280 x y z w v hx hy hz hw
  · rw [binding_input_lookup281,binding_source_lookup281,binding_depth_lookup281]
    simpa only [normalizer,binding_normalizer_lookup281,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input281 x y z w v hx hy hz hw
  · rw [binding_input_lookup282,binding_source_lookup282,binding_depth_lookup282]
    simpa only [normalizer,binding_normalizer_lookup282,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input282 x y z w v hx hy hz hw
  · rw [binding_input_lookup283,binding_source_lookup283,binding_depth_lookup283]
    simpa only [normalizer,binding_normalizer_lookup283,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input283 x y z w v hx hy hz hw
  · rw [binding_input_lookup284,binding_source_lookup284,binding_depth_lookup284]
    simpa only [normalizer,binding_normalizer_lookup284,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input284 x y z w v hx hy hz hw
  · rw [binding_input_lookup285,binding_source_lookup285,binding_depth_lookup285]
    simpa only [normalizer,binding_normalizer_lookup285,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input285 x y z w v hx hy hz hw
  · rw [binding_input_lookup286,binding_source_lookup286,binding_depth_lookup286]
    simpa only [normalizer,binding_normalizer_lookup286,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input286 x y z w v hx hy hz hw
  · rw [binding_input_lookup287,binding_source_lookup287,binding_depth_lookup287]
    simpa only [normalizer,binding_normalizer_lookup287,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input287 x y z w v hx hy hz hw
  · rw [binding_input_lookup288,binding_source_lookup288,binding_depth_lookup288]
    simpa only [normalizer,binding_normalizer_lookup288,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input288 x y z w v hx hy hz hw
  · rw [binding_input_lookup289,binding_source_lookup289,binding_depth_lookup289]
    simpa only [normalizer,binding_normalizer_lookup289,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input289 x y z w v hx hy hz hw
#print axioms input_binding_block28

theorem binding_input_lookup290 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 290=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input290 := rfl
theorem binding_source_lookup290 : selected ⟨290,by decide⟩=sourceRaw2656 := rfl
theorem binding_depth_lookup290 : depth ⟨290,by decide⟩=4 := rfl
theorem binding_normalizer_lookup290 : normalizerData 290=((-1/19691201250:ℚ),(2,3,2,2)) := rfl
theorem binding_input_lookup291 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 291=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input291 := rfl
theorem binding_source_lookup291 : selected ⟨291,by decide⟩=sourceRaw2664 := rfl
theorem binding_depth_lookup291 : depth ⟨291,by decide⟩=4 := rfl
theorem binding_normalizer_lookup291 : normalizerData 291=((2401/221433750:ℚ),(2,6,2,0)) := rfl
theorem binding_input_lookup292 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 292=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input292 := rfl
theorem binding_source_lookup292 : selected ⟨292,by decide⟩=sourceRaw2666 := rfl
theorem binding_depth_lookup292 : depth ⟨292,by decide⟩=4 := rfl
theorem binding_normalizer_lookup292 : normalizerData 292=((-5000/2977309629:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup293 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 293=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input293 := rfl
theorem binding_source_lookup293 : selected ⟨293,by decide⟩=sourceRaw2669 := rfl
theorem binding_depth_lookup293 : depth ⟨293,by decide⟩=4 := rfl
theorem binding_normalizer_lookup293 : normalizerData 293=((19208/553584375:ℚ),(0,6,2,0)) := rfl
theorem binding_input_lookup294 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 294=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input294 := rfl
theorem binding_source_lookup294 : selected ⟨294,by decide⟩=sourceRaw2674 := rfl
theorem binding_depth_lookup294 : depth ⟨294,by decide⟩=4 := rfl
theorem binding_normalizer_lookup294 : normalizerData 294=((9604/4100625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup295 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 295=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input295 := rfl
theorem binding_source_lookup295 : selected ⟨295,by decide⟩=sourceRaw2694 := rfl
theorem binding_depth_lookup295 : depth ⟨295,by decide⟩=4 := rfl
theorem binding_normalizer_lookup295 : normalizerData 295=((19208/50625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup296 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 296=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input296 := rfl
theorem binding_source_lookup296 : selected ⟨296,by decide⟩=sourceRaw2698 := rfl
theorem binding_depth_lookup296 : depth ⟨296,by decide⟩=4 := rfl
theorem binding_normalizer_lookup296 : normalizerData 296=((-1/31505922:ℚ),(2,3,2,2)) := rfl
theorem binding_input_lookup297 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 297=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input297 := rfl
theorem binding_source_lookup297 : selected ⟨297,by decide⟩=sourceRaw2701 := rfl
theorem binding_depth_lookup297 : depth ⟨297,by decide⟩=4 := rfl
theorem binding_normalizer_lookup297 : normalizerData 297=((2401/50625:ℚ),(0,4,2,0)) := rfl
theorem binding_input_lookup298 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 298=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input298 := rfl
theorem binding_source_lookup298 : selected ⟨298,by decide⟩=sourceRaw2707 := rfl
theorem binding_depth_lookup298 : depth ⟨298,by decide⟩=4 := rfl
theorem binding_normalizer_lookup298 : normalizerData 298=((1/635996122787189562890625:ℚ),(1,6,2,2)) := rfl
theorem binding_input_lookup299 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 299=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input299 := rfl
theorem binding_source_lookup299 : selected ⟨299,by decide⟩=sourceRaw2712 := rfl
theorem binding_depth_lookup299 : depth ⟨299,by decide⟩=4 := rfl
theorem binding_normalizer_lookup299 : normalizerData 299=((1/63527879748485376:ℚ),(2,4,2,2)) := rfl

theorem input_binding_block29 (i : Fin 340) (hlo : 290 ≤ i.val) (hhi : i.val < 300) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 290 ≤ i at hlo
  change i < 300 at hhi
  interval_cases i
  · rw [binding_input_lookup290,binding_source_lookup290,binding_depth_lookup290]
    simpa only [normalizer,binding_normalizer_lookup290,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input290 x y z w v hx hy hz hw
  · rw [binding_input_lookup291,binding_source_lookup291,binding_depth_lookup291]
    simpa only [normalizer,binding_normalizer_lookup291,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input291 x y z w v hx hy hz hw
  · rw [binding_input_lookup292,binding_source_lookup292,binding_depth_lookup292]
    simpa only [normalizer,binding_normalizer_lookup292,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input292 x y z w v hx hy hz hw
  · rw [binding_input_lookup293,binding_source_lookup293,binding_depth_lookup293]
    simpa only [normalizer,binding_normalizer_lookup293,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input293 x y z w v hx hy hz hw
  · rw [binding_input_lookup294,binding_source_lookup294,binding_depth_lookup294]
    simpa only [normalizer,binding_normalizer_lookup294,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input294 x y z w v hx hy hz hw
  · rw [binding_input_lookup295,binding_source_lookup295,binding_depth_lookup295]
    simpa only [normalizer,binding_normalizer_lookup295,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input295 x y z w v hx hy hz hw
  · rw [binding_input_lookup296,binding_source_lookup296,binding_depth_lookup296]
    simpa only [normalizer,binding_normalizer_lookup296,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input296 x y z w v hx hy hz hw
  · rw [binding_input_lookup297,binding_source_lookup297,binding_depth_lookup297]
    simpa only [normalizer,binding_normalizer_lookup297,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input297 x y z w v hx hy hz hw
  · rw [binding_input_lookup298,binding_source_lookup298,binding_depth_lookup298]
    simpa only [normalizer,binding_normalizer_lookup298,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input298 x y z w v hx hy hz hw
  · rw [binding_input_lookup299,binding_source_lookup299,binding_depth_lookup299]
    simpa only [normalizer,binding_normalizer_lookup299,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input299 x y z w v hx hy hz hw
#print axioms input_binding_block29

theorem binding_input_lookup300 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 300=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input300 := rfl
theorem binding_source_lookup300 : selected ⟨300,by decide⟩=sourceRaw11 := rfl
theorem binding_depth_lookup300 : depth ⟨300,by decide⟩=3 := rfl
theorem binding_normalizer_lookup300 : normalizerData 300=((8/91125:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup301 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 301=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input301 := rfl
theorem binding_source_lookup301 : selected ⟨301,by decide⟩=sourceRaw22 := rfl
theorem binding_depth_lookup301 : depth ⟨301,by decide⟩=3 := rfl
theorem binding_normalizer_lookup301 : normalizerData 301=((250/729:ℚ),(0,2,0,0)) := rfl
theorem binding_input_lookup302 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 302=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input302 := rfl
theorem binding_source_lookup302 : selected ⟨302,by decide⟩=sourceRaw38 := rfl
theorem binding_depth_lookup302 : depth ⟨302,by decide⟩=3 := rfl
theorem binding_normalizer_lookup302 : normalizerData 302=((125/5832:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup303 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 303=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input303 := rfl
theorem binding_source_lookup303 : selected ⟨303,by decide⟩=sourceRaw47 := rfl
theorem binding_depth_lookup303 : depth ⟨303,by decide⟩=3 := rfl
theorem binding_normalizer_lookup303 : normalizerData 303=((-2/91125:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup304 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 304=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input304 := rfl
theorem binding_source_lookup304 : selected ⟨304,by decide⟩=sourceRaw162 := rfl
theorem binding_depth_lookup304 : depth ⟨304,by decide⟩=3 := rfl
theorem binding_normalizer_lookup304 : normalizerData 304=((-8/91125:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup305 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 305=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input305 := rfl
theorem binding_source_lookup305 : selected ⟨305,by decide⟩=sourceRaw320 := rfl
theorem binding_depth_lookup305 : depth ⟨305,by decide⟩=3 := rfl
theorem binding_normalizer_lookup305 : normalizerData 305=((-125/5832:ℚ),(2,2,0,0)) := rfl
theorem binding_input_lookup306 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 306=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input306 := rfl
theorem binding_source_lookup306 : selected ⟨306,by decide⟩=sourceRaw593 := rfl
theorem binding_depth_lookup306 : depth ⟨306,by decide⟩=3 := rfl
theorem binding_normalizer_lookup306 : normalizerData 306=((125/78732:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup307 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 307=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input307 := rfl
theorem binding_source_lookup307 : selected ⟨307,by decide⟩=sourceRaw594 := rfl
theorem binding_depth_lookup307 : depth ⟨307,by decide⟩=3 := rfl
theorem binding_normalizer_lookup307 : normalizerData 307=((125/78732:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup308 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 308=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input308 := rfl
theorem binding_source_lookup308 : selected ⟨308,by decide⟩=sourceRaw595 := rfl
theorem binding_depth_lookup308 : depth ⟨308,by decide⟩=3 := rfl
theorem binding_normalizer_lookup308 : normalizerData 308=((-1/500:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup309 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 309=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input309 := rfl
theorem binding_source_lookup309 : selected ⟨309,by decide⟩=sourceRaw596 := rfl
theorem binding_depth_lookup309 : depth ⟨309,by decide⟩=3 := rfl
theorem binding_normalizer_lookup309 : normalizerData 309=((-1/500:ℚ),(2,3,2,0)) := rfl

theorem input_binding_block30 (i : Fin 340) (hlo : 300 ≤ i.val) (hhi : i.val < 310) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 300 ≤ i at hlo
  change i < 310 at hhi
  interval_cases i
  · rw [binding_input_lookup300,binding_source_lookup300,binding_depth_lookup300]
    simpa only [normalizer,binding_normalizer_lookup300,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input300 x y z w v hx hy hz hw
  · rw [binding_input_lookup301,binding_source_lookup301,binding_depth_lookup301]
    simpa only [normalizer,binding_normalizer_lookup301,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input301 x y z w v hx hy hz hw
  · rw [binding_input_lookup302,binding_source_lookup302,binding_depth_lookup302]
    simpa only [normalizer,binding_normalizer_lookup302,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input302 x y z w v hx hy hz hw
  · rw [binding_input_lookup303,binding_source_lookup303,binding_depth_lookup303]
    simpa only [normalizer,binding_normalizer_lookup303,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input303 x y z w v hx hy hz hw
  · rw [binding_input_lookup304,binding_source_lookup304,binding_depth_lookup304]
    simpa only [normalizer,binding_normalizer_lookup304,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input304 x y z w v hx hy hz hw
  · rw [binding_input_lookup305,binding_source_lookup305,binding_depth_lookup305]
    simpa only [normalizer,binding_normalizer_lookup305,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input305 x y z w v hx hy hz hw
  · rw [binding_input_lookup306,binding_source_lookup306,binding_depth_lookup306]
    simpa only [normalizer,binding_normalizer_lookup306,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input306 x y z w v hx hy hz hw
  · rw [binding_input_lookup307,binding_source_lookup307,binding_depth_lookup307]
    simpa only [normalizer,binding_normalizer_lookup307,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input307 x y z w v hx hy hz hw
  · rw [binding_input_lookup308,binding_source_lookup308,binding_depth_lookup308]
    simpa only [normalizer,binding_normalizer_lookup308,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input308 x y z w v hx hy hz hw
  · rw [binding_input_lookup309,binding_source_lookup309,binding_depth_lookup309]
    simpa only [normalizer,binding_normalizer_lookup309,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input309 x y z w v hx hy hz hw
#print axioms input_binding_block30

theorem binding_input_lookup310 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 310=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input310 := rfl
theorem binding_source_lookup310 : selected ⟨310,by decide⟩=sourceRaw599 := rfl
theorem binding_depth_lookup310 : depth ⟨310,by decide⟩=3 := rfl
theorem binding_normalizer_lookup310 : normalizerData 310=((8/151875:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup311 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 311=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input311 := rfl
theorem binding_source_lookup311 : selected ⟨311,by decide⟩=sourceRaw600 := rfl
theorem binding_depth_lookup311 : depth ⟨311,by decide⟩=3 := rfl
theorem binding_normalizer_lookup311 : normalizerData 311=((8/151875:ℚ),(0,2,2,0)) := rfl
theorem binding_input_lookup312 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 312=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input312 := rfl
theorem binding_source_lookup312 : selected ⟨312,by decide⟩=sourceRaw603 := rfl
theorem binding_depth_lookup312 : depth ⟨312,by decide⟩=3 := rfl
theorem binding_normalizer_lookup312 : normalizerData 312=((250/19683:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup313 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 313=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input313 := rfl
theorem binding_source_lookup313 : selected ⟨313,by decide⟩=sourceRaw604 := rfl
theorem binding_depth_lookup313 : depth ⟨313,by decide⟩=3 := rfl
theorem binding_normalizer_lookup313 : normalizerData 313=((250/19683:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup314 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 314=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input314 := rfl
theorem binding_source_lookup314 : selected ⟨314,by decide⟩=sourceRaw605 := rfl
theorem binding_depth_lookup314 : depth ⟨314,by decide⟩=3 := rfl
theorem binding_normalizer_lookup314 : normalizerData 314=((-2/125:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup315 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 315=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input315 := rfl
theorem binding_source_lookup315 : selected ⟨315,by decide⟩=sourceRaw606 := rfl
theorem binding_depth_lookup315 : depth ⟨315,by decide⟩=3 := rfl
theorem binding_normalizer_lookup315 : normalizerData 315=((-2/125:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup316 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 316=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input316 := rfl
theorem binding_source_lookup316 : selected ⟨316,by decide⟩=sourceRaw615 := rfl
theorem binding_depth_lookup316 : depth ⟨316,by decide⟩=3 := rfl
theorem binding_normalizer_lookup316 : normalizerData 316=((-16/125:ℚ),(0,3,2,0)) := rfl
theorem binding_input_lookup317 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 317=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input317 := rfl
theorem binding_source_lookup317 : selected ⟨317,by decide⟩=sourceRaw680 := rfl
theorem binding_depth_lookup317 : depth ⟨317,by decide⟩=3 := rfl
theorem binding_normalizer_lookup317 : normalizerData 317=((-1/500:ℚ),(2,3,2,0)) := rfl
theorem binding_input_lookup318 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 318=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input318 := rfl
theorem binding_source_lookup318 : selected ⟨318,by decide⟩=sourceRaw692 := rfl
theorem binding_depth_lookup318 : depth ⟨318,by decide⟩=3 := rfl
theorem binding_normalizer_lookup318 : normalizerData 318=((125/708588:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup319 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 319=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input319 := rfl
theorem binding_source_lookup319 : selected ⟨319,by decide⟩=sourceRaw844 := rfl
theorem binding_depth_lookup319 : depth ⟨319,by decide⟩=3 := rfl
theorem binding_normalizer_lookup319 : normalizerData 319=((1/1000000:ℚ),(2,0,2,0)) := rfl

theorem input_binding_block31 (i : Fin 340) (hlo : 310 ≤ i.val) (hhi : i.val < 320) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 310 ≤ i at hlo
  change i < 320 at hhi
  interval_cases i
  · rw [binding_input_lookup310,binding_source_lookup310,binding_depth_lookup310]
    simpa only [normalizer,binding_normalizer_lookup310,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input310 x y z w v hx hy hz hw
  · rw [binding_input_lookup311,binding_source_lookup311,binding_depth_lookup311]
    simpa only [normalizer,binding_normalizer_lookup311,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input311 x y z w v hx hy hz hw
  · rw [binding_input_lookup312,binding_source_lookup312,binding_depth_lookup312]
    simpa only [normalizer,binding_normalizer_lookup312,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input312 x y z w v hx hy hz hw
  · rw [binding_input_lookup313,binding_source_lookup313,binding_depth_lookup313]
    simpa only [normalizer,binding_normalizer_lookup313,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input313 x y z w v hx hy hz hw
  · rw [binding_input_lookup314,binding_source_lookup314,binding_depth_lookup314]
    simpa only [normalizer,binding_normalizer_lookup314,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input314 x y z w v hx hy hz hw
  · rw [binding_input_lookup315,binding_source_lookup315,binding_depth_lookup315]
    simpa only [normalizer,binding_normalizer_lookup315,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input315 x y z w v hx hy hz hw
  · rw [binding_input_lookup316,binding_source_lookup316,binding_depth_lookup316]
    simpa only [normalizer,binding_normalizer_lookup316,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input316 x y z w v hx hy hz hw
  · rw [binding_input_lookup317,binding_source_lookup317,binding_depth_lookup317]
    simpa only [normalizer,binding_normalizer_lookup317,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input317 x y z w v hx hy hz hw
  · rw [binding_input_lookup318,binding_source_lookup318,binding_depth_lookup318]
    simpa only [normalizer,binding_normalizer_lookup318,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input318 x y z w v hx hy hz hw
  · rw [binding_input_lookup319,binding_source_lookup319,binding_depth_lookup319]
    simpa only [normalizer,binding_normalizer_lookup319,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input319 x y z w v hx hy hz hw
#print axioms input_binding_block31

theorem binding_input_lookup320 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 320=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input320 := rfl
theorem binding_source_lookup320 : selected ⟨320,by decide⟩=sourceRaw988 := rfl
theorem binding_depth_lookup320 : depth ⟨320,by decide⟩=3 := rfl
theorem binding_normalizer_lookup320 : normalizerData 320=((1/387420489:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup321 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 321=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input321 := rfl
theorem binding_source_lookup321 : selected ⟨321,by decide⟩=sourceRaw993 := rfl
theorem binding_depth_lookup321 : depth ⟨321,by decide⟩=3 := rfl
theorem binding_normalizer_lookup321 : normalizerData 321=((1/387420489:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup322 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 322=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input322 := rfl
theorem binding_source_lookup322 : selected ⟨322,by decide⟩=sourceRaw995 := rfl
theorem binding_depth_lookup322 : depth ⟨322,by decide⟩=3 := rfl
theorem binding_normalizer_lookup322 : normalizerData 322=((1/15625:ℚ),(0,0,2,0)) := rfl
theorem binding_input_lookup323 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 323=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input323 := rfl
theorem binding_source_lookup323 : selected ⟨323,by decide⟩=sourceRaw1003 := rfl
theorem binding_depth_lookup323 : depth ⟨323,by decide⟩=3 := rfl
theorem binding_normalizer_lookup323 : normalizerData 323=((1/387420489:ℚ),(1,6,0,0)) := rfl
theorem binding_input_lookup324 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 324=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input324 := rfl
theorem binding_source_lookup324 : selected ⟨324,by decide⟩=sourceRaw1004 := rfl
theorem binding_depth_lookup324 : depth ⟨324,by decide⟩=3 := rfl
theorem binding_normalizer_lookup324 : normalizerData 324=((1/11390625:ℚ),(2,2,2,0)) := rfl
theorem binding_input_lookup325 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 325=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input325 := rfl
theorem binding_source_lookup325 : selected ⟨325,by decide⟩=sourceRaw1022 := rfl
theorem binding_depth_lookup325 : depth ⟨325,by decide⟩=3 := rfl
theorem binding_normalizer_lookup325 : normalizerData 325=((1/15625:ℚ),(1,0,2,0)) := rfl
theorem binding_input_lookup326 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 326=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input326 := rfl
theorem binding_source_lookup326 : selected ⟨326,by decide⟩=sourceRaw1033 := rfl
theorem binding_depth_lookup326 : depth ⟨326,by decide⟩=3 := rfl
theorem binding_normalizer_lookup326 : normalizerData 326=((1/387420489:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup327 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 327=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input327 := rfl
theorem binding_source_lookup327 : selected ⟨327,by decide⟩=sourceRaw1284 := rfl
theorem binding_depth_lookup327 : depth ⟨327,by decide⟩=3 := rfl
theorem binding_normalizer_lookup327 : normalizerData 327=((686/729:ℚ),(0,2,0,0)) := rfl
theorem binding_input_lookup328 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 328=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input328 := rfl
theorem binding_source_lookup328 : selected ⟨328,by decide⟩=sourceRaw1326 := rfl
theorem binding_depth_lookup328 : depth ⟨328,by decide⟩=3 := rfl
theorem binding_normalizer_lookup328 : normalizerData 328=((-8/250047:ℚ),(0,2,0,2)) := rfl
theorem binding_input_lookup329 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 329=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input329 := rfl
theorem binding_source_lookup329 : selected ⟨329,by decide⟩=sourceRaw1413 := rfl
theorem binding_depth_lookup329 : depth ⟨329,by decide⟩=3 := rfl
theorem binding_normalizer_lookup329 : normalizerData 329=((-2/250047:ℚ),(0,2,0,2)) := rfl

theorem input_binding_block32 (i : Fin 340) (hlo : 320 ≤ i.val) (hhi : i.val < 330) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 320 ≤ i at hlo
  change i < 330 at hhi
  interval_cases i
  · rw [binding_input_lookup320,binding_source_lookup320,binding_depth_lookup320]
    simpa only [normalizer,binding_normalizer_lookup320,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input320 x y z w v hx hy hz hw
  · rw [binding_input_lookup321,binding_source_lookup321,binding_depth_lookup321]
    simpa only [normalizer,binding_normalizer_lookup321,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input321 x y z w v hx hy hz hw
  · rw [binding_input_lookup322,binding_source_lookup322,binding_depth_lookup322]
    simpa only [normalizer,binding_normalizer_lookup322,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input322 x y z w v hx hy hz hw
  · rw [binding_input_lookup323,binding_source_lookup323,binding_depth_lookup323]
    simpa only [normalizer,binding_normalizer_lookup323,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input323 x y z w v hx hy hz hw
  · rw [binding_input_lookup324,binding_source_lookup324,binding_depth_lookup324]
    simpa only [normalizer,binding_normalizer_lookup324,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input324 x y z w v hx hy hz hw
  · rw [binding_input_lookup325,binding_source_lookup325,binding_depth_lookup325]
    simpa only [normalizer,binding_normalizer_lookup325,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input325 x y z w v hx hy hz hw
  · rw [binding_input_lookup326,binding_source_lookup326,binding_depth_lookup326]
    simpa only [normalizer,binding_normalizer_lookup326,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input326 x y z w v hx hy hz hw
  · rw [binding_input_lookup327,binding_source_lookup327,binding_depth_lookup327]
    simpa only [normalizer,binding_normalizer_lookup327,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input327 x y z w v hx hy hz hw
  · rw [binding_input_lookup328,binding_source_lookup328,binding_depth_lookup328]
    simpa only [normalizer,binding_normalizer_lookup328,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input328 x y z w v hx hy hz hw
  · rw [binding_input_lookup329,binding_source_lookup329,binding_depth_lookup329]
    simpa only [normalizer,binding_normalizer_lookup329,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input329 x y z w v hx hy hz hw
#print axioms input_binding_block32

theorem binding_input_lookup330 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 330=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input330 := rfl
theorem binding_source_lookup330 : selected ⟨330,by decide⟩=sourceRaw1857 := rfl
theorem binding_depth_lookup330 : depth ⟨330,by decide⟩=3 := rfl
theorem binding_normalizer_lookup330 : normalizerData 330=((-16/83349:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup331 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 331=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input331 := rfl
theorem binding_source_lookup331 : selected ⟨331,by decide⟩=sourceRaw1858 := rfl
theorem binding_depth_lookup331 : depth ⟨331,by decide⟩=3 := rfl
theorem binding_normalizer_lookup331 : normalizerData 331=((-16/83349:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup332 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 332=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input332 := rfl
theorem binding_source_lookup332 : selected ⟨332,by decide⟩=sourceRaw1861 := rfl
theorem binding_depth_lookup332 : depth ⟨332,by decide⟩=3 := rfl
theorem binding_normalizer_lookup332 : normalizerData 332=((343/78732:ℚ),(2,6,0,0)) := rfl
theorem binding_input_lookup333 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 333=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input333 := rfl
theorem binding_source_lookup333 : selected ⟨333,by decide⟩=sourceRaw1872 := rfl
theorem binding_depth_lookup333 : depth ⟨333,by decide⟩=3 := rfl
theorem binding_normalizer_lookup333 : normalizerData 333=((-16/343:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup334 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 334=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input334 := rfl
theorem binding_source_lookup334 : selected ⟨334,by decide⟩=sourceRaw1875 := rfl
theorem binding_depth_lookup334 : depth ⟨334,by decide⟩=3 := rfl
theorem binding_normalizer_lookup334 : normalizerData 334=((343/8748:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup335 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 335=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input335 := rfl
theorem binding_source_lookup335 : selected ⟨335,by decide⟩=sourceRaw1876 := rfl
theorem binding_depth_lookup335 : depth ⟨335,by decide⟩=3 := rfl
theorem binding_normalizer_lookup335 : normalizerData 335=((343/8748:ℚ),(2,4,0,0)) := rfl
theorem binding_input_lookup336 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 336=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input336 := rfl
theorem binding_source_lookup336 : selected ⟨336,by decide⟩=sourceRaw1914 := rfl
theorem binding_depth_lookup336 : depth ⟨336,by decide⟩=3 := rfl
theorem binding_normalizer_lookup336 : normalizerData 336=((-1/343:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup337 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 337=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input337 := rfl
theorem binding_source_lookup337 : selected ⟨337,by decide⟩=sourceRaw1915 := rfl
theorem binding_depth_lookup337 : depth ⟨337,by decide⟩=3 := rfl
theorem binding_normalizer_lookup337 : normalizerData 337=((-1/343:ℚ),(0,3,0,2)) := rfl
theorem binding_input_lookup338 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 338=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input338 := rfl
theorem binding_source_lookup338 : selected ⟨338,by decide⟩=sourceRaw1916 := rfl
theorem binding_depth_lookup338 : depth ⟨338,by decide⟩=3 := rfl
theorem binding_normalizer_lookup338 : normalizerData 338=((343/19683:ℚ),(0,6,0,0)) := rfl
theorem binding_input_lookup339 : QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs 339=QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.input339 := rfl
theorem binding_source_lookup339 : selected ⟨339,by decide⟩=sourceRaw1955 := rfl
theorem binding_depth_lookup339 : depth ⟨339,by decide⟩=3 := rfl
theorem binding_normalizer_lookup339 : normalizerData 339=((-16/343:ℚ),(0,3,0,2)) := rfl

theorem input_binding_block33 (i : Fin 340) (hlo : 330 ≤ i.val) (hhi : i.val < 340) (x y z w : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    QuantitativeArithmeticIntegerSevenLaurentRows.eval x y z w 0 0 0 v (QuantitativeArithmeticSmallLevelTwentySevenFourthFlatInteger.inputs i.val)=
      normalizer x y z w i.val*normalizedRow (selected i) (1) QuantitativeArithmeticSmallLevelTwentySevenFourthAnchorProfilePlus.profile (depth i) x y z w v := by
  rcases i with ⟨i,hi⟩
  change 330 ≤ i at hlo
  change i < 340 at hhi
  interval_cases i
  · rw [binding_input_lookup330,binding_source_lookup330,binding_depth_lookup330]
    simpa only [normalizer,binding_normalizer_lookup330,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input330 x y z w v hx hy hz hw
  · rw [binding_input_lookup331,binding_source_lookup331,binding_depth_lookup331]
    simpa only [normalizer,binding_normalizer_lookup331,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input331 x y z w v hx hy hz hw
  · rw [binding_input_lookup332,binding_source_lookup332,binding_depth_lookup332]
    simpa only [normalizer,binding_normalizer_lookup332,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input332 x y z w v hx hy hz hw
  · rw [binding_input_lookup333,binding_source_lookup333,binding_depth_lookup333]
    simpa only [normalizer,binding_normalizer_lookup333,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input333 x y z w v hx hy hz hw
  · rw [binding_input_lookup334,binding_source_lookup334,binding_depth_lookup334]
    simpa only [normalizer,binding_normalizer_lookup334,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input334 x y z w v hx hy hz hw
  · rw [binding_input_lookup335,binding_source_lookup335,binding_depth_lookup335]
    simpa only [normalizer,binding_normalizer_lookup335,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input335 x y z w v hx hy hz hw
  · rw [binding_input_lookup336,binding_source_lookup336,binding_depth_lookup336]
    simpa only [normalizer,binding_normalizer_lookup336,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input336 x y z w v hx hy hz hw
  · rw [binding_input_lookup337,binding_source_lookup337,binding_depth_lookup337]
    simpa only [normalizer,binding_normalizer_lookup337,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input337 x y z w v hx hy hz hw
  · rw [binding_input_lookup338,binding_source_lookup338,binding_depth_lookup338]
    simpa only [normalizer,binding_normalizer_lookup338,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input338 x y z w v hx hy hz hw
  · rw [binding_input_lookup339,binding_source_lookup339,binding_depth_lookup339]
    simpa only [normalizer,binding_normalizer_lookup339,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero,Rat.cast_neg] using normalized_plus_input339 x y z w v hx hy hz hw
#print axioms input_binding_block33

end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily.Plus
end
end
