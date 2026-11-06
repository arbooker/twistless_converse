module

public import SmallLevelTwentyOneWordCertificateV1

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
@[expose] public section
namespace SmallLevelTwentyOneKnownWords
open Matrix

def augmentedWord000 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.generator 0))
theorem augmentedWord000_matrix : integerRaw augmentedWord000=!![0,-1;21,42] := by decide
theorem augmentedWord000_count : frickeCount augmentedWord000=1 := by decide
#print axioms augmentedWord000_matrix

def augmentedWord001 : Word := (.mul (.mul .one (.generator 3)) (.generator 0))
theorem augmentedWord001_matrix : integerRaw augmentedWord001=!![0,-1;21,21] := by decide
theorem augmentedWord001_count : frickeCount augmentedWord001=1 := by decide
#print axioms augmentedWord001_matrix

def augmentedWord002 : Word := (.mul .one (.generator 3))
theorem augmentedWord002_matrix : integerRaw augmentedWord002=!![0,-1;21,0] := by decide
theorem augmentedWord002_count : frickeCount augmentedWord002=1 := by decide
#print axioms augmentedWord002_matrix

def augmentedWord003 : Word := (.mul (.mul .one (.generator 1)) (.generator 3))
theorem augmentedWord003_matrix : integerRaw augmentedWord003=!![0,-1;21,-21] := by decide
theorem augmentedWord003_count : frickeCount augmentedWord003=1 := by decide
#print axioms augmentedWord003_matrix

def augmentedWord004 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 1)) (.generator 3))
theorem augmentedWord004_matrix : integerRaw augmentedWord004=!![0,-1;21,-42] := by decide
theorem augmentedWord004_count : frickeCount augmentedWord004=1 := by decide
#print axioms augmentedWord004_matrix

def augmentedWord005 : Word := (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 0)))
theorem augmentedWord005_matrix : integerRaw augmentedWord005=!![1,-1;-21,22] := by decide
theorem augmentedWord005_count : frickeCount augmentedWord005=0 := by decide
#print axioms augmentedWord005_matrix

def augmentedWord006 : Word := (.mul (.mul .one (.generator 1)) (.inv (.generator 0)))
theorem augmentedWord006_matrix : integerRaw augmentedWord006=!![1,-1;21,-20] := by decide
theorem augmentedWord006_count : frickeCount augmentedWord006=0 := by decide
#print axioms augmentedWord006_matrix

def augmentedWord007 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 1)) (.inv (.generator 0)))
theorem augmentedWord007_matrix : integerRaw augmentedWord007=!![1,-1;42,-41] := by decide
theorem augmentedWord007_count : frickeCount augmentedWord007=0 := by decide
#print axioms augmentedWord007_matrix

def augmentedWord008 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 1))) (.inv (.generator 1)))
theorem augmentedWord008_matrix : integerRaw augmentedWord008=!![1,0;-63,1] := by decide
theorem augmentedWord008_count : frickeCount augmentedWord008=0 := by decide
#print axioms augmentedWord008_matrix

def augmentedWord009 : Word := (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 1)))
theorem augmentedWord009_matrix : integerRaw augmentedWord009=!![1,0;-42,1] := by decide
theorem augmentedWord009_count : frickeCount augmentedWord009=0 := by decide
#print axioms augmentedWord009_matrix

def augmentedWord010 : Word := (.mul .one (.inv (.generator 1)))
theorem augmentedWord010_matrix : integerRaw augmentedWord010=!![1,0;-21,1] := by decide
theorem augmentedWord010_count : frickeCount augmentedWord010=0 := by decide
#print axioms augmentedWord010_matrix

def augmentedWord011 : Word := (.mul .one (.generator 1))
theorem augmentedWord011_matrix : integerRaw augmentedWord011=!![1,0;21,1] := by decide
theorem augmentedWord011_count : frickeCount augmentedWord011=0 := by decide
#print axioms augmentedWord011_matrix

def augmentedWord012 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 1))) (.generator 2))
theorem augmentedWord012_matrix : integerRaw augmentedWord012=!![2,-1;-105,53] := by decide
theorem augmentedWord012_count : frickeCount augmentedWord012=0 := by decide
#print axioms augmentedWord012_matrix

def augmentedWord013 : Word := (.mul (.mul .one (.inv (.generator 1))) (.generator 2))
theorem augmentedWord013_matrix : integerRaw augmentedWord013=!![2,-1;-63,32] := by decide
theorem augmentedWord013_count : frickeCount augmentedWord013=0 := by decide
#print axioms augmentedWord013_matrix

def augmentedWord014 : Word := (.mul .one (.generator 2))
theorem augmentedWord014_matrix : integerRaw augmentedWord014=!![2,-1;-21,11] := by decide
theorem augmentedWord014_count : frickeCount augmentedWord014=0 := by decide
#print axioms augmentedWord014_matrix

def augmentedWord015 : Word := (.mul (.mul .one (.generator 1)) (.generator 2))
theorem augmentedWord015_matrix : integerRaw augmentedWord015=!![2,-1;21,-10] := by decide
theorem augmentedWord015_count : frickeCount augmentedWord015=0 := by decide
#print axioms augmentedWord015_matrix

def augmentedWord016 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 1)) (.generator 2))
theorem augmentedWord016_matrix : integerRaw augmentedWord016=!![2,-1;63,-31] := by decide
theorem augmentedWord016_count : frickeCount augmentedWord016=0 := by decide
#print axioms augmentedWord016_matrix

def augmentedWord017 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2))) (.inv (.generator 0)))
theorem augmentedWord017_matrix : integerRaw augmentedWord017=!![-10,9;21,-19] := by decide
theorem augmentedWord017_count : frickeCount augmentedWord017=0 := by decide
#print axioms augmentedWord017_matrix

def augmentedWord018 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 2))) (.inv (.generator 1)))
theorem augmentedWord018_matrix : integerRaw augmentedWord018=!![-10,1;189,-19] := by decide
theorem augmentedWord018_count : frickeCount augmentedWord018=0 := by decide
#print axioms augmentedWord018_matrix

def augmentedWord019 : Word := (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1)))
theorem augmentedWord019_matrix : integerRaw augmentedWord019=!![-10,1;-21,2] := by decide
theorem augmentedWord019_count : frickeCount augmentedWord019=0 := by decide
#print axioms augmentedWord019_matrix

def augmentedWord020 : Word := (.mul (.mul (.mul .one (.generator 1)) (.inv (.generator 2))) (.inv (.generator 1)))
theorem augmentedWord020_matrix : integerRaw augmentedWord020=!![-10,1;-231,23] := by decide
theorem augmentedWord020_count : frickeCount augmentedWord020=0 := by decide
#print axioms augmentedWord020_matrix

def augmentedWord021 : Word := (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2)))
theorem augmentedWord021_matrix : integerRaw augmentedWord021=!![-10,-1;21,2] := by decide
theorem augmentedWord021_count : frickeCount augmentedWord021=0 := by decide
#print axioms augmentedWord021_matrix

def augmentedWord022 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 2))) (.inv (.generator 0)))
theorem augmentedWord022_matrix : integerRaw augmentedWord022=!![11,-10;-210,191] := by decide
theorem augmentedWord022_count : frickeCount augmentedWord022=0 := by decide
#print axioms augmentedWord022_matrix

def augmentedWord023 : Word := (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 0)))
theorem augmentedWord023_matrix : integerRaw augmentedWord023=!![11,-10;21,-19] := by decide
theorem augmentedWord023_count : frickeCount augmentedWord023=0 := by decide
#print axioms augmentedWord023_matrix

def augmentedWord024 : Word := (.mul (.mul (.mul .one (.generator 1)) (.inv (.generator 2))) (.inv (.generator 0)))
theorem augmentedWord024_matrix : integerRaw augmentedWord024=!![11,-10;252,-229] := by decide
theorem augmentedWord024_count : frickeCount augmentedWord024=0 := by decide
#print axioms augmentedWord024_matrix

def augmentedWord025 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2))) (.inv (.generator 1)))
theorem augmentedWord025_matrix : integerRaw augmentedWord025=!![11,-1;-21,2] := by decide
theorem augmentedWord025_count : frickeCount augmentedWord025=0 := by decide
#print axioms augmentedWord025_matrix

def augmentedWord026 : Word := (.mul .one (.inv (.generator 2)))
theorem augmentedWord026_matrix : integerRaw augmentedWord026=!![11,1;21,2] := by decide
theorem augmentedWord026_count : frickeCount augmentedWord026=0 := by decide
#print axioms augmentedWord026_matrix

def augmentedWord027 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 0)) (.generator 2))
theorem augmentedWord027_matrix : integerRaw augmentedWord027=!![-17,9;168,-89] := by decide
theorem augmentedWord027_count : frickeCount augmentedWord027=0 := by decide
#print axioms augmentedWord027_matrix

def augmentedWord028 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 1)) (.generator 2))
theorem augmentedWord028_matrix : integerRaw augmentedWord028=!![-17,8;189,-89] := by decide
theorem augmentedWord028_count : frickeCount augmentedWord028=0 := by decide
#print axioms augmentedWord028_matrix

def augmentedWord029 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 1)) (.inv (.generator 0)))
theorem augmentedWord029_matrix : integerRaw augmentedWord029=!![-19,18;210,-199] := by decide
theorem augmentedWord029_count : frickeCount augmentedWord029=0 := by decide
#print axioms augmentedWord029_matrix

def augmentedWord030 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.generator 0)) (.generator 2))
theorem augmentedWord030_matrix : integerRaw augmentedWord030=!![-19,10;378,-199] := by decide
theorem augmentedWord030_count : frickeCount augmentedWord030=0 := by decide
#print axioms augmentedWord030_matrix

def augmentedWord031 : Word := (.mul (.mul .one (.generator 0)) (.generator 2))
theorem augmentedWord031_matrix : integerRaw augmentedWord031=!![-19,10;-21,11] := by decide
theorem augmentedWord031_count : frickeCount augmentedWord031=0 := by decide
#print axioms augmentedWord031_matrix

def augmentedWord032 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 0)) (.generator 2))
theorem augmentedWord032_matrix : integerRaw augmentedWord032=!![-19,10;-420,221] := by decide
theorem augmentedWord032_count : frickeCount augmentedWord032=0 := by decide
#print axioms augmentedWord032_matrix

def augmentedWord033 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 1)) (.generator 2))
theorem augmentedWord033_matrix : integerRaw augmentedWord033=!![-19,9;21,-10] := by decide
theorem augmentedWord033_count : frickeCount augmentedWord033=0 := by decide
#print axioms augmentedWord033_matrix

def augmentedWord034 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 0)) (.inv (.generator 1)))
theorem augmentedWord034_matrix : integerRaw augmentedWord034=!![-19,1;189,-10] := by decide
theorem augmentedWord034_count : frickeCount augmentedWord034=0 := by decide
#print axioms augmentedWord034_matrix

def augmentedWord035 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 1))) (.inv (.generator 0)))
theorem augmentedWord035_matrix : integerRaw augmentedWord035=!![-20,21;-21,22] := by decide
theorem augmentedWord035_count : frickeCount augmentedWord035=0 := by decide
#print axioms augmentedWord035_matrix

def augmentedWord036 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 1)) (.inv (.generator 0)))
theorem augmentedWord036_matrix : integerRaw augmentedWord036=!![-20,19;21,-20] := by decide
theorem augmentedWord036_count : frickeCount augmentedWord036=0 := by decide
#print axioms augmentedWord036_matrix

def augmentedWord037 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.generator 0)) (.inv (.generator 1)))
theorem augmentedWord037_matrix : integerRaw augmentedWord037=!![-20,1;399,-20] := by decide
theorem augmentedWord037_count : frickeCount augmentedWord037=0 := by decide
#print axioms augmentedWord037_matrix

def augmentedWord038 : Word := (.mul (.mul .one (.generator 0)) (.inv (.generator 1)))
theorem augmentedWord038_matrix : integerRaw augmentedWord038=!![-20,1;-21,1] := by decide
theorem augmentedWord038_count : frickeCount augmentedWord038=0 := by decide
#print axioms augmentedWord038_matrix

def augmentedWord039 : Word := (.mul (.mul .one (.inv (.generator 0))) (.generator 1))
theorem augmentedWord039_matrix : integerRaw augmentedWord039=!![-20,-1;21,1] := by decide
theorem augmentedWord039_count : frickeCount augmentedWord039=0 := by decide
#print axioms augmentedWord039_matrix

def augmentedWord040 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 1)) (.generator 3))
theorem augmentedWord040_matrix : integerRaw augmentedWord040=!![21,-22;21,-21] := by decide
theorem augmentedWord040_count : frickeCount augmentedWord040=1 := by decide
#print axioms augmentedWord040_matrix

def augmentedWord041 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 1)) (.inv (.generator 0)))
theorem augmentedWord041_matrix : integerRaw augmentedWord041=!![-21,20;21,-21] := by decide
theorem augmentedWord041_count : frickeCount augmentedWord041=1 := by decide
#print axioms augmentedWord041_matrix

def augmentedWord042 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 1)) (.generator 3))
theorem augmentedWord042_matrix : integerRaw augmentedWord042=!![-21,19;231,-210] := by decide
theorem augmentedWord042_count : frickeCount augmentedWord042=1 := by decide
#print axioms augmentedWord042_matrix

def augmentedWord043 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.generator 2))
theorem augmentedWord043_matrix : integerRaw augmentedWord043=!![21,-11;-399,210] := by decide
theorem augmentedWord043_count : frickeCount augmentedWord043=1 := by decide
#print axioms augmentedWord043_matrix

def augmentedWord044 : Word := (.mul (.mul .one (.generator 3)) (.generator 2))
theorem augmentedWord044_matrix : integerRaw augmentedWord044=!![21,-11;42,-21] := by decide
theorem augmentedWord044_count : frickeCount augmentedWord044=1 := by decide
#print axioms augmentedWord044_matrix

def augmentedWord045 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 3)) (.generator 2))
theorem augmentedWord045_matrix : integerRaw augmentedWord045=!![21,-11;483,-252] := by decide
theorem augmentedWord045_count : frickeCount augmentedWord045=1 := by decide
#print axioms augmentedWord045_matrix

def augmentedWord046 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 1)) (.generator 2))
theorem augmentedWord046_matrix : integerRaw augmentedWord046=!![-21,10;42,-21] := by decide
theorem augmentedWord046_count : frickeCount augmentedWord046=1 := by decide
#print axioms augmentedWord046_matrix

def augmentedWord047 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 0)) (.generator 3))
theorem augmentedWord047_matrix : integerRaw augmentedWord047=!![21,-2;-210,21] := by decide
theorem augmentedWord047_count : frickeCount augmentedWord047=1 := by decide
#print axioms augmentedWord047_matrix

def augmentedWord048 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.inv (.generator 1)))
theorem augmentedWord048_matrix : integerRaw augmentedWord048=!![21,-1;-420,21] := by decide
theorem augmentedWord048_count : frickeCount augmentedWord048=1 := by decide
#print axioms augmentedWord048_matrix

def augmentedWord049 : Word := (.mul (.mul .one (.generator 0)) (.generator 3))
theorem augmentedWord049_matrix : integerRaw augmentedWord049=!![21,-1;21,0] := by decide
theorem augmentedWord049_count : frickeCount augmentedWord049=1 := by decide
#print axioms augmentedWord049_matrix

def augmentedWord050 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 0)) (.generator 3))
theorem augmentedWord050_matrix : integerRaw augmentedWord050=!![21,-1;462,-21] := by decide
theorem augmentedWord050_count : frickeCount augmentedWord050=1 := by decide
#print axioms augmentedWord050_matrix

def augmentedWord051 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.generator 1))
theorem augmentedWord051_matrix : integerRaw augmentedWord051=!![-21,-1;462,21] := by decide
theorem augmentedWord051_count : frickeCount augmentedWord051=1 := by decide
#print axioms augmentedWord051_matrix

def augmentedWord052 : Word := (.mul (.mul .one (.generator 3)) (.generator 1))
theorem augmentedWord052_matrix : integerRaw augmentedWord052=!![-21,-1;21,0] := by decide
theorem augmentedWord052_count : frickeCount augmentedWord052=1 := by decide
#print axioms augmentedWord052_matrix

def augmentedWord053 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 3)) (.generator 1))
theorem augmentedWord053_matrix : integerRaw augmentedWord053=!![-21,-1;-420,-21] := by decide
theorem augmentedWord053_count : frickeCount augmentedWord053=1 := by decide
#print axioms augmentedWord053_matrix

def augmentedWord054 : Word := (.mul (.mul .one (.generator 2)) (.generator 3))
theorem augmentedWord054_matrix : integerRaw augmentedWord054=!![-21,-2;231,21] := by decide
theorem augmentedWord054_count : frickeCount augmentedWord054=1 := by decide
#print axioms augmentedWord054_matrix

def augmentedWord055 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 2)) (.generator 3))
theorem augmentedWord055_matrix : integerRaw augmentedWord055=!![-21,-2;-210,-21] := by decide
theorem augmentedWord055_count : frickeCount augmentedWord055=1 := by decide
#print axioms augmentedWord055_matrix

def augmentedWord056 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 2)) (.generator 0))
theorem augmentedWord056_matrix : integerRaw augmentedWord056=!![21,10;42,21] := by decide
theorem augmentedWord056_count : frickeCount augmentedWord056=1 := by decide
#print axioms augmentedWord056_matrix

def augmentedWord057 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 3)) (.generator 0))
theorem augmentedWord057_matrix : integerRaw augmentedWord057=!![21,20;21,21] := by decide
theorem augmentedWord057_count : frickeCount augmentedWord057=1 := by decide
#print axioms augmentedWord057_matrix

def augmentedWord058 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 1)) (.generator 0))
theorem augmentedWord058_matrix : integerRaw augmentedWord058=!![-21,-22;21,21] := by decide
theorem augmentedWord058_count : frickeCount augmentedWord058=1 := by decide
#print axioms augmentedWord058_matrix

def augmentedWord059 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1))) (.inv (.generator 0)))
theorem augmentedWord059_matrix : integerRaw augmentedWord059=!![22,-23;-21,22] := by decide
theorem augmentedWord059_count : frickeCount augmentedWord059=0 := by decide
#print axioms augmentedWord059_matrix

def augmentedWord060 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 1)) (.inv (.generator 0)))
theorem augmentedWord060_matrix : integerRaw augmentedWord060=!![22,-21;21,-20] := by decide
theorem augmentedWord060_count : frickeCount augmentedWord060=0 := by decide
#print axioms augmentedWord060_matrix

def augmentedWord061 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 0))) (.inv (.generator 1)))
theorem augmentedWord061_matrix : integerRaw augmentedWord061=!![22,-1;-483,22] := by decide
theorem augmentedWord061_count : frickeCount augmentedWord061=0 := by decide
#print axioms augmentedWord061_matrix

def augmentedWord062 : Word := (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1)))
theorem augmentedWord062_matrix : integerRaw augmentedWord062=!![22,-1;-21,1] := by decide
theorem augmentedWord062_count : frickeCount augmentedWord062=0 := by decide
#print axioms augmentedWord062_matrix

def augmentedWord063 : Word := (.mul (.mul .one (.generator 0)) (.generator 1))
theorem augmentedWord063_matrix : integerRaw augmentedWord063=!![22,1;21,1] := by decide
theorem augmentedWord063_count : frickeCount augmentedWord063=0 := by decide
#print axioms augmentedWord063_matrix

def augmentedWord064 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 0))) (.generator 2))
theorem augmentedWord064_matrix : integerRaw augmentedWord064=!![23,-12;-504,263] := by decide
theorem augmentedWord064_count : frickeCount augmentedWord064=0 := by decide
#print axioms augmentedWord064_matrix

def augmentedWord065 : Word := (.mul (.mul .one (.inv (.generator 0))) (.generator 2))
theorem augmentedWord065_matrix : integerRaw augmentedWord065=!![23,-12;-21,11] := by decide
theorem augmentedWord065_count : frickeCount augmentedWord065=0 := by decide
#print axioms augmentedWord065_matrix

def augmentedWord066 : Word := (.mul (.mul (.mul .one (.generator 1)) (.inv (.generator 0))) (.generator 2))
theorem augmentedWord066_matrix : integerRaw augmentedWord066=!![23,-12;462,-241] := by decide
theorem augmentedWord066_count : frickeCount augmentedWord066=0 := by decide
#print axioms augmentedWord066_matrix

def augmentedWord067 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 1)) (.generator 2))
theorem augmentedWord067_matrix : integerRaw augmentedWord067=!![23,-11;21,-10] := by decide
theorem augmentedWord067_count : frickeCount augmentedWord067=0 := by decide
#print axioms augmentedWord067_matrix

def augmentedWord068 : Word := (.mul (.mul .one (.generator 2)) (.inv (.generator 1)))
theorem augmentedWord068_matrix : integerRaw augmentedWord068=!![23,-1;-252,11] := by decide
theorem augmentedWord068_count : frickeCount augmentedWord068=0 := by decide
#print axioms augmentedWord068_matrix

def augmentedWord069 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 2)) (.inv (.generator 1)))
theorem augmentedWord069_matrix : integerRaw augmentedWord069=!![23,-1;231,-10] := by decide
theorem augmentedWord069_count : frickeCount augmentedWord069=0 := by decide
#print axioms augmentedWord069_matrix

def augmentedWord070 : Word := (.mul (.mul .one (.generator 2)) (.generator 2))
theorem augmentedWord070_matrix : integerRaw augmentedWord070=!![25,-13;-273,142] := by decide
theorem augmentedWord070_count : frickeCount augmentedWord070=0 := by decide
#print axioms augmentedWord070_matrix

def augmentedWord071 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 2)) (.generator 2))
theorem augmentedWord071_matrix : integerRaw augmentedWord071=!![25,-13;252,-131] := by decide
theorem augmentedWord071_count : frickeCount augmentedWord071=0 := by decide
#print axioms augmentedWord071_matrix

def augmentedWord072 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 2))) (.inv (.generator 1)))
theorem augmentedWord072_matrix : integerRaw augmentedWord072=!![-31,3;-21,2] := by decide
theorem augmentedWord072_count : frickeCount augmentedWord072=0 := by decide
#print axioms augmentedWord072_matrix

def augmentedWord073 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1))) (.inv (.generator 1)))
theorem augmentedWord073_matrix : integerRaw augmentedWord073=!![-31,1;-63,2] := by decide
theorem augmentedWord073_count : frickeCount augmentedWord073=0 := by decide
#print axioms augmentedWord073_matrix

def augmentedWord074 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 2))) (.generator 1))
theorem augmentedWord074_matrix : integerRaw augmentedWord074=!![-31,-1;63,2] := by decide
theorem augmentedWord074_count : frickeCount augmentedWord074=0 := by decide
#print axioms augmentedWord074_matrix

def augmentedWord075 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.inv (.generator 2)))
theorem augmentedWord075_matrix : integerRaw augmentedWord075=!![-31,-3;21,2] := by decide
theorem augmentedWord075_count : frickeCount augmentedWord075=0 := by decide
#print axioms augmentedWord075_matrix

def augmentedWord076 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 1)) (.inv (.generator 0)))
theorem augmentedWord076_matrix : integerRaw augmentedWord076=!![32,-31;63,-61] := by decide
theorem augmentedWord076_count : frickeCount augmentedWord076=0 := by decide
#print axioms augmentedWord076_matrix

def augmentedWord077 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 2))) (.inv (.generator 0)))
theorem augmentedWord077_matrix : integerRaw augmentedWord077=!![32,-29;21,-19] := by decide
theorem augmentedWord077_count : frickeCount augmentedWord077=0 := by decide
#print axioms augmentedWord077_matrix

def augmentedWord078 : Word := (.mul (.mul .one (.inv (.generator 2))) (.generator 1))
theorem augmentedWord078_matrix : integerRaw augmentedWord078=!![32,1;63,2] := by decide
theorem augmentedWord078_count : frickeCount augmentedWord078=0 := by decide
#print axioms augmentedWord078_matrix

def augmentedWord079 : Word := (.mul (.mul .one (.generator 0)) (.inv (.generator 2)))
theorem augmentedWord079_matrix : integerRaw augmentedWord079=!![32,3;21,2] := by decide
theorem augmentedWord079_count : frickeCount augmentedWord079=0 := by decide
#print axioms augmentedWord079_matrix

def augmentedWord080 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.generator 2))
theorem augmentedWord080_matrix : integerRaw augmentedWord080=!![-40,21;-21,11] := by decide
theorem augmentedWord080_count : frickeCount augmentedWord080=0 := by decide
#print axioms augmentedWord080_matrix

def augmentedWord081 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 1))) (.generator 2))
theorem augmentedWord081_matrix : integerRaw augmentedWord081=!![-41,21;-84,43] := by decide
theorem augmentedWord081_count : frickeCount augmentedWord081=0 := by decide
#print axioms augmentedWord081_matrix

def augmentedWord082 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.inv (.generator 1)))
theorem augmentedWord082_matrix : integerRaw augmentedWord082=!![-41,2;-21,1] := by decide
theorem augmentedWord082_count : frickeCount augmentedWord082=0 := by decide
#print axioms augmentedWord082_matrix

def augmentedWord083 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 1))) (.inv (.generator 1)))
theorem augmentedWord083_matrix : integerRaw augmentedWord083=!![-41,1;-42,1] := by decide
theorem augmentedWord083_count : frickeCount augmentedWord083=0 := by decide
#print axioms augmentedWord083_matrix

def augmentedWord084 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.generator 1))
theorem augmentedWord084_matrix : integerRaw augmentedWord084=!![-41,-2;21,1] := by decide
theorem augmentedWord084_count : frickeCount augmentedWord084=0 := by decide
#print axioms augmentedWord084_matrix

def augmentedWord085 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.generator 3))
theorem augmentedWord085_matrix : integerRaw augmentedWord085=!![42,-1;21,0] := by decide
theorem augmentedWord085_count : frickeCount augmentedWord085=1 := by decide
#print axioms augmentedWord085_matrix

def augmentedWord086 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 1)) (.generator 1))
theorem augmentedWord086_matrix : integerRaw augmentedWord086=!![-42,-1;21,0] := by decide
theorem augmentedWord086_count : frickeCount augmentedWord086=1 := by decide
#print axioms augmentedWord086_matrix

def augmentedWord087 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 1)) (.generator 2))
theorem augmentedWord087_matrix : integerRaw augmentedWord087=!![43,-21;84,-41] := by decide
theorem augmentedWord087_count : frickeCount augmentedWord087=0 := by decide
#print axioms augmentedWord087_matrix

def augmentedWord088 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.inv (.generator 1)))
theorem augmentedWord088_matrix : integerRaw augmentedWord088=!![43,-2;-21,1] := by decide
theorem augmentedWord088_count : frickeCount augmentedWord088=0 := by decide
#print axioms augmentedWord088_matrix

def augmentedWord089 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1))) (.inv (.generator 1)))
theorem augmentedWord089_matrix : integerRaw augmentedWord089=!![43,-1;-42,1] := by decide
theorem augmentedWord089_count : frickeCount augmentedWord089=0 := by decide
#print axioms augmentedWord089_matrix

def augmentedWord090 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.generator 1))
theorem augmentedWord090_matrix : integerRaw augmentedWord090=!![43,2;21,1] := by decide
theorem augmentedWord090_count : frickeCount augmentedWord090=0 := by decide
#print axioms augmentedWord090_matrix

def augmentedWord091 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 0))) (.generator 2))
theorem augmentedWord091_matrix : integerRaw augmentedWord091=!![44,-23;-21,11] := by decide
theorem augmentedWord091_count : frickeCount augmentedWord091=0 := by decide
#print axioms augmentedWord091_matrix

def augmentedWord092 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 1))) (.inv (.generator 1)))
theorem augmentedWord092_matrix : integerRaw augmentedWord092=!![44,-1;-483,11] := by decide
theorem augmentedWord092_count : frickeCount augmentedWord092=0 := by decide
#print axioms augmentedWord092_matrix

def augmentedWord093 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 1)) (.generator 1))
theorem augmentedWord093_matrix : integerRaw augmentedWord093=!![53,1;105,2] := by decide
theorem augmentedWord093_count : frickeCount augmentedWord093=0 := by decide
#print axioms augmentedWord093_matrix

def augmentedWord094 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 0)) (.inv (.generator 2)))
theorem augmentedWord094_matrix : integerRaw augmentedWord094=!![53,5;21,2] := by decide
theorem augmentedWord094_count : frickeCount augmentedWord094=0 := by decide
#print axioms augmentedWord094_matrix

def augmentedWord095 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 1))) (.generator 2))
theorem augmentedWord095_matrix : integerRaw augmentedWord095=!![-61,31;-63,32] := by decide
theorem augmentedWord095_count : frickeCount augmentedWord095=0 := by decide
#print axioms augmentedWord095_matrix

def augmentedWord096 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 3)) (.generator 2))
theorem augmentedWord096_matrix : integerRaw augmentedWord096=!![63,-32;42,-21] := by decide
theorem augmentedWord096_count : frickeCount augmentedWord096=1 := by decide
#print axioms augmentedWord096_matrix

def augmentedWord097 : Word := (.mul (.mul (.mul .one (.generator 2)) (.generator 3)) (.generator 1))
theorem augmentedWord097_matrix : integerRaw augmentedWord097=!![-63,-2;672,21] := by decide
theorem augmentedWord097_count : frickeCount augmentedWord097=1 := by decide
#print axioms augmentedWord097_matrix

def augmentedWord098 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.inv (.generator 1))) (.generator 2))
theorem augmentedWord098_matrix : integerRaw augmentedWord098=!![65,-33;-63,32] := by decide
theorem augmentedWord098_count : frickeCount augmentedWord098=0 := by decide
#print axioms augmentedWord098_matrix

def augmentedWord099 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 0))) (.inv (.generator 1)))
theorem augmentedWord099_matrix : integerRaw augmentedWord099=!![65,-3;-693,32] := by decide
theorem augmentedWord099_count : frickeCount augmentedWord099=0 := by decide
#print axioms augmentedWord099_matrix

def augmentedWord100 : Word := (.mul (.mul (.mul .one (.generator 2)) (.inv (.generator 0))) (.generator 2))
theorem augmentedWord100_matrix : integerRaw augmentedWord100=!![67,-35;-714,373] := by decide
theorem augmentedWord100_count : frickeCount augmentedWord100=0 := by decide
#print axioms augmentedWord100_matrix

def augmentedWord101 : Word := (.mul (.mul (.mul .one (.generator 0)) (.inv (.generator 2))) (.generator 1))
theorem augmentedWord101_matrix : integerRaw augmentedWord101=!![95,3;63,2] := by decide
theorem augmentedWord101_count : frickeCount augmentedWord101=0 := by decide
#print axioms augmentedWord101_matrix

def augmentedWord102 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 2))) (.inv (.generator 1)))
theorem augmentedWord102_matrix : integerRaw augmentedWord102=!![-131,13;-252,25] := by decide
theorem augmentedWord102_count : frickeCount augmentedWord102=0 := by decide
#print axioms augmentedWord102_matrix

def augmentedWord103 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 2))) (.inv (.generator 0)))
theorem augmentedWord103_matrix : integerRaw augmentedWord103=!![142,-129;273,-248] := by decide
theorem augmentedWord103_count : frickeCount augmentedWord103=0 := by decide
#print axioms augmentedWord103_matrix

def augmentedWord104 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 2)) (.generator 1))
theorem augmentedWord104_matrix : integerRaw augmentedWord104=!![-210,-11;-399,-21] := by decide
theorem augmentedWord104_count : frickeCount augmentedWord104=1 := by decide
#print axioms augmentedWord104_matrix

def augmentedWord105 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 2)) (.generator 3))
theorem augmentedWord105_matrix : integerRaw augmentedWord105=!![210,19;231,21] := by decide
theorem augmentedWord105_count : frickeCount augmentedWord105=1 := by decide
#print axioms augmentedWord105_matrix

def augmentedWord106 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.inv (.generator 0))) (.inv (.generator 1)))
theorem augmentedWord106_matrix : integerRaw augmentedWord106=!![221,-10;420,-19] := by decide
theorem augmentedWord106_count : frickeCount augmentedWord106=0 := by decide
#print axioms augmentedWord106_matrix

def augmentedWord107 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 2)) (.inv (.generator 1)))
theorem augmentedWord107_matrix : integerRaw augmentedWord107=!![-229,10;-252,11] := by decide
theorem augmentedWord107_count : frickeCount augmentedWord107=0 := by decide
#print axioms augmentedWord107_matrix

def augmentedWord108 : Word := (.mul (.mul (.mul .one (.inv (.generator 2))) (.generator 0)) (.inv (.generator 1)))
theorem augmentedWord108_matrix : integerRaw augmentedWord108=!![-241,12;-462,23] := by decide
theorem augmentedWord108_count : frickeCount augmentedWord108=0 := by decide
#print axioms augmentedWord108_matrix

def augmentedWord109 : Word := (.mul (.mul (.mul .one (.generator 0)) (.generator 2)) (.generator 2))
theorem augmentedWord109_matrix : integerRaw augmentedWord109=!![-248,129;-273,142] := by decide
theorem augmentedWord109_count : frickeCount augmentedWord109=0 := by decide
#print axioms augmentedWord109_matrix

def augmentedWord110 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 2)) (.inv (.generator 1)))
theorem augmentedWord110_matrix : integerRaw augmentedWord110=!![252,-11;483,-21] := by decide
theorem augmentedWord110_count : frickeCount augmentedWord110=1 := by decide
#print axioms augmentedWord110_matrix

def augmentedWord111 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 1)) (.inv (.generator 2)))
theorem augmentedWord111_matrix : integerRaw augmentedWord111=!![-252,-23;231,21] := by decide
theorem augmentedWord111_count : frickeCount augmentedWord111=1 := by decide
#print axioms augmentedWord111_matrix

def augmentedWord112 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 2)) (.generator 2))
theorem augmentedWord112_matrix : integerRaw augmentedWord112=!![273,-142;525,-273] := by decide
theorem augmentedWord112_count : frickeCount augmentedWord112=1 := by decide
#print axioms augmentedWord112_matrix

def augmentedWord113 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 2)) (.inv (.generator 1)))
theorem augmentedWord113_matrix : integerRaw augmentedWord113=!![275,-12;-252,11] := by decide
theorem augmentedWord113_count : frickeCount augmentedWord113=0 := by decide
#print axioms augmentedWord113_matrix

def augmentedWord114 : Word := (.mul (.mul (.mul .one (.inv (.generator 0))) (.generator 2)) (.generator 2))
theorem augmentedWord114_matrix : integerRaw augmentedWord114=!![298,-155;-273,142] := by decide
theorem augmentedWord114_count : frickeCount augmentedWord114=0 := by decide
#print axioms augmentedWord114_matrix

end SmallLevelTwentyOneKnownWords
