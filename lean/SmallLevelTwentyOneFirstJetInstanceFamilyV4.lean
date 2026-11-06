module
public import SmallLevelTwentyOneFirstJetBundleFamilyV4
public import SmallLevelTwentyOneFirstJetCertificateV1
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneFirstJetInstance0
open Complex SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneFirstJetBundle0

theorem coeff429_analytic (m : ℕ) (a s : ℂ) (i : Fin 10) :
    AnalyticAt ℂ (fun z => coeff429 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff429] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff429_analytic

theorem coeff435_analytic (m : ℕ) (a s : ℂ) (i : Fin 11) :
    AnalyticAt ℂ (fun z => coeff435 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff435] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff435_analytic

def certificate : FirstJetCertificate (-1) (-1) (-1) where
  size0 := 10
  size1 := 11
  rows0 := rows429
  rows1 := rows435
  coeff0 := coeff429
  coeff1 := coeff435
  syzygy0 := syzygy429_model
  syzygy1 := syzygy435_model
  analytic0 := coeff429_analytic
  analytic1 := coeff435_analytic
  conditions := conditions

#print axioms certificate
end SmallLevelTwentyOneFirstJetInstance0
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneFirstJetInstance1
open Complex SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneFirstJetBundle1

theorem coeff429_analytic (m : ℕ) (a s : ℂ) (i : Fin 10) :
    AnalyticAt ℂ (fun z => coeff429 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff429] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff429_analytic

theorem coeff435_analytic (m : ℕ) (a s : ℂ) (i : Fin 11) :
    AnalyticAt ℂ (fun z => coeff435 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff435] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff435_analytic

def certificate : FirstJetCertificate (-1) (-1) (1) where
  size0 := 10
  size1 := 11
  rows0 := rows429
  rows1 := rows435
  coeff0 := coeff429
  coeff1 := coeff435
  syzygy0 := syzygy429_model
  syzygy1 := syzygy435_model
  analytic0 := coeff429_analytic
  analytic1 := coeff435_analytic
  conditions := conditions

#print axioms certificate
end SmallLevelTwentyOneFirstJetInstance1
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneFirstJetInstance2
open Complex SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneFirstJetBundle2

theorem coeff429_analytic (m : ℕ) (a s : ℂ) (i : Fin 10) :
    AnalyticAt ℂ (fun z => coeff429 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff429] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff429_analytic

theorem coeff435_analytic (m : ℕ) (a s : ℂ) (i : Fin 11) :
    AnalyticAt ℂ (fun z => coeff435 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff435] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff435_analytic

def certificate : FirstJetCertificate (-1) (1) (-1) where
  size0 := 10
  size1 := 11
  rows0 := rows429
  rows1 := rows435
  coeff0 := coeff429
  coeff1 := coeff435
  syzygy0 := syzygy429_model
  syzygy1 := syzygy435_model
  analytic0 := coeff429_analytic
  analytic1 := coeff435_analytic
  conditions := conditions

#print axioms certificate
end SmallLevelTwentyOneFirstJetInstance2
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneFirstJetInstance3
open Complex SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneFirstJetBundle3

theorem coeff429_analytic (m : ℕ) (a s : ℂ) (i : Fin 10) :
    AnalyticAt ℂ (fun z => coeff429 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff429] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff429_analytic

theorem coeff435_analytic (m : ℕ) (a s : ℂ) (i : Fin 11) :
    AnalyticAt ℂ (fun z => coeff435 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff435] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff435_analytic

def certificate : FirstJetCertificate (-1) (1) (1) where
  size0 := 10
  size1 := 11
  rows0 := rows429
  rows1 := rows435
  coeff0 := coeff429
  coeff1 := coeff435
  syzygy0 := syzygy429_model
  syzygy1 := syzygy435_model
  analytic0 := coeff429_analytic
  analytic1 := coeff435_analytic
  conditions := conditions

#print axioms certificate
end SmallLevelTwentyOneFirstJetInstance3
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneFirstJetInstance4
open Complex SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneFirstJetBundle4

theorem coeff429_analytic (m : ℕ) (a s : ℂ) (i : Fin 10) :
    AnalyticAt ℂ (fun z => coeff429 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff429] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff429_analytic

theorem coeff435_analytic (m : ℕ) (a s : ℂ) (i : Fin 11) :
    AnalyticAt ℂ (fun z => coeff435 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff435] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff435_analytic

def certificate : FirstJetCertificate (1) (-1) (-1) where
  size0 := 10
  size1 := 11
  rows0 := rows429
  rows1 := rows435
  coeff0 := coeff429
  coeff1 := coeff435
  syzygy0 := syzygy429_model
  syzygy1 := syzygy435_model
  analytic0 := coeff429_analytic
  analytic1 := coeff435_analytic
  conditions := conditions

#print axioms certificate
end SmallLevelTwentyOneFirstJetInstance4
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneFirstJetInstance5
open Complex SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneFirstJetBundle5

theorem coeff429_analytic (m : ℕ) (a s : ℂ) (i : Fin 10) :
    AnalyticAt ℂ (fun z => coeff429 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff429] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff429_analytic

theorem coeff435_analytic (m : ℕ) (a s : ℂ) (i : Fin 11) :
    AnalyticAt ℂ (fun z => coeff435 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff435] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff435_analytic

def certificate : FirstJetCertificate (1) (-1) (1) where
  size0 := 10
  size1 := 11
  rows0 := rows429
  rows1 := rows435
  coeff0 := coeff429
  coeff1 := coeff435
  syzygy0 := syzygy429_model
  syzygy1 := syzygy435_model
  analytic0 := coeff429_analytic
  analytic1 := coeff435_analytic
  conditions := conditions

#print axioms certificate
end SmallLevelTwentyOneFirstJetInstance5
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneFirstJetInstance6
open Complex SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneFirstJetBundle6

theorem coeff429_analytic (m : ℕ) (a s : ℂ) (i : Fin 10) :
    AnalyticAt ℂ (fun z => coeff429 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff429] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff429_analytic

theorem coeff435_analytic (m : ℕ) (a s : ℂ) (i : Fin 11) :
    AnalyticAt ℂ (fun z => coeff435 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff435] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff435_analytic

def certificate : FirstJetCertificate (1) (1) (-1) where
  size0 := 10
  size1 := 11
  rows0 := rows429
  rows1 := rows435
  coeff0 := coeff429
  coeff1 := coeff435
  syzygy0 := syzygy429_model
  syzygy1 := syzygy435_model
  analytic0 := coeff429_analytic
  analytic1 := coeff435_analytic
  conditions := conditions

#print axioms certificate
end SmallLevelTwentyOneFirstJetInstance6
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneFirstJetInstance7
open Complex SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneFirstJetBundle7

theorem coeff429_analytic (m : ℕ) (a s : ℂ) (i : Fin 10) :
    AnalyticAt ℂ (fun z => coeff429 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff429] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff429_analytic

theorem coeff435_analytic (m : ℕ) (a s : ℂ) (i : Fin 11) :
    AnalyticAt ℂ (fun z => coeff435 (primeParameter 2 m z) (primeParameter 3 m z)
      (primeParameter 7 m z) a i) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  fin_cases i <;> dsimp [coeff435] <;>
    fun_prop (disch := simp [mul_ne_zero,pow_ne_zero,hn2,hn3,hn7])

#print axioms coeff435_analytic

def certificate : FirstJetCertificate (1) (1) (1) where
  size0 := 10
  size1 := 11
  rows0 := rows429
  rows1 := rows435
  coeff0 := coeff429
  coeff1 := coeff435
  syzygy0 := syzygy429_model
  syzygy1 := syzygy435_model
  analytic0 := coeff429_analytic
  analytic1 := coeff435_analytic
  conditions := conditions

#print axioms certificate
end SmallLevelTwentyOneFirstJetInstance7
end
