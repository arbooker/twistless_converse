module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FinCases
public import QuantitativeArithmeticComplexHornerBoundsTheoryV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor6XRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def pCoefficient : ℕ→ℚ := fun j => match j with
  | 0 => (43200/541)
  | 1 => (-113160/541)
  | 2 => (59254/541)
  | 3 => (22673/541)
  | 4 => (-16365/541)
  | 5 => (437/541)
  | 6 => (1/1)
  | _ => 0
def centerQ : Fin 6→ℚ×ℚ := ![((-1545485682372482533503724905387/250000000000000000000000000000),(0/1)),((-1093382482817998415264993649489/500000000000000000000000000000),(0/1)),((145902600899140870546794035277/250000000000000000000000000000),(0/1)),((234728617099808584547159729863/200000000000000000000000000000),(0/1)),((2901845402460631629164005972629/1000000000000000000000000000000),(-450695075834288889051801021753/1000000000000000000000000000000)),((2901845402460631629164005972629/1000000000000000000000000000000),(56336884479286111131475127719/125000000000000000000000000000))]
def radiusQ : ℚ := (1/100000000000000000000)
def pRoot : ℂ[X] := hornerPolynomial (fun j => (pCoefficient j:ℂ)) 7 0

theorem pRoot_monic : pRoot.Monic := by
  norm_num [pRoot,hornerPolynomial,pCoefficient]
  monicity!

theorem pRoot_degree : pRoot.degree=(6:WithBot ℕ) := by
  norm_num [pRoot,hornerPolynomial,pCoefficient]
  compute_degree!

#print axioms pRoot_monic
#print axioms pRoot_degree

end SmallLevelTwentySixFactor6XRoot
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace SmallLevelTwentySixFactor7XRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def pCoefficient : ℕ→ℚ := fun j => match j with
  | 0 => (-1440/1)
  | 1 => (1464/1)
  | 2 => (204/1)
  | 3 => (-529/1)
  | 4 => (164/1)
  | 5 => (0/1)
  | 6 => (-8/1)
  | 7 => (1/1)
  | _ => 0
def centerQ : Fin 7→ℚ×ℚ := ![((-1156110034927169520060729203021/250000000000000000000000000000),(0/1)),((-408227793742152704266138694911/250000000000000000000000000000),(0/1)),((1177300437805623126007236873719/1000000000000000000000000000000),(0/1)),((1635205850351752570210972214893/500000000000000000000000000000),(0/1)),((2446032643999310592497629824881/500000000000000000000000000000),(0/1)),((614696736021192430735378829807/250000000000000000000000000000),(-252441883455479173625258796313/125000000000000000000000000000)),((614696736021192430735378829807/250000000000000000000000000000),(2019535067643833389002070370503/1000000000000000000000000000000))]
def radiusQ : ℚ := (1/100000000000000000000)
def pRoot : ℂ[X] := hornerPolynomial (fun j => (pCoefficient j:ℂ)) 8 0

theorem pRoot_monic : pRoot.Monic := by
  norm_num [pRoot,hornerPolynomial,pCoefficient]
  monicity!

theorem pRoot_degree : pRoot.degree=(7:WithBot ℕ) := by
  norm_num [pRoot,hornerPolynomial,pCoefficient]
  compute_degree!
  norm_num [Polynomial.coeff_C]

#print axioms pRoot_monic
#print axioms pRoot_degree

end SmallLevelTwentySixFactor7XRoot
end
