/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Defs
public import PierceLengthBound.Block
public import PierceLengthBound.Fiber
public import PierceLengthBound.Window
public import PierceLengthBound.Main
public import PierceLengthBound.SixStep
public import PierceLengthBound.ShortSum
public import PierceLengthBound.Geometric
public import PierceLengthBound.Conditional
public import PierceLengthBound.Hooley
public import PierceLengthBound.Rises
public import PierceLengthBound.RisesMain
public import PierceLengthBound.Hankel
public import PierceLengthBound.Hadamard
public import PierceLengthBound.Functional
public import PierceLengthBound.Gram
public import PierceLengthBound.TwoState
public import PierceLengthBound.PatternBound
public import PierceLengthBound.PatternCount
public import PierceLengthBound.OrbitPattern
public import PierceLengthBound.TwentyThreeMain
public import PierceLengthBound.NormCount
public import PierceLengthBound.SliceCount
public import PierceLengthBound.ElevenCount
public import PierceLengthBound.ElevenMain
public import PierceLengthBound.MinorCount
public import PierceLengthBound.MinorHeight
public import PierceLengthBound.EightMain
public import PierceLengthBound.DefiniteNorm
public import PierceLengthBound.Reduce3
public import PierceLengthBound.TernComp
public import PierceLengthBound.ShortVec
public import PierceLengthBound.LatticeCount
public import PierceLengthBound.CubeRoot
public import PierceLengthBound.FortyFiveMain
public import PierceLengthBound.FixedDividend
public import PierceLengthBound.FixedDividendLines
public import PierceLengthBound.FixedDividendWeights
public import PierceLengthBound.FixedDividendCoordinates
public import PierceLengthBound.FixedDividendContainedLines
public import PierceLengthBound.FixedDividendComplexLines
public import PierceLengthBound.FixedDividendCubicGeometry
public import PierceLengthBound.FixedDividendTotalDegree
public import PierceLengthBound.FixedDividendWindow
public import PierceLengthBound.FixedDividendCoprimality
public import PierceLengthBound.FixedDividendCurveEquations
public import PierceLengthBound.FixedDividendCount
public import PierceLengthBound.FixedDividendSelection
public import PierceLengthBound.FixedDividendComponents
public import PierceLengthBound.FixedDividendFilteredIntersection
public import PierceLengthBound.FixedDividendMonomialDimension
public import PierceLengthBound.FixedDividendGlobalReduction
public import PierceLengthBound.FixedDividendCountAssembly
public import PierceLengthBound.FixedDividendComponentCount
public import PierceLengthBound.FixedDividendHilbertLinearity
public import PierceLengthBound.ConicArithmetic
public import PierceLengthBound.ConicIntegerValues
public import PierceLengthBound.ConicReconstruction
public import PierceLengthBound.ConicRawDeterminant
public import PierceLengthBound.FixedDividendComponentLineExclusion
public import PierceLengthBound.ConicParabola
public import PierceLengthBound.FixedDividendHyperplaneDegree
public import PierceLengthBound.FixedDividendRationalOrbit
public import PierceLengthBound.ExceptionalSlack
public import PierceLengthBound.ConicPlaneHeight
public import PierceLengthBound.FixedDividendLatticeCurveCover
public import PierceLengthBound.ConicParameterHeight
public import PierceLengthBound.ConicFactorHeight
public import PierceLengthBound.ConicCofactors
public import PierceLengthBound.FixedDividendParityCover
public import PierceLengthBound.IntegralLiftMoments
public import PierceLengthBound.OrdinaryPatternCount
public import PierceLengthBound.IntegralLiftParabola
public import PierceLengthBound.IntegralLiftCofactors
public import PierceLengthBound.FixedDividendConicParabolicModel
public import PierceLengthBound.IntegralLiftCoordinateSystem
public import PierceLengthBound.FixedDividendOrbitConicParameter
public import PierceLengthBound.FixedDividendConicPolynomialIdentities
public import PierceLengthBound.IntegralLiftOrbitConicProperness
public import PierceLengthBound.JointLiftCurvatureHeight
public import PierceLengthBound.JointLiftOptimization
public import PierceLengthBound.IntegralLiftConicSlack
public import PierceLengthBound.JointLiftResolventCut
public import PierceLengthBound.OrbitConicGapCount
public import PierceLengthBound.JointLiftInfinityOrder
public import PierceLengthBound.ChartRawDeterminantOrders
public import PierceLengthBound.JointLiftChartOrders
public import PierceLengthBound.JointLiftNormalizedOrders
public import PierceLengthBound.NormalizationInfinityDegree
public import PierceLengthBound.BranchZeroDegree
public import PierceLengthBound.JointLiftPoleDegree
public import PierceLengthBound.JointLiftFiniteZero
public import PierceLengthBound.JointLiftCurvatureDegree
public import PierceLengthBound.JointLiftGraphLowerDegree
public import PierceLengthBound.PoweredJointGraphLowerDegree
public import PierceLengthBound.PoweredJointPointCount
public import PierceLengthBound.JointLiftMain
public import PierceLengthBound.LatticeExterior
public import PierceLengthBound.LatticeCurvature
public import PierceLengthBound.LinearJointGraph
public import PierceLengthBound.LatticeJointPointCount
public import PierceLengthBound.LatticeJointPatternCount
public import PierceLengthBound.RealPowerBounds
public import PierceLengthBound.LatticeJointWeights
public import PierceLengthBound.LatticeJointLocalEstimate
public import PierceLengthBound.LatticeJointWindow
public import PierceLengthBound.LatticeJointBound
public import PierceLengthBound.LatticeJointOptimization
public import PierceLengthBound.LatticeJointMain
public import PierceLengthBound.PolarProjectionAlgebra
public import PierceLengthBound.PolarProjectionOrbit
public import PierceLengthBound.PolarProjectionBasePoint
public import PierceLengthBound.PolarProjectionNewton
public import PierceLengthBound.PolarProjectionCertificate
public import PierceLengthBound.BranchSieveCertificate
public import PierceLengthBound.HypersurfacePatternCountWeights
public import PierceLengthBound.HypersurfacePatternCountLattice
public import PierceLengthBound.HypersurfacePatternCountCoordinates
public import PierceLengthBound.HypersurfacePatternCountGrid
public import PierceLengthBound.HypersurfacePatternCountFiber
public import PierceLengthBound.PolarProjectionExponent
public import PierceLengthBound.PolarProjectionOptimization
public import PierceLengthBound.PolarProjectionWindow
public import PierceLengthBound.PolarProjectionLocalEstimate
public import PierceLengthBound.PolarProjectionBound
public import PierceLengthBound.HypersurfacePatternCount
public import PierceLengthBound.PolarProjectionLinearSystem
public import PierceLengthBound.PolarProjectionCenteredQuadric
public import PierceLengthBound.BranchSieveSpecialization
public import PierceLengthBound.BranchSieveElimination
public import PierceLengthBound.BranchSieveSextic
public import PierceLengthBound.BranchSieveQuadratic
public import PierceLengthBound.BranchSieveReconstruction
public import PierceLengthBound.PolarProjectionBaseDegree
public import PierceLengthBound.PolarProjectionRankFiveDegree
public import PierceLengthBound.PolarProjectionDegreeReduction
public import PierceLengthBound.PolarProjectionRetainedBase
public import PierceLengthBound.BranchSieveBarycentric
public import PierceLengthBound.BranchSieveUniformRootBound
public import PierceLengthBound.BranchSieveBivariateFactorHeight
public import PierceLengthBound.BranchSieveCoefficientResolvent
public import PierceLengthBound.BranchSieveIntegerSpecialization
public import PierceLengthBound.PolarProjectionGeometryGoodPattern
public import PierceLengthBound.BranchSieveMonicHilbert
public import PierceLengthBound.BranchSieveMultivariateKronecker
public import PierceLengthBound.BranchSievePatternCountSlow
public import PierceLengthBound.PolarProjectionMain

/-!
# Hankel determinants and the length of finite Pierce expansions

Root module of the development. For `0 < b < a`, `P a b` is the number of positive terms of
`b₀ = b`, `bᵢ₊₁ = a mod bᵢ`. The principal results, each uniform in `0 < b < a`:

* `P_le_polar_optimal`, `P_le_4317_14677` (`PolarProjectionMain`): `P ≪ a^{β* + ε}` with
  `β* = (41301 − 3√82849)/137480` (Theorem 1.1), and the rational instance `4317/14677`.
* `P_le_joint_optimal`, `P_le_2201_7480`, `P_le_128_435` (`JointLiftMain`): the
  joint-invariant bound `a^{α* + ε}`, `α* = (1310 − √655)/4365` (Theorem 1.2), and the
  powers `m = 50, n = 51` and `m = n = 1`.
* `P_le_lattice_optimal`, `P_le_153_520` (`LatticeJointMain`): the exterior lattice bound
  `a^{γ* + ε}`, `γ* = 471/1559 − 6√105/7795` (Theorem 1.3), and `153/520`.
* `P_le_45_152`, `P_le_8_27`, `P_le_11_37`, `P_le_23_77` (`FortyFiveMain`, `EightMain`,
  `ElevenMain`, `TwentyThreeMain`): the pattern bounds.
* `P_le` (`Main`): `P ≪ a^{3/10 + ε}` (Theorem 1.4).
* `P_le_loglog` (`Hooley`): `P ≪ a^{3/10} √(log log 3a)`, assuming the theorems of
  Nair–Tenenbaum and de la Bretèche–Tenenbaum as explicit hypotheses.
* `P_le_rises` (`RisesMain`): `P ≪ a^{1/4} √(R + 1)`, where `R` counts the rises of the
  quotient increments (Theorem 1.5).
* `hankelInv_pos_int` (`Hankel`): the Hankel determinants `I_r(i)` are positive integers
  (Theorem 6.2).
-/
