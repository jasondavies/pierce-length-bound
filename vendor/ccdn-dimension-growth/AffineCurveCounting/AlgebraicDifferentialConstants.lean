module

public import Mathlib.FieldTheory.Differential.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Lifts

/-! Constants in algebraic extensions of differential fields. This is a
prerequisite for the differential irreducibility criterion, not that criterion. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Differential
open scoped Differential

/-- Coefficientwise differentiation strictly lowers the degree of a monic
polynomial, since its leading coefficient differentiates to zero. -/
lemma differential_mapCoeffs_degree_lt {K : Type*} [Field K] [Differential K]
    {p : K[X]} (hp : p.Monic) : (Differential.mapCoeffs p).degree < p.degree := by
  rw [degree_eq_natDegree hp.ne_zero, degree_lt_iff_coeff_zero]
  intro n hn
  rw [Differential.coeff_mapCoeffs]
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h, hp.coeff_natDegree]
    exact Derivation.map_one_eq_zero _
  · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]

/-- The minimal polynomial of an algebraic differential constant has constant
coefficients in the differential sense. -/
theorem minpoly_mapCoeffs_eq_zero {K L : Type*} [Field K] [Field L]
    [Differential K] [Differential L] [Algebra K L] [DifferentialAlgebra K L]
    {x : L} (hx : IsIntegral K x) (hder : x′ = 0) :
    Differential.mapCoeffs (minpoly K x) = 0 := by
  have hzero : aeval x (Differential.mapCoeffs (minpoly K x)) = 0 := by
    have h := Differential.deriv_aeval_eq x (minpoly K x)
    simpa only [minpoly.aeval, map_zero, hder, mul_zero, add_zero] using h.symm
  have hdiv := minpoly.dvd K x hzero
  by_contra hn
  have hle := degree_le_of_dvd hdiv hn
  exact (not_le_of_gt (differential_mapCoeffs_degree_lt (minpoly.monic hx))) hle

/-- Constants algebraic over a differential field descend to any algebraically
closed base field containing all constants of that differential field. -/
theorem algebraic_differential_constant_mem_base
    {F K L : Type*} [Field F] [Field K] [Field L] [IsAlgClosed F]
    [Differential K] [Differential L] [Algebra F K] [Algebra K L] [Algebra F L]
    [IsScalarTower F K L] [DifferentialAlgebra K L]
    [Differential.ContainConstants F K]
    {x : L} (hx : IsIntegral K x) (hder : x′ = 0) :
    x ∈ (algebraMap F L).range := by
  have hcoeff : ∀ n, (minpoly K x).coeff n ∈ Set.range (algebraMap F K) := by
    intro n
    apply mem_range_of_deriv_eq_zero F
    have h := congrArg (fun q : K[X] => q.coeff n) (minpoly_mapCoeffs_eq_zero hx hder)
    simpa only [Differential.coeff_mapCoeffs, coeff_zero] using h
  obtain ⟨q, hq⟩ := (mem_lifts (f := algebraMap F K) (minpoly K x)).mp
    ((lifts_iff_coeff_lifts _).mpr hcoeff)
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, Polynomial.map_zero] at hq
    exact (minpoly.ne_zero hx) hq.symm
  have hroot : (q.map (algebraMap F L)).IsRoot x := by
    change eval x (q.map (algebraMap F L)) = 0
    rw [eval_map]
    change aeval x q = 0
    rw [aeval_eq_aeval_map (IsScalarTower.algebraMap_eq F K L).symm, hq]
    exact minpoly.aeval K x
  exact (IsAlgClosed.splits q).mem_range_of_isRoot hq0 hroot

/-- The constant-field property is preserved by an algebraic differential
extension over an algebraically closed constant base. -/
theorem containConstants_of_algebraic
    {F K L : Type*} [Field F] [Field K] [Field L] [IsAlgClosed F]
    [Differential K] [Differential L] [Algebra F K] [Algebra K L] [Algebra F L]
    [IsScalarTower F K L] [DifferentialAlgebra K L]
    [Differential.ContainConstants F K] [Algebra.IsAlgebraic K L] :
    Differential.ContainConstants F L := by
  constructor
  intro x hx
  exact algebraic_differential_constant_mem_base (IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic (R := K) x)) hx

end
end AffineCurveCounting
