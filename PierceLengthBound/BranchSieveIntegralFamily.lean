/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveNormPolynomial
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! Clearing the branch matrix denominators uniformly in the dividend.
The result is a monic degree-twelve family, with polynomial dependence on the
four vertex parameters and on the dividend. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Matrix Polynomial
open scoped nonZeroDivisors RatFunc
attribute [local instance] Polynomial.algebra
local instance branchIntegralLocationField : Field BranchLocationField :=
  inferInstance
local instance branchIntegralLocationExtension : Field BranchLocationExtension :=
  inferInstance
local instance branchIntegralRatField : Field (RatFunc BranchLocationField) :=
  inferInstance
local instance branchIntegralRatExtension : Field (RatFunc BranchLocationExtension) :=
  inferInstance

/-- Three normalized vertex parameters and the absolute-scale variable. -/
abbrev BranchVertexParameters := Polynomial BranchLocationParameters

local instance : IsScalarTower BranchVertexParameters
    (Polynomial BranchLocationField) (RatFunc BranchLocationField) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The existing iterated rational function field is the fraction field of the
four-variable vertex polynomial ring. -/
instance branchVertexParameters_fractionRing :
    IsFractionRing BranchVertexParameters (RatFunc BranchLocationField) := by
  let : IsLocalization ((nonZeroDivisors BranchLocationParameters).map Polynomial.C)
      (Polynomial BranchLocationField) := Polynomial.isLocalization _ _
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    ((nonZeroDivisors BranchLocationParameters).map Polynomial.C)
    (nonZeroDivisors (Polynomial BranchLocationField)) (RatFunc BranchLocationField)
    (fun _ hx => hx.mem_nonZeroDivisors)
  convert h using 1
  ext x
  simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  change x ≠ 0 ↔ x.map (algebraMap BranchLocationParameters BranchLocationField) ≠ 0
  simpa only [Polynomial.map_zero] using
    ((Polynomial.map_injective (algebraMap BranchLocationParameters BranchLocationField)
      (IsFractionRing.injective _ _)).ne_iff (x := x) (y := 0)).symm

/-- The actual branch matrix, before specializing its dividend variable. -/
def branchDividendMatrix (c : ℕ) :
    Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (Polynomial (RatFunc BranchLocationField)) :=
  branchLabelMatrix (branchGenericLocationMatrix.map Polynomial.C)
    (branchGenericDeltaMatrix.map Polynomial.C) (c : Polynomial (RatFunc BranchLocationField))
    (Polynomial.X * Polynomial.C (RatFunc.X⁻¹))

/-- Dividend specialization recovers the actual generic branch matrix. -/
lemma branchDividendMatrix_specialize (a : ℚ) (c : ℕ) :
    (branchDividendMatrix c).map
      (Polynomial.evalRingHom (RatFunc.C (algebraMap ℚ BranchLocationField a))) =
      branchLabelMatrix branchGenericLocationMatrix branchGenericDeltaMatrix c
        (RatFunc.C (algebraMap ℚ BranchLocationField a) / RatFunc.X) := by
  rw [branchDividendMatrix, branchLabelMatrix_map]
  congr 1
  · ext i j
    simp
  · ext i j
    simp
  · simp
  · change (Polynomial.X * Polynomial.C (RatFunc.X⁻¹)).eval
      (RatFunc.C (algebraMap ℚ BranchLocationField a)) = _
    rw [eval_mul, eval_X, eval_C, div_eq_mul_inv]

/-- A denominator-cleared matrix model. The denominator depends on the chosen
bounded slope, but is independent of the dividend. -/
structure BranchLabelIntegralModel (c : ℕ) where
  denominator : BranchVertexParameters
  denominator_ne_zero : denominator ≠ 0
  matrix : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (Polynomial BranchVertexParameters)
  matrix_map : matrix.map (Polynomial.mapRingHom
      (algebraMap BranchVertexParameters (RatFunc BranchLocationField))) =
    Polynomial.C (algebraMap BranchVertexParameters (RatFunc BranchLocationField) denominator) •
      branchDividendMatrix c

private def branchVertexDenominators : Submonoid (Polynomial BranchVertexParameters) :=
  (nonZeroDivisors BranchVertexParameters).map Polynomial.C

/-- All matrix denominators can be cleared by one vertex polynomial, without
introducing a dividend-dependent exceptional divisor. -/
theorem branchLabelIntegralModel_nonempty (c : ℕ) : Nonempty (BranchLabelIntegralModel c) := by
  let : IsLocalization branchVertexDenominators
      (Polynomial (RatFunc BranchLocationField)) := by
    exact Polynomial.isLocalization (nonZeroDivisors BranchVertexParameters)
      (RatFunc BranchLocationField)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (R := Polynomial BranchVertexParameters) (S := Polynomial (RatFunc BranchLocationField))
    branchVertexDenominators
    (fun ij : (Fin 6 ⊕ Fin 6) × (Fin 6 ⊕ Fin 6) => branchDividendMatrix c ij.1 ij.2)
  obtain ⟨q, hq, hqb⟩ := b.property
  choose Q hQ using hb
  refine ⟨⟨q, nonZeroDivisors.ne_zero hq, fun i j => Q (i, j), ?_⟩⟩
  funext i j
  have he := hQ (i, j)
  simp only [Algebra.smul_def, Polynomial.algebraMap_def] at he
  rw [← hqb] at he
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_C] at he
  exact he

/-- A fixed cleared model for each slope. -/
def branchLabelIntegralModel (c : ℕ) : BranchLabelIntegralModel c :=
  Classical.choice (branchLabelIntegralModel_nonempty c)

/-- The monic polynomial family over the four vertex parameters and dividend. -/
def branchIntegralLabelFamily (c : ℕ) : Polynomial (Polynomial BranchVertexParameters) :=
  (branchLabelIntegralModel c).matrix.charpoly

/-- Fixing the rational dividend leaves an honest polynomial in the four vertex
parameters, with a monic degree-twelve label equation. -/
def branchIntegralLabelPolynomial (a : ℚ) (c : ℕ) : Polynomial BranchVertexParameters :=
  (branchIntegralLabelFamily c).map
    (Polynomial.evalRingHom (Polynomial.C (MvPolynomial.C a)))

lemma branchIntegralLabelFamily_monic (c : ℕ) : (branchIntegralLabelFamily c).Monic :=
  Matrix.charpoly_monic _

lemma branchIntegralLabelFamily_natDegree (c : ℕ) :
    (branchIntegralLabelFamily c).natDegree = 12 := by
  simp [branchIntegralLabelFamily, Matrix.charpoly_natDegree_eq_dim]

lemma branchIntegralLabelPolynomial_monic (a : ℚ) (c : ℕ) :
    (branchIntegralLabelPolynomial a c).Monic :=
  (branchIntegralLabelFamily_monic c).map _

lemma branchIntegralLabelPolynomial_natDegree (a : ℚ) (c : ℕ) :
    (branchIntegralLabelPolynomial a c).natDegree = 12 := by
  rw [branchIntegralLabelPolynomial, (branchIntegralLabelFamily_monic c).natDegree_map,
    branchIntegralLabelFamily_natDegree]

/-- The vertex-ring embedding sends a constant rational dividend to its usual
image in the generic rational function field. -/
lemma branchVertexParameters_map_rat (a : ℚ) :
    algebraMap BranchVertexParameters (RatFunc BranchLocationField)
      (Polynomial.C (MvPolynomial.C a)) = RatFunc.C (algebraMap ℚ BranchLocationField a) := by
  rw [IsScalarTower.algebraMap_apply BranchVertexParameters
    (Polynomial BranchLocationField) (RatFunc BranchLocationField),
    Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, Polynomial.map_C, RatFunc.algebraMap_C]
  congr 1
  exact (IsScalarTower.algebraMap_apply ℚ BranchLocationParameters BranchLocationField a).symm

/-- The integral matrix model specializes to a fixed nonzero scalar multiple of
the original branch matrix. -/
lemma branchIntegralLabelPolynomial_map (a : ℚ) (c : ℕ) :
    (branchIntegralLabelPolynomial a c).map
      (algebraMap BranchVertexParameters (RatFunc BranchLocationField)) =
    ((algebraMap BranchVertexParameters (RatFunc BranchLocationField)
      (branchLabelIntegralModel c).denominator) •
      branchLabelMatrix branchGenericLocationMatrix branchGenericDeltaMatrix c
        (RatFunc.C (algebraMap ℚ BranchLocationField a) / RatFunc.X)).charpoly := by
  let φ := algebraMap BranchVertexParameters (RatFunc BranchLocationField)
  let r : BranchVertexParameters := Polynomial.C (MvPolynomial.C a)
  have he := congrArg (fun M => M.map (Polynomial.evalRingHom (φ r)))
    (branchLabelIntegralModel c).matrix_map
  have hc : ((branchLabelIntegralModel c).matrix.map (Polynomial.evalRingHom r)).map φ =
      (φ (branchLabelIntegralModel c).denominator) •
        (branchDividendMatrix c).map (Polynomial.evalRingHom (φ r)) := by
    convert he using 1
    · ext i j
      change φ (((branchLabelIntegralModel c).matrix i j).eval r) =
        (((branchLabelIntegralModel c).matrix i j).map φ).eval (φ r)
      exact (Polynomial.eval_map_apply _ _).symm
    · ext i j
      simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, φ]
  rw [show φ r = RatFunc.C (algebraMap ℚ BranchLocationField a) from
    branchVertexParameters_map_rat a, branchDividendMatrix_specialize] at hc
  have hh := congrArg Matrix.charpoly hc
  rw [Matrix.charpoly_map] at hh
  have heval := Matrix.charpoly_map (branchLabelIntegralModel c).matrix
    (Polynomial.evalRingHom r)
  rw [heval] at hh
  exact hh

/-- Scaling a matrix scales each root of its characteristic polynomial, over any
field receiving the coefficient ring. -/
lemma branch_matrix_scaled_root {R K ι : Type*} [CommRing R] [Field K]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (φ : R →+* K) (q : R) (z : K)
    (h : Polynomial.eval₂ φ z M.charpoly = 0) :
    Polynomial.eval₂ φ (φ q * z) (q • M).charpoly = 0 := by
  have he : ((q • M).map φ) = φ q • M.map φ := by
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Polynomial.eval_map, ← Matrix.charpoly_map, he, Matrix.eval_charpoly]
  have hs : Matrix.scalar ι (φ q * z) - φ q • M.map φ =
      φ q • (Matrix.scalar ι z - M.map φ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar, Matrix.sub_apply, Matrix.smul_apply,
      hij, smul_eq_mul, mul_sub]
  rw [hs, Matrix.det_smul]
  have h' : (Matrix.scalar ι z - M.map φ).det = 0 := by
    rwa [← Polynomial.eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly] at h
  rw [h', mul_zero]

/-- The cleared family annihilates the scaled actual generic branch label. -/
theorem branchIntegralLabelPolynomial_generic_root (a : ℚ) (ha : a ≠ 0) (c : ℕ) :
    let R := RatFunc BranchLocationField
    let E := BranchGenericSignAlgebra a
    let q := algebraMap BranchVertexParameters R (branchLabelIntegralModel c).denominator
    Polynomial.aeval (q • (branchGenericLocationInSignAlgebra a +
      (c : E) * branchGenericSignRoot a))
      ((branchIntegralLabelPolynomial a c).map (algebraMap BranchVertexParameters R)) = 0 := by
  let : Fact (Irreducible (branchSignPolynomial
      (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)) :=
    ⟨branchSignPolynomial_irreducible
      (by simpa only [map_zero] using (algebraMap ℚ BranchLocationExtension).injective.ne ha)
      branchGenericDelta_ne_zero⟩
  let : Field (BranchGenericSignAlgebra a) := inferInstance
  dsimp only
  rw [branchIntegralLabelPolynomial_map]
  rw [Polynomial.aeval_def, Algebra.smul_def]
  exact branch_matrix_scaled_root _ (algebraMap (RatFunc BranchLocationField)
    (BranchGenericSignAlgebra a)) _ _ (branchGenericLabelPolynomial_root a ha c)

/-- For every nonzero dividend, one of the bounded slopes yields an irreducible
monic degree-twelve polynomial in the generic vertex field, with a fixed cleared
coefficient family independent of that dividend. -/
theorem branchIntegral_exists_irreducible_label_polynomial (a : ℚ) (ha : a ≠ 0) :
    ∃ c : ℕ, c ≤ 144 ∧ Irreducible ((branchIntegralLabelPolynomial a c).map
      (algebraMap BranchVertexParameters (RatFunc BranchLocationField))) ∧
      (branchIntegralLabelPolynomial a c).natDegree = 12 := by
  let : Fact (Irreducible (branchSignPolynomial
      (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)) :=
    ⟨branchSignPolynomial_irreducible
      (by simpa only [map_zero] using (algebraMap ℚ BranchLocationExtension).injective.ne ha)
      branchGenericDelta_ne_zero⟩
  let : Field (BranchGenericSignAlgebra a) := inferInstance
  obtain ⟨c, hc, _, hdeg⟩ := branchGeneric_exists_degree_twelve_polynomial a ha
  have hd := (branchGenericSignExtension_field_degree a ha).2
  let : FiniteDimensional (RatFunc BranchLocationField) (BranchGenericSignAlgebra a) :=
    Module.finite_of_finrank_pos (by rw [hd]; norm_num)
  let q := algebraMap BranchVertexParameters (RatFunc BranchLocationField)
    (branchLabelIntegralModel c).denominator
  have hq : q ≠ 0 := by
    simpa only [q, map_zero] using
      (IsFractionRing.injective BranchVertexParameters (RatFunc BranchLocationField)).ne
        (branchLabelIntegralModel c).denominator_ne_zero
  let z := branchGenericLocationInSignAlgebra a +
    (c : BranchGenericSignAlgebra a) * branchGenericSignRoot a
  have hz := IsIntegral.of_finite (RatFunc BranchLocationField) z
  let : Module.IsTorsionFree (RatFunc BranchLocationField) (BranchGenericSignAlgebra a) :=
    Module.IsTorsionFree.of_smul_eq_zero
      (R := RatFunc BranchLocationField) (M := BranchGenericSignAlgebra a) (by
      intro r x hx
      rw [Algebra.smul_def] at hx
      rcases mul_eq_zero.mp hx with hr | hx
      · exact Or.inl ((algebraMap (RatFunc BranchLocationField)
          (BranchGenericSignAlgebra a)).injective (by simpa only [map_zero] using hr))
      · exact Or.inr hx)
  have hs : (minpoly (RatFunc BranchLocationField) (q • z)).natDegree = 12 := by
    rw [IsIntegrallyClosed.minpoly_smul hq hz, Polynomial.natDegree_scaleRoots]
    exact hdeg
  have hm := (branchIntegralLabelPolynomial_monic a c).map
    (algebraMap BranchVertexParameters (RatFunc BranchLocationField))
  have he := Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hz.smul q)) hm
    (minpoly.dvd (RatFunc BranchLocationField) _
      (branchIntegralLabelPolynomial_generic_root a ha c))
    (by rw [(branchIntegralLabelPolynomial_monic a c).natDegree_map,
      branchIntegralLabelPolynomial_natDegree, hs])
  exact ⟨c, hc, he ▸ minpoly.irreducible (hz.smul q),
    branchIntegralLabelPolynomial_natDegree a c⟩

end
end PierceLengthBound.FixedDividend
