/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveBarycentric
public import PierceLengthBound.BranchSievePrimitive
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Data.Matrix.Block

/-! A universal degree-twelve branch polynomial. The block matrix represents
multiplication by `t+cβ`, where `β²=αΔ`; it is defined over arbitrary coefficient
rings and commutes with specialization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Matrix Polynomial

/-- Multiplication by `t+cβ`, in a basis and the same basis multiplied by β.
The matrices act on evaluation vectors, so they are transposes of the usual
coordinate multiplication matrices. -/
def branchLabelMatrix {R ι : Type*} [CommRing R] [DecidableEq ι]
    (T D : Matrix ι ι R) (c α : R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks T (c • (1 : Matrix ι ι R)) ((c * α) • D) T

/-- The characteristic polynomial of the universal branch-label matrix. -/
def branchLabelPolynomial {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (T D : Matrix ι ι R) (c α : R) : Polynomial R :=
  (branchLabelMatrix T D c α).charpoly

lemma branchLabelPolynomial_monic {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (T D : Matrix ι ι R) (c α : R) : (branchLabelPolynomial T D c α).Monic :=
  Matrix.charpoly_monic _

lemma branchLabelPolynomial_natDegree {R ι : Type*} [CommRing R] [Nontrivial R]
    [Fintype ι] [DecidableEq ι] (T D : Matrix ι ι R) (c α : R) :
    (branchLabelPolynomial T D c α).natDegree = 2 * Fintype.card ι := by
  simp only [branchLabelPolynomial, Matrix.charpoly_natDegree_eq_dim, Fintype.card_sum]
  omega

lemma branchLabelMatrix_map {R S ι : Type*} [CommRing R] [CommRing S] [DecidableEq ι]
    (φ : R →+* S) (T D : Matrix ι ι R) (c α : R) :
    (branchLabelMatrix T D c α).map φ = branchLabelMatrix (T.map φ) (D.map φ) (φ c) (φ α) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [branchLabelMatrix, Matrix.map_apply, Matrix.fromBlocks, Matrix.one_apply,
      apply_ite φ, map_mul]

/-- The branch polynomial specializes coefficientwise, without changing its degree. -/
lemma branchLabelPolynomial_map {R S ι : Type*} [CommRing R] [CommRing S]
    [Fintype ι] [DecidableEq ι] (φ : R →+* S) (T D : Matrix ι ι R) (c α : R) :
    (branchLabelPolynomial T D c α).map φ =
      branchLabelPolynomial (T.map φ) (D.map φ) (φ c) (φ α) := by
  rw [branchLabelPolynomial, ← Matrix.charpoly_map, branchLabelMatrix_map]
  rfl

/-- The evaluation vector of a location and its sign is an actual eigenvector
of the universal block matrix. -/
lemma branchLabelMatrix_eigenvector {K ι : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] (T D : Matrix ι ι K) (c α t Δ β : K) (v : ι → K)
    (hT : T *ᵥ v = t • v) (hD : D *ᵥ v = Δ • v) (hβ : β ^ 2 = α * Δ) :
    branchLabelMatrix T D c α *ᵥ Sum.elim v (β • v) =
      (t + c * β) • Sum.elim v (β • v) := by
  rw [branchLabelMatrix, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_smul, hT, hD]
  funext j
  rcases j with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  · ring
  · linear_combination -c * v j * hβ

/-- An eigenvector with a nonzero coordinate forces vanishing of the characteristic polynomial. -/
lemma branch_charpoly_root_of_eigenvector {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (t : K) (v : ι → K)
    (hv : ∃ j, v j ≠ 0) (he : M *ᵥ v = t • v) : M.charpoly.eval t = 0 := by
  obtain ⟨j, hj⟩ := hv
  rw [Matrix.eval_charpoly]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (i := j)
  · rw [Matrix.sub_mulVec, he]
    ext k
    simp [Matrix.scalar, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr hj

/-- The universal branch polynomial vanishes at every location/sign pair
satisfying the specialized sextic algebra and quadratic sign relation. -/
theorem branchLabelPolynomial_eval_eq_zero {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (T D : Matrix ι ι K) (c α t Δ β : K) (v : ι → K)
    (hv : ∃ j, v j ≠ 0) (hT : T *ᵥ v = t • v) (hD : D *ᵥ v = Δ • v)
    (hβ : β ^ 2 = α * Δ) : (branchLabelPolynomial T D c α).eval (t + c * β) = 0 := by
  apply branch_charpoly_root_of_eigenvector _ _ (Sum.elim v (β • v))
  · obtain ⟨j, hj⟩ := hv
    exact ⟨Sum.inl j, hj⟩
  · exact branchLabelMatrix_eigenvector T D c α t Δ β v hT hD hβ

/-- Specialization/root compatibility for the degree-twelve family. -/
theorem branchLabelPolynomial_specialize_root {R K ι : Type*} [CommRing R] [Field K]
    [Fintype ι] [DecidableEq ι] (φ : R →+* K) (T D : Matrix ι ι R)
    (c α : R) (t Δ β : K) (v : ι → K) (hv : ∃ j, v j ≠ 0)
    (hT : T.map φ *ᵥ v = t • v) (hD : D.map φ *ᵥ v = Δ • v)
    (hβ : β ^ 2 = φ α * Δ) :
    (branchLabelPolynomial T D c α).eval₂ φ (t + φ c * β) = 0 := by
  rw [← Polynomial.eval_map, branchLabelPolynomial_map]
  exact branchLabelPolynomial_eval_eq_zero _ _ _ _ _ _ _ v hv hT hD hβ

/-- Six locations and their two signs always give a monic degree-twelve family. -/
theorem branchLabelPolynomial_degree_twelve {R : Type*} [CommRing R] [Nontrivial R]
    (T D : Matrix (Fin 6) (Fin 6) R) (c α : R) :
    (branchLabelPolynomial T D c α).Monic ∧ (branchLabelPolynomial T D c α).natDegree = 12 :=
  ⟨branchLabelPolynomial_monic T D c α, by simp [branchLabelPolynomial_natDegree]⟩

/-- Evaluating a basis turns transposed multiplication matrices into eigenvectors. -/
lemma branch_basis_evaluation_eigenvector {R L K ι : Type*}
    [CommRing R] [CommRing L] [Algebra R L] [CommRing K] [Algebra R K]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R L) (φ : L →ₐ[R] K) (x : L) :
    (Algebra.leftMulMatrix b x).transpose.map (algebraMap R K) *ᵥ
        (fun j => φ (b j)) = φ x • (fun j => φ (b j)) := by
  funext i
  change (∑ j, algebraMap R K (Algebra.leftMulMatrix b x j i) * φ (b j)) = φ x * φ (b i)
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
  simpa only [map_sum, map_smul, Algebra.smul_def, map_mul, φ.commutes] using
    congrArg φ (b.sum_repr (x * b i))

/-- The basis evaluation vector is nonzero for every unital algebra specialization. -/
lemma branch_basis_evaluation_nonzero {R L K ι : Type*}
    [CommRing R] [CommRing L] [Algebra R L] [CommRing K] [Algebra R K] [Nontrivial K]
    [Finite ι] (b : Module.Basis ι R L) (φ : L →ₐ[R] K) :
    ∃ j, φ (b j) ≠ 0 := by
  let := Fintype.ofFinite ι
  by_contra! h
  have hh := congrArg φ (b.sum_repr (1 : L))
  simp only [map_sum, map_smul, h, smul_zero, Finset.sum_const_zero, map_one] at hh
  exact zero_ne_one hh

/-- The matrix family is the actual norm polynomial of a location and quadratic
sign, with a root under every algebra specialization. -/
theorem branchLabelPolynomial_basis_root {R L K ι : Type*}
    [CommRing R] [CommRing L] [Algebra R L] [Field K] [Algebra R K]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R L) (φ : L →ₐ[R] K)
    (t Δ : L) (c α : R) (β : K) (hβ : β ^ 2 = algebraMap R K α * φ Δ) :
    Polynomial.aeval (φ t + algebraMap R K c * β)
      (branchLabelPolynomial (Algebra.leftMulMatrix b t).transpose
        (Algebra.leftMulMatrix b Δ).transpose c α) = 0 := by
  exact branchLabelPolynomial_specialize_root (algebraMap R K) _ _ c α (φ t) (φ Δ) β
    (fun j => φ (b j)) (branch_basis_evaluation_nonzero b φ)
    (branch_basis_evaluation_eigenvector b φ t) (branch_basis_evaluation_eigenvector b φ Δ) hβ

open scoped RatFunc
attribute [local instance] Polynomial.algebra

-- Fix the field structures before deriving their modules; the concrete quotient and
-- fraction types also carry direct ring instances with a different elaboration path.
local instance branchNormLocationField : Field BranchLocationField :=
  inferInstance
local instance branchNormLocationExtension : Field BranchLocationExtension :=
  inferInstance
local instance branchNormRatField : Field (RatFunc BranchLocationField) :=
  inferInstance
local instance branchNormRatExtension : Field (RatFunc BranchLocationExtension) :=
  inferInstance

instance branchLocationExtension_finiteDimensional :
    FiniteDimensional BranchLocationField BranchLocationExtension :=
  Module.finite_of_finrank_pos (by rw [branchLocationExtension_finrank]; norm_num)

lemma branchSignRoot_square {K : Type*} [Field K] (a Δ : K) :
    (AdjoinRoot.root (branchSignPolynomial a Δ)) ^ 2 =
      algebraMap (RatFunc K) (AdjoinRoot (branchSignPolynomial a Δ)) (branchSignSquare a Δ) := by
  have he : Polynomial.eval₂ (AdjoinRoot.of (branchSignPolynomial a Δ))
      (AdjoinRoot.root (branchSignPolynomial a Δ))
      (Polynomial.X ^ 2 - Polynomial.C (branchSignSquare a Δ)) = 0 :=
    AdjoinRoot.eval₂_root (branchSignPolynomial a Δ)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at he
  exact sub_eq_zero.mp he

lemma branch_ratFunc_scale_mul {F L : Type*} [Field F] [Field L]
    [Algebra ℚ F] [Algebra ℚ L] [Algebra F L] [IsScalarTower ℚ F L]
    (a : ℚ) (Δ : L) :
    algebraMap (RatFunc F) (RatFunc L)
      (RatFunc.C (algebraMap ℚ F a) / RatFunc.X) * RatFunc.C Δ =
      branchSignSquare (algebraMap ℚ L a) Δ := by
  rw [map_div₀, branch_ratFunc_algebraMap_C, branch_ratFunc_algebraMap_X,
    ← IsScalarTower.algebraMap_apply ℚ F L]
  simp only [branchSignSquare, map_mul]
  ring

/-- A fixed six-element basis of the generic location field after adjoining the
absolute-scale indeterminate. The basis does not depend on the dividend. -/
def branchGenericLocationRatBasis : Module.Basis (Fin 6)
    (RatFunc BranchLocationField) (RatFunc BranchLocationExtension) := by
  let : FiniteDimensional BranchLocationField BranchLocationExtension :=
    Module.finite_of_finrank_pos (by rw [branchLocationExtension_finrank]; norm_num)
  have hd : Module.finrank (RatFunc BranchLocationField) (RatFunc BranchLocationExtension) = 6 := by
    rw [RatFunc.finrank_ratFunc_ratFunc, branchLocationExtension_finrank]
  let : FiniteDimensional (RatFunc BranchLocationField) (RatFunc BranchLocationExtension) :=
    Module.finite_of_finrank_pos (by rw [hd]; norm_num)
  exact Module.finBasisOfFinrankEq _ _ hd

/-- Fixed transposed multiplication matrix of the first generic location. -/
def branchGenericLocationMatrix : Matrix (Fin 6) (Fin 6) (RatFunc BranchLocationField) :=
  (Algebra.leftMulMatrix branchGenericLocationRatBasis (RatFunc.C (AdjoinRoot.root
    (branchGenericLocationSextic.map
      (algebraMap BranchLocationParameters BranchLocationField))))).transpose

/-- Fixed transposed multiplication matrix of the location Vandermonde factor. -/
def branchGenericDeltaMatrix : Matrix (Fin 6) (Fin 6) (RatFunc BranchLocationField) :=
  (Algebra.leftMulMatrix branchGenericLocationRatBasis (RatFunc.C branchGenericDelta)).transpose

/-- An explicit characteristic-polynomial family for the actual generic branch
labels. Only the scalar `a/A` depends on the dividend. -/
def branchGenericLabelPolynomial (a : ℚ) (c : ℕ) : Polynomial (RatFunc BranchLocationField) :=
  branchLabelPolynomial branchGenericLocationMatrix branchGenericDeltaMatrix c
    (RatFunc.C (algebraMap ℚ BranchLocationField a) / RatFunc.X)

lemma branchGenericLabelPolynomial_monic (a : ℚ) (c : ℕ) :
    (branchGenericLabelPolynomial a c).Monic := branchLabelPolynomial_monic _ _ _ _

lemma branchGenericLabelPolynomial_natDegree (a : ℚ) (c : ℕ) :
    (branchGenericLabelPolynomial a c).natDegree = 12 :=
  (branchLabelPolynomial_degree_twelve _ _ _ _).2

/-- The concrete characteristic polynomial annihilates the actual generic
location/sign combination, so it can replace the abstract minimal polynomial. -/
theorem branchGenericLabelPolynomial_root (a : ℚ) (ha : a ≠ 0) (c : ℕ) :
    Polynomial.aeval (branchGenericLocationInSignAlgebra a +
      (c : BranchGenericSignAlgebra a) * branchGenericSignRoot a)
      (branchGenericLabelPolynomial a c) = 0 := by
  let : Fact (Irreducible (branchSignPolynomial
      (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)) :=
    ⟨branchSignPolynomial_irreducible
      (by simpa only [map_zero] using (algebraMap ℚ BranchLocationExtension).injective.ne ha)
      branchGenericDelta_ne_zero⟩
  let : Field (BranchGenericSignAlgebra a) := inferInstance
  let R := RatFunc BranchLocationField
  let L := RatFunc BranchLocationExtension
  let E := BranchGenericSignAlgebra a
  let φ := IsScalarTower.toAlgHom R L E
  let α : R := RatFunc.C (algebraMap ℚ BranchLocationField a) / RatFunc.X
  let Δ : L := RatFunc.C branchGenericDelta
  have hscale : algebraMap R L α * Δ =
      branchSignSquare (algebraMap ℚ BranchLocationExtension a) branchGenericDelta :=
    branch_ratFunc_scale_mul a branchGenericDelta
  have hβ : branchGenericSignRoot a ^ 2 = algebraMap R E α * φ Δ := by
    have he := branchSignRoot_square (algebraMap ℚ BranchLocationExtension a) branchGenericDelta
    change branchGenericSignRoot a ^ 2 = φ
      (branchSignSquare (algebraMap ℚ BranchLocationExtension a) branchGenericDelta) at he
    rw [← hscale, map_mul, φ.commutes] at he
    exact he
  have h := branchLabelPolynomial_basis_root branchGenericLocationRatBasis φ
    (RatFunc.C (AdjoinRoot.root (branchGenericLocationSextic.map
      (algebraMap BranchLocationParameters BranchLocationField)))) Δ (c : R) α
    (branchGenericSignRoot a) hβ
  have hloc : φ (RatFunc.C (AdjoinRoot.root (branchGenericLocationSextic.map
      (algebraMap BranchLocationParameters BranchLocationField)))) =
      branchGenericLocationInSignAlgebra a := rfl
  rw [hloc, map_natCast] at h
  exact h

/-- For each nonzero dividend, a bounded slope makes the concrete monic
characteristic polynomial irreducible of degree twelve. -/
theorem branchGeneric_exists_irreducible_label_polynomial (a : ℚ) (ha : a ≠ 0) :
    ∃ c : ℕ, c ≤ 144 ∧ Irreducible (branchGenericLabelPolynomial a c) ∧
      (branchGenericLabelPolynomial a c).natDegree = 12 := by
  let : Fact (Irreducible (branchSignPolynomial
      (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)) :=
    ⟨branchSignPolynomial_irreducible
      (by simpa only [map_zero] using (algebraMap ℚ BranchLocationExtension).injective.ne ha)
      branchGenericDelta_ne_zero⟩
  obtain ⟨c, hc, hirr, hdeg⟩ := branchGeneric_exists_degree_twelve_polynomial a ha
  have hd := (branchGenericSignExtension_field_degree a ha).2
  let : FiniteDimensional (RatFunc BranchLocationField) (BranchGenericSignAlgebra a) :=
    Module.finite_of_finrank_pos (by rw [hd]; norm_num)
  have he := Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite (RatFunc BranchLocationField)
      (branchGenericLocationInSignAlgebra a +
        (c : BranchGenericSignAlgebra a) * branchGenericSignRoot a)))
    (branchGenericLabelPolynomial_monic a c)
    (minpoly.dvd (RatFunc BranchLocationField) _ (branchGenericLabelPolynomial_root a ha c))
    (by rw [branchGenericLabelPolynomial_natDegree, hdeg])
  exact ⟨c, hc, he ▸ hirr, branchGenericLabelPolynomial_natDegree a c⟩

end
end PierceLengthBound.FixedDividend
