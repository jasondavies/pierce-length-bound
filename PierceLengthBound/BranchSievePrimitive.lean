/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveReconstruction
public import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Tactic

/-! A bounded primitive-element choice for the degree-twelve label
(Lemma 10.3). In the degree-twelve generic branch algebra, the location plus
`c` times the branch sign is primitive for some integer slope `0 ≤ c ≤ 144`;
the bound is the square of the number of embeddings. The paper states the same
range and remarks that counting unordered pairs gives `0 ≤ c ≤ 66`. A bounded slope keeps the
resulting family of branch polynomials uniform in the dividend. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Polynomial
open scoped IntermediateField

/-- A bounded integer slope separates a finite collection of distinct pairs. -/
theorem branch_exists_separating_nat_slope {K ι : Type*} [Field K] [CharZero K]
    [Fintype ι] (x y : ι → K)
    (hxy : Function.Injective fun i => (x i, y i)) :
    ∃ c : ℕ, c ≤ Fintype.card ι ^ 2 ∧
      Function.Injective (fun i => x i + (c : K) * y i) := by
  classical
  let bad : Finset K := (univ : Finset (ι × ι)).image
    (fun ij => (x ij.2 - x ij.1) / (y ij.1 - y ij.2))
  let choices : Finset K := (range (Fintype.card ι ^ 2 + 1)).image (fun c : ℕ => (c : K))
  have hbad : bad.card ≤ Fintype.card ι ^ 2 := by
    exact (card_image_le).trans_eq (by simp [pow_two])
  have hchoices : choices.card = Fintype.card ι ^ 2 + 1 := by
    rw [card_image_of_injective _ Nat.cast_injective, card_range]
  obtain ⟨z, hz, hzbad⟩ := exists_mem_notMem_of_card_lt_card
    (lt_of_le_of_lt hbad (by omega : Fintype.card ι ^ 2 < choices.card))
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hz
  refine ⟨c, by simpa using Nat.le_of_lt_succ (mem_range.mp hc), ?_⟩
  intro i j he
  by_cases hy : y i = y j
  · apply hxy
    exact Prod.ext (add_right_cancel (by simpa only [hy] using he)) hy
  · exfalso
    apply hzbad
    apply mem_image.mpr
    refine ⟨(i, j), mem_univ _, ?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    linear_combination -he

open scoped RatFunc
attribute [local instance] Polynomial.algebra

lemma branch_ratFunc_algebraMap_C {F L : Type*} [Field F] [Field L] [Algebra F L]
    (c : F) :
    algebraMap (RatFunc F) (RatFunc L) (RatFunc.C c) = RatFunc.C (algebraMap F L c) := by
  rw [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply F[X]]
  rw [IsScalarTower.algebraMap_apply F[X] L[X] (RatFunc L)]
  simp

lemma branch_ratFunc_algebraMap_X {F L : Type*} [Field F] [Field L] [Algebra F L] :
    algebraMap (RatFunc F) (RatFunc L) RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply F[X]]
  rw [IsScalarTower.algebraMap_apply F[X] L[X] (RatFunc L)]
  simp

/-- Over the rational-function base field, homomorphisms are determined by the
constant coefficient field, since the common indeterminate lies in the base. -/
theorem branch_ratFunc_algHom_ext {F L K : Type*} [Field F] [Field L] [Field K]
    [Algebra F L] [Algebra (RatFunc F) K]
    (φ ψ : RatFunc L →ₐ[RatFunc F] K)
    (hc : ∀ c : L, φ (RatFunc.C c) = ψ (RatFunc.C c)) : φ = ψ := by
  have hX : φ RatFunc.X = ψ RatFunc.X := by
    rw [← branch_ratFunc_algebraMap_X (F := F) (L := L), φ.commutes, ψ.commutes]
  apply AlgHom.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := L[X])
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [RatFunc.algebraMap_monomial, map_mul, map_pow]
    change φ (RatFunc.C c) * φ RatFunc.X ^ n = ψ (RatFunc.C c) * ψ RatFunc.X ^ n
    rw [hc, hX]

instance branchLocationExtension_finiteDimensional :
    FiniteDimensional BranchLocationField BranchLocationExtension :=
  Module.finite_of_finrank_pos (by rw [branchLocationExtension_finrank]; norm_num)

/-- The generic branch algebra: the branch sign adjoined to the generic
location field with the absolute scale. -/
abbrev BranchGenericSignAlgebra (a : ℚ) := AdjoinRoot
  (branchSignPolynomial (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)

/-- The location viewed in the generic branch algebra. -/
def branchGenericLocationInSignAlgebra (a : ℚ) : BranchGenericSignAlgebra a :=
  algebraMap (RatFunc BranchLocationExtension) (BranchGenericSignAlgebra a)
    (RatFunc.C (AdjoinRoot.root
      (branchGenericLocationSextic.map (algebraMap BranchLocationParameters BranchLocationField))))

/-- The sign generator viewed in the generic branch algebra. -/
def branchGenericSignRoot (a : ℚ) : BranchGenericSignAlgebra a :=
  AdjoinRoot.root (branchSignPolynomial
    (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)

/-- A branch embedding is determined by its location and sign. -/
theorem branchGeneric_embedding_pair_injective (a : ℚ)
    {K : Type*} [Field K] [Algebra (RatFunc BranchLocationField) K] :
    Function.Injective (fun φ : BranchGenericSignAlgebra a →ₐ[RatFunc BranchLocationField] K =>
      (φ (branchGenericLocationInSignAlgebra a), φ (branchGenericSignRoot a))) := by
  intro φ ψ he
  apply AdjoinRoot.algHom_ext'
  · apply branch_ratFunc_algHom_ext (F := BranchLocationField)
    intro c
    let ι := algebraMap (RatFunc BranchLocationExtension) (BranchGenericSignAlgebra a)
    have hcoeff : (φ.toRingHom.comp ι).comp RatFunc.C =
        (ψ.toRingHom.comp ι).comp RatFunc.C := by
      apply AdjoinRoot.ringHom_ext
      · ext c
        change φ (ι (RatFunc.C (algebraMap BranchLocationField BranchLocationExtension c))) =
          ψ (ι (RatFunc.C (algebraMap BranchLocationField BranchLocationExtension c)))
        rw [← branch_ratFunc_algebraMap_C (F := BranchLocationField)
          (L := BranchLocationExtension)]
        dsimp only [ι]
        rw [← IsScalarTower.algebraMap_apply, φ.commutes, ψ.commutes]
      · exact congrArg Prod.fst he
    exact DFunLike.congr_fun hcoeff c
  · exact congrArg Prod.snd he

/-- For every nonzero dividend, one of the 145 explicit combinations `t+cβ`
has irreducible degree-twelve minimal polynomial over the vertex function field.
The coefficient bound is independent of the dividend. -/
theorem branchGeneric_exists_degree_twelve_polynomial (a : ℚ) (ha : a ≠ 0) :
    ∃ c : ℕ, c ≤ 144 ∧
      Irreducible (minpoly (RatFunc BranchLocationField)
        (branchGenericLocationInSignAlgebra a + (c : BranchGenericSignAlgebra a) *
          branchGenericSignRoot a)) ∧
      (minpoly (RatFunc BranchLocationField)
        (branchGenericLocationInSignAlgebra a + (c : BranchGenericSignAlgebra a) *
          branchGenericSignRoot a)).natDegree = 12 := by
  have := Fact.mk (branchGenericSignPolynomial_irreducible ha)
  let F := RatFunc BranchLocationField
  let E := BranchGenericSignAlgebra a
  let K := AlgebraicClosure F
  have hd : Module.finrank F E = 12 := (branchGenericSignExtension_field_degree a ha).2
  let : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hd]; norm_num)
  obtain ⟨c, hc, hinj⟩ := branch_exists_separating_nat_slope
    (fun φ : E →ₐ[F] K => φ (branchGenericLocationInSignAlgebra a))
    (fun φ => φ (branchGenericSignRoot a)) (branchGeneric_embedding_pair_injective a)
  have hc' : c ≤ 144 := by simpa only [AlgHom.card F E K, hd, Nat.reducePow] using hc
  have hp : F⟮branchGenericLocationInSignAlgebra a + (c : E) * branchGenericSignRoot a⟯ = ⊤ := by
    apply (Field.primitive_element_iff_algHom_eq_of_eval' F K
      (fun _ => IsAlgClosed.splits _) _).mpr
    simpa only [map_add, map_mul, map_natCast] using hinj
  refine ⟨c, hc', minpoly.irreducible (IsIntegral.of_finite F _), ?_⟩
  exact ((Field.primitive_element_iff_minpoly_natDegree_eq F _).mp hp).trans hd

/-! Direct field instances for the generic location fields, opened where repeated
field-instance search through `FractionRing` and `RatFunc` is too slow. -/
namespace BranchLocationFields

scoped instance locationField : Field BranchLocationField := inferInstance
scoped instance locationExtension : Field BranchLocationExtension := inferInstance
scoped instance ratField : Field (RatFunc BranchLocationField) := inferInstance
scoped instance ratExtension : Field (RatFunc BranchLocationExtension) := inferInstance

end BranchLocationFields

end
end PierceLengthBound.FixedDividend
