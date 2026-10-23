/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveVertexFamily
public import PierceLengthBound.BranchSieveMonicization
public import PierceLengthBound.BranchSieveMonicTransfer
public import PierceLengthBound.PolarProjectionGeometryGoodPattern
public import PierceLengthBound.BranchSieveResultantGeneric

/-! The actual monic four-vertex family for Hilbert specialization. It has
uniform degree and polynomial dividend height, is generically irreducible for
a bounded slope, and detects every bad nonzero-scale orbit pattern.

Generic unnormalized first-minor vertices recover the normalized branch
coefficients. They provide a coefficient map for proving generic irreducibility
of the monic integer family. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra
open scoped BranchLocationFields

/-- Generic vertices in order `(A,D,C,B)`, inverse to the normalized location
coefficients `c₁=−(B+C)/A`, `c₂=(C+D)/A`, `c₃=−(D+A)/A`. -/
def branchGenericVertex : Fin 4 → RatFunc BranchLocationField :=
  ![RatFunc.X, -RatFunc.X * (branchResultantGenericCoefficient 2 + 1),
    RatFunc.X * (branchResultantGenericCoefficient 1 + branchResultantGenericCoefficient 2 + 1),
    -RatFunc.X * (branchResultantGenericCoefficient 0 + branchResultantGenericCoefficient 1 +
      branchResultantGenericCoefficient 2 + 1)]

lemma branchGenericVertex_zero :
    branchGenericVertex 0 = (RatFunc.X : RatFunc BranchLocationField) := rfl

lemma branchGenericVertex_normalized :
    (-branchGenericVertex 3 - branchGenericVertex 2) / branchGenericVertex 0 =
        branchResultantGenericCoefficient 0 ∧
      (branchGenericVertex 2 + branchGenericVertex 1) / branchGenericVertex 0 =
        branchResultantGenericCoefficient 1 ∧
      (-branchGenericVertex 1 - branchGenericVertex 0) / branchGenericVertex 0 =
        branchResultantGenericCoefficient 2 := by
  dsimp [branchGenericVertex]
  constructor <;> (try constructor) <;> field_simp [RatFunc.X_ne_zero] <;> ring

/-- Monic degree-twelve family, before fixing its dividend variable. -/
def branchMonicVertexFamily (c : ℕ) : Polynomial (MvPolynomial (Fin 5) ℤ) :=
  branchMonicization 12 (branchVertexFamily c)

/-- The actual monic family in the four integer first-minor vertices. -/
def branchMonicVertexFamilyAt (a : ℤ) (c : ℕ) : Polynomial (MvPolynomial (Fin 4) ℤ) :=
  branchFamilyHead a (branchMonicVertexFamily c)

lemma branchMonicVertexFamilyAt_eq (a : ℤ) (c : ℕ) :
    branchMonicVertexFamilyAt a c = branchMonicization 12 (branchVertexFamilyAt a c) := by
  exact branchMonicization_map _ _ _

lemma branchMonicVertexFamily_monic (c : ℕ) : (branchMonicVertexFamily c).Monic :=
  branchMonicization_monic _ _

lemma branchMonicVertexFamilyAt_monic (a : ℤ) (c : ℕ) :
    (branchMonicVertexFamilyAt a c).Monic := (branchMonicVertexFamily_monic c).map _

lemma branchGenericResultantLabel_intCast (a : ℤ) (c : ℕ) :
    branchResultantLabel (a : RatFunc BranchLocationField) RatFunc.X c
      (branchResultantGenericCoefficient 0) (branchResultantGenericCoefficient 1)
      (branchResultantGenericCoefficient 2) = branchGenericResultantLabel (a : ℚ) c := by
  unfold branchGenericResultantLabel
  rw [map_intCast, map_intCast]

lemma branchGenericVertex_resultant (a : ℤ) (c : ℕ) :
    branchResultantLabel (a : RatFunc BranchLocationField) (branchGenericVertex 0) c
      ((-branchGenericVertex 3 - branchGenericVertex 2) / branchGenericVertex 0)
      ((branchGenericVertex 2 + branchGenericVertex 1) / branchGenericVertex 0)
      ((-branchGenericVertex 1 - branchGenericVertex 0) / branchGenericVertex 0) =
      branchGenericResultantLabel (a : ℚ) c := by
  obtain ⟨h0, h1, h2⟩ := branchGenericVertex_normalized
  rw [h0, h1, h2, branchGenericVertex_zero, branchGenericResultantLabel_intCast]

/-- The generic vertex evaluation recovers the explicit irreducible resultant
up to the nonzero denominator-clearing scalar. -/
lemma branchVertexFamilyAt_generic (a : ℤ) (c : ℕ) :
    (branchVertexFamilyAt a c).map
      (MvPolynomial.eval₂Hom (Int.castRingHom (RatFunc BranchLocationField)) branchGenericVertex) =
      Polynomial.C (RatFunc.X ^ branchVertexClearingExponent c) *
        branchGenericResultantLabel (a : ℚ) c := by
  have hA : branchGenericVertex 0 ≠ 0 := by
    rw [branchGenericVertex_zero]
    exact RatFunc.X_ne_zero
  have h := branchVertexFamilyAt_eval_field a c (RatFunc BranchLocationField)
    branchGenericVertex hA
  apply h.trans
  exact congrArg₂ (fun p q : Polynomial (RatFunc BranchLocationField) => p * q)
    (congrArg (fun z : RatFunc BranchLocationField =>
      Polynomial.C (z ^ branchVertexClearingExponent c)) branchGenericVertex_zero)
    (branchGenericVertex_resultant a c)

lemma branchFamilyRational_eval_map {r : ℕ} {K : Type} [CommRing K]
    (ψ : ℚ →+* K) (x : Fin r → K) (p : Polynomial (MvPolynomial (Fin r) ℤ)) :
    (branchFamilyRational p).map (MvPolynomial.eval₂Hom ψ x) =
      p.map (MvPolynomial.eval₂Hom (Int.castRingHom K) x) := by
  unfold branchFamilyRational
  rw [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro z
    simp
  · intro j
    simp

lemma branchFamilyRational_monicization {r : ℕ} (n : ℕ)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) :
    branchFamilyRational (branchMonicization n p) =
      branchMonicization n (branchFamilyRational p) :=
  branchMonicization_map _ _ _

lemma branchMonicVertexFamilyAt_rational_eq (a : ℤ) (c : ℕ) :
    branchFamilyRational (branchMonicVertexFamilyAt a c) =
      branchMonicization 12 (branchFamilyRational (branchVertexFamilyAt a c)) := by
  exact (congrArg branchFamilyRational (branchMonicVertexFamilyAt_eq a c)).trans
    (branchFamilyRational_monicization 12 (branchVertexFamilyAt a c))

lemma branchFamilyEval_monicization {r : ℕ} (n : ℕ) (x : Fin r → ℤ)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) :
    branchFamilyEval x (branchMonicization n p) =
      branchMonicization n (branchFamilyEval x p) :=
  branchMonicization_map _ _ _

lemma branchFamilyEval_natDegree_le {r : ℕ} (x : Fin r → ℤ)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) :
    (branchFamilyEval x p).natDegree ≤ p.natDegree := Polynomial.natDegree_map_le

lemma branchMonicVertexFamilyAt_eval_eq (a : ℤ) (c : ℕ) (x : Fin 4 → ℤ) :
    branchFamilyEval x (branchMonicVertexFamilyAt a c) =
      branchMonicization 12 (branchFamilyEval x (branchVertexFamilyAt a c)) := by
  exact (congrArg (branchFamilyEval x) (branchMonicVertexFamilyAt_eq a c)).trans
    (branchFamilyEval_monicization 12 x (branchVertexFamilyAt a c))

lemma branchVertexFamilyAt_rational_generic (a : ℤ) (c : ℕ) :
    (branchFamilyRational (branchVertexFamilyAt a c)).map
      (MvPolynomial.eval₂Hom (algebraMap ℚ (RatFunc BranchLocationField)) branchGenericVertex) =
      Polynomial.C ((RatFunc.X : RatFunc BranchLocationField) ^ branchVertexClearingExponent c) *
        branchGenericResultantLabel (a : ℚ) c :=
  (branchFamilyRational_eval_map (algebraMap ℚ (RatFunc BranchLocationField)) branchGenericVertex
    (branchVertexFamilyAt a c)).trans (branchVertexFamilyAt_generic a c)

lemma branchMonicization_vertexFamily_irreducible (a : ℤ) (c : ℕ)
    (hirr : Irreducible (branchGenericResultantLabel (a : ℚ) c))
    (hdeg : (branchGenericResultantLabel (a : ℚ) c).natDegree = 12)
    (he : (branchFamilyRational (branchVertexFamilyAt a c)).map
      (MvPolynomial.eval₂Hom (algebraMap ℚ (RatFunc BranchLocationField)) branchGenericVertex) =
      Polynomial.C ((RatFunc.X : RatFunc BranchLocationField) ^ branchVertexClearingExponent c) *
        branchGenericResultantLabel (a : ℚ) c) :
    Irreducible (branchMonicization 12 (branchFamilyRational (branchVertexFamilyAt a c))) :=
  branchMonicization_irreducible_of_scalar 12
    (branchFamilyRational (branchVertexFamilyAt a c))
    (MvPolynomial.eval₂Hom (algebraMap ℚ (RatFunc BranchLocationField)) branchGenericVertex)
    ((RatFunc.X : RatFunc BranchLocationField) ^ branchVertexClearingExponent c)
    (branchGenericResultantLabel (a : ℚ) c) he
    (pow_ne_zero _ RatFunc.X_ne_zero) hirr hdeg (by norm_num)

lemma branchMonicVertexFamilyAt_irreducible_of_monicization (a : ℤ) (c : ℕ)
    (hi : Irreducible (branchMonicization 12 (branchFamilyRational (branchVertexFamilyAt a c)))) :
    Irreducible (branchFamilyRational (branchMonicVertexFamilyAt a c)) :=
  Eq.mp (congrArg Irreducible (branchMonicVertexFamilyAt_rational_eq a c).symm) hi

lemma branchMonicVertexFamilyAt_irreducible_of_generic (a : ℤ) (c : ℕ)
    (hirr : Irreducible (branchGenericResultantLabel (a : ℚ) c))
    (hdeg : (branchGenericResultantLabel (a : ℚ) c).natDegree = 12) :
    Irreducible (branchFamilyRational (branchMonicVertexFamilyAt a c)) :=
  branchMonicVertexFamilyAt_irreducible_of_monicization a c
    (branchMonicization_vertexFamily_irreducible a c hirr hdeg
      (branchVertexFamilyAt_rational_generic a c))

/-- The monic integer family is generically irreducible for a slope between
zero and 144. This is proved by mapping back to the normalized generic field;
monicity makes irreducibility descend along that coefficient map. -/
theorem branchMonicVertexFamilyAt_exists_irreducible (a : ℤ) (ha : a ≠ 0) :
    ∃ c : ℕ, c ≤ 144 ∧ Irreducible
      (branchFamilyRational (branchMonicVertexFamilyAt a c)) := by
  obtain ⟨c, hc, hirr, hdeg⟩ := branchGeneric_exists_irreducible_resultant_label (a : ℚ)
    (by exact_mod_cast ha)
  exact ⟨c, hc, branchMonicVertexFamilyAt_irreducible_of_generic a c hirr hdeg⟩

/-- Uniform degree and polynomial-height bounds for the actual monic families,
with constants independent of the dividend and the bounded slope. -/
theorem branchMonicVertexFamilyAt_uniform_bounds :
    ∃ d C : ℕ, 0 < C ∧ ∀ (a : ℤ) (c : ℕ), c ≤ 144 →
      (branchMonicVertexFamilyAt a c).natDegree ≤ d ∧
      (∀ j, ((branchMonicVertexFamilyAt a c).coeff j).totalDegree ≤ d) ∧
      ∀ j s, |((branchMonicVertexFamilyAt a c).coeff j).coeff s| ≤
        (C * (a.natAbs + 1) ^ d : ℕ) := by
  obtain ⟨d, H, hH, hb⟩ := branch_bounded_slope_family_bounds branchMonicVertexFamily
  refine ⟨d, (d + 1) * H, by positivity, ?_⟩
  intro a c hc
  obtain ⟨hd, hp, hh⟩ := hb c hc
  exact branchFamilyHead_degree_height (branchMonicVertexFamily c) hd hp hh (by omega)
    (show |a| ≤ ((a.natAbs + 1 : ℕ) : ℤ) by simp)

lemma branchVertexLabelPolynomial_sub (a : ℕ) (c : ℕ) (x : Fin 4 → ℤ) :
    branchResultantLabel ((a : ℤ) : ℚ) (x 0 : ℚ) c
      ((-(x 3 : ℚ) - x 2) / x 0) (((x 2 : ℚ) + x 1) / x 0)
      ((-(x 1 : ℚ) - x 0) / x 0) = branchVertexLabelPolynomial a x (c : ℚ) := by
  simp only [branchVertexLabelPolynomial, Int.cast_natCast, neg_add, sub_eq_add_neg]

/-- An irreducible specialization of the monic family certifies the actual
branch-good predicate. Leading-degree degeneration is automatically excluded
by irreducibility of the monic degree-twelve equation. -/
theorem branchVertexGood_of_monic_irreducible (a : ℕ) (c : ℕ) (x : Fin 4 → ℤ)
    (hx : x 0 ≠ 0)
    (hir : Irreducible (branchFamilyEval x (branchMonicVertexFamilyAt (a : ℤ) c))) :
    branchVertexGood a x := by
  have hi : Irreducible
      (branchMonicization 12 (branchFamilyEval x (branchVertexFamilyAt (a : ℤ) c))) :=
    Eq.mp (congrArg Irreducible (branchMonicVertexFamilyAt_eval_eq (a : ℤ) c x)) hir
  have hd : (branchFamilyEval x (branchVertexFamilyAt (a : ℤ) c)).natDegree ≤ 12 :=
    (branchFamilyEval_natDegree_le x _).trans (branchVertexFamilyAt_natDegree_le _ _)
  have he : branchFamilyEval x (branchVertexFamilyAt (a : ℤ) c) =
      Polynomial.C ((x 0 : ℚ) ^ branchVertexClearingExponent c) *
        branchVertexLabelPolynomial a x (c : ℚ) := by
    exact (branchVertexFamilyAt_eval (a : ℤ) c x hx).trans
      (congrArg (fun q : Polynomial ℚ =>
        Polynomial.C ((x 0 : ℚ) ^ branchVertexClearingExponent c) * q)
        (branchVertexLabelPolynomial_sub a c x))
  have hscalar : (x 0 : ℚ) ^ branchVertexClearingExponent c ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hx)
  exact ⟨c, branchMonicization_rat_scalar_consequences 12
    (branchFamilyEval x (branchVertexFamilyAt (a : ℤ) c)) hd (by norm_num) hi
    ((x 0 : ℚ) ^ branchVertexClearingExponent c) (branchVertexLabelPolynomial a x c)
    he hscalar⟩

end
end PierceLengthBound.FixedDividend
