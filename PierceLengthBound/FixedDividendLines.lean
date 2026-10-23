/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividend

/-!
# Line obstructions along the four exceptional directions

The fourth node and the next two gaps are eliminated through the kernel relations,
giving the quadratic `lineQuadratic` and the norm `lineNorm` in three free nodes.
Symmetric second differences give four quadratic-coefficient identities, one for
each exceptional direction, for arbitrary real parameters. On a line with affine
norm each forces an obstruction equation, which large gaps exclude. The degree-six
resultant bound along these directions is in `FixedDividendLineResultant`.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

/-- Fourth node recovered from the first kernel relation. -/
def fourthNode {R : Type*} [CommRing R] (ρ u v a b c : R) : R :=
  (ρ + u) * a - (u - v) * b - (v - 1) * c

/-- Gap data, including the fifth gap from the next linear kernel relation. -/
def lineGaps {R : Type*} [CommRing R] (ρ u v ρ' u' v' a b c : R) : Fin 5 → R :=
  let d := fourthNode ρ u v a b c
  ![a, b - a, c - b, d - c, ρ' * (b - a) - u' * (c - b) - v' * (d - c)]

/-- The first five nodes and the following node. -/
def lineNodes {R : Type*} [CommRing R] (ρ u v ρ' u' v' a b c : R) : Fin 6 → R :=
  let d := fourthNode ρ u v a b c
  let k := lineGaps ρ u v ρ' u' v' a b c
  ![0, a, b, c, d, d + k 4]

/-- Six gaps, with the last eliminated by the next quadratic kernel relation. -/
def extendedLineGaps {R : Type*} [CommRing R] (ρ u v ρ' u' v' a b c : R) : Fin 6 → R :=
  let k := lineGaps ρ u v ρ' u' v' a b c
  let s := lineNodes ρ u v ρ' u' v' a b c
  let r1 := k 1 * (s 1 + s 2) + k 2
  let r2 := k 2 * (s 2 + s 3) + k 3
  let r3 := k 3 * (s 3 + s 4) + k 4
  ![k 0, k 1, k 2, k 3, k 4,
    ρ' * r1 - u' * r2 - v' * r3 - k 4 * (s 4 + s 5)]

/-- The first quadratic with both linear kernel relations imposed. -/
def lineQuadratic {R : Type*} [CommRing R] (ρ u v ρ' u' v' a b c : R) : R :=
  let s := lineNodes ρ u v ρ' u' v' a b c
  let k := lineGaps ρ u v ρ' u' v' a b c
  ∑ j : Fin 5, coeffs ρ u v j * (s j.castSucc ^ 2 + k j)

/-- The cubic norm expression with the next quadratic imposed. -/
def lineNorm {R : Type*} [CommRing R] (ρ u v ρ' u' v' a b c : R) : R :=
  let s := lineNodes ρ u v ρ' u' v' a b c
  let k := extendedLineGaps ρ u v ρ' u' v' a b c
  ∑ j : Fin 5, coeffs ρ u v j *
    (s j.castSucc ^ 3 + 3 * s j.castSucc ^ 2 +
      3 * s j.castSucc * (1 + k j.castSucc) + (1 + k j.castSucc) ^ 2 + k j.succ)

/-- Pair `(0,3)`: the quadratic coefficient is `-ρ s₃ + 2 f₁`. -/
theorem line_identity_03 (ρ u ρ' u' v' a b c : ℝ) :
    lineNorm ρ u (1 - ρ) ρ' u' v' (a + 1) (b + 1) c +
      lineNorm ρ u (1 - ρ) ρ' u' v' (a - 1) (b - 1) c -
      2 * lineNorm ρ u (1 - ρ) ρ' u' v' a b c =
    -2 * ρ * c + 2 * (lineQuadratic ρ u (1 - ρ) ρ' u' v' (a + 1) (b + 1) c -
      lineQuadratic ρ u (1 - ρ) ρ' u' v' (a - 1) (b - 1) c) := by
  simp [lineNorm, lineQuadratic, lineNodes, extendedLineGaps, lineGaps,
    fourthNode, coeffs, Fin.sum_univ_succ]
  ring

/-- Pair `(1,2)`: the quadratic coefficient is `(ρ+u)(s₂-s₁-1) + f₁`. -/
theorem line_identity_12 (ρ u ρ' u' v' a b c : ℝ) :
    lineNorm ρ u (-ρ) ρ' u' v' (a + 1) (b + 1) c +
      lineNorm ρ u (-ρ) ρ' u' v' (a - 1) (b - 1) c -
      2 * lineNorm ρ u (-ρ) ρ' u' v' a b c =
    2 * (ρ + u) * (b - a - 1) +
      (lineQuadratic ρ u (-ρ) ρ' u' v' (a + 1) (b + 1) c -
      lineQuadratic ρ u (-ρ) ρ' u' v' (a - 1) (b - 1) c) := by
  simp [lineNorm, lineQuadratic, lineNodes, extendedLineGaps, lineGaps,
    fourthNode, coeffs, Fin.sum_univ_succ]
  ring

/-- Pair `(2,3)`: the quadratic coefficient is `(v-1)(s₃-s₂-1) + f₁`. -/
theorem line_identity_23 (ρ v ρ' u' v' a b c : ℝ) :
    lineNorm ρ 1 v ρ' u' v' a (b + 1) (c + 1) +
      lineNorm ρ 1 v ρ' u' v' a (b - 1) (c - 1) -
      2 * lineNorm ρ 1 v ρ' u' v' a b c =
    2 * (v - 1) * (c - b - 1) +
      (lineQuadratic ρ 1 v ρ' u' v' a (b + 1) (c + 1) -
      lineQuadratic ρ 1 v ρ' u' v' a (b - 1) (c - 1)) := by
  simp [lineNorm, lineQuadratic, lineNodes, extendedLineGaps, lineGaps,
    fourthNode, coeffs, Fin.sum_univ_succ]
  ring

/-- Pair `(1,4)`: the quadratic coefficient is `c₂-(s₄-s₁) + 2 f₁`. -/
theorem line_identity_14 (ρ v ρ' u' v' a b c : ℝ) :
    lineNorm ρ (1 - ρ) v ρ' u' v' (a + 1) b c +
      lineNorm ρ (1 - ρ) v ρ' u' v' (a - 1) b c -
      2 * lineNorm ρ (1 - ρ) v ρ' u' v' a b c =
    2 * ((1 - ρ - v) - (fourthNode ρ (1 - ρ) v a b c - a)) +
      2 * (lineQuadratic ρ (1 - ρ) v ρ' u' v' (a + 1) b c -
      lineQuadratic ρ (1 - ρ) v ρ' u' v' (a - 1) b c) := by
  simp [lineNorm, lineQuadratic, lineNodes, extendedLineGaps, lineGaps,
    fourthNode, coeffs, Fin.sum_univ_succ]
  ring

/-- On a line with affine norm, pair `(0,3)` forces the third node to vanish. -/
theorem line_obstruction_03 {ρ u ρ' u' v' a b c : ℝ} (hρ : 0 < ρ)
    (hp : lineQuadratic ρ u (1 - ρ) ρ' u' v' (a + 1) (b + 1) c = 0)
    (hm : lineQuadratic ρ u (1 - ρ) ρ' u' v' (a - 1) (b - 1) c = 0)
    (hD : lineNorm ρ u (1 - ρ) ρ' u' v' (a + 1) (b + 1) c +
      lineNorm ρ u (1 - ρ) ρ' u' v' (a - 1) (b - 1) c =
      2 * lineNorm ρ u (1 - ρ) ρ' u' v' a b c) : c = 0 := by
  have h := line_identity_03 ρ u ρ' u' v' a b c
  rw [hp, hm, hD] at h
  have hz : ρ * c = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left hρ.ne'

/-- On a line with affine norm, pair `(1,2)` forces the second gap to be one. -/
theorem line_obstruction_12 {ρ u ρ' u' v' a b c : ℝ} (hρu : 0 < ρ + u)
    (hp : lineQuadratic ρ u (-ρ) ρ' u' v' (a + 1) (b + 1) c = 0)
    (hm : lineQuadratic ρ u (-ρ) ρ' u' v' (a - 1) (b - 1) c = 0)
    (hD : lineNorm ρ u (-ρ) ρ' u' v' (a + 1) (b + 1) c +
      lineNorm ρ u (-ρ) ρ' u' v' (a - 1) (b - 1) c =
      2 * lineNorm ρ u (-ρ) ρ' u' v' a b c) : b - a = 1 := by
  have h := line_identity_12 ρ u ρ' u' v' a b c
  rw [hp, hm, hD] at h
  have hz : (ρ + u) * (b - a - 1) = 0 := by linarith
  have := (mul_eq_zero.mp hz).resolve_left hρu.ne'
  linarith

/-- On a line with affine norm, pair `(2,3)` forces the third gap to be one. -/
theorem line_obstruction_23 {ρ v ρ' u' v' a b c : ℝ} (hv : v < 1)
    (hp : lineQuadratic ρ 1 v ρ' u' v' a (b + 1) (c + 1) = 0)
    (hm : lineQuadratic ρ 1 v ρ' u' v' a (b - 1) (c - 1) = 0)
    (hD : lineNorm ρ 1 v ρ' u' v' a (b + 1) (c + 1) +
      lineNorm ρ 1 v ρ' u' v' a (b - 1) (c - 1) =
      2 * lineNorm ρ 1 v ρ' u' v' a b c) : c - b = 1 := by
  have h := line_identity_23 ρ v ρ' u' v' a b c
  rw [hp, hm, hD] at h
  have hz : (v - 1) * (c - b - 1) = 0 := by linarith
  have := (mul_eq_zero.mp hz).resolve_left (by linarith : v - 1 ≠ 0)
  linarith

/-- On a line with affine norm, pair `(1,4)` fixes the sum of three gaps. -/
theorem line_obstruction_14 {ρ v ρ' u' v' a b c : ℝ}
    (hp : lineQuadratic ρ (1 - ρ) v ρ' u' v' (a + 1) b c = 0)
    (hm : lineQuadratic ρ (1 - ρ) v ρ' u' v' (a - 1) b c = 0)
    (hD : lineNorm ρ (1 - ρ) v ρ' u' v' (a + 1) b c +
      lineNorm ρ (1 - ρ) v ρ' u' v' (a - 1) b c =
      2 * lineNorm ρ (1 - ρ) v ρ' u' v' a b c) :
    fourthNode ρ (1 - ρ) v a b c - a = 1 - ρ - v := by
  have h := line_identity_14 ρ v ρ' u' v' a b c
  rw [hp, hm, hD] at h
  linarith

/-- Under the gap lower bounds, none of the four obstruction equations holds. -/
theorem line_obstructions_excluded {a b c d c₂ X : ℝ}
    (hc : 0 < c) (hab : 1 < b - a) (hbc : 1 < c - b)
    (hheight : c₂ ≤ 2 * X) (hlarge : 2 * X < d - a) :
    ¬ (c = 0 ∨ b - a = 1 ∨ c - b = 1 ∨ d - a = c₂) := by
  rintro (h | h | h | h) <;> linarith

/-- A resultant of degree at most six and the fixed-dividend identity force a norm of
degree at most one. -/
theorem norm_degree_le_one {A a : ℝ} {D R : Polynomial ℝ}
    (hA : A ≠ 0) (ha : a ≠ 0) (hR : R.natDegree ≤ 6)
    (hidentity : Polynomial.C A * R = Polynomial.C a * D ^ 4) :
    D.natDegree ≤ 1 := by
  have h := congrArg Polynomial.natDegree hidentity
  rw [Polynomial.natDegree_C_mul hA, Polynomial.natDegree_C_mul ha,
    Polynomial.natDegree_pow] at h
  omega

end PierceLengthBound.FixedDividend
