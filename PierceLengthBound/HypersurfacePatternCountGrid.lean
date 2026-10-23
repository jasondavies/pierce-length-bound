/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendLinearCoordinates

/-! # Polynomial zeros on a rectangular three-dimensional grid -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Matrix

/-- Schwartz–Zippel on a product grid with unequal sides: a nonzero ternary polynomial
of degree `D` has at most `D (|S₀||S₁| + |S₀||S₂| + |S₁||S₂|)` zeros. -/
theorem ternary_polynomial_grid_count {f : MvPolynomial (Fin 3) ℚ} (hf : f ≠ 0)
    (S : Fin 3 → Finset ℚ) (hS : ∀ i, (S i).Nonempty) :
    (((Fintype.piFinset S).filter fun x => eval x f = 0).card : ℝ) ≤
      f.totalDegree * ((S 0).card * (S 1).card +
        (S 0).card * (S 2).card + (S 1).card * (S 2).card) := by
  classical
  have hsz := schwartz_zippel_sum_degreeOf hf S
  have hh : (((Fintype.piFinset S).filter fun x => eval x f = 0).card : ℝ) /
      ((S 0).card * (S 1).card * (S 2).card) ≤
      f.degreeOf 0 / (S 0).card + f.degreeOf 1 / (S 1).card +
        f.degreeOf 2 / (S 2).card := by
    have h := (NNRat.cast_le (K := ℝ)).mpr hsz
    simpa [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_prod, NNRat.cast_sum,
      Fin.sum_univ_succ, Fin.prod_univ_succ, mul_assoc, add_assoc] using h
  have h0 : (0 : ℝ) < (S 0).card := by exact_mod_cast Finset.card_pos.mpr (hS 0)
  have h1 : (0 : ℝ) < (S 1).card := by exact_mod_cast Finset.card_pos.mpr (hS 1)
  have h2 : (0 : ℝ) < (S 2).card := by exact_mod_cast Finset.card_pos.mpr (hS 2)
  have hh' : (((Fintype.piFinset S).filter fun x => eval x f = 0).card : ℝ) ≤
      (f.degreeOf 0 : ℝ) * ((S 1).card * (S 2).card) +
      (f.degreeOf 1 : ℝ) * ((S 0).card * (S 2).card) +
      (f.degreeOf 2 : ℝ) * ((S 0).card * (S 1).card) := by
    have hhh := (div_le_iff₀ (by positivity : (0 : ℝ) < (S 0).card * (S 1).card *
      (S 2).card)).mp hh
    convert hhh using 1
    field_simp
  have d0 : (f.degreeOf 0 : ℝ) ≤ f.totalDegree := by
    exact_mod_cast degreeOf_le_totalDegree f 0
  have d1 : (f.degreeOf 1 : ℝ) ≤ f.totalDegree := by
    exact_mod_cast degreeOf_le_totalDegree f 1
  have d2 : (f.degreeOf 2 : ℝ) ≤ f.totalDegree := by
    exact_mod_cast degreeOf_le_totalDegree f 2
  have hd0 := mul_le_mul_of_nonneg_right d0
    (by positivity : (0 : ℝ) ≤ (S 1).card * (S 2).card)
  have hd1 := mul_le_mul_of_nonneg_right d1
    (by positivity : (0 : ℝ) ≤ (S 0).card * (S 2).card)
  have hd2 := mul_le_mul_of_nonneg_right d2
    (by positivity : (0 : ℝ) ≤ (S 0).card * (S 1).card)
  nlinarith

/-- Rational images of the integers in the centered real interval. -/
def rationalIntegerInterval (R : ℝ) : Finset ℚ :=
  (Finset.Icc (-⌊R⌋) ⌊R⌋).image (fun z : ℤ => (z : ℚ))

lemma rationalIntegerInterval_nonempty {R : ℝ} (hR : 0 ≤ R) :
    (rationalIntegerInterval R).Nonempty := by
  refine ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr ?_, by simp⟩⟩
  have h := Int.floor_nonneg.mpr hR
  omega

lemma mem_rationalIntegerInterval {R : ℝ} {z : ℤ} (hz : |(z : ℝ)| ≤ R) :
    (z : ℚ) ∈ rationalIntegerInterval R := by
  refine Finset.mem_image.mpr ⟨z, Finset.mem_Icc.mpr ?_, rfl⟩
  have h1 : z ≤ ⌊R⌋ := Int.le_floor.mpr (le_trans (le_abs_self _) hz)
  have h2 : -z ≤ ⌊R⌋ := Int.le_floor.mpr (by
    push_cast
    exact le_trans (neg_le_abs _) hz)
  omega

lemma rationalIntegerInterval_card {R : ℝ} (hR : 1 ≤ R) :
    ((rationalIntegerInterval R).card : ℝ) ≤ 3 * R := by
  classical
  have hfloor : 0 ≤ ⌊R⌋ := Int.floor_nonneg.mpr (by linarith)
  calc ((rationalIntegerInterval R).card : ℝ)
      ≤ ((Finset.Icc (-⌊R⌋) ⌊R⌋).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
    _ = 2 * (⌊R⌋ : ℝ) + 1 := by
      rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    _ ≤ 3 * R := by linarith [Int.floor_le R]

/-- On the integer grid with sides `[-3X/ℓᵢ, 3X/ℓᵢ]`, a nonzero ternary polynomial of
degree `D` has at most `243 D X² / L` zeros when `ℓᵢ ≤ 3X` and every pair of lengths
has product at least `L`. -/
theorem ternary_polynomial_weighted_grid_count {f : MvPolynomial (Fin 3) ℚ} (hf : f ≠ 0)
    {X L : ℝ} (hX : 0 < X) (hL : 0 < L) (ℓ : Fin 3 → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hsmall : ∀ i, ℓ i ≤ 3 * X)
    (hpair : ∀ i j, i ≠ j → L ≤ ℓ i * ℓ j) :
    let S := fun i => rationalIntegerInterval (3 * X / ℓ i)
    (((Fintype.piFinset S).filter fun x => eval x f = 0).card : ℝ) ≤
      243 * f.totalDegree * X ^ 2 / L := by
  classical
  dsimp only
  let S := fun i => rationalIntegerInterval (3 * X / ℓ i)
  have hR i : 1 ≤ 3 * X / ℓ i := (le_div_iff₀ (hℓ i)).mpr (by simpa using hsmall i)
  have hcard i : ((S i).card : ℝ) ≤ 9 * X / ℓ i := by
    have := rationalIntegerInterval_card (hR i)
    dsimp only [S]
    convert this using 1
    ring
  have htwo i j (hij : i ≠ j) : ((S i).card : ℝ) * (S j).card ≤ 81 * X ^ 2 / L := by
    calc ((S i).card : ℝ) * (S j).card
        ≤ (9 * X / ℓ i) * (9 * X / ℓ j) :=
          mul_le_mul (hcard i) (hcard j) (by positivity)
            (div_nonneg (by positivity) (hℓ i).le)
      _ = 81 * X ^ 2 / (ℓ i * ℓ j) := by ring
      _ ≤ 81 * X ^ 2 / L := div_le_div_of_nonneg_left (by positivity) hL (hpair i j hij)
  have hc := ternary_polynomial_grid_count hf S
    (fun i => rationalIntegerInterval_nonempty
      (div_nonneg (by positivity) (hℓ i).le))
  have hp01 := htwo 0 1 (by decide)
  have hp02 := htwo 0 2 (by decide)
  have hp12 := htwo 1 2 (by decide)
  calc _ ≤ (f.totalDegree : ℝ) * ((S 0).card * (S 1).card +
      (S 0).card * (S 2).card + (S 1).card * (S 2).card) := hc
    _ ≤ (f.totalDegree : ℝ) * (3 * (81 * X ^ 2 / L)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

/-- If every point of `T` has integral coordinates `y` in an invertible rational basis
with `ℓᵢ |yᵢ| ≤ 3X`, a nonzero ternary polynomial of degree `D` vanishes at most
`243 D X² / L` times on `T`. -/
theorem polynomial_integer_set_count_of_coordinates
    {f : MvPolynomial (Fin 3) ℚ} (hf : f ≠ 0)
    (T : Finset (Fin 3 → ℤ)) (C : Matrix (Fin 3) (Fin 3) ℚ) (hC : C.det ≠ 0)
    {X L : ℝ} (hX : 0 < X) (hL : 0 < L) (ℓ : Fin 3 → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hsmall : ∀ i, ℓ i ≤ 3 * X)
    (hpair : ∀ i j, i ≠ j → L ≤ ℓ i * ℓ j)
    (hcoord : ∀ w ∈ T, ∃ y : Fin 3 → ℤ,
      C *ᵥ (fun i => (y i : ℚ)) = (fun i => (w i : ℚ)) ∧
      ∀ i, ℓ i * |(y i : ℝ)| ≤ 3 * X) :
    ((T.filter fun w => eval (fun i => (w i : ℚ)) f = 0).card : ℝ) ≤
      243 * f.totalDegree * X ^ 2 / L := by
  classical
  let g := matrixSubstitution C f
  have hg : g ≠ 0 := by
    let e := matrixCoordinateEquiv C C⁻¹ (C.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hC))
      (C.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hC))
    intro hz
    apply hf
    exact e.injective (hz.trans (map_zero e).symm)
  have hdeg : g.totalDegree ≤ f.totalDegree :=
    affine_hom_totalDegree_le _ (matrixSubstitution_X_degree C) f
  let S := fun i => rationalIntegerInterval (3 * X / ℓ i)
  let G := (Fintype.piFinset S).filter fun y => eval y g = 0
  let Z := T.filter fun w => eval (fun i => (w i : ℚ)) f = 0
  let castPoint : (Fin 3 → ℤ) → (Fin 3 → ℚ) := fun w i => (w i : ℚ)
  have hinj : Function.Injective castPoint := by
    intro x y h
    funext i
    have hi : (x i : ℚ) = (y i : ℚ) := congrFun h i
    exact_mod_cast hi
  have hsub : Z.image castPoint ⊆ G.image (fun y => C *ᵥ y) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hvT, hvf⟩ := Finset.mem_filter.mp hv
    obtain ⟨y, hy, hby⟩ := hcoord v hvT
    refine Finset.mem_image.mpr ⟨fun i => (y i : ℚ), ?_, hy⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      apply mem_rationalIntegerInterval
      exact (le_div_iff₀ (hℓ i)).mpr (by simpa [mul_comm] using hby i)
    · change eval (fun i => (y i : ℚ)) (matrixSubstitution C f) = 0
      rw [eval_matrixSubstitution, hy]
      exact hvf
  have hgrid : (G.card : ℝ) ≤ 243 * g.totalDegree * X ^ 2 / L :=
    ternary_polynomial_weighted_grid_count hg hX hL ℓ hℓ hsmall hpair
  calc
    (Z.card : ℝ) = ((Z.image castPoint).card : ℝ) := by
      rw [Finset.card_image_of_injective _ hinj]
    _ ≤ ((G.image (fun y => C *ᵥ y)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ (G.card : ℝ) := by exact_mod_cast Finset.card_image_le
    _ ≤ 243 * g.totalDegree * X ^ 2 / L := hgrid
    _ ≤ 243 * f.totalDegree * X ^ 2 / L := by
      gcongr

end
end PierceLengthBound.FixedDividend
