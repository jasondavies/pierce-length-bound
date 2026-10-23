/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeCount

/-!
# Exterior coordinates in a reduced basis

Let `b₁, b₂, b₃` be a reduced basis of a lattice `Λ ⊆ ℤ³`, and let `x, y ∈ Λ` have
coordinates `ξ, η`. The cross product `x × y` has the integer coordinates `c = ξ × η` in the
basis `b₂ × b₃, b₃ × b₁, b₁ × b₂` (`cross_coords`), and `bᵢ · (x × y) = Δ cᵢ` with
`Δ = det(b₁, b₂, b₃)`. (The paper writes `β_i`, `V`, `ξ, ζ` and `λ` for `bᵢ`, `Δ`, `ξ, η` and
`R`.) Cauchy–Schwarz and the reduction bound `27 |b₁|²|b₂|²|b₃|² ≤ 64 Δ²`
(`reduced_basis`, paper `lem:reduce`) then give `27 R⁴ cᵢ² ≤ 64 |x × y|²` when every
`|bⱼ| ≥ R` (`wcoord_spec`, paper `lem:exterior`). The pattern lattice takes `R = λ = shortR p`,
so the box of the cross product shrinks by the factor `λ²`.
-/

@[expose] public section

namespace PierceLengthBound
open scoped Matrix
open Matrix (vec3_dotProduct)

/-- Cramer's rule in a basis of a lattice: the coordinates `ycoord` are exact. -/
lemma ycoord_repr {b1 b2 b3 x : Fin 3 → ℤ} (hD : det3 b1 b2 b3 ≠ 0)
    (hdvd : det3 b1 b2 b3 ∣ det3 x b2 b3 ∧ det3 b1 b2 b3 ∣ det3 b1 x b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 b2 x) (j : Fin 3) :
    x j = ycoord b1 b2 b3 x 0 * b1 j + ycoord b1 b2 b3 x 1 * b2 j +
      ycoord b1 b2 b3 x 2 * b3 j := by
  obtain ⟨⟨y0, hy0⟩, ⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := hdvd
  have hc := congrFun (cramer b1 b2 b3 x) j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
  simp only [ycoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hy0, hy1, hy2, Int.mul_ediv_cancel_left _ hD]
  apply mul_left_cancel₀ hD
  rw [hc, hy0, hy1, hy2]
  ring

/-- The cross product of two combinations of a basis. -/
lemma cross_coords (b1 b2 b3 ξ η : Fin 3 → ℤ) (j : Fin 3) :
    ((fun a => ξ 0 * b1 a + ξ 1 * b2 a + ξ 2 * b3 a) ⨯₃
        (fun a => η 0 * b1 a + η 1 * b2 a + η 2 * b3 a)) j =
      (ξ ⨯₃ η) 0 * (b2 ⨯₃ b3) j + (ξ ⨯₃ η) 1 * (b3 ⨯₃ b1) j +
        (ξ ⨯₃ η) 2 * (b1 ⨯₃ b2) j := by
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero,
    cross_apply_one, cross_apply_two] <;> ring

/-- The exterior coordinates of `x × y` in the basis `b₂ × b₃, b₃ × b₁, b₁ × b₂`. -/
def wcoord (b1 b2 b3 x y : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ycoord b1 b2 b3 x ⨯₃ ycoord b1 b2 b3 y

/-- **Exterior coordinates in a reduced basis.** Let `x, y` lie in the lattice spanned by
`b₁, b₂, b₃` (`hdx`, `hdy`: Cramer's rule gives integer coordinates), and let every basis vector
have length `≥ R`. Then `x × y = c₀ (b₂ × b₃) + c₁ (b₃ × b₁) + c₂ (b₁ × b₂)` for the integer
coordinates `c = wcoord`, `bᵢ · (x × y) = Δ cᵢ`, and `27 R⁴ cᵢ² ≤ 64 |x × y|²`. -/
theorem wcoord_spec {b1 b2 b3 x y : Fin 3 → ℤ} {R : ℕ} (hD : det3 b1 b2 b3 ≠ 0)
    (hdx : det3 b1 b2 b3 ∣ det3 x b2 b3 ∧ det3 b1 b2 b3 ∣ det3 b1 x b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 b2 x)
    (hdy : det3 b1 b2 b3 ∣ det3 y b2 b3 ∧ det3 b1 b2 b3 ∣ det3 b1 y b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 b2 y)
    (hred : 27 * (nrm3 b1 * nrm3 b2 * nrm3 b3) ≤ 64 * det3 b1 b2 b3 ^ 2) (hR : (0 : ℤ) < R)
    (n1 : (R : ℤ) ^ 2 ≤ nrm3 b1) (n2 : (R : ℤ) ^ 2 ≤ nrm3 b2) (n3 : (R : ℤ) ^ 2 ≤ nrm3 b3) :
    (∀ j, (x ⨯₃ y) j = wcoord b1 b2 b3 x y 0 * (b2 ⨯₃ b3) j +
      wcoord b1 b2 b3 x y 1 * (b3 ⨯₃ b1) j + wcoord b1 b2 b3 x y 2 * (b1 ⨯₃ b2) j) ∧
    (b1 ⬝ᵥ (x ⨯₃ y) = det3 b1 b2 b3 * wcoord b1 b2 b3 x y 0 ∧
      b2 ⬝ᵥ (x ⨯₃ y) = det3 b1 b2 b3 * wcoord b1 b2 b3 x y 1 ∧
      b3 ⬝ᵥ (x ⨯₃ y) = det3 b1 b2 b3 * wcoord b1 b2 b3 x y 2) ∧
    ∀ i, 27 * ((R : ℤ) ^ 4 * wcoord b1 b2 b3 x y i ^ 2) ≤ 64 * nrm3 (x ⨯₃ y) := by
  set D := det3 b1 b2 b3 with hDdef
  set c := wcoord b1 b2 b3 x y
  have hxy : x ⨯₃ y = fun j => c 0 * (b2 ⨯₃ b3) j + c 1 * (b3 ⨯₃ b1) j +
      c 2 * (b1 ⨯₃ b2) j := by
    have ex : x = fun a => ycoord b1 b2 b3 x 0 * b1 a + ycoord b1 b2 b3 x 1 * b2 a +
        ycoord b1 b2 b3 x 2 * b3 a := funext (ycoord_repr hD hdx)
    have ey : y = fun a => ycoord b1 b2 b3 y 0 * b1 a + ycoord b1 b2 b3 y 1 * b2 a +
        ycoord b1 b2 b3 y 2 * b3 a := funext (ycoord_repr hD hdy)
    funext j
    conv_lhs => rw [ex, ey]
    exact cross_coords b1 b2 b3 _ _ j
  have hdot : b1 ⬝ᵥ (x ⨯₃ y) = D * c 0 ∧ b2 ⬝ᵥ (x ⨯₃ y) = D * c 1 ∧
      b3 ⬝ᵥ (x ⨯₃ y) = D * c 2 := by
    rw [hxy, hDdef]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [vec3_dotProduct, det3_apply, cross_apply_zero, cross_apply_one,
        cross_apply_two] <;> ring
  refine ⟨fun j => congrFun hxy j, hdot, fun i => ?_⟩
  set w := x ⨯₃ y
  have hn1 : 0 < nrm3 b1 := lt_of_lt_of_le (by positivity) n1
  have hn2 : 0 < nrm3 b2 := lt_of_lt_of_le (by positivity) n2
  have hn3 : 0 < nrm3 b3 := lt_of_lt_of_le (by positivity) n3
  have hw := nrm3_nonneg w
  have hR4 (u v : ℤ) (hu : (R : ℤ) ^ 2 ≤ u) (hv : (R : ℤ) ^ 2 ≤ v) : (R : ℤ) ^ 4 ≤ u * v := by
    have : (R : ℤ) ^ 2 * (R : ℤ) ^ 2 ≤ u * v :=
      mul_le_mul hu hv (by positivity) (le_trans (by positivity) hu)
    linarith [show (R : ℤ) ^ 4 = (R : ℤ) ^ 2 * (R : ℤ) ^ 2 by ring]
  -- `27 nⱼ nₖ cᵢ² ≤ 64 |w|²`, after cancelling `nᵢ`
  have key (nb nj nk ci : ℤ) (hnb : 0 < nb) (hdi : (D * ci) ^ 2 ≤ nb * nrm3 w)
      (hred' : 27 * (nb * nj * nk) ≤ 64 * D ^ 2) (hj : (R : ℤ) ^ 2 ≤ nj)
      (hk : (R : ℤ) ^ 2 ≤ nk) : 27 * ((R : ℤ) ^ 4 * ci ^ 2) ≤ 64 * nrm3 w := by
    have h1 : nb * (27 * (nj * nk * ci ^ 2)) ≤ nb * (64 * nrm3 w) := by
      have : 27 * (nb * nj * nk) * ci ^ 2 ≤ 64 * D ^ 2 * ci ^ 2 :=
        mul_le_mul_of_nonneg_right hred' (sq_nonneg _)
      nlinarith
    have h2 := le_of_mul_le_mul_left h1 hnb
    have h3 : (R : ℤ) ^ 4 * ci ^ 2 ≤ nj * nk * ci ^ 2 :=
      mul_le_mul_of_nonneg_right (hR4 nj nk hj hk) (sq_nonneg _)
    linarith
  obtain ⟨d1, d2, d3⟩ := hdot
  fin_cases i
  · exact key _ _ _ _ hn1 (d1 ▸ dotProduct_sq_le b1 w) hred n2 n3
  · exact key _ (nrm3 b1) (nrm3 b3) _ hn2 (d2 ▸ dotProduct_sq_le b2 w)
      (by linarith [show nrm3 b2 * nrm3 b1 * nrm3 b3 = nrm3 b1 * nrm3 b2 * nrm3 b3 by ring]) n1 n3
  · exact key _ (nrm3 b1) (nrm3 b2) _ hn3 (d3 ▸ dotProduct_sq_le b3 w)
      (by linarith [show nrm3 b3 * nrm3 b1 * nrm3 b2 = nrm3 b1 * nrm3 b2 * nrm3 b3 by ring]) n1 n2

/-- **The sup-norm form.** If `27 R⁴ cᵢ² ≤ 64 |w|²` (the last part of `wcoord_spec`, with
`w = x × y`) and every entry of `w` is at most `S`, then `3 R² |cᵢ| ≤ 8 S`. -/
theorem wcoord_bound {c w : Fin 3 → ℤ} {R S : ℕ}
    (hc : ∀ i, 27 * ((R : ℤ) ^ 4 * c i ^ 2) ≤ 64 * nrm3 w) (hS : ∀ a, |w a| ≤ S) (i : Fin 3) :
    3 * (R : ℤ) ^ 2 * |c i| ≤ 8 * S := by
  have h := hc i
  have hw := nrm3_le_of_abs_le hS
  have hsq : (3 * (R : ℤ) ^ 2 * |c i|) ^ 2 ≤ (8 * (S : ℤ)) ^ 2 := by
    have : (3 * (R : ℤ) ^ 2 * |c i|) ^ 2 = 9 * ((R : ℤ) ^ 4 * c i ^ 2) := by
      rw [mul_pow, sq_abs]; ring
    nlinarith
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

/-! ### Cofactor rows -/

/-- The matrix of cofactor rows `l₁ × l₂, l₂ × l₀, l₀ × l₁`. -/
def cofRows (l0 l1 l2 : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![l1 ⨯₃ l2, l2 ⨯₃ l0, l0 ⨯₃ l1]

/-- `det Cof(L) = det(L)²`. -/
lemma cofRows_det (l0 l1 l2 : Fin 3 → ℤ) : (cofRows l0 l1 l2).det = det3 l0 l1 l2 ^ 2 := by
  rw [Matrix.det_fin_three]
  simp only [cofRows, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    cross_apply_zero, cross_apply_one, cross_apply_two, det3_apply]
  ring

end PierceLengthBound
