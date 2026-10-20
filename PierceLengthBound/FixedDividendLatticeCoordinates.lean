/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendLinearCoordinates
public import PierceLengthBound.LatticeCount

/-! Integral reduced-lattice coordinates for the actual three node variables. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Matrix

/-- The first three nonzero cumulative nodes of a five-gap vector. -/
def gapNodes (k : Fin 5 → ℤ) : Fin 3 → ℤ := ![k 0, k 0 + k 1, k 0 + k 1 + k 2]

lemma lift_first_det (M : Fin 3 → Fin 5 → ℤ) (τ : Fin 10) :
    det3 (Lrow (plk M) τ 0) (Lrow (plk M) τ 1) (Lrow (plk M) τ 2) =
      plk M τ ^ 2 * plk M 0 := by
  fin_cases τ <;>
    simp [Lrow, role, det3, plk, trip, minor3, uVec, vVec, puX, puS, pvX, pvS] <;> ring

/-- Lift the first three gaps; cumulative summation gives the node coordinates. -/
def liftFirstM (p : Fin 10 → ℤ) (b1 b2 b3 : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![liftv p b1 0, liftv p b2 0, liftv p b3 0;
     liftv p b1 1, liftv p b2 1, liftv p b3 1;
     liftv p b1 2, liftv p b2 2, liftv p b3 2]

lemma liftFirstM_det_ne {p : Fin 10 → ℤ} {M : Fin 3 → Fin 5 → ℤ} {b1 b2 b3 : Fin 3 → ℤ}
    (hM : plk M = p) (hm : p (piv p) ≠ 0) (h0 : p 0 ≠ 0)
    (h1 : b1 ∈ pivLat p) (h2 : b2 ∈ pivLat p) (h3 : b3 ∈ pivLat p)
    (hD : det3 b1 b2 b3 ≠ 0) : (liftFirstM p b1 b2 b3).det ≠ 0 := by
  let τ := piv p
  have hE : p τ • liftFirstM p b1 b2 b3 = Matrix.of
      ![![dot3 (Lrow p τ 0) b1, dot3 (Lrow p τ 0) b2, dot3 (Lrow p τ 0) b3],
        ![dot3 (Lrow p τ 1) b1, dot3 (Lrow p τ 1) b2, dot3 (Lrow p τ 1) b3],
        ![dot3 (Lrow p τ 2) b1, dot3 (Lrow p τ 2) b2, dot3 (Lrow p τ 2) b3]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [liftFirstM, liftv_spec h1, liftv_spec h2, liftv_spec h3, τ]
  have he := det3_mul (Lrow p τ 0) (Lrow p τ 1) (Lrow p τ 2) b1 b2 b3
  rw [← hE, Matrix.det_smul, Fintype.card_fin] at he
  have hL := lift_first_det M τ
  rw [hM] at hL
  rw [hL] at he
  intro hz
  rw [hz, mul_zero] at he
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hm) h0) hD he.symm

/-- A fixed minor pattern admits injective integral coordinates of radius
`floor(3H/shortR)`, and its cumulative nodes are an invertible integer matrix
applied to those coordinates. -/
theorem lattice_node_coordinates {p : Fin 10 → ℤ} {H : ℕ} {V : Finset (Fin 5 → ℤ)}
    (hV : V.Nonempty) (h0 : p 0 ≠ 0)
    (hVs : ∀ k ∈ V, (∀ j, |k j| ≤ H) ∧
      ∃ M : Fin 3 → Fin 5 → ℤ, plk M = p ∧ ∀ j, M 1 j = k j) :
    ∃ (B : Matrix (Fin 3) (Fin 3) ℤ) (y : (Fin 5 → ℤ) → Fin 3 → ℤ),
      B.det ≠ 0 ∧ Set.InjOn y V ∧
      ∀ k ∈ V, (∀ j, |y k j| ≤ (3 * H / shortR p : ℕ)) ∧ gapNodes k = B *ᵥ y k := by
  classical
  obtain ⟨k0, hk0⟩ := hV
  obtain ⟨_, M, hM, _⟩ := hVs k0 hk0
  have hm : p (piv p) ≠ 0 := by
    intro hz
    have := piv_max p 0
    rw [hz, abs_zero] at this
    exact h0 (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))
  let τ := piv p
  let m := p τ
  have hΛ : ∀ x : Fin 3 → ℤ, (∀ j, ((m.natAbs : ℕ) : ℤ) ∣ x j) → x ∈ pivLat p :=
    fun x h => pivLat_of_dvd fun j => Int.natAbs_dvd.mp (h j)
  obtain ⟨b1, b2, b3, h1, h2, h3, hD, _, hbas, hred⟩ :=
    reduced_basis (Λ := pivLat p) (Int.natAbs_pos.mpr hm) hΛ
  obtain ⟨hR1, _, hRlow⟩ := shortR_spec hm
  have hb10 : b1 ≠ 0 := by intro h; apply hD; rw [h]; simp [det3]
  have hb20 : b2 ≠ 0 := by intro h; apply hD; rw [h]; simp [det3]
  have hb30 : b3 ≠ 0 := by intro h; apply hD; rw [h]; simp [det3]
  have n1 := hRlow b1 h1 hb10
  have n2 := hRlow b2 h2 hb20
  have n3 := hRlow b3 h3 hb30
  let kp := fun k : Fin 5 → ℤ => fun j => k (pcol τ j)
  let yc := fun k : Fin 5 → ℤ => ycoord b1 b2 b3 (kp k)
  have hlift : ∀ k ∈ V, ∀ j, m * k j = dot3 (Lrow p τ j) (kp k) := by
    intro k hk j
    obtain ⟨_, Mk, hMk, hrow⟩ := hVs k hk
    have h := lift_row Mk τ 1 j
    simpa only [hMk, hrow] using h
  have hmem : ∀ k ∈ V, kp k ∈ pivLat p := by
    intro k hk
    refine ⟨⟨k (restc τ 0), ?_⟩, ⟨k (restc τ 1), ?_⟩⟩
    · have h := hlift k hk (restc τ 0)
      rw [Lrow_rest0] at h
      exact h.symm
    · have h := hlift k hk (restc τ 1)
      rw [Lrow_rest1] at h
      exact h.symm
  have hRpos : (0 : ℤ) < shortR p := by exact_mod_cast hR1
  have hcoord : ∀ k ∈ V,
      (∀ j, kp k j = yc k 0 * b1 j + yc k 1 * b2 j + yc k 2 * b3 j) ∧
      ∀ j, (shortR p : ℤ) * |yc k j| ≤ 3 * H := by
    intro k hk
    exact ycoord_spec hD (hbas _ (hmem k hk)) hred hRpos n1 n2 n3
      (fun j => (hVs k hk).1 (pcol τ j))
  have hexp : ∀ k ∈ V, ∀ j, k j = yc k 0 * liftv p b1 j +
      yc k 1 * liftv p b2 j + yc k 2 * liftv p b3 j := by
    intro k hk j
    apply mul_left_cancel₀ hm
    rw [hlift k hk j]
    have hj := (hcoord k hk).1
    have e1 := liftv_spec h1 j
    have e2 := liftv_spec h2 j
    have e3 := liftv_spec h3 j
    simp only [dot3] at e1 e2 e3 ⊢
    rw [hj 0, hj 1, hj 2]
    linear_combination -(yc k 0 * e1 + yc k 1 * e2 + yc k 2 * e3)
  let U : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 1, 1, 0; 1, 1, 1]
  let B := U * liftFirstM p b1 b2 b3
  refine ⟨B, yc, ?_, ?_, ?_⟩
  · have hU : U.det = 1 := by norm_num [U, Matrix.det_fin_three]
    rw [Matrix.det_mul, hU, one_mul]
    exact liftFirstM_det_ne hM hm h0 h1 h2 h3 hD
  · intro k hk k' hk' he
    funext j
    rw [hexp k hk j, hexp k' hk' j, he]
  · intro k hk
    constructor
    · intro j
      have h := (hcoord k hk).2 j
      have hdiv : |yc k j| ≤ (3 * (H : ℤ)) / shortR p :=
        Int.le_ediv_of_mul_le hRpos (by linarith)
      simpa only [Int.natCast_div, Nat.cast_mul, Nat.cast_ofNat] using hdiv
    · have h0 := hexp k hk 0
      have h1 := hexp k hk 1
      have h2 := hexp k hk 2
      change gapNodes k = (U * liftFirstM p b1 b2 b3) *ᵥ yc k
      rw [← Matrix.mulVec_mulVec]
      ext j
      fin_cases j <;> norm_num [gapNodes, U, liftFirstM, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three] <;>
        first | linear_combination h0 | linear_combination h0 + h1 | linear_combination h0 + h1 + h2

end
end PierceLengthBound.FixedDividend
