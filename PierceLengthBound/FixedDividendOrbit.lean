/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividend

/-!
# The orthogonal quartic attached to an actual orbit window

The coefficients here are the normalized integer cofactors of the orbit matrix.
Thus the orthogonality statements below have only orbit support hypotheses.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open Finset Polynomial Matrix

variable {a b : ℕ}

noncomputable def orbitCoeffs (a b i : ℕ) : Fin 5 → ℝ :=
  coeffs ((Lz a b (i + 1) : ℝ) / Lz a b i)
    ((U1z a b i : ℝ) / Lz a b i) ((U2z a b i : ℝ) / Lz a b i)

noncomputable def orbitQuartic (a b i : ℕ) : ℝ[X] :=
  newtonQuartic a b i (orbitCoeffs a b i)

lemma orbit_label_ne_zero (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    (Lz a b i : ℝ) ≠ 0 := by
  have h := Lz_pos hba hi
  have : (1 : ℝ) ≤ Lz a b i := by exact_mod_cast h
  linarith

lemma orbitCoeffs_sum (i : ℕ) : ∑ j, orbitCoeffs a b i j = 0 := coeffs_sum _ _ _

lemma orbitCoeffs_last (i : ℕ) : orbitCoeffs a b i 4 = 1 := rfl

/-- Summation by parts for the five Newton coefficients. -/
lemma coeffs_sum_mul (ρ u v : ℝ) (f : Fin 5 → ℝ) :
    ∑ j, coeffs ρ u v j * f j =
      -ρ * (f 1 - f 0) + u * (f 2 - f 1) + v * (f 3 - f 2) + (f 4 - f 3) := by
  simp [coeffs, Fin.sum_univ_succ]
  ring

lemma orbitCoeffs_first_moment (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    ∑ j : Fin 5, orbitCoeffs a b i j * pt a b i j = 0 := by
  have hL := orbit_label_ne_zero hba hi
  have he : -(Lz a b (i + 1) : ℝ) * (kq a b i : ℝ) +
      (U1z a b i : ℝ) * (kq a b (i + 1) : ℝ) +
      (U2z a b i : ℝ) * (kq a b (i + 2) : ℝ) +
      (Lz a b i : ℝ) * (kq a b (i + 3) : ℝ) = 0 := by exact_mod_cast e0_at (a := a) (b := b) i
  simp only [orbitCoeffs, coeffs_sum_mul, pt, kq, Nat.add_assoc] at he ⊢
  push_cast at he
  field_simp
  linear_combination he

lemma orbitCoeffs_second_moment (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    ∑ j : Fin 5, orbitCoeffs a b i j * (pt a b i j ^ 2 + kk a b (i + j)) = 0 := by
  have hL := orbit_label_ne_zero hba hi
  have he := e3_at (a := a) (b := b) i
  have he' : -(Lz a b (i + 1) : ℝ) * ((kq a b i : ℝ) ^ 2 + kq a b (i + 1)) +
      (U1z a b i : ℝ) * ((kq a b (i + 1) : ℝ) * (2 * kq a b i + kq a b (i + 1)) + kq a b (i + 2)) +
      (U2z a b i : ℝ) * ((kq a b (i + 2) : ℝ) *
        (2 * kq a b i + 2 * kq a b (i + 1) + kq a b (i + 2)) + kq a b (i + 3)) +
      (Lz a b i : ℝ) * ((kq a b (i + 3) : ℝ) *
        (2 * kq a b i + 2 * kq a b (i + 1) + 2 * kq a b (i + 2) + kq a b (i + 3)) +
          kq a b (i + 4)) = 0 := by exact_mod_cast he
  simp only [orbitCoeffs, coeffs_sum_mul, pt, kk, kq, Nat.add_assoc] at he' ⊢
  have hk : -(Lz a b (i + 1) : ℝ) * (kq a b i : ℝ) +
      (U1z a b i : ℝ) * (kq a b (i + 1) : ℝ) +
      (U2z a b i : ℝ) * (kq a b (i + 2) : ℝ) +
      (Lz a b i : ℝ) * (kq a b (i + 3) : ℝ) = 0 := by exact_mod_cast e0_at (a := a) (b := b) i
  simp only [kq] at hk
  push_cast at he' hk
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.reduceAdd, Nat.add_zero,
    Nat.add_assoc] at *
  field_simp
  linear_combination he' - hk

lemma orbitCoeffs_weighted_moment (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    ∑ j : Fin 5, orbitCoeffs a b i j * ((orb a b (i + j) : ℝ) / a) = 0 := by
  have hL := orbit_label_ne_zero hba hi
  have he : -Lz a b (i + 1) * dq a b i + U1z a b i * dq a b (i + 1) +
      U2z a b i * dq a b (i + 2) + Lz a b i * dq a b (i + 3) = 0 :=
    null_d _ _ _ _ _ _ _ _ _
  have he' : -(Lz a b (i + 1) : ℝ) * (dq a b i : ℝ) +
      (U1z a b i : ℝ) * (dq a b (i + 1) : ℝ) +
      (U2z a b i : ℝ) * (dq a b (i + 2) : ℝ) +
      (Lz a b i : ℝ) * (dq a b (i + 3) : ℝ) = 0 := by exact_mod_cast he
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  simp only [orbitCoeffs, coeffs_sum_mul, dq, Nat.add_assoc] at he' ⊢
  push_cast at he'
  field_simp
  linear_combination -he'

/-- Orthogonality for the actual normalized cofactor polynomial. -/
theorem orbitQuartic_orthogonal (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    ∀ m < 4, nuF a b i (orbitQuartic a b i * X ^ m) = 0 :=
  newtonQuartic_orthogonal hba hi _ (orbitCoeffs_sum i)
    (orbitCoeffs_first_moment hba (by omega))
    (orbitCoeffs_second_moment hba (by omega))
    (orbitCoeffs_weighted_moment hba (by omega))

lemma newtonQuartic_degree_le (i : ℕ) (c : Fin 5 → ℝ) :
    (newtonQuartic a b i c).natDegree ≤ 4 := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le _ _).trans (by rw [nb_natDegree]; omega)

lemma newtonQuartic_coeff_four (i : ℕ) (c : Fin 5 → ℝ) :
    (newtonQuartic a b i c).coeff 4 = c 4 := by
  simp only [newtonQuartic, finsetSum_coeff, coeff_C_mul]
  rw [Finset.sum_eq_single (4 : Fin 5)]
  · have h := (nb_monic (a := a) (b := b) i 4).coeff_natDegree
    rw [nb_natDegree] at h
    change c 4 * (nb a b i 4).coeff 4 = c 4
    rw [h, mul_one]
  · intro j _ hj
    rw [coeff_eq_zero_of_natDegree_lt (by rw [nb_natDegree]; omega), mul_zero]
  · simp

lemma orbitQuartic_monic (i : ℕ) : (orbitQuartic a b i).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 4 (newtonQuartic_degree_le i _)
    (newtonQuartic_coeff_four i _)

lemma orbitQuartic_natDegree (i : ℕ) : (orbitQuartic a b i).natDegree = 4 :=
  natDegree_eq_of_le_of_coeff_ne_zero (newtonQuartic_degree_le i _)
    (by rw [orbitQuartic, newtonQuartic_coeff_four, orbitCoeffs_last]; norm_num)

/-- Orthogonality to monomials extends to every polynomial of smaller degree. -/
lemma nuF_mul_eq_zero_of_orthogonal {i n : ℕ} {p g : ℝ[X]}
    (ho : ∀ m < n, nuF a b i (p * X ^ m) = 0) (hg : g.natDegree < n) :
    nuF a b i (p * g) = 0 := by
  conv_lhs => rw [g.as_sum_range_C_mul_X_pow' hg]
  rw [mul_sum, nuF_sum]
  apply sum_eq_zero
  intro j hj
  rw [show p * (C (g.coeff j) * X ^ j) = C (g.coeff j) * (p * X ^ j) by ring,
    nuF_C_mul, ho j (mem_range.mp hj), mul_zero]

/-- The quartic norm equals its pairing with the leading monomial. -/
lemma orbitQuartic_norm_top (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    nuF a b i (orbitQuartic a b i * orbitQuartic a b i) =
      nuF a b i (orbitQuartic a b i * X ^ 4) := by
  let f := orbitQuartic a b i
  have hdeg : f.natDegree < 5 := by dsimp [f]; rw [orbitQuartic_natDegree]; norm_num
  change nuF a b i (f * f) = _
  conv_lhs => enter [4, 2]; rw [f.as_sum_range_C_mul_X_pow' hdeg]
  rw [mul_sum, nuF_sum, sum_range_succ]
  have hz : ∑ j ∈ range 4, nuF a b i (orbitQuartic a b i * (C (f.coeff j) * X ^ j)) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [show orbitQuartic a b i * (C (f.coeff j) * X ^ j) =
      C (f.coeff j) * (orbitQuartic a b i * X ^ j) by ring,
      nuF_C_mul, orbitQuartic_orthogonal hba hi j (mem_range.mp hj), mul_zero]
  rw [hz, zero_add]
  have hc : f.coeff 4 = 1 := newtonQuartic_coeff_four i _
  rw [hc, map_one, one_mul]

/-- This is the norm polynomial `D` evaluated at an actual orbit window. -/
noncomputable def orbitNorm (a b i : ℕ) : ℝ :=
  ∑ j : Fin 5, orbitCoeffs a b i j *
    (pt a b i j ^ 3 + 3 * pt a b i j ^ 2 + 3 * pt a b i j * (1 + kk a b (i + j)) +
      (1 + kk a b (i + j)) ^ 2 + kk a b (i + j + 1))

/-- The cubic moment expression is the squared norm of the actual quartic. -/
theorem orbitNorm_eq_square (hba : b < a) {i : ℕ} (hi : i + 7 < P a b) :
    orbitNorm a b i = nuF a b i (orbitQuartic a b i * orbitQuartic a b i) := by
  have hm : muF a b i (orbitQuartic a b i * X ^ 3) = orbitNorm a b i := by
    rw [orbitQuartic, muF_newtonQuartic_mul]
    apply sum_congr rfl
    intro j _
    rw [muF_nb_cube_X hba (by have := j.isLt; omega)]
    ring
  have he := nuF_mul_X_add hba i (orbitQuartic a b i * X ^ 3)
  rw [show orbitQuartic a b i * X ^ 3 * X = orbitQuartic a b i * X ^ 4 by ring,
    orbitQuartic_orthogonal hba (by omega) 3 (by norm_num), mul_zero, add_zero, hm] at he
  rw [orbitQuartic_norm_top hba (by omega)]
  exact he.symm

/-- Strict positivity of a polynomial square below the size of the actual support. -/
lemma nuF_square_pos (hba : b < a) {i : ℕ} (hi : i < P a b) {f : ℝ[X]}
    (hf : f ≠ 0) (hd : f.natDegree < P a b - i) : 0 < nuF a b i (f * f) := by
  classical
  obtain ⟨hw, -⟩ := wt_spec hba (P a b - 1 - i) i (by omega)
  have hterm : ∀ j ∈ range (P a b - i),
      0 ≤ wt a b i j * (f.eval (pt a b i j) * f.eval (pt a b i j)) / qq a b (i + j) := by
    intro j hj
    exact div_nonneg (mul_nonneg (hw j (mem_range.mp hj)).le (mul_self_nonneg _))
      (Nat.cast_nonneg _)
  by_contra hn
  have hz : nuF a b i (f * f) = 0 := le_antisymm (le_of_not_gt hn) (nuF_sq_nonneg hba hi f)
  simp only [nuF, eval_mul] at hz
  have hall := (sum_eq_zero_iff_of_nonneg hterm).mp hz
  have hev : ∀ j : Fin (P a b - i), f.eval (pt a b i j) = 0 := by
    intro j
    have he := hall j (mem_range.mpr j.isLt)
    have hq : (qq a b (i + j) : ℝ) ≠ 0 := by
      have := qq_pos hba (i := i + j) (by omega)
      exact_mod_cast (show qq a b (i + j) ≠ 0 by omega)
    have he' := (div_eq_zero_iff.mp he).resolve_right hq
    have he'' := (mul_eq_zero.mp he').resolve_left (hw j j.isLt).ne'
    exact mul_self_eq_zero.mp he''
  have hinj : Function.Injective (fun j : Fin (P a b - i) => pt a b i j) := by
    intro j k he
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact (pt_strictMono h (by omega)).ne he
    · exact (pt_strictMono h (by omega)).ne he.symm
  exact hf (eq_zero_of_natDegree_lt_card_of_eval_eq_zero f hinj hev (by simpa using hd))

/-- In particular the candidate's norm is strictly positive at supported orbit windows. -/
theorem orbitNorm_pos (hba : b < a) {i : ℕ} (hi : i + 7 < P a b) :
    0 < orbitNorm a b i := by
  rw [orbitNorm_eq_square hba hi]
  exact nuF_square_pos hba (by omega) (orbitQuartic_monic i).ne_zero
    (by rw [orbitQuartic_natDegree]; omega)

/-- General coefficient change of basis for the weighted moment matrix. -/
lemma polynomial_gram_eq {i r : ℕ} (f : Fin r → ℝ[X]) (hd : ∀ j, (f j).natDegree < r) :
    (fun j k => nuF a b i (f j * f k)) =
      (Matrix.of fun j k : Fin r => (f j).coeff k) * hankel a b i r *
        (Matrix.of fun j k : Fin r => (f j).coeff k)ᵀ := by
  ext j k
  conv_lhs => rw [(f j).as_sum_range_C_mul_X_pow' (hd j),
    (f k).as_sum_range_C_mul_X_pow' (hd k)]
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range, sum_mul_sum, nuF_sum]
  simp only [nuF_sum, Matrix.mul_apply, Matrix.transpose_apply, hankel, Matrix.of_apply, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro s _
  rw [show C ((f j).coeff s) * X ^ (s : ℕ) * (C ((f k).coeff t) * X ^ (t : ℕ)) =
    C ((f j).coeff s * (f k).coeff t) * X ^ ((s : ℕ) + t) by rw [map_mul, pow_add]; ring,
    nuF_C_mul, nuF_X_pow]
  ring

/-- Appending a monic orthogonal polynomial multiplies the Hankel determinant by its norm. -/
theorem orthogonal_norm_det {i n : ℕ} {p : ℝ[X]} (hp : p.Monic) (hd : p.natDegree = n)
    (ho : ∀ m < n, nuF a b i (p * X ^ m) = 0) :
    (hankel a b i (n + 1)).det = nuF a b i (p * p) * (hankel a b i n).det := by
  classical
  let f : Fin (n + 1) → ℝ[X] := fun j => if (j : ℕ) = n then p else X ^ (j : ℕ)
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun j k => (f j).coeff k
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun j k => nuF a b i (f j * f k)
  have hdeg : ∀ j, (f j).natDegree < n + 1 := by
    intro j
    dsimp [f]
    split_ifs <;> simp only [hd, natDegree_X_pow] <;> omega
  have hdiag : ∀ j, U j j = 1 := by
    intro j
    dsimp [U, f]
    split_ifs with hj
    · rw [hj, ← hd]; exact hp.coeff_natDegree
    · simp
  have htri : ∀ j k, j < k → U j k = 0 := by
    intro j k hjk
    dsimp [U, f]
    rw [ite_eq_right (by have := k.isLt; omega)]
    exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_X_pow]; exact hjk)
  have hU : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular U htri]
    exact prod_eq_one fun j _ => hdiag j
  have hG : G = U * hankel a b i (n + 1) * Uᵀ := polynomial_gram_eq f hdeg
  have hdet : G.det = (hankel a b i (n + 1)).det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hU, one_mul, mul_one]
  rw [← hdet, Matrix.det_succ_row G (Fin.last n), sum_eq_single (Fin.last n)]
  · have hm : G.submatrix (Fin.last n).succAbove (Fin.last n).succAbove = hankel a b i n := by
      ext j k
      change nuF a b i (f ((Fin.last n).succAbove j) * f ((Fin.last n).succAbove k)) = _
      simp only [Fin.succAbove_last_apply, f, Fin.val_castSucc,
        ite_eq_right (by omega : (j : ℕ) ≠ n), ite_eq_right (by omega : (k : ℕ) ≠ n), ← pow_add,
        nuF_X_pow, hankel, Matrix.of_apply]
    rw [hm]
    have hnn : G (Fin.last n) (Fin.last n) = nuF a b i (p * p) := by simp [G, f]
    rw [hnn]
    rw [Fin.val_last, ← two_mul, pow_mul]
    norm_num
  · intro j _ hj
    have hjn : (j : ℕ) < n := by
      have hne : (j : ℕ) ≠ n := by intro he; exact hj (Fin.ext he)
      omega
    have hzero : G (Fin.last n) j = 0 := by
      simpa [G, f, hjn.ne] using ho j hjn
    rw [hzero, mul_zero, zero_mul]
  · simp

/-- The actual rank-five/rank-four Hankel ratio is the cubic norm. -/
theorem orbitNorm_hankel (hba : b < a) {i : ℕ} (hi : i + 7 < P a b) :
    (hankel a b i 5).det = orbitNorm a b i * (hankel a b i 4).det := by
  rw [orthogonal_norm_det (orbitQuartic_monic i) (orbitQuartic_natDegree i)
    (orbitQuartic_orthogonal hba (by omega)), ← orbitNorm_eq_square hba hi]

end PierceLengthBound.FixedDividend
