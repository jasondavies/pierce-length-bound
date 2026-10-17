import PierceBound.Functional
import PierceBound.Hadamard

/-!
# The label bound `Iᵣ(i) ≤ a ∏ⱼ μᵢ(Fⱼ²) / qᵢʳ`

The Hankel matrix of `νᵢ` becomes the Gram matrix `(νᵢ(Fⱼ Fₗ))` of the Newton basis after a
unit lower triangular change of basis. Hadamard's inequality bounds its determinant by
`∏ⱼ νᵢ(Fⱼ²) ≤ ∏ⱼ μᵢ(Fⱼ²)/qᵢ`. For `r = 4` the right side is an explicit polynomial in the
increments (`gramP`), and `I₄(i)` is the six-step integer `L` (`hankelInv_four`), so
`L qᵢ⁴ ≤ a · gramP` in `ℤ` (`label_bound`).
-/

namespace PierceBound

open Finset Polynomial Matrix

variable {a b : ℕ}

lemma nb_monic (i j : ℕ) : (nb a b i j).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma nb_natDegree (i j : ℕ) : (nb a b i j).natDegree = j := by
  unfold nb
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

/-- The coefficient matrix of the Newton basis. -/
noncomputable def nbMat (a b i r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun j t => (nb a b i j).coeff t

lemma nb_expand (i r : ℕ) (j : Fin r) :
    nb a b i j = ∑ t : Fin r, C (nbMat a b i r j t) * X ^ (t : ℕ) := by
  conv_lhs => rw [as_sum_range' (nb a b i j) r (by rw [nb_natDegree]; exact j.2)]
  rw [← Fin.sum_univ_eq_sum_range (fun t => monomial t ((nb a b i j).coeff t)) r]
  refine sum_congr rfl fun t _ => ?_
  rw [← C_mul_X_pow_eq_monomial]; rfl

lemma nbMat_det (i r : ℕ) : (nbMat a b i r).det = 1 := by
  rw [det_of_isLowerTriangular]
  · refine prod_eq_one fun j _ => ?_
    simp only [nbMat, of_apply]
    have := (nb_monic (a := a) (b := b) i j).coeff_natDegree
    rwa [nb_natDegree] at this
  · intro j t hjt
    simp only [nbMat, of_apply]
    exact coeff_eq_zero_of_natDegree_lt (by rw [nb_natDegree]; exact hjt)

/-- The Newton-basis Gram matrix is `U H Uᵀ`. -/
lemma gram_eq (i r : ℕ) (j l : Fin r) :
    nuF a b i (nb a b i j * nb a b i l) =
      (nbMat a b i r * hankel a b i r * (nbMat a b i r)ᵀ) j l := by
  rw [nb_expand i r j, nb_expand i r l, sum_mul_sum, nuF_sum]
  simp only [nuF_sum, mul_apply, transpose_apply, hankel, of_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t' _ => sum_congr rfl fun t _ => ?_
  rw [show C (nbMat a b i r j t) * X ^ (t : ℕ) * (C (nbMat a b i r l t') * X ^ (t' : ℕ)) =
    C (nbMat a b i r j t * nbMat a b i r l t') * X ^ ((t : ℕ) + t') by
      rw [map_mul, pow_add]; ring, nuF_C_mul, nuF_X_pow]
  ring

/-- **The Gram comparison.** `Iᵣ(i) ≤ a ∏ⱼ μᵢ(Fⱼ²)/qᵢ`. -/
theorem hankelInv_le_prod (hba : b < a) {i r : ℕ} (hi : i < P a b) (hr : r ≤ P a b - i) :
    hankelInv a b i r ≤ a * ∏ j : Fin r, (muF a b i (nb a b i j * nb a b i j) / qq a b i) := by
  set U := nbMat a b i r
  set H := hankel a b i r
  have hU : U.det = 1 := nbMat_det i r
  have hinj : Function.Injective (Uᵀ).mulVec := by
    rw [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det, det_transpose, hU]
    exact isUnit_one
  have hPD : (U * H * Uᵀ).PosDef := by
    have := (hankel_posDef hba hi hr).conjTranspose_mul_mul_same hinj
    rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
  have hdet : (U * H * Uᵀ).det = H.det := by
    rw [det_mul, det_mul, det_transpose, hU]; ring
  have hha := det_le_prod_diag hPD
  rw [hdet] at hha
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  unfold hankelInv
  refine mul_le_mul_of_nonneg_left (hha.trans ?_) ha
  refine Finset.prod_le_prod₀ (fun j _ => ?_) fun j _ => ?_
  · rw [← gram_eq]; exact nuF_sq_nonneg hba hi _
  · rw [← gram_eq]; exact nuF_sq_le hba hi _

/-! ### The rank-four case -/

/-- `∏_{j<4} μᵢ(Fⱼ²)` as a polynomial in the increments `k₀, …, k₄`. -/
def gramP (k0 k1 k2 k3 k4 : ℤ) : ℤ :=
  (k0 + 1) * ((k0 + k1) * k1 + (k0 + 2 * k1) + k2 + 1) *
    ((k0 + k1 + k2) * (k1 + k2) * k2 +
      ((k0 + k1 + k2) * (k1 + k2) + (k0 + k1 + k2) * k2 + (k1 + k2) * k2) +
      (3 * (k0 + k1 + k2) - k0 - (k0 + k1)) * (k3 + 1) + (k3 ^ 2 + 2 * k3 + k4 + 1))

lemma pt_eq_sum (i : ℕ) : ∀ j, pt a b i j = ∑ m ∈ range j, kk a b (i + m)
  | 0 => by simp [pt]
  | j + 1 => by
    rw [sum_range_succ, ← pt_eq_sum i j]
    simp [pt, kk, ← add_assoc]

lemma muF_nb_sq (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    ∏ j : Fin 4, muF a b i (nb a b i j * nb a b i j) =
      ((gramP ((qq a b (i + 1) : ℤ) - qq a b i) ((qq a b (i + 2) : ℤ) - qq a b (i + 1))
        ((qq a b (i + 3) : ℤ) - qq a b (i + 2)) ((qq a b (i + 4) : ℤ) - qq a b (i + 3))
        ((qq a b (i + 5) : ℤ) - qq a b (i + 4)) : ℤ) : ℝ) := by
  have p1 : pt a b i 1 = kk a b i := by rw [pt_eq_sum]; simp
  have p2 : pt a b i 2 = kk a b i + kk a b (i + 1) := by rw [pt_eq_sum]; simp [sum_range_succ]
  have p3 : pt a b i 3 = kk a b i + kk a b (i + 1) + kk a b (i + 2) := by
    rw [pt_eq_sum]; simp [sum_range_succ]
  have e : ∀ j : ℕ, j < 4 → muF a b i (nb a b i j * nb a b i j) =
      muF a b (i + j) ((nb a b i j).comp (X + C (pt a b i j))) := fun j hj =>
    muF_nb_mul j i (by omega) _
  rw [Fin.prod_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
  simp only [nb, prod_range_succ, prod_range_zero, one_mul, mul_comp, sub_comp, X_comp, C_comp,
    one_comp, pt_zero, map_zero, sub_zero, add_zero]
  rw [muF_one hba (by omega), p1, p2, p3]
  -- expand the products
  rw [show (X + C (kk a b i)) = X + C (kk a b i) * 1 by ring, muF_add, muF_C_mul,
    muF_X hba (by omega), muF_one hba (by omega)]
  have h2 : (X + C (kk a b i + kk a b (i + 1))) * (X + C (kk a b i + kk a b (i + 1)) - C (kk a b i)) =
      X ^ 2 + C (2 * kk a b (i + 1) + kk a b i) * X +
        C ((kk a b i + kk a b (i + 1)) * kk a b (i + 1)) * 1 := by
    simp only [map_add, map_mul, map_ofNat, map_one]; ring
  have h3 : (X + C (kk a b i + kk a b (i + 1) + kk a b (i + 2))) *
      (X + C (kk a b i + kk a b (i + 1) + kk a b (i + 2)) - C (kk a b i)) *
      (X + C (kk a b i + kk a b (i + 1) + kk a b (i + 2)) - C (kk a b i + kk a b (i + 1))) =
      X ^ 3 + C (3 * (kk a b i + kk a b (i + 1) + kk a b (i + 2)) - kk a b i -
        (kk a b i + kk a b (i + 1))) * X ^ 2 +
        C ((kk a b i + kk a b (i + 1) + kk a b (i + 2)) * (kk a b (i + 1) + kk a b (i + 2)) +
          (kk a b i + kk a b (i + 1) + kk a b (i + 2)) * kk a b (i + 2) +
          (kk a b (i + 1) + kk a b (i + 2)) * kk a b (i + 2)) * X +
        C ((kk a b i + kk a b (i + 1) + kk a b (i + 2)) * (kk a b (i + 1) + kk a b (i + 2)) *
          kk a b (i + 2)) * 1 := by
    simp only [map_add, map_mul, map_ofNat, map_one, map_sub]; ring
  rw [h2, h3]
  simp only [muF_add, muF_C_mul]
  rw [muF_X_sq hba (by omega), muF_X hba (by omega), muF_one hba (by omega),
    muF_X_cube hba (by omega), muF_X_sq hba (by omega), muF_X hba (by omega),
    muF_one hba (by omega)]
  unfold gramP
  push_cast
  simp only [kk, show i + 3 + 1 = i + 4 from rfl, show i + 4 + 1 = i + 5 from rfl,
    show i + 2 + 1 = i + 3 from rfl, show i + 1 + 1 = i + 2 from rfl]
  ring

/-- **The label bound.** `L qᵢ⁴ ≤ a · gramP(k₀, …, k₄)`, where `L = I₄(i)` is the six-step
integer. -/
theorem label_bound (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    sixL ((qq a b (i + 1) : ℤ) - qq a b i) ((qq a b (i + 2) : ℤ) - qq a b (i + 1))
      ((qq a b (i + 3) : ℤ) - qq a b (i + 2)) ((qq a b (i + 4) : ℤ) - qq a b (i + 3))
      ((orb a b i : ℤ) - orb a b (i + 1)) ((orb a b (i + 1) : ℤ) - orb a b (i + 2))
      ((orb a b (i + 2) : ℤ) - orb a b (i + 3)) * (qq a b i : ℤ) ^ 4 ≤
    a * gramP ((qq a b (i + 1) : ℤ) - qq a b i) ((qq a b (i + 2) : ℤ) - qq a b (i + 1))
        ((qq a b (i + 3) : ℤ) - qq a b (i + 2)) ((qq a b (i + 4) : ℤ) - qq a b (i + 3))
        ((qq a b (i + 5) : ℤ) - qq a b (i + 4)) := by
  have h := hankelInv_le_prod hba (i := i) (r := 4) (by omega) (by omega)
  rw [hankelInv_four hba (by omega), prod_div_distrib, muF_nb_sq hba hi] at h
  simp only [prod_const, card_univ, Fintype.card_fin] at h
  have hq : (0 : ℝ) < (qq a b i : ℝ) ^ 4 := by
    have : (0 : ℝ) < qq a b i := by exact_mod_cast qq_pos hba (by omega)
    positivity
  rw [mul_div_assoc', le_div_iff₀ hq] at h
  exact_mod_cast h

end PierceBound
