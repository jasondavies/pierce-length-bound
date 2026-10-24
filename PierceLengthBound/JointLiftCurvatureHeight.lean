/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftAlgebra
public import PierceLengthBound.JointLiftExponent
public import PierceLengthBound.FixedDividendWindow

/-! First-order reciprocal expansion for the uniform curvature-minor height. The height of the
minors among the first `c` columns (`orbit_curvature_minor_height`) serves the joint lift
(`c = 3`, constant `68`) and the exterior lattice coordinates (`c = 5`, constant `148`), and
`le_cubic_height_div` turns either into a selected box. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Polynomial

/-- Positive remainder in the first-order reciprocal expansion. -/
def curvatureError (a b m : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ range (P a b - m), wt a b m j * ((qq a b m - q) + pt a b m j) ^ 2 /
    (q ^ 2 * (q + ((qq a b m - q) + pt a b m j)))

/-- For `0 < q ≤ q_m`, `b_m / a = 1/q - (1 + (q_m - q))/q² + ε` with
`0 ≤ ε ≤ μ_m((x + q_m - q)²) / q³` (the expansion in the proof of Lemma 8.8). -/
theorem curvature_reciprocal_expansion {a b m : ℕ} (hba : b < a)
    (hm : m + 2 < P a b) {q : ℝ} (hq : 0 < q) (hqm : q ≤ qq a b m) :
    0 ≤ curvatureError a b m q ∧
      curvatureError a b m q ≤ muF a b m ((X + C ((qq a b m : ℝ) - q)) ^ 2) / q ^ 3 ∧
      (orb a b m : ℝ) / a = 1 / q - (1 + ((qq a b m : ℝ) - q)) / q ^ 2 +
        curvatureError a b m q := by
  obtain ⟨hw, -⟩ := wt_spec hba (P a b - 1 - m) m (by omega)
  set s : ℝ := (qq a b m : ℝ) - q with hs
  have hs0 : 0 ≤ s := by simp only [hs]; linarith
  have hy : ∀ j ∈ range (P a b - m), 0 ≤ s + pt a b m j := fun j hj => by
    have := pt_ge (a := a) (b := b) (i := m) (j := j) (by have := mem_range.mp hj; omega)
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  refine ⟨sum_nonneg fun j hj => ?_, ?_, ?_⟩
  · have := hw j (mem_range.mp hj)
    have := hy j hj
    positivity
  · rw [show muF a b m ((X + C s) ^ 2) = ∑ j ∈ range (P a b - m),
      wt a b m j * (s + pt a b m j) ^ 2 by
        unfold muF; refine sum_congr rfl fun j _ => ?_
        simp only [eval_pow, eval_add, eval_X, eval_C]; ring, sum_div]
    refine sum_le_sum fun j hj => ?_
    have h1 := hw j (mem_range.mp hj)
    have h2 := hy j hj
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ h1.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (s + pt a b m j) ^ 2 * q ^ 3 ≤ (s + pt a b m j) ^ 2
        * (q ^ 2 * (q + (s + pt a b m j))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [pow_pos hq 2]
    linarith
  · have hnu : (orb a b m : ℝ) / a = nuF a b m 1 := (nuF_one hba (by omega)).symm
    have hterm : ∀ j ∈ range (P a b - m), wt a b m j * (1 : ℝ[X]).eval (pt a b m j) /
        qq a b (m + j) = wt a b m j * (1 / q - (s + pt a b m j) / q ^ 2) +
        wt a b m j * (s + pt a b m j) ^ 2 / (q ^ 2 * (q + (s + pt a b m j))) := by
      intro j hj
      have hqq : (qq a b (m + j) : ℝ) = q + (s + pt a b m j) := by
        rw [qq_eq_add_pt]; simp only [hs]; ring
      have hpos : 0 < q + (s + pt a b m j) := by have := hy j hj; linarith
      rw [eval_one, hqq]
      field_simp
      ring
    have hmom : ∑ j ∈ range (P a b - m), wt a b m j * (1 / q - (s + pt a b m j) / q ^ 2) =
        1 / q * muF a b m 1 - 1 / q ^ 2 * muF a b m (X + C s) := by
      unfold muF
      simp only [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      simp only [eval_add, eval_X, eval_C, eval_one]; ring
    rw [hnu]
    unfold nuF
    rw [sum_congr rfl hterm, sum_add_distrib, hmom, muF_one hba (by omega),
      muF_add, muF_X hba (by omega), muF_C, muF_one hba (by omega)]
    unfold curvatureError
    simp only [hs]
    ring

/-- Uniform error at a shifted start whose quotient exceeds `q` by at most `r H`. With `r = 3`
the constant is `17`, and with `r = 5` it is `37`. -/
theorem curvature_error_le {a b m : ℕ} (hba : b < a) (hm : m + 2 < P a b)
    {q H r : ℝ} (hq : 0 < q) (hH : 1 ≤ H) (hr : 0 ≤ r) (hqm : q ≤ qq a b m)
    (hs : (qq a b m : ℝ) - q ≤ r * H) (hk : kk a b m ≤ H) :
    curvatureError a b m q ≤ (r ^ 2 + 2 * r + 2) * H ^ 2 / q ^ 3 := by
  have h := (curvature_reciprocal_expansion hba hm hq hqm).2.1
  rw [muF_shift_sq hba hm] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs0 : 0 ≤ (qq a b m : ℝ) - q := by linarith
  have hsq : ((qq a b m : ℝ) - q) ^ 2 ≤ (r * H) ^ 2 := by gcongr
  nlinarith [sq_nonneg (H - 1), mul_nonneg hr (sq_nonneg (H - 1))]

/-- A drop differs from `a k / q²` by twice the error of `curvature_error_le`. -/
lemma curvature_drop_error {a b m : ℕ} (hba : b < a) (hm : m + 3 < P a b)
    {q H r : ℝ} (hq : 0 < q) (hH : 1 ≤ H) (hr : 0 ≤ r) (hqm : q ≤ qq a b m)
    (hs0 : (qq a b m : ℝ) - q ≤ r * H)
    (hs1 : (qq a b (m + 1) : ℝ) - q ≤ r * H)
    (hk0 : kk a b m ≤ H) (hk1 : kk a b (m + 1) ≤ H) :
    |(dq a b m : ℝ) - (a : ℝ) / q ^ 2 * kk a b m| ≤
      2 * (r ^ 2 + 2 * r + 2) * a * H ^ 2 / q ^ 3 := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hqm1 : q ≤ qq a b (m + 1) := hqm.trans (by
    exact_mod_cast (qq_le_of_le (a := a) (b := b) (by omega : m ≤ m + 1) (by omega)))
  have h0 := curvature_reciprocal_expansion hba (by omega : m + 2 < P a b) hq hqm
  have h1 := curvature_reciprocal_expansion hba (by omega : m + 1 + 2 < P a b) hq hqm1
  have hb0 := curvature_error_le hba (by omega : m + 2 < P a b) hq hH hr hqm hs0 hk0
  have hb1 := curvature_error_le hba (by omega : m + 1 + 2 < P a b) hq hH hr hqm1 hs1 hk1
  have he0 := (div_eq_iff ha.ne').mp h0.2.2
  have he1 := (div_eq_iff ha.ne').mp h1.2.2
  have he : (dq a b m : ℝ) - (a : ℝ) / q ^ 2 * kk a b m =
      a * (curvatureError a b m q - curvatureError a b (m + 1) q) := by
    simp only [dq, Int.cast_sub, Int.cast_natCast, kk]
    rw [he0, he1]
    ring
  rw [he, abs_mul, abs_of_pos ha]
  calc (a : ℝ) * |curvatureError a b m q - curvatureError a b (m + 1) q| ≤
      a * (|curvatureError a b m q| + |curvatureError a b (m + 1) q|) := by
        gcongr
        exact abs_sub _ _
    _ = a * (curvatureError a b m q + curvatureError a b (m + 1) q) := by
      rw [abs_of_nonneg h0.1, abs_of_nonneg h1.1]
    _ ≤ a * ((r ^ 2 + 2 * r + 2) * H ^ 2 / q ^ 3 + (r ^ 2 + 2 * r + 2) * H ^ 2 / q ^ 3) := by
      gcongr
    _ = _ := by ring

/-- The curvature minors among the first `c` columns have a uniform cubic height, without
division by any gap; `c + 1` later gaps are used. The joint lift takes `c = 3` (constant `68`)
and the lattice coordinates take `c = 5` (constant `148`). -/
theorem orbit_curvature_minor_height (c : ℕ) {a b i H j l : ℕ}
    (hba : b < a) (hi : i + c + 3 < P a b) (hH : 1 ≤ H)
    (hk : ∀ t < c + 1, kq a b (i + t) ≤ H) (hj : j < c) (hl : l < c) :
    |(dq a b (i + j) : ℝ) * kq a b (i + l) - dq a b (i + l) * kq a b (i + j)| ≤
      4 * ((c : ℝ) ^ 2 + 2 * c + 2) * a * (H : ℝ) ^ 3 / (qq a b i : ℝ) ^ 3 := by
  have hq : (0 : ℝ) < qq a b i := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (qq_pos hba (by omega))
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hkr (t : ℕ) (ht : t < c + 1) : kk a b (i + t) ≤ H := by
    have h := hk t ht
    have h' : (kq a b (i + t) : ℝ) ≤ H := by exact_mod_cast h
    simpa only [kk, kq, Int.cast_sub, Int.cast_natCast] using h'
  have hqr (t : ℕ) (ht : t < c + 1) : (qq a b i : ℝ) ≤ qq a b (i + t) := by
    exact_mod_cast (qq_le_of_le (by omega : i ≤ i + t) (by omega : i + t < P a b))
  have hs (t : ℕ) (ht : t < c + 1) : (qq a b (i + t) : ℝ) - qq a b i ≤ c * H := by
    rw [qq_eq_add_pt, add_sub_cancel_right, pt_eq_sum]
    calc (∑ m ∈ range t, kk a b (i + m)) ≤ ∑ _m ∈ range t, (H : ℝ) := by
          exact sum_le_sum (fun m hm => hkr m (by have := mem_range.mp hm; omega))
      _ = (t : ℝ) * H := by simp
      _ ≤ c * H := by gcongr; exact_mod_cast (show t ≤ c by omega)
  have hd (t : ℕ) (ht : t < c) :
      |(dq a b (i + t) : ℝ) - (a : ℝ) / (qq a b i : ℝ)^2 * (kq a b (i + t) : ℝ)| ≤
        2 * ((c : ℝ) ^ 2 + 2 * c + 2) * a * (H : ℝ)^2 / (qq a b i : ℝ)^3 := by
    have h := curvature_drop_error hba (by omega : i + t + 3 < P a b) hq hHR (Nat.cast_nonneg c)
      (hqr t (by omega)) (hs t (by omega))
      (by simpa only [Nat.add_assoc] using hs (t + 1) (by omega))
      (hkr t (by omega)) (by simpa only [Nat.add_assoc] using hkr (t + 1) (by omega))
    simpa only [kk, kq, Int.cast_sub, Int.cast_natCast] using h
  have hab (t : ℕ) (ht : t < c) : |(kq a b (i + t) : ℝ)| ≤ H := by
    have hp : (0 : ℝ) ≤ kq a b (i + t) := by
      exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) (kq_pos (by omega : i + t + 1 < P a b)))
    rw [abs_of_nonneg hp]
    exact_mod_cast hk t (by omega)
  have h := curvature_minor_error_bound (hd j hj) (hd l hl) (hab j hj) (hab l hl)
  convert h using 1
  ring

/-- If the four gaps from state `i` are at most `H`, each coordinate of the curvature-minor
vector satisfies `|W_j| q_i³ ≤ 68 a H³`. -/
theorem orbitCurvature_height {a b i H : ℕ} (hba : b < a) (hi : i + 6 < P a b)
    (hH : 1 ≤ H) (hk : ∀ t < 4, kq a b (i + t) ≤ H) (j : Fin 3) :
    |orbitCurvatureVector a b i j| * (qq a b i : ℤ)^3 ≤ 68 * (a : ℤ) * H^3 := by
  have hq : (0 : ℝ) < qq a b i := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (qq_pos hba (by omega))
  have hm (r s : ℕ) (hr : r < 3) (hs : s < 3) :=
    (le_div_iff₀ (pow_pos hq 3)).mp ((orbit_curvature_minor_height 3 hba (by omega) hH hk hr hs
      ).trans_eq (by push_cast; ring) : _ ≤ 68 * (a : ℝ) * (H : ℝ) ^ 3 / (qq a b i : ℝ) ^ 3)
  have h12 := hm 1 2 (by decide) (by decide)
  have h20 := hm 2 0 (by decide) (by decide)
  have h01 := hm 0 1 (by decide) (by decide)
  fin_cases j <;> norm_num [orbitCurvatureVector, curvatureVector] <;>
    first | exact_mod_cast h12 | exact_mod_cast h20 | exact_mod_cast h01

/-- A quantity with `e q³ ≤ K a H³` at a start with `a ≤ 4 A q` satisfies
`e ≤ 64 K A³ H³ / a²`, using `q³ ≥ a³/(64 A³)`. -/
lemma le_cubic_height_div {e : ℤ} {q a A H K K' : ℕ} (he : 0 ≤ e) (ha : 0 < a)
    (hq : a ≤ 4 * A * q) (h : e * (q : ℤ) ^ 3 ≤ K * a * H ^ 3) (hK : 64 * K = K') :
    e ≤ ((K' * A ^ 3 * H ^ 3 / a ^ 2 : ℕ) : ℤ) := by
  have hqZ : (a : ℤ) ≤ 4 * A * q := by exact_mod_cast hq
  have hb : e * (a : ℤ) ^ 3 ≤ K' * (a : ℤ) * A ^ 3 * H ^ 3 := by
    calc _ ≤ e * (4 * (A : ℤ) * q) ^ 3 := by gcongr
      _ = (64 * (A : ℤ) ^ 3) * (e * (q : ℤ) ^ 3) := by ring
      _ ≤ (64 * (A : ℤ) ^ 3) * (K * (a : ℤ) * H ^ 3) := by gcongr
      _ = _ := by rw [← hK]; push_cast; ring
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : e * (a : ℤ) ^ 2 ≤ K' * (A : ℤ) ^ 3 * H ^ 3 := by
    apply (mul_le_mul_iff_right₀ haZ).mp
    convert hb using 1 <;> ring
  have hd := Int.le_ediv_of_mul_le (by positivity : (0 : ℤ) < (a : ℤ) ^ 2) hb'
  simpa only [Int.natCast_div, Nat.cast_mul, Nat.cast_pow] using hd

/-- At a selected start, each coordinate of the curvature-minor vector is at most the
curvature height `S` in absolute value (Lemma 8.8). -/
theorem selected_orbitCurvature_bound {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) (j : Fin 3) :
    |orbitCurvatureVector a b i j| ≤ (selectedCurvatureHeight a A T : ℕ) := by
  obtain ⟨hP, hk, hA⟩ := selectedStart_spec hmem hsT hi
  have hh := orbitCurvature_height hba (by omega : i + 6 < P a b)
    (show 1 ≤ selectedGapHeight a A T from Nat.le_add_left 1 _)
    (fun t ht => (hk t (by omega)).2) j
  exact le_cubic_height_div (abs_nonneg _) (by omega)
    (window_quotient_lower hba (by omega : i < P a b) hA) (by exact_mod_cast hh) (by norm_num)

end
end PierceLengthBound.FixedDividend
