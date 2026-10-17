import PierceBound.MinorCount
import PierceBound.TwoStateMain

/-!
# All ten minors are small

At a state `i` let `𝓜ᵢ` be the `3 × 5` integer matrix with rows `(d₀,…,d₄)`, `(k₀,…,k₄)` and
`(r₀,…,r₄)`. With `q = qᵢ` and `sⱼ = q_{i+j} - q`, the exact identity
`1/(q+y) = 1/q - y/q² + y²/q³ - y³/(q³(q+y))` applied to `νᵢ₊ⱼ(1) = b_{i+j}/a` gives
`b_{i+j}/a = 1/q - (1+sⱼ)/q² + (sⱼ² + 2sⱼ + kⱼ + 1)/q³ - eⱼ` with
`0 ≤ eⱼ ≤ μ_{i+j}((X+sⱼ)³)/q⁴` (`nu_expand`). Hence the first row of `𝓜ᵢ` equals
`a(q⁻² - q⁻³)·k - a q⁻³·r + O(aH³/q⁴)`, and every maximal minor is `O(aH⁶/q⁴)`
(`minor_height`): `|p| a³ ≤ 3609600 A⁴ H⁶`.
-/

namespace PierceBound

open Finset Polynomial

variable {a b : ℕ}

/-- The error term `eⱼ` of the expansion at state `m` relative to the base quotient `q`. -/
noncomputable def nuErr (a b m : ℕ) (q : ℝ) : ℝ :=
  ∑ j ∈ range (P a b - m), wt a b m j * ((qq a b m - q) + pt a b m j) ^ 3 /
    (q ^ 3 * (q + ((qq a b m - q) + pt a b m j)))

lemma muF_shift_sq (hba : b < a) {m : ℕ} (hm : m + 2 < P a b) (s : ℝ) :
    muF a b m ((X + C s) ^ 2) = s ^ 2 + 2 * s + kk a b m + 1 := by
  rw [show (X + C s) ^ 2 = X ^ 2 + C (2 * s) * X + C (s ^ 2) by
    simp only [map_mul, map_pow, map_ofNat]; ring, muF_add, muF_add, muF_C_mul, muF_C,
    muF_X_sq hba hm, muF_X hba (by omega), muF_one hba (by omega)]
  ring

lemma muF_shift_cube (hba : b < a) {m : ℕ} (hm : m + 3 < P a b) (s : ℝ) :
    muF a b m ((X + C s) ^ 3) = s ^ 3 + 3 * s ^ 2 + 3 * s * (kk a b m + 1) +
      (kk a b m ^ 2 + 2 * kk a b m + kk a b (m + 1) + 1) := by
  rw [show (X + C s) ^ 3 = X ^ 3 + C (3 * s) * X ^ 2 + C (3 * s ^ 2) * X + C (s ^ 3) by
    simp only [map_mul, map_pow, map_ofNat]; ring, muF_add, muF_add, muF_add, muF_C_mul,
    muF_C_mul, muF_C, muF_X_cube hba hm, muF_X_sq hba (by omega), muF_X hba (by omega),
    muF_one hba (by omega)]
  ring

/-- **The expansion of `b_m / a`.** -/
theorem nu_expand (hba : b < a) {m : ℕ} (hm : m + 3 < P a b) {q : ℝ} (hq : 0 < q)
    (hqm : q ≤ qq a b m) :
    0 ≤ nuErr a b m q ∧
      nuErr a b m q ≤ muF a b m ((X + C ((qq a b m : ℝ) - q)) ^ 3) / q ^ 4 ∧
      (orb a b m : ℝ) / a = 1 / q - (1 + ((qq a b m : ℝ) - q)) / q ^ 2 +
        (((qq a b m : ℝ) - q) ^ 2 + 2 * ((qq a b m : ℝ) - q) + kk a b m + 1) / q ^ 3 -
        nuErr a b m q := by
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
  · rw [show muF a b m ((X + C s) ^ 3) = ∑ j ∈ range (P a b - m),
      wt a b m j * (s + pt a b m j) ^ 3 by
        unfold muF; refine sum_congr rfl fun j _ => ?_
        simp only [eval_pow, eval_add, eval_X, eval_C]; ring, sum_div]
    refine sum_le_sum fun j hj => ?_
    have h1 := hw j (mem_range.mp hj)
    have h2 := hy j hj
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ h1.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (s + pt a b m j) ^ 3 * q ^ 4 ≤ (s + pt a b m j) ^ 3 * (q ^ 3 * (q + (s + pt a b m j))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [pow_pos hq 3]
    linarith
  · -- termwise identity, then the moments
    have hnu : (orb a b m : ℝ) / a = nuF a b m 1 := (nuF_one hba (by omega)).symm
    have hterm : ∀ j ∈ range (P a b - m), wt a b m j * (1 : ℝ[X]).eval (pt a b m j) /
        qq a b (m + j) = wt a b m j * (1 / q - (s + pt a b m j) / q ^ 2 +
          (s + pt a b m j) ^ 2 / q ^ 3) -
        wt a b m j * (s + pt a b m j) ^ 3 / (q ^ 3 * (q + (s + pt a b m j))) := by
      intro j hj
      have hqq : (qq a b (m + j) : ℝ) = q + (s + pt a b m j) := by
        rw [qq_eq_add_pt]; simp only [hs]; ring
      have hpos : 0 < q + (s + pt a b m j) := by have := hy j hj; linarith
      rw [eval_one, hqq]
      field_simp
      ring
    have hmom : ∑ j ∈ range (P a b - m), wt a b m j * (1 / q - (s + pt a b m j) / q ^ 2 +
        (s + pt a b m j) ^ 2 / q ^ 3) =
        1 / q * muF a b m 1 - 1 / q ^ 2 * muF a b m (X + C s) +
          1 / q ^ 3 * muF a b m ((X + C s) ^ 2) := by
      unfold muF
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      simp only [eval_pow, eval_add, eval_X, eval_C, eval_one]; ring
    rw [hnu]
    unfold nuF
    rw [sum_congr rfl hterm, sum_sub_distrib, hmom, muF_one hba (by omega),
      muF_shift_sq hba (by omega), muF_add, muF_X hba (by omega), muF_C, muF_one hba (by omega)]
    unfold nuErr
    simp only [hs]
    ring

/-! ### The matrix and its minors -/

section Matrix

variable (a b : ℕ)

/-- `sⱼ = q_{i+j} - qᵢ`. -/
def sq (i j : ℕ) : ℤ := (qq a b (i + j) : ℤ) - qq a b i

/-- `rⱼ = kⱼ (sⱼ + sⱼ₊₁) + kⱼ₊₁`. -/
def rq (i j : ℕ) : ℤ := kq a b (i + j) * (sq a b i j + sq a b i (j + 1)) + kq a b (i + j + 1)

/-- The `3 × 5` matrix `𝓜ᵢ`. -/
def Mi (i : ℕ) : Fin 3 → Fin 5 → ℤ :=
  ![fun j => dq a b (i + j), fun j => kq a b (i + j), fun j => rq a b i j]

end Matrix

/-- The real `3 × 3` minor of three rows. -/
def rminor3 (x y z : Fin 5 → ℝ) (c1 c2 c3 : Fin 5) : ℝ :=
  x c1 * (y c2 * z c3 - y c3 * z c2) - x c2 * (y c1 * z c3 - y c3 * z c1) +
    x c3 * (y c1 * z c2 - y c2 * z c1)

lemma rminor3_row (x y z : Fin 5 → ℝ) (α β : ℝ) (c1 c2 c3 : Fin 5) :
    rminor3 (fun c => x c - α * y c + β * z c) y z c1 c2 c3 = rminor3 x y z c1 c2 c3 := by
  unfold rminor3; ring

lemma rminor3_le {x y z : Fin 5 → ℝ} {X0 Y0 Z0 : ℝ} (hx : ∀ c, |x c| ≤ X0) (hy : ∀ c, |y c| ≤ Y0)
    (hz : ∀ c, |z c| ≤ Z0) (c1 c2 c3 : Fin 5) : |rminor3 x y z c1 c2 c3| ≤ 6 * X0 * Y0 * Z0 := by
  have h3 : ∀ c c' c'', |x c * y c' * z c''| ≤ X0 * Y0 * Z0 := fun c c' c'' => by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hx c) (hy c') (abs_nonneg _) ((abs_nonneg _).trans (hx c)))
      (hz c'') (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans (hx c)) ((abs_nonneg _).trans (hy c')))
  have e : rminor3 x y z c1 c2 c3 = x c1 * y c2 * z c3 - x c1 * y c3 * z c2 - x c2 * y c1 * z c3 +
      x c2 * y c3 * z c1 + x c3 * y c1 * z c2 - x c3 * y c2 * z c1 := by unfold rminor3; ring
  rw [e]
  have := h3 c1 c2 c3; have := h3 c1 c3 c2; have := h3 c2 c1 c3
  have := h3 c2 c3 c1; have := h3 c3 c1 c2; have := h3 c3 c2 c1
  calc _ ≤ |x c1 * y c2 * z c3| + |x c1 * y c3 * z c2| + |x c2 * y c1 * z c3| +
        |x c2 * y c3 * z c1| + |x c3 * y c1 * z c2| + |x c3 * y c2 * z c1| := by
        have a1 := abs_sub (x c1 * y c2 * z c3 - x c1 * y c3 * z c2 - x c2 * y c1 * z c3 +
          x c2 * y c3 * z c1 + x c3 * y c1 * z c2) (x c3 * y c2 * z c1)
        have a2 := abs_add_le (x c1 * y c2 * z c3 - x c1 * y c3 * z c2 - x c2 * y c1 * z c3 +
          x c2 * y c3 * z c1) (x c3 * y c1 * z c2)
        have a3 := abs_add_le (x c1 * y c2 * z c3 - x c1 * y c3 * z c2 - x c2 * y c1 * z c3)
          (x c2 * y c3 * z c1)
        have a4 := abs_sub (x c1 * y c2 * z c3 - x c1 * y c3 * z c2) (x c2 * y c1 * z c3)
        have a5 := abs_sub (x c1 * y c2 * z c3) (x c1 * y c3 * z c2)
        linarith
    _ ≤ 6 * X0 * Y0 * Z0 := by linarith

lemma plk_cast (M : Fin 3 → Fin 5 → ℤ) (t : Fin 10) :
    ((plk M t : ℤ) : ℝ) = rminor3 (fun c => (M 0 c : ℝ)) (fun c => (M 1 c : ℝ))
      (fun c => (M 2 c : ℝ)) (trip t).1 (trip t).2.1 (trip t).2.2 := by
  unfold plk minor3 rminor3; push_cast; ring

lemma sq_eq_sum (i j : ℕ) : sq a b i j = ∑ m ∈ Ico i (i + j), kq a b m := by
  rw [sum_kq]; rfl

/-- **Every maximal minor of `𝓜ᵢ` is small.** -/
theorem minor_height (hba : b < a) {A H i : ℕ} (hP : i + 8 < P a b) (hb : orb a b i < 2 * A)
    (hk : ∀ m, m < 7 → 1 ≤ kq a b (i + m) ∧ kq a b (i + m) ≤ H) (t : Fin 10) :
    |plk (Mi a b i) t| * (a : ℤ) ^ 3 ≤ 3609600 * (A : ℤ) ^ 4 * (H : ℤ) ^ 6 := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hq0 : (0 : ℝ) < qq a b i := by exact_mod_cast qq_pos hba (by omega)
  set q : ℝ := (qq a b i : ℝ)
  have hH1 : (1 : ℝ) ≤ H := by
    have := (hk 0 (by norm_num)).2; have := (hk 0 (by norm_num)).1
    have : (1 : ℤ) ≤ H := by omega
    exact_mod_cast this
  have hkR : ∀ m, m < 7 → (1 : ℝ) ≤ kk a b (i + m) ∧ kk a b (i + m) ≤ H := by
    intro m hm
    have e : kk a b (i + m) = ((kq a b (i + m) : ℤ) : ℝ) := by simp [kk, kq]
    rw [e]
    exact ⟨by exact_mod_cast (hk m hm).1, by exact_mod_cast (hk m hm).2⟩
  -- `0 ≤ sⱼ ≤ jH`
  have hsR : ∀ j, j ≤ 6 → (0 : ℝ) ≤ (qq a b (i + j) : ℝ) - q ∧ (qq a b (i + j) : ℝ) - q ≤ j * H := by
    intro j hj
    have e : (qq a b (i + j) : ℝ) - q = ((sq a b i j : ℤ) : ℝ) := by simp [sq, q]
    rw [e, sq_eq_sum]
    have hb' : ∀ m ∈ Ico i (i + j), 0 ≤ kq a b m ∧ kq a b m ≤ H := by
      intro m hm
      have := mem_Ico.mp hm
      have h := hk (m - i) (by omega)
      rw [show i + (m - i) = m by omega] at h
      exact ⟨by linarith [h.1], h.2⟩
    constructor
    · exact_mod_cast sum_nonneg fun m hm => (hb' m hm).1
    · have : ∑ m ∈ Ico i (i + j), kq a b m ≤ ∑ _m ∈ Ico i (i + j), (H : ℤ) :=
        sum_le_sum fun m hm => (hb' m hm).2
      rw [sum_const, Nat.card_Ico, show i + j - i = j by omega, nsmul_eq_mul] at this
      exact_mod_cast this
  -- the expansions at `i, …, i+5`
  have hexp : ∀ j, j ≤ 5 → 0 ≤ nuErr a b (i + j) q ∧ nuErr a b (i + j) q ≤ 235 * H ^ 3 / q ^ 4 ∧
      (orb a b (i + j) : ℝ) / a = 1 / q - (1 + ((qq a b (i + j) : ℝ) - q)) / q ^ 2 +
        (((qq a b (i + j) : ℝ) - q) ^ 2 + 2 * ((qq a b (i + j) : ℝ) - q) + kk a b (i + j) + 1) /
          q ^ 3 - nuErr a b (i + j) q := by
    intro j hj
    have hqm : q ≤ qq a b (i + j) := by
      have h := qq_le_of_le (a := a) (b := b) (show i ≤ i + j by omega) (by omega)
      have h' : ((qq a b i : ℕ) : ℝ) ≤ ((qq a b (i + j) : ℕ) : ℝ) := by exact_mod_cast h
      exact h'
    obtain ⟨e1, e2, e3⟩ := nu_expand hba (m := i + j) (by omega) hq0 hqm
    refine ⟨e1, e2.trans ?_, e3⟩
    rw [muF_shift_cube hba (by omega)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    obtain ⟨s0, s1⟩ := hsR j (by omega)
    have sH : (qq a b (i + j) : ℝ) - q ≤ 5 * H := s1.trans (by
      have : (j : ℝ) ≤ 5 := by exact_mod_cast hj
      nlinarith)
    obtain ⟨k0, k1⟩ := hkR j (by omega)
    obtain ⟨k0', k1'⟩ := hkR (j + 1) (by omega)
    rw [show i + j + 1 = i + (j + 1) by ring]
    set x := (qq a b (i + j) : ℝ) - q
    have hx2 : x ^ 2 ≤ 25 * H ^ 2 := by nlinarith
    have hx3 : x ^ 3 ≤ 125 * H ^ 3 := by nlinarith
    have hH2 : (H : ℝ) ≤ H ^ 2 := by nlinarith
    have hH3 : (H : ℝ) ^ 2 ≤ H ^ 3 := by nlinarith
    nlinarith
  -- the modified first row
  set D' : Fin 5 → ℝ := fun c => (dq a b (i + c) : ℝ) -
    a * (1 / q ^ 2 - 1 / q ^ 3) * (kq a b (i + c) : ℝ) + a / q ^ 3 * (rq a b i c : ℝ)
  have hD' : ∀ c : Fin 5, |D' c| ≤ a * (235 * H ^ 3 / q ^ 4) := by
    intro c
    have hc := c.2
    obtain ⟨e0, e1, e2⟩ := hexp c (by omega)
    obtain ⟨f0, f1, f2⟩ := hexp (c + 1) (by omega)
    have hdq : (dq a b (i + c) : ℝ) = a * ((orb a b (i + c) : ℝ) / a - (orb a b (i + c + 1) : ℝ) / a) := by
      simp only [dq]; push_cast; field_simp
    have hkq : (kq a b (i + c) : ℝ) = (qq a b (i + (c + 1)) : ℝ) - qq a b (i + c) := by
      simp only [kq]; push_cast; ring_nf
    have hrq : (rq a b i c : ℝ) = ((qq a b (i + (c + 1)) : ℝ) - qq a b (i + c)) *
        (((qq a b (i + c) : ℝ) - q) + ((qq a b (i + (c + 1)) : ℝ) - q)) + kk a b (i + (c + 1)) := by
      simp only [rq, sq, kq, kk, q]; push_cast; ring_nf
    have hkk : kk a b (i + c) = (qq a b (i + (c + 1)) : ℝ) - qq a b (i + c) := by
      simp only [kk]; ring_nf
    have hD : D' c = a * (nuErr a b (i + (c + 1)) q - nuErr a b (i + c) q) := by
      simp only [D']
      rw [hdq, hkq, hrq, show i + c + 1 = i + (c + 1) by ring, e2, f2, hkk]
      field_simp
      ring
    rw [hD, abs_mul, abs_of_pos ha]
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    rw [abs_le]; constructor <;> linarith
  have hK : ∀ c : Fin 5, |((Mi a b i 1 c : ℤ) : ℝ)| ≤ H := by
    intro c
    simp only [Mi, Matrix.cons_val_one, Matrix.head_cons]
    obtain ⟨h1, h2⟩ := hk c (by have := c.2; omega)
    rw [abs_of_pos (by exact_mod_cast (show (0 : ℤ) < kq a b (i + c) by omega))]
    exact_mod_cast h2
  have hR : ∀ c : Fin 5, |((Mi a b i 2 c : ℤ) : ℝ)| ≤ 10 * H ^ 2 := by
    intro c
    simp only [Mi, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    have hc := c.2
    obtain ⟨k1, k2⟩ := hk c (by omega)
    obtain ⟨k1', k2'⟩ := hk (c + 1) (by omega)
    have hs := hsR c (by omega)
    have hs' := hsR (c + 1) (by omega)
    have e1 : ((sq a b i c : ℤ) : ℝ) = (qq a b (i + c) : ℝ) - q := by simp [sq, q]
    have e2 : ((sq a b i (c + 1) : ℤ) : ℝ) = (qq a b (i + (c + 1)) : ℝ) - q := by simp [sq, q]
    have hk1 : (1 : ℝ) ≤ (kq a b (i + c) : ℝ) := by exact_mod_cast k1
    have hk2 : (kq a b (i + c) : ℝ) ≤ H := by exact_mod_cast k2
    have hk1' : (1 : ℝ) ≤ (kq a b (i + (c + 1)) : ℝ) := by exact_mod_cast k1'
    have hk2' : (kq a b (i + (c + 1)) : ℝ) ≤ H := by exact_mod_cast k2'
    have hcR : ((c : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show (c : ℕ) ≤ 4 by omega)
    have hval : ((rq a b i c : ℤ) : ℝ) = (kq a b (i + c) : ℝ) *
        (((qq a b (i + c) : ℝ) - q) + ((qq a b (i + (c + 1)) : ℝ) - q)) + (kq a b (i + (c + 1)) : ℝ) := by
      simp only [rq]; push_cast; rw [e1, e2, show i + c + 1 = i + (c + 1) by ring]
    rw [hval]
    push_cast at hs hs'
    have hsum : ((qq a b (i + c) : ℝ) - q) + ((qq a b (i + (c + 1)) : ℝ) - q) ≤ 9 * H := by
      nlinarith
    have hnn : 0 ≤ (kq a b (i + c) : ℝ) * (((qq a b (i + c) : ℝ) - q) +
        ((qq a b (i + (c + 1)) : ℝ) - q)) + (kq a b (i + (c + 1)) : ℝ) := by
      have : 0 ≤ ((qq a b (i + c) : ℝ) - q) + ((qq a b (i + (c + 1)) : ℝ) - q) := by linarith
      positivity
    rw [abs_of_nonneg hnn]
    nlinarith
  -- the minor
  have hrow : rminor3 (fun c => ((Mi a b i 0 c : ℤ) : ℝ)) (fun c => ((Mi a b i 1 c : ℤ) : ℝ))
      (fun c => ((Mi a b i 2 c : ℤ) : ℝ)) (trip t).1 (trip t).2.1 (trip t).2.2 =
      rminor3 D' (fun c => ((Mi a b i 1 c : ℤ) : ℝ)) (fun c => ((Mi a b i 2 c : ℤ) : ℝ))
        (trip t).1 (trip t).2.1 (trip t).2.2 := by
    rw [← rminor3_row D' _ _ (-(a * (1 / q ^ 2 - 1 / q ^ 3))) (-(a / q ^ 3))]
    congr 1
    funext c
    simp only [D', Mi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hbd := rminor3_le hD' hK hR (trip t).1 (trip t).2.1 (trip t).2.2
  rw [← hrow, ← plk_cast] at hbd
  -- `a ≤ 4 A q`
  have h4 : (a : ℝ) ≤ 4 * A * q := by
    have h := a_le_four (A := A) hba (by omega) hb
    have h' : ((a : ℕ) : ℝ) ≤ ((4 * A * qq a b i : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have h44 : (a : ℝ) ^ 4 ≤ 256 * A ^ 4 * q ^ 4 := by
    calc (a : ℝ) ^ 4 ≤ (4 * A * q) ^ 4 := pow_le_pow_left₀ ha.le h4 4
      _ = 256 * A ^ 4 * q ^ 4 := by ring
  have hfin : |((plk (Mi a b i) t : ℤ) : ℝ)| * (a : ℝ) ^ 3 ≤ 3609600 * (A : ℝ) ^ 4 * (H : ℝ) ^ 6 := by
    have hq4 : 0 < q ^ 4 := by positivity
    calc |((plk (Mi a b i) t : ℤ) : ℝ)| * (a : ℝ) ^ 3
        ≤ 6 * (a * (235 * H ^ 3 / q ^ 4)) * H * (10 * H ^ 2) * (a : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hbd (by positivity)
      _ = 14100 * H ^ 6 * ((a : ℝ) ^ 4 / q ^ 4) := by field_simp; ring
      _ ≤ 14100 * H ^ 6 * (256 * A ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ hq4]; linarith
      _ = 3609600 * (A : ℝ) ^ 4 * (H : ℝ) ^ 6 := by ring
  have : ((|plk (Mi a b i) t| * (a : ℤ) ^ 3 : ℤ) : ℝ) ≤ ((3609600 * (A : ℤ) ^ 4 * (H : ℤ) ^ 6 : ℤ) : ℝ) := by
    push_cast; exact hfin
  exact_mod_cast this

end PierceBound
