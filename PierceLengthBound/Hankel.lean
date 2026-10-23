/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.SixStep

/-!
# The moment model and the Hankel hierarchy

For the orbit `b₀ > b₁ > ⋯ > b_{N-1} > 0` of `x ↦ a mod x`, with quotients `qᵢ = ⌊a/bᵢ⌋`,
define probability weights `wᵢ(j) > 0` on the points `pᵢ(j) = q_{i+j} - qᵢ`, `j < N - i`, by
`w_{N-1} = δ₀` and
`wᵢ(0) = 1 - ∑_j w_{i+1}(j)/pᵢ(j+1)`, `wᵢ(j+1) = w_{i+1}(j)/pᵢ(j+1)`.
The moments `hᵢ(s) = ∑_j wᵢ(j) pᵢ(j)^s / q_{i+j}` of the measure `νᵢ = μᵢ/(qᵢ + x)` satisfy

* `hᵢ(0) = bᵢ/a` (`hm_zero`), so `bᵢ/a = E[1/(qᵢ + Xᵢ)]`;
* `hᵢ(s+1) = ∑_t C(s,t) kᵢ^{s-t} h_{i+1}(t)` (`hm_succ`);
* `hᵢ(s) = (-qᵢ)^s bᵢ/a + (integer)` (`hm_int`).

Hence the Hankel invariants `Iᵣ(i) = a · det (hᵢ(j+l))_{j,l<r}` are positive integers for
`1 ≤ r ≤ N - i` (`hankelInv_pos_int`). The first four are `bᵢ`, `bᵢ - b_{i+1}`, the curvature
`D` and the six-step integer `L` (`hankelInv_one` … `hankelInv_four`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

section Moments

variable (a b : ℕ)

/-- The support points `pᵢ(j) = q_{i+j} - qᵢ`. -/
noncomputable def pt (i j : ℕ) : ℝ := (qq a b (i + j) : ℝ) - qq a b i

/-- The weights of the moment model. -/
noncomputable def wt (i : ℕ) : ℕ → ℝ :=
  if _h : i + 1 < P a b then
    fun j => if j = 0 then 1 - ∑ j' ∈ range (P a b - (i + 1)), wt (i + 1) j' / pt a b i (j' + 1)
      else wt (i + 1) (j - 1) / pt a b i j
  else fun j => if j = 0 then 1 else 0
termination_by P a b - i

/-- The moments `hᵢ(s)` of `νᵢ`. -/
noncomputable def hm (i s : ℕ) : ℝ :=
  ∑ j ∈ range (P a b - i), wt a b i j * pt a b i j ^ s / qq a b (i + j)

lemma wt_of_lt {i : ℕ} (h : i + 1 < P a b) (j : ℕ) :
    wt a b i j = if j = 0 then 1 - ∑ j' ∈ range (P a b - (i + 1)), wt a b (i + 1) j' /
      pt a b i (j' + 1) else wt a b (i + 1) (j - 1) / pt a b i j := by
  rw [wt]; simp [h]

lemma wt_of_not_lt {i : ℕ} (h : ¬ i + 1 < P a b) (j : ℕ) :
    wt a b i j = if j = 0 then 1 else 0 := by
  rw [wt]; simp [h]

end Moments

section Orbit

variable {a b : ℕ}

/-- `pᵢ(j) ≥ j`. -/
lemma pt_ge {i j : ℕ} (h : i + j < P a b) : (j : ℝ) ≤ pt a b i j := by
  induction j with
  | zero => simp [pt]
  | succ j ih =>
    have := ih (by omega)
    have hlt := qq_lt (a := a) (b := b) (i := i + j) (by omega)
    have : (qq a b (i + j) : ℝ) + 1 ≤ qq a b (i + (j + 1)) := by exact_mod_cast hlt
    unfold pt at *; push_cast; linarith

lemma pt_succ (i j : ℕ) :
    pt a b i (j + 1) = ((qq a b (i + 1) : ℝ) - qq a b i) + pt a b (i + 1) j := by
  unfold pt; rw [show i + (j + 1) = i + 1 + j by ring]; ring

lemma pt_strictMono {i : ℕ} : ∀ {j j' : ℕ}, j < j' → i + j' < P a b → pt a b i j < pt a b i j' := by
  intro j j' hjj hj'
  have : qq a b (i + j) < qq a b (i + j') := by
    induction j', hjj using Nat.le_induction with
    | base => exact qq_lt (by omega)
    | succ j' hjj ih => exact (ih (by omega)).trans (qq_lt (by omega))
  unfold pt
  have : (qq a b (i + j) : ℝ) < qq a b (i + j') := by exact_mod_cast this
  linarith

/-- The final gap: `q_{N-1} - q_{N-2} ≥ 2`. -/
lemma last_gap (hba : b < a) (hN : 2 ≤ P a b) :
    qq a b (P a b - 2) + 2 ≤ qq a b (P a b - 1) := by
  have hlt := qq_lt (a := a) (b := b) (i := P a b - 2) (by omega)
  rw [show P a b - 2 + 1 = P a b - 1 by omega] at hlt
  by_contra hcon
  have heq : qq a b (P a b - 1) = qq a b (P a b - 2) + 1 := by omega
  have e1 := orb_div (a := a) (b := b) (i := P a b - 2) (by omega)
  rw [show P a b - 2 + 1 = P a b - 1 by omega] at e1
  have e2 := orb_last (a := a) (b := b) (by omega)
  have hq := qq_pos hba (i := P a b - 2) (by omega)
  have hlt' : orb a b (P a b - 1) < orb a b (P a b - 2) := by
    have := orb_succ_of_ne (orb_ne_zero_of_lt (a := a) (b := b) (i := P a b - 2) (by omega))
    rw [show P a b - 2 + 1 = P a b - 1 by omega] at this
    rw [this]; exact Nat.mod_lt _ (orb_pos_of_lt (by omega))
  rw [heq] at e2
  -- `x_{N-1} (q+1) = q x_{N-2} + x_{N-1}` gives `x_{N-1} = x_{N-2}`
  have : orb a b (P a b - 1) * qq a b (P a b - 2) = orb a b (P a b - 2) * qq a b (P a b - 2) := by
    nlinarith
  have := Nat.eq_of_mul_eq_mul_right (by omega) this
  omega

/-- **The weights are positive and sum to `1`.** -/
theorem wt_spec (hba : b < a) : ∀ m i, i + m + 1 = P a b →
    (∀ j < P a b - i, 0 < wt a b i j) ∧ ∑ j ∈ range (P a b - i), wt a b i j = 1 := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have hnl : ¬ i + 1 < P a b := by omega
    rw [show P a b - i = 1 by omega]
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [wt_of_not_lt a b hnl, ite_eq_left (by omega)]; norm_num
    · simp [wt_of_not_lt a b hnl]
  | succ m ih =>
    intro i hi
    have hl : i + 1 < P a b := by omega
    obtain ⟨hpos, hsum⟩ := ih (i + 1) (by omega)
    have hpt : ∀ j' < P a b - (i + 1), 1 ≤ pt a b i (j' + 1) := fun j' hj' => by
      have := pt_ge (a := a) (b := b) (i := i) (j := j' + 1) (by omega)
      push_cast at this; linarith
    -- the sum `S = ∑ w_{i+1}(j')/pᵢ(j'+1)` is `< 1`
    have hS : ∑ j' ∈ range (P a b - (i + 1)), wt a b (i + 1) j' / pt a b i (j' + 1) < 1 := by
      rw [← hsum]
      by_cases hN2 : 2 ≤ P a b - (i + 1)
      · apply sum_lt_sum
        · intro j' hj'
          have := hpos j' (mem_range.mp hj')
          rw [div_le_iff₀ (by linarith [hpt j' (mem_range.mp hj')])]
          nlinarith [hpt j' (mem_range.mp hj')]
        · refine ⟨1, mem_range.mpr (by omega), ?_⟩
          have hw := hpos 1 (by omega)
          have h2 : (2 : ℝ) ≤ pt a b i 2 := by
            have := pt_ge (a := a) (b := b) (i := i) (j := 2) (by omega); exact_mod_cast this
          rw [div_lt_iff₀ (by linarith)]
          nlinarith
      · have hN : P a b - (i + 1) = 1 := by omega
        rw [hN]
        simp only [range_one, sum_singleton]
        have hw := hpos 0 (by omega)
        have hgap := last_gap hba (show 2 ≤ P a b by omega)
        have hi2 : i = P a b - 2 := by omega
        have h2 : (2 : ℝ) ≤ pt a b i 1 := by
          unfold pt
          rw [hi2, show P a b - 2 + 1 = P a b - 1 by omega]
          have : ((qq a b (P a b - 2) + 2 : ℕ) : ℝ) ≤ (qq a b (P a b - 1) : ℕ) := by
            exact_mod_cast hgap
          push_cast at this; linarith
        rw [div_lt_iff₀ (by linarith)]
        nlinarith
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [wt_of_lt a b hl]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [ite_eq_left rfl]; linarith
      · rw [ite_eq_right (by omega)]
        have := hpos (j - 1) (by omega)
        have := hpt (j - 1) (by omega)
        rw [show j - 1 + 1 = j by omega] at this
        positivity
    · rw [show P a b - i = (P a b - (i + 1)) + 1 by omega, sum_range_succ', wt_of_lt a b hl 0,
        ite_eq_left rfl]
      have : ∀ j' ∈ range (P a b - (i + 1)), wt a b i (j' + 1) =
          wt a b (i + 1) j' / pt a b i (j' + 1) := fun j' _ => by
        rw [wt_of_lt a b hl, ite_eq_right (by omega), Nat.add_sub_cancel]
      rw [sum_congr rfl this]
      ring

/-- **The exact representation** `hᵢ(0) = bᵢ / a`. -/
theorem hm_zero (hba : b < a) : ∀ m i, i + m + 1 = P a b → hm a b i 0 = orb a b i / a := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  intro m
  induction m with
  | zero =>
    intro i hi
    have hnl : ¬ i + 1 < P a b := by omega
    have hiN : i = P a b - 1 := by omega
    unfold hm
    rw [show P a b - i = 1 by omega]
    simp only [range_one, sum_singleton, wt_of_not_lt a b hnl, ite_true, pow_zero, add_zero]
    have e := orb_last (a := a) (b := b) (by omega)
    rw [← hiN] at e
    have hq : (0 : ℝ) < qq a b i := by exact_mod_cast (qq_pos hba (by omega))
    rw [eq_div_iff ha.ne']
    have : (orb a b i : ℝ) * qq a b i = a := by exact_mod_cast e
    field_simp
    linarith
  | succ m ih =>
    intro i hi
    have hl : i + 1 < P a b := by omega
    have ih' := ih (i + 1) (by omega)
    obtain ⟨hpos, -⟩ := wt_spec hba m (i + 1) (by omega)
    have hq : (0 : ℝ) < qq a b i := by exact_mod_cast (qq_pos hba (by omega))
    have hpt : ∀ j' < P a b - (i + 1), 0 < pt a b i (j' + 1) := fun j' hj' => by
      have := pt_ge (a := a) (b := b) (i := i) (j := j' + 1) (by omega)
      push_cast at this; linarith
    -- `qᵢ hᵢ(0) + h_{i+1}(0) = 1`
    have h1 : hm a b i 0 = wt a b i 0 / qq a b i +
        ∑ j' ∈ range (P a b - (i + 1)), wt a b i (j' + 1) / qq a b (i + (j' + 1)) := by
      unfold hm
      rw [show P a b - i = (P a b - (i + 1)) + 1 by omega, sum_range_succ']
      simp only [pow_zero, mul_one, add_zero]
      ring
    have h2 : hm a b (i + 1) 0 =
        ∑ j' ∈ range (P a b - (i + 1)), wt a b (i + 1) j' / qq a b (i + 1 + j') := by
      unfold hm; simp only [pow_zero, mul_one]
    have h3 : wt a b i 0 = 1 - ∑ j' ∈ range (P a b - (i + 1)), wt a b (i + 1) j' /
        pt a b i (j' + 1) := by rw [wt_of_lt a b hl 0, ite_eq_left rfl]
    have hterm : ∀ j' ∈ range (P a b - (i + 1)),
        (qq a b i : ℝ) * (wt a b i (j' + 1) / qq a b (i + (j' + 1))) +
          wt a b (i + 1) j' / qq a b (i + 1 + j') = wt a b (i + 1) j' / pt a b i (j' + 1) := by
      intro j' hj'
      rw [wt_of_lt a b hl, ite_eq_right (by omega), Nat.add_sub_cancel]
      have hp := hpt j' (mem_range.mp hj')
      have hQ : (qq a b (i + (j' + 1)) : ℝ) = qq a b i + pt a b i (j' + 1) := by unfold pt; ring
      rw [show i + 1 + j' = i + (j' + 1) by ring, hQ]
      have : (0 : ℝ) < qq a b i + pt a b i (j' + 1) := by linarith
      field_simp
    have key : (qq a b i : ℝ) * hm a b i 0 + hm a b (i + 1) 0 = 1 := by
      rw [h1, h2, mul_add, mul_div_cancel₀ _ hq.ne', mul_sum, add_assoc, ← sum_add_distrib,
        sum_congr rfl hterm, h3]
      ring
    rw [ih'] at key
    have e := orb_div (a := a) (b := b) (i := i) (by omega)
    have e' : (orb a b i : ℝ) * qq a b i + orb a b (i + 1) = a := by exact_mod_cast e
    rw [eq_div_iff ha.ne']
    field_simp at key
    nlinarith

lemma pt_zero (i : ℕ) : pt a b i 0 = 0 := by simp [pt]

/-- **The moment recursion** `hᵢ(s+1) = ∑_t C(s,t) kᵢ^{s-t} h_{i+1}(t)`. -/
theorem hm_succ {i : ℕ} (hl : i + 1 < P a b) (s : ℕ) :
    hm a b i (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      ((qq a b (i + 1) : ℝ) - qq a b i) ^ (s - t) * hm a b (i + 1) t := by
  have hpt : ∀ j' < P a b - (i + 1), 0 < pt a b i (j' + 1) := fun j' hj' => by
    have := pt_ge (a := a) (b := b) (i := i) (j := j' + 1) (by omega)
    push_cast at this; linarith
  have hL : hm a b i (s + 1) = ∑ j' ∈ range (P a b - (i + 1)),
      wt a b (i + 1) j' * pt a b i (j' + 1) ^ s / qq a b (i + (j' + 1)) := by
    unfold hm
    rw [show P a b - i = (P a b - (i + 1)) + 1 by omega, sum_range_succ', pt_zero,
      zero_pow (Nat.succ_ne_zero s), mul_zero, zero_div, add_zero]
    refine sum_congr rfl fun j' hj' => ?_
    rw [wt_of_lt a b hl, ite_eq_right (by omega), Nat.add_sub_cancel]
    have hp := hpt j' (mem_range.mp hj')
    field_simp
    ring
  rw [hL]
  unfold hm
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j' _ => ?_
  rw [pt_succ, add_comm ((qq a b (i + 1) : ℝ) - qq a b i) (pt a b (i + 1) j'),
    show i + 1 + j' = i + (j' + 1) by ring, add_pow, mul_sum, sum_div]
  refine sum_congr rfl fun t _ => ?_
  ring

/-- At the last state, `h_{N-1}(s+1) = 0`. -/
theorem hm_last {i : ℕ} (hi : i + 1 = P a b) (s : ℕ) : hm a b i (s + 1) = 0 := by
  unfold hm
  rw [show P a b - i = 1 by omega]
  simp [pt]

/-- `hᵢ(1) = b_{i+1} / a`. -/
theorem hm_one (hba : b < a) {i : ℕ} (hi : i < P a b) : hm a b i 1 = orb a b (i + 1) / a := by
  by_cases hl : i + 1 < P a b
  · rw [hm_succ hl 0]
    simp [hm_zero hba (P a b - (i + 1) - 1) (i + 1) (by omega)]
  · have h1 : i + 1 = P a b := by omega
    rw [hm_last h1 0, h1, orb_P]; simp

/-- **Integrality**: `hᵢ(s) = (-qᵢ)^s bᵢ/a + z` with `z ∈ ℤ`. -/
theorem hm_int (hba : b < a) : ∀ m i, i + m + 1 = P a b → ∀ s, ∃ z : ℤ,
    hm a b i s = (-(qq a b i : ℝ)) ^ s * (orb a b i / a) + z := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  intro m
  induction m with
  | zero =>
    intro i hi s
    have e := orb_last (a := a) (b := b) (by omega)
    rw [show P a b - 1 = i by omega] at e
    have e' : (orb a b i : ℝ) * qq a b i = a := by exact_mod_cast e
    have hq : (0 : ℝ) < qq a b i := by exact_mod_cast (qq_pos hba (by omega))
    have hβ : (orb a b i : ℝ) / a = 1 / qq a b i := by
      rw [div_eq_div_iff ha.ne' hq.ne']; linarith
    rcases s with _ | s
    · exact ⟨0, by rw [hm_zero hba 0 i hi]; simp⟩
    · refine ⟨(qq a b i : ℤ) ^ s * (-1) ^ s, ?_⟩
      rw [hm_last (by omega) s, hβ]
      push_cast
      field_simp
      ring
  | succ m ih =>
    intro i hi s
    have hl : i + 1 < P a b := by omega
    choose z hz using ih (i + 1) (by omega)
    rcases s with _ | s
    · exact ⟨0, by rw [hm_zero hba (m + 1) i hi]; simp⟩
    · refine ⟨(-(qq a b i : ℤ)) ^ s + ∑ t ∈ range (s + 1), (s.choose t : ℤ) *
          ((qq a b (i + 1) : ℤ) - qq a b i) ^ (s - t) * z t, ?_⟩
      rw [hm_succ hl s]
      simp only [hz]
      have e := orb_div (a := a) (b := b) (i := i) (by omega)
      have hβ' : (orb a b (i + 1) : ℝ) / a = 1 - qq a b i * (orb a b i / a) := by
        have e' : (orb a b i : ℝ) * qq a b i + orb a b (i + 1) = a := by exact_mod_cast e
        field_simp; linarith
      rw [hβ']
      have hpow : ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
          ((qq a b (i + 1) : ℝ) - qq a b i) ^ (s - t) * (-(qq a b (i + 1) : ℝ)) ^ t =
          (-(qq a b i : ℝ)) ^ s := by
        rw [show (-(qq a b i : ℝ)) = -(qq a b (i + 1) : ℝ) + ((qq a b (i + 1) : ℝ) - qq a b i)
          by ring, add_pow]
        refine sum_congr rfl fun t _ => ?_
        ring
      push_cast
      have : ∑ t ∈ range (s + 1), (s.choose t : ℝ) * ((qq a b (i + 1) : ℝ) - qq a b i) ^ (s - t) *
          ((-(qq a b (i + 1) : ℝ)) ^ t * (1 - qq a b i * (orb a b i / a)) + z t) =
          (-(qq a b i : ℝ)) ^ s * (1 - qq a b i * (orb a b i / a)) +
            ∑ t ∈ range (s + 1), (s.choose t : ℝ) * ((qq a b (i + 1) : ℝ) - qq a b i) ^ (s - t) *
              z t := by
        rw [← hpow, sum_mul, ← sum_add_distrib]
        refine sum_congr rfl fun t _ => ?_
        ring
      rw [this]
      ring

end Orbit

section HankelDefs

variable (a b : ℕ)

/-- The Hankel matrix `(hᵢ(j + l))_{j, l < r}`. -/
noncomputable def hankel (i r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun j l => hm a b i (j + l)

/-- The Hankel invariant `Iᵣ(i) = a · det (hᵢ(j + l))_{j, l < r}`. -/
noncomputable def hankelInv (i r : ℕ) : ℝ := a * (hankel a b i r).det

end HankelDefs

section Hankel

open scoped Matrix

variable {a b : ℕ}

/-- **Integrality.** `Iᵣ(i) ∈ ℤ`. Multiplying by the unit lower triangular matrix
`E = 1 + qᵢ · (shift)` makes rows `1, …, r-1` integral; expanding along row `0`, which is
`(-qᵢ)^l bᵢ/a + (integer)`, gives `a det ∈ ℤ`. -/
theorem hankelInv_int (hba : b < a) {i : ℕ} (hi : i < P a b) (r : ℕ) :
    ∃ z : ℤ, hankelInv a b i r = z := by
  rcases r with _ | k
  · exact ⟨a, by simp [hankelInv]⟩
  choose zz hzz using hm_int hba (P a b - 1 - i) i (by omega)
  set q : ℝ := (qq a b i : ℝ) with hq
  set H := hankel a b i (k + 1)
  set E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    Matrix.of fun j l => if j = l then 1 else if (j : ℕ) = l + 1 then q else 0 with hE
  have hEdet : E.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular E ?_]
    · simp [E]
    · intro j l hjl
      have : (j : ℕ) < l := hjl
      simp only [E, Matrix.of_apply]
      rw [ite_eq_right (by intro h; rw [h] at this; omega), ite_eq_right (by omega)]
  have hEH0 : ∀ l, (E * H) 0 l = H 0 l := by
    intro l
    rw [Matrix.mul_apply, Fintype.sum_eq_single 0]
    · simp [E]
    · intro l' hl'
      simp only [E, Matrix.of_apply]
      rw [ite_eq_right (Ne.symm hl'), ite_eq_right (by simp)]
      ring
  have hEHs : ∀ (j : Fin k) l, (E * H) j.succ l = H j.succ l + q * H j.castSucc l := by
    intro j l
    have hne : j.succ ≠ j.castSucc := (Fin.castSucc_lt_succ (i := j)).ne'
    rw [Matrix.mul_apply, Fintype.sum_eq_add j.succ j.castSucc hne ?_]
    · have hc : ((j.succ : Fin (k + 1)) : ℕ) = (j.castSucc : ℕ) + 1 := by simp
      simp only [E, Matrix.of_apply, ite_eq_right hne, hc, ite_true, one_mul]
    · intro l' ⟨h1, h2⟩
      simp only [E, Matrix.of_apply]
      rw [ite_eq_right (Ne.symm h1), ite_eq_right ?_]
      · ring
      · intro h; apply h2; ext; simp at h ⊢; omega
  have hdet : H.det = (E * H).det := by rw [Matrix.det_mul, hEdet, one_mul]
  -- the submatrices are integral
  have hsub : ∀ l : Fin (k + 1), ∃ D : ℤ, ((E * H).submatrix Fin.succ l.succAbove).det = D := by
    intro l
    refine ⟨(Matrix.of fun (j : Fin k) (l' : Fin k) =>
      zz ((j : ℕ) + 1 + (l.succAbove l' : ℕ)) + qq a b i * zz ((j : ℕ) + (l.succAbove l' : ℕ))).det,
      ?_⟩
    rw [Int.cast_det]
    congr 1
    ext j l'
    simp only [Matrix.submatrix_apply, hEHs, Matrix.map_apply,
      Matrix.of_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    simp only [H, hankel, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
    rw [hzz, hzz, show (j : ℕ) + 1 + (l.succAbove l' : ℕ) = (j : ℕ) + (l.succAbove l' : ℕ) + 1 by
      ring]
    rw [pow_succ]
    ring
  choose D hD using hsub
  refine ⟨∑ l : Fin (k + 1), (-1) ^ (l : ℕ) *
    ((-(qq a b i : ℤ)) ^ (l : ℕ) * orb a b i + a * zz l) * D l, ?_⟩
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold hankelInv
  rw [show hankel a b i (k + 1) = H from rfl, hdet, Matrix.det_succ_row_zero, mul_sum]
  push_cast
  refine sum_congr rfl fun l _ => ?_
  rw [hD, hEH0]
  simp only [H, hankel, Matrix.of_apply, Fin.val_zero, zero_add]
  rw [hzz]
  field_simp
  ring

/-- **Positivity.** For `r ≤ N - i`, the Hankel matrix is positive definite. -/
theorem hankel_posDef (hba : b < a) {i r : ℕ} (hi : i < P a b) (hr : r ≤ P a b - i) :
    (hankel a b i r).PosDef := by
  obtain ⟨hwpos, -⟩ := wt_spec hba (P a b - 1 - i) i (by omega)
  set M := P a b - i
  set c : ℕ → ℝ := fun n => wt a b i n / qq a b (i + n)
  have hc : ∀ n < M, 0 < c n := fun n hn => by
    have := hwpos n hn
    have : (0 : ℝ) < qq a b (i + n) := by exact_mod_cast (qq_pos hba (by omega))
    positivity
  have hquad : ∀ x : Fin r → ℝ, x ⬝ᵥ (hankel a b i r *ᵥ x) =
      ∑ n ∈ range M, c n * (∑ j, x j * pt a b i n ^ (j : ℕ)) ^ 2 := by
    intro x
    calc x ⬝ᵥ (hankel a b i r *ᵥ x)
        = ∑ j : Fin r, ∑ l : Fin r, ∑ n ∈ range M, x j
            * (wt a b i n * pt a b i n ^ ((j : ℕ) + (l : ℕ)) /
            qq a b (i + n)) * x l := by
          simp only [dotProduct, Matrix.mulVec, hankel, Matrix.of_apply, hm, mul_sum, sum_mul]
          refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => sum_congr rfl fun n _ => ?_
          ring
      _ = ∑ j : Fin r, ∑ n ∈ range M, ∑ l : Fin r, x j
          * (wt a b i n * pt a b i n ^ ((j : ℕ) + (l : ℕ)) /
            qq a b (i + n)) * x l := sum_congr rfl fun j _ => sum_comm
      _ = ∑ n ∈ range M, ∑ j : Fin r, ∑ l : Fin r, x j
          * (wt a b i n * pt a b i n ^ ((j : ℕ) + (l : ℕ)) /
            qq a b (i + n)) * x l := sum_comm
      _ = ∑ n ∈ range M, c n * (∑ j, x j * pt a b i n ^ (j : ℕ)) ^ 2 := by
          refine sum_congr rfl fun n _ => ?_
          simp only [sq, sum_mul, mul_sum, c]
          refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
          rw [pow_add]; ring
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext j l; simp [hankel, add_comm]
  · intro x hx
    simp only [star_trivial]
    rw [hquad]
    have hnn : ∀ n ∈ range M, 0 ≤ c n * (∑ j, x j * pt a b i n ^ (j : ℕ)) ^ 2 :=
      fun n hn => mul_nonneg (hc n (mem_range.mp hn)).le (sq_nonneg _)
    by_contra hle
    push Not at hle
    have hzero := (sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm hle (sum_nonneg hnn))
    -- the Vandermonde system at the first `r` points forces `x = 0`
    set v : Fin r → ℝ := fun n => pt a b i n
    have hinj : Function.Injective v := by
      intro n n' h
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h' | h'
      · exact (pt_strictMono (a := a) (b := b) h' (by omega)).ne h
      · exact (pt_strictMono (a := a) (b := b) h' (by omega)).ne h.symm
    have hV : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
    apply hx
    apply Matrix.eq_zero_of_mulVec_eq_zero hV
    ext n
    have := hzero n (mem_range.mpr (by omega))
    have hcn := hc n (by omega)
    have : (∑ j, x j * pt a b i n ^ (j : ℕ)) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hcn.ne'
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply, v]
    rw [← this]
    refine sum_congr rfl fun j _ => ?_
    ring

/-- Hence `Iᵣ(i) > 0`. -/
theorem hankelInv_pos (hba : b < a) {i r : ℕ} (hi : i < P a b) (hr : r ≤ P a b - i) :
    0 < hankelInv a b i r := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  unfold hankelInv
  exact mul_pos ha (hankel_posDef hba hi hr).det_pos

/-- **The Hankel invariants are positive integers.** For `1 ≤ r ≤ N - i`, `Iᵣ(i) ∈ ℤ_{>0}`. -/
theorem hankelInv_pos_int (hba : b < a) {i r : ℕ} (hi : i < P a b) (hr : r ≤ P a b - i) :
    ∃ n : ℕ, 0 < n ∧ hankelInv a b i r = n := by
  obtain ⟨z, hz⟩ := hankelInv_int hba hi r
  have hpos := hankelInv_pos hba hi hr
  rw [hz] at hpos
  have hz0 : 0 < z := by exact_mod_cast hpos
  refine ⟨z.toNat, by omega, ?_⟩
  rw [hz]
  have : ((z.toNat : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg hz0.le]
  exact_mod_cast this.symm

end Hankel

/-! ### The first four invariants -/

section Identities

/-- The moments generated from remainders `β` and increments `k` by the moment recursion
`H_j(0) = β_j`, `H_j(s+1) = ∑_t C(s,t) k_j^{s-t} H_{j+1}(t)` (`hm_succ`). -/
noncomputable def momSeq (β k : ℕ → ℝ) : ℕ → ℕ → ℝ
  | j, 0 => β j
  | j, s + 1 => ∑ t : Fin (s + 1), (s.choose t : ℝ) * k j ^ (s - t) * momSeq β k (j + 1) t
termination_by _ s => s

lemma momSeq_zero (β k : ℕ → ℝ) (j : ℕ) : momSeq β k j 0 = β j := by rw [momSeq]

lemma momSeq_succ (β k : ℕ → ℝ) (j s : ℕ) : momSeq β k j (s + 1) =
    ∑ t ∈ range (s + 1), (s.choose t : ℝ) * k j ^ (s - t) * momSeq β k (j + 1) t := by
  rw [momSeq, Fin.sum_univ_eq_sum_range fun t => (s.choose t : ℝ) * k j ^ (s - t) *
    momSeq β k (j + 1) t]

/-- The rank-2 Hankel determinant, as an identity modulo the division relations. -/
theorem hankel2_alg (β k : ℕ → ℝ) (q : ℝ)
    (f : ∀ j < 2, (q + ∑ l ∈ range j, k l) * β j + β (j + 1) = 1) :
    (Matrix.of fun j l : Fin 2 => momSeq β k 0 (j + l)).det = β 0 - β 1 := by
  have f0 := f 0 (by norm_num)
  have f1 := f 1 (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add, add_zero] at f0 f1
  simp [Matrix.det_fin_two, momSeq_zero, momSeq_succ, sum_range_succ]
  linear_combination (β 0) * f1 + (-β 1) * f0

/-- The rank-3 Hankel determinant, as an identity modulo the division relations. -/
theorem hankel3_alg (β k : ℕ → ℝ) (q : ℝ)
    (f : ∀ j < 4, (q + ∑ l ∈ range j, k l) * β j + β (j + 1) = 1) :
    (Matrix.of fun j l : Fin 3 => momSeq β k 0 (j + l)).det = β 0*k 1 - β 1*k 0 - β 1*k 1
      + β 2*k 0 := by
  have f0 := f 0 (by norm_num)
  have f1 := f 1 (by norm_num)
  have f2 := f 2 (by norm_num)
  have f3 := f 3 (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add, add_zero] at f0 f1 f2 f3
  simp [Matrix.det_fin_three, momSeq_zero, momSeq_succ, sum_range_succ, Nat.choose]
  linear_combination (β 0*β 1*k 0 + β 0*β 2 - β 1^2) * f3 + (β 0*β 1*k 0*k 1 - β 0*β 1*k 0*q
      - β 0*β 2*k 0 - β 0*β 3 - β 0 - β 1^2*k 1 + β 1^2*q + 2*β 1*β 2) * f2 + (β 0*β 2*k 0*q
      + β 0*k 0*q + β 0*k 1 + β 0*q + β 0 - β 1*β 2*q + β 1*k 0 + 2*β 1 - β 2^2 - β 2 - k 0
      - 1) * f1 + (-β 1*k 0^2 - β 1*k 0*q - 2*β 1*k 0 - β 1*k 1 - β 1*q - β 1 + k 0 + 1) * f0

/-- The rank-4 Hankel determinant, as an identity modulo the division relations. -/
theorem hankel4_alg (β k : ℕ → ℝ) (q : ℝ)
    (f : ∀ j < 6, (q + ∑ l ∈ range j, k l) * β j + β (j + 1) = 1) :
    (Matrix.of fun j l : Fin 4 => momSeq β k 0 (j + l)).det = β 0*k 1^2*k 2 + β 0*k 1*k 2^2
      + β 0*k 1*k 3 - β 0*k 2^2 - β 1*k 0^2*k 2 - 2*β 1*k 0*k 1*k 2 - β 1*k 0*k 2^2 - β 1*k 0*k 3
      - β 1*k 1^2*k 2 - β 1*k 1*k 2^2 + β 1*k 1*k 2 - β 1*k 1*k 3 + β 1*k 2^2 + β 2*k 0^2*k 1
      + β 2*k 0^2*k 2 + β 2*k 0*k 1^2 + 2*β 2*k 0*k 1*k 2 + β 2*k 0*k 2^2 + β 2*k 0*k 2
      + β 2*k 0*k 3 - β 2*k 1^2 - β 2*k 1*k 2 - β 3*k 0^2*k 1 - β 3*k 0*k 1^2 - β 3*k 0*k 2
      + β 3*k 1^2 := by
  have f0 := f 0 (by norm_num)
  have f1 := f 1 (by norm_num)
  have f2 := f 2 (by norm_num)
  have f3 := f 3 (by norm_num)
  have f4 := f 4 (by norm_num)
  have f5 := f 5 (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add, add_zero] at f0 f1 f2 f3 f4 f5
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, momSeq_zero, momSeq_succ,
    sum_range_succ, Nat.choose]
  linear_combination (β 0*β 1*β 2*k 0^2*k 1 + β 0*β 1*β 2*k 0*k 1^2 + β 0*β 1*β 3*k 0^2
      + 2*β 0*β 1*β 3*k 0*k 1 + β 0*β 1*β 3*k 0*k 2 + β 0*β 1*β 4*k 0 - β 0*β 2^2*k 0^2
      - β 0*β 2^2*k 0*k 1 - β 0*β 2*β 3*k 0 + β 0*β 2*β 3*k 2 + β 0*β 2*β 4 - β 0*β 3^2
      - β 1^2*β 2*k 0*k 1 - β 1^2*β 2*k 1^2 - β 1^2*β 3*k 0 - 2*β 1^2*β 3*k 1 - β 1^2*β 3*k 2
      - β 1^2*β 4 + β 1*β 2^2*k 0 + 2*β 1*β 2^2*k 1 + 2*β 1*β 2*β 3 - β 2^3) * f5
      + (β 0*β 1*β 2*k 0^2*k 1^2 + 2*β 0*β 1*β 2*k 0^2*k 1*k 2 + β 0*β 1*β 2*k 0^2*k 1*k 3
      - β 0*β 1*β 2*k 0^2*k 1*q + β 0*β 1*β 2*k 0*k 1^3 + 2*β 0*β 1*β 2*k 0*k 1^2*k 2
      + β 0*β 1*β 2*k 0*k 1^2*k 3 - β 0*β 1*β 2*k 0*k 1^2*q - β 0*β 1*β 3*k 0^2*k 1
      + β 0*β 1*β 3*k 0^2*k 3 - β 0*β 1*β 3*k 0^2*q + β 0*β 1*β 3*k 0*k 1*k 2
      + 2*β 0*β 1*β 3*k 0*k 1*k 3 - 2*β 0*β 1*β 3*k 0*k 1*q + β 0*β 1*β 3*k 0*k 2*k 3
      - β 0*β 1*β 3*k 0*k 2*q - β 0*β 1*β 4*k 0^2 - 2*β 0*β 1*β 4*k 0*k 1 - β 0*β 1*β 4*k 0*k 2
      - β 0*β 1*β 5*k 0 - β 0*β 1*k 0 - β 0*β 2^2*k 0^2*k 1 - 2*β 0*β 2^2*k 0^2*k 2
      - β 0*β 2^2*k 0^2*k 3 + β 0*β 2^2*k 0^2*q - β 0*β 2^2*k 0*k 1^2 - 2*β 0*β 2^2*k 0*k 1*k 2
      - β 0*β 2^2*k 0*k 1*k 3 + β 0*β 2^2*k 0*k 1*q + 2*β 0*β 2*β 3*k 0^2 + β 0*β 2*β 3*k 0*k 1
      - 2*β 0*β 2*β 3*k 0*k 2 - β 0*β 2*β 3*k 0*k 3 + β 0*β 2*β 3*k 0*q - β 0*β 2*β 3*k 1*k 2
      + β 0*β 2*β 3*k 2*k 3 - β 0*β 2*β 3*k 2*q + β 0*β 2*β 4*k 0 - β 0*β 2*β 4*k 2 - β 0*β 2*β 5
      - β 0*β 2 + 2*β 0*β 3^2*k 0 + β 0*β 3^2*k 1 - β 0*β 3^2*k 3 + β 0*β 3^2*q + 2*β 0*β 3*β 4
      - β 1^2*β 2*k 0*k 1^2 - 2*β 1^2*β 2*k 0*k 1*k 2 - β 1^2*β 2*k 0*k 1*k 3 + β 1^2*β 2*k 0*k 1*q
      - β 1^2*β 2*k 1^3 - 2*β 1^2*β 2*k 1^2*k 2 - β 1^2*β 2*k 1^2*k 3 + β 1^2*β 2*k 1^2*q
      + β 1^2*β 3*k 0*k 1 - β 1^2*β 3*k 0*k 3 + β 1^2*β 3*k 0*q - β 1^2*β 3*k 1*k 2
      - 2*β 1^2*β 3*k 1*k 3 + 2*β 1^2*β 3*k 1*q - β 1^2*β 3*k 2*k 3 + β 1^2*β 3*k 2*q
      + β 1^2*β 4*k 0 + 2*β 1^2*β 4*k 1 + β 1^2*β 4*k 2 + β 1^2*β 5 + β 1^2 + β 1*β 2^2*k 0*k 1
      + 2*β 1*β 2^2*k 0*k 2 + β 1*β 2^2*k 0*k 3 - β 1*β 2^2*k 0*q + 2*β 1*β 2^2*k 1^2
      + 4*β 1*β 2^2*k 1*k 2 + 2*β 1*β 2^2*k 1*k 3 - 2*β 1*β 2^2*k 1*q - 2*β 1*β 2*β 3*k 0
      - 2*β 1*β 2*β 3*k 1 + 2*β 1*β 2*β 3*k 2 + 2*β 1*β 2*β 3*k 3 - 2*β 1*β 2*β 3*q - 2*β 1*β 2*β 4
      - 2*β 1*β 3^2 - β 2^3*k 1 - 2*β 2^3*k 2 - β 2^3*k 3 + β 2^3*q + 2*β 2^2*β 3) * f4
      + (β 0*β 1*β 2*k 0^3*k 1*q + β 0*β 1*β 2*k 0^2*k 1^2*k 2 + β 0*β 1*β 2*k 0^2*k 1^2*q
      + β 0*β 1*β 2*k 0^2*k 1*k 2^2 - β 0*β 1*β 2*k 0^2*k 1*k 2*q + β 0*β 1*β 2*k 0^2*k 1*q^2
      + β 0*β 1*β 2*k 0*k 1^3*k 2 + β 0*β 1*β 2*k 0*k 1^2*k 2^2 - β 0*β 1*β 2*k 0*k 1^2*k 2*q
      + β 0*β 1*β 2*k 0*k 1^2*q^2 - β 0*β 1*β 3*k 0^2*k 1^2 - β 0*β 1*β 3*k 0^2*k 1*k 2
      + β 0*β 1*β 3*k 0^2*k 1*q - β 0*β 1*β 3*k 0*k 1^3 - β 0*β 1*β 3*k 0*k 1^2*k 2
      + β 0*β 1*β 3*k 0*k 1^2*q + β 0*β 1*β 4*k 0^2*q - β 0*β 1*β 4*k 0*k 1^2
      - β 0*β 1*β 4*k 0*k 1*k 2 + 2*β 0*β 1*β 4*k 0*k 1*q + β 0*β 1*β 4*k 0*k 2*q + β 0*β 1*k 0^2*q
      - β 0*β 1*k 0*k 1^2 - β 0*β 1*k 0*k 1*k 2 + 2*β 0*β 1*k 0*k 1*q - β 0*β 1*k 0*k 1
      + β 0*β 1*k 0*k 2*q + β 0*β 1*k 0*k 3 + β 0*β 1*k 0*q + β 0*β 1*k 0 - β 0*β 2^2*k 0^3*q
      - β 0*β 2^2*k 0^2*k 1*k 2 - β 0*β 2^2*k 0^2*k 1*q - β 0*β 2^2*k 0^2*k 2^2
      + β 0*β 2^2*k 0^2*k 2*q - β 0*β 2^2*k 0^2*q^2 - β 0*β 2^2*k 0*k 1^2*k 2
      - β 0*β 2^2*k 0*k 1*k 2^2 + β 0*β 2^2*k 0*k 1*k 2*q - β 0*β 2^2*k 0*k 1*q^2
      + β 0*β 2*β 3*k 0^2*k 1 + 2*β 0*β 2*β 3*k 0^2*k 2 - 2*β 0*β 2*β 3*k 0^2*q
      + β 0*β 2*β 3*k 0*k 1^2 + 2*β 0*β 2*β 3*k 0*k 1*k 2 - 2*β 0*β 2*β 3*k 0*k 1*q
      + β 0*β 2*β 4*k 0*k 1 + 2*β 0*β 2*β 4*k 0*k 2 - β 0*β 2*β 4*k 0*q + β 0*β 2*β 4*k 1*k 2
      + β 0*β 2*β 4*k 2*q + β 0*β 2*k 0*k 1 + 2*β 0*β 2*k 0*k 2 - β 0*β 2*k 0*q + 2*β 0*β 2*k 0
      + β 0*β 2*k 1*k 2 + β 0*β 2*k 1 + β 0*β 2*k 2*q + β 0*β 2*k 3 + β 0*β 2*q + β 0*β 2
      - β 0*β 3^2*k 0^2 - β 0*β 3^2*k 0*k 1 - 2*β 0*β 3*β 4*k 0 - β 0*β 3*β 4*k 1 - β 0*β 3*β 4*q
      - β 0*β 3*k 0 + β 0*β 3*k 2 + 2*β 0*β 3 - β 0*β 4^2 - β 0*β 4 - β 0 - β 1^2*β 2*k 0^2*k 1*q
      - β 1^2*β 2*k 0*k 1^2*k 2 - β 1^2*β 2*k 0*k 1^2*q - β 1^2*β 2*k 0*k 1*k 2^2
      + β 1^2*β 2*k 0*k 1*k 2*q - β 1^2*β 2*k 0*k 1*q^2 - β 1^2*β 2*k 1^3*k 2
      - β 1^2*β 2*k 1^2*k 2^2 + β 1^2*β 2*k 1^2*k 2*q - β 1^2*β 2*k 1^2*q^2 + β 1^2*β 3*k 0*k 1^2
      + β 1^2*β 3*k 0*k 1*k 2 - β 1^2*β 3*k 0*k 1*q + β 1^2*β 3*k 1^3 + β 1^2*β 3*k 1^2*k 2
      - β 1^2*β 3*k 1^2*q - β 1^2*β 4*k 0*q + β 1^2*β 4*k 1^2 + β 1^2*β 4*k 1*k 2
      - 2*β 1^2*β 4*k 1*q - β 1^2*β 4*k 2*q - β 1^2*k 0*q + β 1^2*k 1^2 + β 1^2*k 1*k 2
      - 2*β 1^2*k 1*q + β 1^2*k 1 - β 1^2*k 2*q - β 1^2*k 3 - β 1^2*q - β 1^2 + β 1*β 2^2*k 0^2*q
      + β 1*β 2^2*k 0*k 1*k 2 + 2*β 1*β 2^2*k 0*k 1*q + β 1*β 2^2*k 0*k 2^2 - β 1*β 2^2*k 0*k 2*q
      + β 1*β 2^2*k 0*q^2 + 2*β 1*β 2^2*k 1^2*k 2 + 2*β 1*β 2^2*k 1*k 2^2 - 2*β 1*β 2^2*k 1*k 2*q
      + 2*β 1*β 2^2*k 1*q^2 - 2*β 1*β 2*β 3*k 0*k 2 + 2*β 1*β 2*β 3*k 0*q - 2*β 1*β 2*β 3*k 1^2
      - 4*β 1*β 2*β 3*k 1*k 2 + 4*β 1*β 2*β 3*k 1*q - 2*β 1*β 2*β 4*k 1 - 2*β 1*β 2*β 4*k 2
      + 2*β 1*β 2*β 4*q - 2*β 1*β 2*k 1 - 2*β 1*β 2*k 2 + 2*β 1*β 2*q - 2*β 1*β 2 + β 1*β 3^2*k 0
      + 2*β 1*β 3^2*k 1 + 2*β 1*β 3*β 4 + 2*β 1*β 3 - β 2^3*k 0*q - β 2^3*k 1*k 2 - β 2^3*k 2^2
      + β 2^3*k 2*q - β 2^3*q^2 - β 2^2*β 3*k 0 + β 2^2*β 3*k 1 + 3*β 2^2*β 3*k 2 - 3*β 2^2*β 3*q
      + β 2^2*β 4 + β 2^2 - 3*β 2*β 3^2) * f3 + (-β 0*β 1*β 3*k 0^3*k 1*q
      - β 0*β 1*β 3*k 0^2*k 1^2*q - β 0*β 1*β 3*k 0^2*k 1*q^2 - β 0*β 1*β 3*k 0*k 1^2*q^2
      - β 0*β 1*k 0^3*k 1*q - β 0*β 1*k 0^3*q - β 0*β 1*k 0^2*k 1^2*q - β 0*β 1*k 0^2*k 1*q^2
      - 2*β 0*β 1*k 0^2*k 1*q - 2*β 0*β 1*k 0^2*k 2*q - β 0*β 1*k 0^2*q^2 - 2*β 0*β 1*k 0^2*q
      + β 0*β 1*k 0*k 1^2*k 2 - β 0*β 1*k 0*k 1^2*q^2 + β 0*β 1*k 0*k 1^2 + β 0*β 1*k 0*k 1*k 2^2
      - 2*β 0*β 1*k 0*k 1*k 2*q + 2*β 0*β 1*k 0*k 1*k 2 + β 0*β 1*k 0*k 1*k 3
      - 2*β 0*β 1*k 0*k 1*q^2 - 2*β 0*β 1*k 0*k 1*q + β 0*β 1*k 0*k 1 - β 0*β 1*k 0*k 2^2*q
      - β 0*β 1*k 0*k 2*q^2 - 2*β 0*β 1*k 0*k 2*q - β 0*β 1*k 0*k 3*q - β 0*β 1*k 0*q^2
      - β 0*β 1*k 0*q + β 0*β 2*β 3*k 0^3*q + β 0*β 2*β 3*k 0^2*k 1*q + β 0*β 2*β 3*k 0^2*q^2
      + β 0*β 2*β 3*k 0*k 1*q^2 - β 0*β 2*k 0^2*k 1*q - 2*β 0*β 2*k 0^2*q - β 0*β 2*k 0*k 1^2*q
      - β 0*β 2*k 0*k 1*k 2 - 3*β 0*β 2*k 0*k 1*q - β 0*β 2*k 0*k 1 - β 0*β 2*k 0*k 2^2
      - β 0*β 2*k 0*k 2*q - 2*β 0*β 2*k 0*k 2 - β 0*β 2*k 0*k 3 - β 0*β 2*k 0*q - β 0*β 2*k 0
      + β 0*β 3^2*k 0^2*q + β 0*β 3^2*k 0*k 1*q + β 0*β 3*k 0^2*q + β 0*β 3*k 0*k 1*q
      + β 0*β 3*k 0*q - β 0*β 3*k 1*k 2 - β 0*β 3*k 1 - β 0*β 3*k 2^2 - β 0*β 3*k 2*q
      - 2*β 0*β 3*k 2 - β 0*β 3*k 3 - β 0*β 3*q - β 0*β 3 + β 0*k 0^2*q + β 0*k 0*k 1*q + β 0*k 0*q
      - β 0*k 1*k 2 - β 0*k 2^2 - β 0*k 2*q - β 0*k 3 + β 0 + β 1^2*β 3*k 0^2*k 1*q
      + β 1^2*β 3*k 0*k 1^2*q + β 1^2*β 3*k 0*k 1*q^2 + β 1^2*β 3*k 1^2*q^2 + β 1^2*k 0^2*k 1*q
      + β 1^2*k 0^2*q + β 1^2*k 0*k 1^2*q + β 1^2*k 0*k 1*q^2 + 2*β 1^2*k 0*k 1*q
      + 2*β 1^2*k 0*k 2*q + β 1^2*k 0*q^2 + 2*β 1^2*k 0*q - β 1^2*k 1^2*k 2 + β 1^2*k 1^2*q^2
      - β 1^2*k 1^2 - β 1^2*k 1*k 2^2 + 2*β 1^2*k 1*k 2*q - 2*β 1^2*k 1*k 2 - β 1^2*k 1*k 3
      + 2*β 1^2*k 1*q^2 + 2*β 1^2*k 1*q - β 1^2*k 1 + β 1^2*k 2^2*q + β 1^2*k 2*q^2 + 2*β 1^2*k 2*q
      + β 1^2*k 3*q + β 1^2*q^2 + β 1^2*q - β 1*β 2*β 3*k 0^2*q - 2*β 1*β 2*β 3*k 0*k 1*q
      - β 1*β 2*β 3*k 0*q^2 - 2*β 1*β 2*β 3*k 1*q^2 + β 1*β 2*k 0^2*k 1 + β 1*β 2*k 0^2
      + β 1*β 2*k 0*k 1^2 + 2*β 1*β 2*k 0*k 1*q + 3*β 1*β 2*k 0*k 1 + 2*β 1*β 2*k 0*k 2
      + 3*β 1*β 2*k 0*q + 2*β 1*β 2*k 0 + 2*β 1*β 2*k 1^2*q + 2*β 1*β 2*k 1*k 2 + 6*β 1*β 2*k 1*q
      + 2*β 1*β 2*k 1 + 2*β 1*β 2*k 2^2 + 2*β 1*β 2*k 2*q + 4*β 1*β 2*k 2 + 2*β 1*β 2*k 3
      + 2*β 1*β 2*q + 2*β 1*β 2 - β 1*β 3^2*k 0*k 1 - β 1*β 3^2*k 0*q - 2*β 1*β 3^2*k 1*q
      - β 1*β 3*k 0*k 1 - β 1*β 3*k 0*q - β 1*β 3*k 0 - 2*β 1*β 3*k 1*q - 2*β 1*β 3*k 2
      - 2*β 1*β 3*q - 2*β 1*β 3 - β 1*k 0*k 1 - β 1*k 0*q - β 1*k 0 - 2*β 1*k 1*q - 2*β 1*k 2
      - 2*β 1*q + β 2^2*β 3*k 0*q + β 2^2*β 3*q^2 + β 2^2*k 0*k 1 + β 2^2*k 0 + β 2^2*k 1^2
      + 3*β 2^2*k 1 + 2*β 2^2*k 2 - β 2^2*q + 2*β 2^2 + β 2*β 3^2*k 0 + 2*β 2*β 3^2*q - β 2*β 3*k 1
      + β 2*β 3*q - 3*β 2*β 3 - β 2*k 0 - 2*β 2*k 1 - 3*β 2 + β 3^3 + β 3^2 + β 3 + k 0^2*k 1
      + k 0*k 1^2 + k 0*k 2 - k 1^2 + 1) * f2 + (β 0*β 2*k 0^3*k 1*q + β 0*β 2*k 0^3*q
      + 2*β 0*β 2*k 0^2*k 1^2*q + β 0*β 2*k 0^2*k 1*q^2 + 4*β 0*β 2*k 0^2*k 1*q
      + 2*β 0*β 2*k 0^2*k 2*q + β 0*β 2*k 0^2*q^2 + 2*β 0*β 2*k 0^2*q + β 0*β 2*k 0*k 1^3*q
      + β 0*β 2*k 0*k 1^2*q^2 + 3*β 0*β 2*k 0*k 1^2*q + 3*β 0*β 2*k 0*k 1*k 2*q
      + 2*β 0*β 2*k 0*k 1*q^2 + 3*β 0*β 2*k 0*k 1*q + β 0*β 2*k 0*k 2^2*q + β 0*β 2*k 0*k 2*q^2
      + 2*β 0*β 2*k 0*k 2*q + β 0*β 2*k 0*k 3*q + β 0*β 2*k 0*q^2 + β 0*β 2*k 0*q + β 0*k 0^3*k 1*q
      + 2*β 0*k 0^2*k 1^2*q + β 0*k 0^2*k 1*q^2 + β 0*k 0^2*k 1*q + 2*β 0*k 0^2*k 2*q - β 0*k 0^2*q
      + β 0*k 0*k 1^3*q + β 0*k 0*k 1^2*q^2 + β 0*k 0*k 1^2*q + 3*β 0*k 0*k 1*k 2*q
      + β 0*k 0*k 1*q^2 - β 0*k 0*k 1*q + β 0*k 0*k 2^2*q + β 0*k 0*k 2*q^2 + 2*β 0*k 0*k 2*q
      + β 0*k 0*k 3*q - β 0*k 0*q + β 0*k 1^2*k 2 + β 0*k 1*k 2^2 + 2*β 0*k 1*k 2*q + β 0*k 1*k 2
      + β 0*k 1*k 3 + β 0*k 2^2*q + β 0*k 2*q^2 + β 0*k 2*q + β 0*k 3*q + β 0*k 3
      - β 1*β 2*k 0^2*k 1*q - β 1*β 2*k 0^2*q - 2*β 1*β 2*k 0*k 1^2*q - β 1*β 2*k 0*k 1*q^2
      - 4*β 1*β 2*k 0*k 1*q - 2*β 1*β 2*k 0*k 2*q - β 1*β 2*k 0*q^2 - 2*β 1*β 2*k 0*q
      - β 1*β 2*k 1^3*q - β 1*β 2*k 1^2*q^2 - 3*β 1*β 2*k 1^2*q - 3*β 1*β 2*k 1*k 2*q
      - 2*β 1*β 2*k 1*q^2 - 3*β 1*β 2*k 1*q - β 1*β 2*k 2^2*q - β 1*β 2*k 2*q^2 - 2*β 1*β 2*k 2*q
      - β 1*β 2*k 3*q - β 1*β 2*q^2 - β 1*β 2*q + β 1*k 0^3*k 1 + 2*β 1*k 0^2*k 1^2
      + β 1*k 0^2*k 1*q + 2*β 1*k 0^2*k 1 + 2*β 1*k 0^2*k 2 + β 1*k 0*k 1^3 + β 1*k 0*k 1^2*q
      + 2*β 1*k 0*k 1^2 + 3*β 1*k 0*k 1*k 2 + 2*β 1*k 0*k 1*q + β 1*k 0*k 1 + β 1*k 0*k 2^2
      + β 1*k 0*k 2*q + 4*β 1*k 0*k 2 + β 1*k 0*k 3 + β 1*k 0*q + β 1*k 1^2*q + 4*β 1*k 1*k 2
      + 2*β 1*k 1*q + 2*β 1*k 2^2 + 2*β 1*k 2*q + 2*β 1*k 2 + 2*β 1*k 3 + β 1*q - β 2^2*k 0^2*k 1
      - β 2^2*k 0^2 - 2*β 2^2*k 0*k 1^2 - β 2^2*k 0*k 1*q - 4*β 2^2*k 0*k 1 - 2*β 2^2*k 0*k 2
      - β 2^2*k 0*q - 2*β 2^2*k 0 - β 2^2*k 1^3 - β 2^2*k 1^2*q - 3*β 2^2*k 1^2 - 3*β 2^2*k 1*k 2
      - 2*β 2^2*k 1*q - 3*β 2^2*k 1 - β 2^2*k 2^2 - β 2^2*k 2*q - 2*β 2^2*k 2 - β 2^2*k 3 - β 2^2*q
      - β 2^2 - β 2*k 0^2*k 1 - 2*β 2*k 0*k 1^2 - β 2*k 0*k 1*q - 2*β 2*k 0*k 2 + 2*β 2*k 0
      - β 2*k 1^3 - β 2*k 1^2*q - 3*β 2*k 1*k 2 + 3*β 2*k 1 - β 2*k 2^2 - β 2*k 2*q - β 2*k 3
      + β 2*q + 2*β 2 - k 0^3*k 1 - 2*k 0^2*k 1^2 - k 0^2*k 1*q - 2*k 0^2*k 1 - 2*k 0^2*k 2
      - k 0*k 1^3 - k 0*k 1^2*q - 2*k 0*k 1^2 - 3*k 0*k 1*k 2 - k 0*k 1*q - k 0*k 2^2 - k 0*k 2*q
      - 3*k 0*k 2 - k 0*k 3 + k 1^2 - 2*k 1*k 2 - k 2^2 - k 2*q - k 3 - 1) * f1 + (-β 1*k 0^4*k 1
      - 2*β 1*k 0^3*k 1^2 - 2*β 1*k 0^3*k 1*q - 2*β 1*k 0^3*k 1 - 2*β 1*k 0^3*k 2 - β 1*k 0^2*k 1^3
      - 3*β 1*k 0^2*k 1^2*q - 2*β 1*k 0^2*k 1^2 - 3*β 1*k 0^2*k 1*k 2 - β 1*k 0^2*k 1*q^2
      - 3*β 1*k 0^2*k 1*q - β 1*k 0^2*k 1 - β 1*k 0^2*k 2^2 - 3*β 1*k 0^2*k 2*q - 4*β 1*k 0^2*k 2
      - β 1*k 0^2*k 3 - β 1*k 0*k 1^3*q - β 1*k 0*k 1^2*q^2 - 2*β 1*k 0*k 1^2*q
      - 3*β 1*k 0*k 1*k 2*q - 4*β 1*k 0*k 1*k 2 - β 1*k 0*k 1*q^2 - β 1*k 0*k 1*q - β 1*k 0*k 2^2*q
      - 2*β 1*k 0*k 2^2 - β 1*k 0*k 2*q^2 - 4*β 1*k 0*k 2*q - 2*β 1*k 0*k 2 - β 1*k 0*k 3*q
      - 2*β 1*k 0*k 3 - β 1*k 1^2*k 2 - β 1*k 1*k 2^2 - 2*β 1*k 1*k 2*q - β 1*k 1*k 2 - β 1*k 1*k 3
      - β 1*k 2^2*q - β 1*k 2*q^2 - β 1*k 2*q - β 1*k 3*q - β 1*k 3 + k 0^3*k 1 + 2*k 0^2*k 1^2
      + k 0^2*k 1*q + k 0^2*k 1 + 2*k 0^2*k 2 + k 0*k 1^3 + k 0*k 1^2*q + k 0*k 1^2 + 3*k 0*k 1*k 2
      + k 0*k 1*q + k 0*k 2^2 + k 0*k 2*q + 2*k 0*k 2 + k 0*k 3 + 2*k 1*k 2 + k 2^2 + k 2*q
      + k 3) * f0

variable (a b : ℕ)

/-- The normalised remainder `βⱼ = b_{i+j} / a`. -/
noncomputable def βv (i j : ℕ) : ℝ := (orb a b (i + j) : ℝ) / a

/-- The increment `kᵢ = q_{i+1} - qᵢ`, as a real number. -/
noncomputable def kk (i : ℕ) : ℝ := (qq a b (i + 1) : ℝ) - qq a b i

/-- The increments `k_{i+j}` seen from state `i`: `kv a b i j` is `kk a b (i + j)`. -/
noncomputable abbrev kv (i j : ℕ) : ℝ := kk a b (i + j)

variable {a b}

/-- The moments `h_{i+j}(s)` are given by the moment recursion in `β` and `k`. -/
lemma hm_eq_momSeq (hba : b < a) {i : ℕ} (s : ℕ) : ∀ j, i + j < P a b → i + j + s ≤ P a b →
    hm a b (i + j) s = momSeq (βv a b i) (kv a b i) j s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro j hj hs
  rcases s with _ | s
  · rw [momSeq_zero, hm_zero hba (P a b - (i + j) - 1) (i + j) (by omega), βv]
  rw [momSeq_succ]
  by_cases hl : i + j + 1 < P a b
  · rw [hm_succ hl]
    refine sum_congr rfl fun t ht => ?_
    have := mem_range.mp ht
    have h := ih t (by omega) (j + 1) (by omega) (by omega)
    rw [← add_assoc] at h
    rw [h, kv, kk]
  · obtain rfl : s = 0 := by omega
    simp [hm_one hba hj, momSeq_zero, βv, add_assoc]

/-- The Hankel matrix in terms of `β` and `k`. -/
lemma hankel_eq_momSeq (hba : b < a) {i r : ℕ} (hi : i < P a b) (hr : i + 2 * (r - 1) ≤ P a b) :
    hankel a b i r = Matrix.of fun j l : Fin r => momSeq (βv a b i) (kv a b i) 0 (j + l) := by
  ext j l
  have := j.isLt
  have := l.isLt
  simpa [hankel] using hm_eq_momSeq hba (j + l) 0 (by omega) (by omega)

/-- The division equations `(qᵢ + k₀ + ⋯ + k_{j-1}) βⱼ + β_{j+1} = 1`. -/
lemma rel_sum (hba : b < a) {i j : ℕ} (hij : i + j < P a b) :
    ((qq a b i : ℝ) + ∑ l ∈ range j, kv a b i l) * βv a b i j + βv a b i (j + 1) = 1 := by
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hQ : ∀ j, (qq a b i : ℝ) + ∑ l ∈ range j, kv a b i l = qq a b (i + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [sum_range_succ, ← add_assoc, ih, kv, kk, ← add_assoc]; ring
  have e := orb_div (a := a) (b := b) (i := i + j) hij
  have e' : (orb a b (i + j) : ℝ) * qq a b (i + j) + orb a b (i + j + 1) = a := by exact_mod_cast e
  rw [hQ, βv, βv, ← add_assoc]
  field_simp
  linarith

/-- `I₁(i) = bᵢ`. -/
theorem hankelInv_one (hba : b < a) {i : ℕ} (hi : i < P a b) : hankelInv a b i 1 = orb a b i := by
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold hankelInv
  rw [Matrix.det_unique]
  simp only [hankel, Matrix.of_apply, Fin.default_eq_zero, Fin.val_zero, add_zero]
  rw [hm_zero hba (P a b - i - 1) i (by omega)]
  field_simp

theorem hankelInv_two (hba : b < a) {i : ℕ} (hi : i + 1 < P a b) :
    hankelInv a b i 2 = (orb a b i : ℝ) - orb a b (i + 1) := by
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold hankelInv
  rw [hankel_eq_momSeq hba (by omega) (by omega),
    hankel2_alg _ _ _ fun j hj => rel_sum hba (by omega)]
  unfold βv
  simp only [add_zero]
  field_simp

theorem hankelInv_three (hba : b < a) {i : ℕ} (hi : i + 3 < P a b) :
    hankelInv a b i 3 = ((orb a b i : ℝ) - orb a b (i + 1)) * kv a b i 1 -
      ((orb a b (i + 1) : ℝ) - orb a b (i + 2)) * kv a b i 0 := by
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold hankelInv
  rw [hankel_eq_momSeq hba (by omega) (by omega),
    hankel3_alg _ _ _ fun j hj => rel_sum hba (by omega)]
  unfold βv
  simp only [add_zero]
  field_simp
  ring

theorem hankelInv_four (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    hankelInv a b i 4 = ((sixL ((qq a b (i + 1) : ℤ) - qq a b i)
        ((qq a b (i + 2) : ℤ) - qq a b (i + 1))
      ((qq a b (i + 3) : ℤ) - qq a b (i + 2)) ((qq a b (i + 4) : ℤ) - qq a b (i + 3))
      ((orb a b i : ℤ) - orb a b (i + 1)) ((orb a b (i + 1) : ℤ) - orb a b (i + 2))
      ((orb a b (i + 2) : ℤ) - orb a b (i + 3)) : ℤ) : ℝ) := by
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold hankelInv
  rw [hankel_eq_momSeq hba (by omega) (by omega),
    hankel4_alg _ _ _ fun j hj => rel_sum hba (by omega)]
  unfold βv kv kk sixL
  simp only [add_zero]
  push_cast
  field_simp
  ring

end Identities

end PierceLengthBound
