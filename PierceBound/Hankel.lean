import PierceBound.RisesMain

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

namespace PierceBound

open Finset

section Moments

variable (a b : ℕ)

/-- The quotient `qᵢ = ⌊a / bᵢ⌋`. -/
def qq (i : ℕ) : ℕ := a / orb a b i

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

lemma orb_pos_of_lt {i : ℕ} (hi : i < P a b) : 0 < orb a b i :=
  Nat.pos_of_ne_zero (orb_ne_zero_of_lt hi)

lemma orb_div {i : ℕ} (hi : i < P a b) : orb a b i * qq a b i + orb a b (i + 1) = a := by
  rw [orb_succ_of_ne (orb_ne_zero_of_lt hi)]; exact Nat.div_add_mod a _

lemma orb_last (hN : 1 ≤ P a b) : orb a b (P a b - 1) * qq a b (P a b - 1) = a := by
  have := orb_div (a := a) (b := b) (i := P a b - 1) (by omega)
  rw [show P a b - 1 + 1 = P a b by omega, orb_P] at this
  omega

lemma qq_lt {i : ℕ} (hi : i + 1 < P a b) : qq a b i < qq a b (i + 1) := by
  have e : a % orb a b i = orb a b (i + 1) := (orb_succ_of_ne (orb_ne_zero_of_lt (by omega))).symm
  have := div_lt_div_mod (a := a) (orb_pos_of_lt (by omega : i < P a b))
    (by rw [e]; exact orb_ne_zero_of_lt hi)
  rw [e] at this; exact this

lemma qq_pos (hba : b < a) {i : ℕ} (hi : i < P a b) : 1 ≤ qq a b i :=
  (Nat.le_div_iff_mul_le (orb_pos_of_lt hi)).mpr (by simpa using (orb_le a b i).trans hba.le)

lemma qq_le_of_le {i i' : ℕ} (hii : i ≤ i') (hi' : i' < P a b) : qq a b i ≤ qq a b i' := by
  induction i', hii using Nat.le_induction with
  | base => exact le_rfl
  | succ i' hii ih => exact (ih (by omega)).trans (qq_lt hi').le

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
      try ring
    rw [ih'] at key
    have e := orb_div (a := a) (b := b) (i := i) (by omega)
    have e' : (orb a b i : ℝ) * qq a b i + orb a b (i + 1) = a := by exact_mod_cast e
    rw [eq_div_iff ha.ne']
    field_simp at key
    nlinarith

lemma pt_zero (i : ℕ) : pt a b i 0 = 0 := by simp [pt]

/-- **The moment recursion** `hᵢ(s+1) = ∑_t C(s,t) kᵢ^{s-t} h_{i+1}(t)`. -/
theorem hm_succ (_hba : b < a) {i : ℕ} (hl : i + 1 < P a b) (s : ℕ) :
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
  · rw [hm_succ hba hl 0]
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
      rw [hm_succ hba hl s]
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
        = ∑ j : Fin r, ∑ l : Fin r, ∑ n ∈ range M, x j * (wt a b i n * pt a b i n ^ ((j : ℕ) + (l : ℕ)) /
            qq a b (i + n)) * x l := by
          simp only [dotProduct, Matrix.mulVec, hankel, Matrix.of_apply, hm, mul_sum, sum_mul]
          refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => sum_congr rfl fun n _ => ?_
          ring
      _ = ∑ j : Fin r, ∑ n ∈ range M, ∑ l : Fin r, x j * (wt a b i n * pt a b i n ^ ((j : ℕ) + (l : ℕ)) /
            qq a b (i + n)) * x l := sum_congr rfl fun j _ => sum_comm
      _ = ∑ n ∈ range M, ∑ j : Fin r, ∑ l : Fin r, x j * (wt a b i n * pt a b i n ^ ((j : ℕ) + (l : ℕ)) /
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

variable (a b : ℕ)

/-- The normalised remainder `βⱼ = b_{i+j} / a`. -/
noncomputable def βv (i j : ℕ) : ℝ := (orb a b (i + j) : ℝ) / a

/-- The quotient increment `k_{i+j} = q_{i+j+1} - q_{i+j}`, as a real number. -/
noncomputable def kv (i j : ℕ) : ℝ := (qq a b (i + j + 1) : ℝ) - qq a b (i + j)

variable {a b}

/-- The division equation `q_{i+j} β_j + β_{j+1} = 1`. -/
lemma rel_at (hba : b < a) {i j : ℕ} (hij : i + j < P a b) {Q : ℝ}
    (hQ : (qq a b (i + j) : ℝ) = Q) : Q * βv a b i j + βv a b i (j + 1) = 1 := by
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have e := orb_div (a := a) (b := b) (i := i + j) hij
  have e' : (orb a b (i + j) : ℝ) * qq a b (i + j) + orb a b (i + j + 1) = a := by exact_mod_cast e
  unfold βv
  rw [← hQ, show i + (j + 1) = i + j + 1 by ring]
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

/-- The rank-2 Hankel determinant, as an identity modulo the division relations. -/
theorem hankel2_alg (b0 b1 b2 q k0 _k1 : ℝ)
    (f0 : (q) * b0 + b1 = 1)
    (f1 : (q + k0) * b1 + b2 = 1) :
    Matrix.det !![(b0), (b1); (b1), (b1*k0 + b2)] = b0 - b1 := by
  rw [Matrix.det_fin_two_of]
  linear_combination (b0) * f1 + (-b1) * f0

/-- The rank-3 Hankel determinant, as an identity modulo the division relations. -/
theorem hankel3_alg (b0 b1 b2 b3 b4 q k0 k1 k2 _k3 : ℝ)
    (f0 : (q) * b0 + b1 = 1)
    (f1 : (q + k0) * b1 + b2 = 1)
    (f2 : (q + k0 + k1) * b2 + b3 = 1)
    (f3 : (q + k0 + k1 + k2) * b3 + b4 = 1) :
    Matrix.det !![(b0), (b1), (b1*k0 + b2); (b1), (b1*k0 + b2), (b1*k0^2 + 2*b2*k0 + b2*k1 + b3); (b1*k0 + b2), (b1*k0^2 + 2*b2*k0 + b2*k1 + b3), (b1*k0^3 + 3*b2*k0^2 + 3*b2*k0*k1 + b2*k1^2 + 3*b3*k0 + 2*b3*k1 + b3*k2 + b4)] = b0*k1 - b1*k0 - b1*k1 + b2*k0 := by
  simp [Matrix.det_fin_three]
  linear_combination (b0*b1*k0 + b0*b2 - b1^2) * f3 + (b0*b1*k0*k1 - b0*b1*k0*q - b0*b2*k0 - b0*b3 - b0 - b1^2*k1 + b1^2*q + 2*b1*b2) * f2 + (b0*b2*k0*q + b0*k0*q + b0*k1 + b0*q + b0 - b1*b2*q + b1*k0 + 2*b1 - b2^2 - b2 - k0 - 1) * f1 + (-b1*k0^2 - b1*k0*q - 2*b1*k0 - b1*k1 - b1*q - b1 + k0 + 1) * f0

/-- The rank-4 Hankel determinant, as an identity modulo the division relations. -/
theorem hankel4_alg (b0 b1 b2 b3 b4 b5 b6 q k0 k1 k2 k3 k4 _k5 : ℝ)
    (f0 : (q) * b0 + b1 = 1)
    (f1 : (q + k0) * b1 + b2 = 1)
    (f2 : (q + k0 + k1) * b2 + b3 = 1)
    (f3 : (q + k0 + k1 + k2) * b3 + b4 = 1)
    (f4 : (q + k0 + k1 + k2 + k3) * b4 + b5 = 1)
    (f5 : (q + k0 + k1 + k2 + k3 + k4) * b5 + b6 = 1) :
    Matrix.det !![(b0), (b1), (b1*k0 + b2), (b1*k0^2 + 2*b2*k0 + b2*k1 + b3); (b1), (b1*k0 + b2), (b1*k0^2 + 2*b2*k0 + b2*k1 + b3), (b1*k0^3 + 3*b2*k0^2 + 3*b2*k0*k1 + b2*k1^2 + 3*b3*k0 + 2*b3*k1 + b3*k2 + b4); (b1*k0 + b2), (b1*k0^2 + 2*b2*k0 + b2*k1 + b3), (b1*k0^3 + 3*b2*k0^2 + 3*b2*k0*k1 + b2*k1^2 + 3*b3*k0 + 2*b3*k1 + b3*k2 + b4), (b1*k0^4 + 4*b2*k0^3 + 6*b2*k0^2*k1 + 4*b2*k0*k1^2 + b2*k1^3 + 6*b3*k0^2 + 8*b3*k0*k1 + 4*b3*k0*k2 + 3*b3*k1^2 + 3*b3*k1*k2 + b3*k2^2 + 4*b4*k0 + 3*b4*k1 + 2*b4*k2 + b4*k3 + b5); (b1*k0^2 + 2*b2*k0 + b2*k1 + b3), (b1*k0^3 + 3*b2*k0^2 + 3*b2*k0*k1 + b2*k1^2 + 3*b3*k0 + 2*b3*k1 + b3*k2 + b4), (b1*k0^4 + 4*b2*k0^3 + 6*b2*k0^2*k1 + 4*b2*k0*k1^2 + b2*k1^3 + 6*b3*k0^2 + 8*b3*k0*k1 + 4*b3*k0*k2 + 3*b3*k1^2 + 3*b3*k1*k2 + b3*k2^2 + 4*b4*k0 + 3*b4*k1 + 2*b4*k2 + b4*k3 + b5), (b1*k0^5 + 5*b2*k0^4 + 10*b2*k0^3*k1 + 10*b2*k0^2*k1^2 + 5*b2*k0*k1^3 + b2*k1^4 + 10*b3*k0^3 + 20*b3*k0^2*k1 + 10*b3*k0^2*k2 + 15*b3*k0*k1^2 + 15*b3*k0*k1*k2 + 5*b3*k0*k2^2 + 4*b3*k1^3 + 6*b3*k1^2*k2 + 4*b3*k1*k2^2 + b3*k2^3 + 10*b4*k0^2 + 15*b4*k0*k1 + 10*b4*k0*k2 + 5*b4*k0*k3 + 6*b4*k1^2 + 8*b4*k1*k2 + 4*b4*k1*k3 + 3*b4*k2^2 + 3*b4*k2*k3 + b4*k3^2 + 5*b5*k0 + 4*b5*k1 + 3*b5*k2 + 2*b5*k3 + b5*k4 + b6)] = b0*k1^2*k2 + b0*k1*k2^2 + b0*k1*k3 - b0*k2^2 - b1*k0^2*k2 - 2*b1*k0*k1*k2 - b1*k0*k2^2 - b1*k0*k3 - b1*k1^2*k2 - b1*k1*k2^2 + b1*k1*k2 - b1*k1*k3 + b1*k2^2 + b2*k0^2*k1 + b2*k0^2*k2 + b2*k0*k1^2 + 2*b2*k0*k1*k2 + b2*k0*k2^2 + b2*k0*k2 + b2*k0*k3 - b2*k1^2 - b2*k1*k2 - b3*k0^2*k1 - b3*k0*k1^2 - b3*k0*k2 + b3*k1^2 := by
  rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  linear_combination (b0*b1*b2*k0^2*k1 + b0*b1*b2*k0*k1^2 + b0*b1*b3*k0^2 + 2*b0*b1*b3*k0*k1 + b0*b1*b3*k0*k2 + b0*b1*b4*k0 - b0*b2^2*k0^2 - b0*b2^2*k0*k1 - b0*b2*b3*k0 + b0*b2*b3*k2 + b0*b2*b4 - b0*b3^2 - b1^2*b2*k0*k1 - b1^2*b2*k1^2 - b1^2*b3*k0 - 2*b1^2*b3*k1 - b1^2*b3*k2 - b1^2*b4 + b1*b2^2*k0 + 2*b1*b2^2*k1 + 2*b1*b2*b3 - b2^3) * f5 + (b0*b1*b2*k0^2*k1^2 + 2*b0*b1*b2*k0^2*k1*k2 + b0*b1*b2*k0^2*k1*k3 - b0*b1*b2*k0^2*k1*q + b0*b1*b2*k0*k1^3 + 2*b0*b1*b2*k0*k1^2*k2 + b0*b1*b2*k0*k1^2*k3 - b0*b1*b2*k0*k1^2*q - b0*b1*b3*k0^2*k1 + b0*b1*b3*k0^2*k3 - b0*b1*b3*k0^2*q + b0*b1*b3*k0*k1*k2 + 2*b0*b1*b3*k0*k1*k3 - 2*b0*b1*b3*k0*k1*q + b0*b1*b3*k0*k2*k3 - b0*b1*b3*k0*k2*q - b0*b1*b4*k0^2 - 2*b0*b1*b4*k0*k1 - b0*b1*b4*k0*k2 - b0*b1*b5*k0 - b0*b1*k0 - b0*b2^2*k0^2*k1 - 2*b0*b2^2*k0^2*k2 - b0*b2^2*k0^2*k3 + b0*b2^2*k0^2*q - b0*b2^2*k0*k1^2 - 2*b0*b2^2*k0*k1*k2 - b0*b2^2*k0*k1*k3 + b0*b2^2*k0*k1*q + 2*b0*b2*b3*k0^2 + b0*b2*b3*k0*k1 - 2*b0*b2*b3*k0*k2 - b0*b2*b3*k0*k3 + b0*b2*b3*k0*q - b0*b2*b3*k1*k2 + b0*b2*b3*k2*k3 - b0*b2*b3*k2*q + b0*b2*b4*k0 - b0*b2*b4*k2 - b0*b2*b5 - b0*b2 + 2*b0*b3^2*k0 + b0*b3^2*k1 - b0*b3^2*k3 + b0*b3^2*q + 2*b0*b3*b4 - b1^2*b2*k0*k1^2 - 2*b1^2*b2*k0*k1*k2 - b1^2*b2*k0*k1*k3 + b1^2*b2*k0*k1*q - b1^2*b2*k1^3 - 2*b1^2*b2*k1^2*k2 - b1^2*b2*k1^2*k3 + b1^2*b2*k1^2*q + b1^2*b3*k0*k1 - b1^2*b3*k0*k3 + b1^2*b3*k0*q - b1^2*b3*k1*k2 - 2*b1^2*b3*k1*k3 + 2*b1^2*b3*k1*q - b1^2*b3*k2*k3 + b1^2*b3*k2*q + b1^2*b4*k0 + 2*b1^2*b4*k1 + b1^2*b4*k2 + b1^2*b5 + b1^2 + b1*b2^2*k0*k1 + 2*b1*b2^2*k0*k2 + b1*b2^2*k0*k3 - b1*b2^2*k0*q + 2*b1*b2^2*k1^2 + 4*b1*b2^2*k1*k2 + 2*b1*b2^2*k1*k3 - 2*b1*b2^2*k1*q - 2*b1*b2*b3*k0 - 2*b1*b2*b3*k1 + 2*b1*b2*b3*k2 + 2*b1*b2*b3*k3 - 2*b1*b2*b3*q - 2*b1*b2*b4 - 2*b1*b3^2 - b2^3*k1 - 2*b2^3*k2 - b2^3*k3 + b2^3*q + 2*b2^2*b3) * f4 + (b0*b1*b2*k0^3*k1*q + b0*b1*b2*k0^2*k1^2*k2 + b0*b1*b2*k0^2*k1^2*q + b0*b1*b2*k0^2*k1*k2^2 - b0*b1*b2*k0^2*k1*k2*q + b0*b1*b2*k0^2*k1*q^2 + b0*b1*b2*k0*k1^3*k2 + b0*b1*b2*k0*k1^2*k2^2 - b0*b1*b2*k0*k1^2*k2*q + b0*b1*b2*k0*k1^2*q^2 - b0*b1*b3*k0^2*k1^2 - b0*b1*b3*k0^2*k1*k2 + b0*b1*b3*k0^2*k1*q - b0*b1*b3*k0*k1^3 - b0*b1*b3*k0*k1^2*k2 + b0*b1*b3*k0*k1^2*q + b0*b1*b4*k0^2*q - b0*b1*b4*k0*k1^2 - b0*b1*b4*k0*k1*k2 + 2*b0*b1*b4*k0*k1*q + b0*b1*b4*k0*k2*q + b0*b1*k0^2*q - b0*b1*k0*k1^2 - b0*b1*k0*k1*k2 + 2*b0*b1*k0*k1*q - b0*b1*k0*k1 + b0*b1*k0*k2*q + b0*b1*k0*k3 + b0*b1*k0*q + b0*b1*k0 - b0*b2^2*k0^3*q - b0*b2^2*k0^2*k1*k2 - b0*b2^2*k0^2*k1*q - b0*b2^2*k0^2*k2^2 + b0*b2^2*k0^2*k2*q - b0*b2^2*k0^2*q^2 - b0*b2^2*k0*k1^2*k2 - b0*b2^2*k0*k1*k2^2 + b0*b2^2*k0*k1*k2*q - b0*b2^2*k0*k1*q^2 + b0*b2*b3*k0^2*k1 + 2*b0*b2*b3*k0^2*k2 - 2*b0*b2*b3*k0^2*q + b0*b2*b3*k0*k1^2 + 2*b0*b2*b3*k0*k1*k2 - 2*b0*b2*b3*k0*k1*q + b0*b2*b4*k0*k1 + 2*b0*b2*b4*k0*k2 - b0*b2*b4*k0*q + b0*b2*b4*k1*k2 + b0*b2*b4*k2*q + b0*b2*k0*k1 + 2*b0*b2*k0*k2 - b0*b2*k0*q + 2*b0*b2*k0 + b0*b2*k1*k2 + b0*b2*k1 + b0*b2*k2*q + b0*b2*k3 + b0*b2*q + b0*b2 - b0*b3^2*k0^2 - b0*b3^2*k0*k1 - 2*b0*b3*b4*k0 - b0*b3*b4*k1 - b0*b3*b4*q - b0*b3*k0 + b0*b3*k2 + 2*b0*b3 - b0*b4^2 - b0*b4 - b0 - b1^2*b2*k0^2*k1*q - b1^2*b2*k0*k1^2*k2 - b1^2*b2*k0*k1^2*q - b1^2*b2*k0*k1*k2^2 + b1^2*b2*k0*k1*k2*q - b1^2*b2*k0*k1*q^2 - b1^2*b2*k1^3*k2 - b1^2*b2*k1^2*k2^2 + b1^2*b2*k1^2*k2*q - b1^2*b2*k1^2*q^2 + b1^2*b3*k0*k1^2 + b1^2*b3*k0*k1*k2 - b1^2*b3*k0*k1*q + b1^2*b3*k1^3 + b1^2*b3*k1^2*k2 - b1^2*b3*k1^2*q - b1^2*b4*k0*q + b1^2*b4*k1^2 + b1^2*b4*k1*k2 - 2*b1^2*b4*k1*q - b1^2*b4*k2*q - b1^2*k0*q + b1^2*k1^2 + b1^2*k1*k2 - 2*b1^2*k1*q + b1^2*k1 - b1^2*k2*q - b1^2*k3 - b1^2*q - b1^2 + b1*b2^2*k0^2*q + b1*b2^2*k0*k1*k2 + 2*b1*b2^2*k0*k1*q + b1*b2^2*k0*k2^2 - b1*b2^2*k0*k2*q + b1*b2^2*k0*q^2 + 2*b1*b2^2*k1^2*k2 + 2*b1*b2^2*k1*k2^2 - 2*b1*b2^2*k1*k2*q + 2*b1*b2^2*k1*q^2 - 2*b1*b2*b3*k0*k2 + 2*b1*b2*b3*k0*q - 2*b1*b2*b3*k1^2 - 4*b1*b2*b3*k1*k2 + 4*b1*b2*b3*k1*q - 2*b1*b2*b4*k1 - 2*b1*b2*b4*k2 + 2*b1*b2*b4*q - 2*b1*b2*k1 - 2*b1*b2*k2 + 2*b1*b2*q - 2*b1*b2 + b1*b3^2*k0 + 2*b1*b3^2*k1 + 2*b1*b3*b4 + 2*b1*b3 - b2^3*k0*q - b2^3*k1*k2 - b2^3*k2^2 + b2^3*k2*q - b2^3*q^2 - b2^2*b3*k0 + b2^2*b3*k1 + 3*b2^2*b3*k2 - 3*b2^2*b3*q + b2^2*b4 + b2^2 - 3*b2*b3^2) * f3 + (-b0*b1*b3*k0^3*k1*q - b0*b1*b3*k0^2*k1^2*q - b0*b1*b3*k0^2*k1*q^2 - b0*b1*b3*k0*k1^2*q^2 - b0*b1*k0^3*k1*q - b0*b1*k0^3*q - b0*b1*k0^2*k1^2*q - b0*b1*k0^2*k1*q^2 - 2*b0*b1*k0^2*k1*q - 2*b0*b1*k0^2*k2*q - b0*b1*k0^2*q^2 - 2*b0*b1*k0^2*q + b0*b1*k0*k1^2*k2 - b0*b1*k0*k1^2*q^2 + b0*b1*k0*k1^2 + b0*b1*k0*k1*k2^2 - 2*b0*b1*k0*k1*k2*q + 2*b0*b1*k0*k1*k2 + b0*b1*k0*k1*k3 - 2*b0*b1*k0*k1*q^2 - 2*b0*b1*k0*k1*q + b0*b1*k0*k1 - b0*b1*k0*k2^2*q - b0*b1*k0*k2*q^2 - 2*b0*b1*k0*k2*q - b0*b1*k0*k3*q - b0*b1*k0*q^2 - b0*b1*k0*q + b0*b2*b3*k0^3*q + b0*b2*b3*k0^2*k1*q + b0*b2*b3*k0^2*q^2 + b0*b2*b3*k0*k1*q^2 - b0*b2*k0^2*k1*q - 2*b0*b2*k0^2*q - b0*b2*k0*k1^2*q - b0*b2*k0*k1*k2 - 3*b0*b2*k0*k1*q - b0*b2*k0*k1 - b0*b2*k0*k2^2 - b0*b2*k0*k2*q - 2*b0*b2*k0*k2 - b0*b2*k0*k3 - b0*b2*k0*q - b0*b2*k0 + b0*b3^2*k0^2*q + b0*b3^2*k0*k1*q + b0*b3*k0^2*q + b0*b3*k0*k1*q + b0*b3*k0*q - b0*b3*k1*k2 - b0*b3*k1 - b0*b3*k2^2 - b0*b3*k2*q - 2*b0*b3*k2 - b0*b3*k3 - b0*b3*q - b0*b3 + b0*k0^2*q + b0*k0*k1*q + b0*k0*q - b0*k1*k2 - b0*k2^2 - b0*k2*q - b0*k3 + b0 + b1^2*b3*k0^2*k1*q + b1^2*b3*k0*k1^2*q + b1^2*b3*k0*k1*q^2 + b1^2*b3*k1^2*q^2 + b1^2*k0^2*k1*q + b1^2*k0^2*q + b1^2*k0*k1^2*q + b1^2*k0*k1*q^2 + 2*b1^2*k0*k1*q + 2*b1^2*k0*k2*q + b1^2*k0*q^2 + 2*b1^2*k0*q - b1^2*k1^2*k2 + b1^2*k1^2*q^2 - b1^2*k1^2 - b1^2*k1*k2^2 + 2*b1^2*k1*k2*q - 2*b1^2*k1*k2 - b1^2*k1*k3 + 2*b1^2*k1*q^2 + 2*b1^2*k1*q - b1^2*k1 + b1^2*k2^2*q + b1^2*k2*q^2 + 2*b1^2*k2*q + b1^2*k3*q + b1^2*q^2 + b1^2*q - b1*b2*b3*k0^2*q - 2*b1*b2*b3*k0*k1*q - b1*b2*b3*k0*q^2 - 2*b1*b2*b3*k1*q^2 + b1*b2*k0^2*k1 + b1*b2*k0^2 + b1*b2*k0*k1^2 + 2*b1*b2*k0*k1*q + 3*b1*b2*k0*k1 + 2*b1*b2*k0*k2 + 3*b1*b2*k0*q + 2*b1*b2*k0 + 2*b1*b2*k1^2*q + 2*b1*b2*k1*k2 + 6*b1*b2*k1*q + 2*b1*b2*k1 + 2*b1*b2*k2^2 + 2*b1*b2*k2*q + 4*b1*b2*k2 + 2*b1*b2*k3 + 2*b1*b2*q + 2*b1*b2 - b1*b3^2*k0*k1 - b1*b3^2*k0*q - 2*b1*b3^2*k1*q - b1*b3*k0*k1 - b1*b3*k0*q - b1*b3*k0 - 2*b1*b3*k1*q - 2*b1*b3*k2 - 2*b1*b3*q - 2*b1*b3 - b1*k0*k1 - b1*k0*q - b1*k0 - 2*b1*k1*q - 2*b1*k2 - 2*b1*q + b2^2*b3*k0*q + b2^2*b3*q^2 + b2^2*k0*k1 + b2^2*k0 + b2^2*k1^2 + 3*b2^2*k1 + 2*b2^2*k2 - b2^2*q + 2*b2^2 + b2*b3^2*k0 + 2*b2*b3^2*q - b2*b3*k1 + b2*b3*q - 3*b2*b3 - b2*k0 - 2*b2*k1 - 3*b2 + b3^3 + b3^2 + b3 + k0^2*k1 + k0*k1^2 + k0*k2 - k1^2 + 1) * f2 + (b0*b2*k0^3*k1*q + b0*b2*k0^3*q + 2*b0*b2*k0^2*k1^2*q + b0*b2*k0^2*k1*q^2 + 4*b0*b2*k0^2*k1*q + 2*b0*b2*k0^2*k2*q + b0*b2*k0^2*q^2 + 2*b0*b2*k0^2*q + b0*b2*k0*k1^3*q + b0*b2*k0*k1^2*q^2 + 3*b0*b2*k0*k1^2*q + 3*b0*b2*k0*k1*k2*q + 2*b0*b2*k0*k1*q^2 + 3*b0*b2*k0*k1*q + b0*b2*k0*k2^2*q + b0*b2*k0*k2*q^2 + 2*b0*b2*k0*k2*q + b0*b2*k0*k3*q + b0*b2*k0*q^2 + b0*b2*k0*q + b0*k0^3*k1*q + 2*b0*k0^2*k1^2*q + b0*k0^2*k1*q^2 + b0*k0^2*k1*q + 2*b0*k0^2*k2*q - b0*k0^2*q + b0*k0*k1^3*q + b0*k0*k1^2*q^2 + b0*k0*k1^2*q + 3*b0*k0*k1*k2*q + b0*k0*k1*q^2 - b0*k0*k1*q + b0*k0*k2^2*q + b0*k0*k2*q^2 + 2*b0*k0*k2*q + b0*k0*k3*q - b0*k0*q + b0*k1^2*k2 + b0*k1*k2^2 + 2*b0*k1*k2*q + b0*k1*k2 + b0*k1*k3 + b0*k2^2*q + b0*k2*q^2 + b0*k2*q + b0*k3*q + b0*k3 - b1*b2*k0^2*k1*q - b1*b2*k0^2*q - 2*b1*b2*k0*k1^2*q - b1*b2*k0*k1*q^2 - 4*b1*b2*k0*k1*q - 2*b1*b2*k0*k2*q - b1*b2*k0*q^2 - 2*b1*b2*k0*q - b1*b2*k1^3*q - b1*b2*k1^2*q^2 - 3*b1*b2*k1^2*q - 3*b1*b2*k1*k2*q - 2*b1*b2*k1*q^2 - 3*b1*b2*k1*q - b1*b2*k2^2*q - b1*b2*k2*q^2 - 2*b1*b2*k2*q - b1*b2*k3*q - b1*b2*q^2 - b1*b2*q + b1*k0^3*k1 + 2*b1*k0^2*k1^2 + b1*k0^2*k1*q + 2*b1*k0^2*k1 + 2*b1*k0^2*k2 + b1*k0*k1^3 + b1*k0*k1^2*q + 2*b1*k0*k1^2 + 3*b1*k0*k1*k2 + 2*b1*k0*k1*q + b1*k0*k1 + b1*k0*k2^2 + b1*k0*k2*q + 4*b1*k0*k2 + b1*k0*k3 + b1*k0*q + b1*k1^2*q + 4*b1*k1*k2 + 2*b1*k1*q + 2*b1*k2^2 + 2*b1*k2*q + 2*b1*k2 + 2*b1*k3 + b1*q - b2^2*k0^2*k1 - b2^2*k0^2 - 2*b2^2*k0*k1^2 - b2^2*k0*k1*q - 4*b2^2*k0*k1 - 2*b2^2*k0*k2 - b2^2*k0*q - 2*b2^2*k0 - b2^2*k1^3 - b2^2*k1^2*q - 3*b2^2*k1^2 - 3*b2^2*k1*k2 - 2*b2^2*k1*q - 3*b2^2*k1 - b2^2*k2^2 - b2^2*k2*q - 2*b2^2*k2 - b2^2*k3 - b2^2*q - b2^2 - b2*k0^2*k1 - 2*b2*k0*k1^2 - b2*k0*k1*q - 2*b2*k0*k2 + 2*b2*k0 - b2*k1^3 - b2*k1^2*q - 3*b2*k1*k2 + 3*b2*k1 - b2*k2^2 - b2*k2*q - b2*k3 + b2*q + 2*b2 - k0^3*k1 - 2*k0^2*k1^2 - k0^2*k1*q - 2*k0^2*k1 - 2*k0^2*k2 - k0*k1^3 - k0*k1^2*q - 2*k0*k1^2 - 3*k0*k1*k2 - k0*k1*q - k0*k2^2 - k0*k2*q - 3*k0*k2 - k0*k3 + k1^2 - 2*k1*k2 - k2^2 - k2*q - k3 - 1) * f1 + (-b1*k0^4*k1 - 2*b1*k0^3*k1^2 - 2*b1*k0^3*k1*q - 2*b1*k0^3*k1 - 2*b1*k0^3*k2 - b1*k0^2*k1^3 - 3*b1*k0^2*k1^2*q - 2*b1*k0^2*k1^2 - 3*b1*k0^2*k1*k2 - b1*k0^2*k1*q^2 - 3*b1*k0^2*k1*q - b1*k0^2*k1 - b1*k0^2*k2^2 - 3*b1*k0^2*k2*q - 4*b1*k0^2*k2 - b1*k0^2*k3 - b1*k0*k1^3*q - b1*k0*k1^2*q^2 - 2*b1*k0*k1^2*q - 3*b1*k0*k1*k2*q - 4*b1*k0*k1*k2 - b1*k0*k1*q^2 - b1*k0*k1*q - b1*k0*k2^2*q - 2*b1*k0*k2^2 - b1*k0*k2*q^2 - 4*b1*k0*k2*q - 2*b1*k0*k2 - b1*k0*k3*q - 2*b1*k0*k3 - b1*k1^2*k2 - b1*k1*k2^2 - 2*b1*k1*k2*q - b1*k1*k2 - b1*k1*k3 - b1*k2^2*q - b1*k2*q^2 - b1*k2*q - b1*k3*q - b1*k3 + k0^3*k1 + 2*k0^2*k1^2 + k0^2*k1*q + k0^2*k1 + 2*k0^2*k2 + k0*k1^3 + k0*k1^2*q + k0*k1^2 + 3*k0*k1*k2 + k0*k1*q + k0*k2^2 + k0*k2*q + 2*k0*k2 + k0*k3 + 2*k1*k2 + k2^2 + k2*q + k3) * f0

theorem hankelInv_two (hba : b < a) {i : ℕ} (hi : i + 1 < P a b) :
    hankelInv a b i 2 = (orb a b i : ℝ) - orb a b (i + 1) := by
  have r0 : ∀ s, hm a b i (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 0 ^ (s - t) * hm a b (i + 1) t := fun s => hm_succ hba (i := i) (by omega) s
  have g1_0 : hm a b (i + 1) 0 = βv a b i 1 := hm_zero hba (P a b - ((i + 1)) - 1) (i + 1) (by omega)
  have g1_1 : hm a b (i + 1) 1 = βv a b i 2 := hm_one hba (i := (i + 1)) (by omega)
  have g0_0 : hm a b i 0 = βv a b i 0 := hm_zero hba (P a b - (i) - 1) i (by omega)
  have g0_1 : hm a b i 1 = βv a b i 1 := by
    rw [r0 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0]
    norm_num [Nat.choose]
  have g0_2 : hm a b i 2 = βv a b i 1*kv a b i 0 + βv a b i 2 := by
    rw [r0 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1]
    norm_num [Nat.choose]; try ring
  have f0 : ((qq a b i : ℝ)) * βv a b i 0 + βv a b i 1 = 1 := rel_at hba (i := i) (j := 0) (by omega) (by simp only [add_zero])
  have f1 : ((qq a b i : ℝ) + kv a b i 0) * βv a b i 1 + βv a b i 2 = 1 := rel_at hba (i := i) (j := 1) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have hH : hankel a b i 2 = !![(βv a b i 0), (βv a b i 1); (βv a b i 1), (βv a b i 1*kv a b i 0 + βv a b i 2)] := by
    ext j l; fin_cases j <;> fin_cases l <;> simp [hankel, g0_0, g0_1, g0_2]
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold hankelInv
  rw [hH, hankel2_alg (βv a b i 0) (βv a b i 1) (βv a b i 2) (qq a b i : ℝ) (kv a b i 0) (kv a b i 1) f0 f1]
  unfold βv
  simp only [add_zero]
  field_simp

theorem hankelInv_three (hba : b < a) {i : ℕ} (hi : i + 3 < P a b) :
    hankelInv a b i 3 = ((orb a b i : ℝ) - orb a b (i + 1)) * kv a b i 1 -
      ((orb a b (i + 1) : ℝ) - orb a b (i + 2)) * kv a b i 0 := by
  have r0 : ∀ s, hm a b i (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 0 ^ (s - t) * hm a b (i + 1) t := fun s => hm_succ hba (i := i) (by omega) s
  have r1 : ∀ s, hm a b (i + 1) (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 1 ^ (s - t) * hm a b (i + 2) t := fun s => hm_succ hba (i := (i + 1)) (by omega) s
  have r2 : ∀ s, hm a b (i + 2) (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 2 ^ (s - t) * hm a b (i + 3) t := fun s => hm_succ hba (i := (i + 2)) (by omega) s
  have g3_0 : hm a b (i + 3) 0 = βv a b i 3 := hm_zero hba (P a b - ((i + 3)) - 1) (i + 3) (by omega)
  have g3_1 : hm a b (i + 3) 1 = βv a b i 4 := hm_one hba (i := (i + 3)) (by omega)
  have g2_0 : hm a b (i + 2) 0 = βv a b i 2 := hm_zero hba (P a b - ((i + 2)) - 1) (i + 2) (by omega)
  have g2_1 : hm a b (i + 2) 1 = βv a b i 3 := by
    rw [r2 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g3_0]
    norm_num [Nat.choose]
  have g2_2 : hm a b (i + 2) 2 = βv a b i 3*kv a b i 2 + βv a b i 4 := by
    rw [r2 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g3_0, g3_1]
    norm_num [Nat.choose]; try ring
  have g1_0 : hm a b (i + 1) 0 = βv a b i 1 := hm_zero hba (P a b - ((i + 1)) - 1) (i + 1) (by omega)
  have g1_1 : hm a b (i + 1) 1 = βv a b i 2 := by
    rw [r1 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g2_0]
    norm_num [Nat.choose]
  have g1_2 : hm a b (i + 1) 2 = βv a b i 2*kv a b i 1 + βv a b i 3 := by
    rw [r1 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g2_0, g2_1]
    norm_num [Nat.choose]; try ring
  have g1_3 : hm a b (i + 1) 3 = βv a b i 2*kv a b i 1^2 + 2*βv a b i 3*kv a b i 1 + βv a b i 3*kv a b i 2 + βv a b i 4 := by
    rw [r1 2]; simp only [sum_range_succ, sum_range_zero, zero_add, g2_0, g2_1, g2_2]
    norm_num [Nat.choose]; try ring
  have g0_0 : hm a b i 0 = βv a b i 0 := hm_zero hba (P a b - (i) - 1) i (by omega)
  have g0_1 : hm a b i 1 = βv a b i 1 := by
    rw [r0 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0]
    norm_num [Nat.choose]
  have g0_2 : hm a b i 2 = βv a b i 1*kv a b i 0 + βv a b i 2 := by
    rw [r0 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1]
    norm_num [Nat.choose]; try ring
  have g0_3 : hm a b i 3 = βv a b i 1*kv a b i 0^2 + 2*βv a b i 2*kv a b i 0 + βv a b i 2*kv a b i 1 + βv a b i 3 := by
    rw [r0 2]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1, g1_2]
    norm_num [Nat.choose]; try ring
  have g0_4 : hm a b i 4 = βv a b i 1*kv a b i 0^3 + 3*βv a b i 2*kv a b i 0^2 + 3*βv a b i 2*kv a b i 0*kv a b i 1 + βv a b i 2*kv a b i 1^2 + 3*βv a b i 3*kv a b i 0 + 2*βv a b i 3*kv a b i 1 + βv a b i 3*kv a b i 2 + βv a b i 4 := by
    rw [r0 3]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1, g1_2, g1_3]
    norm_num [Nat.choose]; try ring
  have f0 : ((qq a b i : ℝ)) * βv a b i 0 + βv a b i 1 = 1 := rel_at hba (i := i) (j := 0) (by omega) (by simp only [add_zero])
  have f1 : ((qq a b i : ℝ) + kv a b i 0) * βv a b i 1 + βv a b i 2 = 1 := rel_at hba (i := i) (j := 1) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have f2 : ((qq a b i : ℝ) + kv a b i 0 + kv a b i 1) * βv a b i 2 + βv a b i 3 = 1 := rel_at hba (i := i) (j := 2) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have f3 : ((qq a b i : ℝ) + kv a b i 0 + kv a b i 1 + kv a b i 2) * βv a b i 3 + βv a b i 4 = 1 := rel_at hba (i := i) (j := 3) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have hH : hankel a b i 3 = !![(βv a b i 0), (βv a b i 1), (βv a b i 1*kv a b i 0 + βv a b i 2); (βv a b i 1), (βv a b i 1*kv a b i 0 + βv a b i 2), (βv a b i 1*kv a b i 0^2 + 2*βv a b i 2*kv a b i 0 + βv a b i 2*kv a b i 1 + βv a b i 3); (βv a b i 1*kv a b i 0 + βv a b i 2), (βv a b i 1*kv a b i 0^2 + 2*βv a b i 2*kv a b i 0 + βv a b i 2*kv a b i 1 + βv a b i 3), (βv a b i 1*kv a b i 0^3 + 3*βv a b i 2*kv a b i 0^2 + 3*βv a b i 2*kv a b i 0*kv a b i 1 + βv a b i 2*kv a b i 1^2 + 3*βv a b i 3*kv a b i 0 + 2*βv a b i 3*kv a b i 1 + βv a b i 3*kv a b i 2 + βv a b i 4)] := by
    ext j l; fin_cases j <;> fin_cases l <;> simp [hankel, g0_0, g0_1, g0_2, g0_3, g0_4]
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold hankelInv
  rw [hH, hankel3_alg (βv a b i 0) (βv a b i 1) (βv a b i 2) (βv a b i 3) (βv a b i 4) (qq a b i : ℝ) (kv a b i 0) (kv a b i 1) (kv a b i 2) (kv a b i 3) f0 f1 f2 f3]
  unfold βv
  simp only [add_zero]
  field_simp
  ring

theorem hankelInv_four (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    hankelInv a b i 4 = ((sixL ((qq a b (i + 1) : ℤ) - qq a b i) ((qq a b (i + 2) : ℤ) - qq a b (i + 1))
      ((qq a b (i + 3) : ℤ) - qq a b (i + 2)) ((qq a b (i + 4) : ℤ) - qq a b (i + 3))
      ((orb a b i : ℤ) - orb a b (i + 1)) ((orb a b (i + 1) : ℤ) - orb a b (i + 2))
      ((orb a b (i + 2) : ℤ) - orb a b (i + 3)) : ℤ) : ℝ) := by
  have r0 : ∀ s, hm a b i (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 0 ^ (s - t) * hm a b (i + 1) t := fun s => hm_succ hba (i := i) (by omega) s
  have r1 : ∀ s, hm a b (i + 1) (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 1 ^ (s - t) * hm a b (i + 2) t := fun s => hm_succ hba (i := (i + 1)) (by omega) s
  have r2 : ∀ s, hm a b (i + 2) (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 2 ^ (s - t) * hm a b (i + 3) t := fun s => hm_succ hba (i := (i + 2)) (by omega) s
  have r3 : ∀ s, hm a b (i + 3) (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 3 ^ (s - t) * hm a b (i + 4) t := fun s => hm_succ hba (i := (i + 3)) (by omega) s
  have r4 : ∀ s, hm a b (i + 4) (s + 1) = ∑ t ∈ range (s + 1), (s.choose t : ℝ) *
      kv a b i 4 ^ (s - t) * hm a b (i + 5) t := fun s => hm_succ hba (i := (i + 4)) (by omega) s
  have g5_0 : hm a b (i + 5) 0 = βv a b i 5 := hm_zero hba (P a b - ((i + 5)) - 1) (i + 5) (by omega)
  have g5_1 : hm a b (i + 5) 1 = βv a b i 6 := hm_one hba (i := (i + 5)) (by omega)
  have g4_0 : hm a b (i + 4) 0 = βv a b i 4 := hm_zero hba (P a b - ((i + 4)) - 1) (i + 4) (by omega)
  have g4_1 : hm a b (i + 4) 1 = βv a b i 5 := by
    rw [r4 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g5_0]
    norm_num [Nat.choose]
  have g4_2 : hm a b (i + 4) 2 = βv a b i 5*kv a b i 4 + βv a b i 6 := by
    rw [r4 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g5_0, g5_1]
    norm_num [Nat.choose]; try ring
  have g3_0 : hm a b (i + 3) 0 = βv a b i 3 := hm_zero hba (P a b - ((i + 3)) - 1) (i + 3) (by omega)
  have g3_1 : hm a b (i + 3) 1 = βv a b i 4 := by
    rw [r3 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g4_0]
    norm_num [Nat.choose]
  have g3_2 : hm a b (i + 3) 2 = βv a b i 4*kv a b i 3 + βv a b i 5 := by
    rw [r3 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g4_0, g4_1]
    norm_num [Nat.choose]; try ring
  have g3_3 : hm a b (i + 3) 3 = βv a b i 4*kv a b i 3^2 + 2*βv a b i 5*kv a b i 3 + βv a b i 5*kv a b i 4 + βv a b i 6 := by
    rw [r3 2]; simp only [sum_range_succ, sum_range_zero, zero_add, g4_0, g4_1, g4_2]
    norm_num [Nat.choose]; try ring
  have g2_0 : hm a b (i + 2) 0 = βv a b i 2 := hm_zero hba (P a b - ((i + 2)) - 1) (i + 2) (by omega)
  have g2_1 : hm a b (i + 2) 1 = βv a b i 3 := by
    rw [r2 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g3_0]
    norm_num [Nat.choose]
  have g2_2 : hm a b (i + 2) 2 = βv a b i 3*kv a b i 2 + βv a b i 4 := by
    rw [r2 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g3_0, g3_1]
    norm_num [Nat.choose]; try ring
  have g2_3 : hm a b (i + 2) 3 = βv a b i 3*kv a b i 2^2 + 2*βv a b i 4*kv a b i 2 + βv a b i 4*kv a b i 3 + βv a b i 5 := by
    rw [r2 2]; simp only [sum_range_succ, sum_range_zero, zero_add, g3_0, g3_1, g3_2]
    norm_num [Nat.choose]; try ring
  have g2_4 : hm a b (i + 2) 4 = βv a b i 3*kv a b i 2^3 + 3*βv a b i 4*kv a b i 2^2 + 3*βv a b i 4*kv a b i 2*kv a b i 3 + βv a b i 4*kv a b i 3^2 + 3*βv a b i 5*kv a b i 2 + 2*βv a b i 5*kv a b i 3 + βv a b i 5*kv a b i 4 + βv a b i 6 := by
    rw [r2 3]; simp only [sum_range_succ, sum_range_zero, zero_add, g3_0, g3_1, g3_2, g3_3]
    norm_num [Nat.choose]; try ring
  have g1_0 : hm a b (i + 1) 0 = βv a b i 1 := hm_zero hba (P a b - ((i + 1)) - 1) (i + 1) (by omega)
  have g1_1 : hm a b (i + 1) 1 = βv a b i 2 := by
    rw [r1 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g2_0]
    norm_num [Nat.choose]
  have g1_2 : hm a b (i + 1) 2 = βv a b i 2*kv a b i 1 + βv a b i 3 := by
    rw [r1 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g2_0, g2_1]
    norm_num [Nat.choose]; try ring
  have g1_3 : hm a b (i + 1) 3 = βv a b i 2*kv a b i 1^2 + 2*βv a b i 3*kv a b i 1 + βv a b i 3*kv a b i 2 + βv a b i 4 := by
    rw [r1 2]; simp only [sum_range_succ, sum_range_zero, zero_add, g2_0, g2_1, g2_2]
    norm_num [Nat.choose]; try ring
  have g1_4 : hm a b (i + 1) 4 = βv a b i 2*kv a b i 1^3 + 3*βv a b i 3*kv a b i 1^2 + 3*βv a b i 3*kv a b i 1*kv a b i 2 + βv a b i 3*kv a b i 2^2 + 3*βv a b i 4*kv a b i 1 + 2*βv a b i 4*kv a b i 2 + βv a b i 4*kv a b i 3 + βv a b i 5 := by
    rw [r1 3]; simp only [sum_range_succ, sum_range_zero, zero_add, g2_0, g2_1, g2_2, g2_3]
    norm_num [Nat.choose]; try ring
  have g1_5 : hm a b (i + 1) 5 = βv a b i 2*kv a b i 1^4 + 4*βv a b i 3*kv a b i 1^3 + 6*βv a b i 3*kv a b i 1^2*kv a b i 2 + 4*βv a b i 3*kv a b i 1*kv a b i 2^2 + βv a b i 3*kv a b i 2^3 + 6*βv a b i 4*kv a b i 1^2 + 8*βv a b i 4*kv a b i 1*kv a b i 2 + 4*βv a b i 4*kv a b i 1*kv a b i 3 + 3*βv a b i 4*kv a b i 2^2 + 3*βv a b i 4*kv a b i 2*kv a b i 3 + βv a b i 4*kv a b i 3^2 + 4*βv a b i 5*kv a b i 1 + 3*βv a b i 5*kv a b i 2 + 2*βv a b i 5*kv a b i 3 + βv a b i 5*kv a b i 4 + βv a b i 6 := by
    rw [r1 4]; simp only [sum_range_succ, sum_range_zero, zero_add, g2_0, g2_1, g2_2, g2_3, g2_4]
    norm_num [Nat.choose]; try ring
  have g0_0 : hm a b i 0 = βv a b i 0 := hm_zero hba (P a b - (i) - 1) i (by omega)
  have g0_1 : hm a b i 1 = βv a b i 1 := by
    rw [r0 0]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0]
    norm_num [Nat.choose]
  have g0_2 : hm a b i 2 = βv a b i 1*kv a b i 0 + βv a b i 2 := by
    rw [r0 1]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1]
    norm_num [Nat.choose]; try ring
  have g0_3 : hm a b i 3 = βv a b i 1*kv a b i 0^2 + 2*βv a b i 2*kv a b i 0 + βv a b i 2*kv a b i 1 + βv a b i 3 := by
    rw [r0 2]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1, g1_2]
    norm_num [Nat.choose]; try ring
  have g0_4 : hm a b i 4 = βv a b i 1*kv a b i 0^3 + 3*βv a b i 2*kv a b i 0^2 + 3*βv a b i 2*kv a b i 0*kv a b i 1 + βv a b i 2*kv a b i 1^2 + 3*βv a b i 3*kv a b i 0 + 2*βv a b i 3*kv a b i 1 + βv a b i 3*kv a b i 2 + βv a b i 4 := by
    rw [r0 3]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1, g1_2, g1_3]
    norm_num [Nat.choose]; try ring
  have g0_5 : hm a b i 5 = βv a b i 1*kv a b i 0^4 + 4*βv a b i 2*kv a b i 0^3 + 6*βv a b i 2*kv a b i 0^2*kv a b i 1 + 4*βv a b i 2*kv a b i 0*kv a b i 1^2 + βv a b i 2*kv a b i 1^3 + 6*βv a b i 3*kv a b i 0^2 + 8*βv a b i 3*kv a b i 0*kv a b i 1 + 4*βv a b i 3*kv a b i 0*kv a b i 2 + 3*βv a b i 3*kv a b i 1^2 + 3*βv a b i 3*kv a b i 1*kv a b i 2 + βv a b i 3*kv a b i 2^2 + 4*βv a b i 4*kv a b i 0 + 3*βv a b i 4*kv a b i 1 + 2*βv a b i 4*kv a b i 2 + βv a b i 4*kv a b i 3 + βv a b i 5 := by
    rw [r0 4]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1, g1_2, g1_3, g1_4]
    norm_num [Nat.choose]; try ring
  have g0_6 : hm a b i 6 = βv a b i 1*kv a b i 0^5 + 5*βv a b i 2*kv a b i 0^4 + 10*βv a b i 2*kv a b i 0^3*kv a b i 1 + 10*βv a b i 2*kv a b i 0^2*kv a b i 1^2 + 5*βv a b i 2*kv a b i 0*kv a b i 1^3 + βv a b i 2*kv a b i 1^4 + 10*βv a b i 3*kv a b i 0^3 + 20*βv a b i 3*kv a b i 0^2*kv a b i 1 + 10*βv a b i 3*kv a b i 0^2*kv a b i 2 + 15*βv a b i 3*kv a b i 0*kv a b i 1^2 + 15*βv a b i 3*kv a b i 0*kv a b i 1*kv a b i 2 + 5*βv a b i 3*kv a b i 0*kv a b i 2^2 + 4*βv a b i 3*kv a b i 1^3 + 6*βv a b i 3*kv a b i 1^2*kv a b i 2 + 4*βv a b i 3*kv a b i 1*kv a b i 2^2 + βv a b i 3*kv a b i 2^3 + 10*βv a b i 4*kv a b i 0^2 + 15*βv a b i 4*kv a b i 0*kv a b i 1 + 10*βv a b i 4*kv a b i 0*kv a b i 2 + 5*βv a b i 4*kv a b i 0*kv a b i 3 + 6*βv a b i 4*kv a b i 1^2 + 8*βv a b i 4*kv a b i 1*kv a b i 2 + 4*βv a b i 4*kv a b i 1*kv a b i 3 + 3*βv a b i 4*kv a b i 2^2 + 3*βv a b i 4*kv a b i 2*kv a b i 3 + βv a b i 4*kv a b i 3^2 + 5*βv a b i 5*kv a b i 0 + 4*βv a b i 5*kv a b i 1 + 3*βv a b i 5*kv a b i 2 + 2*βv a b i 5*kv a b i 3 + βv a b i 5*kv a b i 4 + βv a b i 6 := by
    rw [r0 5]; simp only [sum_range_succ, sum_range_zero, zero_add, g1_0, g1_1, g1_2, g1_3, g1_4, g1_5]
    norm_num [Nat.choose]; try ring
  have f0 : ((qq a b i : ℝ)) * βv a b i 0 + βv a b i 1 = 1 := rel_at hba (i := i) (j := 0) (by omega) (by simp only [add_zero])
  have f1 : ((qq a b i : ℝ) + kv a b i 0) * βv a b i 1 + βv a b i 2 = 1 := rel_at hba (i := i) (j := 1) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have f2 : ((qq a b i : ℝ) + kv a b i 0 + kv a b i 1) * βv a b i 2 + βv a b i 3 = 1 := rel_at hba (i := i) (j := 2) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have f3 : ((qq a b i : ℝ) + kv a b i 0 + kv a b i 1 + kv a b i 2) * βv a b i 3 + βv a b i 4 = 1 := rel_at hba (i := i) (j := 3) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have f4 : ((qq a b i : ℝ) + kv a b i 0 + kv a b i 1 + kv a b i 2 + kv a b i 3) * βv a b i 4 + βv a b i 5 = 1 := rel_at hba (i := i) (j := 4) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have f5 : ((qq a b i : ℝ) + kv a b i 0 + kv a b i 1 + kv a b i 2 + kv a b i 3 + kv a b i 4) * βv a b i 5 + βv a b i 6 = 1 := rel_at hba (i := i) (j := 5) (by omega) (by simp only [kv, add_zero]; try ring_nf)
  have hH : hankel a b i 4 = !![(βv a b i 0), (βv a b i 1), (βv a b i 1*kv a b i 0 + βv a b i 2), (βv a b i 1*kv a b i 0^2 + 2*βv a b i 2*kv a b i 0 + βv a b i 2*kv a b i 1 + βv a b i 3); (βv a b i 1), (βv a b i 1*kv a b i 0 + βv a b i 2), (βv a b i 1*kv a b i 0^2 + 2*βv a b i 2*kv a b i 0 + βv a b i 2*kv a b i 1 + βv a b i 3), (βv a b i 1*kv a b i 0^3 + 3*βv a b i 2*kv a b i 0^2 + 3*βv a b i 2*kv a b i 0*kv a b i 1 + βv a b i 2*kv a b i 1^2 + 3*βv a b i 3*kv a b i 0 + 2*βv a b i 3*kv a b i 1 + βv a b i 3*kv a b i 2 + βv a b i 4); (βv a b i 1*kv a b i 0 + βv a b i 2), (βv a b i 1*kv a b i 0^2 + 2*βv a b i 2*kv a b i 0 + βv a b i 2*kv a b i 1 + βv a b i 3), (βv a b i 1*kv a b i 0^3 + 3*βv a b i 2*kv a b i 0^2 + 3*βv a b i 2*kv a b i 0*kv a b i 1 + βv a b i 2*kv a b i 1^2 + 3*βv a b i 3*kv a b i 0 + 2*βv a b i 3*kv a b i 1 + βv a b i 3*kv a b i 2 + βv a b i 4), (βv a b i 1*kv a b i 0^4 + 4*βv a b i 2*kv a b i 0^3 + 6*βv a b i 2*kv a b i 0^2*kv a b i 1 + 4*βv a b i 2*kv a b i 0*kv a b i 1^2 + βv a b i 2*kv a b i 1^3 + 6*βv a b i 3*kv a b i 0^2 + 8*βv a b i 3*kv a b i 0*kv a b i 1 + 4*βv a b i 3*kv a b i 0*kv a b i 2 + 3*βv a b i 3*kv a b i 1^2 + 3*βv a b i 3*kv a b i 1*kv a b i 2 + βv a b i 3*kv a b i 2^2 + 4*βv a b i 4*kv a b i 0 + 3*βv a b i 4*kv a b i 1 + 2*βv a b i 4*kv a b i 2 + βv a b i 4*kv a b i 3 + βv a b i 5); (βv a b i 1*kv a b i 0^2 + 2*βv a b i 2*kv a b i 0 + βv a b i 2*kv a b i 1 + βv a b i 3), (βv a b i 1*kv a b i 0^3 + 3*βv a b i 2*kv a b i 0^2 + 3*βv a b i 2*kv a b i 0*kv a b i 1 + βv a b i 2*kv a b i 1^2 + 3*βv a b i 3*kv a b i 0 + 2*βv a b i 3*kv a b i 1 + βv a b i 3*kv a b i 2 + βv a b i 4), (βv a b i 1*kv a b i 0^4 + 4*βv a b i 2*kv a b i 0^3 + 6*βv a b i 2*kv a b i 0^2*kv a b i 1 + 4*βv a b i 2*kv a b i 0*kv a b i 1^2 + βv a b i 2*kv a b i 1^3 + 6*βv a b i 3*kv a b i 0^2 + 8*βv a b i 3*kv a b i 0*kv a b i 1 + 4*βv a b i 3*kv a b i 0*kv a b i 2 + 3*βv a b i 3*kv a b i 1^2 + 3*βv a b i 3*kv a b i 1*kv a b i 2 + βv a b i 3*kv a b i 2^2 + 4*βv a b i 4*kv a b i 0 + 3*βv a b i 4*kv a b i 1 + 2*βv a b i 4*kv a b i 2 + βv a b i 4*kv a b i 3 + βv a b i 5), (βv a b i 1*kv a b i 0^5 + 5*βv a b i 2*kv a b i 0^4 + 10*βv a b i 2*kv a b i 0^3*kv a b i 1 + 10*βv a b i 2*kv a b i 0^2*kv a b i 1^2 + 5*βv a b i 2*kv a b i 0*kv a b i 1^3 + βv a b i 2*kv a b i 1^4 + 10*βv a b i 3*kv a b i 0^3 + 20*βv a b i 3*kv a b i 0^2*kv a b i 1 + 10*βv a b i 3*kv a b i 0^2*kv a b i 2 + 15*βv a b i 3*kv a b i 0*kv a b i 1^2 + 15*βv a b i 3*kv a b i 0*kv a b i 1*kv a b i 2 + 5*βv a b i 3*kv a b i 0*kv a b i 2^2 + 4*βv a b i 3*kv a b i 1^3 + 6*βv a b i 3*kv a b i 1^2*kv a b i 2 + 4*βv a b i 3*kv a b i 1*kv a b i 2^2 + βv a b i 3*kv a b i 2^3 + 10*βv a b i 4*kv a b i 0^2 + 15*βv a b i 4*kv a b i 0*kv a b i 1 + 10*βv a b i 4*kv a b i 0*kv a b i 2 + 5*βv a b i 4*kv a b i 0*kv a b i 3 + 6*βv a b i 4*kv a b i 1^2 + 8*βv a b i 4*kv a b i 1*kv a b i 2 + 4*βv a b i 4*kv a b i 1*kv a b i 3 + 3*βv a b i 4*kv a b i 2^2 + 3*βv a b i 4*kv a b i 2*kv a b i 3 + βv a b i 4*kv a b i 3^2 + 5*βv a b i 5*kv a b i 0 + 4*βv a b i 5*kv a b i 1 + 3*βv a b i 5*kv a b i 2 + 2*βv a b i 5*kv a b i 3 + βv a b i 5*kv a b i 4 + βv a b i 6)] := by
    ext j l; fin_cases j <;> fin_cases l <;> simp [hankel, g0_0, g0_1, g0_2, g0_3, g0_4, g0_5, g0_6]
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  unfold hankelInv
  rw [hH, hankel4_alg (βv a b i 0) (βv a b i 1) (βv a b i 2) (βv a b i 3) (βv a b i 4) (βv a b i 5) (βv a b i 6) (qq a b i : ℝ) (kv a b i 0) (kv a b i 1) (kv a b i 2) (kv a b i 3) (kv a b i 4) (kv a b i 5) f0 f1 f2 f3 f4 f5]
  unfold βv kv sixL
  simp only [add_zero]
  push_cast
  field_simp
  ring

end Identities

end PierceBound
