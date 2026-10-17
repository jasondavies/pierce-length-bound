import PierceBound.SliceCount
import PierceBound.DefiniteNorm

/-!
# Ternary quadratics under linear substitution

A ternary quadratic is stored as its ten coefficients `c : Fin 10 → ℤ` in the order of `tern`.
`tcomp c C` is the quadratic `y ↦ F_c(C y)` (`ternv_tcomp`). Its discriminant
`disc3 = det(2S)` of the quadratic part scales by `det(C)²` (`disc3_tcomp`).

If `disc3 c ≠ 0`, a unimodular substitution with small inverse makes both the `x²` coefficient
and the discriminant of the binary part in `(x, y)` nonzero (`plane_one`, `plane_two`). The
slice count `slice_count_ne` then applies with the norm equation definite or indefinite
(`slice_count_tv`).
-/

namespace PierceBound

open Finset Matrix

/-- Evaluation of a ternary quadratic. -/
def ternv (c : Fin 10 → ℤ) (v : Fin 3 → ℤ) : ℤ :=
  tern (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) (c 9) (v 0) (v 1) (v 2)

/-- The quadratic part at a vector. -/
def quadv (c : Fin 10 → ℤ) (v : Fin 3 → ℤ) : ℤ :=
  c 0 * v 0 ^ 2 + c 1 * v 0 * v 1 + c 2 * v 1 ^ 2 + c 3 * v 0 * v 2 + c 5 * v 1 * v 2 + c 7 * v 2 ^ 2

/-- The polarised quadratic part. -/
def bilv (c : Fin 10 → ℤ) (v w : Fin 3 → ℤ) : ℤ :=
  2 * c 0 * v 0 * w 0 + c 1 * (v 0 * w 1 + v 1 * w 0) + 2 * c 2 * v 1 * w 1 +
    c 3 * (v 0 * w 2 + v 2 * w 0) + c 5 * (v 1 * w 2 + v 2 * w 1) + 2 * c 7 * v 2 * w 2

/-- The linear part at a vector. -/
def linv (c : Fin 10 → ℤ) (v : Fin 3 → ℤ) : ℤ := c 4 * v 0 + c 6 * v 1 + c 8 * v 2

/-- The quadratic `y ↦ F_c(C y)`. -/
def tcomp (c : Fin 10 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ) : Fin 10 → ℤ :=
  ![quadv c (fun i => C i 0), bilv c (fun i => C i 0) (fun i => C i 1), quadv c (fun i => C i 1),
    bilv c (fun i => C i 0) (fun i => C i 2), linv c (fun i => C i 0),
    bilv c (fun i => C i 1) (fun i => C i 2), linv c (fun i => C i 1), quadv c (fun i => C i 2),
    linv c (fun i => C i 2), c 9]

/-- `det(2S)` for the quadratic part `S`. -/
def disc3 (c : Fin 10 → ℤ) : ℤ :=
  8 * c 0 * c 2 * c 7 + 2 * c 1 * c 3 * c 5 - 2 * c 0 * c 5 ^ 2 - 2 * c 1 ^ 2 * c 7 -
    2 * c 2 * c 3 ^ 2

/-- The discriminant of the binary part in the first two variables. -/
def bdisc (c : Fin 10 → ℤ) : ℤ := c 1 ^ 2 - 4 * c 0 * c 2

lemma ternv_tcomp (c : Fin 10 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℤ) :
    ternv (tcomp c C) y = ternv c (C *ᵥ y) := by
  simp only [ternv, tcomp, tern, quadv, bilv, linv, mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  simp only [Matrix.cons_val]
  ring

lemma disc3_tcomp (c : Fin 10 → ℤ) (C : Matrix (Fin 3) (Fin 3) ℤ) :
    disc3 (tcomp c C) = disc3 c * C.det ^ 2 := by
  simp only [disc3, tcomp, quadv, bilv, Matrix.det_fin_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [Matrix.cons_val]
  ring

/-- The `z²` coefficient of `N(z)` is `-2α det(2S)`. -/
lemma lead_eq (c : Fin 10 → ℤ) :
    (c 1 * c 3 - 2 * c 0 * c 5) ^ 2 + (c 1 ^ 2 - 4 * c 0 * c 2) * (4 * c 0 * c 7 - c 3 ^ 2) =
      -2 * c 0 * disc3 c := by
  unfold disc3; ring

/-- A row-sum bound transfers sup-norm bounds. -/
lemma mulVec_abs_le {M : Matrix (Fin 3) (Fin 3) ℤ} {k : ℤ} (hM : ∀ i, ∑ j, |M i j| ≤ k)
    {y : Fin 3 → ℤ} {Y : ℤ} (hy : ∀ j, |y j| ≤ Y) (i : Fin 3) : |(M *ᵥ y) i| ≤ k * Y := by
  have hY : 0 ≤ Y := (abs_nonneg _).trans (hy 0)
  calc |(M *ᵥ y) i| = |∑ j, M i j * y j| := rfl
    _ ≤ ∑ j, |M i j * y j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * Y := sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * Y := by rw [sum_mul]
    _ ≤ k * Y := mul_le_mul_of_nonneg_right (hM i) hY

/-- A substitution with a small inverse. -/
def GoodSub (C Ci : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  C * Ci = 1 ∧ (∀ i, ∑ j, |Ci i j| ≤ 2) ∧ C.det ^ 2 = 1 ∧ ∀ i j, |C i j| ≤ 1

/-- **Choosing the plane.** -/
lemma plane_one (c : Fin 10 → ℤ) (hD : disc3 c ≠ 0) :
    ∃ C Ci, GoodSub C Ci ∧ bdisc (tcomp c C) ≠ 0 := by
  have key : bdisc c ≠ 0 ∨ c 3 ^ 2 - 4 * c 0 * c 7 ≠ 0 ∨ c 5 ^ 2 - 4 * c 2 * c 7 ≠ 0 ∨
      (c 3 + c 5) ^ 2 - 4 * (c 0 + c 1 + c 2) * c 7 ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    apply hD
    unfold bdisc at h1
    unfold disc3
    linear_combination 2 * c 7 * h1 - 2 * c 0 * h3 - 2 * c 2 * h2 + c 1 * (h4 - h2 - h3)
  rcases key with h | h | h | h
  · refine ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 0, 1], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · intro i; fin_cases i <;> simp [Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
    · intro i j; fin_cases i <;> fin_cases j <;> simp
    · convert h using 1
      simp [bdisc, tcomp, quadv, bilv]
  · refine ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · intro i; fin_cases i <;> simp [Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
    · intro i j; fin_cases i <;> fin_cases j <;> simp
    · convert h using 1
      simp [bdisc, tcomp, quadv, bilv]
  · refine ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · intro i; fin_cases i <;> simp [Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
    · intro i j; fin_cases i <;> fin_cases j <;> simp
    · convert h using 1
      simp [bdisc, tcomp, quadv, bilv]
  · refine ⟨!![1, 0, 0; 1, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; -1, 1, 0], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · intro i; fin_cases i <;> simp [Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
    · intro i j; fin_cases i <;> fin_cases j <;> simp
    · convert h using 1
      simp [bdisc, tcomp, quadv, bilv]

/-- **Choosing the first vector in the plane.** -/
lemma plane_two (c : Fin 10 → ℤ) (hΔ : bdisc c ≠ 0) :
    ∃ C Ci, GoodSub C Ci ∧ tcomp c C 0 ≠ 0 ∧ bdisc (tcomp c C) ≠ 0 := by
  by_cases h0 : c 0 ≠ 0
  · refine ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 0, 1], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · intro i; fin_cases i <;> simp [Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
    · intro i j; fin_cases i <;> fin_cases j <;> simp
    · simpa [tcomp, quadv] using h0
    · convert hΔ using 1
      simp [bdisc, tcomp, quadv, bilv]
  push Not at h0
  by_cases h2 : c 2 ≠ 0
  · refine ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    · intro i; fin_cases i <;> simp [Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
    · intro i j; fin_cases i <;> fin_cases j <;> simp
    · simpa [tcomp, quadv] using h2
    · convert hΔ using 1
      simp [bdisc, tcomp, quadv, bilv]; try ring
  push Not at h2
  have h1 : c 1 ≠ 0 := by
    intro h1; apply hΔ; unfold bdisc; rw [h0, h1]; ring
  refine ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], !![1, 0, 0; -1, 1, 0; 0, 0, 1], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · intro i; fin_cases i <;> simp [Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · simp [tcomp, quadv, h0, h2]; exact h1
  · convert hΔ using 1
    simp [bdisc, tcomp, quadv, bilv]; try ring

/-- **The slice count for a coefficient vector.** -/
theorem slice_count_tv {c : Fin 10 → ℤ} {K Y W : ℕ} (hY : 1 ≤ Y) (hα : c 0 ≠ 0)
    (hΔ : bdisc c ≠ 0) (hD : disc3 c ≠ 0) (hK : ∀ t, |c t| ≤ K)
    (hW : ∀ M : ℤ, M ≠ 0 → |M| ≤ 116 * K ^ 4 * Y ^ 2 →
      2 * M.natAbs.divisors.card ^ 3 * (Nat.log 3 ((11 * K ^ 2 * Y * (3 * K + 2)) ^ 2) + 1) ≤ W) :
    ((Fintype.piFinset fun _ : Fin 3 => ibox Y).filter fun v => ternv c v = 0).card ≤
      (2 * Y + 1) * (W + 4) := by
  have main : ∀ c' : Fin 10 → ℤ, 0 < c' 0 → bdisc c' ≠ 0 → disc3 c' ≠ 0 → (∀ t, |c' t| ≤ K) →
      (∀ v, ternv c v = 0 → ternv c' v = 0) →
      ((Fintype.piFinset fun _ : Fin 3 => ibox Y).filter fun v => ternv c v = 0).card ≤
        (2 * Y + 1) * (W + 4) := by
    intro c' h0 h1 h2 h3 h4
    refine le_trans (card_le_card_of_injOn (fun v => (v 0, v 1, v 2))
      (t := (ibox Y ×ˢ ibox Y ×ˢ ibox Y).filter fun p =>
        tern (c' 0) (c' 1) (c' 2) (c' 3) (c' 4) (c' 5) (c' 6) (c' 7) (c' 8) (c' 9)
          p.1 p.2.1 p.2.2 = 0) (fun v hv => ?_) (fun v _ v' _ h => ?_)) ?_
    · obtain ⟨hb, hz⟩ := mem_filter.mp (mem_coe.mp hv)
      have hb' := Fintype.mem_piFinset.mp hb
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hb' 0, mem_product.mpr ⟨hb' 1, hb' 2⟩⟩, h4 v hz⟩
    · simp only [Prod.mk.injEq] at h
      funext j; fin_cases j
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    · refine slice_count_ne hY h0 h1 ?_ ⟨h3 0, h3 1, h3 2, h3 3, h3 4, h3 5, h3 6, h3 7, h3 8, h3 9⟩
        hW
      have := lead_eq c'
      rw [this]
      exact mul_ne_zero (mul_ne_zero (by norm_num) h0.ne') h2
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · refine main (fun t => -c t) (by simp; linarith) ?_ ?_ (fun t => by simpa using hK t) ?_
    · intro h; apply hΔ; unfold bdisc at h ⊢; linear_combination h
    · intro h; apply hD; unfold disc3 at h ⊢; linear_combination -h
    · intro v hv; simp only [ternv, tern] at hv ⊢; linear_combination -hv
  · exact main c hpos hΔ hD hK fun v hv => hv

end PierceBound
