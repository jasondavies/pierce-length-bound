import PierceBound.SliceCount
import PierceBound.DefiniteNorm

/-!
# Ternary quadratics under linear substitution

A ternary quadratic is stored as its ten coefficients `c : Fin 10 → ℤ` in the order of `tern`.
`tcomp c C` is the quadratic `y ↦ F_c(C y)` (`ternv_tcomp`). Its discriminant
`disc3 = det(2S)` of the quadratic part scales by `det(C)²` (`disc3_tcomp`).

If `disc3 c ≠ 0`, a unimodular substitution with small inverse makes both the `x²` coefficient
and the discriminant of the binary part in `(x, y)` nonzero (`plane_choice`). The slice count
then applies with the norm equation definite or indefinite (`slice_count_pos`,
`slice_count_tv`).
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

set_option maxHeartbeats 1000000 in
/-- **The slice count** for either sign of the binary discriminant. -/
theorem slice_count_pos {α β γ d1 d0 e1 e0 f2 f1 f0 : ℤ} {K H W : ℕ} (hH : 1 ≤ H)
    (hα : 0 < α) (hΔ : β ^ 2 - 4 * α * γ ≠ 0)
    (hlead : (β * d1 - 2 * α * e1) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f2 - d1 ^ 2) ≠ 0)
    (hK : |α| ≤ K ∧ |β| ≤ K ∧ |γ| ≤ K ∧ |d1| ≤ K ∧ |d0| ≤ K ∧ |e1| ≤ K ∧ |e0| ≤ K ∧
      |f2| ≤ K ∧ |f1| ≤ K ∧ |f0| ≤ K)
    (hW : ∀ M : ℤ, M ≠ 0 → |M| ≤ 116 * K ^ 4 * H ^ 2 →
      4 * M.natAbs.divisors.card ^ 3 ≤ W ∧
      2 * M.natAbs.divisors.card ^ 3 * (Nat.log 3 ((11 * K ^ 2 * H * (3 * K + 2)) ^ 2) + 1) ≤ W) :
    ((ibox H ×ˢ ibox H ×ˢ ibox H).filter fun p =>
      tern α β γ d1 d0 e1 e0 f2 f1 f0 p.1 p.2.1 p.2.2 = 0).card ≤ (2 * H + 1) * (W + 4) := by
  classical
  set Δ := β ^ 2 - 4 * α * γ with hΔdef
  set S := (ibox H ×ˢ ibox H ×ˢ ibox H).filter fun p =>
    tern α β γ d1 d0 e1 e0 f2 f1 f0 p.1 p.2.1 p.2.2 = 0
  obtain ⟨kα, kβ, kγ, kd1, kd0, ke1, ke0, kf2, kf1, kf0⟩ := hK
  have hK1 : (1 : ℤ) ≤ K := by
    have : (1 : ℤ) ≤ |α| := by rw [abs_of_pos hα]; omega
    linarith
  -- the slice of a fixed `z`
  set slice : ℤ → Finset (ℤ × ℤ) := fun z => (ibox H ×ˢ ibox H).filter fun q =>
    tern α β γ d1 d0 e1 e0 f2 f1 f0 q.1 q.2 z = 0
  have hsplit : S.card = ∑ z ∈ ibox H, (slice z).card := by
    rw [card_eq_sum_card_fiberwise (f := fun p => p.2.2) (t := ibox H)
      (fun p hp => (mem_product.mp (mem_product.mp (mem_filter.mp hp).1).2).2)]
    refine sum_congr rfl fun z hz => ?_
    refine card_bij (fun p _ => (p.1, p.2.1)) (fun p hp => ?_) (fun p hp p' hp' h => ?_)
      (fun q hq => ?_)
    · obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
      obtain ⟨hpb, hpF⟩ := mem_filter.mp hp1
      obtain ⟨hx, hyz⟩ := mem_product.mp hpb
      obtain ⟨hy, -⟩ := mem_product.mp hyz
      refine mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, ?_⟩
      rw [← hp2]; exact hpF
    · have e1 := (mem_filter.mp hp).2
      have e2 := (mem_filter.mp hp').2
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2 (e1.trans e2.symm))
    · obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
      obtain ⟨hx, hy⟩ := mem_product.mp hq1
      refine ⟨(q.1, q.2, z), mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hx,
        mem_product.mpr ⟨hy, hz⟩⟩, hq2⟩, rfl⟩, rfl⟩
  have hΔ0 : Δ ≠ 0 := hΔ
  have hα0 : α ≠ 0 := hα.ne'
  -- size bounds on the box
  have bnd : ∀ x y z : ℤ, x ∈ ibox H → y ∈ ibox H → z ∈ ibox H →
      |2 * α * x + β * y + (d1 * z + d0)| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) ∧
      |Δ * y + (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) := by
    intro x y z hx hy hz
    have ax := abs_le_of_mem_ibox hx
    have ay := abs_le_of_mem_ibox hy
    have az := abs_le_of_mem_ibox hz
    have hH1 : (1 : ℤ) ≤ H := by exact_mod_cast hH
    have hKH : (K : ℤ) ≤ K * H := by nlinarith
    have m2 : ∀ a b : ℤ, ∀ A Bb : ℤ, |a| ≤ A → |b| ≤ Bb → |a * b| ≤ A * Bb := fun a b A Bb ha hb => by
      rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
    have hd : |d1 * z + d0| ≤ 2 * K * H := by
      have := m2 _ _ _ _ kd1 az
      calc |d1 * z + d0| ≤ |d1 * z| + |d0| := abs_add_le _ _
        _ ≤ K * H + K := add_le_add this kd0
        _ ≤ 2 * K * H := by linarith
    have he : |e1 * z + e0| ≤ 2 * K * H := by
      have := m2 _ _ _ _ ke1 az
      calc |e1 * z + e0| ≤ |e1 * z| + |e0| := abs_add_le _ _
        _ ≤ K * H + K := add_le_add this ke0
        _ ≤ 2 * K * H := by linarith
    have hDl : |Δ| ≤ 5 * K ^ 2 := by
      have h1 := m2 _ _ _ _ kβ kβ
      have h2 := m2 _ _ _ _ kα kγ
      calc |Δ| = |β * β - 4 * (α * γ)| := by rw [hΔdef]; ring_nf
        _ ≤ |β * β| + |4 * (α * γ)| := abs_sub _ _
        _ = |β * β| + 4 * |α * γ| := by rw [abs_mul (4 : ℤ)]; norm_num
        _ ≤ K * K + 4 * (K * K) := by linarith
        _ = 5 * K ^ 2 := by ring
    push_cast
    constructor
    · have t1 := m2 _ _ _ _ (show |2 * α| ≤ 2 * K by rw [abs_mul]; norm_num; linarith) ax
      have t2 := m2 _ _ _ _ kβ ay
      calc |2 * α * x + β * y + (d1 * z + d0)| ≤ |2 * α * x| + |β * y| + |d1 * z + d0| :=
            abs_add_three _ _ _
        _ ≤ 2 * K * H + K * H + 2 * K * H := by linarith
        _ ≤ 11 * K ^ 2 * H := by nlinarith
    · have t1 := m2 _ _ _ _ hDl ay
      have t2 := m2 _ _ _ _ kβ hd
      have t3 := m2 _ _ _ _ (show |2 * α| ≤ 2 * K by rw [abs_mul]; norm_num; linarith) he
      have s1 := abs_add_le (Δ * y) (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))
      have s2 := abs_sub (β * (d1 * z + d0)) (2 * α * (e1 * z + e0))
      have : 5 * (K : ℤ) ^ 2 * H + (K * (2 * K * H) + 2 * K * (2 * K * H)) = 11 * K ^ 2 * H := by
        ring
      linarith
  have hH1 : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hKH : (K : ℤ) ≤ K * H := by nlinarith
  have m2 : ∀ a b : ℤ, ∀ A Bb : ℤ, |a| ≤ A → |b| ≤ Bb → |a * b| ≤ A * Bb := fun a b A Bb ha hb => by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  have hDl : |Δ| ≤ 5 * K ^ 2 := by
    have h1 := m2 _ _ _ _ kβ kβ
    have h2 := m2 _ _ _ _ kα kγ
    calc |Δ| = |β * β - 4 * (α * γ)| := by rw [hΔdef]; ring_nf
      _ ≤ |β * β| + |4 * (α * γ)| := abs_sub _ _
      _ = |β * β| + 4 * |α * γ| := by rw [abs_mul (4 : ℤ)]; norm_num
      _ ≤ K * K + 4 * (K * K) := by linarith
      _ = 5 * K ^ 2 := by ring
  have hNb : ∀ z ∈ ibox H, |ternN α β γ d1 d0 e1 e0 f2 f1 f0 z| ≤ 116 * K ^ 4 * H ^ 2 := by
    intro z hz
    have az := abs_le_of_mem_ibox hz
    have hd : |d1 * z + d0| ≤ 2 * K * H := by
      have := m2 _ _ _ _ kd1 az
      calc |d1 * z + d0| ≤ |d1 * z| + |d0| := abs_add_le _ _
        _ ≤ K * H + K := add_le_add this kd0
        _ ≤ 2 * K * H := by linarith
    have he : |e1 * z + e0| ≤ 2 * K * H := by
      have := m2 _ _ _ _ ke1 az
      calc |e1 * z + e0| ≤ |e1 * z| + |e0| := abs_add_le _ _
        _ ≤ K * H + K := add_le_add this ke0
        _ ≤ 2 * K * H := by linarith
    have hf : |f2 * z ^ 2 + f1 * z + f0| ≤ 3 * (K : ℤ) * (H : ℤ) ^ 2 := by
      have t1 := m2 _ _ _ _ kf2 (show |z ^ 2| ≤ (H : ℤ) ^ 2 by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) az 2)
      have t2 := m2 _ _ _ _ kf1 az
      have s1 := abs_add_three (f2 * z ^ 2) (f1 * z) f0
      have : (K : ℤ) * H ≤ K * H ^ 2 := by nlinarith
      have : (K : ℤ) ≤ K * H ^ 2 := by nlinarith
      linarith
    have hΛ : |β * (d1 * z + d0) - 2 * α * (e1 * z + e0)| ≤ 6 * (K : ℤ) ^ 2 * H := by
      have t1 := m2 _ _ _ _ kβ hd
      have t2 := m2 _ _ _ _ (show |2 * α| ≤ 2 * K by rw [abs_mul]; norm_num; linarith) he
      have := abs_sub (β * (d1 * z + d0)) (2 * α * (e1 * z + e0))
      nlinarith
    have hQ : |4 * α * (f2 * z ^ 2 + f1 * z + f0) - (d1 * z + d0) ^ 2| ≤ 16 * (K : ℤ) ^ 2 * (H : ℤ) ^ 2 := by
      have t1 := m2 _ _ _ _ (show |4 * α| ≤ 4 * K by rw [abs_mul]; norm_num; linarith) hf
      have t2 : |(d1 * z + d0) ^ 2| ≤ (2 * (K : ℤ) * H) ^ 2 := by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      have := abs_sub (4 * α * (f2 * z ^ 2 + f1 * z + f0)) ((d1 * z + d0) ^ 2)
      nlinarith
    have t1 : |(β * (d1 * z + d0) - 2 * α * (e1 * z + e0)) ^ 2| ≤ (6 * (K : ℤ) ^ 2 * H) ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hΛ 2
    have t2 := m2 _ _ _ _ hDl hQ
    have e : ternN α β γ d1 d0 e1 e0 f2 f1 f0 z =
        (β * (d1 * z + d0) - 2 * α * (e1 * z + e0)) ^ 2 +
          Δ * (4 * α * (f2 * z ^ 2 + f1 * z + f0) - (d1 * z + d0) ^ 2) := by
      simp only [ternN, hΔdef]
    rw [e]
    calc _ ≤ |(β * (d1 * z + d0) - 2 * α * (e1 * z + e0)) ^ 2| +
          |Δ * (4 * α * (f2 * z ^ 2 + f1 * z + f0) - (d1 * z + d0) ^ 2)| := abs_add_le _ _
      _ ≤ (6 * (K : ℤ) ^ 2 * H) ^ 2 + 5 * (K : ℤ) ^ 2 * (16 * (K : ℤ) ^ 2 * (H : ℤ) ^ 2) :=
          add_le_add t1 t2
      _ = 116 * (K : ℤ) ^ 4 * (H : ℤ) ^ 2 := by ring
  -- a slice with `N(z) ≠ 0`
  have hgood : ∀ z ∈ ibox H, ternN α β γ d1 d0 e1 e0 f2 f1 f0 z ≠ 0 → (slice z).card ≤ W := by
    intro z hz hN
    have hinj : Set.InjOn (fun q : ℤ × ℤ => (Δ * q.2 + (β * (d1 * z + d0) -
        2 * α * (e1 * z + e0)), 2 * α * q.1 + β * q.2 + (d1 * z + d0))) (slice z) := by
      intro q hq q' hq' h
      simp only [Prod.mk.injEq] at h
      have hy : q.2 = q'.2 := by
        have : Δ * q.2 = Δ * q'.2 := by linarith
        exact mul_left_cancel₀ hΔ0 this
      have hx : q.1 = q'.1 := by
        have : (2 * α) * q.1 = (2 * α) * q'.1 := by rw [hy] at h; linarith
        exact mul_left_cancel₀ (by positivity) this
      exact Prod.ext hx hy
    have hbox : ∀ q ∈ slice z,
        |Δ * q.2 + (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) ∧
        |2 * α * q.1 + β * q.2 + (d1 * z + d0)| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) ∧
        (Δ * q.2 + (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))) ^ 2 -
          Δ * (2 * α * q.1 + β * q.2 + (d1 * z + d0)) ^ 2 =
          ternN α β γ d1 d0 e1 e0 f2 f1 f0 z := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
      obtain ⟨hx, hy⟩ := mem_product.mp hq1
      obtain ⟨b1, b2⟩ := bnd q.1 q.2 z hx hy hz
      refine ⟨b2, b1, ?_⟩
      have := slice_identity α β γ d1 d0 e1 e0 f2 f1 f0 q.1 q.2 z
      rw [hq2, mul_zero, sub_zero] at this
      exact this
    rcases lt_or_gt_of_ne hΔ0 with hneg | hpos
    · -- definite: `V² + |Δ| U² = N`
      have hDcast : (((-Δ).toNat : ℕ) : ℤ) = -Δ := Int.toNat_of_nonneg (by linarith)
      refine le_trans (card_le_card_of_injOn _ (t := defSols (-Δ).toNat
        (ternN α β γ d1 d0 e1 e0 f2 f1 f0 z) (11 * K ^ 2 * H)) (fun q hq => ?_) hinj)
        ((norm_count_def _ (by omega) hN).trans (hW _ hN (hNb z hz)).1)
      obtain ⟨b2, b1, hid⟩ := hbox q (mem_coe.mp hq)
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp b2), mem_Icc.mpr (abs_le.mp b1)⟩,
        ?_⟩
      simp only
      rw [hDcast]
      linear_combination hid
    · have hsqrt : Nat.sqrt Δ.toNat ≤ 3 * K := by
        have : Δ ≤ 5 * K ^ 2 := le_trans (le_abs_self _) hDl
        have h2 : (Δ.toNat : ℤ) ≤ (((3 * K) ^ 2 : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg hpos.le]; push_cast
          linarith [show ((3 : ℤ) * K) ^ 2 = 9 * (K : ℤ) ^ 2 by ring, sq_nonneg (K : ℤ)]
        have h3 : Δ.toNat ≤ (3 * K) ^ 2 := by exact_mod_cast h2
        calc Nat.sqrt Δ.toNat ≤ Nat.sqrt ((3 * K) ^ 2) := Nat.sqrt_le_sqrt h3
          _ = 3 * K := Nat.sqrt_eq' _
      have hD1 : 1 ≤ Δ.toNat := by omega
      have hDcast : ((Δ.toNat : ℕ) : ℤ) = Δ := Int.toNat_of_nonneg hpos.le
      refine le_trans (card_le_card_of_injOn _
        (t := normSols Δ.toNat (ternN α β γ d1 d0 e1 e0 f2 f1 f0 z) (11 * K ^ 2 * H))
        (fun q hq => ?_) hinj)
        ((norm_count _ hD1 hN).trans (le_trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ
          (Nat.log_mono_right (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) 2))))
          (hW _ hN (hNb z hz)).2))
      obtain ⟨b2, b1, hid⟩ := hbox q (mem_coe.mp hq)
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp b2), mem_Icc.mpr (abs_le.mp b1)⟩,
        ?_⟩
      simp only
      rw [hDcast]
      exact hid
  -- a slice with `N(z) = 0`
  have hbad : ∀ z ∈ ibox H, ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0 →
      (slice z).card ≤ 2 * (2 * H + 1) := by
    intro z hz hN
    refine (card_le_mul_card_image_of_maps_to (f := fun q => q.2) (t := ibox H)
      (fun q hq => (mem_product.mp (mem_filter.mp hq).1).2) 2 fun y _ => ?_).trans
      (by rw [card_ibox])
    set Fy := (slice z).filter fun q => q.2 = y
    rw [← card_image_of_injOn (f := fun q => q.1) (s := Fy) (fun q hq q' hq' h => Prod.ext h
      ((mem_filter.mp (mem_coe.mp hq)).2.trans (mem_filter.mp (mem_coe.mp hq')).2.symm))]
    refine card_le_two_of_quad (α := 4 * α ^ 2 * Δ) (β := 4 * α * Δ * (β * y + (d1 * z + d0)))
      (γ := Δ * (β * y + (d1 * z + d0)) ^ 2 - (Δ * y + (β * (d1 * z + d0) -
        2 * α * (e1 * z + e0))) ^ 2) (mul_ne_zero (by positivity) hΔ0) fun x hx => ?_
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    have hF := (mem_filter.mp hq1).2
    have := slice_identity α β γ d1 d0 e1 e0 f2 f1 f0 q.1 q.2 z
    rw [hF, hN, mul_zero, sub_zero, hq2, ← hΔdef] at this
    linear_combination -this
  -- at most two bad slices
  have hbadz : ((ibox H).filter fun z => ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0).card ≤ 2 :=
    card_le_two_of_quad hlead fun z hz => by
      have := (mem_filter.mp hz).2
      rw [ternN_eq] at this
      exact this
  rw [hsplit]
  calc ∑ z ∈ ibox H, (slice z).card
      ≤ ∑ z ∈ ibox H, (W + if ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0 then 2 * (2 * H + 1) else 0) := by
        refine sum_le_sum fun z hz => ?_
        by_cases hN : ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0
        · rw [ite_eq_left hN]; exact (hbad z hz hN).trans (Nat.le_add_left _ _)
        · rw [ite_eq_right hN, add_zero]; exact hgood z hz hN
    _ = (2 * H + 1) * W + ((ibox H).filter fun z => ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0).card *
          (2 * (2 * H + 1)) := by
        rw [sum_add_distrib, sum_const, card_ibox, smul_eq_mul, ← sum_filter, sum_const,
          smul_eq_mul]
    _ ≤ (2 * H + 1) * W + 2 * (2 * (2 * H + 1)) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hbadz) _
    _ = (2 * H + 1) * (W + 4) := by ring

/-- **The slice count for a coefficient vector.** -/
theorem slice_count_tv {c : Fin 10 → ℤ} {K Y W : ℕ} (hY : 1 ≤ Y) (hα : c 0 ≠ 0)
    (hΔ : bdisc c ≠ 0) (hD : disc3 c ≠ 0) (hK : ∀ t, |c t| ≤ K)
    (hW : ∀ M : ℤ, M ≠ 0 → |M| ≤ 116 * K ^ 4 * Y ^ 2 →
      4 * M.natAbs.divisors.card ^ 3 ≤ W ∧
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
    · refine slice_count_pos hY h0 h1 ?_ ⟨h3 0, h3 1, h3 2, h3 3, h3 4, h3 5, h3 6, h3 7, h3 8, h3 9⟩
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
