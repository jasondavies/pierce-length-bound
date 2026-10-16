import Mathlib

/-!
# The iteration `x ↦ a mod x`

For integers `a > b > 0` put `b₁ = b` and `b_{i+1} = a mod bᵢ`. The sequence reaches `0`;
if `b_{n+1} = 0` then `P(a, b) = n` (Shallit, Open Problem Garden). Thus `P(a, b)` is the
number of positive terms of the sequence.

Here the sequence is indexed from `0`: `orb a b i = b_{i+1}`. Lean's `a % 0 = a`, so the
iteration is frozen at `0` explicitly (`step`).
-/

namespace PierceBound

/-- One step of the iteration, frozen at `0`. -/
def step (a x : ℕ) : ℕ := if x = 0 then 0 else a % x

/-- The orbit: `orb a b i = b_{i+1}`. -/
def orb (a b : ℕ) (i : ℕ) : ℕ := (step a)^[i] b

/-- `P(a, b)`: the number of positive terms of the orbit of `b` under `x ↦ a mod x`. -/
def P (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => P a (a % (b + 1)) + 1
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

@[simp] lemma step_zero (a : ℕ) : step a 0 = 0 := by simp [step]

lemma step_of_ne {a x : ℕ} (hx : x ≠ 0) : step a x = a % x := by simp [step, hx]

lemma step_le (a x : ℕ) : step a x ≤ x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [step_of_ne hx]; exact (Nat.mod_lt _ (Nat.pos_of_ne_zero hx)).le

@[simp] lemma orb_zero (a b : ℕ) : orb a b 0 = b := rfl

lemma orb_succ (a b i : ℕ) : orb a b (i + 1) = step a (orb a b i) :=
  Function.iterate_succ_apply' _ _ _

lemma orb_succ' (a b i : ℕ) : orb a b (i + 1) = orb a (step a b) i :=
  Function.iterate_succ_apply _ _ _

lemma orb_succ_of_ne {a b i : ℕ} (h : orb a b i ≠ 0) : orb a b (i + 1) = a % orb a b i := by
  rw [orb_succ, step_of_ne h]

@[simp] lemma P_zero (a : ℕ) : P a 0 = 0 := by simp [P]

lemma P_of_ne {a b : ℕ} (hb : b ≠ 0) : P a b = P a (a % b) + 1 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  simp [P]

lemma orb_ne_zero_of_lt {a b i : ℕ} (hi : i < P a b) : orb a b i ≠ 0 := by
  induction b using Nat.strong_induction_on generalizing i with
  | _ b ih =>
    by_cases hb : b = 0
    · subst hb; simp at hi
    · rw [P_of_ne hb] at hi
      cases i with
      | zero => simpa using hb
      | succ i =>
        rw [orb_succ', step_of_ne hb]
        exact ih _ (Nat.mod_lt _ (Nat.pos_of_ne_zero hb)) (by omega)

lemma orb_antitone (a b : ℕ) : Antitone (orb a b) :=
  antitone_nat_of_succ_le fun i => by rw [orb_succ]; exact step_le _ _

lemma orb_le (a b i : ℕ) : orb a b i ≤ b := by
  simpa using orb_antitone a b (Nat.zero_le i)

/-- The example on the Open Problem Garden page: `22, 13, 9, 8, 3, 2, 1, 0`. -/
example : P 35 22 = 7 := by simp [P_of_ne]

end PierceBound
