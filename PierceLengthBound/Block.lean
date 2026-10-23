/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Defs

/-!
# Three consecutive steps

Let `x = bᵢ`, `y = b_{i+1} = a mod x`, `z = b_{i+2} = a mod y`, `w = b_{i+3} = a mod z`, with
`z > 0`. Write `q = ⌊a/x⌋`, `u = ⌊a/y⌋ - ⌊a/x⌋`, `v = ⌊a/z⌋ - ⌊a/y⌋` and
`d = x - y`, `e = y - z`, `f = z - w`. The *curvature* of the block is `D = dv - eu`.

* `curvature_identity`: `D z = df + ude + (u-1)e²`, hence `D ≥ 1` (`one_le_bD`; Lemma 3.2);
* `block_fiber_eq`: `x M(q) = a N(q) + D` with `M(q) = uq² + (u²+u+v)q + v`,
  `N(q) = uq + u² + v` (Lemma 3.3);
* `bu_mul_le`, `bv_mul_le`, `bD_mul_le`: the size bounds used in the counting (Lemma 3.4).
-/

@[expose] public section

namespace PierceLengthBound

/-- The quotient increment `u = ⌊a/(a mod x)⌋ - ⌊a/x⌋`. -/
def bu (a x : ℕ) : ℕ := a / (a % x) - a / x

/-- The next quotient increment `v`. -/
def bv (a x : ℕ) : ℕ := bu a (a % x)

/-- The curvature `D = dv - eu` of the block starting at `x`. -/
def bD (a x : ℕ) : ℕ := (x - a % x) * bv a x - (a % x - a % (a % x)) * bu a x

/-! ### The algebra, in terms of the drops `d, e, f` and the increments `u, v` -/

/-- **The curvature identity.** With `z = w + f`, `y = z + e`, `x = y + d`. -/
theorem curvature_identity (a w f e d q u v : ℤ)
    (h1 : (w + f + e + d) * q + (w + f + e) = a)
    (h2 : (w + f + e) * (q + u) + (w + f) = a)
    (h3 : (w + f) * (q + u + v) + w = a) :
    (d * v - e * u) * (w + f) = d * f + u * d * e + (u - 1) * e ^ 2 := by
  linear_combination d * h3 + (a - q * (w + f + e + d) - (w + f + e + d) - (w + f + e) + (w + f))
      * h2 +
    (-a + (q + u) * (w + f + e) + (w + f + e)) * h1

/-- **The fiber equation.** `D = M(q) x - a N(q)`. -/
theorem fiber_identity (a w f e d q u v : ℤ)
    (h1 : (w + f + e + d) * q + (w + f + e) = a)
    (h2 : (w + f + e) * (q + u) + (w + f) = a) :
    d * v - e * u = (w + f + e + d) * (u * q ^ 2 + (u ^ 2 + u + v) * q + v) -
      a * (u * q + (u ^ 2 + v)) := by
  linear_combination u * h2 + (q * (q + u) + q - (q + u) ^ 2 - (q + u + v)) * h1

/-- `u y = q d + e`. -/
theorem increment_identity (a w f e d q u : ℤ)
    (h1 : (w + f + e + d) * q + (w + f + e) = a)
    (h2 : (w + f + e) * (q + u) + (w + f) = a) :
    u * (w + f + e) = q * d + e := by
  linear_combination h2 - h1

/-- Everything about one block, for natural-number data. -/
theorem block_core (a w f e d q u v : ℕ) (hf : 0 < f) (hd : 0 < d) (hu : 1 ≤ u)
    (h1 : (w + f + e + d) * q + (w + f + e) = a)
    (h2 : (w + f + e) * (q + u) + (w + f) = a)
    (h3 : (w + f) * (q + u + v) + w = a) :
    e * u < d * v ∧
    (d * v - e * u) * (w + f) ≤ (u + 1) * (d + e + f) ^ 2 ∧
    (w + f + e + d) * (u * q ^ 2 + (u ^ 2 + u + v) * q + v) =
      a * u * q + (a * (u ^ 2 + v) + (d * v - e * u)) := by
  have h1' : ((w + f + e + d : ℕ) : ℤ) * q + (w + f + e : ℕ) = a := by exact_mod_cast h1
  have h2' : ((w + f + e : ℕ) : ℤ) * ((q + u : ℕ) : ℤ) + (w + f : ℕ) = a := by exact_mod_cast h2
  have h3' : ((w + f : ℕ) : ℤ) * ((q + u + v : ℕ) : ℤ) + w = a := by exact_mod_cast h3
  push_cast at h1' h2' h3'
  have hc := curvature_identity a w f e d q u v h1' h2' h3'
  have hfib := fiber_identity a w f e d q u v h1' h2'
  have hw0 : (0 : ℤ) ≤ w := by positivity
  have he0 : (0 : ℤ) ≤ e := by positivity
  have hf0 : (0 : ℤ) < f := by exact_mod_cast hf
  have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
  have hu0 : (1 : ℤ) ≤ u := by exact_mod_cast hu
  have hpos : (0 : ℤ) < (d * v - e * u) * (w + f) := by
    rw [hc]
    have := mul_pos hd0 hf0
    have : (0 : ℤ) ≤ u * d * e := by positivity
    have : (0 : ℤ) ≤ (u - 1) * e ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hDpos : (0 : ℤ) < d * v - e * u := pos_of_mul_pos_left hpos (by linarith)
  have hlt : e * u < d * v := by
    have : ((e * u : ℕ) : ℤ) < ((d * v : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hcast : ((d * v - e * u : ℕ) : ℤ) = (d : ℤ) * v - e * u := by
    rw [Nat.cast_sub hlt.le]; push_cast; ring
  refine ⟨hlt, ?_, ?_⟩
  · have : (((d * v - e * u) * (w + f) : ℕ) : ℤ) ≤ (((u + 1) * (d + e + f) ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [hcast, hc]
      have hd0' : (0 : ℤ) ≤ d := hd0.le
      have hf0' : (0 : ℤ) ≤ f := hf0.le
      have hu0' : (0 : ℤ) ≤ u := by linarith
      nlinarith [mul_nonneg hd0' he0, mul_nonneg hd0' hf0', mul_nonneg he0 hf0',
        mul_nonneg (mul_nonneg hd0' he0) hu0', mul_nonneg (mul_nonneg hd0' hf0') hu0',
        mul_nonneg (mul_nonneg he0 hf0') hu0', mul_nonneg (mul_nonneg hd0' hd0') hu0',
        mul_nonneg (mul_nonneg hf0' hf0') hu0', mul_nonneg hd0' hd0', mul_nonneg hf0' hf0',
        mul_nonneg he0 he0, mul_nonneg (mul_nonneg he0 he0) hu0']
    exact_mod_cast this
  · have : (((w + f + e + d) * (u * q ^ 2 + (u ^ 2 + u + v) * q + v) : ℕ) : ℤ) =
        ((a * u * q + (a * (u ^ 2 + v) + (d * v - e * u)) : ℕ) : ℤ) := by
      push_cast
      rw [hcast, hfib]
      ring
    exact_mod_cast this

/-- `u · y · x ≤ a (d + e)`, from `u y = q d + e`, `q x ≤ a` and `x ≤ a`. -/
theorem increment_core (a w f e d q u : ℕ) (hxa : w + f + e + d ≤ a)
    (h1 : (w + f + e + d) * q + (w + f + e) = a)
    (h2 : (w + f + e) * (q + u) + (w + f) = a) :
    u * ((w + f + e) * (w + f + e + d)) ≤ a * (d + e) := by
  have h1' : ((w + f + e + d : ℕ) : ℤ) * q + (w + f + e : ℕ) = a := by exact_mod_cast h1
  have h2' : ((w + f + e : ℕ) : ℤ) * ((q + u : ℕ) : ℤ) + (w + f : ℕ) = a := by exact_mod_cast h2
  push_cast at h1' h2'
  have hi := increment_identity a w f e d q u h1' h2'
  have hxa' : ((w + f + e + d : ℕ) : ℤ) ≤ a := by exact_mod_cast hxa
  push_cast at hxa'
  have hqx : ((w : ℤ) + f + e + d) * q ≤ a := by
    have : (0 : ℤ) ≤ w + f + e := by positivity
    linarith
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have he0 : (0 : ℤ) ≤ e := by positivity
  have : ((u * ((w + f + e) * (w + f + e + d)) : ℕ) : ℤ) ≤ ((a * (d + e) : ℕ) : ℤ) := by
    push_cast
    have e1 : (u : ℤ) * ((w + f + e) * (w + f + e + d)) = (q * d + e) * (w + f + e + d) := by
      rw [← hi]; ring
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_right hqx hd0, mul_le_mul_of_nonneg_left hxa' he0]
  exact_mod_cast this

/-! ### Specialisation to `y = a mod x`, `z = a mod y`, `w = a mod z` -/

section Block

variable {a x : ℕ}

/-- The data of a block in drop form. -/
private lemma block_data (hx : 0 < x) (hy : a % x ≠ 0) (hz : a % (a % x) ≠ 0) :
    ∃ w f e d u v : ℕ, 0 < f ∧ 0 < d ∧ 1 ≤ u ∧ 1 ≤ v ∧
      a % (a % (a % x)) = w ∧ a % (a % x) = w + f ∧ a % x = w + f + e ∧ x = w + f + e + d ∧
      bu a x = u ∧ bv a x = v ∧
      (w + f + e + d) * (a / x) + (w + f + e) = a ∧
      (w + f + e) * (a / x + u) + (w + f) = a ∧
      (w + f) * (a / x + u + v) + w = a := by
  have hwz : a % (a % (a % x)) < a % (a % x) := Nat.mod_lt _ (Nat.pos_of_ne_zero hz)
  have hzy : a % (a % x) < a % x := Nat.mod_lt _ (Nat.pos_of_ne_zero hy)
  have hyx : a % x < x := Nat.mod_lt _ hx
  have hq := div_lt_div_mod hx hy
  have hq1 := div_lt_div_mod (Nat.pos_of_ne_zero hy) hz
  have h1 := Nat.div_add_mod a x
  have h2 := Nat.div_add_mod a (a % x)
  have h3 := Nat.div_add_mod a (a % (a % x))
  refine ⟨a % (a % (a % x)), a % (a % x) - a % (a % (a % x)), a % x - a % (a % x),
    x - a % x, bu a x, bv a x, by omega, by omega, by unfold bu; omega,
    by unfold bv bu; omega, rfl, by omega, by omega, by omega, rfl, rfl, ?_, ?_, ?_⟩
  · rw [show a % (a % (a % x)) + (a % (a % x) - a % (a % (a % x))) +
      (a % x - a % (a % x)) + (x - a % x) = x by omega,
      show a % (a % (a % x)) + (a % (a % x) - a % (a % (a % x))) +
      (a % x - a % (a % x)) = a % x by omega]
    exact h1
  · rw [show a % (a % (a % x)) + (a % (a % x) - a % (a % (a % x))) +
      (a % x - a % (a % x)) = a % x by omega,
      show a % (a % (a % x)) + (a % (a % x) - a % (a % (a % x))) = a % (a % x) by omega,
      show a / x + bu a x = a / (a % x) by unfold bu; omega]
    exact h2
  · rw [show a % (a % (a % x)) + (a % (a % x) - a % (a % (a % x))) = a % (a % x) by omega,
      show a / x + bu a x + bv a x = a / (a % (a % x)) by unfold bv bu; omega]
    exact h3

lemma one_le_bu (hx : 0 < x) (hy : a % x ≠ 0) : 1 ≤ bu a x := by
  have := div_lt_div_mod hx hy; unfold bu; omega

lemma one_le_bv (hy : a % x ≠ 0) (hz : a % (a % x) ≠ 0) : 1 ≤ bv a x :=
  one_le_bu (Nat.pos_of_ne_zero hy) hz

/-- Unfolding the curvature. -/
private lemma bD_eq :
    bD a x = (x - a % x) * bv a x - (a % x - a % (a % x)) * bu a x := rfl

/-- **Positivity of the curvature.** -/
lemma one_le_bD (hx : 0 < x) (hy : a % x ≠ 0) (hz : a % (a % x) ≠ 0) : 1 ≤ bD a x := by
  obtain ⟨w, f, e, d, u, v, hf, hd, hu, -, hw, hz', hy, hx', hbu, hbv, h1, h2, h3⟩ :=
    block_data hx hy hz
  have := (block_core a w f e d (a / x) u v hf hd hu h1 h2 h3).1
  rw [bD_eq, hbu, hbv, hz', hy, hx']
  rw [show w + f + e + d - (w + f + e) = d by omega, show w + f + e - (w + f) = e by omega]
  omega

/-- **The curvature bound.** `D z ≤ (u + 1)(x - w)²`, where `x - w = d + e + f`. -/
lemma bD_mul_le (hx : 0 < x) (hy : a % x ≠ 0) (hz : a % (a % x) ≠ 0) :
    bD a x * (a % (a % x)) ≤ (bu a x + 1) * (x - a % (a % (a % x))) ^ 2 := by
  obtain ⟨w, f, e, d, u, v, hf, hd, hu, -, hw, hz', hy, hx', hbu, hbv, h1, h2, h3⟩ :=
    block_data hx hy hz
  have := (block_core a w f e d (a / x) u v hf hd hu h1 h2 h3).2.1
  rw [bD_eq, hbu, hbv, hw, hz', hy, hx']
  rw [show w + f + e + d - (w + f + e) = d by omega, show w + f + e - (w + f) = e by omega,
    show w + f + e + d - w = d + e + f by omega]
  exact this

/-- **The fiber equation.** `x M(q) = a N(q) + D` with `q = ⌊a/x⌋`. -/
lemma block_fiber_eq (hx : 0 < x) (hy : a % x ≠ 0) (hz : a % (a % x) ≠ 0) :
    x * (bu a x * (a / x) ^ 2 + (bu a x ^ 2 + bu a x + bv a x) * (a / x) + bv a x) =
      a * bu a x * (a / x) + (a * (bu a x ^ 2 + bv a x) + bD a x) := by
  obtain ⟨w, f, e, d, u, v, hf, hd, hu, -, hw, hz', hy, hx', hbu, hbv, h1, h2, h3⟩ :=
    block_data hx hy hz
  have := (block_core a w f e d (a / x) u v hf hd hu h1 h2 h3).2.2
  rw [bD_eq, hbu, hbv, hz', hy]
  rw [show x - (w + f + e) = d by omega, show w + f + e - (w + f) = e by omega]
  rw [← hx'] at this
  exact this

/-- **Size of `u`.** `u · y · x ≤ a (x - z)` when `x ≤ a`. -/
lemma bu_mul_le (hx : 0 < x) (hy : a % x ≠ 0) (hz : a % (a % x) ≠ 0) (hxa : x ≤ a) :
    bu a x * (a % x * x) ≤ a * (x - a % (a % x)) := by
  obtain ⟨w, f, e, d, u, v, -, -, -, -, -, hz', hy, hx', hbu, -, h1, h2, -⟩ := block_data hx hy hz
  have := increment_core a w f e d (a / x) u (hx' ▸ hxa) h1 h2
  rw [hbu, hz', hy]
  rw [show x - (w + f) = d + e by omega]
  rw [← hx'] at this
  exact this

end Block

/-- **Size of `v`.** `v · z · y ≤ a (y - w)`. -/
lemma bv_mul_le {a x : ℕ} (hy : a % x ≠ 0) (hz : a % (a % x) ≠ 0)
    (hw : a % (a % (a % x)) ≠ 0) :
    bv a x * (a % (a % x) * (a % x)) ≤ a * (a % x - a % (a % (a % x))) := bu_mul_le (x := a % x)
        (Nat.pos_of_ne_zero hy) hz hw (Nat.mod_le _ _)

end PierceLengthBound
