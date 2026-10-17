import PierceBound.TwoState
import PierceBound.Gram

/-!
# Sizes of the pattern integers

At a state whose increments `k₀,…,k₅` lie in `[1, H]`, with labels `L(i), L(i+1) ≥ 1` obeying
the label bound `L · a³ ≤ 256 A⁴ gramP`, and under the scale condition
`237568 A⁴ H⁵ ≤ a³`, the four pattern integers `L(i), L(i+1), U₁, U₂` are at most
`172032 A⁴ H⁶ / a³` in absolute value (`state_bound`).

The proof: `gramP ≤ Δ₄ + 464 H⁵` and `Δ₄ ≤ 6 H³ V` with `V = k₁ k₂ (k₁ + k₂)`, for both
adjacent states; the scale condition absorbs the error, giving `L a³ ≤ 3072 A⁴ H³ V` and
`V ≥ 77 H²`. Then Cramer's rule for `(U₁, U₂)` has determinant `δ = k₁ r₂ - k₂ r₁ ≥ V/2`
and numerators `≤ 14 (L(i) + L(i+1)) H³`.
-/

namespace PierceBound

private lemma mul_le_mul' {x y X Y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hX : x ≤ X) (hY : y ≤ Y) :
    x * y ≤ X * Y :=
  mul_le_mul hX hY hy (hx.trans hX)

/-- `gramP ≤ Δ₄ + 464 H⁵` for increments in `[1, H]`. -/
lemma gramP_le {k0 k1 k2 k3 k4 H : ℤ} (h0 : 1 ≤ k0) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) (h3 : 1 ≤ k3)
    (h4 : 1 ≤ k4) (g0 : k0 ≤ H) (g1 : k1 ≤ H) (g2 : k2 ≤ H) (g3 : k3 ≤ H) (g4 : k4 ≤ H) :
    gramP k0 k1 k2 k3 k4 ≤ k0 * (k1 * (k0 + k1)) * (k2 * (k1 + k2) * (k0 + k1 + k2)) +
      464 * H ^ 5 := by
  have hH : 1 ≤ H := h0.trans g0
  have hH0 : 0 ≤ H := by linarith
  have hg : gramP k0 k1 k2 k3 k4 = (k0 + 1) * (k1 * (k0 + k1) + (k0 + 2 * k1 + k2 + 1)) *
      (k2 * (k1 + k2) * (k0 + k1 + k2) +
        ((k0 + k1 + k2) * (k1 + k2) + (k0 + k1 + k2) * k2 + (k1 + k2) * k2 +
          (k0 + 2 * k1 + 3 * k2) * (k3 + 1) + (k3 ^ 2 + 2 * k3 + k4 + 1))) := by
    simp only [gramP]; ring
  rw [hg]
  generalize he2 : k0 + 2 * k1 + k2 + 1 = e2
  generalize hM3 : k2 * (k1 + k2) * (k0 + k1 + k2) = M3
  generalize hm1 : k1 * (k0 + k1) = m1
  generalize he3 : (k0 + k1 + k2) * (k1 + k2) + (k0 + k1 + k2) * k2 + (k1 + k2) * k2 +
    (k0 + 2 * k1 + 3 * k2) * (k3 + 1) + (k3 ^ 2 + 2 * k3 + k4 + 1) = e3
  have e2le : e2 ≤ 5 * H := by rw [← he2]; linarith
  have e2nn : 0 ≤ e2 := by rw [← he2]; linarith
  have e3le : e3 ≤ 28 * H ^ 2 := by
    rw [← he3]
    have t1 : (k0 + k1 + k2) * (k1 + k2) ≤ (3 * H) * (2 * H) :=
      mul_le_mul' (by linarith) (by linarith) (by linarith) (by linarith)
    have t2 : (k0 + k1 + k2) * k2 ≤ (3 * H) * H :=
      mul_le_mul' (by linarith) (by linarith) (by linarith) g2
    have t3 : (k1 + k2) * k2 ≤ (2 * H) * H :=
      mul_le_mul' (by linarith) (by linarith) (by linarith) g2
    have t4 : (k0 + 2 * k1 + 3 * k2) * (k3 + 1) ≤ (6 * H) * (2 * H) :=
      mul_le_mul' (by linarith) (by linarith) (by linarith) (by linarith)
    have t5 : k3 ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (by linarith) g3 2
    have t6 : H ≤ H ^ 2 := by
      calc H = H ^ 1 := (pow_one H).symm
        _ ≤ H ^ 2 := pow_le_pow_right₀ hH (by norm_num)
    have : (3 * H) * (2 * H) = 6 * H ^ 2 := by ring
    have : (3 * H) * H = 3 * H ^ 2 := by ring
    have : (2 * H) * H = 2 * H ^ 2 := by ring
    have : (6 * H) * (2 * H) = 12 * H ^ 2 := by ring
    linarith
  have e3nn : 0 ≤ e3 := by rw [← he3]; positivity
  have m1le : m1 ≤ 2 * H ^ 2 := by
    rw [← hm1]
    have := mul_le_mul' (by linarith) (by linarith) g1 (by linarith : k0 + k1 ≤ 2 * H)
    linarith [show H * (2 * H) = 2 * H ^ 2 by ring]
  have m1nn : 0 ≤ m1 := by rw [← hm1]; positivity
  have M3le : M3 ≤ 6 * H ^ 3 := by
    rw [← hM3]
    have a1 := mul_le_mul' (by linarith) (by linarith) g2 (by linarith : k1 + k2 ≤ 2 * H)
    have a2 := mul_le_mul' (by positivity) (by linarith) a1 (by linarith : k0 + k1 + k2 ≤ 3 * H)
    linarith [show H * (2 * H) * (3 * H) = 6 * H ^ 3 by ring]
  have M3nn : 0 ≤ M3 := by rw [← hM3]; positivity
  have k0m1 : k0 * m1 ≤ 2 * H ^ 3 := by
    have := mul_le_mul' (by linarith) m1nn g0 m1le
    linarith [show H * (2 * H ^ 2) = 2 * H ^ 3 by ring]
  have p23 : H ^ 2 ≤ H ^ 3 := pow_le_pow_right₀ hH (by norm_num)
  have p12 : H ≤ H ^ 2 := by
    calc H = H ^ 1 := (pow_one H).symm
      _ ≤ H ^ 2 := pow_le_pow_right₀ hH (by norm_num)
  have B3le : M3 + e3 ≤ 34 * H ^ 3 := by linarith
  have A2le : m1 + e2 ≤ 7 * H ^ 2 := by linarith
  have t1 : k0 * m1 * e3 ≤ 2 * H ^ 3 * (28 * H ^ 2) :=
    mul_le_mul' (by positivity) e3nn k0m1 e3le
  have t2 : k0 * e2 * (M3 + e3) ≤ H * (5 * H) * (34 * H ^ 3) :=
    mul_le_mul' (by positivity) (by linarith) (mul_le_mul' (by linarith) e2nn g0 e2le) B3le
  have t3 : (m1 + e2) * (M3 + e3) ≤ 7 * H ^ 2 * (34 * H ^ 3) :=
    mul_le_mul' (by linarith) (by linarith) A2le B3le
  have hsplit : (k0 + 1) * (m1 + e2) * (M3 + e3) = k0 * m1 * M3 +
      (k0 * m1 * e3 + k0 * e2 * (M3 + e3) + (m1 + e2) * (M3 + e3)) := by ring
  rw [hsplit]
  have : 2 * H ^ 3 * (28 * H ^ 2) + H * (5 * H) * (34 * H ^ 3) + 7 * H ^ 2 * (34 * H ^ 3) =
    464 * H ^ 5 := by ring
  linarith

/-- `Δ₄(k₀,k₁,k₂) ≤ 6 H³ V` with `V = k₁ k₂ (k₁ + k₂)`. -/
lemma delta_left_le {k0 k1 k2 H : ℤ} (h0 : 1 ≤ k0) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2)
    (g0 : k0 ≤ H) (g1 : k1 ≤ H) (g2 : k2 ≤ H) :
    k0 * (k1 * (k0 + k1)) * (k2 * (k1 + k2) * (k0 + k1 + k2)) ≤
      6 * H ^ 3 * (k1 * k2 * (k1 + k2)) := by
  have hV : 0 ≤ k1 * k2 * (k1 + k2) := by positivity
  have a1 := mul_le_mul' (by linarith) (by linarith) g0 (by linarith : k0 + k1 ≤ 2 * H)
  have a2 := mul_le_mul' (by positivity) (by linarith) a1 (by linarith : k0 + k1 + k2 ≤ 3 * H)
  have hW : k0 * (k0 + k1) * (k0 + k1 + k2) ≤ 6 * H ^ 3 := by
    linarith [show H * (2 * H) * (3 * H) = 6 * H ^ 3 by ring]
  calc k0 * (k1 * (k0 + k1)) * (k2 * (k1 + k2) * (k0 + k1 + k2)) =
      (k0 * (k0 + k1) * (k0 + k1 + k2)) * (k1 * k2 * (k1 + k2)) := by ring
    _ ≤ 6 * H ^ 3 * (k1 * k2 * (k1 + k2)) := mul_le_mul_of_nonneg_right hW hV

/-- `Δ₄(k₁,k₂,k₃) ≤ 6 H³ V` with `V = k₁ k₂ (k₁ + k₂)`. -/
lemma delta_right_le {k1 k2 k3 H : ℤ} (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) (h3 : 1 ≤ k3)
    (g1 : k1 ≤ H) (g2 : k2 ≤ H) (g3 : k3 ≤ H) :
    k1 * (k2 * (k1 + k2)) * (k3 * (k2 + k3) * (k1 + k2 + k3)) ≤
      6 * H ^ 3 * (k1 * k2 * (k1 + k2)) := by
  have hV : 0 ≤ k1 * k2 * (k1 + k2) := by positivity
  have a1 := mul_le_mul' (by linarith) (by linarith) g3 (by linarith : k2 + k3 ≤ 2 * H)
  have a2 := mul_le_mul' (by positivity) (by linarith) a1 (by linarith : k1 + k2 + k3 ≤ 3 * H)
  have hW : k3 * (k2 + k3) * (k1 + k2 + k3) ≤ 6 * H ^ 3 := by
    linarith [show H * (2 * H) * (3 * H) = 6 * H ^ 3 by ring]
  calc k1 * (k2 * (k1 + k2)) * (k3 * (k2 + k3) * (k1 + k2 + k3)) =
      (k3 * (k2 + k3) * (k1 + k2 + k3)) * (k1 * k2 * (k1 + k2)) := by ring
    _ ≤ 6 * H ^ 3 * (k1 * k2 * (k1 + k2)) := mul_le_mul_of_nonneg_right hW hV

/-- From the label bound and the scale condition: `L a³ ≤ 3072 A⁴ H³ V`. -/
lemma label_absorb {a A H L G V : ℤ} (hL : 1 ≤ L) (hG : G ≤ 6 * H ^ 3 * V + 464 * H ^ 5)
    (hLa : L * a ^ 3 ≤ 256 * A ^ 4 * G) (hc : 237568 * A ^ 4 * H ^ 5 ≤ a ^ 3)
    (ha3 : 0 ≤ a ^ 3) : L * a ^ 3 ≤ 3072 * A ^ 4 * H ^ 3 * V := by
  have h1 : L * a ^ 3 ≤ 256 * A ^ 4 * (6 * H ^ 3 * V) + 118784 * A ^ 4 * H ^ 5 := by
    have := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℤ) ≤ 256 * A ^ 4)
    linarith
  have h2 : 2 * (118784 * A ^ 4 * H ^ 5) ≤ L * a ^ 3 := by
    have : 1 * a ^ 3 ≤ L * a ^ 3 := mul_le_mul_of_nonneg_right hL ha3
    linarith
  linarith

private lemma abs_lin_le {N M x y X Y Z : ℤ} (hN : 0 ≤ N) (hM : 0 ≤ M) (hx : |x| ≤ X)
    (hy : |y| ≤ Y) (hX : X ≤ Z) (hY : Y ≤ Z) : |N * x - M * y| ≤ (N + M) * Z := by
  calc |N * x - M * y| ≤ |N * x| + |M * y| := abs_sub _ _
    _ = N * |x| + M * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg hN, abs_of_nonneg hM]
    _ ≤ N * Z + M * Z := by
        gcongr
        · exact hx.trans hX
        · exact hy.trans hY
    _ = (N + M) * Z := by ring

/-- **The pattern integers are small.** -/
theorem state_bound {a A H Nn N1 u1 u2 k0 k1 k2 k3 k4 k5 : ℤ}
    (h0 : 1 ≤ k0) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) (h3 : 1 ≤ k3) (h4 : 1 ≤ k4) (h5 : 1 ≤ k5)
    (g0 : k0 ≤ H) (g1 : k1 ≤ H) (g2 : k2 ≤ H) (g3 : k3 ≤ H) (g4 : k4 ≤ H) (g5 : k5 ≤ H)
    (hA : 1 ≤ A) (hNn : 1 ≤ Nn) (hN1 : 1 ≤ N1)
    (hL0 : Nn * a ^ 3 ≤ 256 * A ^ 4 * gramP k0 k1 k2 k3 k4)
    (hL1 : N1 * a ^ 3 ≤ 256 * A ^ 4 * gramP k1 k2 k3 k4 k5)
    (hc : 237568 * A ^ 4 * H ^ 5 ≤ a ^ 3)
    (e0 : -N1 * k0 + u1 * k1 + u2 * k2 + Nn * k3 = 0)
    (e3 : -N1 * (k0 ^ 2 + k1) + u1 * (k1 * (2 * k0 + k1) + k2) +
      u2 * (k2 * (2 * k0 + 2 * k1 + k2) + k3) +
      Nn * (k3 * (2 * k0 + 2 * k1 + 2 * k2 + k3) + k4) = 0) :
    |u1| * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 ∧ |u2| * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 ∧
      Nn * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 ∧ N1 * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 := by
  have hH : 1 ≤ H := h0.trans g0
  have hH0 : 0 ≤ H := by linarith
  have hA4 : 0 ≤ A ^ 4 := by positivity
  have ha3 : 0 ≤ a ^ 3 := le_trans (by positivity) hc
  -- the Cramer system: `u₁ δ = ρ₁ r₂ - ρ₂ k₂`, `u₂ δ = ρ₂ k₁ - ρ₁ r₁`
  have c1 : u1 * (k1 * (k2 * (2 * k0 + 2 * k1 + k2) + k3) - k2 * (k1 * (2 * k0 + k1) + k2)) =
      (N1 * k0 - Nn * k3) * (k2 * (2 * k0 + 2 * k1 + k2) + k3) -
        (N1 * (k0 ^ 2 + k1) - Nn * (k3 * (2 * k0 + 2 * k1 + 2 * k2 + k3) + k4)) * k2 := by
    linear_combination (k2 * (2 * k0 + 2 * k1 + k2) + k3) * e0 - k2 * e3
  have c2 : u2 * (k1 * (k2 * (2 * k0 + 2 * k1 + k2) + k3) - k2 * (k1 * (2 * k0 + k1) + k2)) =
      (N1 * (k0 ^ 2 + k1) - Nn * (k3 * (2 * k0 + 2 * k1 + 2 * k2 + k3) + k4)) * k1 -
        (N1 * k0 - Nn * k3) * (k1 * (2 * k0 + k1) + k2) := by
    linear_combination k1 * e3 - (k1 * (2 * k0 + k1) + k2) * e0
  generalize hV : k1 * k2 * (k1 + k2) = V
  generalize hδ : k1 * (k2 * (2 * k0 + 2 * k1 + k2) + k3) - k2 * (k1 * (2 * k0 + k1) + k2) = δ
    at c1 c2
  generalize hr0 : k0 ^ 2 + k1 = r0 at c1 c2
  generalize hr1 : k1 * (2 * k0 + k1) + k2 = r1 at c2
  generalize hr2 : k2 * (2 * k0 + 2 * k1 + k2) + k3 = r2 at c1
  generalize hr3 : k3 * (2 * k0 + 2 * k1 + 2 * k2 + k3) + k4 = r3 at c1 c2
  have hVpos : 0 < V := by rw [← hV]; positivity
  have hVle : V ≤ 2 * H ^ 3 := by
    rw [← hV]
    have := mul_le_mul' (by positivity) (by linarith) (mul_le_mul' (by linarith) (by linarith)
      g1 g2) (by linarith : k1 + k2 ≤ 2 * H)
    linarith [show H * H * (2 * H) = 2 * H ^ 3 by ring]
  -- labels
  have G0 : gramP k0 k1 k2 k3 k4 ≤ 6 * H ^ 3 * V + 464 * H ^ 5 := by
    have := gramP_le h0 h1 h2 h3 h4 g0 g1 g2 g3 g4
    have := delta_left_le h0 h1 h2 g0 g1 g2
    rw [hV] at this; linarith
  have G1 : gramP k1 k2 k3 k4 k5 ≤ 6 * H ^ 3 * V + 464 * H ^ 5 := by
    have := gramP_le h1 h2 h3 h4 h5 g1 g2 g3 g4 g5
    have := delta_right_le h1 h2 h3 g1 g2 g3
    rw [hV] at this; linarith
  have L0 := label_absorb hNn G0 hL0 hc ha3
  have L1 := label_absorb hN1 G1 hL1 hc ha3
  -- `V ≥ 77 H²`
  have hV77 : 77 * H ^ 2 ≤ V := by
    have e1 : 1 * a ^ 3 ≤ Nn * a ^ 3 := mul_le_mul_of_nonneg_right hNn ha3
    have : (A ^ 4 * H ^ 3) * (237568 * H ^ 2) ≤ (A ^ 4 * H ^ 3) * (3072 * V) := by
      calc (A ^ 4 * H ^ 3) * (237568 * H ^ 2) = 237568 * A ^ 4 * H ^ 5 := by ring
        _ ≤ 3072 * A ^ 4 * H ^ 3 * V := by linarith
        _ = (A ^ 4 * H ^ 3) * (3072 * V) := by ring
    have hpos : 0 < A ^ 4 * H ^ 3 := by positivity
    have := le_of_mul_le_mul_left this hpos
    linarith
  have hδV : V ≤ 2 * δ := by
    have e : δ = V + k1 * k3 - k2 ^ 2 := by rw [← hδ, ← hV]; ring
    have : k2 ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (by linarith) g2 2
    have : 0 ≤ k1 * k3 := by positivity
    have : 0 ≤ H ^ 2 := by positivity
    linarith
  have hδpos : 0 < δ := by linarith
  have hNn0 : 0 ≤ Nn := by linarith
  have hN10 : 0 ≤ N1 := by linarith
  have bk0 : |k0| ≤ H := by rw [abs_of_pos (by linarith)]; exact g0
  have bk1 : |k1| ≤ H := by rw [abs_of_pos (by linarith)]; exact g1
  have bk2 : |k2| ≤ H := by rw [abs_of_pos (by linarith)]; exact g2
  have bk3 : |k3| ≤ H := by rw [abs_of_pos (by linarith)]; exact g3
  have p12 : H ≤ H ^ 2 := by
    calc H = H ^ 1 := (pow_one H).symm
      _ ≤ H ^ 2 := pow_le_pow_right₀ hH (by norm_num)
  have br0 : |r0| ≤ 8 * H ^ 2 := by
    rw [← hr0, abs_of_nonneg (by positivity)]
    have := pow_le_pow_left₀ (by linarith) g0 2
    linarith
  have br1 : |r1| ≤ 4 * H ^ 2 := by
    rw [← hr1, abs_of_nonneg (by positivity)]
    have := mul_le_mul' (by linarith) (by linarith) g1 (by linarith : 2 * k0 + k1 ≤ 3 * H)
    linarith [show H * (3 * H) = 3 * H ^ 2 by ring]
  have br2 : |r2| ≤ 6 * H ^ 2 := by
    rw [← hr2, abs_of_nonneg (by positivity)]
    have := mul_le_mul' (by linarith) (by linarith) g2 (by linarith : 2 * k0 + 2 * k1 + k2 ≤ 5 * H)
    linarith [show H * (5 * H) = 5 * H ^ 2 by ring]
  have br3 : |r3| ≤ 8 * H ^ 2 := by
    rw [← hr3, abs_of_nonneg (by positivity)]
    have := mul_le_mul' (by linarith) (by linarith) g3
      (by linarith : 2 * k0 + 2 * k1 + 2 * k2 + k3 ≤ 7 * H)
    linarith [show H * (7 * H) = 7 * H ^ 2 by ring]
  have bρ1 : |N1 * k0 - Nn * k3| ≤ (N1 + Nn) * H := abs_lin_le hN10 hNn0 bk0 bk3 le_rfl le_rfl
  have bρ2 : |N1 * r0 - Nn * r3| ≤ (N1 + Nn) * (8 * H ^ 2) :=
    abs_lin_le hN10 hNn0 br0 br3 le_rfl le_rfl
  have bu1 : |u1| * δ ≤ 14 * (Nn + N1) * H ^ 3 := by
    rw [← abs_of_pos hδpos, ← abs_mul, c1]
    calc |(N1 * k0 - Nn * k3) * r2 - (N1 * r0 - Nn * r3) * k2|
        ≤ |N1 * k0 - Nn * k3| * |r2| + |N1 * r0 - Nn * r3| * |k2| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ (N1 + Nn) * H * (6 * H ^ 2) + (N1 + Nn) * (8 * H ^ 2) * H := by
          gcongr
      _ = 14 * (Nn + N1) * H ^ 3 := by ring
  have bu2 : |u2| * δ ≤ 14 * (Nn + N1) * H ^ 3 := by
    rw [← abs_of_pos hδpos, ← abs_mul, c2]
    calc |(N1 * r0 - Nn * r3) * k1 - (N1 * k0 - Nn * k3) * r1|
        ≤ |N1 * r0 - Nn * r3| * |k1| + |N1 * k0 - Nn * k3| * |r1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ (N1 + Nn) * (8 * H ^ 2) * H + (N1 + Nn) * H * (4 * H ^ 2) := by
          gcongr
      _ ≤ 14 * (Nn + N1) * H ^ 3 := by
          have : 0 ≤ (N1 + Nn) * H ^ 3 := by positivity
          linarith [show (N1 + Nn) * (8 * H ^ 2) * H + (N1 + Nn) * H * (4 * H ^ 2) =
            12 * ((N1 + Nn) * H ^ 3) by ring, show 14 * (Nn + N1) * H ^ 3 =
            14 * ((N1 + Nn) * H ^ 3) by ring]
  -- conclude
  have hsum : (Nn + N1) * a ^ 3 ≤ 6144 * A ^ 4 * H ^ 3 * V := by
    have : (Nn + N1) * a ^ 3 = Nn * a ^ 3 + N1 * a ^ 3 := by ring
    linarith
  have fin : ∀ u : ℤ, |u| * δ ≤ 14 * (Nn + N1) * H ^ 3 →
      |u| * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 := by
    intro u hu
    have hu0 : 0 ≤ |u| := abs_nonneg u
    have k1' : |u| * V ≤ 28 * (Nn + N1) * H ^ 3 := by
      have := mul_le_mul_of_nonneg_left hδV hu0
      linarith
    have k2' : |u| * V * a ^ 3 ≤ 28 * H ^ 3 * ((Nn + N1) * a ^ 3) := by
      have := mul_le_mul_of_nonneg_right k1' ha3
      calc |u| * V * a ^ 3 ≤ 28 * (Nn + N1) * H ^ 3 * a ^ 3 := this
        _ = 28 * H ^ 3 * ((Nn + N1) * a ^ 3) := by ring
    have k3' : |u| * a ^ 3 * V ≤ 172032 * A ^ 4 * H ^ 6 * V := by
      have h28 : 0 ≤ 28 * H ^ 3 := by positivity
      have := mul_le_mul_of_nonneg_left hsum h28
      calc |u| * a ^ 3 * V = |u| * V * a ^ 3 := by ring
        _ ≤ 28 * H ^ 3 * ((Nn + N1) * a ^ 3) := k2'
        _ ≤ 28 * H ^ 3 * (6144 * A ^ 4 * H ^ 3 * V) := this
        _ = 172032 * A ^ 4 * H ^ 6 * V := by ring
    exact le_of_mul_le_mul_right k3' hVpos
  have hlab : ∀ L : ℤ, L * a ^ 3 ≤ 3072 * A ^ 4 * H ^ 3 * V →
      L * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 := by
    intro L hL
    have e1 : 3072 * A ^ 4 * H ^ 3 * V ≤ 3072 * A ^ 4 * H ^ 3 * (2 * H ^ 3) :=
      mul_le_mul_of_nonneg_left hVle (by positivity)
    have e2 : 0 ≤ A ^ 4 * H ^ 6 := by positivity
    have e3 : 3072 * A ^ 4 * H ^ 3 * (2 * H ^ 3) = 6144 * (A ^ 4 * H ^ 6) := by ring
    linarith
  exact ⟨fin u1 bu1, fin u2 bu2, hlab _ L0, hlab _ L1⟩

end PierceBound
