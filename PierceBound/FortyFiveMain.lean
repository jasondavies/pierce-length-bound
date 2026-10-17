import PierceBound.LatticeCount

/-!
# `P(a, b) ≪_ε a^{45/152 + ε}`

For each minor vector `p`, the gap vectors with that minor vector are counted through the
lattice `Λ_p`: at most `(8 ⌊3H/λ₁(p)⌋ + 3) Ξ` of them (`pattern_count_lattice`). Few minor vectors
have a short lattice vector (`short_count`), and every `Λ_p` has one of length
`≤ L ≍ X^{1/3}` (`pivLat_short`). Partial summation (`abel_sum`) then gives
`T ≪ Ξ (H X^{14/3} + X⁵)` in place of `T ≪ Ξ H X⁵`, so `T³ ≤ C Ξ⁹ (H³X¹⁴ + X¹⁵)`
(`two_state_window_45`). The exponent arithmetic turns this into `T¹⁵² ≤ C Δ³⁹ Ξ¹¹⁷ a⁴⁵`, hence
`P ≪ a^{45/152 + ε}`.
-/

namespace PierceBound

open Finset

/-- The polynomial range for the lattice slices. -/
def Pbig2 (a : ℕ) : ℕ := 10 ^ 1000 * a ^ 400

/-- The slack factor of the lattice count. -/
def Xi2 (a : ℕ) : ℕ := 2 * tauMax (Pbig2 a) ^ 3 * (Nat.log 3 (Pbig2 a) + 1) + 4

set_option exponentiation.threshold 1000 in
/-- The polynomial range bound. -/
lemma pbig2_bounds {a X H : ℕ} (ha : 1 ≤ a) (hH : H ≤ 29 * a) (hX : X ≤ 2 * 10 ^ 16 * a ^ 7) :
    116 * (248832 * X ^ 8) ^ 4 * (12 * H + 1) ^ 2 ≤ Pbig2 a ∧
      (11 * (248832 * X ^ 8) ^ 2 * (12 * H + 1) * (3 * (248832 * X ^ 8) + 2)) ^ 2 ≤ Pbig2 a ∧
      X ≤ Pbig2 a := by
  have hK : 248832 * X ^ 8 ≤ 248832 * 2 ^ 8 * 10 ^ 128 * a ^ 56 := by
    calc 248832 * X ^ 8 ≤ 248832 * (2 * 10 ^ 16 * a ^ 7) ^ 8 := by gcongr
      _ = 248832 * 2 ^ 8 * 10 ^ 128 * a ^ 56 := by ring
  have hH' : 12 * H + 1 ≤ 349 * a := by omega
  have hP : Pbig2 a = 10 ^ 1000 * a ^ 400 := rfl
  have hmono : ∀ k, k ≤ 400 → a ^ k ≤ a ^ 400 := fun k hk => Nat.pow_le_pow_right ha hk
  have ha1 : 1 ≤ a ^ 56 := Nat.one_le_pow _ _ ha
  refine ⟨?_, ?_, ?_⟩
  · calc 116 * (248832 * X ^ 8) ^ 4 * (12 * H + 1) ^ 2
        ≤ 116 * (248832 * 2 ^ 8 * 10 ^ 128 * a ^ 56) ^ 4 * (349 * a) ^ 2 := by gcongr
      _ = (116 * (248832 * 2 ^ 8 * 10 ^ 128) ^ 4 * 349 ^ 2) * a ^ 226 := by ring
      _ ≤ 10 ^ 1000 * a ^ 400 := Nat.mul_le_mul (by norm_num) (hmono 226 (by norm_num))
      _ = Pbig2 a := hP.symm
  · have h3 : 3 * (248832 * X ^ 8) + 2 ≤ 5 * (248832 * 2 ^ 8 * 10 ^ 128 * a ^ 56) := by
      have : 1 ≤ 248832 * 2 ^ 8 * 10 ^ 128 * a ^ 56 := by nlinarith
      omega
    calc (11 * (248832 * X ^ 8) ^ 2 * (12 * H + 1) * (3 * (248832 * X ^ 8) + 2)) ^ 2
        ≤ (11 * (248832 * 2 ^ 8 * 10 ^ 128 * a ^ 56) ^ 2 * (349 * a) *
            (5 * (248832 * 2 ^ 8 * 10 ^ 128 * a ^ 56))) ^ 2 := by gcongr
      _ = (11 * (248832 * 2 ^ 8 * 10 ^ 128) ^ 2 * 349 * 5 * (248832 * 2 ^ 8 * 10 ^ 128)) ^ 2 *
            a ^ 338 := by ring
      _ ≤ 10 ^ 1000 * a ^ 400 := Nat.mul_le_mul (by norm_num) (hmono 338 (by norm_num))
      _ = Pbig2 a := hP.symm
  · calc X ≤ 2 * 10 ^ 16 * a ^ 7 := hX
      _ ≤ 10 ^ 1000 * a ^ 400 := Nat.mul_le_mul (by norm_num) (hmono 7 (by norm_num))
      _ = Pbig2 a := hP.symm

/-- **The slack factor is `O_η(a^η)`.** -/
lemma slack_le2 (η : ℝ) (hη : 0 < η) : ∃ C > 0, ∀ a : ℕ, 1 ≤ a → (Xi2 a : ℝ) ≤ C * (a : ℝ) ^ η :=
  xi_le 1000 400 (by norm_num) η hη

/-- `1/r = 1/L + ∑_{r ≤ j < L} 1/(j(j+1))`. -/
lemma inv_telescope {r L : ℕ} (hr : 1 ≤ r) (hrL : r ≤ L) :
    (1 : ℝ) / r = 1 / L + ∑ j ∈ Ico r L, (1 : ℝ) / (j * (j + 1)) := by
  induction L, hrL using Nat.le_induction with
  | base => simp
  | succ L hL ih =>
    rw [sum_Ico_succ_top hL, ih]
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    push_cast
    field_simp
    ring

/-- **Partial summation.** -/
theorem abel_sum {ι : Type*} (S : Finset ι) (R : ι → ℕ) {L N C : ℕ}
    (hR : ∀ p ∈ S, 1 ≤ R p ∧ R p ≤ L)
    (hc : ∀ r, 1 ≤ r → (S.filter fun p => R p ≤ r).card ≤ C * r ^ 3) :
    L * ∑ p ∈ S, N / R p ≤ N * S.card + N * C * L ^ 3 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨p0, hp0⟩
  · subst hS; simp
  have hL : 1 ≤ L := ((hR p0 hp0).1).trans (hR p0 hp0).2
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set g : ℕ → ℝ := fun j => (1 : ℝ) / (j * (j + 1))
  have key : ∑ p ∈ S, (1 : ℝ) / R p =
      S.card / L + ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j := by
    have h1 : ∀ p ∈ S, (1 : ℝ) / R p = 1 / L + ∑ j ∈ Ico 1 L, if R p ≤ j then g j else 0 := by
      intro p hp
      rw [inv_telescope (hR p hp).1 (hR p hp).2, ← sum_filter]
      congr 1
      refine sum_congr ?_ fun _ _ => rfl
      ext j; simp only [mem_Ico, mem_filter]; have := (hR p hp).1; omega
    rw [sum_congr rfl h1, sum_add_distrib, sum_comm]
    congr 1
    · rw [sum_const, nsmul_eq_mul]; ring
    · refine sum_congr rfl fun j _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hbound : ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j ≤ C * L ^ 2 := by
    calc ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j
        ≤ ∑ _j ∈ Ico 1 L, (C : ℝ) * L := by
          refine sum_le_sum fun j hj => ?_
          have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
          have hjL : j < L := (mem_Ico.mp hj).2
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
          have hc' : ((S.filter fun p => R p ≤ j).card : ℝ) ≤ C * (j : ℝ) ^ 3 := by
            exact_mod_cast hc j hj1
          have hg : g j ≤ 1 / (j : ℝ) ^ 2 := by
            simp only [g]
            apply one_div_le_one_div_of_le (by positivity)
            nlinarith
          have hgp : 0 ≤ g j := by simp only [g]; positivity
          calc ((S.filter fun p => R p ≤ j).card : ℝ) * g j ≤ (C * (j : ℝ) ^ 3) * (1 / (j : ℝ) ^ 2) :=
                mul_le_mul hc' hg hgp (by positivity)
            _ = C * j := by field_simp
            _ ≤ C * L := by gcongr
      _ = ((L - 1 : ℕ) : ℝ) * (C * L) := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ C * L ^ 2 := by
          have : ((L - 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
          calc ((L - 1 : ℕ) : ℝ) * (C * L) ≤ (L : ℝ) * (C * L) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = C * L ^ 2 := by ring
  have hdiv : ∀ p ∈ S, ((N / R p : ℕ) : ℝ) ≤ N * ((1 : ℝ) / R p) := by
    intro p hp
    have hR0 : (0 : ℝ) < R p := by exact_mod_cast (show 0 < R p by have := (hR p hp).1; omega)
    rw [mul_one_div]
    exact Nat.cast_div_le
  have hreal : (L : ℝ) * ∑ p ∈ S, ((N / R p : ℕ) : ℝ) ≤ N * S.card + N * C * L ^ 3 := by
    calc (L : ℝ) * ∑ p ∈ S, ((N / R p : ℕ) : ℝ) ≤ L * ∑ p ∈ S, (N : ℝ) * ((1 : ℝ) / R p) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hdiv) hLr.le
      _ = L * (N * ∑ p ∈ S, (1 : ℝ) / R p) := by rw [mul_sum (a := (N : ℝ))]
      _ = L * (N * (S.card / L + ∑ j ∈ Ico 1 L,
            ((S.filter fun p => R p ≤ j).card : ℝ) * g j)) := by rw [key]
      _ ≤ L * (N * (S.card / L + C * L ^ 2)) := by
          gcongr
      _ = N * S.card + N * C * L ^ 3 := by field_simp
  exact_mod_cast hreal

/-- A cube root: `X ≤ L³ ≤ 8X`. -/
lemma exists_cube_root {X : ℕ} (hX : 1 ≤ X) : ∃ L : ℕ, 1 ≤ L ∧ X ≤ L ^ 3 ∧ L ^ 3 ≤ 8 * X := by
  classical
  have hex : ∃ L, X ≤ L ^ 3 := ⟨X, by nlinarith [Nat.le_self_pow (n := 3) (by norm_num) X]⟩
  set L := Nat.find hex
  have hL : X ≤ L ^ 3 := Nat.find_spec hex
  have hL1 : 1 ≤ L := by
    by_contra h; push Not at h
    have : L = 0 := by omega
    rw [this] at hL; simp at hL; omega
  refine ⟨L, hL1, hL, ?_⟩
  rcases Nat.lt_or_ge L 2 with h | h
  · have : L = 1 := by omega
    rw [this]; omega
  · have hmin : ¬ X ≤ (L - 1) ^ 3 := Nat.find_min hex (by omega)
    push Not at hmin
    have : L ≤ 2 * (L - 1) := by omega
    calc L ^ 3 ≤ (2 * (L - 1)) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 8 * (L - 1) ^ 3 := by ring
      _ ≤ 8 * X := by omega

/-- The constant of the window bound. -/
def C3w : ℕ := 32 * 607461312 ^ 3

/-- **The window arithmetic.** -/
theorem arith45 {T G L X H Xi Ssum Sc τ0 : ℕ} (hT : T ≤ 2 * G)
    (hG : G ≤ 4 * Xi * (8 * Ssum + 3 * Sc))
    (hab : L * Ssum ≤ 3 * H * Sc + 3 * H * (393660 * X ^ 4 * τ0 ^ 2) * L ^ 3)
    (hSc : Sc ≤ 14581 * X ^ 5 * τ0) (hτ : 1 ≤ τ0) (hτΞ : τ0 ≤ Xi) (hX : 1 ≤ X)
    (hL1 : X ≤ L ^ 3) (hL2 : L ^ 3 ≤ 8 * X) :
    T ^ 3 ≤ C3w * Xi ^ 9 * (H ^ 3 * X ^ 14 + X ^ 15) := by
  have hXi : 1 ≤ Xi := hτ.trans hτΞ
  have hS2 : Sc ≤ 14581 * X ^ 5 * Xi ^ 2 := by
    have : τ0 ≤ Xi ^ 2 := hτΞ.trans (Nat.le_self_pow (by norm_num) _)
    calc Sc ≤ 14581 * X ^ 5 * τ0 := hSc
      _ ≤ 14581 * X ^ 5 * Xi ^ 2 := Nat.mul_le_mul_left _ this
  have hτ2 : τ0 ^ 2 ≤ Xi ^ 2 := Nat.pow_le_pow_left hτΞ 2
  -- `T L ≤ c Ξ³ X⁵ (H + L)`
  have h1 : T * L ≤ 8 * Xi * (8 * (L * Ssum) + 3 * Sc * L) := by
    calc T * L ≤ 2 * G * L := Nat.mul_le_mul_right _ hT
      _ ≤ 2 * (4 * Xi * (8 * Ssum + 3 * Sc)) * L := by gcongr
      _ = 8 * Xi * (8 * (L * Ssum) + 3 * Sc * L) := by ring
  have h2 : 8 * (L * Ssum) + 3 * Sc * L ≤
      Xi ^ 2 * X ^ 5 * (75932664 * H + 43743 * L) := by
    have a1 : L * Ssum ≤ 3 * H * (14581 * X ^ 5 * Xi ^ 2) +
        3 * H * (393660 * X ^ 4 * Xi ^ 2) * (8 * X) := by
      calc L * Ssum ≤ 3 * H * Sc + 3 * H * (393660 * X ^ 4 * τ0 ^ 2) * L ^ 3 := hab
        _ ≤ 3 * H * (14581 * X ^ 5 * Xi ^ 2) + 3 * H * (393660 * X ^ 4 * Xi ^ 2) * (8 * X) := by
            gcongr
    have a2 : 3 * Sc * L ≤ 3 * (14581 * X ^ 5 * Xi ^ 2) * L := by gcongr
    calc 8 * (L * Ssum) + 3 * Sc * L
        ≤ 8 * (3 * H * (14581 * X ^ 5 * Xi ^ 2) + 3 * H * (393660 * X ^ 4 * Xi ^ 2) * (8 * X)) +
          3 * (14581 * X ^ 5 * Xi ^ 2) * L := add_le_add (Nat.mul_le_mul_left _ a1) a2
      _ = Xi ^ 2 * X ^ 5 * (75932664 * H + 43743 * L) := by ring
  have h3 : T * L ≤ 607461312 * (Xi ^ 3 * X ^ 5 * (H + L)) := by
    calc T * L ≤ 8 * Xi * (Xi ^ 2 * X ^ 5 * (75932664 * H + 43743 * L)) :=
          h1.trans (Nat.mul_le_mul_left _ h2)
      _ ≤ 8 * Xi * (Xi ^ 2 * X ^ 5 * (75932664 * (H + L))) := by gcongr; omega
      _ = 607461312 * (Xi ^ 3 * X ^ 5 * (H + L)) := by ring
  have hcube : (H + L) ^ 3 ≤ 4 * (H ^ 3 + L ^ 3) := by
    have : (H + L) ^ 3 + 3 * ((H + L) * (H - L) ^ 2) ≤ 4 * (H ^ 3 + L ^ 3) ∨ True := Or.inr trivial
    rcases le_total H L with h | h
    · have e : ∃ d, L = H + d := ⟨L - H, by omega⟩
      obtain ⟨d, rfl⟩ := e
      nlinarith [sq_nonneg d, Nat.zero_le (H * d), Nat.zero_le (H * d * d), Nat.zero_le (d ^ 3),
        Nat.zero_le (H ^ 2 * d)]
    · have e : ∃ d, H = L + d := ⟨H - L, by omega⟩
      obtain ⟨d, rfl⟩ := e
      nlinarith [sq_nonneg d, Nat.zero_le (L * d), Nat.zero_le (L * d * d), Nat.zero_le (d ^ 3),
        Nat.zero_le (L ^ 2 * d)]
  have h4 : T ^ 3 * X ≤ 4 * 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (H ^ 3 + 8 * X)) := by
    calc T ^ 3 * X ≤ T ^ 3 * L ^ 3 := Nat.mul_le_mul_left _ hL1
      _ = (T * L) ^ 3 := by ring
      _ ≤ (607461312 * (Xi ^ 3 * X ^ 5 * (H + L))) ^ 3 := Nat.pow_le_pow_left h3 3
      _ = 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (H + L) ^ 3) := by ring
      _ ≤ 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (4 * (H ^ 3 + L ^ 3))) := by gcongr
      _ ≤ 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (4 * (H ^ 3 + 8 * X))) := by gcongr
      _ = 4 * 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (H ^ 3 + 8 * X)) := by ring
  have h5 : T ^ 3 * X ≤ (C3w * Xi ^ 9 * (H ^ 3 * X ^ 14 + X ^ 15)) * X := by
    calc T ^ 3 * X ≤ 4 * 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (H ^ 3 + 8 * X)) := h4
      _ ≤ 32 * 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (H ^ 3 + X)) := by
          have : 4 * (H ^ 3 + 8 * X) ≤ 32 * (H ^ 3 + X) := by omega
          calc 4 * 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (H ^ 3 + 8 * X))
              = 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (4 * (H ^ 3 + 8 * X))) := by ring
            _ ≤ 607461312 ^ 3 * (Xi ^ 9 * X ^ 15 * (32 * (H ^ 3 + X))) := by gcongr
            _ = _ := by ring
      _ = (C3w * Xi ^ 9 * (H ^ 3 * X ^ 14 + X ^ 15)) * X := by unfold C3w; ring
  exact Nat.le_of_mul_le_mul_right h5 (by omega)

section Window

variable {a b : ℕ}

/-- **The window bound through the pattern lattices.** -/
theorem two_state_window_45 (hba : b < a) {s T A : ℕ} (hA : 1 ≤ A)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T) :
    T ^ 3 ≤ C3w * Xi2 a ^ 9 * ((28 * a / (A * T) + 1) ^ 3 *
      (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 14 +
      (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 15) := by
  classical
  set H : ℕ := 28 * a / (A * T) + 1 with hH
  set M : ℕ := 3609600 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  set X := M + 1 with hXdef
  set G := (Ico s (s + T)).filter fun i => i + 9 ≤ s + T ∧
    ∀ m ∈ range 7, kq a b (i + m) ≤ (H : ℤ)
  have hgood := good_card hba hA hmem hsT hT
  have ha : 0 < a := by omega
  have ha3 : 0 < a ^ 3 := by positivity
  have facts : ∀ i ∈ G, i + 8 < P a b ∧ (∀ m, m < 7 → 1 ≤ kq a b (i + m) ∧ kq a b (i + m) ≤ H) ∧
      orb a b i < 2 * A := by
    intro i hi
    obtain ⟨hiI, h9, hk⟩ := mem_filter.mp hi
    have := mem_Ico.mp hiI
    refine ⟨by omega, fun m hm => ⟨kq_pos (by omega), hk m (mem_range.mpr hm)⟩, ?_⟩
    have := (hmem (i - s) (by omega)).2; rwa [show s + (i - s) = i by omega] at this
  have hH1 : 1 ≤ H := by rw [hH]; exact Nat.le_add_left 1 _
  have hH29 : H ≤ 29 * a := by
    have : 28 * a / (A * T) ≤ 28 * a := Nat.div_le_self _ _
    omega
  have hA_a : A ≤ a := by
    have := (hmem 0 (by omega)).1
    have := (orb_le a b (s + 0)).trans hba.le
    omega
  have hMb : M ≤ 10 ^ 16 * a ^ 7 := by
    have h1 : M * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
    have h2 : 3609600 * A ^ 4 * H ^ 6 ≤ 3609600 * a ^ 4 * (29 * a) ^ 6 := by gcongr
    have h3 : M * a ^ 3 ≤ (10 ^ 16 * a ^ 7) * a ^ 3 := by
      calc M * a ^ 3 ≤ 3609600 * a ^ 4 * (29 * a) ^ 6 := h1.trans h2
        _ = 2147074259481600 * a ^ 7 * a ^ 3 := by ring
        _ ≤ (10 ^ 16 * a ^ 7) * a ^ 3 := by gcongr; norm_num
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hXb : X ≤ 2 * 10 ^ 16 * a ^ 7 := by
    have : 1 ≤ 10 ^ 16 * a ^ 7 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  obtain ⟨P1, P2, P3⟩ := pbig2_bounds (by omega) hH29 hXb
  have hX1 : 1 ≤ X := by rw [hXdef]; exact Nat.le_add_left 1 M
  -- every minor is bounded by `M`
  have hminor : ∀ i ∈ G, ∀ t, |plk (Mi a b i) t| ≤ X := by
    intro i hi t
    obtain ⟨hP, hk, hb0⟩ := facts i hi
    have := abs_le_div ha3 (by exact_mod_cast minor_height (A := A) hba hP hb0 hk t)
    have h' : ((M : ℕ) : ℤ) ≤ (X : ℤ) := by exact_mod_cast (show M ≤ X by omega)
    exact this.trans h'
  set τ0 := tauMax (Pbig2 a)
  set W := 2 * τ0 ^ 3 * (Nat.log 3 (Pbig2 a) + 1)
  have hXi : W + 4 = Xi2 a := rfl
  have hτ1 : 1 ≤ τ0 := by
    have : (1 : ℕ).divisors.card ≤ τ0 := tau_le_tauMax (Nat.one_le_iff_ne_zero.mpr
      (by unfold Pbig2; positivity))
    simpa using this
  have hτΞ : τ0 ≤ Xi2 a := by
    rw [← hXi]
    have h1 : τ0 ≤ τ0 ^ 3 := Nat.le_self_pow (by norm_num) _
    have h2 : τ0 ^ 3 ≤ 2 * τ0 ^ 3 * (Nat.log 3 (Pbig2 a) + 1) :=
      calc τ0 ^ 3 ≤ 2 * τ0 ^ 3 := by omega
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    simp only [W]; omega
  set pm : ℕ → Fin 10 → ℤ := fun i => plk (Mi a b i)
  set S := G.image pm
  have hcount := pattern_count_lattice (G := G) (θ := theta a b) (κ := kap a b) (pm := pm)
    (Q := fun i => (qq a b i : ℤ)) (a := (a : ℤ)) (M := X) (H := H) (W := W) hX1
    (fun i _ => theta_eq i) ?_ ?_ (fun i hi => hminor i hi) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left
  -- injectivity of the quotient
  · intro i hi i' hi' h
    have hP := (facts i hi).1
    have hP' := (facts i' hi').1
    simp only [Nat.cast_inj] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h.symm
  -- the matrix rows
  · intro i _
    refine ⟨Mi a b i, rfl, fun c => ?_⟩
    fin_cases c <;> simp [Mi, kap]
  -- the gaps
  · intro i hi t
    obtain ⟨-, hk, -⟩ := facts i hi
    fin_cases t
    · simpa [kap] using hk 0 (by norm_num)
    · simpa [kap] using hk 1 (by norm_num)
    · simpa [kap] using hk 2 (by norm_num)
    · simpa [kap] using hk 3 (by norm_num)
    · simpa [kap] using hk 4 (by norm_num)
  · intro i hi; simpa [theta] using Lz_pos hba (i := i) (by have := (facts i hi).1; omega)
  · intro i hi; simpa [theta] using Lz_pos hba (i := i + 1) (by have := (facts i hi).1; omega)
  · intro i _; simpa [theta, kap] using e0_at (a := a) (b := b) i
  · intro i _; simpa [theta, kap, add_assoc] using e0_at (a := a) (b := b) (i + 1)
  · intro i _; simpa [theta, kap] using e3_at (a := a) (b := b) i
  · intro i hi; simpa [theta, kap] using mult_at (a := a) (b := b) (i := i)
      (by have := (facts i hi).1; omega)
  -- the divisor and logarithm bounds
  · intro M' hM' hb
    have hτ : M'.natAbs.divisors.card ≤ τ0 := by
      refine tau_le_tauMax ?_
      have : M'.natAbs ≤ 116 * (248832 * X ^ 8) ^ 4 * (12 * H + 1) ^ 2 := by
        have h' : (M'.natAbs : ℤ) ≤ ((116 * (248832 * X ^ 8) ^ 4 * (12 * H + 1) ^ 2 : ℕ) : ℤ) := by
          rw [Int.natCast_natAbs]; push_cast at hb ⊢; linarith
        exact_mod_cast h'
      omega
    have hlog : Nat.log 3 ((11 * (248832 * X ^ 8) ^ 2 * (12 * H + 1) *
        (3 * (248832 * X ^ 8) + 2)) ^ 2) ≤ Nat.log 3 (Pbig2 a) := Nat.log_mono_right P2
    calc 2 * M'.natAbs.divisors.card ^ 3 * (Nat.log 3 ((11 * (248832 * X ^ 8) ^ 2 *
            (12 * H + 1) * (3 * (248832 * X ^ 8) + 2)) ^ 2) + 1)
          ≤ 2 * τ0 ^ 3 * (Nat.log 3 (Pbig2 a) + 1) := by gcongr
        _ = W := rfl
  -- the minor vectors
  have hS : ∀ p ∈ S, (∀ t, |p t| ≤ X) ∧ PluckerRel p ∧ p (piv p) ≠ 0 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    refine ⟨hminor i hi, plucker _, ?_⟩
    have h6 : 1 ≤ pm i 6 := by
      have := Lz_pos hba (i := i + 1) (by have := (facts i hi).1; omega)
      have e := congrFun (theta_eq (a := a) (b := b) i) 1
      simp [theta, projθ] at e
      simp only [pm]; rw [← e]; exact_mod_cast this
    intro h0
    have hle := piv_max (pm i) 6
    rw [h0, abs_zero, abs_of_pos (by omega : (0 : ℤ) < pm i 6)] at hle
    omega
  have hτX : ∀ m ∈ Icc 1 X, m.divisors.card ≤ τ0 := fun m hm =>
    tau_le_tauMax ((mem_Icc.mp hm).2.trans P3)
  have hSc : S.card ≤ 14581 * X ^ 5 * τ0 := by
    have h1 : S.card ≤ 1 + 20 * ∑ m ∈ Icc 1 X, 729 * m ^ 4 * m.divisors.card :=
      minor_vector_count fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩
    have h2 : ∑ m ∈ Icc 1 X, 729 * m ^ 4 * m.divisors.card ≤ 729 * X ^ 5 * τ0 := by
      calc ∑ m ∈ Icc 1 X, 729 * m ^ 4 * m.divisors.card ≤ ∑ _m ∈ Icc 1 X, 729 * X ^ 4 * τ0 :=
            sum_le_sum fun m hm => by
              have := (mem_Icc.mp hm).2
              gcongr
              exact hτX m hm
        _ = 729 * X ^ 5 * τ0 := by
            rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]; ring
    have : 1 ≤ X ^ 5 * τ0 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  obtain ⟨L, hL1, hLX, hLX8⟩ := exists_cube_root hX1
  have hR : ∀ p ∈ S, 1 ≤ shortR p ∧ shortR p ≤ L := by
    intro p hp
    obtain ⟨hb, hpl, hm⟩ := hS p hp
    refine ⟨(shortR_spec hm).1, shortR_le (pivLat_short hpl hm ?_)⟩
    have : (p (piv p)).natAbs ≤ X := by
      have := hb (piv p)
      have h' : ((p (piv p)).natAbs : ℤ) ≤ X := by rw [Int.natCast_natAbs]; exact this
      exact_mod_cast h'
    calc (p (piv p)).natAbs ≤ L ^ 3 := this.trans hLX
      _ < (L + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hab := abel_sum S shortR (N := 3 * H) (C := 393660 * X ^ 4 * τ0 ^ 2) hR fun r _ =>
    (short_count (Y := X) (R := r) hS hτX).trans (by ring_nf; exact le_rfl)
  refine arith45 (G := G.card) (L := L) (Ssum := ∑ p ∈ S, 3 * H / shortR p) (Sc := S.card)
    (τ0 := τ0) hgood ?_ (by ring_nf; ring_nf at hab; exact hab) hSc hτ1 hτΞ hX1 hLX hLX8
  rw [← hXi]
  calc G.card ≤ ∑ p ∈ S, 4 * ((2 * (4 * (3 * H / shortR p) + 1) + 1) * (W + 4)) := hcount
    _ = 4 * (W + 4) * (8 * ∑ p ∈ S, 3 * H / shortR p + 3 * S.card) := by
        have e : ∀ p ∈ S, 4 * ((2 * (4 * (3 * H / shortR p) + 1) + 1) * (W + 4)) =
            4 * (W + 4) * 8 * (3 * H / shortR p) + 4 * (W + 4) * 3 := fun p _ => by ring
        rw [sum_congr rfl e, sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul]
        ring

end Window

section Exponent

/-- The constants of the exponent arithmetic. -/
def c0w : ℕ := 512 * (2 * C3w) * 56 ^ 3
def cAw : ℕ := 2 ^ 15 * C3w * 3609600 ^ 14 * 56 ^ 87
def cBw : ℕ := 2 ^ 16 * C3w * 3609600 ^ 15 * 56 ^ 90
def C152 : ℕ := 122449 ^ 38 + c0w ^ 13 + 8 ^ 31 * cAw + 8 ^ 30 * cBw

lemma mono_152 {Δ X a c e f g : ℕ} (hΔ : 1 ≤ Δ) (hX : 1 ≤ X) (ha : 1 ≤ a) (hc : c ≤ C152)
    (he : e ≤ 39) (hf : f ≤ 117) (hg : g ≤ 45) :
    c * Δ ^ e * X ^ f * a ^ g ≤ C152 * Δ ^ 39 * X ^ 117 * a ^ 45 :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right hΔ he))
    (Nat.pow_le_pow_right hX hf)) (Nat.pow_le_pow_right ha hg)

/-- The case `AT > 28a`: then `T⁴ ≤ 122449 a`. -/
lemma window_152_big {a A T Δ X : ℕ} (ha : 1 ≤ a) (hΔ : 1 ≤ Δ) (hX : 1 ≤ X)
    (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hbig : 28 * a < A * T) :
    T ^ 152 ≤ C152 * Δ ^ 39 * X ^ 117 * a ^ 45 := by
  have hC1 : 122449 ^ 38 ≤ C152 := by unfold C152; omega
  have h1 : (28 * a) ^ 2 * T ^ 4 ≤ 96000000 * a ^ 3 := by
    calc (28 * a) ^ 2 * T ^ 4 ≤ (A * T) ^ 2 * T ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbig.le 2)
      _ = T ^ 6 * A ^ 2 := by ring
      _ ≤ _ := hsix
  have h2 : T ^ 4 ≤ 122449 * a := by
    have : (784 * T ^ 4) * a ^ 2 ≤ (784 * (122449 * a)) * a ^ 2 := by
      calc (784 * T ^ 4) * a ^ 2 = (28 * a) ^ 2 * T ^ 4 := by ring
        _ ≤ 96000000 * a ^ 3 := h1
        _ ≤ (784 * (122449 * a)) * a ^ 2 := by ring_nf; omega
    have := Nat.le_of_mul_le_mul_right this (by positivity)
    omega
  calc T ^ 152 = (T ^ 4) ^ 38 := by ring
    _ ≤ (122449 * a) ^ 38 := Nat.pow_le_pow_left h2 38
    _ = 122449 ^ 38 * Δ ^ 0 * X ^ 0 * a ^ 38 := by ring
    _ ≤ _ := mono_152 hΔ hX ha hC1 (by norm_num) (by norm_num) (by norm_num)

/-- The case `Y = 0` (minor height `1`): `T³ ≤ C (H³ + 1)`. -/
lemma window_152_zero {a A T Δ X H : ℕ} (ha : 1 ≤ a) (hΔ : 1 ≤ Δ) (hX : 1 ≤ X) (hT : 36 ≤ T)
    (hH1 : 1 ≤ H) (hT2 : T ^ 2 ≤ 8 * A * Δ) (hHAT : H * (A * T) ≤ 56 * a)
    (hwin : T ^ 3 ≤ C3w * X ^ 9 * (H ^ 3 + 1)) :
    T ^ 152 ≤ C152 * Δ ^ 39 * X ^ 117 * a ^ 45 := by
  have hC2 : c0w ^ 13 ≤ C152 := by unfold C152; omega
  have h1 : T ^ 3 ≤ 2 * C3w * X ^ 9 * H ^ 3 := by
    have : H ^ 3 + 1 ≤ 2 * H ^ 3 := by
      have : 1 ≤ H ^ 3 := Nat.one_le_pow _ _ hH1
      omega
    calc T ^ 3 ≤ C3w * X ^ 9 * (H ^ 3 + 1) := hwin
      _ ≤ C3w * X ^ 9 * (2 * H ^ 3) := Nat.mul_le_mul_left _ this
      _ = 2 * C3w * X ^ 9 * H ^ 3 := by ring
  have h2 : T ^ 6 * A ^ 3 ≤ 2 * C3w * 56 ^ 3 * X ^ 9 * a ^ 3 := by
    calc T ^ 6 * A ^ 3 = T ^ 3 * (A * T) ^ 3 := by ring
      _ ≤ 2 * C3w * X ^ 9 * H ^ 3 * (A * T) ^ 3 := Nat.mul_le_mul_right _ h1
      _ = 2 * C3w * X ^ 9 * (H * (A * T)) ^ 3 := by ring
      _ ≤ 2 * C3w * X ^ 9 * (56 * a) ^ 3 := by gcongr
      _ = 2 * C3w * 56 ^ 3 * X ^ 9 * a ^ 3 := by ring
  have h3 : T ^ 12 ≤ c0w * Δ ^ 3 * X ^ 9 * a ^ 3 := by
    calc T ^ 12 = T ^ 6 * (T ^ 2) ^ 3 := by ring
      _ ≤ T ^ 6 * (8 * A * Δ) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT2 3)
      _ = 512 * Δ ^ 3 * (T ^ 6 * A ^ 3) := by ring
      _ ≤ 512 * Δ ^ 3 * (2 * C3w * 56 ^ 3 * X ^ 9 * a ^ 3) := Nat.mul_le_mul_left _ h2
      _ = c0w * Δ ^ 3 * X ^ 9 * a ^ 3 := by unfold c0w; ring
  calc T ^ 152 ≤ T ^ 156 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ = (T ^ 12) ^ 13 := by ring
    _ ≤ (c0w * Δ ^ 3 * X ^ 9 * a ^ 3) ^ 13 := Nat.pow_le_pow_left h3 13
    _ = c0w ^ 13 * Δ ^ 39 * X ^ 117 * a ^ 39 := by ring
    _ ≤ _ := mono_152 hΔ hX ha hC2 (by norm_num) (by norm_num) (by norm_num)

/-- The case `2Y ≤ H³`: `T³ ≪ H³ Y¹⁴`. -/
lemma window_152_A {a A T Δ X H Y : ℕ} (ha : 1 ≤ a) (hA : 1 ≤ A) (hΔ : 1 ≤ Δ) (hX : 1 ≤ X)
    (hT2 : T ^ 2 ≤ 8 * A * Δ) (hHAT : H * (A * T) ≤ 56 * a)
    (hYa : Y * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6)
    (hw1 : T ^ 3 ≤ C3w * X ^ 9 * (H ^ 3 * (2 * Y) ^ 14 + (2 * Y) ^ 15)) (hc : 2 * Y ≤ H ^ 3) :
    T ^ 152 ≤ C152 * Δ ^ 39 * X ^ 117 * a ^ 45 := by
  have hC3 : 8 ^ 31 * cAw ≤ C152 := by unfold C152; omega
  have hAa : 0 < A ^ 56 * a ^ 42 := by positivity
  have h1 : T ^ 3 ≤ 2 * C3w * X ^ 9 * H ^ 3 * (2 * Y) ^ 14 := by
    have : (2 * Y) ^ 15 ≤ H ^ 3 * (2 * Y) ^ 14 := by
      calc (2 * Y) ^ 15 = (2 * Y) * (2 * Y) ^ 14 := by ring
        _ ≤ H ^ 3 * (2 * Y) ^ 14 := Nat.mul_le_mul_right _ hc
    calc T ^ 3 ≤ C3w * X ^ 9 * (H ^ 3 * (2 * Y) ^ 14 + (2 * Y) ^ 15) := hw1
      _ ≤ C3w * X ^ 9 * (H ^ 3 * (2 * Y) ^ 14 + H ^ 3 * (2 * Y) ^ 14) := by gcongr
      _ = 2 * C3w * X ^ 9 * H ^ 3 * (2 * Y) ^ 14 := by ring
  have h2 : T ^ 3 * a ^ 42 ≤ 2 ^ 15 * C3w * 3609600 ^ 14 * X ^ 9 * A ^ 56 * H ^ 87 := by
    calc T ^ 3 * a ^ 42 ≤ 2 * C3w * X ^ 9 * H ^ 3 * (2 * Y) ^ 14 * a ^ 42 :=
          Nat.mul_le_mul_right _ h1
      _ = 2 ^ 15 * C3w * X ^ 9 * H ^ 3 * (Y * a ^ 3) ^ 14 := by ring
      _ ≤ 2 ^ 15 * C3w * X ^ 9 * H ^ 3 * (3609600 * A ^ 4 * H ^ 6) ^ 14 := by gcongr
      _ = 2 ^ 15 * C3w * 3609600 ^ 14 * X ^ 9 * A ^ 56 * H ^ 87 := by ring
  have h3 : (T ^ 90 * A ^ 31) * (A ^ 56 * a ^ 42) ≤ (cAw * X ^ 9 * a ^ 45) * (A ^ 56 * a ^ 42) := by
    calc (T ^ 90 * A ^ 31) * (A ^ 56 * a ^ 42) = T ^ 3 * a ^ 42 * (A * T) ^ 87 := by ring
      _ ≤ 2 ^ 15 * C3w * 3609600 ^ 14 * X ^ 9 * A ^ 56 * H ^ 87 * (A * T) ^ 87 :=
          Nat.mul_le_mul_right _ h2
      _ = 2 ^ 15 * C3w * 3609600 ^ 14 * X ^ 9 * A ^ 56 * (H * (A * T)) ^ 87 := by ring
      _ ≤ 2 ^ 15 * C3w * 3609600 ^ 14 * X ^ 9 * A ^ 56 * (56 * a) ^ 87 := by gcongr
      _ = (cAw * X ^ 9 * a ^ 45) * (A ^ 56 * a ^ 42) := by unfold cAw; ring
  have h4 := Nat.le_of_mul_le_mul_right h3 hAa
  calc T ^ 152 = T ^ 90 * (T ^ 2) ^ 31 := by ring
    _ ≤ T ^ 90 * (8 * A * Δ) ^ 31 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT2 31)
    _ = 8 ^ 31 * Δ ^ 31 * (T ^ 90 * A ^ 31) := by ring
    _ ≤ 8 ^ 31 * Δ ^ 31 * (cAw * X ^ 9 * a ^ 45) := Nat.mul_le_mul_left _ h4
    _ = 8 ^ 31 * cAw * Δ ^ 31 * X ^ 9 * a ^ 45 := by ring
    _ ≤ _ := mono_152 hΔ hX ha hC3 (by norm_num) (by norm_num) (by norm_num)

/-- The case `2Y ≥ H³`: `T³ ≪ Y¹⁵`. -/
lemma window_152_B {a A T Δ X H Y : ℕ} (ha : 1 ≤ a) (hA : 1 ≤ A) (hΔ : 1 ≤ Δ) (hX : 1 ≤ X)
    (hT : 36 ≤ T) (hT2 : T ^ 2 ≤ 8 * A * Δ) (hHAT : H * (A * T) ≤ 56 * a)
    (hYa : Y * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6)
    (hw1 : T ^ 3 ≤ C3w * X ^ 9 * (H ^ 3 * (2 * Y) ^ 14 + (2 * Y) ^ 15)) (hc : H ^ 3 ≤ 2 * Y) :
    T ^ 152 ≤ C152 * Δ ^ 39 * X ^ 117 * a ^ 45 := by
  have hC4 : 8 ^ 30 * cBw ≤ C152 := by unfold C152; omega
  have h1 : T ^ 3 ≤ 2 * C3w * X ^ 9 * (2 * Y) ^ 15 := by
    have : H ^ 3 * (2 * Y) ^ 14 ≤ (2 * Y) ^ 15 := by
      calc H ^ 3 * (2 * Y) ^ 14 ≤ (2 * Y) * (2 * Y) ^ 14 := Nat.mul_le_mul_right _ hc
        _ = (2 * Y) ^ 15 := by ring
    calc T ^ 3 ≤ C3w * X ^ 9 * (H ^ 3 * (2 * Y) ^ 14 + (2 * Y) ^ 15) := hw1
      _ ≤ C3w * X ^ 9 * ((2 * Y) ^ 15 + (2 * Y) ^ 15) := by gcongr
      _ = 2 * C3w * X ^ 9 * (2 * Y) ^ 15 := by ring
  have h2 : T ^ 3 * a ^ 45 ≤ 2 ^ 16 * C3w * 3609600 ^ 15 * X ^ 9 * A ^ 60 * H ^ 90 := by
    calc T ^ 3 * a ^ 45 ≤ 2 * C3w * X ^ 9 * (2 * Y) ^ 15 * a ^ 45 := Nat.mul_le_mul_right _ h1
      _ = 2 ^ 16 * C3w * X ^ 9 * (Y * a ^ 3) ^ 15 := by ring
      _ ≤ 2 ^ 16 * C3w * X ^ 9 * (3609600 * A ^ 4 * H ^ 6) ^ 15 := by gcongr
      _ = 2 ^ 16 * C3w * 3609600 ^ 15 * X ^ 9 * A ^ 60 * H ^ 90 := by ring
  have hAa' : 0 < A ^ 60 * a ^ 45 := by positivity
  have h3 : (T ^ 93 * A ^ 30) * (A ^ 60 * a ^ 45) ≤ (cBw * X ^ 9 * a ^ 45) * (A ^ 60 * a ^ 45) := by
    calc (T ^ 93 * A ^ 30) * (A ^ 60 * a ^ 45) = T ^ 3 * a ^ 45 * (A * T) ^ 90 := by ring
      _ ≤ 2 ^ 16 * C3w * 3609600 ^ 15 * X ^ 9 * A ^ 60 * H ^ 90 * (A * T) ^ 90 :=
          Nat.mul_le_mul_right _ h2
      _ = 2 ^ 16 * C3w * 3609600 ^ 15 * X ^ 9 * A ^ 60 * (H * (A * T)) ^ 90 := by ring
      _ ≤ 2 ^ 16 * C3w * 3609600 ^ 15 * X ^ 9 * A ^ 60 * (56 * a) ^ 90 := by gcongr
      _ = (cBw * X ^ 9 * a ^ 45) * (A ^ 60 * a ^ 45) := by unfold cBw; ring
  have h4 := Nat.le_of_mul_le_mul_right h3 hAa'
  calc T ^ 152 ≤ T ^ 153 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ = T ^ 93 * (T ^ 2) ^ 30 := by ring
    _ ≤ T ^ 93 * (8 * A * Δ) ^ 30 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT2 30)
    _ = 8 ^ 30 * Δ ^ 30 * (T ^ 93 * A ^ 30) := by ring
    _ ≤ 8 ^ 30 * Δ ^ 30 * (cBw * X ^ 9 * a ^ 45) := Nat.mul_le_mul_left _ h4
    _ = 8 ^ 30 * cBw * Δ ^ 30 * X ^ 9 * a ^ 45 := by ring
    _ ≤ _ := mono_152 hΔ hX ha hC4 (by norm_num) (by norm_num) (by norm_num)

/-- **The exponent arithmetic.** Every window run satisfies `T¹⁵² ≤ C Δ³⁹ Ξ¹¹⁷ a⁴⁵`. -/
theorem window_152 {a A T Δ X : ℕ} (ha : 1 ≤ a) (hA : 1 ≤ A) (hΔ : 1 ≤ Δ) (hX : 1 ≤ X)
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hwin : T ^ 3 ≤ C3w * X ^ 9 * ((28 * a / (A * T) + 1) ^ 3 *
      (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 14 +
      (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 15)) :
    T ^ 152 ≤ C152 * Δ ^ 39 * X ^ 117 * a ^ 45 := by
  set H := 28 * a / (A * T) + 1 with hH
  set Y := 3609600 * A ^ 4 * H ^ 6 / a ^ 3 with hY
  have hH1 : 1 ≤ H := by rw [hH]; exact Nat.le_add_left 1 _
  have hT2 : T ^ 2 ≤ 8 * A * Δ := by
    have : T ^ 2 ≤ 2 * (T * (T - 1)) := by
      have : T ≤ 2 * (T - 1) := by omega
      calc T ^ 2 = T * T := pow_two T
        _ ≤ T * (2 * (T - 1)) := Nat.mul_le_mul_left _ this
        _ = 2 * (T * (T - 1)) := by ring
    calc T ^ 2 ≤ 2 * (T * (T - 1)) := this
      _ ≤ 2 * (4 * A * Δ) := Nat.mul_le_mul_left _ hdrop
      _ = 8 * A * Δ := by ring
  by_cases hbig : 28 * a < A * T
  · exact window_152_big ha hΔ hX hsix hbig
  push Not at hbig
  have hHAT : H * (A * T) ≤ 56 * a := by
    have := Nat.div_mul_le_self (28 * a) (A * T)
    calc H * (A * T) = 28 * a / (A * T) * (A * T) + A * T := by rw [hH]; ring
      _ ≤ 56 * a := by omega
  rcases Nat.eq_zero_or_pos Y with hY0 | hY1
  · rw [hY0] at hwin
    simp only [zero_add, one_pow, mul_one] at hwin
    exact window_152_zero ha hΔ hX hT hH1 hT2 hHAT hwin
  · have hYa : Y * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
    have hw1 : T ^ 3 ≤ C3w * X ^ 9 * (H ^ 3 * (2 * Y) ^ 14 + (2 * Y) ^ 15) := by
      have : Y + 1 ≤ 2 * Y := by omega
      calc T ^ 3 ≤ C3w * X ^ 9 * (H ^ 3 * (Y + 1) ^ 14 + (Y + 1) ^ 15) := hwin
        _ ≤ C3w * X ^ 9 * (H ^ 3 * (2 * Y) ^ 14 + (2 * Y) ^ 15) := by gcongr
    rcases le_total (2 * Y) (H ^ 3) with hc | hc
    · exact window_152_A ha hA hΔ hX hT2 hHAT hYa hw1 hc
    · exact window_152_B ha hA hΔ hX hT hT2 hHAT hYa hw1 hc

end Exponent

section Global

/-- Every dyadic window satisfies `T ≤ 35` or `T¹⁵² ≤ C Δ³⁹ Ξ(a)¹¹⁷ a⁴⁵`. -/
theorem visits_152 {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) (hΔ1 : 1 ≤ Δ) :
    (visits a b k).card ≤ 35 ∨
      (visits a b k).card ^ 152 ≤ C152 * Δ ^ 39 * Xi2 a ^ 117 * a ^ 45 := by
  by_cases hT : (visits a b k).card ≤ 35
  · exact Or.inl hT
  right
  set T := (visits a b k).card
  have hne : (visits a b k).Nonempty := by rw [← card_pos]; omega
  have W := visits_window hba.le hne
  set s := (visits a b k).min' hne
  have hmem : ∀ j < T, 2 ^ k ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * 2 ^ k := W.mem
  have hsT : s + T ≤ P a b := by
    have h := (hmem (T - 1) (by omega)).1
    have := lt_P_of_orb_pos (a := a) (b := b) (i := s + (T - 1))
      (lt_of_lt_of_le (Nat.two_pow_pos k) h)
    omega
  exact window_152 (by omega) Nat.one_le_two_pow hΔ1 (by unfold Xi2; omega) (by omega)
    (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (two_state_window_45 hba Nat.one_le_two_pow hmem hsT (by omega))

/-- **Theorem.** `P(a, b) ≪_ε a^{45/152 + ε}` uniformly in `0 < b < a`. -/
theorem P_le_45_152 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((45 : ℝ) / 152 + ε) := by
  intro ε hε
  obtain ⟨Cs, hCs, hslack⟩ := slack_le (ε / 312) (by positivity)
  obtain ⟨Cs2, hCs2, hslack2⟩ := slack_le2 (ε / 312) (by positivity)
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (ε / 2) (by positivity)
  set K : ℝ := (C152 : ℝ) * Cs ^ 39 * Cs2 ^ 117
  set C2 : ℝ := K ^ ((152 : ℝ)⁻¹)
  have hK : 0 < K := by
    have : (0 : ℝ) < C152 := by unfold C152; positivity
    positivity
  have hC2 : 0 ≤ C2 := by positivity
  refine ⟨CL * (35 + C2), by positivity, fun a b hb hba => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  set Δ := tauMax (32 * a ^ 7)
  have hΔ : DivBound a Δ := fun n _ hn =>
    le_sup (f := fun n => n.divisors.card) (mem_range.mpr (by omega))
  have hΔ1 : 1 ≤ Δ := by
    have h7 : 1 ≤ a ^ 7 := Nat.one_le_pow _ _ ha1
    have h1 : (1 : ℕ).divisors.card ≤ Δ :=
      le_sup (f := fun n => n.divisors.card) (mem_range.mpr (by omega))
    rw [Nat.divisors_one, card_singleton] at h1
    exact h1
  have hsΔ := (hslack a ha1).1
  have hsX := hslack2 a ha1
  set β : ℝ := 45 / 152 + ε / 2
  have hβ : 1 ≤ (a : ℝ) ^ β := Real.one_le_rpow ha (by positivity)
  have hwin : ∀ k, ((visits a b k).card : ℝ) ≤ (35 + C2) * (a : ℝ) ^ β := by
    intro k
    rcases visits_152 (k := k) hba hΔ hΔ1 with h | h
    · have : ((visits a b k).card : ℝ) ≤ 35 := by exact_mod_cast h
      nlinarith
    · set T := (visits a b k).card
      have hTr : (T : ℝ) ^ 152 ≤ K * (a : ℝ) ^ (45 + 156 * (ε / 312)) := by
        have h' : (T : ℝ) ^ 152 ≤ (C152 : ℝ) * (Δ : ℝ) ^ 39 * (Xi2 a : ℝ) ^ 117 * (a : ℝ) ^ 45 := by
          exact_mod_cast h
        have p1 : (Δ : ℝ) ^ 39 ≤ (Cs * (a : ℝ) ^ (ε / 312)) ^ 39 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsΔ 39
        have p2 : (Xi2 a : ℝ) ^ 117 ≤ (Cs2 * (a : ℝ) ^ (ε / 312)) ^ 117 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsX 117
        have q1 : ((a : ℝ) ^ (ε / 312)) ^ 156 = (a : ℝ) ^ (156 * (ε / 312)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num; ring_nf
        have q2 : (a : ℝ) ^ (45 : ℕ) = (a : ℝ) ^ (45 : ℝ) := by
          rw [← Real.rpow_natCast]; norm_num
        calc (T : ℝ) ^ 152 ≤ (C152 : ℝ) * (Δ : ℝ) ^ 39 * (Xi2 a : ℝ) ^ 117 * (a : ℝ) ^ 45 := h'
          _ ≤ (C152 : ℝ) * (Cs * (a : ℝ) ^ (ε / 312)) ^ 39 * (Cs2 * (a : ℝ) ^ (ε / 312)) ^ 117 *
              (a : ℝ) ^ 45 := by gcongr
          _ = (C152 : ℝ) * Cs ^ 39 * Cs2 ^ 117 * ((a : ℝ) ^ (ε / 312)) ^ 156 *
              (a : ℝ) ^ (45 : ℕ) := by ring
          _ = K * (a : ℝ) ^ (45 + 156 * (ε / 312)) := by
              rw [q1, q2, Real.rpow_add (by positivity)]; simp only [K]; ring
      have hroot : (T : ℝ) ≤ C2 * (a : ℝ) ^ ((45 + 156 * (ε / 312)) / 152) := by
        have h1 : ((T : ℝ) ^ 152) ^ ((152 : ℝ)⁻¹) ≤
            (K * (a : ℝ) ^ (45 + 156 * (ε / 312))) ^ ((152 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hTr (by positivity)
        rw [show (152 : ℝ) = ((152 : ℕ) : ℝ) by norm_num,
          Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num),
          Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul (by positivity)] at h1
        simp only [C2]
        convert h1 using 2
        all_goals norm_num
        all_goals (congr 1; ring)
      have hexp : (45 + 156 * (ε / 312)) / 152 ≤ β := by simp only [β]; nlinarith
      have := Real.rpow_le_rpow_of_exponent_le ha hexp
      nlinarith [mul_le_mul_of_nonneg_left this hC2]
  have hP : (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((35 + C2) * (a : ℝ) ^ β) := by
    rw [P_eq_sum_visits hba.le]
    push_cast
    calc ∑ k ∈ range (Nat.log 2 a + 1), ((visits a b k).card : ℝ)
        ≤ ∑ _k ∈ range (Nat.log 2 a + 1), (35 + C2) * (a : ℝ) ^ β :=
          sum_le_sum fun k _ => hwin k
      _ = _ := by simp
  have hL := hlog a ha1
  calc (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((35 + C2) * (a : ℝ) ^ β) := hP
    _ ≤ (CL * (a : ℝ) ^ (ε / 2)) * ((35 + C2) * (a : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_right hL (by positivity)
    _ = CL * (35 + C2) * ((a : ℝ) ^ (ε / 2) * (a : ℝ) ^ β) := by ring
    _ = CL * (35 + C2) * (a : ℝ) ^ ((45 : ℝ) / 152 + ε) := by
        rw [← Real.rpow_add (by positivity)]
        congr 2
        simp only [β]; ring

end Global

end PierceBound
