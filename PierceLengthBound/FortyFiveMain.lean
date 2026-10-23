/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.CubeRoot
public import PierceLengthBound.LatticeCount
public import PierceLengthBound.EightMain

/-!
# `P(a, b) ≪_ε a^{45/152 + ε}`

For each minor vector `p`, the gap vectors with that minor vector are counted through the
lattice `Λ_p`: at most `(8 ⌊3H/λ₁(p)⌋ + 3) Ξ` of them (`pattern_count_lattice`). Few minor vectors
have a short lattice vector (`short_count`), and every `Λ_p` has one of length
`≤ L ≍ X^{1/3}` (`pivLat_short`). Partial summation (`abel_sum`) then gives
`T ≪ Ξ (H X^{14/3} + X⁵)` in place of `T ≪ Ξ H X⁵`, so `T³ ≤ C Ξ⁹ (H³X¹⁴ + X¹⁵)`
(`two_state_window_152`). The exponent arithmetic turns this into `T¹⁵² ≤ C Δ³⁹ Ξ¹¹⁷ a⁴⁵`, hence
`P ≪ a^{45/152 + ε}`.
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- The polynomial range for the lattice slices. -/
abbrev Pbig2 : ℕ → ℕ := PbigOf 1000 400

/-- The slack factor of the lattice count. -/
abbrev Xi2 : ℕ → ℕ := XiOf 1000 400

set_option exponentiation.threshold 1000 in
-- `norm_num` must evaluate the constant `10 ^ 1000` of `Pbig2`.
/-- The polynomial range bound. -/
lemma pbig2_bounds {a X H : ℕ} (ha : 1 ≤ a) (hH : H ≤ 29 * a) (hX : X ≤ 2 * 10 ^ 16 * a ^ 7) :
    116 * (248832 * X ^ 8) ^ 4 * (12 * H + 1) ^ 2 ≤ Pbig2 a ∧
      (11 * (248832 * X ^ 8) ^ 2 * (12 * H + 1) * (3 * (248832 * X ^ 8) + 2)) ^ 2 ≤ Pbig2 a ∧
      X ≤ Pbig2 a :=
  pbig_bounds (k := 248832 * 2 ^ 8 * 10 ^ 128) (p := 56) (h := 349) ha (by norm_num)
    ((Nat.mul_le_mul_left 248832 (Nat.pow_le_pow_left hX 8)).trans_eq (by ring)) (by omega) hX
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The slack factor is `O_η(a^η)`.** -/
lemma slack_le2 : SlowGrowth Xi2 := xiOf_slow 1000 400

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
          calc ((S.filter fun p => R p ≤ j).card : ℝ) * g j ≤ (C * (j : ℝ) ^ 3)
                 * (1 / (j : ℝ) ^ 2) :=
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

/-- The constant of the window bound. -/
def C3w : ℕ := 32 * 607461312 ^ 3

/-- **The window arithmetic.** -/
theorem arith_152 {T G L X H Xi Ssum Sc τ0 : ℕ} (hT : T ≤ 2 * G)
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
theorem two_state_window_152 (hba : b < a) {s T A : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T) :
    T ^ 3 ≤ C3w * Xi2 a ^ 9 * ((28 * a / (A * T) + 1) ^ 3 *
      (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 14 +
      (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 15) := by
  classical
  obtain ⟨hH29, hMb⟩ := run_height_le hba hmem (by omega) 3609600
  have hXb : 3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1 ≤ 2 * 10 ^ 16 * a ^ 7 := by
    have : 1 ≤ a ^ 7 := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨P1, P2, P3⟩ := pbig2_bounds (by omega) hH29 hXb
  set H : ℕ := 28 * a / (A * T) + 1 with hH
  set M : ℕ := 3609600 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  set X := M + 1 with hXdef
  set G := goodStarts a b s T H
  have hX1 : 1 ≤ X := Nat.le_add_left 1 M
  have hp := goodStarts_patternHyps (H := H) hba hmem hsT
  -- every minor is bounded by `X`
  have hminor : ∀ i ∈ G, ∀ t, |plk (Mi a b i) t| ≤ X := fun i hi t =>
    (goodStarts_minor_le hba hmem hsT i hi t).trans (by exact_mod_cast Nat.le_succ M)
  set τ0 := tauMax (Pbig2 a)
  set W := 2 * τ0 ^ 3 * (Nat.log 3 (Pbig2 a) + 1)
  have hXi : W + 4 = Xi2 a := rfl
  have hτ1 : 1 ≤ τ0 := by simpa using tau_le_tauMax (n := 1) (hX1.trans P3)
  have hτΞ : τ0 ≤ Xi2 a := tauMax_le_xiOf _ _ _
  set pm : ℕ → Fin 10 → ℤ := fun i => plk (Mi a b i)
  set S := G.image pm
  have hcount := pattern_count_lattice (pm := pm) hX1 (fun i _ => theta_eq i) hp.inj
    (fun i _ => ⟨Mi a b i, rfl, fun c => by fin_cases c <;> simp [Mi, kap]⟩) hminor hp.gaps
    hp.pos0 hp.pos1 hp.e0 hp.e4 hp.e3 hp.mult (slack_le_range P1 P2)
  -- the minor vectors
  have hS : ∀ p ∈ S, (∀ t, |p t| ≤ X) ∧ PluckerRel p ∧ p (piv p) ≠ 0 := by
    intro p hp'
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp'
    refine ⟨hminor i hi, plucker _, ?_⟩
    have h6 : 1 ≤ pm i 6 := by
      have := hp.pos1 i hi
      have e := congrFun (theta_eq (a := a) (b := b) i) 1
      simp only [theta, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, projθ] at e this
      simp only [pm]; rw [← e]; exact this
    exact piv_ne_zero (by omega : pm i 6 ≠ 0)
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
  refine arith_152 (G := G.card) (L := L) (Ssum := ∑ p ∈ S, 3 * H / shortR p) (Sc := S.card)
    (τ0 := τ0) (good_card hba hmem hsT hT) ?_ (by ring_nf; ring_nf at hab; exact hab) hSc hτ1
    hτΞ hX1 hLX hLX8
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
  have h2 := window_large_mean_gap ha hsix hbig
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
theorem window_152 {a A T Δ X : ℕ}
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hwin : T ^ 3 ≤ C3w * X ^ 9 * ((28 * a / (A * T) + 1) ^ 3 *
      (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 14 +
      (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 15)) :
    T ^ 152 ≤ C152 * Δ ^ 39 * X ^ 117 * a ^ 45 := by
  obtain ⟨hA, hΔ, ha, hT2⟩ := window_facts (by omega) hsix hdrop
  have hX : 1 ≤ X := Nat.pos_of_ne_zero fun h => by simp [h] at hwin; omega
  set H := 28 * a / (A * T) + 1 with hH
  set Y := 3609600 * A ^ 4 * H ^ 6 / a ^ 3 with hY
  have hH1 : 1 ≤ H := Nat.le_add_left 1 _
  by_cases hbig : 28 * a < A * T
  · exact window_152_big ha hΔ hX hsix hbig
  push Not at hbig
  have hHAT : H * (A * T) ≤ 56 * a := gap_height_mul_le hbig
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
theorem visits_152 {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 35 ∨
      (visits a b k).card ^ 152 ≤ C152 * Δ ^ 39 * Xi2 a ^ 117 * a ^ 45 := by
  refine or_iff_not_imp_left.mpr fun hT => ?_
  obtain ⟨s, W, hsT⟩ := visits_run (k := k) hba.le (by omega)
  exact window_152 (by omega) (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (two_state_window_152 hba W.mem hsT (by omega))

/-- **Theorem.** `P(a, b) ≪_ε a^{45/152 + ε}` uniformly in `0 < b < a`. -/
theorem P_le_45_152 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((45 : ℝ) / 152 + ε) := by
  simpa only [Nat.cast_ofNat] using P_le_of_visits (N := 152) (r := 45) (K := C152)
    (by norm_num) (((tauMax_slow 32 7).pow 39).mul (slack_le2.pow 117)) fun a b k _ hba =>
      (visits_152 (k := k) hba (tauMax_divBound a)).imp id fun h => h.trans_eq (by ring)

end Global

end PierceLengthBound
