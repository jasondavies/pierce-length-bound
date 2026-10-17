import PierceBound.ElevenCount
import PierceBound.TwoStateMain

/-!
# `P(a, b) ≪_ε a^{11/37 + ε}`

The two-state pattern of `TwoStateMain.lean`, counted with the ternary quadratic of
`ElevenCount.lean`, gives `T ≤ 24 (2M+1)⁷ H Ξ(a)` for a window run (`two_state_window_eleven`),
where `Ξ(a) = 2 τ_max³ (log₃ P(a) + 1) + 4` collects the divisor and logarithm factors of
`norm_count` over the polynomial range `[1, P(a)]`, `P(a) = 10³⁰⁰ a¹⁰⁰`. With the six-step
and drop bounds this gives `T⁷⁴ ≤ C Δ¹⁹ Ξ(a)¹⁹ a²²` (`window_74`). Both `Δ` and `Ξ(a)` are
`O_η(a^η)`, which gives the theorem (`P_le_11_37`).
-/

namespace PierceBound

open Finset

/-- The polynomial range `P(a) = 10³⁰⁰ a¹⁰⁰` containing all norm-equation right sides. -/
def Pbig (a : ℕ) : ℕ := 10 ^ 300 * a ^ 100

/-- `max_{n ≤ X} τ(n)`. -/
def tauMax (X : ℕ) : ℕ := (range (X + 1)).sup fun n => n.divisors.card

/-- The slack factor `Ξ(a)`. -/
def Xi (a : ℕ) : ℕ := 2 * tauMax (Pbig a) ^ 3 * (Nat.log 3 (Pbig a) + 1) + 4

set_option exponentiation.threshold 400 in
/-- The two quantities controlled by `Ξ(a)` lie in `[1, P(a)]`. -/
lemma pbig_bounds {a M H : ℕ} (ha : 1 ≤ a) (hH : H ≤ 29 * a) (hM : M ≤ 10 ^ 15 * a ^ 7) :
    116 * (4 * M ^ 2) ^ 4 * H ^ 2 ≤ Pbig a ∧
      (11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2 ≤ Pbig a := by
  have hK : 4 * M ^ 2 ≤ 4 * 10 ^ 30 * a ^ 14 := by
    calc 4 * M ^ 2 ≤ 4 * (10 ^ 15 * a ^ 7) ^ 2 := by gcongr
      _ = 4 * 10 ^ 30 * a ^ 14 := by ring
  have ha1 : 1 ≤ a ^ 14 := Nat.one_le_pow _ _ ha
  have hP : Pbig a = 10 ^ 300 * a ^ 100 := rfl
  have hmono : ∀ k, k ≤ 100 → a ^ k ≤ a ^ 100 := fun k hk => Nat.pow_le_pow_right ha hk
  constructor
  · calc 116 * (4 * M ^ 2) ^ 4 * H ^ 2 ≤ 116 * (4 * 10 ^ 30 * a ^ 14) ^ 4 * (29 * a) ^ 2 := by
          gcongr
      _ = (116 * 4 ^ 4 * 10 ^ 120 * 29 ^ 2) * a ^ 58 := by ring
      _ ≤ 10 ^ 300 * a ^ 100 := Nat.mul_le_mul (by norm_num) (hmono 58 (by norm_num))
      _ = Pbig a := hP.symm
  · have h3 : 3 * (4 * M ^ 2) + 2 ≤ 5 * (4 * 10 ^ 30 * a ^ 14) := by
      have : 1 ≤ 4 * 10 ^ 30 * a ^ 14 := by nlinarith
      omega
    calc (11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2
        ≤ (11 * (4 * 10 ^ 30 * a ^ 14) ^ 2 * (29 * a) * (5 * (4 * 10 ^ 30 * a ^ 14))) ^ 2 := by
          gcongr
      _ = (11 * 16 * 10 ^ 60 * 29 * 20 * 10 ^ 30) ^ 2 * a ^ 86 := by ring
      _ ≤ 10 ^ 300 * a ^ 100 := Nat.mul_le_mul (by norm_num) (hmono 86 (by norm_num))
      _ = Pbig a := hP.symm

section Window

variable {a b : ℕ}

theorem two_state_window_eleven (hba : b < a) {s T A : ℕ} (hA : 1 ≤ A)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T)
    (hc : 237568 * A ^ 4 * (28 * a / (A * T) + 1) ^ 5 ≤ a ^ 3) :
    T ≤ 24 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
      (28 * a / (A * T) + 1) * Xi a := by
  set H : ℕ := 28 * a / (A * T) + 1 with hH
  set M : ℕ := 172032 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  set G := (Ico s (s + T)).filter fun i => i + 9 ≤ s + T ∧
    ∀ m ∈ range 7, kq a b (i + m) ≤ (H : ℤ)
  have hgood := good_card hba hA hmem hsT hT
  have ha : 0 < a := by omega
  have ha3 : 0 < a ^ 3 := by positivity
  have hcZ : (237568 : ℤ) * (A : ℤ) ^ 4 * (H : ℤ) ^ 5 ≤ (a : ℤ) ^ 3 := by exact_mod_cast hc
  have hAZ : (1 : ℤ) ≤ A := by exact_mod_cast hA
  -- facts at a good start
  have facts : ∀ i ∈ G, i + 8 < P a b ∧ (∀ m, m < 7 → 1 ≤ kq a b (i + m) ∧ kq a b (i + m) ≤ H) ∧
      orb a b i < 2 * A ∧ orb a b (i + 1) < 2 * A ∧ orb a b (i + 2) < 2 * A := by
    intro i hi
    obtain ⟨hiI, h9, hk⟩ := mem_filter.mp hi
    have := mem_Ico.mp hiI
    refine ⟨by omega, fun m hm => ⟨kq_pos (by omega), hk m (mem_range.mpr hm)⟩, ?_, ?_, ?_⟩
    · have := (hmem (i - s) (by omega)).2; rwa [show s + (i - s) = i by omega] at this
    · have := (hmem (i + 1 - s) (by omega)).2; rwa [show s + (i + 1 - s) = i + 1 by omega] at this
    · have := (hmem (i + 2 - s) (by omega)).2; rwa [show s + (i + 2 - s) = i + 2 by omega] at this
  have hH1 : 1 ≤ H := by rw [hH]; exact Nat.le_add_left 1 _
  have hcount := pattern_count_eleven (G := G) (θ := theta a b) (κ := kap a b)
    (Q := fun i => (qq a b i : ℤ)) (a := (a : ℤ)) (M := M) (H := H)
    (W := 2 * tauMax (Pbig a) ^ 3 * (Nat.log 3 (Pbig a) + 1)) hH1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have hg2 : T ≤ 2 * G.card := hgood
    have hXi : 2 * tauMax (Pbig a) ^ 3 * (Nat.log 3 (Pbig a) + 1) + 4 = Xi a := rfl
    rw [hXi] at hcount
    calc T ≤ 2 * G.card := hg2
      _ ≤ 2 * (4 * (2 * M + 1) ^ 7 * ((2 * H + 1) * Xi a)) := Nat.mul_le_mul_left _ hcount
      _ ≤ 2 * (4 * (2 * M + 1) ^ 7 * ((3 * H) * Xi a)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
      _ = 24 * (2 * M + 1) ^ 7 * H * Xi a := by ring
  -- injectivity of the quotient
  · intro i hi i' hi' h
    have hP := (facts i hi).1
    have hP' := (facts i' hi').1
    simp only [Nat.cast_inj] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h.symm
  -- the pattern bound
  · intro i hi t
    obtain ⟨hP, hk, hb0, hb1, hb2⟩ := facts i hi
    have K := fun m (hm : m < 7) => hk m hm
    have L0 := label_at (A := A) hba (i := i) (by omega) hb0
    have L1 := label_at (A := A) hba (i := i + 1) (by omega) hb1
    have L2 := label_at (A := A) hba (i := i + 2) (by omega) hb2
    have P0 := Lz_pos hba (i := i) (by omega)
    have P1 := Lz_pos hba (i := i + 1) (by omega)
    have P2 := Lz_pos hba (i := i + 2) (by omega)
    have SB0 := state_bound (K 0 (by norm_num)).1 (K 1 (by norm_num)).1 (K 2 (by norm_num)).1
      (K 3 (by norm_num)).1 (K 4 (by norm_num)).1 (K 5 (by norm_num)).1 (K 0 (by norm_num)).2
      (K 1 (by norm_num)).2 (K 2 (by norm_num)).2 (K 3 (by norm_num)).2 (K 4 (by norm_num)).2
      (K 5 (by norm_num)).2 hAZ P0 P1 L0 L1 hcZ (e0_at i) (e3_at i)
    have SB1 := state_bound (K 1 (by norm_num)).1 (K 2 (by norm_num)).1 (K 3 (by norm_num)).1
      (K 4 (by norm_num)).1 (K 5 (by norm_num)).1 (K 6 (by norm_num)).1 (K 1 (by norm_num)).2
      (K 2 (by norm_num)).2 (K 3 (by norm_num)).2 (K 4 (by norm_num)).2 (K 5 (by norm_num)).2
      (K 6 (by norm_num)).2 hAZ P1 P2 L1 L2 hcZ (e0_at (i + 1)) (e3_at (i + 1))
    have cv : ∀ z : ℤ, |z| * (a : ℤ) ^ 3 ≤ 172032 * (A : ℤ) ^ 4 * (H : ℤ) ^ 6 → |z| ≤ M := by
      intro z hz
      refine abs_le_div ha3 ?_
      exact_mod_cast hz
    have cvL : ∀ z : ℤ, 1 ≤ z → z * (a : ℤ) ^ 3 ≤ 172032 * (A : ℤ) ^ 4 * (H : ℤ) ^ 6 →
        |z| ≤ M := fun z hz h => cv z (by rwa [abs_of_pos (by omega)])
    fin_cases t
    · exact cvL _ P0 SB0.2.2.1
    · exact cvL _ P1 SB0.2.2.2
    · exact cvL _ P2 SB1.2.2.2
    · exact cv _ SB0.1
    · exact cv _ SB0.2.1
    · exact cv _ SB1.1
    · exact cv _ SB1.2.1
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
    have hA_a : A ≤ a := by
      have := (hmem 0 (by omega)).1
      have := (orb_le a b (s + 0)).trans hba.le
      omega
    have hMb : M ≤ 10 ^ 15 * a ^ 7 := by
      have h1 : M * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
      have hH29 : H ≤ 29 * a := by
        have : 28 * a / (A * T) ≤ 28 * a := Nat.div_le_self _ _
        omega
      have h2 : 172032 * A ^ 4 * H ^ 6 ≤ 172032 * a ^ 4 * (29 * a) ^ 6 := by gcongr
      have h3 : M * a ^ 3 ≤ (10 ^ 15 * a ^ 7) * a ^ 3 := by
        calc M * a ^ 3 ≤ 172032 * a ^ 4 * (29 * a) ^ 6 := h1.trans h2
          _ = 102328645558272 * a ^ 7 * a ^ 3 := by ring
          _ ≤ (10 ^ 15 * a ^ 7) * a ^ 3 := by gcongr; norm_num
      exact Nat.le_of_mul_le_mul_right h3 (by positivity)
    have hH29 : H ≤ 29 * a := by
      have : 28 * a / (A * T) ≤ 28 * a := Nat.div_le_self _ _
      omega
    obtain ⟨P1, P2⟩ := pbig_bounds (by omega) hH29 hMb
    have hτ : M'.natAbs.divisors.card ≤ tauMax (Pbig a) := by
      unfold tauMax
      refine le_sup (f := fun n => n.divisors.card) (mem_range.mpr ?_)
      have : M'.natAbs ≤ 116 * (4 * M ^ 2) ^ 4 * H ^ 2 := by
        have h' : (M'.natAbs : ℤ) ≤ ((116 * (4 * M ^ 2) ^ 4 * H ^ 2 : ℕ) : ℤ) := by
          rw [Int.natCast_natAbs]; push_cast at hb ⊢; linarith
        exact_mod_cast h'
      omega
    have hlog : Nat.log 3 ((11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2) ≤
        Nat.log 3 (Pbig a) := Nat.log_mono_right P2
    gcongr


end Window

section Exponent

/-- The constant in `window_74`. -/
def C74 : ℕ := 122449 ^ 19 + (8 * 237568 * 56 ^ 5) ^ 11 + 10752 ^ 19 +
  8 ^ 15 * (24 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 43

private lemma pow_cancel' {x y z : ℕ} (hz : 0 < z) (h : x * z ≤ y * z) : x ≤ y :=
  Nat.le_of_mul_le_mul_right h hz

/-- **The exponent arithmetic.** Every window run satisfies `T⁷⁴ ≤ C₇₄ Δ¹⁹ Ξ¹⁹ a²²`. -/
theorem window_74 {a A T Δ X : ℕ} (ha : 1 ≤ a) (hA : 1 ≤ A) (hΔ : 1 ≤ Δ) (hX : 1 ≤ X)
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hwin : 237568 * A ^ 4 * (28 * a / (A * T) + 1) ^ 5 ≤ a ^ 3 →
      T ≤ 24 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
        (28 * a / (A * T) + 1) * X) :
    T ^ 74 ≤ C74 * Δ ^ 19 * X ^ 19 * a ^ 22 := by
  set H := 28 * a / (A * T) + 1 with hH
  set M := 172032 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  have ha0 : 0 < a := by omega
  have hT2 : T ^ 2 ≤ 8 * A * Δ := by
    have : T ^ 2 ≤ 2 * (T * (T - 1)) := by
      have : T ≤ 2 * (T - 1) := by omega
      calc T ^ 2 = T * T := sq T
        _ ≤ T * (2 * (T - 1)) := Nat.mul_le_mul_left _ this
        _ = 2 * (T * (T - 1)) := by ring
    calc T ^ 2 ≤ 2 * (T * (T - 1)) := this
      _ ≤ 2 * (4 * A * Δ) := Nat.mul_le_mul_left _ hdrop
      _ = 8 * A * Δ := by ring
  have hT74 : T ^ 74 ≤ T ^ 76 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hT77 : T ^ 74 ≤ T ^ 77 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hmono : ∀ c : ℕ, c ≤ C74 → ∀ e f g : ℕ, e ≤ 19 → f ≤ 19 → g ≤ 22 →
      c * Δ ^ e * X ^ f * a ^ g ≤ C74 * Δ ^ 19 * X ^ 19 * a ^ 22 := by
    intro c hc e f g he hf hg
    have e1 : Δ ^ e ≤ Δ ^ 19 := Nat.pow_le_pow_right hΔ he
    have e2 : X ^ f ≤ X ^ 19 := Nat.pow_le_pow_right hX hf
    have e3 : a ^ g ≤ a ^ 22 := Nat.pow_le_pow_right ha hg
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc e1) e2) e3
  by_cases hbig : 28 * a < A * T
  · have h1 : (28 * a) ^ 2 * T ^ 4 ≤ 96000000 * a ^ 3 := by
      calc (28 * a) ^ 2 * T ^ 4 ≤ (A * T) ^ 2 * T ^ 4 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbig.le 2)
        _ = T ^ 6 * A ^ 2 := by ring
        _ ≤ _ := hsix
    have h2 : T ^ 4 ≤ 122449 * a := by
      have : (784 * T ^ 4) * a ^ 2 ≤ (784 * (122449 * a)) * a ^ 2 := by
        calc (784 * T ^ 4) * a ^ 2 = (28 * a) ^ 2 * T ^ 4 := by ring
          _ ≤ 96000000 * a ^ 3 := h1
          _ ≤ (784 * (122449 * a)) * a ^ 2 := by ring_nf; omega
      have := pow_cancel' (by positivity) this
      omega
    calc T ^ 74 ≤ T ^ 76 := hT74
      _ = (T ^ 4) ^ 19 := by ring
      _ ≤ (122449 * a) ^ 19 := Nat.pow_le_pow_left h2 19
      _ = 122449 ^ 19 * Δ ^ 0 * X ^ 0 * a ^ 19 := by ring
      _ ≤ _ := hmono _ (by unfold C74; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)
  push Not at hbig
  have hHAT : H * (A * T) ≤ 56 * a := by
    have := Nat.div_mul_le_self (28 * a) (A * T)
    calc H * (A * T) = 28 * a / (A * T) * (A * T) + A * T := by rw [hH]; ring
      _ ≤ 56 * a := by omega
  by_cases hcond : 237568 * A ^ 4 * H ^ 5 ≤ a ^ 3
  · have hw := hwin hcond
    rcases Nat.eq_zero_or_pos M with hM0 | hM1
    · rw [hM0] at hw
      simp only [mul_zero, zero_add, one_pow, mul_one] at hw
      have h1 : T ^ 2 * A ≤ 1344 * X * a := by
        have : (T ^ 2 * A) * 1 ≤ (1344 * X * a) * 1 := by
          calc (T ^ 2 * A) * 1 = T * (A * T) := by ring
            _ ≤ 24 * H * X * (A * T) := Nat.mul_le_mul_right _ hw
            _ = 24 * X * (H * (A * T)) := by ring
            _ ≤ 24 * X * (56 * a) := Nat.mul_le_mul_left _ hHAT
            _ = (1344 * X * a) * 1 := by ring
        omega
      have h2 : T ^ 4 ≤ 10752 * Δ * X * a := by
        calc T ^ 4 = T ^ 2 * T ^ 2 := by ring
          _ ≤ (8 * A * Δ) * T ^ 2 := Nat.mul_le_mul_right _ hT2
          _ = 8 * Δ * (T ^ 2 * A) := by ring
          _ ≤ 8 * Δ * (1344 * X * a) := Nat.mul_le_mul_left _ h1
          _ = 10752 * Δ * X * a := by ring
      calc T ^ 74 ≤ T ^ 76 := hT74
        _ = (T ^ 4) ^ 19 := by ring
        _ ≤ (10752 * Δ * X * a) ^ 19 := Nat.pow_le_pow_left h2 19
        _ = 10752 ^ 19 * Δ ^ 19 * X ^ 19 * a ^ 19 := by ring
        _ ≤ _ := hmono _ (by unfold C74; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)
    · have hMa : M * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
      have h3M : 2 * M + 1 ≤ 3 * M := by omega
      have hw' : T ≤ 24 * 3 ^ 7 * M ^ 7 * H * X := by
        calc T ≤ 24 * (2 * M + 1) ^ 7 * H * X := hw
          _ ≤ 24 * (3 * M) ^ 7 * H * X := by gcongr
          _ = 24 * 3 ^ 7 * M ^ 7 * H * X := by ring
      have h1 : T * a ^ 21 ≤ 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 43 * X := by
        calc T * a ^ 21 ≤ 24 * 3 ^ 7 * M ^ 7 * H * X * a ^ 21 := Nat.mul_le_mul_right _ hw'
          _ = 24 * 3 ^ 7 * H * X * (M * a ^ 3) ^ 7 := by ring
          _ ≤ 24 * 3 ^ 7 * H * X * (172032 * A ^ 4 * H ^ 6) ^ 7 := by gcongr
          _ = 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 43 * X := by ring
      have h2 : (T ^ 44 * A ^ 15) * (A ^ 28 * a ^ 21) ≤
          (24 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 43 * X * a ^ 22) * (A ^ 28 * a ^ 21) := by
        calc (T ^ 44 * A ^ 15) * (A ^ 28 * a ^ 21) = T * a ^ 21 * (A * T) ^ 43 := by ring
          _ ≤ 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 43 * X * (A * T) ^ 43 :=
              Nat.mul_le_mul_right _ h1
          _ = 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * X * (H * (A * T)) ^ 43 := by ring
          _ ≤ 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * X * (56 * a) ^ 43 := by gcongr
          _ = (24 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 43 * X * a ^ 22) * (A ^ 28 * a ^ 21) := by ring
      have h3 := pow_cancel' (by positivity) h2
      calc T ^ 74 = T ^ 44 * (T ^ 2) ^ 15 := by ring
        _ ≤ T ^ 44 * (8 * A * Δ) ^ 15 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT2 15)
        _ = 8 ^ 15 * Δ ^ 15 * (T ^ 44 * A ^ 15) := by ring
        _ ≤ 8 ^ 15 * Δ ^ 15 * (24 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 43 * X * a ^ 22) :=
            Nat.mul_le_mul_left _ h3
        _ = 8 ^ 15 * (24 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 43 * Δ ^ 15 * X ^ 1 * a ^ 22 := by ring
        _ ≤ _ := hmono _ (by unfold C74; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)
  · push Not at hcond
    have h1 : (A * T ^ 5) * (A ^ 4 * a ^ 3) ≤ (237568 * 56 ^ 5 * a ^ 2) * (A ^ 4 * a ^ 3) := by
      calc (A * T ^ 5) * (A ^ 4 * a ^ 3) = a ^ 3 * (A * T) ^ 5 := by ring
        _ ≤ 237568 * A ^ 4 * H ^ 5 * (A * T) ^ 5 := Nat.mul_le_mul_right _ hcond.le
        _ = 237568 * A ^ 4 * (H * (A * T)) ^ 5 := by ring
        _ ≤ 237568 * A ^ 4 * (56 * a) ^ 5 := by gcongr
        _ = (237568 * 56 ^ 5 * a ^ 2) * (A ^ 4 * a ^ 3) := by ring
    have h2 := pow_cancel' (by positivity) h1
    have h3 : T ^ 7 ≤ 8 * 237568 * 56 ^ 5 * Δ * a ^ 2 := by
      calc T ^ 7 = T ^ 5 * T ^ 2 := by ring
        _ ≤ T ^ 5 * (8 * A * Δ) := Nat.mul_le_mul_left _ hT2
        _ = 8 * Δ * (A * T ^ 5) := by ring
        _ ≤ 8 * Δ * (237568 * 56 ^ 5 * a ^ 2) := Nat.mul_le_mul_left _ h2
        _ = 8 * 237568 * 56 ^ 5 * Δ * a ^ 2 := by ring
    calc T ^ 74 ≤ T ^ 77 := hT77
      _ = (T ^ 7) ^ 11 := by ring
      _ ≤ (8 * 237568 * 56 ^ 5 * Δ * a ^ 2) ^ 11 := Nat.pow_le_pow_left h3 11
      _ = (8 * 237568 * 56 ^ 5) ^ 11 * Δ ^ 11 * X ^ 0 * a ^ 22 := by ring
      _ ≤ _ := hmono _ (by unfold C74; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)

end Exponent

section Global

/-- `max_{n ≤ X} τ(n)^k ≤ D X` from the divisor bound. -/
lemma tauMax_pow_le {k D : ℕ} (hk : k ≠ 0) (hdiv : ∀ n : ℕ, n ≠ 0 → n.divisors.card ^ k ≤ D * n)
    (X : ℕ) : tauMax X ^ k ≤ D * X := by
  obtain ⟨n0, hn0, he⟩ := exists_mem_eq_sup (range (X + 1)) nonempty_range_add_one
    fun n => n.divisors.card
  unfold tauMax
  rw [he]
  have hn0' : n0 ≤ X := by have := mem_range.mp hn0; omega
  by_cases h0 : n0 = 0
  · subst h0; simp [zero_pow hk]
  · exact (hdiv n0 h0).trans (Nat.mul_le_mul_left _ hn0')

/-- A root bound: `x^k ≤ D c a^e` gives `x ≤ (D c)^{1/k} a^η` once `e/k ≤ η`. -/
lemma root_le {x D c e k a : ℕ} (hk : k ≠ 0) (ha : 1 ≤ a) (h : x ^ k ≤ D * (c * a ^ e))
    {η : ℝ} (hη : (e : ℝ) / k ≤ η) :
    (x : ℝ) ≤ ((D * c : ℕ) : ℝ) ^ ((k : ℝ)⁻¹) * (a : ℝ) ^ η := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have h1 := le_rpow_inv_of_pow_le hk h
  have e1 : ((D * (c * a ^ e) : ℕ) : ℝ) ^ ((k : ℝ)⁻¹) =
      ((D * c : ℕ) : ℝ) ^ ((k : ℝ)⁻¹) * (a : ℝ) ^ ((e : ℝ) / k) := by
    rw [show D * (c * a ^ e) = D * c * a ^ e by ring, Nat.cast_mul,
      Real.mul_rpow (by positivity) (by positivity), Nat.cast_pow,
      ← Real.rpow_natCast (a : ℝ) e, ← Real.rpow_mul (by positivity), div_eq_mul_inv]
  rw [e1] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ha' hη)
    (by positivity))

/-- **The slack factor of the polynomial range `10ᶜ aᵉ` is `O_η(a^η)`.** -/
lemma xi_le (c e : ℕ) (he : 1 ≤ e) (η : ℝ) (hη : 0 < η) : ∃ C > 0, ∀ a : ℕ, 1 ≤ a →
    ((2 * tauMax (10 ^ c * a ^ e) ^ 3 * (Nat.log 3 (10 ^ c * a ^ e) + 1) + 4 : ℕ) : ℝ) ≤
      C * (a : ℝ) ^ η := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  obtain ⟨k, hk⟩ := exists_nat_gt (6 * e / η)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  have hk1 : k ≠ 0 := by rintro rfl; simp at hk0
  have hkη : (e : ℝ) / k ≤ η / 6 := by
    rw [div_le_iff₀ hk0]; rw [div_lt_iff₀ hη] at hk; linarith
  obtain ⟨Dc, hDc, hdiv⟩ := OAI.Ostmann.exists_divisors_power_bound k
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (η / (2 * e)) (by positivity)
  set C2 : ℝ := ((Dc * 10 ^ c : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)
  set C3 : ℝ := CL * ((10 : ℝ) ^ c) ^ (η / (2 * e))
  refine ⟨2 * C2 ^ 3 * C3 + 4, by positivity, fun a ha => ?_⟩
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have haη : (1 : ℝ) ≤ (a : ℝ) ^ η := Real.one_le_rpow ha' hη.le
  have hC2 : 0 ≤ C2 := by positivity
  have hC3 : 0 ≤ C3 := by positivity
  -- the divisor maximum, cubed
  have b2 : (tauMax (10 ^ c * a ^ e) : ℝ) ≤ C2 * (a : ℝ) ^ (η / 6) :=
    root_le hk1 ha (tauMax_pow_le hk1 hdiv _) hkη
  have b2' : (tauMax (10 ^ c * a ^ e) : ℝ) ^ 3 ≤ C2 ^ 3 * (a : ℝ) ^ (η / 2) := by
    calc (tauMax (10 ^ c * a ^ e) : ℝ) ^ 3 ≤ (C2 * (a : ℝ) ^ (η / 6)) ^ 3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) b2 3
      _ = C2 ^ 3 * (a : ℝ) ^ (η / 2) := by
          rw [mul_pow, ← Real.rpow_natCast ((a : ℝ) ^ (η / 6)) 3, ← Real.rpow_mul (by positivity)]
          congr 2; push_cast; ring
  -- the logarithm
  have b3 : ((Nat.log 3 (10 ^ c * a ^ e) + 1 : ℕ) : ℝ) ≤ C3 * (a : ℝ) ^ (η / 2) := by
    have hP1 : 1 ≤ 10 ^ c * a ^ e := Nat.mul_pos (by positivity) (pow_pos ha e)
    have h1 : Nat.log 3 (10 ^ c * a ^ e) + 1 ≤ Nat.log 2 (10 ^ c * a ^ e) + 1 :=
      Nat.succ_le_succ (Nat.log_anti_left (by norm_num) (by norm_num))
    have h2 := hlog _ hP1
    have e1 : ((10 ^ c * a ^ e : ℕ) : ℝ) ^ (η / (2 * e)) =
        ((10 : ℝ) ^ c) ^ (η / (2 * e)) * (a : ℝ) ^ (η / 2) := by
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (a : ℝ) e,
        ← Real.rpow_mul (by positivity)]
      congr 2; field_simp
    calc ((Nat.log 3 (10 ^ c * a ^ e) + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 (10 ^ c * a ^ e) + 1 : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ CL * ((10 ^ c * a ^ e : ℕ) : ℝ) ^ (η / (2 * e)) := h2
      _ = C3 * (a : ℝ) ^ (η / 2) := by rw [e1]; simp only [C3]; ring
  push_cast
  have := mul_le_mul b2' (by exact_mod_cast b3) (by positivity) (by positivity)
  have e2 : C2 ^ 3 * (a : ℝ) ^ (η / 2) * (C3 * (a : ℝ) ^ (η / 2)) = C2 ^ 3 * C3 * (a : ℝ) ^ η := by
    rw [show C2 ^ 3 * (a : ℝ) ^ (η / 2) * (C3 * (a : ℝ) ^ (η / 2)) =
      C2 ^ 3 * C3 * ((a : ℝ) ^ (η / 2) * (a : ℝ) ^ (η / 2)) by ring, ← Real.rpow_add (by positivity)]
    ring_nf
  push_cast at this
  nlinarith

/-- **The slack factors are `O_η(a^η)`.** -/
lemma slack_le (η : ℝ) (hη : 0 < η) : ∃ C > 0, ∀ a : ℕ, 1 ≤ a →
    (tauMax (32 * a ^ 7) : ℝ) ≤ C * (a : ℝ) ^ η ∧ (Xi a : ℝ) ≤ C * (a : ℝ) ^ η := by
  obtain ⟨k, hk⟩ := exists_nat_gt (7 / η)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  have hk1 : k ≠ 0 := by rintro rfl; simp at hk0
  have hkη : (7 : ℝ) / k ≤ η := by
    rw [div_le_iff₀ hk0]; rw [div_lt_iff₀ hη] at hk; linarith
  obtain ⟨Dc, hDc, hdiv⟩ := OAI.Ostmann.exists_divisors_power_bound k
  obtain ⟨CX, hCX, hX⟩ := xi_le 300 100 (by norm_num) η hη
  set C1 : ℝ := ((Dc * 32 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)
  have hC1 : 0 ≤ C1 := by positivity
  refine ⟨C1 + CX, by positivity, fun a ha => ⟨?_, ?_⟩⟩
  · have b1 : (tauMax (32 * a ^ 7) : ℝ) ≤ C1 * (a : ℝ) ^ η :=
      root_le hk1 ha (tauMax_pow_le hk1 hdiv _) (by exact_mod_cast hkη)
    nlinarith [mul_nonneg hCX.le (by positivity : (0 : ℝ) ≤ (a : ℝ) ^ η)]
  · have : (Xi a : ℝ) ≤ CX * (a : ℝ) ^ η := hX a ha
    nlinarith [mul_nonneg hC1 (by positivity : (0 : ℝ) ≤ (a : ℝ) ^ η)]

/-- Every dyadic window satisfies `T ≤ 35` or `T⁷⁴ ≤ C₇₄ Δ¹⁹ Ξ(a)¹⁹ a²²`. -/
theorem visits_74 {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) (hΔ1 : 1 ≤ Δ) :
    (visits a b k).card ≤ 35 ∨ (visits a b k).card ^ 74 ≤ C74 * Δ ^ 19 * Xi a ^ 19 * a ^ 22 := by
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
  exact window_74 (by omega) Nat.one_le_two_pow hΔ1 (by unfold Xi; omega) (by omega)
    (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (fun hc => two_state_window_eleven hba Nat.one_le_two_pow hmem hsT (by omega) hc)

/-- **Theorem.** `P(a, b) ≪_ε a^{11/37 + ε}` uniformly in `0 < b < a`. -/
theorem P_le_11_37 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((11 : ℝ) / 37 + ε) := by
  intro ε hε
  obtain ⟨Cs, hCs, hslack⟩ := slack_le (ε / 4) (by positivity)
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (ε / 2) (by positivity)
  set K : ℝ := (C74 : ℝ) * Cs ^ 38
  set C2 : ℝ := K ^ ((74 : ℝ)⁻¹)
  have hK : 0 < K := by have : (0 : ℝ) < C74 := by unfold C74; positivity
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
  obtain ⟨hsΔ, hsX⟩ := hslack a ha1
  set β : ℝ := 11 / 37 + ε / 2
  have hβ : 1 ≤ (a : ℝ) ^ β := Real.one_le_rpow ha (by positivity)
  have hwin : ∀ k, ((visits a b k).card : ℝ) ≤ (35 + C2) * (a : ℝ) ^ β := by
    intro k
    rcases visits_74 (k := k) hba hΔ hΔ1 with h | h
    · have : ((visits a b k).card : ℝ) ≤ 35 := by exact_mod_cast h
      nlinarith
    · set T := (visits a b k).card
      have hTr : (T : ℝ) ^ 74 ≤ K * (a : ℝ) ^ (22 + 38 * (ε / 4)) := by
        have h' : (T : ℝ) ^ 74 ≤ (C74 : ℝ) * (Δ : ℝ) ^ 19 * (Xi a : ℝ) ^ 19 * (a : ℝ) ^ 22 := by
          exact_mod_cast h
        have p1 : (Δ : ℝ) ^ 19 ≤ (Cs * (a : ℝ) ^ (ε / 4)) ^ 19 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsΔ 19
        have p2 : (Xi a : ℝ) ^ 19 ≤ (Cs * (a : ℝ) ^ (ε / 4)) ^ 19 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsX 19
        have e : (C74 : ℝ) * (Cs * (a : ℝ) ^ (ε / 4)) ^ 19 * (Cs * (a : ℝ) ^ (ε / 4)) ^ 19 *
            (a : ℝ) ^ 22 = K * (a : ℝ) ^ (22 + 38 * (ε / 4)) := by
          have q1 : ((a : ℝ) ^ (ε / 4)) ^ 38 = (a : ℝ) ^ (38 * (ε / 4)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num; ring_nf
          have q2 : (a : ℝ) ^ (22 : ℕ) = (a : ℝ) ^ (22 : ℝ) := by
            rw [← Real.rpow_natCast]; norm_num
          calc (C74 : ℝ) * (Cs * (a : ℝ) ^ (ε / 4)) ^ 19 * (Cs * (a : ℝ) ^ (ε / 4)) ^ 19 *
                (a : ℝ) ^ 22 = (C74 : ℝ) * Cs ^ 38 * ((a : ℝ) ^ (ε / 4)) ^ 38 * (a : ℝ) ^ (22 : ℕ) := by
                ring
            _ = K * (a : ℝ) ^ (22 + 38 * (ε / 4)) := by
                rw [q1, q2, Real.rpow_add (by positivity)]; simp only [K]; ring
        calc (T : ℝ) ^ 74 ≤ (C74 : ℝ) * (Δ : ℝ) ^ 19 * (Xi a : ℝ) ^ 19 * (a : ℝ) ^ 22 := h'
          _ ≤ (C74 : ℝ) * (Cs * (a : ℝ) ^ (ε / 4)) ^ 19 * (Cs * (a : ℝ) ^ (ε / 4)) ^ 19 *
              (a : ℝ) ^ 22 := by gcongr
          _ = _ := e
      have hroot : (T : ℝ) ≤ C2 * (a : ℝ) ^ ((22 + 38 * (ε / 4)) / 74) := by
        have h1 : ((T : ℝ) ^ 74) ^ ((74 : ℝ)⁻¹) ≤ (K * (a : ℝ) ^ (22 + 38 * (ε / 4))) ^ ((74 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hTr (by positivity)
        rw [show (74 : ℝ) = ((74 : ℕ) : ℝ) by norm_num, Real.pow_rpow_inv_natCast (Nat.cast_nonneg _)
          (by norm_num), Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul (by positivity)] at h1
        simp only [C2]
        convert h1 using 2
        all_goals norm_num
        all_goals (congr 1; ring)
      have hexp : (22 + 38 * (ε / 4)) / 74 ≤ β := by simp only [β]; nlinarith
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
    _ = CL * (35 + C2) * (a : ℝ) ^ ((11 : ℝ) / 37 + ε) := by
        rw [← Real.rpow_add (by positivity)]
        congr 2
        simp only [β]; ring

end Global

end PierceBound
