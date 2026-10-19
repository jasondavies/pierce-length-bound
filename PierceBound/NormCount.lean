/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib

/-!
# A uniform count for norm equations

For integers `D ≥ 1`, `N ≠ 0` and `B ≥ 0`, the number of `(U, V) ∈ [-B, B]²` with
`U² - D V² = N` is at most `2 τ(|N|)³ (log₃ L² + 1)` with `L = B (⌊√D⌋ + 2)` (`norm_count`).
The bound is uniform in the coefficients.

* If `D = m²`, then `(U - mV)(U + mV) = N`, and `U - mV` is a signed divisor of `N`.
* Otherwise write `D = d f²` with `d > 1` squarefree, put `g = gcd(U, fV)`, `u = U/g`,
  `w = fV/g`, `n = N/g²`. Then `u² - d w² = n`, `gcd(w, n) = 1`, and `t ≡ u w⁻¹ (mod n)` is a
  square root of `d` modulo `n`. There are at most `τ(n)²` such roots (`card_sqRoots_le`): at most
  four modulo a prime power, multiplicatively by the Chinese remainder theorem.
* Two solutions with the same `(g, t)` and the same sign of `ξ = u + w√d` have quotient
  `ξ/ξ' = r + s√d` with `r² - d s² = 1`. If `ξ/ξ' > 1` then `ξ/ξ' ≥ 3` (`unit_ge_three`). Since
  `1/L ≤ |ξ| ≤ L`, the map `ξ ↦ log₃ ⌊L|ξ|⌋` is injective on such a class.
-/

@[expose] public section

namespace PierceBound

open Finset

/-! ### Square roots modulo `m` -/

/-- The square roots of `d` modulo `m`, as residues in `[0, m)`. -/
def sqRoots (d : ℤ) (m : ℕ) : Finset ℕ := (range m).filter fun t => (m : ℤ) ∣ (t : ℤ) ^ 2 - d

lemma eq_emod_of_dvd {M s c : ℤ} (h0 : 0 ≤ s) (hs : s < M) (h : M ∣ s - c) : s = c % M := by
  have h1 : c ≡ s [ZMOD M] := Int.modEq_iff_dvd.mpr h
  unfold Int.ModEq at h1
  rw [Int.emod_eq_of_lt h0 hs] at h1
  exact h1.symm

/-- If `h ∣ s - c` and `0 ≤ s < 2h`, then `s ≡ c` or `s ≡ c + h (mod 2h)`. -/
lemma eq_emod_of_dvd_half {h s c : ℤ} (h0 : 0 ≤ s) (hs : s < 2 * h)
    (hd : h ∣ s - c) : s = c % (2 * h) ∨ s = (c + h) % (2 * h) := by
  obtain ⟨j, hj⟩ := hd
  rcases Int.even_or_odd j with ⟨q, hq⟩ | ⟨q, hq⟩
  · left; exact eq_emod_of_dvd h0 hs ⟨q, by rw [hj, hq]; ring⟩
  · right; exact eq_emod_of_dvd h0 hs
      ⟨q, by rw [show s - (c + h) = s - c - h by ring, hj, hq]; ring⟩

lemma prime_pow_dvd_of_dvd_mul {p : ℤ} (hp : Prime p) {e : ℕ} {a b : ℤ} (h : p ^ e ∣ a * b)
    (ha : ¬ p ∣ a) : p ^ e ∣ b := by
  have hc : IsCoprime p a := (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr ha
  exact (hc.pow_left).dvd_of_dvd_mul_left h

/-- If `p^e ∣ x y` and `p` does not divide both, then `p^e` divides one factor. -/
lemma prime_pow_dvd_or {p : ℤ} (hp : Prime p) {e : ℕ} {x y : ℤ} (h : p ^ e ∣ x * y)
    (hn : ¬ (p ∣ x ∧ p ∣ y)) : p ^ e ∣ x ∨ p ^ e ∣ y := by
  by_cases hy : p ∣ y
  · right
    exact prime_pow_dvd_of_dvd_mul hp h (fun hx => hn ⟨hx, hy⟩)
  · left
    exact prime_pow_dvd_of_dvd_mul hp (by rwa [mul_comm] at h) hy

lemma dvd_of_sq_sub {p : ℤ} {s d : ℤ} (h1 : p ∣ s ^ 2 - d) (h2 : p ∣ s ^ 2) : p ∣ d := by
  have := dvd_sub h2 h1; rwa [sub_sub_cancel] at this

/-- **At most four square roots modulo a prime power** (for squarefree `d`). -/
theorem card_sqRoots_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {d : ℤ}
    (hd : Squarefree d) : (sqRoots d (p ^ e)).card ≤ 4 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  rcases (sqRoots d (p ^ e)).eq_empty_or_nonempty with h | ⟨r, hr⟩
  · rw [h]; simp
  have hr' := mem_filter.mp hr
  have hMZ : (((p ^ e : ℕ)) : ℤ) = (p : ℤ) ^ e := by push_cast; rfl
  rw [hMZ] at hr'
  set h0 : ℤ := (p : ℤ) ^ (e - 1)
  have hpe : (p : ℤ) ^ e = p * h0 := by
    simp only [h0]; rw [← pow_succ']; congr 1; omega
  -- every root `s` is one of four residues determined by `r`
  have key : ∀ s ∈ sqRoots d (p ^ e),
      (s : ℤ) ∈ ({(r : ℤ) % (p ^ e), (-(r : ℤ)) % (p ^ e), ((r : ℤ) + h0) % (p ^ e),
        (-(r : ℤ) + h0) % (p ^ e)} : Finset ℤ) := by
    intro s hs
    have hs' := mem_filter.mp hs
    rw [hMZ] at hs'
    have hs0 : (0 : ℤ) ≤ s := by positivity
    have hsM : (s : ℤ) < (p : ℤ) ^ e := by
      have := mem_range.mp hs'.1; rw [← hMZ]; exact_mod_cast this
    have hprod : (p : ℤ) ^ e ∣ ((s : ℤ) - r) * ((s : ℤ) + r) := by
      have := dvd_sub hs'.2 hr'.2
      rwa [show (s : ℤ) ^ 2 - d - ((r : ℤ) ^ 2 - d) = ((s : ℤ) - r) * ((s : ℤ) + r) by ring]
        at this
    have hdp : ∀ t : ℤ, (p : ℤ) ^ e ∣ t ^ 2 - d → (p : ℤ) ∣ t ^ 2 - d :=
      fun t ht => (dvd_pow_self (p : ℤ) (by omega : e ≠ 0)).trans ht
    simp only [mem_insert, mem_singleton]
    by_cases hpd : (p : ℤ) ∣ d
    · -- `p ∣ d`: then `e = 1` and both roots are `0 mod p`
      have hps : (p : ℤ) ∣ s := hpZ.dvd_of_dvd_pow (by
        have := dvd_add (hdp _ hs'.2) hpd; rwa [sub_add_cancel] at this)
      have hpr : (p : ℤ) ∣ r := hpZ.dvd_of_dvd_pow (by
        have := dvd_add (hdp _ hr'.2) hpd; rwa [sub_add_cancel] at this)
      rcases Nat.lt_or_ge e 2 with he2 | he2
      · left
        have he1 : e = 1 := by omega
        refine eq_emod_of_dvd hs0 hsM ?_
        rw [he1, pow_one]; exact dvd_sub hps hpr
      · exfalso
        have h1 : (p : ℤ) * p ∣ (s : ℤ) ^ 2 - d :=
          (show (p : ℤ) * p ∣ (p : ℤ) ^ e by rw [← sq]; exact pow_dvd_pow _ he2).trans hs'.2
        have h2 : (p : ℤ) * p ∣ (s : ℤ) ^ 2 := by rw [sq]; exact mul_dvd_mul hps hps
        exact hpZ.not_isUnit (hd _ (dvd_of_sq_sub h1 h2))
    -- `p ∤ d`: neither root is divisible by `p`
    have hnd : ∀ t : ℤ, (p : ℤ) ^ e ∣ t ^ 2 - d → ¬ (p : ℤ) ∣ t := fun t ht htp =>
      hpd (dvd_of_sq_sub (hdp t ht) (dvd_pow htp (by norm_num)))
    have hns := hnd _ hs'.2
    have hnr := hnd _ hr'.2
    by_cases hp2 : p = 2
    · subst hp2
      -- `2^{e-1}` divides `s - r` or `s + r`
      have hhalf : h0 ∣ (s : ℤ) - r ∨ h0 ∣ (s : ℤ) + r := by
        rcases Nat.lt_or_ge e 2 with he2 | he2
        · left; simp only [h0, show e - 1 = 0 by omega, pow_zero]; exact one_dvd _
        have hso : Odd (s : ℤ) := Int.not_even_iff_odd.mp fun h => hns (even_iff_two_dvd.mp h)
        have hro : Odd (r : ℤ) := Int.not_even_iff_odd.mp fun h => hnr (even_iff_two_dvd.mp h)
        obtain ⟨a1, ha1⟩ := hso
        obtain ⟨b1, hb1⟩ := hro
        have hdiv : (2 : ℤ) ^ (e - 2) ∣ (a1 - b1) * (a1 + b1 + 1) := by
          have h4 : 4 * (2 : ℤ) ^ (e - 2) ∣ 4 * ((a1 - b1) * (a1 + b1 + 1)) := by
            have : 4 * (2 : ℤ) ^ (e - 2) = 2 ^ e := by
              rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
            rw [this, show 4 * ((a1 - b1) * (a1 + b1 + 1)) = ((s : ℤ) - r) * ((s : ℤ) + r) by
              rw [ha1, hb1]; ring]
            exact_mod_cast hprod
          exact (mul_dvd_mul_iff_left (by norm_num)).mp h4
        have hn2 : ¬ ((2 : ℤ) ∣ (a1 - b1) ∧ (2 : ℤ) ∣ (a1 + b1 + 1)) := by
          rintro ⟨h1, h2⟩
          have := dvd_add h1 h2
          rw [show a1 - b1 + (a1 + b1 + 1) = 2 * a1 + 1 by ring] at this
          omega
        have hh2 : h0 = 2 * 2 ^ (e - 2) := by
          simp only [h0]; push_cast; rw [← pow_succ']; congr 1; omega
        rcases prime_pow_dvd_or Int.prime_two hdiv hn2 with h | h
        · left; rw [hh2, show (s : ℤ) - r = 2 * (a1 - b1) by rw [ha1, hb1]; ring]
          exact mul_dvd_mul_left 2 h
        · right; rw [hh2, show (s : ℤ) + r = 2 * (a1 + b1 + 1) by rw [ha1, hb1]; ring]
          exact mul_dvd_mul_left 2 h
      have hh0 : (0 : ℤ) < h0 := by positivity
      have hsM2 : (s : ℤ) < 2 * h0 := by
        have : ((2 : ℕ) : ℤ) ^ e = 2 * h0 := by push_cast at hpe ⊢; exact hpe
        rw [← this]; exact hsM
      have e2 : ((2 : ℕ) : ℤ) ^ e = 2 * h0 := by push_cast at hpe ⊢; exact hpe
      rw [e2]
      rcases hhalf with h | h
      · rcases eq_emod_of_dvd_half hs0 hsM2 h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inl h'))
      · rcases eq_emod_of_dvd_half hs0 hsM2 (c := -(r : ℤ)) (by rwa [sub_neg_eq_add]) with
          h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr h'))
    · -- odd `p ∤ d`: `p^e ∣ s - r` or `p^e ∣ s + r`
      have hn2 : ¬ ((p : ℤ) ∣ (s : ℤ) - r ∧ (p : ℤ) ∣ (s : ℤ) + r) := by
        rintro ⟨h1, h2⟩
        have h3 : (p : ℤ) ∣ 2 * (s : ℤ) := by
          have := dvd_add h1 h2; rwa [show (s : ℤ) - r + (s + r) = 2 * s by ring] at this
        rcases hpZ.dvd_or_dvd h3 with h4 | h4
        · have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h4
          have : p ≤ 2 := by exact_mod_cast this
          have := hp.two_le
          omega
        · exact hns h4
      rcases prime_pow_dvd_or hpZ hprod hn2 with h | h
      · exact Or.inl (eq_emod_of_dvd hs0 hsM h)
      · exact Or.inr (Or.inl (eq_emod_of_dvd hs0 hsM (by rwa [sub_neg_eq_add])))
  -- conclude
  have hsub : sqRoots d (p ^ e) ⊆ ({(r : ℤ) % (p ^ e), (-(r : ℤ)) % (p ^ e), ((r : ℤ) + h0) %
      (p ^ e),
      (-(r : ℤ) + h0) % (p ^ e)} : Finset ℤ).image Int.toNat := by
    intro s hs
    exact mem_image.mpr ⟨s, key s hs, by simp⟩
  calc (sqRoots d (p ^ e)).card ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ ≤ 4 := card_le_four

/-- **Multiplicativity** (one direction, by the Chinese remainder theorem). -/
lemma card_sqRoots_mul_le (d : ℤ) {a b : ℕ} (hab : a.Coprime b) :
    (sqRoots d (a * b)).card ≤ (sqRoots d a).card * (sqRoots d b).card := by
  rw [← card_product]
  refine card_le_card_of_injOn (fun t => (t % a, t % b)) (fun t ht => ?_) (fun t ht t' ht' h => ?_)
  · have ht' := mem_filter.mp (mem_coe.mp ht)
    have htab := mem_range.mp ht'.1
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at htab)
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at htab)
    have hred : ∀ c : ℕ, c ∣ a * b → 0 < c → (t % c) ∈ sqRoots d c := by
      intro c hc hc0
      refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hc0), ?_⟩
      have h1 : (c : ℤ) ∣ (t : ℤ) ^ 2 - d := (Int.natCast_dvd_natCast.mpr hc).trans (by
        exact_mod_cast ht'.2)
      have h2 : (c : ℤ) ∣ (t : ℤ) - ((t % c : ℕ) : ℤ) := by
        rw [Int.natCast_mod]; exact Int.dvd_self_sub_emod ..
      have : ((t % c : ℕ) : ℤ) ^ 2 - d = ((t : ℤ) ^ 2 - d) -
          ((t : ℤ) - ((t % c : ℕ) : ℤ)) * ((t : ℤ) + ((t % c : ℕ) : ℤ)) := by ring
      rw [this]
      exact dvd_sub h1 (dvd_mul_of_dvd_left h2 _)
    exact mem_product.mpr ⟨hred a (dvd_mul_right a b) ha, hred b (dvd_mul_left b a) hb⟩
  · have h1 := mem_range.mp (mem_filter.mp (mem_coe.mp ht)).1
    have h2 := mem_range.mp (mem_filter.mp (mem_coe.mp ht')).1
    simp only [Prod.mk.injEq] at h
    have hm : t ≡ t' [MOD a * b] := (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨h.1, h.2⟩
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hm

/-- **At most `τ(m)²` square roots of a squarefree `d` modulo `m`.** -/
theorem card_sqRoots_le {d : ℤ} (hd : Squarefree d) (m : ℕ) :
    (sqRoots d m).card ≤ m.divisors.card ^ 2 := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    have := card_sqRoots_prime_pow hp hn hd
    rw [Nat.divisors_prime_pow hp, card_map, card_range]
    nlinarith
  | zero => simp [sqRoots]
  | one =>
    simp only [Nat.divisors_one, card_singleton, one_pow]
    exact (card_le_card (filter_subset _ _)).trans (by simp)
  | coprime a b _ _ hab ha hb =>
    rw [Nat.Coprime.card_divisors_mul hab, mul_pow]
    exact (card_sqRoots_mul_le d hab).trans (Nat.mul_le_mul ha hb)

/-! ### Norm-one numbers -/

/-- A real number `ε = r + s δ > 1` with `r² - s² δ² = 1` and integers `r, s` is at least `3`. -/
lemma unit_ge_three {r s : ℤ} {δ : ℝ} (hn : (r : ℝ) ^ 2 - (s : ℝ) ^ 2 * δ ^ 2 = 1)
    (h : 1 < (r : ℝ) + s * δ) : 3 ≤ (r : ℝ) + s * δ := by
  set ε := (r : ℝ) + s * δ
  set ε' := (r : ℝ) - s * δ
  have hp : ε * ε' = 1 := by simp only [ε, ε']; linear_combination hn
  have hε' : 0 < ε' := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : 2 < ε + ε' := by nlinarith [sq_nonneg (ε - 1)]
  have hr : (2 : ℝ) ≤ r := by
    have : (1 : ℝ) < r := by simp only [ε, ε'] at h2; linarith
    have : (1 : ℤ) < r := by exact_mod_cast this
    exact_mod_cast (show (2 : ℤ) ≤ r by omega)
  by_contra hc
  push Not at hc
  have : ε + ε' = 2 * r := by simp only [ε, ε']; ring
  have hε'1 : ε' < 1 := by nlinarith
  linarith

/-- The real number `u + w√d`. -/
noncomputable def xi (d : ℕ) (q : ℤ × ℤ) : ℝ := q.1 + q.2 * Real.sqrt d

/-- The conjugate `u - w√d`. -/
noncomputable def xiBar (d : ℕ) (q : ℤ × ℤ) : ℝ := q.1 - q.2 * Real.sqrt d

lemma xi_mul_xiBar (d : ℕ) (q : ℤ × ℤ) : xi d q * xiBar d q
    = ((q.1 ^ 2 - d * q.2 ^ 2 : ℤ) : ℝ) := by
  unfold xi xiBar
  have : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  push_cast
  linear_combination -(q.2 : ℝ) ^ 2 * this

/-- Two solutions in the same class differ by a norm-one factor. -/
lemma xi_ratio {d : ℕ} {n t : ℤ} (hn : n ≠ 0) (ht : n ∣ t ^ 2 - d) {q q' : ℤ × ℤ}
    (hq : q.1 ^ 2 - d * q.2 ^ 2 = n) (hq' : q'.1 ^ 2 - d * q'.2 ^ 2 = n)
    (hc : n ∣ q.1 - t * q.2) (hc' : n ∣ q'.1 - t * q'.2) :
    ∃ r s : ℤ, r ^ 2 - d * s ^ 2 = 1 ∧ xi d q = xi d q' * (r + s * Real.sqrt d) := by
  obtain ⟨u, w⟩ := q
  obtain ⟨u', w'⟩ := q'
  simp only at hq hq' hc hc' ⊢
  have h1 : n ∣ u * u' - d * w * w' := by
    obtain ⟨x, hx⟩ := hc; obtain ⟨y, hy⟩ := hc'; obtain ⟨z, hz⟩ := ht
    exact
        ⟨x * u' + t * w * y + w * w' * z, by linear_combination u' * hx + t * w * hy + w * w' * hz⟩
  have h2 : n ∣ w * u' - u * w' := by
    obtain ⟨x, hx⟩ := hc; obtain ⟨y, hy⟩ := hc'
    exact ⟨w * y - w' * x, by linear_combination w * hy - w' * hx⟩
  obtain ⟨r, hr⟩ := h1
  obtain ⟨s, hs⟩ := h2
  refine ⟨r, s, ?_, ?_⟩
  · have : n * n * (r ^ 2 - d * s ^ 2) = n * n * 1 := by
      linear_combination (-(n * r) - (u * u' - d * w * w')) * hr +
        d * (n * s + (w * u' - u * w')) * hs + (u' ^ 2 - d * w' ^ 2) * hq + n * hq'
    exact mul_left_cancel₀ (mul_ne_zero hn hn) this
  · have hδ : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hr' : (n : ℝ) * r = u * u' - d * w * w' := by exact_mod_cast hr.symm
    have hs' : (n : ℝ) * s = w * u' - u * w' := by exact_mod_cast hs.symm
    have hq'' : (n : ℝ) = u' ^ 2 - d * w' ^ 2 := by exact_mod_cast hq'.symm
    unfold xi
    simp only
    apply mul_left_cancel₀ hn'
    linear_combination (-(↑u' + ↑w' * √↑d)) * hr' + (-(↑u' + ↑w' * √↑d) * √↑d) * hs' +
      (↑u + ↑w * √↑d) * hq'' + (↑u * ↑w' ^ 2 - ↑w * ↑u' * ↑w') * hδ

/-- **One residue class.** Solutions of `u² - d w² = n` with `u ≡ t w (mod n)`, a fixed sign
of `u + w√d` and `|u| + |w|√d ≤ L` number at most `log₃ L² + 1`. -/
theorem class_card {d : ℕ} (hd : ¬ IsSquare d) {n t : ℤ} (hn : n ≠ 0) (ht : n ∣ t ^ 2 - d)
    {L : ℕ} {S : Finset (ℤ × ℤ)}
    (hS : ∀ q ∈ S, q.1 ^ 2 - d * q.2 ^ 2 = n ∧ n ∣ q.1 - t * q.2 ∧
      (|(q.1 : ℝ)| + |(q.2 : ℝ)| * Real.sqrt d ≤ L))
    (hsign : ∀ q ∈ S, ∀ q' ∈ S, (0 < xi d q ↔ 0 < xi d q')) :
    S.card ≤ Nat.log 3 (L ^ 2) + 1 := by
  have hirr : Irrational (Real.sqrt d) := irrational_sqrt_natCast_iff.mpr hd
  have hδ0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hδ : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  -- size bounds
  have hbd : ∀ q ∈ S, |xi d q| ≤ L ∧ 1 ≤ L * |xi d q| := by
    intro q hq
    obtain ⟨hq1, -, hq3⟩ := hS q hq
    have hx : |xi d q| ≤ L := by
      unfold xi
      calc |(q.1 : ℝ) + q.2 * Real.sqrt d| ≤ |(q.1 : ℝ)| + |(q.2 : ℝ)
             * Real.sqrt d| := abs_add_le _ _
        _ = |(q.1 : ℝ)| + |(q.2 : ℝ)| * Real.sqrt d := by rw [abs_mul, abs_of_nonneg hδ0]
        _ ≤ L := hq3
    have hxb : |xiBar d q| ≤ L := by
      unfold xiBar
      calc |(q.1 : ℝ) - q.2 * Real.sqrt d| ≤ |(q.1 : ℝ)| + |(q.2 : ℝ) * Real.sqrt d| := abs_sub _ _
        _ = |(q.1 : ℝ)| + |(q.2 : ℝ)| * Real.sqrt d := by rw [abs_mul, abs_of_nonneg hδ0]
        _ ≤ L := hq3
    refine ⟨hx, ?_⟩
    have hprod : |xi d q| * |xiBar d q| = |(n : ℝ)| := by
      rw [← abs_mul, xi_mul_xiBar, hq1]
    calc (1 : ℝ) ≤ |(n : ℝ)| := hn1
      _ = |xi d q| * |xiBar d q| := hprod.symm
      _ ≤ |xi d q| * L := mul_le_mul_of_nonneg_left hxb (abs_nonneg _)
      _ = L * |xi d q| := mul_comm _ _
  set φ : ℤ × ℤ → ℕ := fun q => Nat.log 3 ⌊(L : ℝ) * |xi d q|⌋₊
  -- strict growth across the class
  have hgrow : ∀ q ∈ S, ∀ q' ∈ S, |xi d q'| < |xi d q| → φ q' < φ q := by
    intro q hq q' hq' hlt
    obtain ⟨hq1, hq2, -⟩ := hS q hq
    obtain ⟨hq1', hq2', -⟩ := hS q' hq'
    obtain ⟨r, s, hrs, hrat⟩ := xi_ratio hn ht hq1 hq1' hq2 hq2'
    have hpos' : 0 < |xi d q'| := by
      have := (hbd q' hq').2
      by_contra h; push Not at h
      have : (L : ℝ) * |xi d q'| ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg L) (by linarith [abs_nonneg (xi d q')])
      linarith
    -- the ratio `ε = r + s √d` exceeds `1`
    have hε : 1 < (r : ℝ) + s * Real.sqrt d := by
      have hsame := hsign q hq q' hq'
      have habs : |xi d q| = |xi d q'| * ((r : ℝ) + s * Real.sqrt d) := by
        rw [hrat, abs_mul]
        congr 1
        rcases lt_or_gt_of_ne (show xi d q' ≠ 0 from fun h => by simp [h] at hpos') with hneg | hpo
        · have : xi d q < 0 := by
            by_contra hc; push Not at hc
            rcases hc.lt_or_eq with hc | hc
            · exact absurd (hsame.mp hc) (by linarith)
            · have : |xi d q| = 0 := by rw [← hc]; simp
              linarith
          rw [hrat] at this
          have : 0 < (r : ℝ) + s * Real.sqrt d := by
            by_contra hc; push Not at hc; nlinarith
          exact abs_of_pos this
        · have : 0 < xi d q := hsame.mpr hpo
          rw [hrat] at this
          have : 0 < (r : ℝ) + s * Real.sqrt d := by
            by_contra hc; push Not at hc; nlinarith
          exact abs_of_pos this
      by_contra hc; push Not at hc
      have : |xi d q| ≤ |xi d q'| := by
        rw [habs]; nlinarith
      linarith
    have hn' : (r : ℝ) ^ 2 - (s : ℝ) ^ 2 * Real.sqrt d ^ 2 = 1 := by
      rw [hδ]; exact_mod_cast (by linear_combination hrs : (r ^ 2 - s ^ 2 * d : ℤ) = 1)
    have h3 := unit_ge_three hn' hε
    have habs3 : 3 * |xi d q'| ≤ |xi d q| := by
      rw [hrat, abs_mul]
      have : |(r : ℝ) + s * Real.sqrt d| = (r : ℝ) + s * Real.sqrt d := abs_of_pos (by linarith)
      rw [this]; nlinarith
    -- floors and logarithms
    set m' := ⌊(L : ℝ) * |xi d q'|⌋₊
    have hm'1 : 1 ≤ m' := Nat.le_floor (by exact_mod_cast (hbd q' hq').2)
    have hm3 : 3 * m' ≤ ⌊(L : ℝ) * |xi d q|⌋₊ := by
      apply Nat.le_floor
      have := Nat.floor_le (show 0 ≤ (L : ℝ) * |xi d q'| by positivity)
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) L]
    calc φ q' = Nat.log 3 m' := rfl
      _ < Nat.log 3 m' + 1 := Nat.lt_succ_self _
      _ = Nat.log 3 (m' * 3) := (Nat.log_mul_base (by norm_num) (by omega)).symm
      _ ≤ Nat.log 3 ⌊(L : ℝ) * |xi d q|⌋₊ := Nat.log_mono_right (by omega)
  -- the map `φ` is injective and lands in `[0, log₃ L²]`
  refine (card_le_card_of_injOn φ (t := range (Nat.log 3 (L ^ 2) + 1)) (fun q hq => ?_)
    (fun q hq q' hq' h => ?_)).trans (by simp)
  · have hq := mem_coe.mp hq
    refine mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right ?_))
    apply Nat.floor_le_of_le
    have := (hbd q hq).1
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  · have hq := mem_coe.mp hq
    have hq' := mem_coe.mp hq'
    rcases lt_trichotomy (|xi d q|) (|xi d q'|) with hl | he | hl
    · exact absurd h (hgrow q' hq' q hq hl).ne
    · -- equal absolute values and equal signs force equal numbers
      have hsame := hsign q hq q' hq'
      have hxx : xi d q = xi d q' := by
        rcases abs_eq_abs.mp he with h1 | h1
        · exact h1
        · have hnz : xi d q ≠ 0 := by
            intro h0
            have := (hbd q hq).2
            rw [h0] at this; simp at this; linarith
          rcases lt_or_gt_of_ne hnz with hneg | hpo
          · have : 0 < xi d q' := by rw [h1] at hneg; linarith
            exact absurd (hsame.mpr this) (by linarith)
          · have : xi d q' < 0 := by rw [h1] at hpo; linarith
            exact absurd (hsame.mp hpo) (by linarith)
      obtain ⟨u, w⟩ := q
      obtain ⟨u', w'⟩ := q'
      unfold xi at hxx
      simp only at hxx
      have hw : w = w' := by
        by_contra hne
        have hne' : w - w' ≠ 0 := sub_ne_zero.mpr hne
        have := (hirr.intCast_mul hne').ne_int (u' - u)
        apply this
        push_cast
        linarith
      subst hw
      have : u = u' := by exact_mod_cast (show (u : ℝ) = u' by linarith)
      rw [this]
    · exact absurd h (hgrow q hq q' hq' hl).ne'

/-! ### The norm count -/

/-- The solutions of `U² - D V² = N` in the box `[-B, B]²`. -/
def normSols (D : ℕ) (N : ℤ) (B : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(B : ℤ)) B ×ˢ Icc (-(B : ℤ)) B).filter fun p => p.1 ^ 2 - D * p.2 ^ 2 = N

/-- The square case: `U - mV` is a signed divisor of `N`. -/
lemma normSols_square {m : ℕ} (hm : 0 < m) {N : ℤ} (hN : N ≠ 0) (B : ℕ) :
    (normSols (m * m) N B).card ≤ 2 * N.natAbs.divisors.card := by
  set T : Finset ℤ := N.natAbs.divisors.image (fun k : ℕ => (k : ℤ)) ∪
    N.natAbs.divisors.image (fun k : ℕ => -(k : ℤ))
  have hT : T.card ≤ 2 * N.natAbs.divisors.card := by
    calc T.card ≤ _ := card_union_le _ _
      _ ≤ N.natAbs.divisors.card + N.natAbs.divisors.card := add_le_add card_image_le card_image_le
      _ = _ := by ring
  refine le_trans (card_le_card_of_injOn (fun p => p.1 - m * p.2) (fun p hp => ?_)
    (fun p hp p' hp' h => ?_)) hT
  · have hp' := (mem_filter.mp (mem_coe.mp hp)).2
    push_cast at hp'
    have hdvd : (p.1 - m * p.2) ∣ N := ⟨p.1 + m * p.2, by rw [← hp']; ring⟩
    have hmem : (p.1 - m * p.2).natAbs ∈ N.natAbs.divisors :=
      Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hdvd, by simpa using hN⟩
    rcases Int.natAbs_eq (p.1 - m * p.2) with h | h
    · exact mem_union_left _ (mem_image.mpr ⟨_, hmem, h.symm⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨_, hmem, h.symm⟩)
  · have e1 := (mem_filter.mp (mem_coe.mp hp)).2
    have e2 := (mem_filter.mp (mem_coe.mp hp')).2
    push_cast at e1 e2
    simp only at h
    have hne : p.1 - m * p.2 ≠ 0 := by
      intro h0; apply hN; rw [← e1]
      have : p.1 = m * p.2 := by linarith
      rw [this]; ring
    have hsum : p.1 + m * p.2 = p'.1 + m * p'.2 := by
      apply mul_left_cancel₀ hne
      calc (p.1 - m * p.2) * (p.1 + m * p.2) = N := by rw [← e1]; ring
        _ = (p'.1 - m * p'.2) * (p'.1 + m * p'.2) := by rw [← e2]; ring
        _ = (p.1 - m * p.2) * (p'.1 + m * p'.2) := by rw [h]
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have h1 : p.1 = p'.1 := by linarith
    have h2 : p.2 = p'.2 := by
      have : (m : ℤ) * p.2 = m * p'.2 := by linarith
      exact mul_left_cancel₀ hm' this
    exact Prod.ext h1 h2

/-- The reduction of a solution: `g = gcd(U, fV)`, `u = U/g`, `w = fV/g`, `n = u² - d w²`. -/
structure Reduced (d f : ℕ) (N : ℤ) (p : ℤ × ℤ) (g : ℕ) (u w n : ℤ) : Prop where
  g_pos : 0 < g
  hu : p.1 = g * u
  hw : (f : ℤ) * p.2 = g * w
  hN : N = (g : ℤ) ^ 2 * n
  hn : n = u ^ 2 - d * w ^ 2
  cop : IsCoprime w n

lemma reduce {d f : ℕ} (hf : 0 < f) {N : ℤ} (hN : N ≠ 0) {p : ℤ × ℤ}
    (hp : p.1 ^ 2 - ((f ^ 2 * d : ℕ) : ℤ) * p.2 ^ 2 = N) :
    Reduced d f N p (Int.gcd p.1 (f * p.2)) (p.1 / Int.gcd p.1 (f * p.2))
      ((f * p.2) / Int.gcd p.1 (f * p.2))
      ((p.1 / Int.gcd p.1 (f * p.2)) ^ 2 - d * ((f * p.2) / Int.gcd p.1 (f * p.2)) ^ 2) := by
  set g := Int.gcd p.1 (f * p.2) with hgdef
  have hf' : (f : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  have hg : 0 < g := by
    rw [hgdef, Int.gcd_pos_iff]
    by_contra h
    push Not at h
    apply hN
    rw [← hp, h.1, show p.2 = 0 from (mul_eq_zero.mp h.2).resolve_left hf']
    ring
  have hu : p.1 = g * (p.1 / g) := (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
  have hw : (f : ℤ) * p.2 = g * ((f * p.2) / g) :=
      (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  refine ⟨hg, hu, hw, ?_, rfl, ?_⟩
  · rw [← hp]
    push_cast
    linear_combination (p.1 + g * (p.1 / g)) * hu -
      (d : ℤ) * ((f : ℤ) * p.2 + g * ((f * p.2) / g)) * hw
  · have h1 : IsCoprime (p.1 / g) ((f * p.2) / g) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hg)
    have h2 := (h1.symm.pow_right (n := 2)).add_mul_left_right (-(d : ℤ) * ((f * p.2) / g))
    convert h2 using 1
    ring

/-- The class key of a reduced solution: `t ≡ u w⁻¹ (mod n)`. -/
lemma class_key {d : ℤ} {u w n : ℤ} (hn : n = u ^ 2 - d * w ^ 2) (hc : IsCoprime w n) :
    let t := (u * Int.gcdA w n) % n
    n ∣ t ^ 2 - d ∧ n ∣ u - t * w := by
  intro t
  have hb : w * Int.gcdA w n + n * Int.gcdB w n = 1 := by
    have := Int.gcd_eq_gcd_ab w n
    rw [Int.isCoprime_iff_gcd_eq_one.mp hc] at this
    exact_mod_cast this.symm
  set a := Int.gcdA w n
  set b := Int.gcdB w n
  have hc' : t - u * a = n * (-(u * a / n)) := by
    simp only [t]; rw [Int.emod_def]; ring
  set c := -(u * a / n)
  refine ⟨⟨2 * u * a * c + n * c ^ 2 + a ^ 2 - 2 * d * b + d * n * b ^ 2, ?_⟩, ⟨u * b - c * w, ?_⟩⟩
  · linear_combination (t + u * a + n * c) * hc' - a ^ 2 * hn + d * (w * a + 1 - n * b) * hb
  · linear_combination (-w) * hc' - u * hb

/-- The size bound `|u| + |w|√d ≤ B(⌊√D⌋ + 2)` for a reduced solution in the box. -/
lemma reduced_size {d f B : ℕ} {N : ℤ} {p : ℤ × ℤ} {g : ℕ} {u w n : ℤ}
    (R : Reduced d f N p g u w n) (h1 : |p.1| ≤ B) (h2 : |p.2| ≤ B) :
    |(u : ℝ)| + |(w : ℝ)| * Real.sqrt d ≤ ((B * (Nat.sqrt (f ^ 2 * d) + 2) : ℕ) : ℝ) := by
  have hg : (1 : ℝ) ≤ g := by exact_mod_cast R.g_pos
  have hu : |(u : ℝ)| ≤ B := by
    have e : |((p.1 : ℤ) : ℝ)| = g * |(u : ℝ)| := by
      rw [R.hu]; push_cast; rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg g)]
    have : |((p.1 : ℤ) : ℝ)| ≤ B := by exact_mod_cast h1
    nlinarith [abs_nonneg (u : ℝ)]
  have hw : |(w : ℝ)| ≤ f * B := by
    have e : (f : ℝ) * |((p.2 : ℤ) : ℝ)| = g * |(w : ℝ)| := by
      have := congrArg (fun x : ℤ => |(x : ℝ)|) R.hw
      simp only [Int.cast_mul, Int.cast_natCast, abs_mul, Nat.abs_cast] at this
      exact this
    have : |((p.2 : ℤ) : ℝ)| ≤ B := by exact_mod_cast h2
    nlinarith [abs_nonneg (w : ℝ), Nat.cast_nonneg (α := ℝ) f]
  have hsq : (f : ℝ) * Real.sqrt d < Nat.sqrt (f ^ 2 * d) + 1 := by
    have e : (f : ℝ) * Real.sqrt d = Real.sqrt ((f ^ 2 * d : ℕ) : ℝ) := by
      push_cast
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
    rw [e, Real.sqrt_lt' (by positivity)]
    have := Nat.lt_succ_sqrt (f ^ 2 * d)
    have : ((f ^ 2 * d : ℕ) : ℝ) < ((Nat.sqrt (f ^ 2 * d) + 1)
        * (Nat.sqrt (f ^ 2 * d) + 1) : ℕ) := by
      exact_mod_cast this
    push_cast at this ⊢; nlinarith
  have hδ : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  push_cast
  calc |(u : ℝ)| + |(w : ℝ)| * Real.sqrt d ≤ B + f * B * Real.sqrt d :=
        add_le_add hu (mul_le_mul_of_nonneg_right hw hδ)
    _ = B + B * (f * Real.sqrt d) := by ring
    _ ≤ B + B * (Nat.sqrt (f ^ 2 * d) + 1) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsq.le (Nat.cast_nonneg _)) _
    _ = B * (Nat.sqrt (f ^ 2 * d) + 2) := by ring

/-- **The norm count.** For `D ≥ 1`, `N ≠ 0` the equation `U² - D V² = N` has at most
`2 τ(|N|)³ (log₃ L² + 1)` solutions with `|U|, |V| ≤ B`, where `L = B (⌊√D⌋ + 2)`. -/
theorem norm_count {D : ℕ} {N : ℤ} (B : ℕ) (hD : 1 ≤ D) (hN : N ≠ 0) :
    (normSols D N B).card ≤
      2 * N.natAbs.divisors.card ^ 3 * (Nat.log 3 ((B * (Nat.sqrt D + 2)) ^ 2) + 1) := by
  classical
  have hNa : N.natAbs ≠ 0 := by simpa using hN
  have hτ : 1 ≤ N.natAbs.divisors.card :=
    card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hNa⟩
  by_cases hsq : IsSquare D
  · obtain ⟨m, hm⟩ := hsq
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
    rw [hm]
    calc (normSols (m * m) N B).card ≤ 2 * N.natAbs.divisors.card := normSols_square hm0 hN B
      _ ≤ 2 * N.natAbs.divisors.card ^ 3 * 1 := by
          rw [mul_one]
          exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨d, f, hd0, hf0, hDf, hsf⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < D)
  have hdsq : ¬ IsSquare d := fun ⟨r, hr⟩ => hsq ⟨f * r, by rw [← hDf, hr]; ring⟩
  have hsfZ : Squarefree (d : ℤ) := Int.squarefree_natCast.mpr hsf
  subst hDf
  set L := B * (Nat.sqrt (f ^ 2 * d) + 2)
  -- the reduced data of a solution
  set g : ℤ × ℤ → ℕ := fun p => Int.gcd p.1 (f * p.2)
  set u : ℤ × ℤ → ℤ := fun p => p.1 / g p
  set w : ℤ × ℤ → ℤ := fun p => (f * p.2) / g p
  set n : ℤ × ℤ → ℤ := fun p => u p ^ 2 - d * w p ^ 2
  set t : ℤ × ℤ → ℤ := fun p => (u p * Int.gcdA (w p) (n p)) % n p
  set key : ℤ × ℤ → (ℕ × ℕ) × Bool := fun p => ((g p, (t p).toNat), decide (0 < xi d (u p, w p)))
  have hR : ∀ p ∈ normSols (f ^ 2 * d) N B, Reduced d f N p (g p) (u p) (w p) (n p) := by
    intro p hp
    exact reduce hf0 hN (mem_filter.mp hp).2
  have hn0 : ∀ p ∈ normSols (f ^ 2 * d) N B, n p ≠ 0 := by
    intro p hp h0
    apply hN
    rw [(hR p hp).hN, h0, mul_zero]
  have hkey : ∀ p ∈ normSols (f ^ 2 * d) N B, n p ∣ t p ^ 2 - d ∧ n p ∣ u p - t p * w p :=
    fun p hp => class_key (hR p hp).hn (hR p hp).cop
  have ht0 : ∀ p ∈ normSols (f ^ 2 * d) N B, 0 ≤ t p ∧ t p < (n p).natAbs := fun p hp =>
    ⟨Int.emod_nonneg _ (hn0 p hp), Int.emod_lt _ (hn0 p hp)⟩
  have hnabs : ∀ p ∈ normSols (f ^ 2 * d) N B, (n p).natAbs = N.natAbs / g p ^ 2 ∧
      g p ^ 2 ∣ N.natAbs := by
    intro p hp
    have e : N.natAbs = g p ^ 2 * (n p).natAbs := by
      rw [(hR p hp).hN, Int.natAbs_mul]; simp
    have hg := (hR p hp).g_pos
    exact ⟨by rw [e, Nat.mul_div_cancel_left _ (by positivity)], ⟨_, e⟩⟩
  -- the keys
  set G := N.natAbs.divisors.filter fun g => g ^ 2 ∣ N.natAbs
  set KS : Finset ((ℕ × ℕ) × Bool) :=
    (G.biUnion fun g => (sqRoots d (N.natAbs / g ^ 2)).image fun t => (g, t)) ×ˢ univ
  have hKS : KS.card ≤ 2 * N.natAbs.divisors.card ^ 3 := by
    have h1 : (G.biUnion fun g => (sqRoots d (N.natAbs / g ^ 2)).image fun t => (g, t)).card ≤
        N.natAbs.divisors.card * N.natAbs.divisors.card ^ 2 := by
      refine card_biUnion_le.trans ?_
      calc ∑ g ∈ G, ((sqRoots d (N.natAbs / g ^ 2)).image fun t => (g, t)).card
          ≤ ∑ _g ∈ G, N.natAbs.divisors.card ^ 2 := by
            refine sum_le_sum fun g hg => card_image_le.trans ((card_sqRoots_le hsfZ _).trans ?_)
            have hdiv : N.natAbs / g ^ 2 ∣ N.natAbs := Nat.div_dvd_of_dvd (mem_filter.mp hg).2
            exact Nat.pow_le_pow_left (card_le_card (Nat.divisors_subset_of_dvd hNa hdiv)) 2
        _ = G.card * N.natAbs.divisors.card ^ 2 := by rw [sum_const, smul_eq_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
    calc KS.card = _ * 2 := by rw [card_product, card_univ, Fintype.card_bool]
      _ ≤ N.natAbs.divisors.card * N.natAbs.divisors.card ^ 2 * 2 := Nat.mul_le_mul_right _ h1
      _ = 2 * N.natAbs.divisors.card ^ 3 := by ring
  have hmaps : ∀ p ∈ normSols (f ^ 2 * d) N B, key p ∈ KS := by
    intro p hp
    obtain ⟨hna, hg2⟩ := hnabs p hp
    refine mem_product.mpr ⟨mem_biUnion.mpr ⟨g p, mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(dvd_pow_self _ (by norm_num)).trans hg2, hNa⟩, hg2⟩, mem_image.mpr ⟨(t p).toNat, ?_, rfl⟩⟩,
      mem_univ _⟩
    rw [← hna]
    refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
    · have := ht0 p hp; omega
    · rw [Int.toNat_of_nonneg (ht0 p hp).1, Int.natCast_natAbs]
      exact (abs_dvd _ _).mpr (hkey p hp).1
  -- each key class is small
  have hfib : ∀ k ∈ KS, ((normSols (f ^ 2 * d) N B).filter fun p => key p = k).card ≤
      Nat.log 3 (L ^ 2) + 1 := by
    intro k _
    set F := (normSols (f ^ 2 * d) N B).filter fun p => key p = k
    rcases F.eq_empty_or_nonempty with hF | ⟨p0, hp0⟩
    · rw [hF]; simp
    have hp0' := mem_filter.mp hp0
    have hinj : Set.InjOn (fun p => (u p, w p)) F := by
      intro p hp p' hp' h
      have hp1 := mem_filter.mp (mem_coe.mp hp)
      have hp1' := mem_filter.mp (mem_coe.mp hp')
      have hgg : g p = g p' := by
        have := hp1.2.trans hp1'.2.symm
        simp only [key, Prod.mk.injEq] at this
        exact this.1.1
      simp only [Prod.mk.injEq] at h
      have R := hR p hp1.1
      have R' := hR p' hp1'.1
      have hf' : (f : ℤ) ≠ 0 := by exact_mod_cast hf0.ne'
      refine Prod.ext ?_ ?_
      · rw [R.hu, R'.hu, hgg, h.1]
      · apply mul_left_cancel₀ hf'
        rw [R.hw, R'.hw, hgg, h.2]
    rw [← card_image_of_injOn hinj]
    have R0 := hR p0 hp0'.1
    refine class_card hdsq (hn0 p0 hp0'.1) (hkey p0 hp0'.1).1 (fun q hq => ?_)
        (fun q hq q' hq' => ?_)
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      have hp1 := mem_filter.mp hp
      have R := hR p hp1.1
      have hk := hp1.2.trans hp0'.2.symm
      simp only [key, Prod.mk.injEq] at hk
      obtain ⟨⟨hgg, htt⟩, -⟩ := hk
      have hnn : n p = n p0 := by
        have e := R.hN.symm.trans R0.hN
        rw [hgg] at e
        have hg0 : ((g p0 : ℕ) : ℤ) ^ 2 ≠ 0 := by have := R0.g_pos; positivity
        exact mul_left_cancel₀ hg0 e
      have htt' : t p = t p0 := by
        have := congrArg (fun x : ℕ => (x : ℤ)) htt
        rwa [Int.toNat_of_nonneg (ht0 p hp1.1).1, Int.toNat_of_nonneg (ht0 p0 hp0'.1).1] at this
      refine ⟨by simp only; rw [← hnn], by simp only; rw [← hnn, ← htt']; exact (hkey p
          hp1.1).2, ?_⟩
      have hb := mem_filter.mp hp1.1
      obtain ⟨hb1, hb2⟩ := mem_product.mp hb.1
      exact reduced_size R (abs_le.mpr ⟨(mem_Icc.mp hb1).1, (mem_Icc.mp hb1).2⟩)
        (abs_le.mpr ⟨(mem_Icc.mp hb2).1, (mem_Icc.mp hb2).2⟩)
    · obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      obtain ⟨p', hp', rfl⟩ := mem_image.mp hq'
      have hk := (mem_filter.mp hp).2.trans (mem_filter.mp hp').2.symm
      simp only [key, Prod.mk.injEq, decide_eq_decide] at hk
      exact hk.2
  calc (normSols (f ^ 2 * d) N B).card ≤ (Nat.log 3 (L ^ 2) + 1) * KS.card :=
        card_le_mul_card_image_of_maps_to hmaps _ hfib
    _ ≤ (Nat.log 3 (L ^ 2) + 1) * (2 * N.natAbs.divisors.card ^ 3) := Nat.mul_le_mul_left _ hKS
    _ = _ := by ring

end PierceBound
