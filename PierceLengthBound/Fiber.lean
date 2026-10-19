/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Block

/-!
# A fixed triple `(u, v, D)` allows few starting points

Fix positive integers `u, v, D`. Put `p = u² + u + v`, `c = au`, `ℓ = a(u² + v) + D`,
`M(q) = uq² + pq + v`, `L(q) = cq + ℓ`, `U(q) = ucq + cp - uℓ` and `R = uℓ² - cpℓ + c²v`.
Then `c² M(q) - U(q) L(q) = R` identically, so `x M(q) = L(q)` forces `R = M(q)(c² - U(q)x)`.

* if `R ≠ 0` then `M(q) ∣ R`, and `M` is strictly increasing;
* if `R = 0` then `U(q) x = c²`, so `U(q) ∣ c²`, and `U` is strictly increasing.

Either way the number of admissible `q` is at most a divisor count of a number `≤ 32 a⁷`.
-/

@[expose] public section

namespace PierceLengthBound

/-- The polynomial identity `c² M(q) - U(q) L(q) = R`. -/
theorem fiber_poly_identity (u v c ℓ q : ℤ) :
    c ^ 2 * (u * q ^ 2 + (u ^ 2 + u + v) * q + v) -
        (u * c * q + c * (u ^ 2 + u + v) - u * ℓ) * (c * q + ℓ) =
      u * ℓ ^ 2 - c * (u ^ 2 + u + v) * ℓ + c ^ 2 * v := by
  ring

/-- **Fiber count.** If `Δ` bounds the divisor function on `[1, 32 a⁷]`, a fixed triple
`(u, v, D)` with `u, v ≤ a`, `D ≤ 2a` admits at most `Δ` quotients `q` for which the
fiber equation `x M(q) = L(q)` has a positive solution `x`. -/
theorem fiber_card_le (a u v D Δ : ℕ) (ha : 1 ≤ a) (hu : 1 ≤ u) (hua : u ≤ a) (hv : 1 ≤ v)
    (hva : v ≤ a) (hDa : D ≤ 2 * a)
    (hΔ : ∀ n : ℕ, 0 < n → n ≤ 32 * a ^ 7 → n.divisors.card ≤ Δ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, ∃ x : ℕ, 0 < x ∧
      x * (u * q ^ 2 + (u ^ 2 + u + v) * q + v) = a * u * q + (a * (u ^ 2 + v) + D)) :
    Q.card ≤ Δ := by
  classical
  set c : ℕ := a * u with hc
  set ℓ : ℕ := a * (u ^ 2 + v) + D with hℓ
  set R : ℤ := (u : ℤ) * ℓ ^ 2 - c * (u ^ 2 + u + v) * ℓ + c ^ 2 * v with hR
  set M : ℕ → ℕ := fun q => u * q ^ 2 + (u ^ 2 + u + v) * q + v with hM
  set U : ℕ → ℤ := fun q => (u : ℤ) * c * q + c * (u ^ 2 + u + v) - u * ℓ with hU
  have hMpos : ∀ q, 0 < M q := fun q => by simp only [hM]; positivity
  have hMmono : StrictMono M := by
    intro q₁ q₂ h
    simp only [hM]
    have h1 : q₁ ^ 2 ≤ q₂ ^ 2 := Nat.pow_le_pow_left h.le 2
    have h2 : (u ^ 2 + u + v) * q₁ < (u ^ 2 + u + v) * q₂ :=
      Nat.mul_lt_mul_of_pos_left h (by positivity)
    have h3 : u * q₁ ^ 2 ≤ u * q₂ ^ 2 := Nat.mul_le_mul_left u h1
    omega
  have hcpos : 0 < c := by simp only [hc]; positivity
  have hUmono : StrictMono U := by
    intro q₁ q₂ h
    simp only [hU]
    have : (0 : ℤ) < (u : ℤ) * c := by positivity
    have h' : (q₁ : ℤ) < q₂ := by exact_mod_cast h
    nlinarith
  -- the key relation `R = M(q)(c² - U(q)x)`
  have hkey : ∀ q ∈ Q, ∃ x : ℕ, 0 < x ∧ R = (M q : ℤ) * ((c : ℤ) ^ 2 - U q * x) := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := hQ q hq
    refine ⟨x, hx, ?_⟩
    have hxq' : (x : ℤ) * (M q : ℤ) = (c : ℤ) * q + ℓ := by
      simp only [hM, hc, hℓ]; exact_mod_cast hxq
    have hid := fiber_poly_identity u v c ℓ q
    simp only [hR, hU]
    simp only [hM] at hxq' ⊢
    push_cast at hxq' ⊢
    linear_combination -hid + (u * c * q + c * (u ^ 2 + u + v) - u * ℓ) * hxq'
  -- size bounds
  have hℓle : ℓ ≤ 4 * a ^ 3 := by
    have : u ^ 2 + v ≤ a ^ 2 + a := Nat.add_le_add (Nat.pow_le_pow_left hua 2) hva
    have h1 : a * (u ^ 2 + v) ≤ a * (a ^ 2 + a) := Nat.mul_le_mul_left a this
    have h2 : a ≤ a ^ 3 := by
      calc a = a ^ 1 := (pow_one a).symm
        _ ≤ a ^ 3 := Nat.pow_le_pow_right ha (by norm_num)
    have h3 : a ^ 2 ≤ a ^ 3 := Nat.pow_le_pow_right ha (by norm_num)
    simp only [hℓ]
    nlinarith
  have hple : u ^ 2 + u + v ≤ 3 * a ^ 2 := by
    have h1 : u ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hua 2
    have h2 : a ≤ a ^ 2 := by nlinarith
    omega
  have hcle : c ≤ a ^ 2 := by simp only [hc]; nlinarith
  have hbig : u * ℓ ^ 2 + c * (u ^ 2 + u + v) * ℓ + c ^ 2 * v ≤ 32 * a ^ 7 := by
    calc u * ℓ ^ 2 + c * (u ^ 2 + u + v) * ℓ + c ^ 2 * v
        ≤ a * (4 * a ^ 3) ^ 2 + a ^ 2 * (3 * a ^ 2) * (4 * a ^ 3) + (a ^ 2) ^ 2 * a := by
          gcongr
      _ = 28 * a ^ 7 + a ^ 5 := by ring
      _ ≤ 32 * a ^ 7 := by
          have : a ^ 5 ≤ a ^ 7 := Nat.pow_le_pow_right ha (by norm_num)
          omega
  by_cases hR0 : R = 0
  · -- `U(q) x = c²`
    have hdiv : ∀ q ∈ Q, 0 < U q ∧ (U q).toNat ∣ c ^ 2 := by
      intro q hq
      obtain ⟨x, hx, hrel⟩ := hkey q hq
      rw [hR0] at hrel
      have hM0 : (M q : ℤ) ≠ 0 := by exact_mod_cast (hMpos q).ne'
      have hux : U q * x = (c : ℤ) ^ 2 :=
        by have := (mul_eq_zero.mp hrel.symm).resolve_left hM0; linarith
      have hc2 : (0 : ℤ) < (c : ℤ) ^ 2 := by positivity
      have hx' : (0 : ℤ) < x := by exact_mod_cast hx
      have hUpos : 0 < U q := by
        by_contra hneg; rw [not_lt] at hneg; nlinarith
      refine ⟨hUpos, ?_⟩
      have : ((U q).toNat : ℤ) ∣ ((c ^ 2 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hUpos.le]; push_cast; exact ⟨x, hux.symm⟩
      exact_mod_cast this
    have hinj : Set.InjOn (fun q => (U q).toNat) Q := by
      intro q₁ h₁ q₂ h₂ h
      have e₁ := Int.toNat_of_nonneg (hdiv q₁ h₁).1.le
      have e₂ := Int.toNat_of_nonneg (hdiv q₂ h₂).1.le
      have : U q₁ = U q₂ := by
        have h' : ((U q₁).toNat : ℤ) = ((U q₂).toNat : ℤ) := by simp only at h; rw [h]
        rwa [e₁, e₂] at h'
      exact hUmono.injective this
    calc Q.card ≤ (c ^ 2).divisors.card := by
          apply Finset.card_le_card_of_injOn _ _ hinj
          intro q hq
          exact Nat.mem_divisors.mpr ⟨(hdiv q hq).2, by positivity⟩
      _ ≤ Δ := by
          apply hΔ _ (by positivity)
          calc c ^ 2 ≤ (a ^ 2) ^ 2 := Nat.pow_le_pow_left hcle 2
            _ = a ^ 4 := by ring
            _ ≤ a ^ 7 := Nat.pow_le_pow_right ha (by norm_num)
            _ ≤ 32 * a ^ 7 := by omega
  · -- `M(q) ∣ R`
    have hdiv : ∀ q ∈ Q, M q ∣ R.natAbs := by
      intro q hq
      obtain ⟨x, -, hrel⟩ := hkey q hq
      exact Int.natCast_dvd.mp ⟨_, hrel⟩
    have hRle : R.natAbs ≤ 32 * a ^ 7 := by
      have : (R.natAbs : ℤ) ≤ ((u * ℓ ^ 2 + c * (u ^ 2 + u + v) * ℓ + c ^ 2 * v : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]
        push_cast
        simp only [hR]
        have h0 : (0 : ℤ) ≤ (c : ℤ) * (u ^ 2 + u + v) * ℓ := by positivity
        have h1 : (0 : ℤ) ≤ (u : ℤ) * ℓ ^ 2 := by positivity
        have h2 : (0 : ℤ) ≤ (c : ℤ) ^ 2 * v := by positivity
        rw [abs_le]
        constructor <;> linarith
      have := (show (R.natAbs : ℤ) ≤ ((32 * a ^ 7 : ℕ) : ℤ) from
        this.trans (by exact_mod_cast hbig))
      exact_mod_cast this
    calc Q.card ≤ R.natAbs.divisors.card := by
          apply Finset.card_le_card_of_injOn M _ (hMmono.injective.injOn)
          intro q hq
          exact Nat.mem_divisors.mpr ⟨hdiv q hq, by simpa using hR0⟩
      _ ≤ Δ := hΔ _ (by simpa using hR0) hRle

end PierceLengthBound
