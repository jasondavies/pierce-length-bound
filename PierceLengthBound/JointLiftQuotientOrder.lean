/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftLocalOrders

/-! The monic normalization equation forces the exact quotient pole order and
even infinity multiplicity. This is a discrete Newton-polygon calculation. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

variable {K : Type*} [Field K]

lemma discrete_order_pow (v : AddValuation K (WithTop ℤ)) {q : K} {r : ℤ}
    (hq : v q = (r : WithTop ℤ)) (n : ℕ) :
    v (q ^ n) = (((n : ℤ) * r : ℤ) : WithTop ℤ) := by
  rw [v.map_pow, hq]
  norm_cast

/-- If a monic quartic with the original coordinate degree bounds has order
`-6e` at `-q`, its leading term forces `ord(q) = -3e/2` and `e` even.
The smaller coefficients may vanish identically. -/
theorem monic_quartic_quotient_discrete_order (v : AddValuation K (WithTop ℤ))
    (p : Fin 4 → K) (q : K) {e : ℤ} (he : 0 < e)
    (hp : ∀ j, ((-(4 - (j.val : ℤ)) * e : ℤ) : WithTop ℤ) ≤ v (p j))
    (hP : v (q ^ 4 + ∑ j : Fin 4, p j * (-q) ^ j.val) =
      ((-6 * e : ℤ) : WithTop ℤ)) :
    ∃ t : ℤ, 0 < t ∧ e = 2 * t ∧ v q = ((-3 * t : ℤ) : WithTop ℤ) := by
  have hq0 : q ≠ 0 := by
    intro hz
    have hp0 := hp 0
    have hvp : v (p 0) = ((-6 * e : ℤ) : WithTop ℤ) := by
      simpa [hz, Fin.sum_univ_four] using hP
    change ((-4 * e : ℤ) : WithTop ℤ) ≤ v (p 0) at hp0
    rw [hvp] at hp0
    have hh : -4 * e ≤ -6 * e := by exact_mod_cast hp0
    omega
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hq0)
  have hq : v q = (r : WithTop ℤ) := hr.symm
  have hneg : v (-q) = (r : WithTop ℤ) := by rw [v.map_neg, hq]
  have hterms (j : Fin 4) :
      ((-(4 - (j.val : ℤ)) * e + (j.val : ℤ) * r : ℤ) : WithTop ℤ) ≤
        v (p j * (-q) ^ j.val) :=
    discrete_order_mul_ge v (hp j) (discrete_order_pow v hneg j.val).ge
  have hq4 : v (q ^ 4) = ((4 * r : ℤ) : WithTop ℤ) := by
    simpa using discrete_order_pow v hq 4
  have hrlt : r < -e := by
    by_contra hn
    have hrge : -e ≤ r := by omega
    have hsum : ((-4 * e : ℤ) : WithTop ℤ) ≤
        v (∑ j : Fin 4, p j * (-q) ^ j.val) := by
      apply v.map_le_sum
      intro j _
      apply le_trans ?_ (hterms j)
      exact_mod_cast (show -4 * e ≤ -(4 - (j.val : ℤ)) * e + (j.val : ℤ) * r by
        nlinarith [mul_nonneg (Int.natCast_nonneg j.val) (show 0 ≤ r + e by omega)])
    have htotal : ((-4 * e : ℤ) : WithTop ℤ) ≤
        v (q ^ 4 + ∑ j : Fin 4, p j * (-q) ^ j.val) := by
      apply v.map_le_add _ hsum
      rw [hq4]
      exact_mod_cast (show -4 * e ≤ 4 * r by omega)
    rw [hP] at htotal
    have hh : -4 * e ≤ -6 * e := by exact_mod_cast htotal
    omega
  have hsum : ((4 * r : ℤ) : WithTop ℤ) <
      v (∑ j : Fin 4, p j * (-q) ^ j.val) := by
    apply v.map_lt_sum WithTop.coe_ne_top
    intro j _
    apply lt_of_lt_of_le ?_ (hterms j)
    have hj : (j.val : ℤ) < 4 := by exact_mod_cast j.isLt
    exact_mod_cast (show 4 * r < -(4 - (j.val : ℤ)) * e + (j.val : ℤ) * r by
      nlinarith [mul_pos (show 0 < 4 - (j.val : ℤ) by omega)
        (show 0 < -e - r by omega)])
  have hdom := v.map_add_eq_of_lt_left (hq4 ▸ hsum)
  rw [hP, hq4] at hdom
  have heq : -6 * e = 4 * r := by exact_mod_cast hdom
  refine ⟨e / 2, by omega, by omega, ?_⟩
  rw [hq]
  congr 1
  omega

end
end PierceLengthBound.FixedDividend
