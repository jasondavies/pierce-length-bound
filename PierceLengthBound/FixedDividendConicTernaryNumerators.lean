/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicBoundedParameter

/-! Integer numerators for the exact ternary fixed-dividend quadratic. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The three homogeneous and three linear coefficient numerators, over `D`
and `D²` respectively. -/
def ternaryNumerators (r u v r' u' v' D : ℤ) : Fin 6 → ℤ :=
  let a := -r - u
  let b := u - v
  let c := v - D
  let T := v - D - v'
  ![a, b, c, (r - a - r') * D - a * T,
    (a - b + r' + u') * D - b * T, (b - c - u' + v') * D - c * T]

lemma ternaryNumerators_rat (r u v r' u' v' D : ℤ) (hD : D ≠ 0) :
    let w := ternaryNumerators r u v r' u' v' D
    let ρ : ℚ := r / D
    let U : ℚ := u / D
    let V : ℚ := v / D
    let ρ' : ℚ := r' / D
    let U' : ℚ := u' / D
    let V' : ℚ := v' / D
    ![(w 0 : ℚ) / D, (w 1 : ℚ) / D, (w 2 : ℚ) / D,
      (w 3 : ℚ) / D ^ 2, (w 4 : ℚ) / D ^ 2, (w 5 : ℚ) / D ^ 2] =
    ![-ρ - U, U - V, V - 1,
      ρ - (-ρ - U) - ρ' - (-ρ - U) * (V - 1 - V'),
      (-ρ - U) - (U - V) + ρ' + U' - (U - V) * (V - 1 - V'),
      (U - V) - (V - 1) - U' + V' - (V - 1) * (V - 1 - V')] := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  dsimp only
  ext j
  fin_cases j <;> simp [ternaryNumerators] <;> field_simp

/-- All six ternary numerators have height at most `12M²` if the common
numerators and denominator have height at most `M ≥ 1`. -/
theorem ternaryNumerators_height {r u v r' u' v' D M : ℤ} (hM : 1 ≤ M)
    (hr : |r| ≤ M) (hu : |u| ≤ M) (hv : |v| ≤ M)
    (hr' : |r'| ≤ M) (hu' : |u'| ≤ M) (hv' : |v'| ≤ M) (hD : |D| ≤ M) :
    ∀ j, |ternaryNumerators r u v r' u' v' D j| ≤ 12 * M ^ 2 := by
  let a := -r - u
  let b := u - v
  let c := v - D
  let T := v - D - v'
  have hsub (x y : ℤ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le x 0 y
  have ha : |a| ≤ 2 * M := by
    have hh := hsub (-r) u
    simp only [abs_neg] at hh
    dsimp [a]
    omega
  have hb : |b| ≤ 2 * M := (hsub u v).trans (by omega)
  have hc : |c| ≤ 2 * M := (hsub v D).trans (by omega)
  have hT : |T| ≤ 3 * M := by
    change |c - v'| ≤ 3 * M
    exact (hsub c v').trans (by omega)
  have hlin0 : |r - a - r'| ≤ 4 * M := by
    have h1 := hsub r a
    have h2 := hsub (r - a) r'
    omega
  have hlin1 : |a - b + r' + u'| ≤ 6 * M := by
    have h1 := hsub a b
    have h2 := abs_add_le (a - b) r'
    have h3 := abs_add_le (a - b + r') u'
    omega
  have hlin2 : |b - c - u' + v'| ≤ 6 * M := by
    have h1 := hsub b c
    have h2 := hsub (b - c) u'
    have h3 := abs_add_le (b - c - u') v'
    omega
  have hprod {x y : ℤ} (hx : |x| ≤ 6 * M) (hy : |y| ≤ 2 * M) :
      |x * D - y * T| ≤ 12 * M ^ 2 := by
    calc |x * D - y * T| ≤ |x * D| + |y * T| := hsub _ _
      _ = |x| * |D| + |y| * |T| := by simp only [abs_mul]
      _ ≤ (6 * M) * M + (2 * M) * (3 * M) := by gcongr
      _ = _ := by ring
  have hM2 : 2 * M ≤ 12 * M ^ 2 := by nlinarith
  intro j
  fin_cases j
  · exact ha.trans hM2
  · exact hb.trans hM2
  · exact hc.trans hM2
  · exact hprod (hlin0.trans (by omega)) ha
  · exact hprod hlin1 hb
  · exact hprod hlin2 hc

end
end PierceLengthBound.FixedDividend
