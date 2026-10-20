/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicCoefficientHeight

/-! Bounded integral parameters obtained from the exact rational plane models. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Exact coefficient clearing followed by bounded integer parametrization.
The coefficient height is `10 B²L²`; therefore both the common denominator
and all three quadratic numerators have polynomial height in `B,L`. -/
theorem rational_plane_bounded_integer_parameter
    (a b c l0 l1 l2 D n0 n1 n2 e : ℤ) {B L : ℕ}
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hD0 : D ≠ 0) (hn : n2 ≠ 0)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (hD : |D| ≤ B)
    (hl0 : |l0| ≤ B) (hl1 : |l1| ≤ B) (hl2 : |l2| ≤ B)
    (hn0 : |n0| ≤ L) (hn1 : |n1| ≤ L) (hn2 : |n2| ≤ L) (he : |e| ≤ L)
    (v : Fin 6 → ℚ)
    (hv : ∀ j, v j = planeConicCoefficients ((a : ℚ) / D) ((b : ℚ) / D)
      ((c : ℚ) / D) ((l0 : ℚ) / D ^ 2) ((l1 : ℚ) / D ^ 2) ((l2 : ℚ) / D ^ 2)
      (-(n0 : ℚ) / n2) (-(n1 : ℚ) / n2) (-(e : ℚ) / n2) j)
    (hα : v 0 ≠ 0) (hΔ : (v 1) ^ 2 - 4 * v 0 * v 2 = 0)
    (hJ : 2 * v 1 * v 3 - 4 * v 0 * v 4 ≠ 0) :
    let w := integralPlaneConicCoefficients a b c l0 l1 l2 D n0 n1 n2 e
    ∃ (E : ℤ) (N : Fin 3 → Polynomial ℤ), E ≠ 0 ∧
      |E| ≤ 12 * (L : ℤ) * (10 * B ^ 2 * L ^ 2) ^ 3 ∧
      (∀ j, (N j).natDegree ≤ 2) ∧
      (∀ j k, |(N j).coeff k| ≤ 33 * (L : ℤ) * (10 * B ^ 2 * L ^ 2) ^ 3) ∧
      (N 1).coeff 2 ≠ 0 ∧
      (∀ z : Fin 3 → ℤ,
        conicValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (z 0) (z 1) = 0 →
        n2 * z 2 + n1 * z 0 + n0 * z 1 + e = 0 →
        ∀ j, E * z j = (N j).eval (2 * w 0 * z 0 + w 1 * z 1 + w 3)) ∧
      Set.InjOn (fun z : Fin 3 → ℤ => 2 * w 0 * z 0 + w 1 * z 1 + w 3)
        {z | conicValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (z 0) (z 1) = 0 ∧
          n2 * z 2 + n1 * z 0 + n0 * z 1 + e = 0} := by
  let w := integralPlaneConicCoefficients a b c l0 l1 l2 D n0 n1 n2 e
  let K : ℕ := 10 * B ^ 2 * L ^ 2
  have hK : 1 ≤ K := by
    have hB0 : 0 < B := by omega
    have hL0 : 0 < L := by omega
    have hK0 : 0 < K := by dsimp [K]; positivity
    omega
  have hw : ∀ j, |w j| ≤ (K : ℤ) := by
    have hh := integralPlaneConicCoefficients_height (by exact_mod_cast hB)
      (show (0 : ℤ) ≤ L by positivity) ha hb hc hD hl0 hl1 hl2 hn0 hn1 hn2 he
    simpa only [K, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hh
  obtain ⟨hwα, hwΔ, hwJ, hwpoints⟩ := integralPlaneConicCoefficients_parabolic
    a b c l0 l1 l2 D n0 n1 n2 e hD0 hn v hv hα hΔ hJ
  obtain ⟨E, N, hE, hEb, hNd, hNb, hN2, hrepr, hinj⟩ :=
    parabola_integer_parameter_height hK hL hwα hn hwJ hwΔ
      (hw 0) (hw 1) (hw 3) (hw 4) (hw 5) hn2 hn1 hn0 he
  refine ⟨E, N, hE, ?_, hNd, ?_, hN2, ?_, ?_⟩
  · simpa only [K, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hEb
  · simpa only [K, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hNb
  · intro z hz hp
    exact hrepr z (hwpoints _ _ hz) hp
  · intro z hz t ht hh
    exact hinj ⟨hwpoints _ _ hz.1, hz.2⟩ ⟨hwpoints _ _ ht.1, ht.2⟩ hh

end
end PierceLengthBound.FixedDividend
