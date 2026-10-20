/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalParabolicModel

/-! A containing plane has an available nonconstant coordinate pivot. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma first_node_not_scalar_of_generation {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) {d N M : ℕ} {b : ℤ}
    (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (hspan : ∀ n ≥ M, filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map
          (LinearMap.mulLeft K (Ideal.Quotient.mk I (X 0))) =
      filteredCoordinateSpace I (n + 2)) (c : K) :
    Ideal.Quotient.mk I (X 0) ≠ algebraMap K _ c := by
  intro hc
  let n := max N M
  have hnN : N ≤ n := le_max_left _ _
  have hnM : M ≤ n := le_max_right _ _
  have hs := hspan n hnM
  rw [hc] at hs
  have hle : (filteredCoordinateSpace I (n + 1)).map
      (LinearMap.mulLeft K (algebraMap K _ c)) ≤ filteredCoordinateSpace I (n + 1) := by
    rintro y ⟨x, hx, rfl⟩
    change algebraMap K _ c * x ∈ filteredCoordinateSpace I (n + 1)
    rw [← Algebra.smul_def]
    exact (filteredCoordinateSpace I (n + 1)).smul_mem c hx
  rw [sup_eq_left.mpr hle] at hs
  have he := congrArg
    (fun V : Submodule K (MvPolynomial (Fin 3) K ⧸ I) => (Module.finrank K V : ℤ)) hs
  rw [hdegree (n + 1) (by omega), hdegree (n + 2) (by omega)] at he
  have : (0 : ℤ) < d := by exact_mod_cast hd
  push_cast at he
  nlinarith

/-- The two plane charts cover every nonzero containing plane of an actual
nonexceptional component of positive degree. -/
theorem rational_nonexceptional_plane_pivot
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (ha : a ≠ 0) (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    (n0 n1 n2 e : ℚ) (hn : n0 ≠ 0 ∨ n1 ≠ 0 ∨ n2 ≠ 0)
    (hp : C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e ∈ I)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    n1 ≠ 0 ∨ n2 ≠ 0 := by
  by_contra hh
  push Not at hh
  have hn0 : n0 ≠ 0 := hn.elim id (fun h => False.elim (h.elim (fun h => h hh.1) (fun h => h hh.2)))
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation
    hρ hu hv hne ρ' u' v' A a ha I hf hg
  let q := Ideal.Quotient.mkₐ ℚ I
  have hp' : q (C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp
  simp only [hh.1, hh.2, map_add, map_mul, map_zero, zero_mul, add_zero,
    MvPolynomial.algHom_C] at hp'
  have hr : algebraMap ℚ _ e + algebraMap ℚ _ n0 * q (X 0) = 0 := by
    simpa only [add_comm] using hp'
  exact first_node_not_scalar_of_generation I hd hdegree hs (-e / n0)
    (algebra_scalar_of_linear_eq hn0 hr)

end
end PierceLengthBound.FixedDividend
