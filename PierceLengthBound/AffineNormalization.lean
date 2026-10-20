/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalChart
public import PierceLengthBound.CurveNormalization

/-! Finite normalization of the original affine component. The same eventual
generation which controls infinity makes the affine coordinate ring finite
over its first-coordinate parameter. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

theorem coordinateRing_finite_over_parameter {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (l : MvPolynomial σ K ⧸ I)
    {N : ℕ} (hspan : ∀ n ≥ N, filteredCoordinateSpace I (n + 1) ⊔
      (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
        filteredCoordinateSpace I (n + 2)) :
    Module.Finite (Algebra.adjoin K {l}) (MvPolynomial σ K ⧸ I) := by
  let T := Algebra.adjoin K {l}
  let U := filteredCoordinateSpace I (N + 1)
  let V := Submodule.span T (U : Set (MvPolynomial σ K ⧸ I))
  have hfg : V.FG := (Module.Finite.iff_fg.mp (inferInstance : Module.Finite K U)).span
  have hmem (n : ℕ) : filteredCoordinateSpace I n ≤ V.restrictScalars K := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      by_cases hn : n ≤ N + 1
      · exact Submodule.subset_span (filteredCoordinateSpace_mono I hn ha)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      rw [← hspan m (by omega)] at ha
      obtain ⟨b, hb, z, ⟨c, hc, hcz⟩, hsum⟩ := Submodule.mem_sup.mp ha
      rw [← hsum, ← hcz]
      apply V.add_mem (ih (m + 1) (by omega) hb)
      exact V.smul_mem (⟨l, Algebra.subset_adjoin (Set.mem_singleton l)⟩ : T)
        (ih (m + 1) (by omega) hc)
  have htop : V = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hmem f.totalDegree ⟨f, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl, rfl⟩
  exact ⟨htop ▸ hfg⟩

theorem coordinate_parameter_transcendental {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (l : MvPolynomial σ K ⧸ I)
    {d N M : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (hspan : ∀ n ≥ M, filteredCoordinateSpace I (n + 1) ⊔
      (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
        filteredCoordinateSpace I (n + 2)) : Transcendental K l := by
  intro hl
  let T := Algebra.adjoin K {l}
  let S := MvPolynomial σ K ⧸ I
  let : Module.Finite K T := Algebra.finite_adjoin_simple_of_isIntegral hl.isIntegral
  let : Module.Finite T S := coordinateRing_finite_over_parameter I l hspan
  let : Module.Finite K S := Module.Finite.trans T S
  obtain ⟨m, hm⟩ := exists_nat_gt ((Module.finrank K S : ℤ) - b)
  let n := max N m
  have hnN : N ≤ n := le_max_left _ _
  have hmn : (m : ℤ) ≤ n := by exact_mod_cast (le_max_right N m)
  have hdn : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hb : (Module.finrank K (filteredCoordinateSpace I n) : ℤ) ≤ Module.finrank K S :=
    by exact_mod_cast (Submodule.finrank_le (filteredCoordinateSpace I n))
  rw [hdegree n hnN] at hb
  nlinarith

/-- Original nonexceptional affine components have finite Dedekind
normalization in any realization of their fraction field. -/
theorem nonexceptional_affine_normalization
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (F : Type*) [Field F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    IsDedekindDomain (integralClosure (MvPolynomial (Fin 3) ℚ ⧸ I) F) ∧
      Module.Finite (MvPolynomial (Fin 3) ℚ ⧸ I)
        (integralClosure (MvPolynomial (Fin 3) ℚ ⧸ I) F) := by
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation
    hρ hu hv hne ρ' u' v' A a ha I hf hg
  let l := Ideal.Quotient.mk I (MvPolynomial.X 0)
  let : Module.Finite (Algebra.adjoin ℚ {l}) (MvPolynomial (Fin 3) ℚ ⧸ I) :=
    coordinateRing_finite_over_parameter I l hs
  exact finite_parameter_normalization l
    (coordinate_parameter_transcendental I l hd hdegree hs) F

end
end PierceLengthBound.FixedDividend
