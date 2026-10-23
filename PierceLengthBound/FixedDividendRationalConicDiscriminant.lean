/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalChartResultant
public import PierceLengthBound.FixedDividendConicInfinity
public import PierceLengthBound.FixedDividendLocalizationParity
public import PierceLengthBound.FixedDividendLocalParity
public import Mathlib.RingTheory.Localization.FractionRing
public import PierceLengthBound.FixedDividendConicDiscriminant

/-!
# The actual nonexceptional conic has parabolic leading form

For any containing rational plane whose third coefficient is nonzero, restriction
of the actual leading quadratic to that plane has zero binary discriminant.
The proof uses the actual rational infinity section and its nonzero nilpotent
norm residue; no geometric classification premise is assumed.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma affine_plane_top_component {K : Type*} [Field K] (n0 n1 n2 e : K) :
    homogeneousComponent 1 (C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e :
      MvPolynomial (Fin 3) K) = C n0 * X 0 + C n1 * X 1 + C n2 * X 2 := by
  have hX (j : Fin 3) : homogeneousComponent 1 (X j : MvPolynomial (Fin 3) K) = X j :=
    homogeneousComponent_eq_self (isHomogeneous_X K j)
  have hC : homogeneousComponent 1 (C e : MvPolynomial (Fin 3) K) = 0 :=
    homogeneousComponent_eq_zero 1 _ (by simp)
  simp only [map_add, homogeneousComponent_C_mul, hX, hC, add_zero]

/-- A nonscalar normalized node prevents an additional affine linear equation
with nonzero coefficient on that node. -/
lemma chart_no_affine_linear_relation {K F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : ι l ≠ 0)
    (hz0 : Ideal.Quotient.mk (chartInfinityIdeal I ι l) (chartNode I ι l 0) = 1)
    (hns : ∀ c : K, Ideal.Quotient.mk (chartInfinityIdeal I ι l) (chartNode I ι l 1) ≠
      algebraMap K _ c) :
    ∀ a0 a1 c : K, a1 ≠ 0 → C a0 * X 0 + C a1 * X 1 + C c ∉ I := by
  let q := Ideal.Quotient.mkₐ K (chartInfinityIdeal I ι l)
  let z := fun j => q (chartNode I ι l j)
  have hquot (p : Polynomial (MvPolynomial (Fin 3) K)) :
      q (chartHomogeneousMap I ι l p) = MvPolynomial.aeval z (p.eval 0) :=
    chart_infinity_evaluation I ι l p
  intro a0 a1 c ha1 hline
  have hline' : C a0 * X 0 + C a1 * X 1 + C (0 : K) * X 2 + C c ∈ I := by
    simpa using hline
  have hld : (C a0 * X 0 + C a1 * X 1 + C (0 : K) * X 2 + C c :
      MvPolynomial (Fin 3) K).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (linear_form_degree_le _ _ _) (by simp))
  have hh := chartHomogeneousMap_homogenize_eq_zero I ι l hl hline' hld
  have ht := congrArg q hh
  rw [hquot, curveHomogenize_at_infinity, radialMap_coeff_eq_homogeneousComponent,
    affine_plane_top_component, map_zero] at ht
  have hz0' : z 0 = 1 := hz0
  have hrel : algebraMap K _ a0 + algebraMap K _ a1 * z 1 = 0 := by
    simpa only [map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      map_zero, zero_mul, add_zero, hz0', mul_one] using ht
  exact hns (-a0 / a1) (algebra_scalar_of_linear_eq ha1 hrel)

set_option maxHeartbeats 800000 in
-- This proof uses about 475k heartbeats (`#count_heartbeats`).
/-- The actual plane model has zero leading discriminant. -/
theorem rational_nonexceptional_conic_plane_geometry
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    (n0 n1 n2 e : ℚ) (hn2 : n2 ≠ 0)
    (hplane : C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e ∈ I)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b) :
    let k := -n0 / n2
    let m := -n1 / n2
    let α := (u - v) + (v - 1) * m ^ 2 + ((u - v) + (v - 1) * m) ^ 2
    let β := 2 * (v - 1) * k * m +
      2 * (-ρ - u + (v - 1) * k) * ((u - v) + (v - 1) * m)
    let γ := (-ρ - u) + (v - 1) * k ^ 2 + (-ρ - u + (v - 1) * k) ^ 2
    α ≠ 0 ∧ β ^ 2 - 4 * α * γ = 0 ∧
      ∀ a0 a1 c : ℚ, a1 ≠ 0 → C a0 * X 0 + C a1 * X 1 + C c ∉ I := by
  let B := MvPolynomial (Fin 3) ℚ ⧸ I
  let F := FractionRing B
  let ι : B →ₐ[ℚ] F := IsScalarTower.toAlgHom ℚ B F
  have hι : Function.Injective ι := IsFractionRing.injective B F
  have hd : 0 < (2 : ℕ) := by decide
  let l := Ideal.Quotient.mk I (X 0)
  let R := projectiveChart I ι l
  let w : R := chartInfinityCoordinate I ι l
  let φ := chartHomogeneousMap I ι l
  let r : R := φ (curveHomogenize 10 (curveResultant (ρ : ℚ) u v ρ' u' v'))
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation
    hρ hu hv hne ρ' u' v' A a ha I hf hg
  have hl : ι l ≠ 0 := by
    intro hh
    apply first_node_ne_zero_of_generation I hd hdegree hs
    exact hι (by simpa using hh)
  obtain ⟨hfin, hdim⟩ := rational_nonexceptional_chart_infinity_dimension hρ hu hv hne
    ρ' u' v' A a ha I hf hg ι hι hd hdegree
  have hfin' : Module.Finite ℚ (R ⧸ Ideal.span {w}) := hfin
  have hdim' : Module.finrank ℚ (R ⧸ Ideal.span {w}) = 2 := hdim
  have hr : IsUnit (Ideal.Quotient.mk (Ideal.span {w}) r) :=
    rational_nonexceptional_chart_resultant_unit hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
  have hw : w ≠ 0 := by
    intro hh
    have ht := congrArg (fun x : R => (x : F)) hh
    change (ι l)⁻¹ = 0 at ht
    exact (inv_ne_zero hl) ht
  have he := chartHomogeneousMap_homogenize_eq_zero I ι l hl hg
    (curveEquation_degree_le _ _ _ _ _ _ _ _)
  have huC (c : ℚ) (hc : c ≠ 0) : IsUnit (φ (Polynomial.C (C c))) :=
    ((isUnit_iff_ne_zero.mpr hc).map (Polynomial.C.comp (C : ℚ →+* MvPolynomial (Fin 3) ℚ))).map φ
  have heq : φ (Polynomial.C (C A)) * w ^ 2 * r =
      φ (Polynomial.C (C a)) *
        φ (curveHomogenize 3 (curveNorm (ρ : ℚ) u v ρ' u' v')) ^ 4 := by
    simpa only [φ, chartHomogeneousMap_X, w, r] using
      map_curveEquation_homogenize φ (ρ : ℚ) u v ρ' u' v' A a he
  let S := R ⧸ Ideal.span {w}
  let q := Ideal.Quotient.mkₐ ℚ (Ideal.span {w})
  have : Nontrivial S := Module.nontrivial_of_finrank_pos (R := ℚ) (by
    change 0 < Module.finrank ℚ (R ⧸ Ideal.span {w})
    rw [hdim']
    decide)
  have hnorm := square_fourth_norm_residue (K := ℚ) (huC A hA) (huC a ha) hw hr heq
  have hex : Nonempty (S →ₐ[ℚ] ℂ) := by
    by_contra h
    exact not_isUnit_zero
      (finite_algebra_isUnit_of_closed_points (K := ℚ) (L := ℂ) (R := S) (0 : S)
        (fun ψ => False.elim (h ⟨ψ⟩)))
  obtain ⟨ψ⟩ := hex
  let z : Fin 3 → S := fun j => q (chartNode I ι l j)
  have hz0 : z 0 = 1 := by
    change q (chartNode I ι (Ideal.Quotient.mk I (X 0)) 0) = 1
    rw [chartNode_first_eq_one I ι hl, map_one]
  have hlmem : l ∈ filteredCoordinateSpace I 1 :=
    ⟨X 0, by simp [mem_restrictTotalDegree], rfl⟩
  have hgen : Function.Surjective (MvPolynomial.aeval (R := ℚ) z) :=
    chart_nodes_generate_infinity I ι l hlmem hl
  have hquot (p : Polynomial (MvPolynomial (Fin 3) ℚ)) :
      q (chartHomogeneousMap I ι l p) = MvPolynomial.aeval z (p.eval 0) :=
    chart_infinity_evaluation I ι l p
  have hq : MvPolynomial.aeval z
      (leadingQuadratic (-ρ - u) (u - v) (v - 1)) = 0 := by
    have hh := chartHomogeneousMap_homogenize_eq_zero I ι l hl hf
      (curveQuadratic_degree_le_two _ _ _ _ _ _)
    have ht := congrArg q hh
    rw [hquot, curveQuadratic_at_infinity, map_zero] at ht
    exact ht
  have hpld : (C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e :
      MvPolynomial (Fin 3) ℚ).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (linear_form_degree_le _ _ _) (by simp))
  have hp : algebraMap ℚ S n0 * z 0 + algebraMap ℚ S n1 * z 1 +
      algebraMap ℚ S n2 * z 2 = 0 := by
    have hh := chartHomogeneousMap_homogenize_eq_zero I ι l hl hplane hpld
    have ht := congrArg q hh
    rw [hquot, curveHomogenize_at_infinity,
      radialMap_coeff_eq_homogeneousComponent, affine_plane_top_component, map_zero] at ht
    simpa only [map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X] using ht
  have hcoeff := section_plane_quadratic_coefficients hdim' ψ hnorm.1 hnorm.2
    z hz0 hgen hn2 (by linarith) (by linarith) (by linarith) (by linarith) hp hq
  refine ⟨hcoeff.1, hcoeff.2, ?_⟩
  exact chart_no_affine_linear_relation I ι l hl hz0
    (section_plane_remaining_node_nonscalar hdim' z hz0 hgen hn2 hp)

/-- Nonzero square coefficient and zero discriminant of the actual plane model. -/
theorem rational_nonexceptional_conic_plane_coefficients
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    (n0 n1 n2 e : ℚ) (hn2 : n2 ≠ 0)
    (hplane : C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e ∈ I)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b) :
    let k := -n0 / n2
    let m := -n1 / n2
    let α := (u - v) + (v - 1) * m ^ 2 + ((u - v) + (v - 1) * m) ^ 2
    let β := 2 * (v - 1) * k * m +
      2 * (-ρ - u + (v - 1) * k) * ((u - v) + (v - 1) * m)
    let γ := (-ρ - u) + (v - 1) * k ^ 2 + (-ρ - u + (v - 1) * k) ^ 2
    α ≠ 0 ∧ β ^ 2 - 4 * α * γ = 0 := by
  have h := rational_nonexceptional_conic_plane_geometry hρ hu hv hne
    ρ' u' v' A a hA ha I hf hg n0 n1 n2 e hn2 hplane hdegree
  exact ⟨h.1, h.2.1⟩

/-- The discriminant-only form of the actual plane coefficient theorem. -/
theorem rational_nonexceptional_conic_plane_discriminant
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    (n0 n1 n2 e : ℚ) (hn2 : n2 ≠ 0)
    (hplane : C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e ∈ I)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b) :
    let k := -n0 / n2
    let m := -n1 / n2
    let α := (u - v) + (v - 1) * m ^ 2 + ((u - v) + (v - 1) * m) ^ 2
    let β := 2 * (v - 1) * k * m +
      2 * (-ρ - u + (v - 1) * k) * ((u - v) + (v - 1) * m)
    let γ := (-ρ - u) + (v - 1) * k ^ 2 + (-ρ - u + (v - 1) * k) ^ 2
    β ^ 2 - 4 * α * γ = 0 := by
  exact (rational_nonexceptional_conic_plane_coefficients hρ hu hv hne
    ρ' u' v' A a hA ha I hf hg n0 n1 n2 e hn2 hplane hdegree).2

end
end PierceLengthBound.FixedDividend
