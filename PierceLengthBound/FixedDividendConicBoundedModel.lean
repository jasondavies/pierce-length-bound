/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalParabolicModel
public import PierceLengthBound.FixedDividendRationalOrbit
public import PierceLengthBound.FixedDividendConicCoefficientHeight

/-!
# Bounded integral conic models of actual components

Every actual nonexceptional degree-two component admits a bounded integral
parabolic equation in one of two coordinate orders.

The exact ternary fixed-dividend quadratic has integer numerators over a common
denominator, and the actual seven minor labels give polynomial-height common
numerators for two adjacent rational patterns. A containing plane always has a
nonconstant coordinate pivot, so one of the two plane charts applies.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

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

/-- Six common numerators and their common denominator for the two adjacent
rational patterns. -/
def conicPatternCommon (t : Fin 7 → ℤ) : Fin 7 → ℤ :=
  ![t 1 * t 1, t 3 * t 1, t 4 * t 1, t 2 * t 0,
    t 5 * t 0, t 6 * t 0, t 0 * t 1]

def conicPatternTernary (t : Fin 7 → ℤ) : Fin 6 → ℤ :=
  let w := conicPatternCommon t
  ternaryNumerators (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)

lemma conicPatternCommon_height {t : Fin 7 → ℤ} {X : ℤ}
    (ht : ∀ j, |t j| ≤ X) : ∀ j, |conicPatternCommon t j| ≤ X ^ 2 := by
  have hmul (i j : Fin 7) : |t i * t j| ≤ X ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (ht i) (ht j) (abs_nonneg _) ((abs_nonneg _).trans (ht i))
  intro j
  fin_cases j <;> exact hmul _ _

/-- Actual pattern height `X` gives ternary numerator and common denominator
height at most `12X⁴`. -/
theorem conicPatternTernary_height {t : Fin 7 → ℤ} {X : ℤ}
    (hX : 1 ≤ X) (ht : ∀ j, |t j| ≤ X) :
    |conicPatternCommon t 6| ≤ 12 * X ^ 4 ∧
      ∀ j, |conicPatternTernary t j| ≤ 12 * X ^ 4 := by
  have hw := conicPatternCommon_height ht
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hp := ternaryNumerators_height hX2 (hw 0) (hw 1) (hw 2)
    (hw 3) (hw 4) (hw 5) (hw 6)
  constructor
  · have hh := hw 6
    nlinarith [sq_nonneg (X ^ 2 - 1)]
  · simpa only [conicPatternTernary, ← pow_mul, Nat.reduceMul] using hp

lemma conicPatternCommon_ratios (t : Fin 7 → ℤ) (h0 : t 0 ≠ 0) (h1 : t 1 ≠ 0) :
    let w := conicPatternCommon t
    ![(w 0 : ℚ) / w 6, (w 1 : ℚ) / w 6, (w 2 : ℚ) / w 6,
      (w 3 : ℚ) / w 6, (w 4 : ℚ) / w 6, (w 5 : ℚ) / w 6] =
    ![(t 1 : ℚ) / t 0, (t 3 : ℚ) / t 0, (t 4 : ℚ) / t 0,
      (t 2 : ℚ) / t 1, (t 5 : ℚ) / t 1, (t 6 : ℚ) / t 1] := by
  have h0' : (t 0 : ℚ) ≠ 0 := by exact_mod_cast h0
  have h1' : (t 1 : ℚ) ≠ 0 := by exact_mod_cast h1
  ext j
  fin_cases j <;> simp [conicPatternCommon] <;> field_simp

/-- The common rational coefficients are precisely the actual orbit patterns. -/
lemma conicPatternCommon_orbit {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    let w := conicPatternCommon (theta a b i)
    ![(w 0 : ℚ) / w 6, (w 1 : ℚ) / w 6, (w 2 : ℚ) / w 6,
      (w 3 : ℚ) / w 6, (w 4 : ℚ) / w 6, (w 5 : ℚ) / w 6] =
    ![patternRhoQ a b i, patternUQ a b i, patternVQ a b i,
      patternRhoQ a b (i + 1), patternUQ a b (i + 1), patternVQ a b (i + 1)] := by
  have h0 : theta a b i 0 ≠ 0 := by
    simpa only [theta, Matrix.cons_val_zero] using
      (ne_of_gt (Lz_pos hba (by omega : i + 5 < P a b)))
  have h1 : theta a b i 1 ≠ 0 := by
    simpa only [theta, Matrix.cons_val_one, Matrix.cons_val_zero] using
      (ne_of_gt (Lz_pos hba (by omega : i + 1 + 5 < P a b)))
  simpa [theta, patternRhoQ, patternUQ, patternVQ, Nat.add_assoc] using
    conicPatternCommon_ratios (theta a b i) h0 h1

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

/-- Uniform bounded integral plane model from common rational pattern
numerators. All discriminant and nonvanishing conclusions are proved from the
actual component geometry. -/
theorem nonexceptional_bounded_integer_conic_model
    (r u v r' u' v' D n0 n1 n2 e : ℤ) {M L : ℤ}
    (hM : 1 ≤ M) (hL : 0 ≤ L) (hD0 : D ≠ 0)
    (hr : |r| ≤ M) (hu : |u| ≤ M) (hv : |v| ≤ M)
    (hr' : |r'| ≤ M) (hu' : |u'| ≤ M) (hv' : |v'| ≤ M) (hD : |D| ≤ M)
    (hn0 : |n0| ≤ L) (hn1 : |n1| ≤ L) (hn2 : |n2| ≤ L) (he : |e| ≤ L)
    (hρpos : 0 < (r : ℚ) / D) (hupos : 0 < (u : ℚ) / D)
    (hvneg : (v : ℚ) / D < 0)
    (hne : NonexceptionalPattern (((r : ℚ) / D : ℚ) : ℝ)
      (((u : ℚ) / D : ℚ) : ℝ) (((v : ℚ) / D : ℚ) : ℝ))
    (A a : ℚ) (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) ∈ I)
    (hg : curveEquation ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) A a ∈ I)
    (hn : n0 ≠ 0 ∨ n1 ≠ 0 ∨ n2 ≠ 0)
    (hplane : C (n0 : ℚ) * X 0 + C (n1 : ℚ) * X 1 + C (n2 : ℚ) * X 2 +
      C (e : ℚ) ∈ I)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b)
    (x : Fin 3 → ℚ) (hx : x ∈ coordinateZeroLocus I) :
    ∃ (j k : Fin 3) (c : Fin 6 → ℤ), Function.Bijective ![j, 0, k] ∧
      (![n0, n1, n2] : Fin 3 → ℤ) k ≠ 0 ∧
      (∀ i, |c i| ≤ 10 * (12 * M ^ 2) ^ 2 * L ^ 2) ∧
      c 0 ≠ 0 ∧ (c 1) ^ 2 - 4 * c 0 * c 2 = 0 ∧
      2 * c 1 * c 3 - 4 * c 0 * c 4 ≠ 0 ∧
      ∀ z : Fin 3 → ℤ, (fun i => (z i : ℚ)) ∈ coordinateZeroLocus I →
        conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (z j) (z 0) = 0 := by
  let w := ternaryNumerators r u v r' u' v' D
  have hw : ∀ j, |w j| ≤ 12 * M ^ 2 :=
    ternaryNumerators_height hM hr hu hv hr' hu' hv' hD
  have hB : 1 ≤ 12 * M ^ 2 := by nlinarith
  have hDb : |D| ≤ 12 * M ^ 2 := by nlinarith
  -- Both charts clear the same actual rational ternary coefficients.
  have hrat := ternaryNumerators_rat r u v r' u' v' D hD0
  by_cases hp2 : n2 ≠ 0
  · have hp2q : (n2 : ℚ) ≠ 0 := by exact_mod_cast hp2
    let V := rationalPlaneConicCoefficients ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) n0 n1 n2 e
    have hgeo := rational_nonexceptional_parabolic_model hρpos hupos hvneg hne
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) A a hA ha I hf hg
      n0 n1 n2 e hp2q hplane hdegree x hx
    have hp := integralPlaneConicCoefficients_parabolic
      (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) D n0 n1 n2 e hD0 hp2 V
      (congrFun (congrArg (fun w : Fin 6 → ℚ =>
        planeConicCoefficients (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
          (-(n0 : ℚ) / n2) (-(n1 : ℚ) / n2) (-(e : ℚ) / n2)) hrat).symm)
      hgeo.1 hgeo.2.1 hgeo.2.2.1
    refine ⟨1, 2, _, by decide, hp2, ?_, hp.1, hp.2.1, hp.2.2.1, ?_⟩
    · exact integralPlaneConicCoefficients_height hB hL
        (hw 0) (hw 1) (hw 2) hDb (hw 3) (hw 4) (hw 5) hn0 hn1 hn2 he
    · intro z hz
      exact hp.2.2.2 _ _ (hgeo.2.2.2.2 _ hz)
  · have hnp : (n0 : ℚ) ≠ 0 ∨ (n1 : ℚ) ≠ 0 ∨ (n2 : ℚ) ≠ 0 := by
      exact_mod_cast hn
    have hp1q := (rational_nonexceptional_plane_pivot hρpos hupos hvneg hne
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) A a ha I hf hg
      n0 n1 n2 e hnp hplane (by decide : 0 < 2) hdegree).resolve_right (by
        intro hh
        exact hp2 (by exact_mod_cast hh))
    have hp1 : n1 ≠ 0 := by exact_mod_cast hp1q
    let V := rationalSecondPlaneConicCoefficients
      ((r : ℚ) / D) ((u : ℚ) / D) ((v : ℚ) / D)
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) n0 n1 n2 e
    have hgeo := rational_nonexceptional_second_parabolic_model hρpos hupos hvneg hne
      ((r' : ℚ) / D) ((u' : ℚ) / D) ((v' : ℚ) / D) A a hA ha I hf hg
      n0 n1 n2 e hp1q hplane hdegree x hx
    have hp := integralPlaneConicCoefficients_parabolic
      (w 0) (w 2) (w 1) (w 3) (w 5) (w 4) D n0 n2 n1 e hD0 hp1 V
      (congrFun (congrArg (fun w : Fin 6 → ℚ =>
        planeConicCoefficients (w 0) (w 2) (w 1) (w 3) (w 5) (w 4)
          (-(n0 : ℚ) / n1) (-(n2 : ℚ) / n1) (-(e : ℚ) / n1)) hrat).symm)
      hgeo.1 hgeo.2.1 hgeo.2.2.1
    refine ⟨2, 1, _, by decide, hp1, ?_, hp.1, hp.2.1, hp.2.2.1, ?_⟩
    · exact integralPlaneConicCoefficients_height hB hL
        (hw 0) (hw 2) (hw 1) hDb (hw 3) (hw 5) (hw 4) hn0 hn2 hn1 he
    · intro z hz
      exact hp.2.2.2 _ _ (hgeo.2.2.2.2 _ hz)

end
end PierceLengthBound.FixedDividend
