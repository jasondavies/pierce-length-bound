/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendDegreeOne
public import PierceLengthBound.FixedDividendCriticalGrowth
public import PierceLengthBound.FixedDividendHilbertLinearity
public import PierceLengthBound.FixedDividendTranscendentalCoordinate

/-!
# Prime components with a rational point

A base-field-valued point replaces algebraic closedness in the algebraicity and
critical-growth arguments. Thus the geometric Hilbert-degree interface can be
used directly over the rationals, without a complex component-descent assumption.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- An algebraic element detected by a base-field-valued point is scalar. -/
lemma algebraic_eq_scalar_of_point {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (φ : A →ₐ[K] K) {y : A} (hy : IsAlgebraic K y) :
    algebraMap K A (φ y) = y := by
  have hi := hy.isIntegral
  have hroot : (minpoly K y).IsRoot (φ y) := by
    have he := Polynomial.aeval_algHom_apply φ y (minpoly K y)
    rw [minpoly.aeval, map_zero] at he
    simpa only [Polynomial.IsRoot, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using he
  have hassoc := (Polynomial.irreducible_X_sub_C (φ y)).associated_of_dvd
    (minpoly.irreducible hi) (Polynomial.dvd_iff_isRoot.mpr hroot)
  have he : Polynomial.aeval y (Polynomial.X - Polynomial.C (φ y)) = 0 := by
    obtain ⟨r, hr⟩ := hassoc.symm.dvd
    rw [hr, map_mul, minpoly.aeval, zero_mul]
  simpa using (sub_eq_zero.mp (by simpa using he)).symm

/-- Evaluation at a rational point descends to its prime coordinate ring. -/
def coordinatePoint {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ coordinateZeroLocus p) :
    (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
  Ideal.Quotient.liftₐ p (MvPolynomial.aeval z) (by
    intro f hf
    simpa only [MvPolynomial.aeval_eq_eval] using hz f hf)

@[simp] lemma coordinatePoint_mk {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ coordinateZeroLocus p)
    (f : MvPolynomial σ K) :
    coordinatePoint p z hz ((Ideal.Quotient.mk p) f) = MvPolynomial.eval z f := by
  simp [coordinatePoint, Ideal.Quotient.liftₐ_apply]

/-- A height-two prime in three variables containing a rational point retains a
transcendental coordinate over its base field. -/
theorem height_two_transcendental_coordinate_of_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (z : Fin 3 → K) (hz : z ∈ coordinateZeroLocus p) :
    ∃ j : Fin 3, Transcendental K ((Ideal.Quotient.mk p) (X j)) := by
  classical
  by_contra h
  push Not at h
  have ha (j : Fin 3) : IsAlgebraic K ((Ideal.Quotient.mk p) (X j)) := by
    simpa only [Transcendental, not_not] using h j
  have hc (j : Fin 3) : algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (z j) =
      (Ideal.Quotient.mk p) (X j) := by
    simpa using algebraic_eq_scalar_of_point (coordinatePoint p z hz) (ha j)
  have hcomp : (Ideal.Quotient.mk p).comp (partialCoordinateEval z 3) = Ideal.Quotient.mk p := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp only [RingHom.comp_apply, partialCoordinateEval_X, ite_eq_left j.isLt]
      exact hc j
  have hle : RingHom.ker (partialCoordinateEval z 3) ≤ p := by
    intro f hf
    change partialCoordinateEval z 3 f = 0 at hf
    have he := congrArg (fun φ : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K ⧸ p => φ f) hcomp
    change (Ideal.Quotient.mk p) (partialCoordinateEval z 3 f) = _ at he
    rw [hf, map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  have hd := (three_le_height_coordinate_kernel z).trans (Ideal.height_mono hle)
  rw [hp] at hd
  norm_num at hd

/-- Critical growth over an arbitrary field, provided that the coordinate ring
has a base-field-valued point. -/
theorem affine_of_critical_growth_of_point {K A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] (φ : A →ₐ[K] K)
    (U V : Submodule K A) [Module.Finite K U] [Module.Finite K V]
    (hUV : U ≤ V) (hUone : (1 : A) ∈ U)
    (hd : Module.finrank K V = Module.finrank K U + 1)
    {x y : A} (hx : Transcendental K x)
    (hxU : ∀ u ∈ U, x * u ∈ V) (hyU : ∀ u ∈ U, y * u ∈ V) :
    ∃ c d : K, y = c • x + algebraMap K A d := by
  obtain ⟨c, hc⟩ := algebraic_difference_of_critical_growth U V hUV hUone hd hx hxU hyU
  refine ⟨c, φ (y - c • x), ?_⟩
  rw [algebraic_eq_scalar_of_point φ hc]
  abel

/-- A prime component containing a base-field point has a positive eventual
Hilbert degree, bounded by any proved linear filtration-growth bound. -/
theorem height_two_degree_exists_of_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (z : Fin 3 → K) (hz : z ∈ coordinateZeroLocus p) (C : ℕ)
    (hbound : ∀ N ≥ 14, Module.finrank K (filteredCoordinateSpace p N) ≤ C * (N + 2)) :
    ∃ d, 0 < d ∧ d ≤ C ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = (d : ℤ) * n + c := by
  obtain ⟨d, hd, N, c, hlinear⟩ := filteredCoordinateSpace_eventually_linear p C hbound
  obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point p hp z hz
  have hpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hlo := transcendental_coordinate_filtered_lower p hj (N + c.natAbs)
    have hhi := hlinear (N + c.natAbs) (by omega)
    rw [hd0] at hhi
    simp only [Nat.cast_zero, zero_mul, zero_add] at hhi
    have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
    have hlo' : ((N + c.natAbs + 1 : ℕ) : ℤ) ≤
        (Module.finrank K (filteredCoordinateSpace p (N + c.natAbs)) : ℤ) := by exact_mod_cast hlo
    push_cast at hlo'
    omega
  exact ⟨d, hpos, hd, N, c, hlinear⟩

/-- A degree-one prime curve containing a base-field point has affine coordinate
formulas over that same field. In particular this holds directly over `ℚ`. -/
theorem degree_one_coordinates_affine_of_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = n + b)
    (z : Fin 3 → K) (hz : z ∈ coordinateZeroLocus p) :
    ∃ (j : Fin 3) (c d : Fin 3 → K), c j ≠ 0 ∧
      Transcendental K ((Ideal.Quotient.mk p) (X j)) ∧ ∀ k,
      (Ideal.Quotient.mk p) (X k) =
        c k • (Ideal.Quotient.mk p) (X j) + algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (d k) := by
  obtain ⟨N, b, hN⟩ := hdegree
  obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point p hp z hz
  have hdim : Module.finrank K (filteredCoordinateSpace p (N + 1)) =
      Module.finrank K (filteredCoordinateSpace p N) + 1 := by
    have h0 := hN N le_rfl
    have h1 := hN (N + 1) (by omega)
    omega
  have hUone : (1 : MvPolynomial (Fin 3) K ⧸ p) ∈ filteredCoordinateSpace p N := by
    apply Submodule.mem_map.mpr
    refine ⟨1, ?_, by simp⟩
    rw [mem_restrictTotalDegree, totalDegree_one]
    omega
  have hex (k : Fin 3) : ∃ c d : K,
      (Ideal.Quotient.mk p) (X k) = c • (Ideal.Quotient.mk p) (X j) +
        algebraMap K (MvPolynomial (Fin 3) K ⧸ p) d :=
    affine_of_critical_growth_of_point (coordinatePoint p z hz)
      (filteredCoordinateSpace p N) (filteredCoordinateSpace p (N + 1))
      (filteredCoordinateSpace_mono p (by omega)) hUone hdim hj
      (fun _ hu => coordinate_mul_filtered_mem p j N hu)
      (fun _ hu => coordinate_mul_filtered_mem p k N hu)
  choose c d hcd using hex
  have hcj : c j ≠ 0 := by
    intro hc
    have he := hcd j
    rw [hc, zero_smul, zero_add] at he
    apply hj
    rw [he]
    exact isAlgebraic_algebraMap (d j)
  exact ⟨j, c, d, hcj, hj, hcd⟩

/-- Degree-one line containment over an arbitrary field with a rational point. -/
theorem degree_one_line_through_rational_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = n + b)
    (z : Fin 3 → K) (hz : z ∈ coordinateZeroLocus p) :
    ∃ c : Fin 3 → K, (∃ j, c j ≠ 0) ∧ ∀ f ∈ p,
      MvPolynomial.aeval
        (fun k => Polynomial.C (z k) + Polynomial.C (c k) * Polynomial.X) f = 0 := by
  obtain ⟨j, c, d, hcj, hj, hcd⟩ := degree_one_coordinates_affine_of_point p hp hdegree z hz
  exact line_through_point_of_affine_coordinates p j c d hcj hj hcd z hz

end
end PierceLengthBound.FixedDividend
