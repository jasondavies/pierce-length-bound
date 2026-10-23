/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftCoordinateSystem

/-! Actual quotient reconstruction and its monic quartic normalization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

def orbitQuotientNumeratorQ (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  orbitCurveCofactorsQ a b i 1 - orbitCurveCofactorsQ a b i 2

def orbitQuotientDenominatorQ (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  orbitCurveCofactorsQ a b i 1 - orbitCurveCofactorsQ a b i 0

theorem orbitQuotient_polynomial_degrees (a b i : ℕ) :
    (orbitQuotientNumeratorQ a b i).totalDegree ≤ 40 ∧
      (orbitQuotientDenominatorQ a b i).totalDegree ≤ 40 := by
  constructor <;> exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le (curveMomentCofactors_totalDegree _ _ _ _ _ _ _)
      (curveMomentCofactors_totalDegree _ _ _ _ _ _ _))

/-- The rational quotient reconstructed from the universal cofactors agrees
with the actual quotient, with a nonzero denominator. -/
theorem orbitQuotient_evaluation {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    MvPolynomial.eval (orbitFreeNodesQ a b i) (orbitQuotientDenominatorQ a b i) ≠ 0 ∧
      (qq a b i : ℚ) =
        MvPolynomial.eval (orbitFreeNodesQ a b i) (orbitQuotientNumeratorQ a b i) /
          MvPolynomial.eval (orbitFreeNodesQ a b i) (orbitQuotientDenominatorQ a b i) := by
  obtain ⟨_, hd, _, hq, _⟩ := orbitMomentSystem_reconstruction hba hi
  have he (j : Fin 9) : (algebraMap ℚ ℝ)
      (MvPolynomial.eval (orbitFreeNodesQ a b i) (orbitCurveCofactorsQ a b i j)) =
      momentCofactors (orbitMomentSystem a b i) j := orbit_eval_curveCofactorsQ_cast hba hi j
  constructor
  · intro hz
    apply hd
    have h := congrArg (algebraMap ℚ ℝ) hz
    simpa only [orbitQuotientDenominatorQ, map_sub, he, map_zero] using h
  · apply (algebraMap ℚ ℝ).injective
    simpa only [orbitQuotientNumeratorQ, orbitQuotientDenominatorQ, map_sub, map_div₀,
      he, map_natCast] using hq

/-- Homogeneous evaluation of the first monic Newton quartic at `-n/d`.
The expression remains polynomial even where the denominator vanishes. -/
def clearedNewtonQuartic {R : Type*} [CommRing R]
    (c : Fin 4 → R) (s : Fin 3 → R) (n d : R) : R :=
  c 0 * d ^ 4 - c 1 * n * d ^ 3 + c 2 * n * (n + s 0 * d) * d ^ 2 -
    c 3 * n * (n + s 0 * d) * (n + s 1 * d) * d +
    n * (n + s 0 * d) * (n + s 1 * d) * (n + s 2 * d)

lemma clearedNewtonQuartic_div {K : Type*} [Field K]
    (c : Fin 4 → K) (s : Fin 3 → K) (n d : K) (hd : d ≠ 0) :
    clearedNewtonQuartic c s n d =
      (firstNewtonQuartic c ![s 0, s 1, s 2, 0]).eval (-(n / d)) * d ^ 4 := by
  simp only [clearedNewtonQuartic, firstNewtonQuartic, eval_add, eval_mul, eval_sub,
    eval_C, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

/-- Scalar normalization of the explicit Newton form matches the previously
proved integer quartic identity. -/
lemma newtonQuartic_eval_cast (A B U V k0 k1 k2 q : ℤ) (hA : A ≠ 0) :
    (A : ℚ) * (firstNewtonQuartic
      (fun j : Fin 4 => coeffs ((B : ℚ) / A) ((U : ℚ) / A) ((V : ℚ) / A) j.castSucc)
      ![(k0 : ℚ), k0 + k1, k0 + k1 + k2, 0]).eval (-(q : ℚ)) =
      (quart (-B) U V A k0 k1 k2 q : ℚ) := by
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  simp only [firstNewtonQuartic, eval_add, eval_mul, eval_sub, eval_C, eval_X,
    coeffs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, quart]
  push_cast
  field_simp
  ring

/-- The actual supported orbit satisfies the monic normalization over `ℚ`. -/
theorem orbit_newton_normalization {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    (Lz a b i : ℚ) * (firstNewtonQuartic
      (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
        (patternVQ a b i) j.castSucc)
      ![orbitFreeNodesQ a b i 0, orbitFreeNodesQ a b i 1,
        orbitFreeNodesQ a b i 2, 0]).eval (-(qq a b i : ℚ)) =
      (a : ℚ) * muH4 (kq a b i : ℚ) (kq a b (i + 1) : ℚ)
        (kq a b (i + 2) : ℚ) (kq a b (i + 3) : ℚ) (kq a b (i + 4) : ℚ) := by
  have hA : Lz a b i ≠ 0 := by have := Lz_pos hba (by omega : i + 5 < P a b); omega
  have hs : ![orbitFreeNodesQ a b i 0, orbitFreeNodesQ a b i 1,
        orbitFreeNodesQ a b i 2, (0 : ℚ)] =
      ![(kq a b i : ℚ), (kq a b i : ℚ) + kq a b (i + 1),
        (kq a b i : ℚ) + kq a b (i + 1) + kq a b (i + 2), 0] := by
    ext j
    fin_cases j <;> simp [orbitFreeNodesQ, kq, Nat.add_assoc]
  rw [hs]
  change (Lz a b i : ℚ) * (firstNewtonQuartic
    (fun j : Fin 4 => coeffs ((Lz a b (i + 1) : ℚ) / Lz a b i)
      ((U1z a b i : ℚ) / Lz a b i) ((U2z a b i : ℚ) / Lz a b i) j.castSucc) _).eval _ = _
  rw [show -(qq a b i : ℚ) = -((qq a b i : ℤ) : ℚ) by norm_cast,
    newtonQuartic_eval_cast _ _ _ _ _ _ _ _ hA]
  have h := congrArg (Int.castRingHom ℚ) (mult_at (a := a) (b := b) (i := i) (by omega))
  simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast, muH4, Int.cast_add,
    Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using h

/-- Ring homomorphisms preserve the raw fourth Hankel expression. -/
lemma map_muH4 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (k0 k1 k2 k3 k4 : R) :
    f (muH4 k0 k1 k2 k3 k4) = muH4 (f k0) (f k1) (f k2) (f k3) (f k4) := by
  simp only [muH4, map_add, map_sub, map_mul, map_pow, map_ofNat]

lemma map_lineGaps {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (ρ u v ρ' u' v' x y z : R) (j : Fin 5) :
    f (lineGaps ρ u v ρ' u' v' x y z j) =
      lineGaps (f ρ) (f u) (f v) (f ρ') (f u') (f v') (f x) (f y) (f z) j := by
  fin_cases j <;> simp [lineGaps, fourthNode]

lemma orbit_rational_lineGaps {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b)
    (j : Fin 5) :
    lineGaps (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (orbitFreeNodesQ a b i 0) (orbitFreeNodesQ a b i 1) (orbitFreeNodesQ a b i 2) j =
        (kq a b (i + j.val) : ℚ) := by
  apply (algebraMap ℚ ℝ).injective
  rw [map_lineGaps]
  change lineGaps (patternRhoQ a b i : ℝ) (patternUQ a b i : ℝ) (patternVQ a b i : ℝ)
      (patternRhoQ a b (i + 1) : ℝ) (patternUQ a b (i + 1) : ℝ)
      (patternVQ a b (i + 1) : ℝ) (orbitFreeNodesQ a b i 0 : ℝ)
      (orbitFreeNodesQ a b i 1 : ℝ) (orbitFreeNodesQ a b i 2 : ℝ) j = _
  simp only [patternRhoQ_cast, patternUQ_cast, patternVQ_cast, orbitFreeNodesQ_cast]
  change lineGaps _ _ _ _ _ _ (pt a b i 1) (pt a b i 2) (pt a b i 3) j = _
  rw [orbit_lineGaps hba hi]
  simp [kk, kq]

lemma polynomial_substitution_eval {K : Type*} [CommRing K]
    (z : Fin 3 → Polynomial K) (f : MvPolynomial (Fin 3) K) (t : K) :
    (MvPolynomial.aeval z f).eval t = MvPolynomial.eval (fun j => (z j).eval t) f := by
  have he : (Polynomial.evalRingHom t).comp (MvPolynomial.aeval z).toRingHom =
      MvPolynomial.eval (fun j => (z j).eval t) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro j; simp
  exact congrArg (fun h : MvPolynomial (Fin 3) K →+* K => h f) he

end
end PierceLengthBound.FixedDividend
