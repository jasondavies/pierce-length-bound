/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveBarycentric
public import PierceLengthBound.BranchSieveReconstruction
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! An explicit polynomial branch equation that commutes with every parameter
specialization. The elimination uses only the sextic location equation, its
linear subresultant, and the quadratic sign identity. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- The cleared Vandermonde numerator, with reconstruction denominator cubed. -/
def branchDeltaNumerator {R : Type*} [CommRing R] (c1 c2 c3 : R) : R[X] :=
  let D := branchLocationDenominator c1 c2 c3
  let N := branchLocationNumerator c1 c2 c3
  X * (-N) * (X - 1) * (-N - D) * (-N - X * D)

/-- A polynomial in the location variable with coefficients polynomial in the
branch label. Its zeros impose the quadratic sign relation. -/
def branchLabelEliminand {R : Type*} [CommRing R] (a A c c1 c2 c3 : R) : (R[X])[X] :=
  C (C A) * ((branchLocationDenominator c1 c2 c3).map C) ^ 3 * (C X - X) ^ 2 -
    C (C (c ^ 2 * a)) * (branchDeltaNumerator c1 c2 c3).map C

/-- The explicit degree-twelve candidate before normalizing its leading
coefficient. Its coefficients are universal polynomials in all six parameters. -/
def branchResultantLabel {R : Type*} [CommRing R] (a A c c1 c2 c3 : R) : R[X] :=
  ((branchLocationSextic c1 c2 c3).map C).resultant
    (branchLabelEliminand a A c c1 c2 c3) 6 11

lemma branchLocationDenominator_natDegree_le {R : Type*} [CommRing R] (c1 c2 c3 : R) :
    (branchLocationDenominator c1 c2 c3).natDegree ≤ 2 := by
  unfold branchLocationDenominator
  compute_degree

lemma branchLocationNumerator_natDegree_le {R : Type*} [CommRing R] (c1 c2 c3 : R) :
    (branchLocationNumerator c1 c2 c3).natDegree ≤ 3 := by
  unfold branchLocationNumerator
  compute_degree

lemma branchDeltaNumerator_natDegree_le {R : Type*} [CommRing R] (c1 c2 c3 : R) :
    (branchDeltaNumerator c1 c2 c3).natDegree ≤ 11 := by
  let D := branchLocationDenominator c1 c2 c3
  let N := branchLocationNumerator c1 c2 c3
  have hD : D.natDegree ≤ 2 := branchLocationDenominator_natDegree_le _ _ _
  have hN : N.natDegree ≤ 3 := branchLocationNumerator_natDegree_le _ _ _
  have hn : (-N).natDegree ≤ 3 := by simpa using hN
  have h₁ : (X - (1 : R[X])).natDegree ≤ 1 := by compute_degree
  have h₂ : (-N - D).natDegree ≤ 3 := (natDegree_sub_le _ _).trans (max_le hn (hD.trans (by omega)))
  have h₃ : (-N - X * D).natDegree ≤ 3 := (natDegree_sub_le _ _).trans (max_le hn
    (natDegree_mul_le.trans (Nat.add_le_add natDegree_X_le hD)))
  change (X * (-N) * (X - 1) * (-N - D) * (-N - X * D)).natDegree ≤ 11
  exact natDegree_mul_le.trans (by
    have h₄ : (X * (-N)).natDegree ≤ 4 := natDegree_mul_le.trans
      (Nat.add_le_add natDegree_X_le hn)
    have h₅ : (X * (-N) * (X - 1)).natDegree ≤ 5 :=
      natDegree_mul_le.trans (Nat.add_le_add h₄ h₁)
    have h₆ : (X * (-N) * (X - 1) * (-N - D)).natDegree ≤ 8 :=
      natDegree_mul_le.trans (Nat.add_le_add h₅ h₂)
    exact Nat.add_le_add h₆ h₃)

lemma branchLabelEliminand_natDegree_le {R : Type*} [CommRing R] (a A c c1 c2 c3 : R) :
    (branchLabelEliminand a A c c1 c2 c3).natDegree ≤ 11 := by
  unfold branchLabelEliminand branchDeltaNumerator branchLocationDenominator branchLocationNumerator
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_one]
  compute_degree

lemma branchLocationDenominator_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c1 c2 c3 : R) :
    (branchLocationDenominator c1 c2 c3).map φ =
      branchLocationDenominator (φ c1) (φ c2) (φ c3) := by
  simp [branchLocationDenominator, map_ofNat]

lemma branchLocationNumerator_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c1 c2 c3 : R) :
    (branchLocationNumerator c1 c2 c3).map φ =
      branchLocationNumerator (φ c1) (φ c2) (φ c3) := by
  simp [branchLocationNumerator, map_ofNat]

lemma branchDeltaNumerator_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c1 c2 c3 : R) :
    (branchDeltaNumerator c1 c2 c3).map φ = branchDeltaNumerator (φ c1) (φ c2) (φ c3) := by
  simp only [branchDeltaNumerator, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_neg, Polynomial.map_X, Polynomial.map_one,
    branchLocationDenominator_map, branchLocationNumerator_map]

lemma branchLabelEliminand_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a A c c1 c2 c3 : R) :
    (branchLabelEliminand a A c c1 c2 c3).map (Polynomial.mapRingHom φ) =
      branchLabelEliminand (φ a) (φ A) (φ c) (φ c1) (φ c2) (φ c3) := by
  have hm (p : R[X]) : (p.map C).map (Polynomial.mapRingHom φ) = (p.map φ).map C := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext r
    simp
  simp only [branchLabelEliminand, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom,
    Polynomial.map_C, Polynomial.map_X, map_mul, map_pow,
    branchLocationDenominator_map, branchDeltaNumerator_map]

/-- No injectivity is required: the explicit resultant family specializes at
arbitrary parameter values. -/
theorem branchResultantLabel_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a A c c1 c2 c3 : R) :
    (branchResultantLabel a A c c1 c2 c3).map φ =
      branchResultantLabel (φ a) (φ A) (φ c) (φ c1) (φ c2) (φ c3) := by
  have hm (p : R[X]) : (p.map C).map (Polynomial.mapRingHom φ) = (p.map φ).map C := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext r
    simp
  rw [branchResultantLabel, ← Polynomial.coe_mapRingHom, ← resultant_map_map,
    hm, branchLocationSextic_map, branchLabelEliminand_map]
  rfl

/-- A common root forces the bounded-degree resultant to vanish, including
specializations at which the polynomial degrees fall. -/
lemma branch_resultant_zero_of_common_root {R : Type*} [CommRing R]
    (f g : R[X]) (m n : ℕ) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (t : R) (hft : f.eval t = 0) (hgt : g.eval t = 0) :
    f.resultant g m n = 0 := by
  obtain ⟨p, q, _, _, he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  have hh := congrArg (Polynomial.eval t) he
  simpa only [eval_add, eval_mul, eval_C, hft, hgt, zero_mul, zero_add] using hh.symm

/-- The linear reconstruction equation clears exactly three Vandermonde
factors, so no fourth power of its denominator is introduced. -/
lemma branchDeltaNumerator_eval {R : Type*} [CommRing R] (c1 c2 c3 t y : R)
    (hy : (branchLocationDenominator c1 c2 c3).eval t * y +
      (branchLocationNumerator c1 c2 c3).eval t = 0) :
    (branchDeltaNumerator c1 c2 c3).eval t =
      ((branchLocationDenominator c1 c2 c3).eval t) ^ 3 * branchLocationDelta 1 t y := by
  let D := (branchLocationDenominator c1 c2 c3).eval t
  let N := (branchLocationNumerator c1 c2 c3).eval t
  have hn : -N = D * y := by change D * y + N = 0 at hy; linear_combination -hy
  change (branchDeltaNumerator c1 c2 c3).eval t = D ^ 3 * branchLocationDelta 1 t y
  simp only [branchDeltaNumerator, eval_mul, eval_neg, eval_sub, eval_X, eval_one]
  change t * (-N) * (t - 1) * (-N - D) * (-N - t * D) = _
  rw [hn]
  unfold branchLocationDelta
  ring

/-- Actual location/sign solutions satisfy the explicit label equation. -/
theorem branchResultantLabel_root {R : Type*} [CommRing R]
    (a A c c1 c2 c3 t y β : R)
    (hE : (branchLocationSextic c1 c2 c3).eval t = 0)
    (hy : (branchLocationDenominator c1 c2 c3).eval t * y +
      (branchLocationNumerator c1 c2 c3).eval t = 0)
    (hβ : A * β ^ 2 = a * branchLocationDelta 1 t y) :
    (branchResultantLabel a A c c1 c2 c3).eval (t + c * β) = 0 := by
  let φ := Polynomial.evalRingHom (t + c * β)
  have hid : φ.comp (Polynomial.C : R →+* R[X]) = RingHom.id R := by
    ext r
    simp [φ]
  change φ (branchResultantLabel a A c c1 c2 c3) = 0
  rw [branchResultantLabel, ← resultant_map_map]
  refine branch_resultant_zero_of_common_root _ _ 6 11 ?_ ?_ (Or.inl (by norm_num)) t ?_ ?_
  · exact (natDegree_map_le.trans natDegree_map_le).trans (branchLocationSextic_natDegree_le _ _ _)
  · exact natDegree_map_le.trans (branchLabelEliminand_natDegree_le _ _ _ _ _ _)
  · rw [Polynomial.map_map, hid, Polynomial.map_id]
    exact hE
  · rw [Polynomial.eval_map]
    simp only [branchLabelEliminand, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    have hD : ((branchLocationDenominator c1 c2 c3).map C).eval₂ φ t =
        (branchLocationDenominator c1 c2 c3).eval t := by
      rw [eval₂_map, hid]
      rfl
    have hN : ((branchDeltaNumerator c1 c2 c3).map C).eval₂ φ t =
        (branchDeltaNumerator c1 c2 c3).eval t := by
      rw [eval₂_map, hid]
      rfl
    rw [hD, hN, branchDeltaNumerator_eval c1 c2 c3 t y hy]
    simp only [φ, coe_evalRingHom, eval_C, eval_X]
    linear_combination c ^ 2 * ((branchLocationDenominator c1 c2 c3).eval t) ^ 3 * hβ

/-- The two original moment equations imply both the sextic and the linear
reconstruction relation, with only the displayed scalar degeneracies excluded. -/
theorem branch_moments_imply_sextic_and_reconstruction {K : Type*} [Field K]
    (c1 c2 c3 t y : K) (hc3 : c3 ≠ 0) (hc31 : c3 + 1 ≠ 0)
    (h₂ : c1 + c2 * t ^ 2 + c3 * y ^ 2 + (-c1 - c2 * t - c3 * y) ^ 2 = 0)
    (h₃ : c1 + c2 * t ^ 3 + c3 * y ^ 3 + (-c1 - c2 * t - c3 * y) ^ 3 = 0) :
    (branchLocationSextic c1 c2 c3).eval t = 0 ∧
      (branchLocationDenominator c1 c2 c3).eval t * y +
        (branchLocationNumerator c1 c2 c3).eval t = 0 := by
  have hq : (branchInfinityQuadratic c1 c2 c3 t).eval y = 0 := by
    simpa only [branchInfinityQuadratic_eval] using h₂
  have hg : (branchInfinityCubic c1 c2 c3 t).eval y = 0 := by
    simpa only [branchInfinityCubic_eval] using h₃
  have hs : c3 ^ 2 * (c3 + 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc3) hc31
  have he := branch_resultant_zero_of_common_root
    (branchInfinityQuadratic c1 c2 c3 t) (branchInfinityCubic c1 c2 c3 t) 2 3
    (by unfold branchInfinityQuadratic; compute_degree)
    (by unfold branchInfinityCubic; compute_degree) (Or.inl (by norm_num)) y hq hg
  rw [branchInfinity_resultant] at he
  have hl := branchInfinity_linear_subresultant c1 c2 c3 t y
  rw [hq, hg, mul_zero, mul_zero, sub_zero] at hl
  exact ⟨(mul_eq_zero.mp he).resolve_left hs, (mul_eq_zero.mp hl.symm).resolve_left hs⟩

/-- Direct specialization-compatible root theorem from the original moment
and sign equations. No rational-function-field specialization is assumed. -/
theorem branchResultantLabel_root_of_moments {K : Type*} [Field K]
    (a A c c1 c2 c3 t y β : K) (hc3 : c3 ≠ 0) (hc31 : c3 + 1 ≠ 0)
    (h₂ : c1 + c2 * t ^ 2 + c3 * y ^ 2 + (-c1 - c2 * t - c3 * y) ^ 2 = 0)
    (h₃ : c1 + c2 * t ^ 3 + c3 * y ^ 3 + (-c1 - c2 * t - c3 * y) ^ 3 = 0)
    (hβ : A * β ^ 2 = a * branchLocationDelta 1 t y) :
    (branchResultantLabel a A c c1 c2 c3).eval (t + c * β) = 0 := by
  obtain ⟨hE, hy⟩ := branch_moments_imply_sextic_and_reconstruction c1 c2 c3 t y hc3 hc31 h₂ h₃
  exact branchResultantLabel_root a A c c1 c2 c3 t y β hE hy hβ

/-- The explicit rational branch polynomial attached to an actual orbit window. -/
def orbitBranchLabelPolynomial (a b i : ℕ) (c : ℚ) : ℚ[X] :=
  branchResultantLabel a (Lz a b i : ℚ) c (-patternRhoQ a b i - patternUQ a b i)
    (patternUQ a b i - patternVQ a b i) (patternVQ a b i - 1)

set_option synthInstance.maxHeartbeats 200000 in
-- The projective chart, normalization and residue field have nested scalar towers.
set_option maxHeartbeats 1200000 in
/-- Every actual normalized branch at infinity contains a root of the explicit
rational label polynomial. This is the geometric input for the degree-24
component theorem once the specialized polynomial is irreducible of degree 12. -/
theorem orbit_infinity_residue_label_root
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] (c : ℚ) :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let ι := IsScalarTower.toAlgHom ℚ R F
    let S := projectiveChart I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))
    let C := integralClosure S F
    let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))
    ∀ p : IsDedekindDomain.HeightOneSpectrum C, algebraMap S C w ∈ p.asIdeal →
      ∃ z : C ⧸ p.asIdeal, Polynomial.aeval z (orbitBranchLabelPolynomial a b i c) = 0 := by
  classical
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let S := projectiveChart I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))
  let C := integralClosure S F
  let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))
  let hnormal := orbit_chart_normalization_in_field hba hi hne I hf hg hd hdegree F
  let : IsFractionRing S F := hnormal.1
  let : IsDedekindDomain C := hnormal.2.1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  change ∀ p : IsDedekindDomain.HeightOneSpectrum C, algebraMap S C w ∈ p.asIdeal → _
  intro p hp
  let : Field (C ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  let ψ := (Ideal.Quotient.mkₐ ℚ p.asIdeal).comp (IsScalarTower.toAlgHom ℚ S C)
  let z := fun j => ψ (chartNode I ι (Ideal.Quotient.mk I (MvPolynomial.X 0)) j)
  obtain ⟨hfirst, β, hβ⟩ := orbit_infinity_residue_scaled_sign hba hi hne I hf hg hd hdegree F p hp
  change z 0 = 1 at hfirst
  change β ^ 2 = algebraMap ℚ (C ⧸ p.asIdeal) ((a : ℚ) / (Lz a b i : ℚ)) *
    branchLocationDelta (z 0) (z 1) (z 2) at hβ
  rw [hfirst] at hβ
  have hl : ι (Ideal.Quotient.mk I (MvPolynomial.X 0)) ≠ 0 := by
    intro he
    have hn : chartNode I ι (Ideal.Quotient.mk I (MvPolynomial.X 0)) 0 = 0 := by
      apply Subtype.ext
      simp only [chartNode_val, he, zero_mul, ZeroMemClass.coe_zero]
    change ψ (chartNode I ι (Ideal.Quotient.mk I (MvPolynomial.X 0)) 0) = 1 at hfirst
    rw [hn, map_zero] at hfirst
    exact zero_ne_one hfirst
  have hψw : ψ w = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hA : (Lz a b i : ℚ) ≠ 0 := by
    exact_mod_cast (show Lz a b i ≠ 0 by
      have := Lz_pos hba (by omega : i + 5 < P a b)
      omega)
  obtain ⟨_, _, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  let κ := algebraMap ℚ (C ⧸ p.asIdeal)
  have hc3 : κ (patternVQ a b i - 1) ≠ 0 := by
    simpa only [map_zero] using κ.injective.ne (show patternVQ a b i - 1 ≠ 0 by linarith)
  have hc31 : κ (patternVQ a b i - 1) + 1 ≠ 0 := by
    have hv0 : κ (patternVQ a b i) ≠ 0 := by
      simpa only [map_zero] using κ.injective.ne (ne_of_lt hv)
    simpa only [map_sub, map_one, sub_add_cancel] using hv0
  obtain ⟨h₂, h₃⟩ := chart_infinity_moment_equations (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
    (patternVQ a b (i + 1)) (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι _ hl ψ hψw
  change (-κ (patternRhoQ a b i) - κ (patternUQ a b i)) * z 0 ^ 2 +
    (κ (patternUQ a b i) - κ (patternVQ a b i)) * z 1 ^ 2 +
    (κ (patternVQ a b i) - 1) * z 2 ^ 2 +
    (fourthNode (κ (patternRhoQ a b i)) (κ (patternUQ a b i))
      (κ (patternVQ a b i)) (z 0) (z 1) (z 2)) ^ 2 = 0 at h₂
  change (-κ (patternRhoQ a b i) - κ (patternUQ a b i)) * z 0 ^ 3 +
    (κ (patternUQ a b i) - κ (patternVQ a b i)) * z 1 ^ 3 +
    (κ (patternVQ a b i) - 1) * z 2 ^ 3 +
    (fourthNode (κ (patternRhoQ a b i)) (κ (patternUQ a b i))
      (κ (patternVQ a b i)) (z 0) (z 1) (z 2)) ^ 3 = 0 at h₃
  change β ^ 2 = κ ((a : ℚ) / (Lz a b i : ℚ)) *
    branchLocationDelta 1 (z 1) (z 2) at hβ
  have hs : κ (Lz a b i : ℚ) * β ^ 2 = κ (a : ℚ) *
      branchLocationDelta 1 (z 1) (z 2) := by
    have hAk : κ (Lz a b i : ℚ) ≠ 0 := by
      simpa only [map_zero] using κ.injective.ne hA
    rw [hβ, map_div₀, ← mul_assoc, mul_div_cancel₀ _ hAk]
  refine ⟨z 1 + κ c * β, ?_⟩
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, orbitBranchLabelPolynomial,
    branchResultantLabel_map]
  apply branchResultantLabel_root_of_moments _ _ _ _ _ _ _ (z 2) β hc3 hc31
  · convert h₂ using 1
    simp only [hfirst, one_pow, mul_one, map_neg, map_sub, map_one]
    congr 2
    unfold fourthNode
    ring
  · convert h₃ using 1
    simp only [hfirst, one_pow, mul_one, map_neg, map_sub, map_one]
    congr 2
    unfold fourthNode
    ring
  · exact hs

end
end PierceLengthBound.FixedDividend
