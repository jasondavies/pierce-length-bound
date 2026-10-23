/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftNormalizationCut
public import PierceLengthBound.IntegralLiftParabola

/-! The actual normalization cut forces a polynomial quotient of degree three. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

lemma map_clearedNewtonQuartic {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : Fin 4 → R) (s : Fin 3 → R) (n d : R) :
    f (clearedNewtonQuartic c s n d) =
      clearedNewtonQuartic (f ∘ c) (f ∘ s) (f n) (f d) := by
  simp only [clearedNewtonQuartic, map_add, map_sub, map_mul, map_pow, Function.comp_apply]

lemma newtonNormalization_monic {R : Type*} [CommRing R]
    (c s : Fin 4 → R) (m : R) : (firstNewtonQuartic c s - C m).Monic := by
  rw [firstNewtonQuartic_eq]
  apply monic_of_degree_le 4
  · unfold monicQuartic
    compute_degree
    norm_num
  · simp [monicQuartic_coeff]

lemma firstNewtonQuartic_eval_eq_parabolaV {K : Type*} [Field K]
    (c : Fin 4 → K) (s : Fin 3 → Polynomial K) (q : Polynomial K) :
    (firstNewtonQuartic (fun j => C (c j)) ![s 0, s 1, s 2, 0]).eval (-q) =
      parabolaV c (fun j => q + (![0, s 0, s 1, s 2] : Fin 4 → Polynomial K) j) := by
  simp [firstNewtonQuartic, parabolaV]
  ring

/-- A nonzero polynomial denominator satisfying the cleared monic normalization
cannot produce a genuinely rational quotient. -/
theorem normalization_polynomial_quotient {K : Type*} [Field K]
    (c : Fin 4 → K) (s : Fin 3 → Polynomial K) (n d M : Polynomial K)
    {A a : K} (hA : A ≠ 0) (hd : d ≠ 0)
    (hnorm : C A * clearedNewtonQuartic (fun j => C (c j)) s n d = C a * M * d ^ 4) :
    ∃ q : Polynomial K,
      algebraMap (Polynomial K) (RatFunc K) q =
        algebraMap (Polynomial K) (RatFunc K) n / algebraMap (Polynomial K) (RatFunc K) d ∧
      C A * parabolaV c (fun j => q + (![0, s 0, s 1, s 2] : Fin 4 → Polynomial K) j) =
        C a * M := by
  let f := algebraMap (Polynomial K) (RatFunc K)
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have hdf : f d ≠ 0 := by simpa only [map_zero] using hf.ne hd
  have hAf : f (C A) ≠ 0 := by
    simpa only [map_zero] using hf.ne (show C A ≠ 0 by simpa using hA)
  let qf : RatFunc K := f n / f d
  let B : Polynomial (Polynomial K) :=
    firstNewtonQuartic (fun j => C (c j)) ![s 0, s 1, s 2, 0] - C (C (a / A) * M)
  have heval : aeval (-qf) B = 0 := by
    have h := congrArg f hnorm
    rw [map_mul, map_clearedNewtonQuartic, map_mul, map_mul, map_pow,
      clearedNewtonQuartic_div _ _ _ _ hdf] at h
    have hP :
        (firstNewtonQuartic (f ∘ (fun j => C (c j)))
          ![f (s 0), f (s 1), f (s 2), 0]).eval (-qf) = f (C (a / A) * M) := by
      have hdiv : f (C (a / A)) = f (C a) / f (C A) := by
        exact map_div₀ (f.comp C) a A
      rw [map_mul, hdiv, div_mul_eq_mul_div]
      apply (eq_div_iff hAf).2
      rw [← mul_assoc] at h
      have h' := (mul_right_cancel₀ (pow_ne_zero 4 hdf) h)
      dsimp [qf]
      calc _ = f (C A) * _ := mul_comm _ _
        _ = _ := h'
    simpa [B, firstNewtonQuartic, qf, aeval_def, eval₂_add, eval₂_sub, eval₂_mul,
      eval₂_C, eval₂_X, Function.comp_def, f] using sub_eq_zero.mpr hP
  obtain ⟨w, hw⟩ := rational_monic_root_polynomial (newtonNormalization_monic _ _ _) heval
  refine ⟨-w, ?_, ?_⟩
  · change f (-w) = qf
    rw [map_neg, hw, neg_neg]
  · apply hf
    have h := congrArg f hnorm
    rw [map_mul, map_clearedNewtonQuartic, map_mul, map_mul, map_pow,
      clearedNewtonQuartic_div _ _ _ _ hdf] at h
    rw [← mul_assoc] at h
    have h' := mul_right_cancel₀ (pow_ne_zero 4 hdf) h
    rw [← firstNewtonQuartic_eval_eq_parabolaV]
    simpa [firstNewtonQuartic, map_add, map_sub, map_mul, map_neg,
      eval_add, eval_sub, eval_mul, eval_C, eval_X, Function.comp_def, hw, qf, f] using h'

lemma polynomial_quotient_mul {K : Type*} [Field K] (n d q : Polynomial K)
    (hd : d ≠ 0)
    (hq : algebraMap (Polynomial K) (RatFunc K) q =
      algebraMap (Polynomial K) (RatFunc K) n / algebraMap (Polynomial K) (RatFunc K) d) :
    q * d = n := by
  have hf := IsFractionRing.injective (Polynomial K) (RatFunc K)
  apply hf
  rw [map_mul, hq, div_mul_cancel₀]
  simpa only [map_zero] using hf.ne hd

/-- Outside an absolute finite exception, the quotient on an actual
nonexceptional conic is a polynomial of degree exactly three. The normalization
identity is derived from actual orbit states, not postulated on the conic. -/
theorem orbit_conic_quotient_cubic {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (z : Fin 3 → Polynomial ℚ) (hz : ∀ j, (z j).natDegree ≤ 2)
    (hfirst : (z 0).coeff 2 ≠ 0)
    (hquad : MvPolynomial.aeval z (orbitCurveQuadraticQ a b i) = 0)
    (hcurve : MvPolynomial.aeval z (orbitCurveEquationQ a b i) = 0)
    (t0 : ℚ) (hz0 : ∀ j, (z j).eval t0 = orbitFreeNodesQ a b i j)
    {ι : Type*} [Fintype ι] (l : ι → ℕ) (t : ι → ℚ) (ht : Function.Injective t)
    (hl : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j))
    (hp : ∀ j k, (z k).eval (t j) = orbitFreeNodesQ a b (l j) k)
    (hcard : 332 < Fintype.card ι) :
    ∃ q : Polynomial ℚ,
      q.natDegree = 3 ∧
      q * MvPolynomial.aeval z (orbitQuotientDenominatorQ a b i) =
        MvPolynomial.aeval z (orbitQuotientNumeratorQ a b i) ∧
      (parabolaV
        (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
          (patternVQ a b i) j.castSucc)
        (fun j => q + (![0, z 0, z 1, z 2] : Fin 4 → Polynomial ℚ) j)).natDegree = 12 := by
  let n := MvPolynomial.aeval z (orbitQuotientNumeratorQ a b i)
  let d := MvPolynomial.aeval z (orbitQuotientDenominatorQ a b i)
  let k := orbitParameterGaps a b i z
  let c : Fin 4 → ℚ := fun j => coeffs (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) j.castSucc
  have hden : d ≠ 0 := by
    intro hd
    have he : d.eval t0 = MvPolynomial.eval (orbitFreeNodesQ a b i)
        (orbitQuotientDenominatorQ a b i) := by
      dsimp only [d]
      rw [polynomial_substitution_eval,
        show (fun j => (z j).eval t0) = orbitFreeNodesQ a b i from funext hz0]
    rw [hd, eval_zero] at he
    exact (orbitQuotient_evaluation hba hi).1 he.symm
  obtain ⟨hρ, hu, hv, hneq, ha, hA⟩ := orbit_rational_nonexceptional_data hba hi hne
  have hcut := orbitNormalizationCut_zero_of_many_states hba z hz l t ht hl hθ hp hcard
  have hnorm : C (Lz a b i : ℚ) * clearedNewtonQuartic (fun j => C (c j)) z n d =
      C (a : ℚ) * muH4 (k 0) (k 1) (k 2) (k 3) (k 4) * d ^ 4 := sub_eq_zero.mp hcut
  obtain ⟨q, hq, heq⟩ := normalization_polynomial_quotient c z n d _ hA hden hnorm
  have hraw := quadratic_parameter_raw_degrees hρ hu hv hneq
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a ha z hz hfirst hquad hcurve
  have hV := parabola_normalization_degree c
    (fun j => q + (![0, z 0, z 1, z 2] : Fin 4 → Polynomial ℚ) j) k hA ha hraw.2.1 heq
  have hs : ∀ j : Fin 4, ((![0, z 0, z 1, z 2] : Fin 4 → Polynomial ℚ) j).natDegree ≤ 2 := by
    intro j
    fin_cases j
    · simp
    · exact hz 0
    · exact hz 1
    · exact hz 2
  exact ⟨q, parabola_quotient_degree_three c _ hs q hV,
    polynomial_quotient_mul n d q hden hq, hV⟩

end
end PierceLengthBound.FixedDividend
