/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftResolventCut

/-! # The retained identities in a field

If the cleared normalization and resolvent polynomials vanish under a map `ψ` to a field in
which the reconstruction denominators are nonzero, the identities `N₀ P₄(-Q) = a H₄` and
`E₀ P₄(-Q) = a ((Q - p₃) H₃ - H₀₁₃)` hold in that field. On a component through the free nodes
of an orbit state, both denominators are nonzero in every faithful field realization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- If the free nodes of state `i` lie on the component `I`, the denominators of `Q` and `E₀`
stay nonzero under every injective algebra map from `ℚ[x]/I` to a field. -/
theorem orbit_reconstruction_field_denominators {F : Type*} [Field F] [Algebra ℚ F]
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι) :
    ι (Ideal.Quotient.mk I (orbitQuotientDenominatorQ a b i)) ≠ 0 ∧
      ι (Ideal.Quotient.mk I (orbitLiftDenominatorQ a b i)) ≠ 0 := by
  have hproper : orbitQuotientDenominatorQ a b i ∉ I := by
    intro h
    exact (orbitQuotient_evaluation hba hi).1 (hx _ h)
  constructor
  · intro hz
    exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp (hι (by simpa using hz)))
  · intro hz
    exact (orbitLift_denominator_not_mem hba hi I hx)
      (Ideal.Quotient.eq_zero_iff_mem.mp (hι (by simpa using hz)))

lemma map_rawHankelThree {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k0 k1 k2 : R) :
    f (rawHankelThree k0 k1 k2) = rawHankelThree (f k0) (f k1) (f k2) := by
  simp only [rawHankelThree, map_add, map_sub, map_mul, map_pow, map_one]

lemma map_rawHankelMixed {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k0 k1 k2 k3 : R) :
    f (rawHankelMixed k0 k1 k2 k3) = rawHankelMixed (f k0) (f k1) (f k2) (f k3) := by
  simp only [rawHankelMixed, map_add, map_sub, map_mul, map_pow, map_ofNat]

/-- If the cleared normalization polynomial vanishes under `ψ` and the denominator of `Q` does
not, then `N₀ P₄(-Q) = a H₄` in `F`, with `Q` the reconstructed quotient. -/
theorem jointNormalizationPolynomial_field_identity {F : Type*} [Field F] [Algebra ℚ F]
    (ψ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] F) (a b i : ℕ)
    (hd : ψ (orbitQuotientDenominatorQ a b i) ≠ 0)
    (hz : ψ (jointNormalizationPolynomial a b i) = 0) :
    let c := fun j : Fin 4 => ψ (C (coeffs (patternRhoQ a b i)
      (patternUQ a b i) (patternVQ a b i) j.castSucc))
    let s := fun j : Fin 3 => ψ (X j)
    let q := ψ (orbitQuotientNumeratorQ a b i) / ψ (orbitQuotientDenominatorQ a b i)
    let k := fun j => ψ (jointGapPolynomials a b i j)
    ψ (C (Lz a b i : ℚ)) *
      (firstNewtonQuartic c ![s 0, s 1, s 2, 0]).eval (-q) =
        ψ (C (a : ℚ)) * muH4 (k 0) (k 1) (k 2) (k 3) (k 4) := by
  dsimp only
  change ψ.toRingHom (jointNormalizationPolynomial a b i) = 0 at hz
  simp only [jointNormalizationPolynomial, map_sub, map_mul, map_pow,
    map_clearedNewtonQuartic, map_muH4, sub_eq_zero] at hz
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Function.comp_def] at hz
  rw [clearedNewtonQuartic_div _ _ _ _ hd] at hz
  apply mul_right_cancel₀ (pow_ne_zero 4 hd)
  simpa only [mul_assoc] using hz

/-- If the cleared resolvent polynomial vanishes under `ψ` and the denominators of `Q` and `E₀`
do not, then `E₀ P₄(-Q) = a ((Q - p₃) H₃ - H₀₁₃)` in `F`. -/
theorem jointResolventPolynomial_field_identity {F : Type*} [Field F] [Algebra ℚ F]
    (ψ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] F) (a b i : ℕ)
    (hd : ψ (orbitQuotientDenominatorQ a b i) ≠ 0)
    (hQ : ψ (orbitLiftDenominatorQ a b i) ≠ 0)
    (hz : ψ (jointResolventPolynomial a b i) = 0) :
    let c := fun j : Fin 4 => ψ (C (coeffs (patternRhoQ a b i)
      (patternUQ a b i) (patternVQ a b i) j.castSucc))
    let s := fun j : Fin 3 => ψ (X j)
    let q := ψ (orbitQuotientNumeratorQ a b i) / ψ (orbitQuotientDenominatorQ a b i)
    let k := fun j => ψ (jointGapPolynomials a b i j)
    (ψ (orbitLiftNumeratorQ a b i) / ψ (orbitLiftDenominatorQ a b i)) *
      (firstNewtonQuartic c ![s 0, s 1, s 2, 0]).eval (-q) =
        ψ (C (a : ℚ)) * ((q - ψ (jointQuarticCubicCoefficient a b i)) *
          rawHankelThree (k 0) (k 1) (k 2) - rawHankelMixed (k 0) (k 1) (k 2) (k 3)) := by
  dsimp only
  change ψ.toRingHom (jointResolventPolynomial a b i) = 0 at hz
  simp only [jointResolventPolynomial, map_sub, map_mul, map_pow,
    map_clearedNewtonQuartic, map_rawHankelThree, map_rawHankelMixed, sub_eq_zero] at hz
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Function.comp_def] at hz
  rw [clearedNewtonQuartic_div _ _ _ _ hd] at hz
  have hn : ψ (orbitQuotientNumeratorQ a b i) =
      (ψ (orbitQuotientNumeratorQ a b i) / ψ (orbitQuotientDenominatorQ a b i)) *
        ψ (orbitQuotientDenominatorQ a b i) := (div_mul_cancel₀ _ hd).symm
  have hP : ψ (orbitLiftNumeratorQ a b i) =
      (ψ (orbitLiftNumeratorQ a b i) / ψ (orbitLiftDenominatorQ a b i)) *
        ψ (orbitLiftDenominatorQ a b i) := (div_mul_cancel₀ _ hQ).symm
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 4 hd) hQ)
  linear_combination hz +
    hn * (ψ (C (a : ℚ)) * rawHankelThree (ψ (jointGapPolynomials a b i 0))
      (ψ (jointGapPolynomials a b i 1)) (ψ (jointGapPolynomials a b i 2)) *
        ψ (orbitQuotientDenominatorQ a b i) ^ 3 * ψ (orbitLiftDenominatorQ a b i)) -
    hP * ((firstNewtonQuartic
      (fun j : Fin 4 => ψ (C (coeffs (patternRhoQ a b i) (patternUQ a b i)
        (patternVQ a b i) j.castSucc)))
      ![ψ (X 0), ψ (X 1), ψ (X 2), 0]).eval
        (-(ψ (orbitQuotientNumeratorQ a b i) / ψ (orbitQuotientDenominatorQ a b i))) *
          ψ (orbitQuotientDenominatorQ a b i) ^ 4)

end
end PierceLengthBound.FixedDividend
