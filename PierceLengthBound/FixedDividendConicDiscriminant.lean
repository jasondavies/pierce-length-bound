/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendDualNumberSection
public import PierceLengthBound.FixedDividendCubicGeometry

/-!
# The binary discriminant of a nonreduced conic section

A plane relation eliminates one normalized node. Because the nodes generate a
two-dimensional section, the remaining node is nonscalar. The restricted leading
quadratic consequently has zero discriminant.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma scalar_generators_finrank_le_one {K S : Type*} [Field K] [CommRing S]
    [Algebra K S] (z : Fin 3 → S)
    (hgen : Function.Surjective (MvPolynomial.aeval (R := K) z))
    (hz : ∀ j, ∃ c : K, z j = algebraMap K S c) : Module.finrank K S ≤ 1 := by
  choose c hc using hz
  have he : MvPolynomial.aeval (R := K) z =
      (Algebra.ofId K S).comp (MvPolynomial.aeval (R := K) c) := by
    ext j
    simpa using hc j
  have hs : Function.Surjective (Algebra.linearMap K S) := by
    intro x
    obtain ⟨p, hp⟩ := hgen x
    refine ⟨MvPolynomial.eval c p, ?_⟩
    rw [he] at hp
    exact hp
  simpa using LinearMap.finrank_le_finrank_of_surjective hs

lemma section_plane_solve {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (z : Fin 3 → S) (hz0 : z 0 = 1) {n0 n1 n2 : K} (hn2 : n2 ≠ 0)
    (hp : algebraMap K S n0 * z 0 + algebraMap K S n1 * z 1 +
      algebraMap K S n2 * z 2 = 0) :
    z 2 = algebraMap K S (-n0 / n2) + algebraMap K S (-n1 / n2) * z 1 := by
  rw [hz0, mul_one] at hp
  have hc : algebraMap K S n2⁻¹ * algebraMap K S n2 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hn2, map_one]
  calc
    z 2 = algebraMap K S n2⁻¹ * (algebraMap K S n2 * z 2) := by
      rw [← mul_assoc, hc, one_mul]
    _ = algebraMap K S n2⁻¹ * (-algebraMap K S n0 - algebraMap K S n1 * z 1) := by
      congr 1
      linear_combination hp
    _ = _ := by simp only [div_eq_mul_inv, map_mul, map_neg]; ring

/-- After a plane elimination the remaining node cannot be scalar, since the
node residues generate a section of dimension two. -/
lemma section_plane_remaining_node_nonscalar {K S : Type*} [Field K] [CommRing S]
    [Algebra K S] (hdim : Module.finrank K S = 2)
    (z : Fin 3 → S) (hz0 : z 0 = 1)
    (hgen : Function.Surjective (MvPolynomial.aeval (R := K) z))
    {n0 n1 n2 : K} (hn2 : n2 ≠ 0)
    (hp : algebraMap K S n0 * z 0 + algebraMap K S n1 * z 1 +
      algebraMap K S n2 * z 2 = 0) :
    ∀ e : K, z 1 ≠ algebraMap K S e := by
  have hz2 := section_plane_solve z hz0 hn2 hp
  intro e he
  have hs : ∀ j : Fin 3, ∃ r : K, z j = algebraMap K S r := by
    intro j
    fin_cases j
    · exact ⟨1, by simpa using hz0⟩
    · exact ⟨e, he⟩
    · refine ⟨-n0 / n2 + (-n1 / n2) * e, ?_⟩
      change z 2 = _
      rw [hz2, he, map_add, map_mul]
  have hd := scalar_generators_finrank_le_one z hgen hs
  omega

/-- Explicit discriminant of the quadratic obtained by eliminating the third
node from a homogeneous plane and the actual leading quadratic. -/
theorem section_plane_quadratic_discriminant_zero {K L S : Type*}
    [Field K] [Field L] [Algebra K L] [CommRing S] [Algebra K S]
    [Module.Finite K S] (hdim : Module.finrank K S = 2)
    (φ : S →ₐ[K] L) {δ : S} (hδ : δ ≠ 0) (hn : IsNilpotent δ)
    (z : Fin 3 → S) (hz0 : z 0 = 1)
    (hgen : Function.Surjective (MvPolynomial.aeval (R := K) z))
    {n0 n1 n2 a b c : K} (hn2 : n2 ≠ 0)
    (hp : algebraMap K S n0 * z 0 + algebraMap K S n1 * z 1 +
      algebraMap K S n2 * z 2 = 0)
    (hq : MvPolynomial.aeval z (leadingQuadratic a b c) = 0) :
    let k := -n0 / n2
    let m := -n1 / n2
    (2 * c * k * m + 2 * (a + c * k) * (b + c * m)) ^ 2 -
      4 * (b + c * m ^ 2 + (b + c * m) ^ 2) *
        (a + c * k ^ 2 + (a + c * k) ^ 2) = 0 := by
  dsimp only
  have hz2 := section_plane_solve z hz0 hn2 hp
  have ht := section_plane_remaining_node_nonscalar hdim z hz0 hgen hn2 hp
  apply two_dimensional_quadratic_discriminant_zero hdim φ hδ hn ht
  simp only [leadingQuadratic, ternaryQuadratic, map_add, map_mul, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_zero,
    hz0, one_pow, mul_one, hz2] at hq
  convert hq using 1
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring


/-- A nonsingular ternary quadratic cannot vanish identically on a plane. -/
lemma restricted_leading_coefficients_not_all_zero {K : Type*} [Field K] [CharZero K]
    {a b c k m : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hs : 1 + a + b + c ≠ 0) :
    b + c * m ^ 2 + (b + c * m) ^ 2 ≠ 0 ∨
      2 * c * k * m + 2 * (a + c * k) * (b + c * m) ≠ 0 ∨
      a + c * k ^ 2 + (a + c * k) ^ 2 ≠ 0 := by
  by_contra hh
  push Not at hh
  rcases hh with ⟨hα, hβ, hγ⟩
  have hid :
      4 * a * b * c * (1 + a + b + c) =
        4 * (b + c * m ^ 2 + (b + c * m) ^ 2) *
          (a + c * k ^ 2 + (a + c * k) ^ 2) * c * (1 + c) -
        4 * (a + c * k ^ 2 + (a + c * k) ^ 2) * (c * (b + (1 + c) * m)) ^ 2 -
        4 * (b + c * m ^ 2 + (b + c * m) ^ 2) * (c * (a + (1 + c) * k)) ^ 2 -
        (2 * c * k * m + 2 * (a + c * k) * (b + c * m)) ^ 2 * c * (1 + c) +
        4 * (2 * c * k * m + 2 * (a + c * k) * (b + c * m)) *
          (c * (a + (1 + c) * k)) * (c * (b + (1 + c) * m)) := by ring
  rw [hα, hβ, hγ] at hid
  have hn := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (by norm_num : (4 : K) ≠ 0) ha) hb) hc) hs
  exact hn (by simpa using hid)

/-- The square coefficient in this chart is nonzero as well as having zero
discriminant. The first-node chart contains every infinity point. -/
theorem section_plane_quadratic_coefficients {K L S : Type*}
    [Field K] [CharZero K] [Field L] [Algebra K L] [CommRing S] [Algebra K S]
    [Module.Finite K S] (hdim : Module.finrank K S = 2)
    (φ : S →ₐ[K] L) {δ : S} (hδ : δ ≠ 0) (hn : IsNilpotent δ)
    (z : Fin 3 → S) (hz0 : z 0 = 1)
    (hgen : Function.Surjective (MvPolynomial.aeval (R := K) z))
    {n0 n1 n2 a b c : K} (hn2 : n2 ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hs : 1 + a + b + c ≠ 0)
    (hp : algebraMap K S n0 * z 0 + algebraMap K S n1 * z 1 +
      algebraMap K S n2 * z 2 = 0)
    (hq : MvPolynomial.aeval z (leadingQuadratic a b c) = 0) :
    let k := -n0 / n2
    let m := -n1 / n2
    let α := b + c * m ^ 2 + (b + c * m) ^ 2
    let β := 2 * c * k * m + 2 * (a + c * k) * (b + c * m)
    let γ := a + c * k ^ 2 + (a + c * k) ^ 2
    α ≠ 0 ∧ β ^ 2 - 4 * α * γ = 0 := by
  dsimp only
  have hdisc := section_plane_quadratic_discriminant_zero hdim φ hδ hn z hz0 hgen hn2 hp hq
  dsimp only at hdisc
  refine ⟨?_, hdisc⟩
  intro hα
  have hβ : 2 * c * (-n0 / n2) * (-n1 / n2) +
      2 * (a + c * (-n0 / n2)) * (b + c * (-n1 / n2)) = 0 := by
    rw [hα, mul_zero, zero_mul, sub_zero] at hdisc
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hdisc
  have hz2 := section_plane_solve z hz0 hn2 hp
  have hγ : a + c * (-n0 / n2) ^ 2 + (a + c * (-n0 / n2)) ^ 2 = 0 := by
    apply (algebraMap K L).injective
    have hval := congrArg φ hq
    have ht : φ (z 2) = algebraMap K L (-n0 / n2) +
        algebraMap K L (-n1 / n2) * φ (z 1) := by simpa using congrArg φ hz2
    have hz : φ (z 0) = 1 := by rw [hz0, map_one]
    simp only [leadingQuadratic, ternaryQuadratic, map_add, map_mul, map_pow,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_zero, AlgHom.commutes,
      hz, ht] at hval
    have hα' := congrArg (algebraMap K L) hα
    have hβ' := congrArg (algebraMap K L) hβ
    simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at hα' hβ' ⊢
    linear_combination hval - φ (z 1) ^ 2 * hα' - φ (z 1) * hβ'
  exact (restricted_leading_coefficients_not_all_zero ha hb hc hs).elim
    (fun h => h hα) (fun h => h.elim (fun h => h hβ) (fun h => h hγ))


lemma algebra_scalar_of_linear_eq {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    {x : S} {a b : K} (hb : b ≠ 0)
    (he : algebraMap K S a + algebraMap K S b * x = 0) :
    x = algebraMap K S (-a / b) := by
  have hu : IsUnit (algebraMap K S b) := (isUnit_iff_ne_zero.mpr hb).map (algebraMap K S)
  apply hu.mul_left_cancel
  have hk : b * (-a / b) = -a := by field_simp
  rw [← map_mul, hk, map_neg]
  linear_combination he

end
end PierceLengthBound.FixedDividend
