/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormCount
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! The integer-value lemma for rational functions in the conic refinement.
A nonconstant denominator at an integral value divides the nonzero resultant.
The bound is uniform in the interval containing the integer parameters. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset Polynomial

/-- Signed divisors of a nonzero integer, represented without choosing signs. -/
def signedDivisors (R : ℤ) : Finset ℤ :=
  R.natAbs.divisors.image (fun n : ℕ => (n : ℤ)) ∪
    R.natAbs.divisors.image (fun n : ℕ => -(n : ℤ))

lemma signedDivisors_card (R : ℤ) : (signedDivisors R).card ≤ 2 * R.natAbs.divisors.card := by
  calc (signedDivisors R).card ≤ _ := card_union_le _ _
    _ ≤ R.natAbs.divisors.card + R.natAbs.divisors.card := add_le_add card_image_le card_image_le
    _ = _ := by ring

lemma mem_signedDivisors {R e : ℤ} (hR : R ≠ 0) (he : e ∣ R) : e ∈ signedDivisors R := by
  have hm : e.natAbs ∈ R.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr he, by simpa using hR⟩
  rcases Int.natAbs_eq e with h | h
  · exact mem_union_left _ (mem_image.mpr ⟨_, hm, h.symm⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨_, hm, h.symm⟩)

/-- Every fiber of a nonconstant integer polynomial has at most its degree points. -/
lemma polynomial_eval_fiber_card (G : ℤ[X]) (hG : 0 < G.natDegree)
    (S : Finset ℤ) (e : ℤ) : (S.filter fun t => G.eval t = e).card ≤ G.natDegree := by
  have hz : G - C e ≠ 0 := by
    intro h
    have hd := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
    simp only [natDegree_C] at hd
    omega
  apply (Polynomial.card_le_degree_of_subset_roots (p := G - C e) ?_).trans
    ((natDegree_sub_le _ _).trans (by simp))
  intro t ht
  have he := (mem_filter.mp ht).2
  exact (Polynomial.mem_roots hz).mpr (by simp [Polynomial.IsRoot, he])

/-- Bezout identity version of the integer-value counting lemma. -/
theorem integer_values_card_of_bezout (F G U V : ℤ[X]) {R : ℤ} (hR : R ≠ 0)
    (hG : 0 < G.natDegree) (hbez : F * U + G * V = C R)
    (S : Finset ℤ) (hdiv : ∀ t ∈ S, G.eval t ∣ F.eval t) :
    S.card ≤ 2 * G.natDegree * R.natAbs.divisors.card := by
  have him : S.image G.eval ⊆ signedDivisors R := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := mem_image.mp he
    have hb := congrArg (Polynomial.eval t) hbez
    simp only [eval_add, eval_mul, eval_C] at hb
    apply mem_signedDivisors hR
    rw [← hb]
    exact dvd_add (dvd_mul_of_dvd_left (hdiv t ht) _) (dvd_mul_right _ _)
  have hcard : S.card ≤ G.natDegree * (S.image G.eval).card :=
    card_le_mul_card_image S G.natDegree (fun e _ => polynomial_eval_fiber_card G hG S e)
  calc S.card ≤ G.natDegree * (S.image G.eval).card := hcard
    _ ≤ G.natDegree * (signedDivisors R).card := Nat.mul_le_mul_left _ (card_le_card him)
    _ ≤ G.natDegree * (2 * R.natAbs.divisors.card) := Nat.mul_le_mul_left _ (signedDivisors_card R)
    _ = _ := by ring

/-- Resultant version, with no height or interval hypothesis on the parameters. -/
theorem integer_values_card_of_resultant (F G : ℤ[X]) (hG : 0 < G.natDegree)
    (hR : F.resultant G ≠ 0) (S : Finset ℤ)
    (hdiv : ∀ t ∈ S, G.eval t ∣ F.eval t) :
    S.card ≤ 2 * G.natDegree * (F.resultant G).natAbs.divisors.card := by
  obtain ⟨U, V, _, _, hb⟩ := exists_mul_add_mul_eq_C_resultant F G
    (m := F.natDegree) (n := G.natDegree) le_rfl le_rfl (Or.inr (by omega))
  exact integer_values_card_of_bezout F G U V hR hG hb S hdiv

/-- Coprimality over the rationals supplies the required nonzero integral resultant. -/
lemma resultant_ne_zero_of_rat_coprime (F G : ℤ[X])
    (hcop : IsCoprime (F.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ))) :
    F.resultant G ≠ 0 := by
  have hr := Polynomial.resultant_ne_zero _ _ hcop
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [natDegree_map_eq_of_injective hi, natDegree_map_eq_of_injective hi,
    resultant_map_map] at hr
  intro hz
  exact hr (by rw [hz, map_zero])

/-- The candidate's integer-value lemma for coprime rational numerator and denominator. -/
theorem integer_values_card (F G : ℤ[X]) (hG : 0 < G.natDegree)
    (hcop : IsCoprime (F.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ)))
    (S : Finset ℤ) (hdiv : ∀ t ∈ S, G.eval t ∣ F.eval t) :
    S.card ≤ 2 * G.natDegree * (F.resultant G).natAbs.divisors.card :=
  integer_values_card_of_resultant F G hG (resultant_ne_zero_of_rat_coprime F G hcop) S hdiv

end PierceLengthBound.FixedDividend
