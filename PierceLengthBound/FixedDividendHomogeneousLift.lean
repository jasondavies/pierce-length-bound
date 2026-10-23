/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendLeadingComponents

/-!
# Lifting homogeneous ideal certificates

A certificate for a coordinate power in the leading equations and a chart
coordinate lifts to a relation with a strictly smaller affine degree error.
This is the algebraic input for eventual generation by the chart coordinate.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Extract the homogeneous part of a three-generator ideal certificate. -/
theorem homogeneous_three_generator_certificate {K σ : Type*} [Field K]
    {F G L h : MvPolynomial σ K} {p q N : ℕ}
    (hF : F.IsHomogeneous p) (hG : G.IsHomogeneous q) (hL : L.IsHomogeneous 1)
    (hh : h.IsHomogeneous N) (hpN : p ≤ N) (hqN : q ≤ N) (hN : 1 ≤ N)
    (hmem : h ∈ Ideal.span {F, G, L}) :
    ∃ s t u : MvPolynomial σ K,
      s.totalDegree ≤ N - p ∧ t.totalDegree ≤ N - q ∧ u.totalDegree ≤ N - 1 ∧
      h = s * F + t * G + u * L := by
  obtain ⟨s, z, hz, he⟩ := Ideal.mem_span_insert.mp hmem
  obtain ⟨t, u, htu⟩ := Ideal.mem_span_pair.mp hz
  rw [← htu] at he
  have hf (v B : MvPolynomial σ K) (k : ℕ) (hB : B.IsHomogeneous k) (hk : k ≤ N) :
      homogeneousComponent N (v * B) = homogeneousComponent (N - k) v * B := by
    rw [mul_comm, ← Nat.add_sub_of_le hk,
      homogeneousComponent_mul_of_homogeneous_left hB v (N - k)]
    rw [Nat.add_sub_cancel_left]
    ring
  have ht := congrArg (homogeneousComponent N) he
  rw [homogeneousComponent_eq_self hh, map_add, map_add,
    hf s F p hF hpN, hf t G q hG hqN, hf u L 1 hL hN] at ht
  refine ⟨homogeneousComponent (N - p) s, homogeneousComponent (N - q) t,
    homogeneousComponent (N - 1) u,
    (homogeneousComponent_isHomogeneous _ _).totalDegree_le,
    (homogeneousComponent_isHomogeneous _ _).totalDegree_le,
    (homogeneousComponent_isHomogeneous _ _).totalDegree_le, ?_⟩
  simpa only [add_assoc] using ht

/-- A homogeneous leading-ideal certificate gives an affine relation modulo I,
with both the error and the chart multiplier one degree lower. -/
theorem lift_coordinate_power_certificate {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) {f g : MvPolynomial σ K} {p q N : ℕ}
    (hfI : f ∈ I) (hgI : g ∈ I) (hp : 0 < p) (hq : 0 < q)
    (hf : f.totalDegree ≤ p) (hg : g.totalDegree ≤ q)
    (hpN : p ≤ N) (hqN : q ≤ N) (hN : 1 ≤ N) (j k : σ)
    (hmem : X j ^ N ∈ Ideal.span
      {homogeneousComponent p f, homogeneousComponent q g, X k}) :
    ∃ r s : MvPolynomial σ K, r.totalDegree ≤ N - 1 ∧ s.totalDegree ≤ N - 1 ∧
      Ideal.Quotient.mk I (X j ^ N) = Ideal.Quotient.mk I r +
        Ideal.Quotient.mk I (X k) * Ideal.Quotient.mk I s := by
  obtain ⟨s, t, u, hs, ht, hu, he⟩ := homogeneous_three_generator_certificate
    (homogeneousComponent_isHomogeneous p f) (homogeneousComponent_isHomogeneous q g)
    (isHomogeneous_X K k) (isHomogeneous_X_pow j N) hpN hqN hN hmem
  let r := -(s * (f - homogeneousComponent p f)) - t * (g - homogeneousComponent q g)
  have hsf : (s * (f - homogeneousComponent p f)).totalDegree ≤ N - 1 := by
    apply (totalDegree_mul _ _).trans
    have hdrop := totalDegree_sub_homogeneousComponent_le f hp hf
    omega
  have htg : (t * (g - homogeneousComponent q g)).totalDegree ≤ N - 1 := by
    apply (totalDegree_mul _ _).trans
    have hdrop := totalDegree_sub_homogeneousComponent_le g hq hg
    omega
  refine ⟨r, u, ?_, hu, ?_⟩
  · exact (totalDegree_sub _ _).trans (max_le (by simpa only [totalDegree_neg] using hsf) htg)
  have hf0 : Ideal.Quotient.mk I f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hfI
  have hg0 : Ideal.Quotient.mk I g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hgI
  rw [he]
  dsimp [r]
  simp only [map_add, map_sub, map_mul, map_neg, hf0, hg0, zero_sub]
  ring

end
end PierceLengthBound.FixedDividend
