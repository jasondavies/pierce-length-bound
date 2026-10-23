/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveSpecialization
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic

/-! The mod-71 irreducibility certificate for the specialized location sextic
`E⋆` (Lemma 10.3, Appendix D). All modular arithmetic is checked by the Lean
kernel. The proof excludes irreducible factors of degrees one, two and three
using Frobenius congruences and explicit Bézout identities, then lifts
irreducibility to `ℤ` and `ℚ` through the degree-preserving reduction. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial
noncomputable section

private instance : Fact (Nat.Prime 71) := ⟨by norm_num⟩

/-- The integer sextic obtained at `(c₁,c₂,c₃) = (-7,8,-4)`. -/
def branchSexticSpecialization : ℤ[X] :=
  2400 * X ^ 6 - 20160 * X ^ 5 + 69776 * X ^ 4 - 126448 * X ^ 3 +
    125636 * X ^ 2 - 64680 * X + 13475

/-- The monic reduction of the sextic modulo 71. -/
def branchSexticMod71 : (ZMod 71)[X] :=
  X ^ 6 + 20 * X ^ 5 - 14 * X ^ 4 + 15 * X ^ 3 - 28 * X ^ 2 + 5 * X - 4

lemma branchSexticSpecialization_map_mod71 :
    branchSexticSpecialization.map (Int.castRingHom (ZMod 71)) =
      57 * branchSexticMod71 := by
  simp only [branchSexticSpecialization, branchSexticMod71, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat]
  ring_nf
  reduce_mod_char
  ring_nf
  reduce_mod_char

lemma branchSexticMod71_natDegree : branchSexticMod71.natDegree = 6 := by
  unfold branchSexticMod71
  compute_degree <;> norm_num

lemma branchSexticMod71_monic : branchSexticMod71.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 6 branchSexticMod71_natDegree.le
  simp [branchSexticMod71, coeff_add, coeff_sub, coeff_X]

private lemma remainder_trans {p a b c : (ZMod 71)[X]}
    (hab : p ∣ a - b) (hbc : p ∣ b - c) : p ∣ a - c := by
  convert dvd_add hab hbc using 1
  ring

private lemma remainder_pow {p a b : (ZMod 71)[X]} (h : p ∣ a - b) (n : ℕ) :
    p ∣ a ^ n - b ^ n := h.trans (sub_dvd_pow_sub_pow a b n)

private lemma remainder_mul {p a b c d : (ZMod 71)[X]}
    (hab : p ∣ a - b) (hcd : p ∣ c - d) : p ∣ a * c - b * d := by
  convert dvd_add (hab.mul_right c) (hcd.mul_left b) using 1
  ring

/-- Square-and-multiply for `b ^ 71 = b ^ (64 + 4 + 2 + 1)` modulo `p`, from
one checked division per step. -/
private lemma remainder_pow_71 {p b r₂ r₄ r₈ r₁₆ r₃₂ r₆₄ r₆₈ r₇₀ r₇₁ : (ZMod 71)[X]}
    (c₂ : p ∣ b * b - r₂) (c₄ : p ∣ r₂ * r₂ - r₄) (c₈ : p ∣ r₄ * r₄ - r₈)
    (c₁₆ : p ∣ r₈ * r₈ - r₁₆) (c₃₂ : p ∣ r₁₆ * r₁₆ - r₃₂) (c₆₄ : p ∣ r₃₂ * r₃₂ - r₆₄)
    (c₆₈ : p ∣ r₆₄ * r₄ - r₆₈) (c₇₀ : p ∣ r₆₈ * r₂ - r₇₀) (c₇₁ : p ∣ r₇₀ * b - r₇₁) :
    p ∣ b ^ 71 - r₇₁ := by
  have sq {k : ℕ} {r s : (ZMod 71)[X]} (h : p ∣ b ^ k - r) (c : p ∣ r * r - s) :
      p ∣ b ^ (k * 2) - s := by
    simpa only [pow_mul, pow_two] using
      remainder_trans (remainder_pow h 2) (by simpa only [pow_two] using c)
  have mul {k l : ℕ} {r r' s : (ZMod 71)[X]} (h : p ∣ b ^ k - r) (h' : p ∣ b ^ l - r')
      (c : p ∣ r * r' - s) : p ∣ b ^ (k + l) - s := by
    simpa only [pow_add] using remainder_trans (remainder_mul h h') c
  have h₂ : p ∣ b ^ 2 - r₂ := by simpa only [pow_two] using c₂
  have h₁ : p ∣ b ^ 1 - b := by simp
  have h₄ := sq h₂ c₄
  exact mul (mul (mul (sq (sq (sq (sq h₄ c₈) c₁₆) c₃₂) c₆₄) h₄ c₆₈) h₂ c₇₀) h₁ c₇₁

private def branchFrobeniusRemainder1 : (ZMod 71)[X] :=
  14 * X ^ 5 + 33 * X ^ 4 + 31 * X ^ 3 + 34 * X ^ 2 + 48 * X

private def branchFrobeniusRemainder2 : (ZMod 71)[X] :=
  36 * X ^ 5 + 48 * X ^ 4 + 49 * X ^ 3 + 53 * X ^ 2 + 36 * X + 42

private def branchFrobeniusRemainder3 : (ZMod 71)[X] :=
  37 * X ^ 5 + 22 * X ^ 4 + 60 * X ^ 3 + 13 * X ^ 2 + 66 * X + 35

/-- Check a polynomial identity modulo 71. A second normalization pass is
needed because reducing coefficients can expose further cancellations. -/
local macro "mod71_check" : tactic =>
  `(tactic| (simp only [branchSexticMod71, branchFrobeniusRemainder1, branchFrobeniusRemainder2,
      branchFrobeniusRemainder3]; ring_nf; try reduce_mod_char; try ring_nf; try reduce_mod_char))

/-- The variable over `ZMod 71`; fixing the coefficient ring keeps elaboration cheap. -/
local notation "Y" => (X : (ZMod 71)[X])

private lemma branchFrobeniusStep1 :
    branchSexticMod71 ∣ X ^ 71 - branchFrobeniusRemainder1 :=
  remainder_pow_71
    (r₂ := Y ^ 2)
    (r₄ := Y ^ 4)
    (r₈ := 16 * Y ^ 5 + 18 * Y ^ 4 + 41 * Y ^ 3 + 52 * Y ^ 2 + 51 * Y + 23)
    (r₁₆ := 13 * Y ^ 5 + 50 * Y ^ 4 + 3 * Y ^ 3 + 32 * Y ^ 2 + 24 * Y + 8)
    (r₃₂ := 32 * Y ^ 5 + 36 * Y ^ 4 + 66 * Y ^ 3 + 11 * Y ^ 2 + 23 * Y + 66)
    (r₆₄ := 18 * Y ^ 5 + 29 * Y ^ 4 + 16 * Y ^ 3 + 58 * Y ^ 2 + 64 * Y + 21)
    (r₆₈ := 59 * Y ^ 5 + 56 * Y ^ 4 + 53 * Y ^ 3 + 21 * Y ^ 2 + 52 * Y + 61)
    (r₇₀ := 14 * Y ^ 4 + 33 * Y ^ 3 + 31 * Y ^ 2 + 34 * Y + 48)
    (.intro 0 (by mod71_check))
    (.intro 0 (by mod71_check))
    (.intro (Y ^ 2 + 51 * Y + 59) (by mod71_check))
    (.intro (43 * Y ^ 4 + 37 * Y ^ 2 + 51 * Y + 65) (by mod71_check))
    (.intro (27 * Y ^ 4 + 50 * Y ^ 3 + 39 * Y ^ 2 + 8 * Y + 36) (by mod71_check))
    (.intro (30 * Y ^ 4 + 47 * Y ^ 2 + 19 * Y + 70) (by mod71_check))
    (.intro (18 * Y ^ 3 + 24 * Y ^ 2 + Y + 33) (by mod71_check))
    (.intro (59 * Y + 12) (by mod71_check))
    (.intro 0 (by mod71_check))

private lemma branchFrobeniusCoprime1 :
    IsCoprime branchSexticMod71 (branchFrobeniusRemainder1 - X) :=
  ⟨9 * X ^ 4 + 25 * X ^ 3 + 62 * X ^ 2 + 30 * X + 53,
    45 * X ^ 5 + X ^ 4 + 19 * X ^ 3 + 27 * X ^ 2 + 6 * X + 9, by mod71_check⟩

private lemma branchFrobeniusStep2 :
    branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 71 - branchFrobeniusRemainder2 :=
  remainder_pow_71
    (r₂ := 22 * Y ^ 5 + 66 * Y ^ 4 + 11 * Y ^ 3 + 53 * Y ^ 2 + 10 * Y + 25)
    (r₄ := 19 * Y ^ 5 + 34 * Y ^ 4 + 57 * Y ^ 3 + 11 * Y ^ 2 + 47 * Y + 46)
    (r₈ := 30 * Y ^ 5 + 38 * Y ^ 4 + 70 * Y ^ 3 + 30 * Y ^ 2 + 32 * Y + 69)
    (r₁₆ := 25 * Y ^ 5 + 12 * Y ^ 4 + 62 * Y ^ 3 + 64 * Y ^ 2 + 34 * Y + 5)
    (r₃₂ := 55 * Y ^ 5 + 9 * Y ^ 4 + 30 * Y ^ 3 + 64 * Y ^ 2 + 19 * Y + 63)
    (r₆₄ := 5 * Y ^ 5 + 59 * Y ^ 4 + 44 * Y ^ 3 + 54 * Y ^ 2 + 15 * Y + 32)
    (r₆₈ := 68 * Y ^ 5 + 30 * Y ^ 4 + 66 * Y ^ 3 + 66 * Y ^ 2 + 20 * Y + 51)
    (r₇₀ := 32 * Y ^ 5 + 61 * Y ^ 4 + 7 * Y ^ 3 + 41 * Y ^ 2 + 67 * Y + 36)
    (.intro (54 * Y ^ 4 + 57 * Y ^ 3 + 11 * Y ^ 2 + 68 * Y + 24) (by mod71_check))
    (.intro (58 * Y ^ 4 + 40 * Y ^ 3 + 24 * Y ^ 2 + 12 * Y + 15) (by mod71_check))
    (.intro (6 * Y ^ 4 + 36 * Y ^ 3 + 59 * Y ^ 2 + 49 * Y + 3) (by mod71_check))
    (.intro (48 * Y ^ 4 + 42 * Y ^ 3 + 9 * Y ^ 2 + 63 * Y + 18) (by mod71_check))
    (.intro (57 * Y ^ 4 + 28 * Y ^ 3 + 3 * Y ^ 2 + 47 * Y + 45) (by mod71_check))
    (.intro (43 * Y ^ 4 + 59 * Y ^ 3 + 34 * Y ^ 2 + 52 * Y + 63) (by mod71_check))
    (.intro (24 * Y ^ 4 + 30 * Y ^ 3 + 23 * Y ^ 2 + 2 * Y + 53) (by mod71_check))
    (.intro (5 * Y ^ 4 + 7 * Y ^ 3 + 63 * Y ^ 2 + 56 * Y + 63) (by mod71_check))
    (.intro (22 * Y ^ 4 + 50 * Y ^ 3 + 68 * Y ^ 2 + 25 * Y + 46) (by mod71_check))

private lemma branchFrobeniusCoprime2 :
    IsCoprime branchSexticMod71 (branchFrobeniusRemainder2 - X) :=
  ⟨20 * X ^ 4 + 34 * X ^ 3 + 31 * X ^ 2 + 13 * X + 24,
    31 * X ^ 5 + 61 * X ^ 4 + 42 * X ^ 3 + 61 * X ^ 2 + 39 * X + 4, by mod71_check⟩

private lemma branchFrobeniusStep3 :
    branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 71 - branchFrobeniusRemainder3 :=
  remainder_pow_71
    (r₂ := 17 * Y ^ 5 + 70 * Y ^ 4 + 40 * Y ^ 3 + Y ^ 2 + 25 * Y + 3)
    (r₄ := 28 * Y ^ 5 + 6 * Y ^ 4 + 36 * Y ^ 3 + 48 * Y ^ 2 + 7 * Y + 3)
    (r₈ := 57 * Y ^ 5 + 58 * Y ^ 4 + 34 * Y ^ 3 + 4 * Y ^ 2 + 2 * Y + 53)
    (r₁₆ := 42 * Y ^ 5 + 62 * Y ^ 4 + 15 * Y ^ 3 + 60 * Y ^ 2 + 27 * Y + 45)
    (r₃₂ := 39 * Y ^ 5 + 54 * Y ^ 4 + 16 * Y ^ 3 + 62 * Y ^ 2 + 6 * Y + 41)
    (r₆₄ := 13 * Y ^ 5 + 67 * Y ^ 4 + 55 * Y ^ 3 + 68 * Y ^ 2 + 65 * Y + 61)
    (r₆₈ := 50 * Y ^ 5 + 24 * Y ^ 3 + 61 * Y ^ 2 + 65 * Y + 61)
    (r₇₀ := 67 * Y ^ 5 + 19 * Y ^ 4 + 24 * Y ^ 3 + 36 * Y ^ 2 + 45 * Y + 12)
    (.intro (18 * Y ^ 4 + 43 * Y ^ 3 + 41 * Y ^ 2 + 9 * Y + 39) (by mod71_check))
    (.intro (5 * Y ^ 4 + 8 * Y ^ 3 + 64 * Y ^ 2 + 60 * Y + 34) (by mod71_check))
    (.intro (3 * Y ^ 4 + 63 * Y ^ 3 + 53 * Y ^ 2 + 57 * Y + 11) (by mod71_check))
    (.intro (54 * Y ^ 4 + 65 * Y ^ 3 + 22 * Y ^ 2 + 13 * Y + 19) (by mod71_check))
    (.intro (60 * Y ^ 4 + 32 * Y ^ 3 + 50 * Y ^ 2 + 52 * Y + 1) (by mod71_check))
    (.intro (30 * Y ^ 4 + 62 * Y ^ 3 + 7 * Y ^ 2 + 26 * Y + 21) (by mod71_check))
    (.intro (9 * Y ^ 4 + 70 * Y ^ 3 + 9 * Y + 5) (by mod71_check))
    (.intro (69 * Y ^ 4 + 61 * Y ^ 3 + 24 * Y ^ 2 + 47 * Y + 46) (by mod71_check))
    (.intro (69 * Y ^ 4 + 35 * Y ^ 3 + 66 * Y + 7) (by mod71_check))

private lemma branchFrobeniusCoprime3 :
    IsCoprime branchSexticMod71 (branchFrobeniusRemainder3 - X) :=
  ⟨25 * X ^ 4 + 11 * X ^ 3 + 53 * X ^ 2 + 59 * X + 48,
    7 * X ^ 5 + 30 * X ^ 4 + 65 * X ^ 3 + 64 * X ^ 2 + 25 * X + 40, by mod71_check⟩

private lemma remainder_frobenius_iteration {p r s : (ZMod 71)[X]} (k n : ℕ)
    (hn : 71 ^ n = 71 ^ k * 71)
    (h : p ∣ X ^ (71 ^ k) - r) (hs : p ∣ r ^ 71 - s) :
    p ∣ X ^ (71 ^ n) - s := by
  -- Prove exponent transport with a variable index so that no concrete
  -- polynomial power is unfolded when checking the transport itself.
  rw [hn, pow_mul]
  exact remainder_trans (remainder_pow h 71) hs

private lemma branchFrobenius2 :
    branchSexticMod71 ∣ X ^ (71 ^ 2) - branchFrobeniusRemainder2 :=
  remainder_frobenius_iteration 1 2 (pow_succ 71 1)
    (by simpa only [pow_one] using branchFrobeniusStep1)
    branchFrobeniusStep2

private lemma branchFrobenius3 :
    branchSexticMod71 ∣ X ^ (71 ^ 3) - branchFrobeniusRemainder3 :=
  remainder_frobenius_iteration 2 3 (pow_succ 71 2) branchFrobenius2 branchFrobeniusStep3

private lemma not_irreducible_factor_of_frobenius_certificate
    {g r : (ZMod 71)[X]} {k : ℕ}
    (hg : Irreducible g) (hd : g.natDegree = k) (hgf : g ∣ branchSexticMod71)
    (hrem : branchSexticMod71 ∣ X ^ (71 ^ k) - r)
    (hcoprime : IsCoprime branchSexticMod71 (r - X)) : False := by
  have hfrob : g ∣ X ^ (71 ^ k) - X := by
    have h := hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp
      (show g.natDegree ∣ k by rw [hd])
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using h
  have hr : g ∣ r - X := by
    convert dvd_sub hfrob (hgf.trans hrem) using 1
    ring
  exact hg.not_isUnit (hcoprime.isUnit_of_dvd' hgf hr)

/-- The monic reduction of the sextic is irreducible modulo 71. -/
theorem branchSexticMod71_irreducible : Irreducible branchSexticMod71 := by
  have hf1 : branchSexticMod71 ≠ 1 := by
    intro h
    have := branchSexticMod71_natDegree
    simp [h] at this
  rw [branchSexticMod71_monic.irreducible_iff_lt_natDegree_lt hf1]
  intro q hq hqdeg hqdvd
  have hqpos : 0 < q.natDegree := (Finset.mem_Ioc.mp hqdeg).1
  have hqle : q.natDegree ≤ 3 := by
    simpa only [branchSexticMod71_natDegree, Nat.reduceDiv] using
      (Finset.mem_Ioc.mp hqdeg).2
  obtain ⟨g, hg, hgq⟩ := exists_irreducible_of_natDegree_pos hqpos
  have hgpos : 0 < g.natDegree := hg.natDegree_pos
  have hgle : g.natDegree ≤ 3 := (natDegree_le_of_dvd hgq hq.ne_zero).trans hqle
  have hgf := hgq.trans hqdvd
  interval_cases hgdegree : g.natDegree
  · exact not_irreducible_factor_of_frobenius_certificate hg hgdegree hgf
      (by simpa using branchFrobeniusStep1) branchFrobeniusCoprime1
  · exact not_irreducible_factor_of_frobenius_certificate hg hgdegree hgf
      branchFrobenius2 branchFrobeniusCoprime2
  · exact not_irreducible_factor_of_frobenius_certificate hg hgdegree hgf
      branchFrobenius3 branchFrobeniusCoprime3

/-- The sextic has no nonunit constant divisor. -/
lemma branchSexticSpecialization_isPrimitive : branchSexticSpecialization.IsPrimitive := by
  intro r hr
  have hc := (C_dvd_iff_dvd_coeff r branchSexticSpecialization).mp hr
  have h0 : r ∣ 13475 := by
    simpa [branchSexticSpecialization, coeff_add, coeff_sub, coeff_X] using hc 0
  have h4 : r ∣ 69776 := by
    simpa [branchSexticSpecialization, coeff_add, coeff_sub, coeff_X] using hc 4
  have h6 : r ∣ 2400 := by
    simpa [branchSexticSpecialization, coeff_add, coeff_sub, coeff_X] using hc 6
  apply isUnit_iff_dvd_one.mpr
  convert dvd_sub (dvd_add h4 (h0.mul_left 36283)) (h6.mul_left 203743) using 1
  norm_num

/-- The specialized sextic is irreducible over the integers. -/
theorem branchSexticSpecialization_irreducible : Irreducible branchSexticSpecialization := by
  apply primitive_irreducible_of_degree_preserving_specialization (Int.castRingHom (ZMod 71))
    branchSexticSpecialization_isPrimitive
  · have hdegree : branchSexticSpecialization.natDegree = 6 := by
      unfold branchSexticSpecialization
      compute_degree <;> norm_num
    rw [branchSexticSpecialization_map_mod71, hdegree]
    unfold branchSexticMod71
    compute_degree <;> norm_num
    decide
  · rw [branchSexticSpecialization_map_mod71]
    apply (irreducible_isUnit_mul ?_).mpr branchSexticMod71_irreducible
    change IsUnit (C (57 : ZMod 71))
    apply isUnit_C.mpr
    apply IsUnit.mk0
    decide

/-- The specialized sextic is irreducible over `ℚ`; this is the specialization
used in the generic sextic argument. -/
theorem branchSexticSpecialization_irreducible_rat :
    Irreducible (branchSexticSpecialization.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    branchSexticSpecialization_isPrimitive).mp
    branchSexticSpecialization_irreducible

end
end PierceLengthBound.FixedDividend
