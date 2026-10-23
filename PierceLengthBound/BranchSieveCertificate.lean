/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveSpecialization
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic

/-! An explicit finite-field irreducibility certificate for the sextic specialization
used in the branch-sieve argument. All modular arithmetic is checked by the Lean
kernel. The proof excludes irreducible factors of degrees one, two, and three using
Frobenius congruences and explicit Bézout identities. -/

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

private def branchFrobeniusRemainder1 : (ZMod 71)[X] :=
  14 * X ^ 5 + 33 * X ^ 4 + 31 * X ^ 3 + 34 * X ^ 2 + 48 * X

private lemma branchFrobeniusStep1 :
    branchSexticMod71 ∣ X ^ 71 - branchFrobeniusRemainder1 := by
  let r2 : (ZMod 71)[X] := X ^ 2
  have c2 : branchSexticMod71 ∣ (X * X) - r2 := by
    refine ⟨0, ?_⟩
    dsimp [r2, branchSexticMod71]
    ring
  have h2 : branchSexticMod71 ∣ X ^ 2 - r2 := by
    simpa only [pow_two] using c2
  let r4 : (ZMod 71)[X] := X ^ 4
  have c4 : branchSexticMod71 ∣ (r2 * r2) - r4 := by
    refine ⟨0, ?_⟩
    dsimp [r2, r4, branchSexticMod71]
    ring
  have h4 : branchSexticMod71 ∣ X ^ 4 - r4 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h2 2) (by simpa only [pow_two] using c4)
  let r8 : (ZMod 71)[X] := 16 * X ^ 5 + 18 * X ^ 4 + 41 * X ^ 3 + 52 * X ^ 2 + 51 * X + 23
  have c8 : branchSexticMod71 ∣ (r4 * r4) - r8 := by
    refine ⟨X ^ 2 + 51 * X + 59, ?_⟩
    dsimp [r4, r8, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : branchSexticMod71 ∣ X ^ 8 - r8 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h4 2) (by simpa only [pow_two] using c8)
  let r16 : (ZMod 71)[X] := 13 * X ^ 5 + 50 * X ^ 4 + 3 * X ^ 3 + 32 * X ^ 2 + 24 * X + 8
  have c16 : branchSexticMod71 ∣ (r8 * r8) - r16 := by
    refine ⟨43 * X ^ 4 + 37 * X ^ 2 + 51 * X + 65, ?_⟩
    dsimp [r8, r16, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : branchSexticMod71 ∣ X ^ 16 - r16 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h8 2) (by simpa only [pow_two] using c16)
  let r32 : (ZMod 71)[X] := 32 * X ^ 5 + 36 * X ^ 4 + 66 * X ^ 3 + 11 * X ^ 2 + 23 * X + 66
  have c32 : branchSexticMod71 ∣ (r16 * r16) - r32 := by
    refine ⟨27 * X ^ 4 + 50 * X ^ 3 + 39 * X ^ 2 + 8 * X + 36, ?_⟩
    dsimp [r16, r32, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : branchSexticMod71 ∣ X ^ 32 - r32 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h16 2) (by simpa only [pow_two] using c32)
  let r64 : (ZMod 71)[X] := 18 * X ^ 5 + 29 * X ^ 4 + 16 * X ^ 3 + 58 * X ^ 2 + 64 * X + 21
  have c64 : branchSexticMod71 ∣ (r32 * r32) - r64 := by
    refine ⟨30 * X ^ 4 + 47 * X ^ 2 + 19 * X + 70, ?_⟩
    dsimp [r32, r64, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h64 : branchSexticMod71 ∣ X ^ 64 - r64 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h32 2) (by simpa only [pow_two] using c64)
  let r68 : (ZMod 71)[X] := 59 * X ^ 5 + 56 * X ^ 4 + 53 * X ^ 3 + 21 * X ^ 2 + 52 * X + 61
  have c68 : branchSexticMod71 ∣ (r64 * r4) - r68 := by
    refine ⟨18 * X ^ 3 + 24 * X ^ 2 + X + 33, ?_⟩
    dsimp [r64, r4, r68, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h68 : branchSexticMod71 ∣ X ^ 68 - r68 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h64 h4) c68
  let r70 : (ZMod 71)[X] := 14 * X ^ 4 + 33 * X ^ 3 + 31 * X ^ 2 + 34 * X + 48
  have c70 : branchSexticMod71 ∣ (r68 * r2) - r70 := by
    refine ⟨59 * X + 12, ?_⟩
    dsimp [r68, r2, r70, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h70 : branchSexticMod71 ∣ X ^ 70 - r70 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h68 h2) c70
  let r71 : (ZMod 71)[X] := 14 * X ^ 5 + 33 * X ^ 4 + 31 * X ^ 3 + 34 * X ^ 2 + 48 * X
  have c71 : branchSexticMod71 ∣ (r70 * X) - r71 := by
    refine ⟨0, ?_⟩
    dsimp [r70, r71, branchSexticMod71]
    ring
  have h71 : branchSexticMod71 ∣ X ^ 71 - r71 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h70 (by simp : branchSexticMod71 ∣ X ^ 1 - X)) c71
  exact h71

private lemma branchFrobeniusCoprime1 :
    IsCoprime branchSexticMod71 (branchFrobeniusRemainder1 - X) := by
  refine ⟨9 * X ^ 4 + 25 * X ^ 3 + 62 * X ^ 2 + 30 * X + 53,
    45 * X ^ 5 + X ^ 4 + 19 * X ^ 3 + 27 * X ^ 2 + 6 * X + 9, ?_⟩
  unfold branchSexticMod71 branchFrobeniusRemainder1
  ring_nf
  reduce_mod_char

private def branchFrobeniusRemainder2 : (ZMod 71)[X] :=
  36 * X ^ 5 + 48 * X ^ 4 + 49 * X ^ 3 + 53 * X ^ 2 + 36 * X + 42

private lemma branchFrobeniusStep2 :
    branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 71 - branchFrobeniusRemainder2 := by
  let r2 : (ZMod 71)[X] := 22 * X ^ 5 + 66 * X ^ 4 + 11 * X ^ 3 + 53 * X ^ 2 + 10 * X + 25
  have c2 : branchSexticMod71 ∣ (branchFrobeniusRemainder1 * branchFrobeniusRemainder1) - r2 := by
    refine ⟨54 * X ^ 4 + 57 * X ^ 3 + 11 * X ^ 2 + 68 * X + 24, ?_⟩
    dsimp [branchFrobeniusRemainder1, r2, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 2 - r2 := by
    simpa only [pow_two] using c2
  let r4 : (ZMod 71)[X] := 19 * X ^ 5 + 34 * X ^ 4 + 57 * X ^ 3 + 11 * X ^ 2 + 47 * X + 46
  have c4 : branchSexticMod71 ∣ (r2 * r2) - r4 := by
    refine ⟨58 * X ^ 4 + 40 * X ^ 3 + 24 * X ^ 2 + 12 * X + 15, ?_⟩
    dsimp [r2, r4, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 4 - r4 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h2 2) (by simpa only [pow_two] using c4)
  let r8 : (ZMod 71)[X] := 30 * X ^ 5 + 38 * X ^ 4 + 70 * X ^ 3 + 30 * X ^ 2 + 32 * X + 69
  have c8 : branchSexticMod71 ∣ (r4 * r4) - r8 := by
    refine ⟨6 * X ^ 4 + 36 * X ^ 3 + 59 * X ^ 2 + 49 * X + 3, ?_⟩
    dsimp [r4, r8, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 8 - r8 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h4 2) (by simpa only [pow_two] using c8)
  let r16 : (ZMod 71)[X] := 25 * X ^ 5 + 12 * X ^ 4 + 62 * X ^ 3 + 64 * X ^ 2 + 34 * X + 5
  have c16 : branchSexticMod71 ∣ (r8 * r8) - r16 := by
    refine ⟨48 * X ^ 4 + 42 * X ^ 3 + 9 * X ^ 2 + 63 * X + 18, ?_⟩
    dsimp [r8, r16, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 16 - r16 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h8 2) (by simpa only [pow_two] using c16)
  let r32 : (ZMod 71)[X] := 55 * X ^ 5 + 9 * X ^ 4 + 30 * X ^ 3 + 64 * X ^ 2 + 19 * X + 63
  have c32 : branchSexticMod71 ∣ (r16 * r16) - r32 := by
    refine ⟨57 * X ^ 4 + 28 * X ^ 3 + 3 * X ^ 2 + 47 * X + 45, ?_⟩
    dsimp [r16, r32, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 32 - r32 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h16 2) (by simpa only [pow_two] using c32)
  let r64 : (ZMod 71)[X] := 5 * X ^ 5 + 59 * X ^ 4 + 44 * X ^ 3 + 54 * X ^ 2 + 15 * X + 32
  have c64 : branchSexticMod71 ∣ (r32 * r32) - r64 := by
    refine ⟨43 * X ^ 4 + 59 * X ^ 3 + 34 * X ^ 2 + 52 * X + 63, ?_⟩
    dsimp [r32, r64, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h64 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 64 - r64 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h32 2) (by simpa only [pow_two] using c64)
  let r68 : (ZMod 71)[X] := 68 * X ^ 5 + 30 * X ^ 4 + 66 * X ^ 3 + 66 * X ^ 2 + 20 * X + 51
  have c68 : branchSexticMod71 ∣ (r64 * r4) - r68 := by
    refine ⟨24 * X ^ 4 + 30 * X ^ 3 + 23 * X ^ 2 + 2 * X + 53, ?_⟩
    dsimp [r64, r4, r68, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h68 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 68 - r68 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h64 h4) c68
  let r70 : (ZMod 71)[X] := 32 * X ^ 5 + 61 * X ^ 4 + 7 * X ^ 3 + 41 * X ^ 2 + 67 * X + 36
  have c70 : branchSexticMod71 ∣ (r68 * r2) - r70 := by
    refine ⟨5 * X ^ 4 + 7 * X ^ 3 + 63 * X ^ 2 + 56 * X + 63, ?_⟩
    dsimp [r68, r2, r70, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h70 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 70 - r70 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h68 h2) c70
  let r71 : (ZMod 71)[X] := 36 * X ^ 5 + 48 * X ^ 4 + 49 * X ^ 3 + 53 * X ^ 2 + 36 * X + 42
  have c71 : branchSexticMod71 ∣ (r70 * branchFrobeniusRemainder1) - r71 := by
    refine ⟨22 * X ^ 4 + 50 * X ^ 3 + 68 * X ^ 2 + 25 * X + 46, ?_⟩
    dsimp [r70, branchFrobeniusRemainder1, r71, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h71 : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 71 - r71 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h70
        (by simp : branchSexticMod71 ∣ branchFrobeniusRemainder1 ^ 1 -
          branchFrobeniusRemainder1)) c71
  exact h71

private lemma branchFrobeniusCoprime2 :
    IsCoprime branchSexticMod71 (branchFrobeniusRemainder2 - X) := by
  refine ⟨20 * X ^ 4 + 34 * X ^ 3 + 31 * X ^ 2 + 13 * X + 24,
    31 * X ^ 5 + 61 * X ^ 4 + 42 * X ^ 3 + 61 * X ^ 2 + 39 * X + 4, ?_⟩
  unfold branchSexticMod71 branchFrobeniusRemainder2
  ring_nf
  reduce_mod_char

private def branchFrobeniusRemainder3 : (ZMod 71)[X] :=
  37 * X ^ 5 + 22 * X ^ 4 + 60 * X ^ 3 + 13 * X ^ 2 + 66 * X + 35

private lemma branchFrobeniusStep3 :
    branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 71 - branchFrobeniusRemainder3 := by
  let r2 : (ZMod 71)[X] := 17 * X ^ 5 + 70 * X ^ 4 + 40 * X ^ 3 + X ^ 2 + 25 * X + 3
  have c2 : branchSexticMod71 ∣ (branchFrobeniusRemainder2 * branchFrobeniusRemainder2) - r2 := by
    refine ⟨18 * X ^ 4 + 43 * X ^ 3 + 41 * X ^ 2 + 9 * X + 39, ?_⟩
    dsimp [branchFrobeniusRemainder2, r2, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 2 - r2 := by
    simpa only [pow_two] using c2
  let r4 : (ZMod 71)[X] := 28 * X ^ 5 + 6 * X ^ 4 + 36 * X ^ 3 + 48 * X ^ 2 + 7 * X + 3
  have c4 : branchSexticMod71 ∣ (r2 * r2) - r4 := by
    refine ⟨5 * X ^ 4 + 8 * X ^ 3 + 64 * X ^ 2 + 60 * X + 34, ?_⟩
    dsimp [r2, r4, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 4 - r4 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h2 2) (by simpa only [pow_two] using c4)
  let r8 : (ZMod 71)[X] := 57 * X ^ 5 + 58 * X ^ 4 + 34 * X ^ 3 + 4 * X ^ 2 + 2 * X + 53
  have c8 : branchSexticMod71 ∣ (r4 * r4) - r8 := by
    refine ⟨3 * X ^ 4 + 63 * X ^ 3 + 53 * X ^ 2 + 57 * X + 11, ?_⟩
    dsimp [r4, r8, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 8 - r8 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h4 2) (by simpa only [pow_two] using c8)
  let r16 : (ZMod 71)[X] := 42 * X ^ 5 + 62 * X ^ 4 + 15 * X ^ 3 + 60 * X ^ 2 + 27 * X + 45
  have c16 : branchSexticMod71 ∣ (r8 * r8) - r16 := by
    refine ⟨54 * X ^ 4 + 65 * X ^ 3 + 22 * X ^ 2 + 13 * X + 19, ?_⟩
    dsimp [r8, r16, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 16 - r16 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h8 2) (by simpa only [pow_two] using c16)
  let r32 : (ZMod 71)[X] := 39 * X ^ 5 + 54 * X ^ 4 + 16 * X ^ 3 + 62 * X ^ 2 + 6 * X + 41
  have c32 : branchSexticMod71 ∣ (r16 * r16) - r32 := by
    refine ⟨60 * X ^ 4 + 32 * X ^ 3 + 50 * X ^ 2 + 52 * X + 1, ?_⟩
    dsimp [r16, r32, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 32 - r32 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h16 2) (by simpa only [pow_two] using c32)
  let r64 : (ZMod 71)[X] := 13 * X ^ 5 + 67 * X ^ 4 + 55 * X ^ 3 + 68 * X ^ 2 + 65 * X + 61
  have c64 : branchSexticMod71 ∣ (r32 * r32) - r64 := by
    refine ⟨30 * X ^ 4 + 62 * X ^ 3 + 7 * X ^ 2 + 26 * X + 21, ?_⟩
    dsimp [r32, r64, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h64 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 64 - r64 := by
    simpa only [← pow_mul] using
      remainder_trans (remainder_pow h32 2) (by simpa only [pow_two] using c64)
  let r68 : (ZMod 71)[X] := 50 * X ^ 5 + 24 * X ^ 3 + 61 * X ^ 2 + 65 * X + 61
  have c68 : branchSexticMod71 ∣ (r64 * r4) - r68 := by
    refine ⟨9 * X ^ 4 + 70 * X ^ 3 + 9 * X + 5, ?_⟩
    dsimp [r64, r4, r68, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h68 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 68 - r68 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h64 h4) c68
  let r70 : (ZMod 71)[X] := 67 * X ^ 5 + 19 * X ^ 4 + 24 * X ^ 3 + 36 * X ^ 2 + 45 * X + 12
  have c70 : branchSexticMod71 ∣ (r68 * r2) - r70 := by
    refine ⟨69 * X ^ 4 + 61 * X ^ 3 + 24 * X ^ 2 + 47 * X + 46, ?_⟩
    dsimp [r68, r2, r70, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h70 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 70 - r70 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h68 h2) c70
  let r71 : (ZMod 71)[X] := 37 * X ^ 5 + 22 * X ^ 4 + 60 * X ^ 3 + 13 * X ^ 2 + 66 * X + 35
  have c71 : branchSexticMod71 ∣ (r70 * branchFrobeniusRemainder2) - r71 := by
    refine ⟨69 * X ^ 4 + 35 * X ^ 3 + 66 * X + 7, ?_⟩
    dsimp [r70, branchFrobeniusRemainder2, r71, branchSexticMod71]
    ring_nf
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h71 : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 71 - r71 := by
    simpa only [← pow_add] using
      remainder_trans (remainder_mul h70
        (by simp : branchSexticMod71 ∣ branchFrobeniusRemainder2 ^ 1 -
          branchFrobeniusRemainder2)) c71
  exact h71

private lemma branchFrobeniusCoprime3 :
    IsCoprime branchSexticMod71 (branchFrobeniusRemainder3 - X) := by
  refine ⟨25 * X ^ 4 + 11 * X ^ 3 + 53 * X ^ 2 + 59 * X + 48,
    7 * X ^ 5 + 30 * X ^ 4 + 65 * X ^ 3 + 64 * X ^ 2 + 25 * X + 40, ?_⟩
  unfold branchSexticMod71 branchFrobeniusRemainder3
  ring_nf
  reduce_mod_char

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

/-- The sextic defining the six places at infinity is irreducible modulo 71. -/
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

/-- The exact specialized sextic is irreducible over the integers. -/
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

/-- The characteristic-zero specialization needed for the generic sextic argument. -/
theorem branchSexticSpecialization_irreducible_rat :
    Irreducible (branchSexticSpecialization.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    branchSexticSpecialization_isPrimitive).mp
    branchSexticSpecialization_irreducible

end
end PierceLengthBound.FixedDividend
