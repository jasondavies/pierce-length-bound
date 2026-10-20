/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ShortVec

/-! Uniform counting in a primitive integer plane. The normal's largest coordinate
provides the modulus; primitivity removes its gcd factor. -/

@[expose] public section
namespace PierceLengthBound
open Finset

/-- A primitive two-variable congruence has at most `27 n` residue solutions.
The harmless factor 27 lets us reuse the three-variable congruence count. -/
theorem primitive_pair_residue_count {n : ℕ} (hn : 0 < n) (u v : ℤ)
    (hprim : ∃ e c d : ℤ, (n : ℤ) * e + u * c + v * d = 1) :
    (((Ico (0 : ℤ) n) ×ˢ (Ico (0 : ℤ) n)).filter
      fun xy => (n : ℤ) ∣ u * xy.1 + v * xy.2).card ≤ 27 * n := by
  classical
  let S := (((Ico (0 : ℤ) n) ×ˢ (Ico (0 : ℤ) n)).filter
    fun xy => (n : ℤ) ∣ u * xy.1 + v * xy.2)
  let z : Fin 3 → ℤ := ![u, v, (n : ℤ)]
  have hg : gcd4 n z = 1 := by
    obtain ⟨e, c, d, he⟩ := hprim
    have h0 := gcd4_dvd n z 0
    have h1 := gcd4_dvd n z 1
    have hm : (gcd4 n z : ℤ) ∣ (n : ℤ) := by exact_mod_cast gcd4_dvd_m n z
    have hd : (gcd4 n z : ℤ) ∣ 1 := by
      rw [← he]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left hm _)
        (dvd_mul_of_dvd_left h0 _)) (dvd_mul_of_dvd_left h1 _)
    have : gcd4 n z ∣ 1 := by exact_mod_cast hd
    exact Nat.eq_one_of_dvd_one this
  have hcount := card_dot_dvd_le hn z
  rw [hg, mul_one] at hcount
  have hinj : Function.Injective (fun p : (ℤ × ℤ) × ℤ => ![p.1.1, p.1.2, p.2]) := by
    intro p q h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simpa using Prod.ext (Prod.ext h0 h1) h2
  have hmap : ∀ p ∈ S ×ˢ Ico (0 : ℤ) n,
      (![p.1.1, p.1.2, p.2] : Fin 3 → ℤ) ∈
        (ibox3 n).filter (fun t => (n : ℤ) ∣ dot3 t z) := by
    intro p hp
    obtain ⟨hp, hk⟩ := mem_product.mp hp
    obtain ⟨hxy, hd⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro j
      have bx := mem_Ico.mp hx
      have byy := mem_Ico.mp hy
      have bk := mem_Ico.mp hk
      rw [mem_Icc]
      change -(n : ℤ) ≤ ![p.1.1, p.1.2, p.2] j ∧ ![p.1.1, p.1.2, p.2] j ≤ n
      fin_cases j <;> dsimp <;> omega
    · change (n : ℤ) ∣ p.1.1 * u + p.1.2 * v + p.2 * n
      simpa [mul_comm] using dvd_add hd (dvd_mul_left (n : ℤ) p.2)
  have hc := (card_le_card_of_injOn _ hmap hinj.injOn).trans hcount
  rw [card_product, Int.card_Ico, sub_zero, Int.toNat_natCast] at hc
  exact Nat.le_of_mul_le_mul_right (by nlinarith [hc] : S.card * n ≤ (27 * n) * n) hn

/-- For a primitive normal with a nonzero coordinate of size `n ≤ X`, the
integer points in the plane satisfy `n * count ≤ 243 X²`, uniformly. -/
theorem primitive_plane_box_count {S : Finset (Fin 3 → ℤ)} {X n : ℕ}
    (hn : 0 < n) (hnX : n ≤ X) (u v w : ℤ) (hw : w.natAbs = n)
    (hprim : ∃ e c d : ℤ, (n : ℤ) * e + u * c + v * d = 1)
    (hS : ∀ t ∈ S, (∀ j, |t j| ≤ X) ∧ u * t 0 + v * t 1 + w * t 2 = 0) :
    n * S.card ≤ 243 * X ^ 2 := by
  classical
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw; omega
  have hwd : (n : ℤ) ∣ w := by rw [← hw, Int.natCast_natAbs]; exact (abs_dvd w w).mpr (dvd_refl w)
  let K := (((Ico (0 : ℤ) n) ×ˢ (Ico (0 : ℤ) n)).filter
    fun xy => (n : ℤ) ∣ u * xy.1 + v * xy.2)
  let key := fun t : Fin 3 → ℤ => (t 0 % (n : ℤ), t 1 % (n : ℤ))
  have hmaps : ∀ t ∈ S, key t ∈ K := by
    intro t ht
    refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ico.mpr
      ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩,
      mem_Ico.mpr ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩⟩, ?_⟩
    have he : (n : ℤ) ∣ u * t 0 + v * t 1 := by
      rw [show u * t 0 + v * t 1 = -(w * t 2) by linarith [(hS t ht).2]]
      exact dvd_neg.mpr (dvd_mul_of_dvd_left hwd _)
    have hd : (n : ℤ) ∣ u * (t 0 - t 0 % n) + v * (t 1 - t 1 % n) :=
      dvd_add (dvd_mul_of_dvd_right (Int.dvd_self_sub_emod ..) _)
        (dvd_mul_of_dvd_right (Int.dvd_self_sub_emod ..) _)
    convert dvd_sub he hd using 1
    dsimp [key]
    ring
  have hfiber (r : ℤ × ℤ) : (S.filter fun t => key t = r).card ≤ (2 * X / n + 1) ^ 2 := by
    let B := ((Icc (-(X : ℤ)) X).filter fun x => (n : ℤ) ∣ x - r.1) ×ˢ
      ((Icc (-(X : ℤ)) X).filter fun y => (n : ℤ) ∣ y - r.2)
    have hmap : ∀ t ∈ S.filter (fun t => key t = r), (t 0, t 1) ∈ B := by
      intro t ht
      obtain ⟨ht, hr⟩ := mem_filter.mp ht
      have hx : t 0 % (n : ℤ) = r.1 := congrArg Prod.fst hr
      have hy : t 1 % (n : ℤ) = r.2 := congrArg Prod.snd hr
      exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr (abs_le.mp ((hS t ht).1 0)),
        hx ▸ Int.dvd_self_sub_emod⟩,
        mem_filter.mpr ⟨mem_Icc.mpr (abs_le.mp ((hS t ht).1 1)),
        hy ▸ Int.dvd_self_sub_emod⟩⟩
    have hi : Set.InjOn (fun t : Fin 3 → ℤ => (t 0, t 1)) (S.filter fun t => key t = r) := by
      intro t ht t' ht' he
      have h0 := congrArg Prod.fst he
      have h1 := congrArg Prod.snd he
      have e := (hS t (mem_filter.mp ht).1).2
      have e' := (hS t' (mem_filter.mp ht').1).2
      have h2 : t 2 = t' 2 := by
        apply mul_left_cancel₀ hw0
        linear_combination e - e' - u * h0 - v * h1
      funext j
      fin_cases j <;> assumption
    calc (S.filter fun t => key t = r).card ≤ B.card := card_le_card_of_injOn _ hmap hi
      _ ≤ (2 * X / n + 1) ^ 2 := by
        rw [card_product, pow_two]
        exact Nat.mul_le_mul (card_Icc_dvd_le hn _) (card_Icc_dvd_le hn _)
  have hc : S.card ≤ (2 * X / n + 1) ^ 2 * (27 * n) :=
    (card_le_mul_card_image_of_maps_to hmaps _ (fun r _ => hfiber r)).trans
      (Nat.mul_le_mul_left _ (primitive_pair_residue_count hn u v hprim))
  have hround : n * (2 * X / n + 1) ≤ 3 * X := by
    have := Nat.div_mul_le_self (2 * X) n
    nlinarith
  have hsq := Nat.pow_le_pow_left hround 2
  nlinarith

/-- Coordinate-independent version of the primitive plane bound. -/
theorem primitive_plane_count {S : Finset (Fin 3 → ℤ)} {X : ℕ}
    (z c : Fin 3 → ℤ) (hc : dot3 c z = 1) (j : Fin 3)
    (hj : 0 < (z j).natAbs) (hjX : (z j).natAbs ≤ X)
    (hS : ∀ t ∈ S, (∀ k, |t k| ≤ X) ∧ dot3 z t = 0) :
    (z j).natAbs * S.card ≤ 243 * X ^ 2 := by
  classical
  let rot := fun t : Fin 3 → ℤ => ![t (j + 1), t (j + 2), t j]
  have hi : Function.Injective rot := by
    intro t t' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    dsimp [rot] at h0 h1 h2
    funext k
    fin_cases j <;> fin_cases k <;> norm_num at h0 h1 h2 ⊢ <;> assumption
  have hprim : ∃ e a b : ℤ, ((z j).natAbs : ℤ) * e + z (j + 1) * a +
      z (j + 2) * b = 1 := by
    refine ⟨Int.sign (z j) * c j, c (j + 1), c (j + 2), ?_⟩
    rw [← mul_assoc, mul_comm ((z j).natAbs : ℤ), Int.sign_mul_natAbs]
    fin_cases j <;> norm_num [dot3] at hc ⊢ <;> linear_combination hc
  have hb : ∀ t ∈ S.image rot, (∀ k, |t k| ≤ X) ∧
      z (j + 1) * t 0 + z (j + 2) * t 1 + z j * t 2 = 0 := by
    intro t ht
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ht
    obtain ⟨hb, he⟩ := hS v hv
    constructor
    · intro k
      fin_cases k
      · exact hb (j + 1)
      · exact hb (j + 2)
      · exact hb j
    · dsimp [rot]
      fin_cases j <;> norm_num [dot3] at he ⊢ <;> linear_combination he
  have h := primitive_plane_box_count hj hjX (z (j + 1)) (z (j + 2)) (z j)
    rfl hprim hb
  rwa [card_image_of_injective S hi] at h

end PierceLengthBound
