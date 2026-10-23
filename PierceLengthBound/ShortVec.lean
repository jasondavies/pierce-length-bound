/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.MinorCount
public import PierceLengthBound.Reduce3

/-!
# The pattern lattice and its short vectors

For a minor vector `p` with pivot `τ` and `m = p_τ ≠ 0`, the five gaps are recovered from the
three pivot gaps `k' = (k_{c₁}, k_{c₂}, k_{c₃})` by `m kᶜ = Lᶜ · k'` (`lift_row`), where the rows
`Lᶜ` are `m eₐ` on pivot columns and `u`, `v` on the other two. So `k'` lies in the lattice
`Λ_p = {x : m ∣ u·x, m ∣ v·x}` (`pivLat`). The rows in columns `1, 2, 3` have determinant
`m² p₁₂₃` (`lift_det`). This is Lemma 9.1 of the paper, with columns `1, 2, 3` in place of
`0, 1, 2`.

The cross relation `m ∣ u × v` makes the index at most `|m|`, so `Λ_p` has a nonzero vector of
sup norm at most `L` once `(L+1)³ > |m|` (`pivLat_short`, Lemma 9.3). Let `λ(p)` (`shortR`) be
the least sup norm of a nonzero vector of `Λ_p`. Counting `n ∣ w·x` in a box
(`card_dot_dvd_le`, Lemma 9.5) and the minor-vector encoding with this divisibility condition
(`minor_vector_count_dot`) show that few patterns have a short vector:
`#{p : λ(p) ≤ R} ≤ 393660 R³ Y⁴ τ₀²` for minor vectors of height `≤ Y`, where `τ(m) ≤ τ₀` for
`m ≤ Y` (`short_count`, Proposition 9.6).
-/

@[expose] public section

namespace PierceLengthBound
open scoped Matrix
open Matrix (vec3_dotProduct)

open Finset

/-- The position of each column relative to the pivot: `0, 1, 2` for the pivot columns, `3, 4`
for the other two. -/
def role : Fin 10 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![0, 1, 3, 2, 4], ![0, 1, 3, 4, 2],
  ![0, 3, 1, 2, 4], ![0, 3, 1, 4, 2], ![0, 3, 4, 1, 2], ![3, 0, 1, 2, 4], ![3, 0, 1, 4, 2],
  ![3, 0, 4, 1, 2], ![3, 4, 0, 1, 2]]

/-- The pivot columns. -/
def pcol (τ : Fin 10) : Fin 3 → Fin 5 := ![(trip τ).1, (trip τ).2.1, (trip τ).2.2]

/-- The lifting rows. -/
def Lrow (p : Fin 10 → ℤ) (τ : Fin 10) (c : Fin 5) : Fin 3 → ℤ :=
  ![![p τ, 0, 0], ![0, p τ, 0], ![0, 0, p τ], uVec p τ, vVec p τ] (role τ c)

/-- **Lifting** (Lemma 9.1). Each row of the matrix is recovered from its pivot columns:
`p_τ M_{rc} = L_c · (M_{r,c₁}, M_{r,c₂}, M_{r,c₃})`. -/
theorem lift_row (M : Fin 3 → Fin 5 → ℤ) (τ : Fin 10) (r : Fin 3) (c : Fin 5) :
    plk M τ * M r c = Lrow (plk M) τ c ⬝ᵥ (fun a => M r (pcol τ a)) := by
  fin_cases τ <;> fin_cases c <;>
    simp only [plk, minor3, Fin.isValue, trip, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, Fin.reduceFinMk, vec3_dotProduct, Lrow, Nat.succ_eq_add_one,
        Nat.reduceAdd, role, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one, uVec, puS,
        Int.cast_id, Int.reduceNeg, puX, neg_mul, one_mul, neg_add_rev, neg_sub, vVec, pvS, pvX,
        pcol, zero_mul, add_zero, zero_add, Fin.zero_eta] <;>
    fin_cases r <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> ring

/-- **The determinant of the rows `1, 2, 3`**: `det(L₁, L₂, L₃) = p_τ² p₁₂₃`. -/
theorem lift_det (M : Fin 3 → Fin 5 → ℤ) (τ : Fin 10) :
    det3 (Lrow (plk M) τ 1) (Lrow (plk M) τ 2) (Lrow (plk M) τ 3) = plk M τ ^ 2 * plk M 6 := by
  fin_cases τ <;>
    simp [Lrow, role, det3_apply, plk, trip, minor3, uVec, vVec, puX, puS, pvX, pvS] <;> ring

/-! ### The lattice -/

/-- The pattern lattice in pivot coordinates. -/
def pivLat (p : Fin 10 → ℤ) : AddSubgroup (Fin 3 → ℤ) where
  carrier := {x | p (piv p) ∣ uVec p (piv p) ⬝ᵥ x ∧ p (piv p) ∣ vVec p (piv p) ⬝ᵥ x}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, dotProduct_add] at hx hy ⊢
    exact ⟨dvd_add hx.1 hy.1, dvd_add hx.2 hy.2⟩
  zero_mem' := by simp [vec3_dotProduct]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, dotProduct_neg, dvd_neg] at hx ⊢
    exact hx

lemma dvd_dotProduct_of_dvd {d : ℤ} {x : Fin 3 → ℤ} (h : ∀ j, d ∣ x j) (w : Fin 3 → ℤ) :
    d ∣ w ⬝ᵥ x :=
  Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (h j) _

lemma pivLat_of_dvd {p : Fin 10 → ℤ} {x : Fin 3 → ℤ} (h : ∀ j, p (piv p) ∣ x j) :
    x ∈ pivLat p := ⟨dvd_dotProduct_of_dvd h _, dvd_dotProduct_of_dvd h _⟩

/-- `Λ_p` has a nonzero vector of sup norm at most `R`. -/
def HasShort (p : Fin 10 → ℤ) (R : ℕ) : Prop := ∃ x ∈ pivLat p, x ≠ 0 ∧ ∀ j, |x j| ≤ R

/-- **Pigeonhole** (Lemma 9.3). The index of `Λ_p` is at most `|m|`, so if `(L+1)³ > |m|`, then
`Λ_p` has a nonzero vector of sup norm at most `L`. -/
theorem pivLat_short {p : Fin 10 → ℤ} (hpl : PluckerRel p) (hm : p (piv p) ≠ 0) {L : ℕ}
    (hL : (p (piv p)).natAbs < (L + 1) ^ 3) : HasShort p L := by
  classical
  set τ := piv p
  set m := (p τ).natAbs
  have hm0 : 0 < m := Int.natAbs_pos.mpr hm
  have hd : ∀ a, (m : ℤ) ∣ (uVec p τ ⨯₃ vVec p τ) a := fun a =>
    Int.natAbs_dvd.mpr (piv_cross hpl a)
  obtain ⟨n, u', lam, hn, hmg, hu, hv⟩ := cross_cong hm0 hd
  set g : ℤ := (gcd4 m (uVec p τ) : ℤ)
  have hg : 0 < g := Int.natCast_pos.mpr (gcd4_pos hm0 _)
  choose w hw using hv
  set ψ : (Fin 3 → ℤ) → ℤ × ℤ := fun x =>
    ((u' ⬝ᵥ x) % n, (lam * ((u' ⬝ᵥ x) / n) + w ⬝ᵥ x) % g)
  have hmaps : ∀ x ∈ Fintype.piFinset (fun _ : Fin 3 => Icc (0 : ℤ) L),
      ψ x ∈ Ico (0 : ℤ) n ×ˢ Ico (0 : ℤ) g := fun x _ =>
    mem_product.mpr ⟨mem_Ico.mpr ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩,
      mem_Ico.mpr ⟨Int.emod_nonneg _ hg.ne', Int.emod_lt_of_pos _ hg⟩⟩
  have hcard : (Ico (0 : ℤ) n ×ˢ Ico (0 : ℤ) g).card <
      (Fintype.piFinset fun _ : Fin 3 => Icc (0 : ℤ) L).card := by
    rw [card_product, Int.card_Ico, Int.card_Ico, Fintype.card_piFinset, Fin.prod_univ_three,
      Int.card_Icc]
    have e : ((n - 0).toNat * (g - 0).toNat : ℤ) = m := by
      rw [sub_zero, sub_zero, Int.toNat_of_nonneg hn.le, Int.toNat_of_nonneg hg.le, hmg, mul_comm]
    have e' : (n - 0).toNat * (g - 0).toNat = m := by exact_mod_cast e
    rw [e', show ((L : ℤ) + 1 - 0).toNat = L + 1 by omega]
    calc m < (L + 1) ^ 3 := hL
      _ = (L + 1) * (L + 1) * (L + 1) := by ring
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [ψ, Prod.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  set A := u' ⬝ᵥ x
  set B := u' ⬝ᵥ y
  have hAB : A - B = n * (A / n - B / n) := by
    have e1 := Int.mul_ediv_add_emod A n
    have e2 := Int.mul_ediv_add_emod B n
    linear_combination -e1 + e2 + h1
  have hdu : ∀ z, uVec p τ ⬝ᵥ z = g * u' ⬝ᵥ z := fun z => by
    simp only [vec3_dotProduct, hu]; ring
  have hdv : ∀ z, vVec p τ ⬝ᵥ z = lam * u' ⬝ᵥ z + n * w ⬝ᵥ z := fun z => by
    have := hw 0; have := hw 1; have := hw 2
    simp only [vec3_dotProduct]; linear_combination (z 0) * hw 0 + (z 1) * hw 1 + (z 2) * hw 2
  have hg2 : g ∣ lam * (A / n - B / n) + w ⬝ᵥ (x - y) := by
    have := Int.ModEq.dvd h2.symm
    rw [dotProduct_sub]
    convert this using 1; ring
  refine ⟨x - y, ⟨Int.natAbs_dvd.mp ?_, Int.natAbs_dvd.mp ?_⟩, sub_ne_zero.mpr hne, fun j => ?_⟩
  · rw [hdu, dotProduct_sub, hAB]
    exact ⟨A / n - B / n, by rw [hmg]; ring⟩
  · rw [hdv, dotProduct_sub, hAB]
    obtain ⟨k, hk⟩ := hg2
    refine ⟨k, ?_⟩
    rw [hmg]
    linear_combination n * hk
  · have hxj := mem_Icc.mp (Fintype.mem_piFinset.mp hx j)
    have hyj := mem_Icc.mp (Fintype.mem_piFinset.mp hy j)
    simp only [Pi.sub_apply]
    rw [abs_le]; constructor <;> linarith

/-- The minimum `λ(p)`: the least sup norm of a nonzero vector of `Λ_p`. -/
noncomputable def shortR (p : Fin 10 → ℤ) : ℕ := sInf {R : ℕ | HasShort p R}

lemma hasShort_nonempty {p : Fin 10 → ℤ} (hm : p (piv p) ≠ 0) :
    HasShort p (p (piv p)).natAbs := by
  refine ⟨![p (piv p), 0, 0], pivLat_of_dvd fun j => ?_, ?_, fun j => ?_⟩
  · fin_cases j <;> simp
  · intro h; apply hm; simpa using congrFun h 0
  · fin_cases j <;> simp

/-- **The shortest vector.** If `m ≠ 0`, then `λ(p) ≥ 1` is attained and every nonzero
`x ∈ Λ_p` has `λ(p)² ≤ |x|²`. -/
theorem shortR_spec {p : Fin 10 → ℤ} (hm : p (piv p) ≠ 0) :
    1 ≤ shortR p ∧ HasShort p (shortR p) ∧
      ∀ x ∈ pivLat p, x ≠ 0 → (shortR p : ℤ) ^ 2 ≤ nrm3 x := by
  have hne : ({R : ℕ | HasShort p R} : Set ℕ).Nonempty := ⟨_, hasShort_nonempty hm⟩
  have hmem : HasShort p (shortR p) := Nat.sInf_mem hne
  refine ⟨?_, hmem, fun x hx hx0 => ?_⟩
  · by_contra h0
    push Not at h0
    obtain ⟨x, -, hx0, hb⟩ := hmem
    apply hx0
    funext j
    have := hb j
    rw [show shortR p = 0 by omega] at this
    simpa using this
  · have : ∃ j, (shortR p : ℤ) ≤ |x j| := by
      by_contra h
      push Not at h
      have h1 : 1 ≤ shortR p := by
        by_contra h0
        push Not at h0
        apply hx0; funext j; have := h j; rw [show shortR p = 0 by omega] at this
        simp only [CharP.cast_eq_zero] at this; exact absurd this (not_lt.mpr (abs_nonneg _))
      have : HasShort p (shortR p - 1) := ⟨x, hx, hx0, fun j => by
        have := h j; push_cast [h1]; omega⟩
      exact Nat.notMem_of_lt_sInf (s := {R : ℕ | HasShort p R}) (m := shortR p - 1)
        (show shortR p - 1 < shortR p by omega) this
    obtain ⟨j, hj⟩ := this
    have h0 : (0 : ℤ) ≤ shortR p := by positivity
    have : (shortR p : ℤ) ^ 2 ≤ x j ^ 2 := by
      rw [← sq_abs (x j)]; exact pow_le_pow_left₀ h0 hj 2
    have : x j ^ 2 ≤ nrm3 x := by
      simp only [nrm3, vec3_dotProduct]
      fin_cases j <;> simp <;> nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1),
        mul_self_nonneg (x 2)]
    linarith

/-- The minimum of the pattern lattice is positive when `p 0 ≠ 0`. -/
lemma shortR_pos {p : Fin 10 → ℤ} (h0 : p 0 ≠ 0) : 0 < shortR p :=
  (shortR_spec (piv_ne_zero h0)).1

lemma shortR_le {p : Fin 10 → ℤ} {L : ℕ} (h : HasShort p L) : shortR p ≤ L := Nat.sInf_le h

/-! ### Counting patterns with a short vector -/

/-- **Solutions of `n ∣ w·x` in a box** (Lemma 9.5): at most `27 n² gcd(n, x)` of the
`w ∈ [-n, n]³`. -/
theorem card_dot_dvd_le {n : ℕ} (hn : 0 < n) (x : Fin 3 → ℤ) :
    ((ibox3 n).filter fun w => (n : ℤ) ∣ w ⬝ᵥ x).card ≤ 27 * n ^ 2 * gcd4 n x := by
  classical
  set e := gcd4 n x
  have he0 : 0 < e := gcd4_pos hn x
  have hen : e ∣ n := gcd4_dvd_m n x
  obtain ⟨n', hn'⟩ := hen
  have hn'0 : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h, mul_zero] at hn'; omega
    · exact h
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  set K := (Fintype.piFinset fun _ : Fin 3 => Ico (0 : ℤ) n).filter fun w =>
    (n : ℤ) ∣ w ⬝ᵥ x
  -- step 1: reduce modulo `n`
  have step1 : ((ibox3 n).filter fun w => (n : ℤ) ∣ w ⬝ᵥ x).card ≤ 27 * K.card := by
    refine card_le_mul_card_image_of_maps_to (f := fun (w : Fin 3 → ℤ) (j : Fin 3) => w j % (n : ℤ))
      (t := K) (fun w hw => ?_) 27 fun r _ => ?_
    · obtain ⟨-, hd⟩ := mem_filter.mp hw
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => mem_Ico.mpr
        ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩, ?_⟩
      have : (n : ℤ) ∣ w ⬝ᵥ x - (fun j => w j % (n : ℤ)) ⬝ᵥ x := by
        have e : w ⬝ᵥ x - (fun j => w j % (n : ℤ)) ⬝ᵥ x =
            (w 0 - w 0 % n) * x 0 + (w 1 - w 1 % n) * x 1 + (w 2 - w 2 % n) * x 2 := by
          simp only [vec3_dotProduct]; ring
        rw [e]
        exact dvd_add (dvd_add (dvd_mul_of_dvd_left (Int.dvd_self_sub_emod ..) _)
          (dvd_mul_of_dvd_left (Int.dvd_self_sub_emod ..) _))
          (dvd_mul_of_dvd_left (Int.dvd_self_sub_emod ..) _)
      have := dvd_sub hd this
      simpa using this
    · have hsub : ((ibox3 n).filter fun w => (n : ℤ) ∣ w ⬝ᵥ x).filter
          (fun w => (fun j => w j % (n : ℤ)) = r) ⊆
          Fintype.piFinset fun j => (Icc (-(n : ℤ)) n).filter fun y => (n : ℤ) ∣ y - r j := by
        intro w hw
        obtain ⟨hw1, hwr⟩ := mem_filter.mp hw
        have hb := (mem_filter.mp hw1).1
        refine Fintype.mem_piFinset.mpr fun j => mem_filter.mpr
          ⟨Fintype.mem_piFinset.mp hb j, ?_⟩
        rw [← hwr]
        exact Int.dvd_self_sub_emod ..
      refine (card_le_card hsub).trans ?_
      rw [Fintype.card_piFinset, Fin.prod_univ_three]
      have hb : ∀ c : ℤ, ((Icc (-(n : ℤ)) n).filter fun y => (n : ℤ) ∣ y - c).card ≤ 3 := by
        intro c
        refine (card_Icc_dvd_le hn c).trans ?_
        rw [Nat.mul_div_cancel _ hn]
      calc _ ≤ 3 * 3 * 3 := Nat.mul_le_mul (Nat.mul_le_mul (hb _) (hb _)) (hb _)
        _ = 27 := by norm_num
  -- step 2: a free action of `ℤ/n'` on the residues
  obtain ⟨s0, c0, c1, c2, hbz⟩ := gcd4_bezout n x
  set cc : Fin 3 → ℤ := ![c0, c1, c2]
  have hcc : cc ⬝ᵥ x = e - n * s0 := by
    simp only [vec3_dotProduct, cc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination hbz
  have step2 : K.card * n' ≤ n ^ 3 := by
    have hinj : Set.InjOn (fun wk : (Fin 3 → ℤ) × ℕ => fun j => (wk.1 j + wk.2 * cc j) % (n : ℤ))
        (K ×ˢ range n' : Finset _) := by
      intro wk hwk wk' hwk' h
      obtain ⟨hw, hk⟩ := mem_product.mp (mem_coe.mp hwk)
      obtain ⟨hw', hk'⟩ := mem_product.mp (mem_coe.mp hwk')
      have hd : ∀ j, (n : ℤ) ∣ (wk.1 j - wk'.1 j) + ((wk.2 : ℤ) - wk'.2) * cc j := by
        intro j
        have := congrFun h j
        have := Int.ModEq.dvd this.symm
        convert this using 1; ring
      have hdot : (n : ℤ) ∣ ((wk.2 : ℤ) - wk'.2) * e := by
        have h1 := (mem_filter.mp hw).2
        have h2 := (mem_filter.mp hw').2
        have h3 : (n : ℤ) ∣ (fun j => (wk.1 j - wk'.1 j) + ((wk.2 : ℤ) - wk'.2) * cc j) ⬝ᵥ x := by
          rw [dotProduct_comm]
          exact dvd_dotProduct_of_dvd hd x
        have e1 : (fun j => (wk.1 j - wk'.1 j) + ((wk.2 : ℤ) - wk'.2) * cc j) ⬝ᵥ x =
            wk.1 ⬝ᵥ x - wk'.1 ⬝ᵥ x + ((wk.2 : ℤ) - wk'.2) * cc ⬝ᵥ x := by
          simp only [vec3_dotProduct]; ring
        rw [e1, hcc] at h3
        have := dvd_sub (dvd_sub h3 h1) (dvd_neg.mpr h2)
        have h4 : (n : ℤ) ∣ ((wk.2 : ℤ) - wk'.2) * (n * s0) := dvd_mul_of_dvd_right
            (dvd_mul_right _ _) _
        have := dvd_add this h4
        convert this using 1; ring
      have hk_eq : wk.2 = wk'.2 := by
        have hnn : (n : ℤ) = e * n' := by exact_mod_cast hn'
        rw [hnn, mul_comm ((wk.2 : ℤ) - wk'.2)] at hdot
        have hd' : (n' : ℤ) ∣ (wk.2 : ℤ) - wk'.2 :=
          (mul_dvd_mul_iff_left (by exact_mod_cast he0.ne' : (e : ℤ) ≠ 0)).mp hdot
        have hk1 := mem_range.mp hk
        have hk1' := mem_range.mp hk'
        have : (wk.2 : ℤ) - wk'.2 = 0 :=
          Int.eq_zero_of_abs_lt_dvd hd' (by rw [abs_lt]; constructor <;> omega)
        omega
      have hw_eq : wk.1 = wk'.1 := by
        funext j
        have h1 := hd j
        rw [hk_eq, sub_self, zero_mul, add_zero] at h1
        have b1 := mem_Ico.mp (Fintype.mem_piFinset.mp (mem_filter.mp hw).1 j)
        have b2 := mem_Ico.mp (Fintype.mem_piFinset.mp (mem_filter.mp hw').1 j)
        have : wk.1 j - wk'.1 j = 0 :=
          Int.eq_zero_of_abs_lt_dvd h1 (by rw [abs_lt]; constructor <;> linarith)
        linarith
      exact Prod.ext hw_eq hk_eq
    have := card_le_card_of_injOn _ (t := Fintype.piFinset fun _ : Fin 3 => Ico (0 : ℤ) n)
      (fun wk _ => Fintype.mem_piFinset.mpr fun j => mem_Ico.mpr
        ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩) hinj
    rw [card_product, card_range, Fintype.card_piFinset, Fin.prod_univ_three, Int.card_Ico,
      sub_zero, Int.toNat_natCast] at this
    calc K.card * n' ≤ n * n * n := this
      _ = n ^ 3 := by ring
  have hK : K.card ≤ n ^ 2 * e := by
    have : K.card * n' ≤ (n ^ 2 * e) * n' := by
      calc K.card * n' ≤ n ^ 3 := step2
        _ = (n ^ 2 * e) * n' := by rw [hn']; ring
    exact Nat.le_of_mul_le_mul_right this hn'0
  calc _ ≤ 27 * K.card := step1
    _ ≤ 27 * (n ^ 2 * e) := Nat.mul_le_mul_left _ hK
    _ = 27 * n ^ 2 * e := by ring

lemma gcd4_dvd_gcd4 {e m : ℕ} (h : e ∣ m) (x : Fin 3 → ℤ) : gcd4 e x ∣ gcd4 m x := by
  have h1 : (gcd4 e x : ℤ) ∣ (m : ℤ) :=
    (by exact_mod_cast (gcd4_dvd_m e x).trans h : (gcd4 e x : ℤ) ∣ ((m : ℕ) : ℤ))
  have h2 : (gcd4 e x : ℤ) ∣ (Int.gcd (x 0) (Int.gcd (x 1) (x 2)) : ℤ) :=
    Int.dvd_coe_gcd (gcd4_dvd e x 0) (Int.dvd_coe_gcd (gcd4_dvd e x 1) (gcd4_dvd e x 2))
  have := Int.dvd_coe_gcd h1 h2
  exact_mod_cast this

/-- `∑_{u : m ∣ u·x} gcd(m, u)² ≤ 27 m² τ(m) gcd(m, x)`. -/
theorem sum_gcd4_sq_dot_le {m : ℕ} (hm : 0 < m) (x : Fin 3 → ℤ) :
    ∑ u ∈ (ibox3 m).filter (fun u => (m : ℤ) ∣ u ⬝ᵥ x), gcd4 m u ^ 2 ≤
      27 * m ^ 2 * m.divisors.card * gcd4 m x := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := fun u => gcd4 m u) (t := m.divisors)
    (fun u _ => Nat.mem_divisors.mpr ⟨gcd4_dvd_m m u, hm.ne'⟩)]
  calc ∑ d ∈ m.divisors, ∑ u ∈ ((ibox3 m).filter (fun u => (m : ℤ) ∣ u ⬝ᵥ x)).filter
          (fun u => gcd4 m u = d), gcd4 m u ^ 2
      ≤ ∑ _d ∈ m.divisors, 27 * m ^ 2 * gcd4 m x := by
        refine sum_le_sum fun d hd => ?_
        obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
        obtain ⟨e, he⟩ := hdm
        have he0 : 0 < e := by
          rcases Nat.eq_zero_or_pos e with h | h
          · rw [h, mul_zero] at he; omega
          · exact h
        set F := ((ibox3 m).filter (fun u => (m : ℤ) ∣ u ⬝ᵥ x)).filter fun u => gcd4 m u = d
        have hF : F.card ≤ 27 * e ^ 2 * gcd4 m x := by
          have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd0.ne'
          refine (card_le_card_of_injOn (fun u a => u a / d)
            (t := (ibox3 e).filter fun w => (e : ℤ) ∣ w ⬝ᵥ x) (fun u hu => ?_)
            (fun u hu u' hu' h => ?_)).trans ?_
          · obtain ⟨hu1, hgd⟩ := mem_filter.mp (mem_coe.mp hu)
            obtain ⟨hub, hux⟩ := mem_filter.mp hu1
            have hdv : ∀ a, u a = d * (u a / d) := fun a =>
              (Int.mul_ediv_cancel' (by rw [← hgd]; exact gcd4_dvd m u a)).symm
            refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun a => ?_, ?_⟩
            · have hb := mem_Icc.mp (Fintype.mem_piFinset.mp hub a)
              have hm' : (m : ℤ) = d * e := by exact_mod_cast he
              rw [hm', hdv a] at hb
              have hdpos : (0 : ℤ) < d := by exact_mod_cast hd0
              refine mem_Icc.mpr ⟨?_, ?_⟩
              · by_contra hc; push Not at hc; nlinarith
              · by_contra hc; push Not at hc; nlinarith
            · have e1 : u ⬝ᵥ x = d * (fun a => u a / d) ⬝ᵥ x := by
                simp only [vec3_dotProduct]; rw [hdv 0, hdv 1, hdv 2]
                simp only [Int.mul_ediv_cancel_left _ hdZ]; ring
              rw [e1, show (m : ℤ) = d * e by exact_mod_cast he] at hux
              exact (mul_dvd_mul_iff_left hdZ).mp hux
          · funext a
            have hgd := (mem_filter.mp (mem_coe.mp hu)).2
            have hgd' := (mem_filter.mp (mem_coe.mp hu')).2
            have e1 : u a = d * (u a / d) :=
              (Int.mul_ediv_cancel' (by rw [← hgd]; exact gcd4_dvd m u a)).symm
            have e2 : u' a = d * (u' a / d) :=
              (Int.mul_ediv_cancel' (by rw [← hgd']; exact gcd4_dvd m u' a)).symm
            have h' := congrFun h a
            simp only at h'
            rw [e1, e2, h']
          · refine (card_dot_dvd_le he0 x).trans (Nat.mul_le_mul_left _ ?_)
            exact Nat.le_of_dvd (gcd4_pos hm x) (gcd4_dvd_gcd4 ⟨d, by rw [he]; ring⟩ x)
        calc ∑ u ∈ F, gcd4 m u ^ 2 = ∑ u ∈ F, d ^ 2 :=
              sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2]
          _ = F.card * d ^ 2 := by rw [sum_const, smul_eq_mul]
          _ ≤ (27 * e ^ 2 * gcd4 m x) * d ^ 2 := Nat.mul_le_mul_right _ hF
          _ = 27 * m ^ 2 * gcd4 m x := by rw [he]; ring
    _ = 27 * m ^ 2 * m.divisors.card * gcd4 m x := by rw [sum_const, smul_eq_mul]; ring

/-- `∑_{x ≠ 0, |x| ≤ R} gcd(m, x) ≤ 27 R³ τ(m)`. -/
theorem sum_gcd4_box_le {m : ℕ} (hm : 0 < m) (R : ℕ) :
    ∑ x ∈ (ibox3 R).filter (fun x => x ≠ 0), gcd4 m x ≤ 27 * R ^ 3 * m.divisors.card := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := fun x => gcd4 m x) (t := m.divisors)
    (fun x _ => Nat.mem_divisors.mpr ⟨gcd4_dvd_m m x, hm.ne'⟩)]
  calc ∑ h ∈ m.divisors, ∑ x ∈ ((ibox3 R).filter (fun x => x ≠ 0)).filter
          (fun x => gcd4 m x = h), gcd4 m x
      ≤ ∑ _h ∈ m.divisors, 27 * R ^ 3 := by
        refine sum_le_sum fun h hh => ?_
        have hh0 : 0 < h := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hh).1 hm
        set F := ((ibox3 R).filter (fun x => x ≠ 0)).filter fun x => gcd4 m x = h
        rw [sum_congr rfl fun x hx => (mem_filter.mp hx).2, sum_const, smul_eq_mul]
        by_cases hR : R < h
        · have : F = ∅ := by
            refine eq_empty_of_forall_notMem fun x hx => ?_
            obtain ⟨hx1, hxh⟩ := mem_filter.mp hx
            obtain ⟨hxb, hx0⟩ := mem_filter.mp hx1
            apply hx0
            funext j
            have hb := mem_Icc.mp (Fintype.mem_piFinset.mp hxb j)
            have hd : (h : ℤ) ∣ x j := by rw [← hxh]; exact gcd4_dvd m x j
            exact Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
          simp only [F] at this
          rw [this]; simp
        push Not at hR
        have hsub : F ⊆ Fintype.piFinset fun _ => (Icc (-(R : ℤ)) R).filter fun y =>
            (h : ℤ) ∣ y - 0 := by
          intro x hx
          obtain ⟨hx1, hxh⟩ := mem_filter.mp hx
          have hxb := (mem_filter.mp hx1).1
          refine Fintype.mem_piFinset.mpr fun j => mem_filter.mpr
            ⟨Fintype.mem_piFinset.mp hxb j, ?_⟩
          rw [sub_zero, ← hxh]; exact gcd4_dvd m x j
        have hb := card_Icc_dvd_le (m := R) hh0 0
        have hcard : F.card ≤ (2 * R / h + 1) ^ 3 := by
          refine (card_le_card hsub).trans ?_
          rw [Fintype.card_piFinset, Fin.prod_univ_three]
          calc _ ≤ (2 * R / h + 1) * (2 * R / h + 1) * (2 * R / h + 1) :=
                Nat.mul_le_mul (Nat.mul_le_mul hb hb) hb
            _ = (2 * R / h + 1) ^ 3 := by ring
        have h1 : h * (2 * R / h + 1) ≤ 3 * R := by
          have := Nat.mul_div_le (2 * R) h
          nlinarith
        calc F.card * h ≤ (2 * R / h + 1) ^ 3 * h ^ 3 :=
              Nat.mul_le_mul hcard (Nat.le_self_pow (by norm_num) h)
          _ = (h * (2 * R / h + 1)) ^ 3 := by ring
          _ ≤ (3 * R) ^ 3 := Nat.pow_le_pow_left h1 3
          _ = 27 * R ^ 3 := by ring
    _ = 27 * R ^ 3 * m.divisors.card := by rw [sum_const, smul_eq_mul]; ring

/-- **The admissible `(u, v)` with `m ∣ u·x`**: at most `729 m³ τ(m) gcd(m, x)`. -/
theorem card_crossSet_dot {m : ℕ} (hm : 0 < m) (x : Fin 3 → ℤ) :
    ((crossSet m).filter fun uv => (m : ℤ) ∣ uv.1 ⬝ᵥ x).card ≤
      729 * m ^ 3 * m.divisors.card * gcd4 m x := by
  classical
  set T := (ibox3 m).filter fun u => (m : ℤ) ∣ u ⬝ᵥ x
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := T) (fun uv huv => by
    obtain ⟨h1, h2⟩ := mem_filter.mp huv
    exact mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp h1).1).1, h2⟩)]
  calc ∑ u ∈ T, (((crossSet m).filter fun uv => (m : ℤ) ∣ uv.1 ⬝ᵥ x).filter
          fun uv => uv.1 = u).card
      ≤ ∑ u ∈ T, 27 * m * gcd4 m u ^ 2 := by
        refine sum_le_sum fun u _ => le_trans (card_le_card_of_injOn Prod.snd
          (t := (ibox3 m).filter fun v => ∀ a, (m : ℤ) ∣ (u ⨯₃ v) a) (fun uv huv => ?_)
          (fun uv huv uv' huv' h => ?_)) (card_cross_fiber hm u)
        · obtain ⟨h1, h2⟩ := mem_filter.mp (mem_coe.mp huv)
          obtain ⟨h3, -⟩ := mem_filter.mp h1
          obtain ⟨h5, h6⟩ := mem_filter.mp h3
          rw [← h2]
          exact mem_filter.mpr ⟨(mem_product.mp h5).2, h6⟩
        · have e1 := (mem_filter.mp (mem_coe.mp huv)).2
          have e2 := (mem_filter.mp (mem_coe.mp huv')).2
          exact Prod.ext (e1.trans e2.symm) h
    _ = 27 * m * ∑ u ∈ T, gcd4 m u ^ 2 := by rw [mul_sum]
    _ ≤ 27 * m * (27 * m ^ 2 * m.divisors.card * gcd4 m x) :=
        Nat.mul_le_mul_left _ (sum_gcd4_sq_dot_le hm x)
    _ = 729 * m ^ 3 * m.divisors.card * gcd4 m x := by ring

/-- **The minor-vector count with a divisibility condition.** Minor vectors of height `≤ Y` with
`m ∣ u·x` for the pivot entry `m` number at most `20 ∑_{m ≤ Y} #{(u, v) ∈ crossSet m : m ∣ u·x}`.
-/
theorem minor_vector_count_dot {S : Finset (Fin 10 → ℤ)} {Y : ℕ} (x : Fin 3 → ℤ)
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ Y) ∧ PluckerRel p ∧ p (piv p) ≠ 0 ∧
      p (piv p) ∣ uVec p (piv p) ⬝ᵥ x) :
    S.card ≤ 20 * ∑ m ∈ Icc 1 Y, ((crossSet m).filter fun uv => (m : ℤ) ∣ uv.1 ⬝ᵥ x).card :=
  minor_vector_count_of (fun m u => (m : ℤ) ∣ u ⬝ᵥ x) fun p hp =>
    ⟨(hS p hp).1, (hS p hp).2.1, (hS p hp).2.2.1, Int.natAbs_dvd.mpr (hS p hp).2.2.2⟩

/-- **Few patterns have a short vector** (Proposition 9.6). If `τ(m) ≤ τ₀` for `m ≤ Y`, the
minor vectors of height `≤ Y` with nonzero pivot entry and `λ(p) ≤ R` number at most
`393660 R³ Y⁴ τ₀²`. -/
theorem short_count {S : Finset (Fin 10 → ℤ)} {Y R τ0 : ℕ}
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ Y) ∧ PluckerRel p ∧ p (piv p) ≠ 0)
    (hτ : ∀ m ∈ Icc 1 Y, m.divisors.card ≤ τ0) :
    (S.filter fun p => shortR p ≤ R).card ≤ 393660 * R ^ 3 * Y ^ 4 * τ0 ^ 2 := by
  classical
  set X0 := (ibox3 R).filter fun x => x ≠ 0
  have hsub : S.filter (fun p => shortR p ≤ R) ⊆
      X0.biUnion fun x => S.filter fun p => p (piv p) ∣ uVec p (piv p) ⬝ᵥ x := by
    intro p hp
    obtain ⟨hpS, hR⟩ := mem_filter.mp hp
    obtain ⟨-, ⟨x, hx, hx0, hxb⟩, -⟩ := shortR_spec (hS p hpS).2.2
    refine mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j =>
      mem_Icc.mpr (abs_le.mp ((hxb j).trans (by exact_mod_cast hR))), hx0⟩,
      mem_filter.mpr ⟨hpS, hx.1⟩⟩
  have hY : ∀ m ∈ Icc 1 Y, m ≤ Y := fun m hm => (mem_Icc.mp hm).2
  calc (S.filter fun p => shortR p ≤ R).card
      ≤ ∑ x ∈ X0, (S.filter fun p => p (piv p) ∣ uVec p (piv p) ⬝ᵥ x).card :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ x ∈ X0, 20 * ∑ m ∈ Icc 1 Y, 729 * m ^ 3 * m.divisors.card * gcd4 m x := by
        refine sum_le_sum fun x _ => (minor_vector_count_dot (Y := Y) x fun p hp => ?_).trans ?_
        · obtain ⟨hpS, hd⟩ := mem_filter.mp hp
          exact ⟨(hS p hpS).1, (hS p hpS).2.1, (hS p hpS).2.2, hd⟩
        · exact Nat.mul_le_mul_left _ (sum_le_sum fun m hm =>
            card_crossSet_dot (by have := (mem_Icc.mp hm).1; omega) x)
    _ = 20 * ∑ m ∈ Icc 1 Y, 729 * m ^ 3 * m.divisors.card * ∑ x ∈ X0, gcd4 m x := by
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum]
    _ ≤ 20 * ∑ m ∈ Icc 1 Y, 729 * m ^ 3 * m.divisors.card * (27 * R ^ 3 * m.divisors.card) := by
        refine Nat.mul_le_mul_left _ (sum_le_sum fun m hm => Nat.mul_le_mul_left _ ?_)
        exact sum_gcd4_box_le (by have := (mem_Icc.mp hm).1; omega) R
    _ ≤ 20 * ∑ _m ∈ Icc 1 Y, 729 * Y ^ 3 * τ0 * (27 * R ^ 3 * τ0) := by
        refine Nat.mul_le_mul_left _ (sum_le_sum fun m hm => ?_)
        have h1 := hτ m hm
        have h2 : m ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left (hY m hm) 3
        gcongr
    _ = 393660 * R ^ 3 * Y ^ 4 * τ0 ^ 2 := by
        rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]; ring

end PierceLengthBound
