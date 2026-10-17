import PierceBound.MinorCount
import PierceBound.Reduce3

/-!
# The pattern lattice and its short vectors

For a minor vector `p` with pivot `τ` and `m = p_τ ≠ 0`, the five gaps are recovered from the
three pivot gaps `k' = (k_{c₁}, k_{c₂}, k_{c₃})` by `m kᶜ = Lᶜ · k'` (`lift_row`), where the rows
`Lᶜ` are `m eₐ` on pivot columns and `u`, `v` on the other two. So `k'` lies in the lattice
`Λ_p = {x : m ∣ u·x, m ∣ v·x}` (`pivLat`). The rows in columns `1, 2, 3` have determinant
`m² p₁₂₃` (`lift_det`).

`Λ_p` has a nonzero vector of sup norm at most `L` once `(L+1)³ > |m|` (`pivLat_short`). The
cross relation `m ∣ u × v` makes the index at most `|m|`. Few patterns have a short vector:
`#{p : λ₁(Λ_p) ≤ R} ≤ 393660 R³ Y⁴ τ²` (`short_count`).
-/

namespace PierceBound

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

/-- **Lifting.** Each row of the matrix is recovered from its pivot columns. -/
theorem lift_row (M : Fin 3 → Fin 5 → ℤ) (τ : Fin 10) (r : Fin 3) (c : Fin 5) :
    plk M τ * M r c = dot3 (Lrow (plk M) τ c) (fun a => M r (pcol τ a)) := by
  fin_cases τ <;> fin_cases c <;>
    simp [Lrow, role, pcol, dot3, plk, trip, minor3, uVec, vVec, puX, puS, pvX, pvS] <;>
    fin_cases r <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> ring

/-- **The determinant of the rows `1, 2, 3`.** -/
theorem lift_det (M : Fin 3 → Fin 5 → ℤ) (τ : Fin 10) :
    det3 (Lrow (plk M) τ 1) (Lrow (plk M) τ 2) (Lrow (plk M) τ 3) = plk M τ ^ 2 * plk M 6 := by
  fin_cases τ <;>
    simp [Lrow, role, det3, plk, trip, minor3, uVec, vVec, puX, puS, pvX, pvS] <;> ring

/-! ### The lattice -/

lemma dot3_add_right (u x y : Fin 3 → ℤ) : dot3 u (x + y) = dot3 u x + dot3 u y := by
  simp [dot3]; ring

lemma dot3_neg_right (u x : Fin 3 → ℤ) : dot3 u (-x) = -dot3 u x := by simp [dot3]; ring

lemma dot3_sub_right (u x y : Fin 3 → ℤ) : dot3 u (x - y) = dot3 u x - dot3 u y := by
  simp [dot3]; ring

/-- The pattern lattice in pivot coordinates. -/
def pivLat (p : Fin 10 → ℤ) : AddSubgroup (Fin 3 → ℤ) where
  carrier := {x | p (piv p) ∣ dot3 (uVec p (piv p)) x ∧ p (piv p) ∣ dot3 (vVec p (piv p)) x}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, dot3_add_right] at hx hy ⊢
    exact ⟨dvd_add hx.1 hy.1, dvd_add hx.2 hy.2⟩
  zero_mem' := by simp [dot3]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq, dot3_neg_right, dvd_neg] at hx ⊢
    exact hx

lemma dvd_dot3_of_dvd {d : ℤ} {x : Fin 3 → ℤ} (h : ∀ j, d ∣ x j) (w : Fin 3 → ℤ) :
    d ∣ dot3 w x := by
  unfold dot3
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right (h 0) _) (dvd_mul_of_dvd_right (h 1) _))
    (dvd_mul_of_dvd_right (h 2) _)

lemma pivLat_of_dvd {p : Fin 10 → ℤ} {x : Fin 3 → ℤ} (h : ∀ j, p (piv p) ∣ x j) :
    x ∈ pivLat p := ⟨dvd_dot3_of_dvd h _, dvd_dot3_of_dvd h _⟩

/-- The pivot divides the cross product. -/
lemma piv_cross {p : Fin 10 → ℤ} (hpl : PluckerRel p) (a : Fin 3) :
    p (piv p) ∣ cross3 (uVec p (piv p)) (vVec p (piv p)) a := by
  set τ := piv p
  refine ⟨pwS τ a * p (pwX τ a), ?_⟩
  have h1 := hpl τ a
  have h2 := (sign_sq τ a).2.2
  linear_combination (-pwS τ a) * h1 - cross3 (uVec p τ) (vVec p τ) a * h2

/-- Bézout for `gcd(m, u₀, u₁, u₂)`. -/
lemma gcd4_bezout (m : ℕ) (u : Fin 3 → ℤ) :
    ∃ x c0 c1 c2 : ℤ, (m : ℤ) * x + u 0 * c0 + u 1 * c1 + u 2 * c2 = gcd4 m u := by
  have e1 := Int.gcd_eq_gcd_ab (m : ℤ) (Int.gcd (u 0) (Int.gcd (u 1) (u 2)))
  have e2 := Int.gcd_eq_gcd_ab (u 0) (Int.gcd (u 1) (u 2))
  have e3 := Int.gcd_eq_gcd_ab (u 1) (u 2)
  set y := Int.gcdB (m : ℤ) (Int.gcd (u 0) (Int.gcd (u 1) (u 2)))
  set y0 := Int.gcdB (u 0) (Int.gcd (u 1) (u 2))
  refine ⟨Int.gcdA (m : ℤ) (Int.gcd (u 0) (Int.gcd (u 1) (u 2))), y * Int.gcdA (u 0)
    (Int.gcd (u 1) (u 2)), y * y0 * Int.gcdA (u 1) (u 2), y * y0 * Int.gcdB (u 1) (u 2), ?_⟩
  simp only [gcd4]
  rw [e1]
  have e2' : ((Int.gcd (u 0) (Int.gcd (u 1) (u 2)) : ℕ) : ℤ) = u 0 * Int.gcdA (u 0)
      (Int.gcd (u 1) (u 2)) + (Int.gcd (u 1) (u 2) : ℤ) * y0 := e2
  rw [e2', e3]
  ring

lemma gcd4_pos {m : ℕ} (hm : 0 < m) (u : Fin 3 → ℤ) : 0 < gcd4 m u :=
  Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast hm.ne')

/-- **The cross congruence**: `m ∣ u × v` forces `v ≡ λ u' (mod m/g)`. -/
lemma cross_cong {m : ℕ} (hm : 0 < m) {u v : Fin 3 → ℤ} (hd : ∀ a, (m : ℤ) ∣ cross3 u v a) :
    ∃ n : ℤ, ∃ u' : Fin 3 → ℤ, ∃ lam : ℤ, 0 < n ∧ (m : ℤ) = gcd4 m u * n ∧
      (∀ a, u a = gcd4 m u * u' a) ∧ ∀ a, n ∣ v a - lam * u' a := by
  set g := gcd4 m u
  have hg0 : 0 < g := gcd4_pos hm u
  obtain ⟨x, c0, c1, c2, hb⟩ := gcd4_bezout m u
  obtain ⟨n, hn⟩ : (g : ℤ) ∣ m := Int.gcd_dvd_left _ _
  obtain ⟨w0, hw0⟩ := gcd4_dvd m u 0
  obtain ⟨w1, hw1⟩ := gcd4_dvd m u 1
  obtain ⟨w2, hw2⟩ := gcd4_dvd m u 2
  set u' : Fin 3 → ℤ := ![w0, w1, w2]
  have hu' : ∀ a, u a = g * u' a := by
    intro a; fin_cases a <;> simp [u', hw0, hw1, hw2, g]
  have hg0' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hn1 : n * x + w0 * c0 + w1 * c1 + w2 * c2 = 1 := by
    apply mul_left_cancel₀ hg0'
    rw [hn, hw0, hw1, hw2] at hb
    linear_combination hb
  have hnpos : 0 < n := by
    have : (0 : ℤ) < m := by exact_mod_cast hm
    rw [hn] at this
    exact pos_of_mul_pos_right this (by positivity)
  refine ⟨n, u', c0 * v 0 + c1 * v 1 + c2 * v 2, hnpos, hn, hu', ?_⟩
  have hd' : ∀ a, n ∣ cross3 u' v a := by
    intro a
    have h := hd a
    have e : cross3 u v a = g * cross3 u' v a := by
      simp only [cross3, hu']; ring
    rw [e, hn] at h
    exact (mul_dvd_mul_iff_left hg0').mp h
  obtain ⟨z0, hz0⟩ := hd' 0
  obtain ⟨z1, hz1⟩ := hd' 1
  obtain ⟨z2, hz2⟩ := hd' 2
  rw [cross3_zero] at hz0
  rw [cross3_one] at hz1
  rw [cross3_two] at hz2
  simp only [u', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hz0 hz1 hz2
  intro a
  match a with
  | 0 => exact ⟨v 0 * x - c1 * z2 + c2 * z1, by
      simp [u']
      linear_combination -v 0 * hn1 - c1 * hz2 + c2 * hz1⟩
  | 1 => exact ⟨v 1 * x + c0 * z2 - c2 * z0, by
      simp [u']
      linear_combination -v 1 * hn1 + c0 * hz2 - c2 * hz0⟩
  | 2 => exact ⟨v 2 * x - c0 * z1 + c1 * z0, by
      simp [u']
      linear_combination -v 2 * hn1 - c0 * hz1 + c1 * hz0⟩

/-- `Λ_p` has a nonzero vector of sup norm at most `R`. -/
def HasShort (p : Fin 10 → ℤ) (R : ℕ) : Prop := ∃ x ∈ pivLat p, x ≠ 0 ∧ ∀ j, |x j| ≤ R

/-- **Pigeonhole: the index is at most `|m|`.** -/
theorem pivLat_short {p : Fin 10 → ℤ} (hpl : PluckerRel p) (hm : p (piv p) ≠ 0) {L : ℕ}
    (hL : (p (piv p)).natAbs < (L + 1) ^ 3) : HasShort p L := by
  classical
  set τ := piv p
  set m := (p τ).natAbs
  have hm0 : 0 < m := Int.natAbs_pos.mpr hm
  have hd : ∀ a, (m : ℤ) ∣ cross3 (uVec p τ) (vVec p τ) a := fun a =>
    Int.natAbs_dvd.mpr (piv_cross hpl a)
  obtain ⟨n, u', lam, hn, hmg, hu, hv⟩ := cross_cong hm0 hd
  set g : ℤ := (gcd4 m (uVec p τ) : ℤ)
  have hg : 0 < g := Int.natCast_pos.mpr (gcd4_pos hm0 _)
  choose w hw using hv
  set ψ : (Fin 3 → ℤ) → ℤ × ℤ := fun x =>
    (dot3 u' x % n, (lam * (dot3 u' x / n) + dot3 w x) % g)
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
  set A := dot3 u' x
  set B := dot3 u' y
  have hAB : A - B = n * (A / n - B / n) := by
    have e1 := Int.mul_ediv_add_emod A n
    have e2 := Int.mul_ediv_add_emod B n
    linear_combination -e1 + e2 + h1
  have hdu : ∀ z, dot3 (uVec p τ) z = g * dot3 u' z := fun z => by
    simp only [dot3, hu]; ring
  have hdv : ∀ z, dot3 (vVec p τ) z = lam * dot3 u' z + n * dot3 w z := fun z => by
    have := hw 0; have := hw 1; have := hw 2
    simp only [dot3]; linear_combination (z 0) * hw 0 + (z 1) * hw 1 + (z 2) * hw 2
  have hg2 : g ∣ lam * (A / n - B / n) + dot3 w (x - y) := by
    have := Int.ModEq.dvd h2.symm
    rw [dot3_sub_right]
    convert this using 1; ring
  refine ⟨x - y, ⟨Int.natAbs_dvd.mp ?_, Int.natAbs_dvd.mp ?_⟩, sub_ne_zero.mpr hne, fun j => ?_⟩
  · rw [hdu, dot3_sub_right, hAB]
    exact ⟨A / n - B / n, by rw [hmg]; ring⟩
  · rw [hdv, dot3_sub_right, hAB]
    obtain ⟨k, hk⟩ := hg2
    refine ⟨k, ?_⟩
    rw [hmg]
    linear_combination n * hk
  · have hxj := mem_Icc.mp (Fintype.mem_piFinset.mp hx j)
    have hyj := mem_Icc.mp (Fintype.mem_piFinset.mp hy j)
    simp only [Pi.sub_apply]
    rw [abs_le]; constructor <;> linarith

/-- The shortest sup norm of a nonzero vector of `Λ_p`. -/
noncomputable def shortR (p : Fin 10 → ℤ) : ℕ := sInf {R : ℕ | HasShort p R}

lemma hasShort_nonempty {p : Fin 10 → ℤ} (hm : p (piv p) ≠ 0) :
    HasShort p (p (piv p)).natAbs := by
  refine ⟨![p (piv p), 0, 0], pivLat_of_dvd fun j => ?_, ?_, fun j => ?_⟩
  · fin_cases j <;> simp
  · intro h; apply hm; simpa using congrFun h 0
  · fin_cases j <;> simp

/-- **The shortest vector.** -/
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
        simp at this; exact absurd this (not_lt.mpr (abs_nonneg _))
      have : HasShort p (shortR p - 1) := ⟨x, hx, hx0, fun j => by
        have := h j; push_cast [h1]; omega⟩
      exact Nat.notMem_of_lt_sInf (s := {R : ℕ | HasShort p R}) (m := shortR p - 1)
        (show shortR p - 1 < shortR p by omega) this
    obtain ⟨j, hj⟩ := this
    have h0 : (0 : ℤ) ≤ shortR p := by positivity
    have : (shortR p : ℤ) ^ 2 ≤ x j ^ 2 := by
      rw [← sq_abs (x j)]; exact pow_le_pow_left₀ h0 hj 2
    have : x j ^ 2 ≤ nrm3 x := by
      unfold nrm3 dot3
      fin_cases j <;> simp <;> nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1),
        mul_self_nonneg (x 2)]
    linarith

lemma shortR_le {p : Fin 10 → ℤ} {L : ℕ} (h : HasShort p L) : shortR p ≤ L := Nat.sInf_le h

/-! ### Counting patterns with a short vector -/

/-- **Solutions of `n ∣ w·x` in a box**: at most `27 n² gcd(n, x)`. -/
theorem card_dot_dvd_le {n : ℕ} (hn : 0 < n) (x : Fin 3 → ℤ) :
    ((ibox3 n).filter fun w => (n : ℤ) ∣ dot3 w x).card ≤ 27 * n ^ 2 * gcd4 n x := by
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
    (n : ℤ) ∣ dot3 w x
  -- step 1: reduce modulo `n`
  have step1 : ((ibox3 n).filter fun w => (n : ℤ) ∣ dot3 w x).card ≤ 27 * K.card := by
    refine card_le_mul_card_image_of_maps_to (f := fun (w : Fin 3 → ℤ) (j : Fin 3) => w j % (n : ℤ))
      (t := K) (fun w hw => ?_) 27 fun r _ => ?_
    · obtain ⟨-, hd⟩ := mem_filter.mp hw
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => mem_Ico.mpr
        ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩, ?_⟩
      have : (n : ℤ) ∣ dot3 w x - dot3 (fun j => w j % (n : ℤ)) x := by
        have e : dot3 w x - dot3 (fun j => w j % (n : ℤ)) x =
            (w 0 - w 0 % n) * x 0 + (w 1 - w 1 % n) * x 1 + (w 2 - w 2 % n) * x 2 := by
          simp only [dot3]; ring
        rw [e]
        exact dvd_add (dvd_add (dvd_mul_of_dvd_left (Int.dvd_self_sub_emod ..) _)
          (dvd_mul_of_dvd_left (Int.dvd_self_sub_emod ..) _))
          (dvd_mul_of_dvd_left (Int.dvd_self_sub_emod ..) _)
      have := dvd_sub hd this
      simpa using this
    · have hsub : ((ibox3 n).filter fun w => (n : ℤ) ∣ dot3 w x).filter
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
  have hcc : dot3 cc x = e - n * s0 := by
    simp only [dot3, cc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
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
        have h3 : (n : ℤ) ∣ dot3 (fun j => (wk.1 j - wk'.1 j) + ((wk.2 : ℤ) - wk'.2) * cc j) x := by
          have := dvd_dot3_of_dvd (x := fun j => (wk.1 j - wk'.1 j) + ((wk.2 : ℤ) - wk'.2) * cc j)
            hd x
          rwa [show ∀ y z : Fin 3 → ℤ, dot3 y z = dot3 z y from fun y z => by
            simp only [dot3]; ring] at this
        have e1 : dot3 (fun j => (wk.1 j - wk'.1 j) + ((wk.2 : ℤ) - wk'.2) * cc j) x =
            dot3 wk.1 x - dot3 wk'.1 x + ((wk.2 : ℤ) - wk'.2) * dot3 cc x := by
          simp only [dot3]; ring
        rw [e1, hcc] at h3
        have := dvd_sub (dvd_sub h3 h1) (dvd_neg.mpr h2)
        have h4 : (n : ℤ) ∣ ((wk.2 : ℤ) - wk'.2) * (n * s0) := dvd_mul_of_dvd_right (dvd_mul_right _ _) _
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
    ∑ u ∈ (ibox3 m).filter (fun u => (m : ℤ) ∣ dot3 u x), gcd4 m u ^ 2 ≤
      27 * m ^ 2 * m.divisors.card * gcd4 m x := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := fun u => gcd4 m u) (t := m.divisors)
    (fun u _ => Nat.mem_divisors.mpr ⟨gcd4_dvd_m m u, hm.ne'⟩)]
  calc ∑ d ∈ m.divisors, ∑ u ∈ ((ibox3 m).filter (fun u => (m : ℤ) ∣ dot3 u x)).filter
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
        set F := ((ibox3 m).filter (fun u => (m : ℤ) ∣ dot3 u x)).filter fun u => gcd4 m u = d
        have hF : F.card ≤ 27 * e ^ 2 * gcd4 m x := by
          have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd0.ne'
          refine (card_le_card_of_injOn (fun u a => u a / d)
            (t := (ibox3 e).filter fun w => (e : ℤ) ∣ dot3 w x) (fun u hu => ?_)
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
            · have e1 : dot3 u x = d * dot3 (fun a => u a / d) x := by
                simp only [dot3]; rw [hdv 0, hdv 1, hdv 2]
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

/-- **The admissible `(u, v)` with `m ∣ u·x`.** -/
theorem card_crossSet_dot {m : ℕ} (hm : 0 < m) (x : Fin 3 → ℤ) :
    ((crossSet m).filter fun uv => (m : ℤ) ∣ dot3 uv.1 x).card ≤
      729 * m ^ 3 * m.divisors.card * gcd4 m x := by
  classical
  set T := (ibox3 m).filter fun u => (m : ℤ) ∣ dot3 u x
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := T) (fun uv huv => by
    obtain ⟨h1, h2⟩ := mem_filter.mp huv
    exact mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp h1).1).1, h2⟩)]
  calc ∑ u ∈ T, (((crossSet m).filter fun uv => (m : ℤ) ∣ dot3 uv.1 x).filter
          fun uv => uv.1 = u).card
      ≤ ∑ u ∈ T, 27 * m * gcd4 m u ^ 2 := by
        refine sum_le_sum fun u _ => le_trans (card_le_card_of_injOn Prod.snd
          (t := (ibox3 m).filter fun v => ∀ a, (m : ℤ) ∣ cross3 u v a) (fun uv huv => ?_)
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

/-- **The minor-vector count with a divisibility condition.** -/
theorem minor_vector_count_dot {S : Finset (Fin 10 → ℤ)} {Y : ℕ} (x : Fin 3 → ℤ)
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ Y) ∧ PluckerRel p ∧ p (piv p) ≠ 0 ∧
      p (piv p) ∣ dot3 (uVec p (piv p)) x) :
    S.card ≤ 20 * ∑ m ∈ Icc 1 Y, ((crossSet m).filter fun uv => (m : ℤ) ∣ dot3 uv.1 x).card :=
  minor_vector_count_of (fun m u => (m : ℤ) ∣ dot3 u x) fun p hp =>
    ⟨(hS p hp).1, (hS p hp).2.1, (hS p hp).2.2.1, Int.natAbs_dvd.mpr (hS p hp).2.2.2⟩

/-- **Few patterns have a short vector.** -/
theorem short_count {S : Finset (Fin 10 → ℤ)} {Y R τ0 : ℕ}
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ Y) ∧ PluckerRel p ∧ p (piv p) ≠ 0)
    (hτ : ∀ m ∈ Icc 1 Y, m.divisors.card ≤ τ0) :
    (S.filter fun p => shortR p ≤ R).card ≤ 393660 * R ^ 3 * Y ^ 4 * τ0 ^ 2 := by
  classical
  set X0 := (ibox3 R).filter fun x => x ≠ 0
  have hsub : S.filter (fun p => shortR p ≤ R) ⊆
      X0.biUnion fun x => S.filter fun p => p (piv p) ∣ dot3 (uVec p (piv p)) x := by
    intro p hp
    obtain ⟨hpS, hR⟩ := mem_filter.mp hp
    obtain ⟨-, ⟨x, hx, hx0, hxb⟩, -⟩ := shortR_spec (hS p hpS).2.2
    refine mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j =>
      mem_Icc.mpr (abs_le.mp ((hxb j).trans (by exact_mod_cast hR))), hx0⟩,
      mem_filter.mpr ⟨hpS, hx.1⟩⟩
  have hY : ∀ m ∈ Icc 1 Y, m ≤ Y := fun m hm => (mem_Icc.mp hm).2
  calc (S.filter fun p => shortR p ≤ R).card
      ≤ ∑ x ∈ X0, (S.filter fun p => p (piv p) ∣ dot3 (uVec p (piv p)) x).card :=
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

end PierceBound
