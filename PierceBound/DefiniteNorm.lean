/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceBound.NormCount

/-!
# The definite norm count

For `D ≥ 1` and `N ≠ 0`, the equation `U² + D V² = N` has at most `4 τ(|N|)³` integer solutions
(`norm_count_def`). Write `D = d f²` with `d` squarefree, reduce a solution to a primitive
`u² + d w² = n` with `N = g² n`, and attach the class `t ≡ u w⁻¹ (mod n)`, a square root of `-d`.
Two solutions in one class differ by a unit `r + s√-d` with `r² + d s² = 1`, of which there are at
most four.
-/

@[expose] public section

namespace PierceBound

open Finset

/-- The solutions of `U² + D V² = N` in the box `[-B, B]²`. -/
def defSols (D : ℕ) (N : ℤ) (B : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(B : ℤ)) B ×ˢ Icc (-(B : ℤ)) B).filter fun p => p.1 ^ 2 + D * p.2 ^ 2 = N

/-- The reduction of a solution of the definite equation. -/
structure ReducedDef (d f : ℕ) (N : ℤ) (p : ℤ × ℤ) (g : ℕ) (u w n : ℤ) : Prop where
  g_pos : 0 < g
  hu : p.1 = g * u
  hw : (f : ℤ) * p.2 = g * w
  hN : N = (g : ℤ) ^ 2 * n
  hn : n = u ^ 2 + d * w ^ 2
  cop : IsCoprime w n

lemma reduce_def {d f : ℕ} (hf : 0 < f) {N : ℤ} (hN : N ≠ 0) {p : ℤ × ℤ}
    (hp : p.1 ^ 2 + ((f ^ 2 * d : ℕ) : ℤ) * p.2 ^ 2 = N) :
    ReducedDef d f N p (Int.gcd p.1 (f * p.2)) (p.1 / Int.gcd p.1 (f * p.2))
      ((f * p.2) / Int.gcd p.1 (f * p.2))
      ((p.1 / Int.gcd p.1 (f * p.2)) ^ 2 + d * ((f * p.2) / Int.gcd p.1 (f * p.2)) ^ 2) := by
  set g := Int.gcd p.1 (f * p.2) with hgdef
  have hf' : (f : ℤ) ≠ 0 := by exact_mod_cast hf.ne'
  have hg : 0 < g := by
    rw [hgdef, Int.gcd_pos_iff]
    by_contra h
    push Not at h
    apply hN
    rw [← hp, h.1, show p.2 = 0 from (mul_eq_zero.mp h.2).resolve_left hf']
    ring
  have hu : p.1 = g * (p.1 / g) := (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
  have hw : (f : ℤ) * p.2 = g * ((f * p.2) / g) :=
      (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  refine ⟨hg, hu, hw, ?_, rfl, ?_⟩
  · rw [← hp]
    push_cast
    linear_combination (p.1 + g * (p.1 / g)) * hu +
      (d : ℤ) * ((f : ℤ) * p.2 + g * ((f * p.2) / g)) * hw
  · have h1 : IsCoprime (p.1 / g) ((f * p.2) / g) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hg)
    have h2 := (h1.symm.pow_right (n := 2)).add_mul_left_right ((d : ℤ) * ((f * p.2) / g))
    convert h2 using 1
    ring

/-- The class key of a reduced definite solution: `t ≡ u w⁻¹ (mod n)`, a root of `-d`. -/
lemma class_key_def {d : ℤ} {u w n : ℤ} (hn : n = u ^ 2 + d * w ^ 2) (hc : IsCoprime w n) :
    let t := (u * Int.gcdA w n) % n
    n ∣ t ^ 2 - (-d) ∧ n ∣ u - t * w := by
  have := class_key (d := -d) (u := u) (w := w) (n := n) (by rw [hn]; ring) hc
  exact this

/-- Within one class, all solutions are images of one under the four units. -/
lemma def_class_units {d : ℕ} (hd : 1 ≤ d) {n t : ℤ} (hn : n ≠ 0) (ht : n ∣ t ^ 2 - (-(d : ℤ)))
    {q q' : ℤ × ℤ} (hq : q.1 ^ 2 + d * q.2 ^ 2 = n) (hq' : q'.1 ^ 2 + d * q'.2 ^ 2 = n)
    (hc : n ∣ q.1 - t * q.2) (hc' : n ∣ q'.1 - t * q'.2) :
    ∃ r s : ℤ, (r, s) ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)) ∧
      q = (q'.1 * r - d * q'.2 * s, q'.1 * s + q'.2 * r) := by
  obtain ⟨u, w⟩ := q
  obtain ⟨u', w'⟩ := q'
  simp only at hq hq' hc hc' ⊢
  have h1 : n ∣ u * u' + d * w * w' := by
    obtain ⟨x, hx⟩ := hc; obtain ⟨y, hy⟩ := hc'; obtain ⟨z, hz⟩ := ht
    exact
        ⟨x * u' + t * w * y + w * w' * z, by linear_combination u' * hx + t * w * hy + w * w' * hz⟩
  have h2 : n ∣ w * u' - u * w' := by
    obtain ⟨x, hx⟩ := hc; obtain ⟨y, hy⟩ := hc'
    exact ⟨w * y - w' * x, by linear_combination w * hy - w' * hx⟩
  obtain ⟨r, hr⟩ := h1
  obtain ⟨s, hs⟩ := h2
  have hnorm : r ^ 2 + d * s ^ 2 = 1 := by
    have : n * n * (r ^ 2 + d * s ^ 2) = n * n * 1 := by
      linear_combination (-(n * r) - (u * u' + d * w * w')) * hr -
        d * (n * s + (w * u' - u * w')) * hs + (u' ^ 2 + d * w' ^ 2) * hq + n * hq'
    exact mul_left_cancel₀ (mul_ne_zero hn hn) this
  have hu : u = u' * r - d * w' * s := by
    apply mul_left_cancel₀ hn
    linear_combination u' * hr - d * w' * hs - u * hq'
  have hw : w = u' * s + w' * r := by
    apply mul_left_cancel₀ hn
    linear_combination u' * hs + w' * hr - w * hq'
  refine ⟨r, s, ?_, by rw [hu, hw]⟩
  have hs2 : d * s ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have hr1 : -1 ≤ r ∧ r ≤ 1 := by constructor <;> nlinarith
  have hs1 : -1 ≤ s ∧ s ≤ 1 := by
    have : s ^ 2 ≤ 1 := by nlinarith
    constructor <;> nlinarith
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  have : r = -1 ∨ r = 0 ∨ r = 1 := by omega
  have : s = -1 ∨ s = 0 ∨ s = 1 := by omega
  rcases this with h | h | h <;> rcases ‹r = -1 ∨ r = 0 ∨ r = 1› with h' | h' | h' <;>
    subst h <;> subst h'
  all_goals (try norm_num at hnorm ⊢)
  all_goals omega

/-- **The definite norm count.** -/
theorem norm_count_def {D : ℕ} {N : ℤ} (B : ℕ) (hD : 1 ≤ D) (hN : N ≠ 0) :
    (defSols D N B).card ≤ 4 * N.natAbs.divisors.card ^ 3 := by
  classical
  have hNa : N.natAbs ≠ 0 := by simpa using hN
  obtain ⟨d, f, hd0, hf0, hDf, hsf⟩ := Nat.sq_mul_squarefree_of_pos (by omega : 0 < D)
  have hsfZ : Squarefree (-(d : ℤ)) := fun y hy =>
    Int.squarefree_natCast.mpr hsf y (dvd_neg.mp hy)
  subst hDf
  set g : ℤ × ℤ → ℕ := fun p => Int.gcd p.1 (f * p.2)
  set u : ℤ × ℤ → ℤ := fun p => p.1 / g p
  set w : ℤ × ℤ → ℤ := fun p => (f * p.2) / g p
  set n : ℤ × ℤ → ℤ := fun p => u p ^ 2 + d * w p ^ 2
  set t : ℤ × ℤ → ℤ := fun p => (u p * Int.gcdA (w p) (n p)) % n p
  set key : ℤ × ℤ → ℕ × ℕ := fun p => (g p, (t p).toNat)
  have hR : ∀ p ∈ defSols (f ^ 2 * d) N B, ReducedDef d f N p (g p) (u p) (w p) (n p) :=
    fun p hp => reduce_def hf0 hN (mem_filter.mp hp).2
  have hn0 : ∀ p ∈ defSols (f ^ 2 * d) N B, n p ≠ 0 := by
    intro p hp h0
    apply hN
    rw [(hR p hp).hN, h0, mul_zero]
  have hkey : ∀ p ∈ defSols (f ^ 2 * d) N B, n p ∣ t p ^ 2 - (-(d : ℤ)) ∧ n p ∣ u p - t p * w p :=
    fun p hp => class_key_def (d := (d : ℤ)) (hR p hp).hn (hR p hp).cop
  have ht0 : ∀ p ∈ defSols (f ^ 2 * d) N B, 0 ≤ t p ∧ t p < (n p).natAbs := fun p hp =>
    ⟨Int.emod_nonneg _ (hn0 p hp), Int.emod_lt _ (hn0 p hp)⟩
  have hnabs : ∀ p ∈ defSols (f ^ 2 * d) N B, (n p).natAbs = N.natAbs / g p ^ 2 ∧
      g p ^ 2 ∣ N.natAbs := by
    intro p hp
    have e : N.natAbs = g p ^ 2 * (n p).natAbs := by
      rw [(hR p hp).hN, Int.natAbs_mul]; simp
    have hg := (hR p hp).g_pos
    exact ⟨by rw [e, Nat.mul_div_cancel_left _ (by positivity)], ⟨_, e⟩⟩
  set G := N.natAbs.divisors.filter fun g => g ^ 2 ∣ N.natAbs
  set KS : Finset (ℕ × ℕ) :=
    G.biUnion fun g => (sqRoots (-(d : ℤ)) (N.natAbs / g ^ 2)).image fun t => (g, t)
  have hKS : KS.card ≤ N.natAbs.divisors.card ^ 3 := by
    refine card_biUnion_le.trans ?_
    calc ∑ g ∈ G, ((sqRoots (-(d : ℤ)) (N.natAbs / g ^ 2)).image fun t => (g, t)).card
        ≤ ∑ _g ∈ G, N.natAbs.divisors.card ^ 2 := by
          refine sum_le_sum fun g hg => card_image_le.trans ((card_sqRoots_le hsfZ _).trans ?_)
          have hdiv : N.natAbs / g ^ 2 ∣ N.natAbs := Nat.div_dvd_of_dvd (mem_filter.mp hg).2
          exact Nat.pow_le_pow_left (card_le_card (Nat.divisors_subset_of_dvd hNa hdiv)) 2
      _ = G.card * N.natAbs.divisors.card ^ 2 := by rw [sum_const, smul_eq_mul]
      _ ≤ N.natAbs.divisors.card * N.natAbs.divisors.card ^ 2 :=
          Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
      _ = N.natAbs.divisors.card ^ 3 := by ring
  have hmaps : ∀ p ∈ defSols (f ^ 2 * d) N B, key p ∈ KS := by
    intro p hp
    obtain ⟨hna, hg2⟩ := hnabs p hp
    refine mem_biUnion.mpr ⟨g p, mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(dvd_pow_self _ (by norm_num)).trans hg2, hNa⟩, hg2⟩, mem_image.mpr ⟨(t p).toNat, ?_, rfl⟩⟩
    rw [← hna]
    refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
    · have := ht0 p hp; omega
    · rw [Int.toNat_of_nonneg (ht0 p hp).1, Int.natCast_natAbs]
      exact (abs_dvd _ _).mpr (hkey p hp).1
  have hfib : ∀ k ∈ KS, ((defSols (f ^ 2 * d) N B).filter fun p => key p = k).card ≤ 4 := by
    intro k _
    set F := (defSols (f ^ 2 * d) N B).filter fun p => key p = k
    rcases F.eq_empty_or_nonempty with hF | ⟨p0, hp0⟩
    · rw [hF]; simp
    have hp0' := mem_filter.mp hp0
    have R0 := hR p0 hp0'.1
    have hinj : Set.InjOn (fun p => (u p, w p)) F := by
      intro p hp p' hp' h
      have hp1 := mem_filter.mp (mem_coe.mp hp)
      have hp1' := mem_filter.mp (mem_coe.mp hp')
      have hgg : g p = g p' := by
        have := hp1.2.trans hp1'.2.symm
        simp only [key, Prod.mk.injEq] at this
        exact this.1
      simp only [Prod.mk.injEq] at h
      have R := hR p hp1.1
      have R' := hR p' hp1'.1
      have hf' : (f : ℤ) ≠ 0 := by exact_mod_cast hf0.ne'
      refine Prod.ext ?_ ?_
      · rw [R.hu, R'.hu, hgg, h.1]
      · apply mul_left_cancel₀ hf'
        rw [R.hw, R'.hw, hgg, h.2]
    rw [← card_image_of_injOn hinj]
    -- every reduced solution in the class is a unit multiple of the one at `p0`
    have hsub : F.image (fun p => (u p, w p)) ⊆
        ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)).image fun rs =>
          (u p0 * rs.1 - d * w p0 * rs.2, u p0 * rs.2 + w p0 * rs.1) := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      have hp1 := mem_filter.mp hp
      have R := hR p hp1.1
      have hk := hp1.2.trans hp0'.2.symm
      simp only [key, Prod.mk.injEq] at hk
      obtain ⟨hgg, htt⟩ := hk
      have hnn : n p = n p0 := by
        have e := R.hN.symm.trans R0.hN
        rw [hgg] at e
        have hg0 : ((g p0 : ℕ) : ℤ) ^ 2 ≠ 0 := by have := R0.g_pos; positivity
        exact mul_left_cancel₀ hg0 e
      have htt' : t p = t p0 := by
        have := congrArg (fun x : ℕ => (x : ℤ)) htt
        rwa [Int.toNat_of_nonneg (ht0 p hp1.1).1, Int.toNat_of_nonneg (ht0 p0 hp0'.1).1] at this
      obtain ⟨r, s, hrs, he⟩ := def_class_units (q := (u p, w p)) (q' := (u p0, w p0)) hd0
        (hn0 p0 hp0'.1) (hkey p0 hp0'.1).1 (by rw [← hnn, R.hn]) (by rw [R0.hn])
        (by rw [← hnn, ← htt']; exact (hkey p hp1.1).2) (hkey p0 hp0'.1).2
      exact mem_image.mpr ⟨(r, s), hrs, he.symm⟩
    exact (card_le_card hsub).trans (card_image_le.trans (by decide))
  calc (defSols (f ^ 2 * d) N B).card ≤ 4 * KS.card := card_le_mul_card_image_of_maps_to hmaps _
         hfib
    _ ≤ 4 * N.natAbs.divisors.card ^ 3 := Nat.mul_le_mul_left _ hKS

end PierceBound
