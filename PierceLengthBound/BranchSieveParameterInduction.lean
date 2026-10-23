/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveParameterSpecialization
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The finite-fiber induction from a one-parameter irreducibility estimate
to several parameters. The one-parameter input specializes the first parameter
and keeps the remaining ones as variables; `BranchSieveMultivariateHilbert`
supplies it by Kronecker substitution. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

def branchTailFiber {r : ℕ} (S : Finset (Fin (r + 1) → ℤ)) (t : ℤ) :
    Finset (Fin r → ℤ) := (S.filter (fun x => x 0 = t)).image Fin.tail

lemma branchTailFiber_card {r : ℕ} (S : Finset (Fin (r + 1) → ℤ)) (t : ℤ) :
    (branchTailFiber S t).card = (S.filter (fun x => x 0 = t)).card := by
  classical
  apply card_image_iff.mpr
  intro x hx y hy h
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
  · exact congrFun h j

lemma mem_branchTailFiber {r : ℕ} (S : Finset (Fin (r + 1) → ℤ))
    (t : ℤ) (u : Fin r → ℤ) :
    u ∈ branchTailFiber S t ↔ Fin.cons t u ∈ S := by
  classical
  constructor
  · intro hu
    obtain ⟨x, hx, htail⟩ := mem_image.mp hu
    obtain ⟨hx, ht⟩ := mem_filter.mp hx
    have he : Fin.cons t u = x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ht.symm
      · exact (congrFun htail j).symm
    rwa [he]
  · intro hu
    apply mem_image.mpr
    exact ⟨Fin.cons t u, mem_filter.mpr ⟨hu, by simp⟩, by simp⟩

theorem branch_integer_box_card {r B : ℕ} (S : Finset (Fin r → ℤ))
    (hS : ∀ x ∈ S, ∀ j, |x j| ≤ (B : ℤ)) :
    S.card ≤ (2 * B + 1) ^ r := by
  classical
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin r => Icc (-(B : ℤ)) B) := by
    intro x hx
    exact Fintype.mem_piFinset.mpr fun j => mem_Icc.mpr (abs_le.mp (hS x hx j))
  apply (card_le_card hsub).trans
  simp only [Fintype.card_piFinset, Int.card_Icc, prod_const, card_fin]
  gcongr
  omega

theorem branch_integer_interval_card {B : ℕ} (S : Finset ℤ)
    (hS : ∀ x ∈ S, |x| ≤ (B : ℤ)) : S.card ≤ 2 * B + 1 := by
  simpa using branch_integer_box_card
    (S.map ⟨fun x (_ : Fin 1) => x, fun _ _ h => congrFun h 0⟩) fun _ hx _ => by
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      exact hS a ha

/-- Split a finite set of integer tuples by first coordinate: the exceptional
first coordinates contribute whole boxes, and every other fiber is bounded by
the induction hypothesis. -/
theorem branch_parameter_fiber_count {r B : ℕ} (hB : 1 ≤ B)
    (S : Finset (Fin (r + 1) → ℤ)) (hS : ∀ x ∈ S, ∀ j, |x j| ≤ (B : ℤ))
    (bad : ℤ → Prop) [DecidablePred bad] {Cbad Cgood : ℝ} (hgood0 : 0 ≤ Cgood)
    (hbad : (((S.image (fun x => x 0)).filter bad).card : ℝ) ≤ Cbad)
    (hgood : ∀ t ∈ S.image (fun x => x 0), ¬ bad t →
      ((branchTailFiber S t).card : ℝ) ≤ Cgood) :
    (S.card : ℝ) ≤ Cbad * (3 * B : ℝ) ^ r + 3 * B * Cgood := by
  classical
  let T := S.image (fun x => x 0)
  have hT : (T.card : ℝ) ≤ 3 * B := by
    have h := branch_integer_interval_card T (fun t ht => by
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
      exact hS x hx 0)
    have hc : (T.card : ℝ) ≤ (2 * B + 1 : ℕ) := by exact_mod_cast h
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
    push_cast at hc
    linarith
  have hfiber (t : ℤ) : ((branchTailFiber S t).card : ℝ) ≤ (3 * B : ℝ) ^ r := by
    have h := branch_integer_box_card (branchTailFiber S t) (fun u hu j =>
      hS (Fin.cons t u) ((mem_branchTailFiber S t u).mp hu) j.succ)
    have hc : ((branchTailFiber S t).card : ℝ) ≤ ((2 * B + 1 : ℕ) : ℝ) ^ r := by
      exact_mod_cast h
    apply hc.trans
    gcongr
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
    push_cast
    linarith
  have hsplit (t : ℤ) (ht : t ∈ T) : ((branchTailFiber S t).card : ℝ) ≤
      (if bad t then (3 * B : ℝ) ^ r else 0) + Cgood := by
    by_cases hb : bad t
    · simp only [hb, ite_true]
      exact (hfiber t).trans (le_add_of_nonneg_right hgood0)
    · simpa only [hb, ite_false, zero_add] using hgood t ht hb
  calc
    (S.card : ℝ) = ∑ t ∈ T, ((branchTailFiber S t).card : ℝ) := by
      rw [card_eq_sum_card_image (fun x => x 0) S, Nat.cast_sum]
      exact sum_congr rfl fun t _ => by rw [branchTailFiber_card]
    _ ≤ ∑ t ∈ T, ((if bad t then (3 * B : ℝ) ^ r else 0) + Cgood) :=
      sum_le_sum hsplit
    _ = ((T.filter bad).card : ℝ) * (3 * B : ℝ) ^ r + T.card * Cgood := by
      simp [sum_add_distrib, ← sum_filter, nsmul_eq_mul]
    _ ≤ Cbad * (3 * B : ℝ) ^ r + 3 * B * Cgood := by gcongr

/-- The coefficient-height increase at one step costs just one extra
fourth power of `1+log B` in the outer induction. -/
theorem branch_specialized_log_height_bound (d H B : ℕ) (hB : 1 ≤ B) :
    1 + Real.log (((d + 1) * H * B ^ d + 1 : ℕ) : ℝ) ≤
      ((d : ℝ) + Real.log (d + 2 : ℕ) + 1) *
        (1 + Real.log (H + 1 : ℕ)) * (1 + Real.log B) := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpow : (1 : ℝ) ≤ (B : ℝ) ^ d := one_le_pow₀ hBR
  have hH : 0 ≤ Real.log (H + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hD : 0 ≤ Real.log (d + 2 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ d + 2 by omega))
  have hLB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBR
  have hsize : (((d + 1) * H * B ^ d + 1 : ℕ) : ℝ) ≤
      (d + 2 : ℕ) * (H + 1 : ℕ) * (B : ℝ) ^ d := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ d by positivity,
      show (0 : ℝ) ≤ H by positivity]
  have hl := Real.log_le_log (by positivity) hsize
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
  nlinarith [mul_nonneg hH hLB, mul_nonneg hD hH, mul_nonneg hD hLB,
    mul_nonneg (mul_nonneg hD hH) hLB,
    mul_nonneg (show (0 : ℝ) ≤ d by positivity) hH,
    mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ d by positivity) hH) hLB]

/-- The one-parameter head estimate: specializing the first parameter at
integers `|t| ≤ B`, with the other `r` parameters kept as polynomial
variables, leaves the family irreducible over `ℚ[T₂, …, T_{r+1}]` for all
but `O((1 + log (H+1))^4 √B (1 + log B))` values of `t`. -/
def BranchHeadIrreducibilityEstimate (r d : ℕ) (C : ℝ) : Prop :=
  ∀ p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ), p.Monic →
    Irreducible (branchFamilyRational p) → p.natDegree ≤ d →
    (∀ j, (p.coeff j).totalDegree ≤ d) →
    ∀ H B : ℕ, (∀ j s, |(p.coeff j).coeff s| ≤ (H : ℤ)) → 1 ≤ B →
    ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧
        ¬ Irreducible (branchFamilyRational (branchFamilyHead t p))) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        Real.sqrt B * (1 + Real.log B)

/-- The size `(1 + log (H+1))^4 B^r / √B (1 + log B)^(4r+1)` of the bound in
Theorem 10.4. -/
def branchHilbertSize (r H B : ℕ) : ℝ :=
  (1 + Real.log (H + 1 : ℕ)) ^ 4 * ((B : ℝ) ^ r / Real.sqrt B) *
    (1 + Real.log B) ^ (4 * r + 1)

lemma branchHilbertSize_nonneg (r H B : ℕ) (hB : 1 ≤ B) :
    0 ≤ branchHilbertSize r H B := by
  have hlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hB)
  unfold branchHilbertSize
  positivity

lemma branchFamilyEval_irreducible_zero
    (p : Polynomial (MvPolynomial (Fin 0) ℤ))
    (hp : Irreducible (branchFamilyRational p)) (t : Fin 0 → ℤ) :
    Irreducible (branchFamilyEval t p) := by
  let e := Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv ℚ (Fin 0))
  have h := (MulEquiv.irreducible_iff (f := e.toMulEquiv)).mpr hp
  change Irreducible (e (branchFamilyRational p)) at h
  have he : e (branchFamilyRational p) = branchFamilyEval t p := by
    change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
    rw [Polynomial.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      exact Fin.elim0 i
  rwa [he] at h

/-- The size bookkeeping of one induction step: the bad first coordinates
and the good fibers, of specialized height `(d+1) H B^d`, together fit the
size for `r + 1` parameters. -/
theorem branch_parameter_induction_size (r d H B : ℕ) (hB : 1 ≤ B)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    C₁ * (1 + Real.log (H + 1 : ℕ)) ^ 4 * Real.sqrt B * (1 + Real.log B) *
        (3 * B : ℝ) ^ r +
      3 * B * (C₂ * branchHilbertSize r ((d + 1) * H * B ^ d) B) ≤
      (C₁ * 3 ^ r + 3 * C₂ * ((d : ℝ) + Real.log (d + 2 : ℕ) + 1) ^ 4) *
        branchHilbertSize (r + 1) H B := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < B := by linarith
  have hsqrt : Real.sqrt (B : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hBpos)
  have hsid : Real.sqrt (B : ℝ) = B / Real.sqrt B := by
    apply (eq_div_iff hsqrt).mpr
    exact Real.mul_self_sqrt (by positivity)
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBR
  have hlogH : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hlogH' : 0 ≤ Real.log ((d + 1) * H * B ^ d + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ (d + 1) * H * B ^ d + 1 by omega))
  have hlogD : 0 ≤ Real.log (d + 2 : ℕ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ d + 2 by omega))
  have hL := branch_specialized_log_height_bound d H B hB
  have hfirst :
      C₁ * (1 + Real.log (H + 1 : ℕ)) ^ 4 * Real.sqrt B * (1 + Real.log B) *
        (3 * B : ℝ) ^ r ≤ C₁ * 3 ^ r * branchHilbertSize (r + 1) H B := by
    rw [branchHilbertSize]
    calc
      _ = C₁ * 3 ^ r * ((1 + Real.log (H + 1 : ℕ)) ^ 4 *
        ((B : ℝ) ^ (r + 1) / Real.sqrt B) * (1 + Real.log B)) := by
          conv_lhs => rw [hsid]
          rw [mul_pow, pow_succ]
          ring
      _ ≤ _ := by
        gcongr
        simpa only [pow_one] using
          (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + Real.log B)
            (show 1 ≤ 4 * (r + 1) + 1 by omega))
  have hsecond :
      3 * B * (C₂ * branchHilbertSize r ((d + 1) * H * B ^ d) B) ≤
        (3 * C₂ * ((d : ℝ) + Real.log (d + 2 : ℕ) + 1) ^ 4) *
          branchHilbertSize (r + 1) H B := by
    unfold branchHilbertSize
    calc
      _ ≤ 3 * B * (C₂ *
          ((((d : ℝ) + Real.log (d + 2 : ℕ) + 1) *
            (1 + Real.log (H + 1 : ℕ)) * (1 + Real.log B)) ^ 4 *
              ((B : ℝ) ^ r / Real.sqrt B) * (1 + Real.log B) ^ (4 * r + 1))) := by
        gcongr
      _ = _ := by
        rw [show 4 * (r + 1) + 1 = 4 + (4 * r + 1) by omega,
          pow_add, pow_succ]
        ring
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

/-- The full parameter induction, with explicit height dependence. For four
parameters the power of the box size is `B^4 / sqrt B`. -/
theorem branch_multivariate_hilbert_bound_of_head_estimates (r d : ℕ)
    (hhead : ∀ k < r, ∃ C : ℝ, 0 < C ∧ BranchHeadIrreducibilityEstimate k d C) :
    ∃ C : ℝ, 0 < C ∧
      ∀ p : Polynomial (MvPolynomial (Fin r) ℤ), p.Monic →
        Irreducible (branchFamilyRational p) → p.natDegree ≤ d →
        (∀ j, (p.coeff j).totalDegree ≤ d) →
        ∀ H B : ℕ, (∀ j s, |(p.coeff j).coeff s| ≤ (H : ℤ)) → 1 ≤ B →
        ∀ S : Finset (Fin r → ℤ),
          (∀ t ∈ S, (∀ j, |t j| ≤ (B : ℤ)) ∧ ¬ Irreducible (branchFamilyEval t p)) →
          (S.card : ℝ) ≤ C * branchHilbertSize r H B := by
  classical
  induction r with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro p hp hirr hd hcoeff H B hH hB S hS
    have hS0 : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact (hS t ht).2 (branchFamilyEval_irreducible_zero p hirr t)
    simpa only [hS0, card_empty, Nat.cast_zero, one_mul] using
      branchHilbertSize_nonneg 0 H B hB
  | succ r ih =>
    obtain ⟨C₁, hC₁, h₁⟩ := hhead r (by omega)
    obtain ⟨C₂, hC₂, h₂⟩ := ih (fun k hk => hhead k (by omega))
    let L : ℝ := (d : ℝ) + Real.log (d + 2 : ℕ) + 1
    refine ⟨C₁ * 3 ^ r + 3 * C₂ * L ^ 4, by positivity, ?_⟩
    intro p hp hirr hd hcoeff H B hH hB S hS
    let bad : ℤ → Prop := fun t =>
      ¬ Irreducible (branchFamilyRational (branchFamilyHead t p))
    let H' := (d + 1) * H * B ^ d
    have hbad : (((S.image (fun x => x 0)).filter bad).card : ℝ) ≤
        C₁ * (1 + Real.log (H + 1 : ℕ)) ^ 4 * Real.sqrt B * (1 + Real.log B) := by
      apply h₁ p hp hirr hd hcoeff H B hH hB
      intro t ht
      obtain ⟨ht, hb⟩ := mem_filter.mp ht
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
      exact ⟨(hS x hx).1 0, hb⟩
    have hgood (t : ℤ) (ht : t ∈ S.image (fun x => x 0)) (hb : ¬ bad t) :
        ((branchTailFiber S t).card : ℝ) ≤ C₂ * branchHilbertSize r H' B := by
      have htB : |t| ≤ (B : ℤ) := by
        obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
        exact (hS x hx).1 0
      obtain ⟨hnd, htd, hht⟩ := branchFamilyHead_degree_height p hd hcoeff hH hB htB
      apply h₂ (branchFamilyHead t p) (hp.map _) (not_not.mp hb) hnd htd H' B hht hB
      intro u hu
      have hx := hS (Fin.cons t u) ((mem_branchTailFiber S t u).mp hu)
      exact ⟨fun j => hx.1 j.succ, by simpa only [branchFamilyEval_head] using hx.2⟩
    have hfib := branch_parameter_fiber_count hB S (fun x hx => (hS x hx).1) bad
      (mul_nonneg hC₂.le (branchHilbertSize_nonneg r H' B hB)) hbad hgood
    exact hfib.trans (branch_parameter_induction_size r d H B hB hC₁.le hC₂.le)

end
end PierceLengthBound.FixedDividend
