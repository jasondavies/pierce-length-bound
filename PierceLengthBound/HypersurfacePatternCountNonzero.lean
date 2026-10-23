/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountPolynomial
public import PierceLengthBound.HypersurfacePatternCountScaling

/-! # Counting nonzero polynomial fibers, with all common factors included -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open scoped Matrix
noncomputable section
open MvPolynomial Finset

def nonzeroChartFibers (B : HypersurfaceChartPolynomial) (m : ℕ) :
    Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (crossSet m).filter fun uv =>
    chartPolynomialFiber B (chartFirstVertex m uv.1) ≠ 0 ∧
    eval (fun i => (uv.2 i : ℚ)) (chartPolynomialFiber B (chartFirstVertex m uv.1)) = 0

/-- Divide a fixed common-factor class injectively into the smaller first-vertex box. -/
lemma first_vertex_weight_sum {m g : ℕ} (hm : 0 < m) (hg : g ∈ m.divisors) :
    ∑ u ∈ (ibox3 m).filter (fun u => gcd4 m u = g),
      (normalShortR (m / g) (fun i => u i / (g : ℤ)) : ℝ)⁻¹ ≤
      5859 * ((m / g).divisors.card : ℝ) * (m / g : ℕ) ^ (8 / 3 : ℝ) := by
  classical
  let S := (ibox3 m).filter fun u => gcd4 m u = g
  let φ := fun u : Fin 3 → ℤ => fun i => u i / (g : ℤ)
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  have hn : 0 < m / g := Nat.div_pos (Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hg)) hg0
  have hsub : S.image φ ⊆ ibox3 (m / g) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨hub, hug⟩ := mem_filter.mp hu
    have he : primitiveFirstVertex m u = φ u := by
      funext i
      change u i / (gcd4 m u : ℤ) = u i / (g : ℤ)
      rw [hug]
    simpa only [he, hug] using primitiveFirstVertex_mem_ibox hm hub
  have hinj : Set.InjOn φ S := by
    intro u hu v hv he
    have hug := (mem_filter.mp hu).2
    have hvg := (mem_filter.mp hv).2
    funext i
    have hui : (g : ℤ) ∣ u i := hug ▸ gcd4_dvd m u i
    have hvi : (g : ℤ) ∣ v i := hvg ▸ gcd4_dvd m v i
    have hei : u i / (g : ℤ) = v i / (g : ℤ) := congrFun he i
    calc u i = (g : ℤ) * (u i / (g : ℤ)) := (Int.mul_ediv_cancel' hui).symm
      _ = (g : ℤ) * (v i / (g : ℤ)) := by rw [hei]
      _ = v i := Int.mul_ediv_cancel' hvi
  calc _ = ∑ u ∈ S.image φ, (normalShortR (m / g) u : ℝ)⁻¹ := (sum_image hinj).symm
    _ ≤ ∑ u ∈ ibox3 (m / g), (normalShortR (m / g) u : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := normal_short_weight_sum hn

/-- The contribution from one common-factor class of a nonzero polynomial family. -/
theorem nonzeroChartFibers_gcd_count (B : HypersurfaceChartPolynomial) {m g : ℕ}
    (hm : 0 < m) (hg : g ∈ m.divisors) :
    (((nonzeroChartFibers B m).filter fun uv => gcd4 m uv.1 = g).card : ℝ) ≤
      1423737 * (chartPolynomialFamily B).totalDegree * (tauMax m : ℝ) *
        (m : ℝ) ^ (11 / 3 : ℝ) := by
  classical
  let T := (nonzeroChartFibers B m).filter fun uv => gcd4 m uv.1 = g
  let S := (ibox3 m).filter fun u => gcd4 m u = g
  let n := m / g
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hg)) hg0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnle : n ≤ m := Nat.div_le_self _ _
  have hD : (0 : ℝ) ≤ (chartPolynomialFamily B).totalDegree := by positivity
  have hfiber u (hu : u ∈ S) :
      ((T.filter fun uv => uv.1 = u).card : ℝ) ≤
        (243 * (chartPolynomialFamily B).totalDegree * (m : ℝ) ^ 2 / n) *
          (normalShortR n (fun i => u i / (g : ℤ)) : ℝ)⁻¹ := by
    have hug := (mem_filter.mp hu).2
    let f := chartPolynomialFiber B (chartFirstVertex m u)
    by_cases hf : f = 0
    · have hz : T.filter (fun uv => uv.1 = u) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro uv huv
        obtain ⟨huvT, hueq⟩ := mem_filter.mp huv
        have hnonzero := (mem_filter.mp (mem_filter.mp huvT).1).2.1
        exact hnonzero (hueq.symm ▸ hf)
      rw [hz, card_empty, Nat.cast_zero]
      positivity
    · have hc := cross_congruence_polynomial_fiber_count hm (le_refl m) u hf
      have hi : (T.filter (fun uv => uv.1 = u)).card ≤
          ((ibox3 m).filter fun v => (∀ j, (m : ℤ) ∣ (u ⨯₃ v) j) ∧
            eval (fun i => (v i : ℚ)) f = 0).card := by
        apply card_le_card_of_injOn Prod.snd
        · intro uv huv
          obtain ⟨huvT, hueq⟩ := mem_filter.mp huv
          obtain ⟨huvgood, _⟩ := mem_filter.mp huvT
          obtain ⟨huvcross, _, huvzero⟩ := mem_filter.mp huvgood
          obtain ⟨huvbox, huvc⟩ := mem_filter.mp huvcross
          refine mem_filter.mpr ⟨(mem_product.mp huvbox).2, ?_, ?_⟩
          · simpa only [hueq] using huvc
          · simpa only [hueq] using huvzero
        · intro uv huv uv' huv' he
          exact Prod.ext ((mem_filter.mp huv).2.trans (mem_filter.mp huv').2.symm) he
      have hbound := (show ((T.filter fun uv => uv.1 = u).card : ℝ) ≤ _ by
        exact_mod_cast hi).trans hc
      have hfd := chartPolynomialFiber_degree B (chartFirstVertex m u)
      have hscaled : primitiveFirstVertex m u = (fun i => u i / (g : ℤ)) := by
        funext i
        change u i / (gcd4 m u : ℤ) = u i / (g : ℤ)
        rw [hug]
      rw [hug, hscaled] at hbound
      change ((T.filter fun uv => uv.1 = u).card : ℝ) ≤
        243 * (chartPolynomialFamily B).totalDegree * (m : ℝ) ^ 2 / n *
          (normalShortR n (fun i => u i / (g : ℤ)) : ℝ)⁻¹
      calc _ ≤ 243 * f.totalDegree * (m : ℝ) ^ 2 /
          ((n : ℝ) * normalShortR n (fun i => u i / (g : ℤ))) := hbound
        _ ≤ 243 * (chartPolynomialFamily B).totalDegree * (m : ℝ) ^ 2 /
          ((n : ℝ) * normalShortR n (fun i => u i / (g : ℤ))) := by gcongr
        _ = _ := by ring
  have hcard : (T.card : ℝ) =
      ∑ u ∈ S, ((T.filter fun uv => uv.1 = u).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := S) ?_, Nat.cast_sum]
    intro uv huv
    obtain ⟨hugood, hug⟩ := mem_filter.mp huv
    exact mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp (mem_filter.mp hugood).1).1).1, hug⟩
  have hw := first_vertex_weight_sum hm hg
  have htau : ((n.divisors.card : ℕ) : ℝ) ≤ tauMax m := by exact_mod_cast tau_le_tauMax hnle
  have hpow : (n : ℝ) ^ (5 / 3 : ℝ) ≤ (m : ℝ) ^ (5 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnle) (by norm_num)
  have he : (n : ℝ) ^ (8 / 3 : ℝ) / n = (n : ℝ) ^ (5 / 3 : ℝ) := by
    calc _ = (n : ℝ) ^ (8 / 3 : ℝ) / (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((8 / 3 : ℝ) - 1) := (Real.rpow_sub hnR _ _).symm
      _ = _ := by norm_num
  calc (T.card : ℝ)
      ≤ (243 * (chartPolynomialFamily B).totalDegree * (m : ℝ) ^ 2 / n) *
        ∑ u ∈ S, (normalShortR n (fun i => u i / (g : ℤ)) : ℝ)⁻¹ := by
          rw [hcard, mul_sum]
          exact sum_le_sum hfiber
    _ ≤ (243 * (chartPolynomialFamily B).totalDegree * (m : ℝ) ^ 2 / n) *
        (5859 * (n.divisors.card : ℝ) * (n : ℝ) ^ (8 / 3 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = 1423737 * (chartPolynomialFamily B).totalDegree * (n.divisors.card : ℝ) *
        (m : ℝ) ^ 2 * (n : ℝ) ^ (5 / 3 : ℝ) := by rw [← he]; ring
    _ ≤ 1423737 * (chartPolynomialFamily B).totalDegree * (tauMax m : ℝ) *
        (m : ℝ) ^ 2 * (m : ℝ) ^ (5 / 3 : ℝ) := by gcongr
    _ = _ := by
      rw [mul_assoc (1423737 * _ * _) _ _, ← Real.rpow_natCast (m : ℝ) 2,
        ← Real.rpow_add hmR]
      norm_num

/-- Summing the common-factor classes costs at most one further divisor maximum. -/
theorem nonzeroChartFibers_count (B : HypersurfaceChartPolynomial) {m : ℕ} (hm : 0 < m) :
    ((nonzeroChartFibers B m).card : ℝ) ≤
      1423737 * (chartPolynomialFamily B).totalDegree * (tauMax m : ℝ) ^ 2 *
        (m : ℝ) ^ (11 / 3 : ℝ) := by
  classical
  have hc : ((nonzeroChartFibers B m).card : ℝ) =
      ∑ g ∈ m.divisors, (((nonzeroChartFibers B m).filter fun uv => gcd4 m uv.1 = g).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := fun uv => gcd4 m uv.1) (t := m.divisors)
      (fun uv _ => Nat.mem_divisors.mpr ⟨gcd4_dvd_m m uv.1, hm.ne'⟩), Nat.cast_sum]
  have htau : (m.divisors.card : ℝ) ≤ tauMax m := by exact_mod_cast tau_le_tauMax (le_refl m)
  calc _ ≤ ∑ g ∈ m.divisors, 1423737 * (chartPolynomialFamily B).totalDegree *
      (tauMax m : ℝ) * (m : ℝ) ^ (11 / 3 : ℝ) := by
        rw [hc]
        exact sum_le_sum fun g hg => nonzeroChartFibers_gcd_count B hm hg
    _ = (m.divisors.card : ℝ) * (1423737 * (chartPolynomialFamily B).totalDegree *
      (tauMax m : ℝ) * (m : ℝ) ^ (11 / 3 : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (tauMax m : ℝ) * (1423737 * (chartPolynomialFamily B).totalDegree *
      (tauMax m : ℝ) * (m : ℝ) ^ (11 / 3 : ℝ)) := by gcongr
    _ = _ := by ring

lemma hypersurface_tauMax_mono {m X : ℕ} (h : m ≤ X) : tauMax m ≤ tauMax X := by
  unfold tauMax
  apply Finset.sup_le
  intro n hn
  exact tau_le_tauMax (by have := mem_range.mp hn; omega)

/-- The nonzero fibers contribute `X^(14/3)` times a slowly growing divisor factor. -/
theorem nonzeroChartFibers_sum (B : HypersurfaceChartPolynomial) {X : ℕ} (hX : 1 ≤ X) :
    ∑ m ∈ Icc 1 X, ((nonzeroChartFibers B m).card : ℝ) ≤
      1423737 * (chartPolynomialFamily B).totalDegree * (tauMax X : ℝ) ^ 2 *
        (X : ℝ) ^ (14 / 3 : ℝ) := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hm m (hm : m ∈ Icc 1 X) : ((nonzeroChartFibers B m).card : ℝ) ≤
      1423737 * (chartPolynomialFamily B).totalDegree * (tauMax X : ℝ) ^ 2 *
        (X : ℝ) ^ (11 / 3 : ℝ) := by
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hmx := (mem_Icc.mp hm).2
    refine (nonzeroChartFibers_count B hm0).trans ?_
    gcongr
    · exact_mod_cast hypersurface_tauMax_mono hmx
  calc _ ≤ ∑ m ∈ Icc 1 X, 1423737 * (chartPolynomialFamily B).totalDegree *
      (tauMax X : ℝ) ^ 2 * (X : ℝ) ^ (11 / 3 : ℝ) := sum_le_sum hm
    _ = (X : ℝ) * (1423737 * (chartPolynomialFamily B).totalDegree *
      (tauMax X : ℝ) ^ 2 * (X : ℝ) ^ (11 / 3 : ℝ)) := by
        simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ = _ := by
      have he : (X : ℝ) ^ (11 / 3 : ℝ) * X = (X : ℝ) ^ (14 / 3 : ℝ) := by
        calc _ = (X : ℝ) ^ (11 / 3 : ℝ) * (X : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (X : ℝ) ^ ((11 / 3 : ℝ) + 1) := (Real.rpow_add hXR _ _).symm
          _ = _ := by norm_num
      rw [mul_comm (X : ℝ), mul_assoc, he]

end
end PierceLengthBound.FixedDividend
