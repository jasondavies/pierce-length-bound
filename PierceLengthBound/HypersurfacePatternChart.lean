/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.MinorCount

/-! Rational maximal-minor charts of the Plücker cone, properness of a polynomial
on the cone, and clearing of the chart denominator: a proper polynomial pulls
back to a nonzero polynomial on every signed chart. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Finset
open scoped Matrix
noncomputable section

/-- The Plücker relations survive casting an integer vector to `ℚ`. -/
lemma pluckerRel_intCast {p : Fin 10 → ℤ} (hp : PluckerRel p) :
    PluckerRel (fun i => (p i : ℚ)) := by
  intro t i
  have h := hp t i
  simp only [uVec, vVec, cross_apply_cyc, Int.cast_id] at h ⊢
  exact_mod_cast h

/-- Numerators of a rational minor chart, with common denominator the pivot `m`. -/
def minorChartNumerator {R : Type*} [CommRing R] (t : Fin 10) (m : R)
    (u v : Fin 3 → R) (j : Fin 10) : R :=
  (if j = t then m ^ 2 else 0) +
    (∑ i : Fin 3, if j = puX t i then (puS t i : R) * m * u i else 0) +
    (∑ i : Fin 3, if j = pvX t i then (pvS t i : R) * m * v i else 0) +
    ∑ i : Fin 3, if j = pwX t i then (pwS t i : R) * (u ⨯₃ v) i else 0

/-- No companion index of a chart is its pivot. -/
private lemma chartPivot_ne (t : Fin 10) (i : Fin 3) :
    t ≠ puX t i ∧ t ≠ pvX t i ∧ t ≠ pwX t i ∧
    puX t i ≠ t ∧ pvX t i ≠ t ∧ pwX t i ≠ t := by
  revert t i; decide

/-- The three families of companion indices of a chart are disjoint. -/
private lemma chartCompanion_ne (t : Fin 10) (i k : Fin 3) :
    puX t i ≠ pvX t k ∧ puX t i ≠ pwX t k ∧ pvX t i ≠ puX t k ∧
    pvX t i ≠ pwX t k ∧ pwX t i ≠ puX t k ∧ pwX t i ≠ pvX t k := by
  revert t i k; decide

/-- Each family of companion indices of a chart is injective. -/
private lemma chartIndex_injective (t : Fin 10) :
    Function.Injective (puX t) ∧ Function.Injective (pvX t) ∧ Function.Injective (pwX t) := by
  revert t; decide

lemma minorChartNumerator_pivot {R : Type*} [CommRing R]
    (t : Fin 10) (m : R) (u v : Fin 3 → R) :
    minorChartNumerator t m u v t = m ^ 2 := by
  simp [minorChartNumerator, chartPivot_ne t]

lemma minorChartNumerator_u {R : Type*} [CommRing R]
    (t : Fin 10) (m : R) (u v : Fin 3 → R) (i : Fin 3) :
    minorChartNumerator t m u v (puX t i) = (puS t i : R) * m * u i := by
  simp [minorChartNumerator, chartPivot_ne t i, chartCompanion_ne t i,
    (chartIndex_injective t).1.eq_iff]

lemma minorChartNumerator_v {R : Type*} [CommRing R]
    (t : Fin 10) (m : R) (u v : Fin 3 → R) (i : Fin 3) :
    minorChartNumerator t m u v (pvX t i) = (pvS t i : R) * m * v i := by
  simp [minorChartNumerator, chartPivot_ne t i, chartCompanion_ne t i,
    (chartIndex_injective t).2.1.eq_iff]

lemma minorChartNumerator_w {R : Type*} [CommRing R]
    (t : Fin 10) (m : R) (u v : Fin 3 → R) (i : Fin 3) :
    minorChartNumerator t m u v (pwX t i) = (pwS t i : R) * (u ⨯₃ v) i := by
  simp [minorChartNumerator, chartPivot_ne t i, chartCompanion_ne t i,
    (chartIndex_injective t).2.2.eq_iff]

/-- On a Plücker vector, the chart numerators at pivot `t` are `p t * p j`. -/
lemma minorChartNumerator_reconstruct {p : Fin 10 → ℚ} (hp : PluckerRel p)
    (t j : Fin 10) :
    minorChartNumerator t (p t) (uVec p t) (vVec p t) j = p t * p j := by
  rcases cover t j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [minorChartNumerator_pivot, pow_two]
  · rw [minorChartNumerator_u, uVec]
    have h : (puS t i : ℚ) * (puS t i : ℚ) = 1 := by exact_mod_cast (sign_sq t i).1
    calc _ = ((puS t i : ℚ) * (puS t i : ℚ)) * (p t * p (puX t i)) := by ring
         _ = _ := by rw [h, one_mul]
  · rw [minorChartNumerator_v, vVec]
    have h : (pvS t i : ℚ) * (pvS t i : ℚ) = 1 := by exact_mod_cast (sign_sq t i).2.1
    calc _ = ((pvS t i : ℚ) * (pvS t i : ℚ)) * (p t * p (pvX t i)) := by ring
         _ = _ := by rw [h, one_mul]
  · rw [minorChartNumerator_w]
    exact (hp t i).symm

/-- The rational point of the chart: the numerators divided by the pivot `m`. -/
def minorChartPoint (t : Fin 10) (m : ℚ) (u v : Fin 3 → ℚ) (j : Fin 10) : ℚ :=
  minorChartNumerator t m u v j / m

/-- The rational chart reconstructs every Plücker vector whose pivot is nonzero. -/
lemma minorChartPoint_reconstruct {p : Fin 10 → ℚ} (hp : PluckerRel p)
    (t : Fin 10) (ht : p t ≠ 0) :
    minorChartPoint t (p t) (uVec p t) (vVec p t) = p := by
  funext j
  rw [minorChartPoint, minorChartNumerator_reconstruct hp]
  exact mul_div_cancel_left₀ _ ht

/-- Clear a common denominator `d` in the substitution of `N / d` into an arbitrary
polynomial `F`. -/
theorem exists_cleared_polynomial {σ τ : Type*} (F : MvPolynomial σ ℚ)
    (d : MvPolynomial τ ℚ) (N : σ → MvPolynomial τ ℚ) :
    ∃ e : ℕ, ∃ B : MvPolynomial τ ℚ, ∀ x : τ → ℚ, eval x d ≠ 0 →
      eval x B = (eval x d) ^ e * eval (fun j => eval x (N j) / eval x d) F := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, by simp⟩
  | add F G hF hG =>
    obtain ⟨e, B, hB⟩ := hF
    obtain ⟨f, C, hC⟩ := hG
    refine ⟨e + f, B * d ^ f + C * d ^ e, ?_⟩
    intro x hx
    simp only [map_add, map_mul, map_pow, hB x hx, hC x hx, pow_add]
    ring
  | mul_X F j hF =>
    obtain ⟨e, B, hB⟩ := hF
    refine ⟨e + 1, B * N j, ?_⟩
    intro x hx
    simp only [map_mul, hB x hx, eval_X, pow_succ]
    field_simp

/-- The universal minor polynomial in the fifteen matrix entries. -/
def universalMinor (t : Fin 10) : MvPolynomial (Fin 3 × Fin 5) ℚ :=
  plk (fun r c => X (r, c)) t

lemma eval_universalMinor (x : Fin 3 × Fin 5 → ℚ) (t : Fin 10) :
    eval x (universalMinor t) = plk (fun r c => x (r, c)) t := by
  simp [universalMinor, plk, minor3]

/-- Properness on the decomposable cone, expressed by a rational matrix witness. -/
def ProperOnMinorCone (F : MvPolynomial (Fin 10) ℚ) : Prop :=
  ∃ M : Fin 3 → Fin 5 → ℚ, eval (plk M) F ≠ 0

private def pivotFrame (t : Fin 10) (r : Fin 3) (c : Fin 5) : ℚ :=
  if c = (![ (trip t).1, (trip t).2.1, (trip t).2.2 ] : Fin 3 → Fin 5) r then 1 else 0

private lemma pivotFrame_minor (t : Fin 10) : plk (pivotFrame t) t = 1 := by
  fin_cases t <;> norm_num [plk, minor3, pivotFrame, trip]

lemma universalMinor_ne_zero (t : Fin 10) : universalMinor t ≠ 0 := by
  intro h
  have he := eval_universalMinor (fun rc => pivotFrame t rc.1 rc.2) t
  rw [h, map_zero, pivotFrame_minor] at he
  exact zero_ne_one he

/-- Every maximal-minor chart meets the nonvanishing locus of a proper polynomial. -/
theorem properOnMinorCone_nonzero_pivot {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) (t : Fin 10) :
    ∃ M : Fin 3 → Fin 5 → ℚ, plk M t ≠ 0 ∧ eval (plk M) F ≠ 0 := by
  let P : MvPolynomial (Fin 3 × Fin 5) ℚ := eval₂ C universalMinor F
  have hP : ∀ x : Fin 3 × Fin 5 → ℚ,
      eval x P = eval (plk (fun r c => x (r, c))) F := by
    intro x
    dsimp only [P]
    rw [← eval_assoc]
    have he : (eval x ∘ universalMinor) = plk (fun r c => x (r, c)) := by
      funext j
      exact eval_universalMinor x j
    rw [he]
  have hP0 : P ≠ 0 := by
    obtain ⟨M, hM⟩ := hF
    intro h
    apply hM
    have he := hP (fun rc => M rc.1 rc.2)
    simpa [h] using he.symm
  have hprod : P * universalMinor t ≠ 0 := mul_ne_zero hP0 (universalMinor_ne_zero t)
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 × Fin 5 → ℚ, eval x (P * universalMinor t) ≠ 0 := by
    by_contra! hn
    apply hprod
    apply MvPolynomial.funext
    intro x
    simpa using hn x
  rw [map_mul, hP, eval_universalMinor] at hx
  exact ⟨fun r c => x (r, c), (mul_ne_zero_iff.mp hx).2, (mul_ne_zero_iff.mp hx).1⟩

/-- Clearing denominators in the chart at pivot `t`, with pivot value `s m` for a
fixed `s ≠ 0` (used with `s = ±1`), gives a nonzero polynomial `B` in `(v, m, u)`
that vanishes at the chart coordinates of every integral Plücker vector with
nonzero pivot on which `F` vanishes. -/
theorem exists_minorChart_polynomial {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) (t : Fin 10) (s : ℚ) (hs : s ≠ 0) :
    ∃ B : MvPolynomial (Fin 3 ⊕ Fin 4) ℚ, B ≠ 0 ∧
      ∀ p : Fin 10 → ℤ, PluckerRel p → p t ≠ 0 →
        eval (fun j => (p j : ℚ)) F = 0 →
        ∀ m : ℚ, (p t : ℚ) = s * m →
          eval (Sum.elim (fun i => (vVec p t i : ℚ))
            (Fin.cons m (fun i => (uVec p t i : ℚ)))) B = 0 := by
  let d : MvPolynomial (Fin 3 ⊕ Fin 4) ℚ := C s * X (Sum.inr 0)
  let U : Fin 3 → MvPolynomial (Fin 3 ⊕ Fin 4) ℚ := fun i => X (Sum.inr i.succ)
  let V : Fin 3 → MvPolynomial (Fin 3 ⊕ Fin 4) ℚ := fun i => X (Sum.inl i)
  let N := minorChartNumerator t d U V
  obtain ⟨e, B, hB⟩ := exists_cleared_polynomial F d N
  have hB' (m : ℚ) (u v : Fin 3 → ℚ) (hm : s * m ≠ 0) :
      eval (Sum.elim v (Fin.cons m u)) B =
        (s * m) ^ e * eval (minorChartPoint t (s * m) u v) F := by
    have hd : eval (Sum.elim v (Fin.cons m u)) d = s * m := by simp [d]
    have hN : ∀ j, eval (Sum.elim v (Fin.cons m u)) (N j) =
        minorChartNumerator t (s * m) u v j := by
      intro j
      simp [N, minorChartNumerator, cross_apply_cyc, d, U, V, apply_ite]
    have he := hB (Sum.elim v (Fin.cons m u)) (by rwa [hd])
    change eval (Sum.elim v (Fin.cons m u)) B =
      (s * m) ^ e * eval (fun j => minorChartNumerator t (s * m) u v j / (s * m)) F
    simpa only [hd, hN] using he
  refine ⟨B, ?_, ?_⟩
  · obtain ⟨M, hM, hMF⟩ := properOnMinorCone_nonzero_pivot hF t
    have hsm : s * (plk M t / s) = plk M t := by field_simp
    have he := hB' (plk M t / s) (uVec (plk M) t) (vVec (plk M) t)
      (by rwa [hsm])
    rw [hsm, minorChartPoint_reconstruct (plucker M) t hM] at he
    intro hzero
    rw [hzero, map_zero] at he
    exact (mul_ne_zero (pow_ne_zero _ hM) hMF) he.symm
  · intro p hp hpt hpF m hpm
    have hptQ : (p t : ℚ) ≠ 0 := by exact_mod_cast hpt
    have he := hB' m (fun i => (uVec p t i : ℚ)) (fun i => (vVec p t i : ℚ))
      (by rwa [← hpm])
    have hu : (fun i => (uVec p t i : ℚ)) = uVec (fun i => (p i : ℚ)) t := by
      funext i
      simp [uVec]
    have hv : (fun i => (vVec p t i : ℚ)) = vVec (fun i => (p i : ℚ)) t := by
      funext i
      simp [vVec]
    rw [← hpm, hu, hv, minorChartPoint_reconstruct (pluckerRel_intCast hp) t hptQ,
      hpF, mul_zero] at he
    simpa only [hu, hv] using he

end
end PierceLengthBound.FixedDividend
