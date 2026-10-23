/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.MinorCount

/-! Rational maximal-minor charts and polynomial denominator clearing. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Finset
noncomputable section

/-- The same determinant formula as `minor3`, over any commutative ring. -/
def minor3Ring {R : Type*} [CommRing R] (M : Fin 3 → Fin 5 → R)
    (c1 c2 c3 : Fin 5) : R :=
  M 0 c1 * (M 1 c2 * M 2 c3 - M 1 c3 * M 2 c2) -
    M 0 c2 * (M 1 c1 * M 2 c3 - M 1 c3 * M 2 c1) +
    M 0 c3 * (M 1 c1 * M 2 c2 - M 1 c2 * M 2 c1)

/-- The ten maximal minors over an arbitrary commutative ring. -/
def plkRing {R : Type*} [CommRing R] (M : Fin 3 → Fin 5 → R) (t : Fin 10) : R :=
  minor3Ring M (trip t).1 (trip t).2.1 (trip t).2.2

def chartU {R : Type*} [CommRing R] (p : Fin 10 → R) (t : Fin 10) (i : Fin 3) : R :=
  (puS t i : R) * p (puX t i)

def chartV {R : Type*} [CommRing R] (p : Fin 10 → R) (t : Fin 10) (i : Fin 3) : R :=
  (pvS t i : R) * p (pvX t i)

def crossRing {R : Type*} [CommRing R] (u v : Fin 3 → R) (i : Fin 3) : R :=
  u (i + 1) * v (i + 2) - u (i + 2) * v (i + 1)

def PluckerRelRing {R : Type*} [CommRing R] (p : Fin 10 → R) : Prop :=
  ∀ t i, p t * p (pwX t i) = (pwS t i : R) * crossRing (chartU p t) (chartV p t) i

/-- Ring homomorphisms commute with the defect of a Plücker relation. -/
private lemma map_pluckerDefect {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Fin 3 → Fin 5 → R) (t : Fin 10) (i : Fin 3) :
    f (plkRing M t * plkRing M (pwX t i) -
        (pwS t i : R) * crossRing (chartU (plkRing M) t) (chartV (plkRing M) t) i) =
      plkRing (fun r c => f (M r c)) t * plkRing (fun r c => f (M r c)) (pwX t i) -
        (pwS t i : S) * crossRing (chartU (plkRing fun r c => f (M r c)) t)
          (chartV (plkRing fun r c => f (M r c)) t) i := by
  simp only [plkRing, minor3Ring, chartU, chartV, crossRing, map_add, map_sub, map_mul,
    map_intCast]

/-- The integer identity `plucker` holds at every integer point, so it holds for the universal
integer matrix; specializing that matrix gives it over any commutative ring. -/
lemma pluckerRing {R : Type*} [CommRing R] (M : Fin 3 → Fin 5 → R) :
    PluckerRelRing (plkRing M) := by
  intro t i
  let U : Fin 3 → Fin 5 → MvPolynomial (Fin 3 × Fin 5) ℤ := fun r c => X (r, c)
  have hU : plkRing U t * plkRing U (pwX t i) -
      (pwS t i : MvPolynomial (Fin 3 × Fin 5) ℤ) *
        crossRing (chartU (plkRing U) t) (chartV (plkRing U) t) i = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_pluckerDefect, map_zero, sub_eq_zero]
    simp only [U, eval_X, Int.cast_id]
    exact plucker (fun r c => x (r, c)) t i
  have h := congrArg (eval₂Hom (Int.castRingHom R) fun rc => M rc.1 rc.2) hU
  rw [map_pluckerDefect, map_zero, sub_eq_zero] at h
  simpa only [U, eval₂Hom_X', eq_intCast] using h

lemma pluckerRelRing_intCast {p : Fin 10 → ℤ} (hp : PluckerRel p) :
    PluckerRelRing (fun i => (p i : ℚ)) := by
  intro t i
  have h := hp t i
  dsimp [chartU, chartV, crossRing]
  dsimp [uVec, vVec, cross3] at h
  exact_mod_cast h

/-- Numerators of a rational minor chart, with common denominator the pivot `m`. -/
def minorChartNumerator {R : Type*} [CommRing R] (t : Fin 10) (m : R)
    (u v : Fin 3 → R) (j : Fin 10) : R :=
  (if j = t then m ^ 2 else 0) +
    (∑ i : Fin 3, if j = puX t i then (puS t i : R) * m * u i else 0) +
    (∑ i : Fin 3, if j = pvX t i then (pvS t i : R) * m * v i else 0) +
    ∑ i : Fin 3, if j = pwX t i then (pwS t i : R) * crossRing u v i else 0

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
    minorChartNumerator t m u v (pwX t i) = (pwS t i : R) * crossRing u v i := by
  simp [minorChartNumerator, chartPivot_ne t i, chartCompanion_ne t i,
    (chartIndex_injective t).2.2.eq_iff]

lemma minorChartNumerator_reconstruct {p : Fin 10 → ℚ} (hp : PluckerRelRing p)
    (t j : Fin 10) :
    minorChartNumerator t (p t) (chartU p t) (chartV p t) j = p t * p j := by
  rcases cover t j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [minorChartNumerator_pivot, pow_two]
  · rw [minorChartNumerator_u, chartU]
    have h : (puS t i : ℚ) * (puS t i : ℚ) = 1 := by exact_mod_cast (sign_sq t i).1
    calc _ = ((puS t i : ℚ) * (puS t i : ℚ)) * (p t * p (puX t i)) := by ring
         _ = _ := by rw [h, one_mul]
  · rw [minorChartNumerator_v, chartV]
    have h : (pvS t i : ℚ) * (pvS t i : ℚ) = 1 := by exact_mod_cast (sign_sq t i).2.1
    calc _ = ((pvS t i : ℚ) * (pvS t i : ℚ)) * (p t * p (pvX t i)) := by ring
         _ = _ := by rw [h, one_mul]
  · rw [minorChartNumerator_w]
    exact (hp t i).symm

/-- The rational chart reconstructs every Plücker vector whose chosen pivot is nonzero. -/
def minorChartPoint (t : Fin 10) (m : ℚ) (u v : Fin 3 → ℚ) (j : Fin 10) : ℚ :=
  minorChartNumerator t m u v j / m

lemma minorChartPoint_reconstruct {p : Fin 10 → ℚ} (hp : PluckerRelRing p)
    (t : Fin 10) (ht : p t ≠ 0) :
    minorChartPoint t (p t) (chartU p t) (chartV p t) = p := by
  funext j
  rw [minorChartPoint, minorChartNumerator_reconstruct hp]
  exact mul_div_cancel_left₀ _ ht

/-- Clear a common denominator in a polynomial substitution without a homogeneity assumption. -/
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
  plkRing (fun r c => X (r, c)) t

lemma eval_universalMinor (x : Fin 3 × Fin 5 → ℚ) (t : Fin 10) :
    eval x (universalMinor t) = plkRing (fun r c => x (r, c)) t := by
  simp [universalMinor, plkRing, minor3Ring]

/-- Properness on the decomposable cone, expressed by a rational matrix witness. -/
def ProperOnMinorCone (F : MvPolynomial (Fin 10) ℚ) : Prop :=
  ∃ M : Fin 3 → Fin 5 → ℚ, eval (plkRing M) F ≠ 0

private def pivotFrame (t : Fin 10) (r : Fin 3) (c : Fin 5) : ℚ :=
  if c = (![ (trip t).1, (trip t).2.1, (trip t).2.2 ] : Fin 3 → Fin 5) r then 1 else 0

private lemma pivotFrame_minor (t : Fin 10) : plkRing (pivotFrame t) t = 1 := by
  fin_cases t <;> norm_num [plkRing, minor3Ring, pivotFrame, trip]

lemma universalMinor_ne_zero (t : Fin 10) : universalMinor t ≠ 0 := by
  intro h
  have he := eval_universalMinor (fun rc => pivotFrame t rc.1 rc.2) t
  rw [h, map_zero, pivotFrame_minor] at he
  exact zero_ne_one he

/-- Every maximal-minor chart meets the nonvanishing locus of a proper polynomial. -/
theorem properOnMinorCone_nonzero_pivot {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) (t : Fin 10) :
    ∃ M : Fin 3 → Fin 5 → ℚ, plkRing M t ≠ 0 ∧ eval (plkRing M) F ≠ 0 := by
  let P : MvPolynomial (Fin 3 × Fin 5) ℚ := eval₂ C universalMinor F
  have hP : ∀ x : Fin 3 × Fin 5 → ℚ,
      eval x P = eval (plkRing (fun r c => x (r, c))) F := by
    intro x
    dsimp only [P]
    rw [← eval_assoc]
    have he : (eval x ∘ universalMinor) = plkRing (fun r c => x (r, c)) := by
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

/-- Polynomial clearing of the rational chart, with a nonzero pullback on every pivot.
The sign `s` may in particular be either `1` or `-1`. -/
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
      simp [N, minorChartNumerator, crossRing, d, U, V, apply_ite]
    have he := hB (Sum.elim v (Fin.cons m u)) (by rwa [hd])
    change eval (Sum.elim v (Fin.cons m u)) B =
      (s * m) ^ e * eval (fun j => minorChartNumerator t (s * m) u v j / (s * m)) F
    simpa only [hd, hN] using he
  refine ⟨B, ?_, ?_⟩
  · obtain ⟨M, hM, hMF⟩ := properOnMinorCone_nonzero_pivot hF t
    have hsm : s * (plkRing M t / s) = plkRing M t := by field_simp
    have he := hB' (plkRing M t / s) (chartU (plkRing M) t) (chartV (plkRing M) t)
      (by rwa [hsm])
    rw [hsm, minorChartPoint_reconstruct (pluckerRing M) t hM] at he
    intro hzero
    rw [hzero, map_zero] at he
    exact (mul_ne_zero (pow_ne_zero _ hM) hMF) he.symm
  · intro p hp hpt hpF m hpm
    have hptQ : (p t : ℚ) ≠ 0 := by exact_mod_cast hpt
    have he := hB' m (fun i => (uVec p t i : ℚ)) (fun i => (vVec p t i : ℚ))
      (by rwa [← hpm])
    have hu : (fun i => (uVec p t i : ℚ)) = chartU (fun i => (p i : ℚ)) t := by
      funext i
      simp [uVec, chartU]
    have hv : (fun i => (vVec p t i : ℚ)) = chartV (fun i => (p i : ℚ)) t := by
      funext i
      simp [vVec, chartV]
    rw [← hpm, hu, hv, minorChartPoint_reconstruct (pluckerRelRing_intCast hp) t hptQ,
      hpF, mul_zero] at he
    simpa only [hu, hv] using he

end
end PierceLengthBound.FixedDividend
