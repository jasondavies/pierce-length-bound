/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveResultantGeneric
public import PierceLengthBound.BranchSieveParameterSpecialization

/-! A fixed integer polynomial family for the four first-frame minors.
The vertex order is `(p₀,p₁,p₃,p₆)`. All denominators are cleared before
specializing the dividend, so degree and coefficient bounds are uniform. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Denominator clearing over the integers, with one identity valid in every
field. The cleared polynomial is independent of the specialization field. -/
theorem branch_exists_cleared_mvpolynomial {σ τ : Type}
    (F : MvPolynomial σ ℤ) (d : MvPolynomial τ ℤ) (N : σ → MvPolynomial τ ℤ) :
    ∃ e : ℕ, ∃ B : MvPolynomial τ ℤ, ∀ (K : Type) [Field K] (x : τ → K),
      MvPolynomial.eval₂ (Int.castRingHom K) x d ≠ 0 →
      MvPolynomial.eval₂ (Int.castRingHom K) x B =
        (MvPolynomial.eval₂ (Int.castRingHom K) x d) ^ e *
          MvPolynomial.eval₂ (Int.castRingHom K)
            (fun j => MvPolynomial.eval₂ (Int.castRingHom K) x (N j) /
              MvPolynomial.eval₂ (Int.castRingHom K) x d) F := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨0, MvPolynomial.C c, by
      intros
      simp only [MvPolynomial.eval₂_C, pow_zero, one_mul]⟩
  | add F G hF hG =>
    obtain ⟨e, B, hB⟩ := hF
    obtain ⟨f, C, hC⟩ := hG
    refine ⟨e + f, B * d ^ f + C * d ^ e, ?_⟩
    intro K _ x hx
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      hB K x hx, hC K x hx, pow_add]
    ring
  | mul_X F j hF =>
    obtain ⟨e, B, hB⟩ := hF
    refine ⟨e + 1, B * N j, ?_⟩
    intro K _ x hx
    simp only [MvPolynomial.eval₂_mul, hB K x hx, MvPolynomial.eval₂_X, pow_succ]
    field_simp

/-- Coefficientwise denominator clearing preserves a separate polynomial
variable. The resulting family retains integer coefficients. -/
theorem branch_exists_cleared_polynomial {σ τ : Type}
    (F : Polynomial (MvPolynomial σ ℤ)) (d : MvPolynomial τ ℤ)
    (N : σ → MvPolynomial τ ℤ) :
    ∃ e : ℕ, ∃ B : Polynomial (MvPolynomial τ ℤ), ∀ (K : Type) [Field K] (x : τ → K),
      MvPolynomial.eval₂ (Int.castRingHom K) x d ≠ 0 →
      B.map (MvPolynomial.eval₂Hom (Int.castRingHom K) x) =
        Polynomial.C ((MvPolynomial.eval₂ (Int.castRingHom K) x d) ^ e) *
          F.map (MvPolynomial.eval₂Hom (Int.castRingHom K)
            (fun j => MvPolynomial.eval₂ (Int.castRingHom K) x (N j) /
              MvPolynomial.eval₂ (Int.castRingHom K) x d)) := by
  induction F using Polynomial.induction_on' with
  | add F G hF hG =>
    obtain ⟨e, B, hB⟩ := hF
    obtain ⟨f, C, hC⟩ := hG
    refine ⟨e + f, B * Polynomial.C (d ^ f) + C * Polynomial.C (d ^ e), ?_⟩
    intro K _ x hx
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_pow, hB K x hx, hC K x hx,
      pow_add, Polynomial.C_mul]
    ring
  | monomial n a =>
    obtain ⟨e, B, hB⟩ := branch_exists_cleared_mvpolynomial a d N
    refine ⟨e, Polynomial.monomial n B, ?_⟩
    intro K _ x hx
    simp only [Polynomial.map_monomial, MvPolynomial.coe_eval₂Hom, hB K x hx,
      Polynomial.C_mul_monomial]

/-- Universal normalized coefficients: dividend, scale, and three independent
location coefficients. The slope is a fixed integer from a finite set. -/
def branchUniversalResultantFamily (c : ℕ) : Polynomial (MvPolynomial (Fin 5) ℤ) :=
  branchResultantLabel (MvPolynomial.X 0) (MvPolynomial.X 1) c
    (MvPolynomial.X 2) (MvPolynomial.X 3) (MvPolynomial.X 4)

/-- Numerators for the first-minor vertex order `(A,D,C,B)`, with the dividend
kept as the initial variable. The common denominator is `A`. -/
def branchVertexSubstitution : Fin 5 → MvPolynomial (Fin 5) ℤ :=
  ![MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 1 ^ 2,
    -MvPolynomial.X 4 - MvPolynomial.X 3, MvPolynomial.X 3 + MvPolynomial.X 2,
    -MvPolynomial.X 2 - MvPolynomial.X 1]

/-- One integer family and one power of the scale clear all vertex denominators. -/
def branchVertexClearing (c : ℕ) : ℕ × Polynomial (MvPolynomial (Fin 5) ℤ) :=
  let h := branch_exists_cleared_polynomial (branchUniversalResultantFamily c)
    (MvPolynomial.X 1) branchVertexSubstitution
  ⟨h.choose, h.choose_spec.choose⟩

def branchVertexClearingExponent (c : ℕ) : ℕ := (branchVertexClearing c).1

def branchVertexFamily (c : ℕ) : Polynomial (MvPolynomial (Fin 5) ℤ) :=
  (branchVertexClearing c).2

/-- Fixing the dividend leaves the four integer minor variables. -/
def branchVertexFamilyAt (a : ℤ) (c : ℕ) : Polynomial (MvPolynomial (Fin 4) ℤ) :=
  branchFamilyHead a (branchVertexFamily c)

/-- The chosen denominator clearing satisfies its universal identity. Keep
the choice data behind this accessor when specializing the resultant. -/
theorem branchVertexClearing_spec (c : ℕ) (K : Type) [Field K]
    (x : Fin 5 → K) (hx : x 1 ≠ 0) :
    (branchVertexFamily c).map (MvPolynomial.eval₂Hom (Int.castRingHom K) x) =
      Polynomial.C (x 1 ^ branchVertexClearingExponent c) *
        (branchUniversalResultantFamily c).map
          (MvPolynomial.eval₂Hom (Int.castRingHom K)
            (fun j => MvPolynomial.eval₂ (Int.castRingHom K) x
              (branchVertexSubstitution j) / x 1)) := by
  have h := (branch_exists_cleared_polynomial (branchUniversalResultantFamily c)
    (MvPolynomial.X 1) branchVertexSubstitution).choose_spec.choose_spec K x
    (by simpa only [MvPolynomial.eval₂_X] using hx)
  simpa only [branchVertexFamily, branchVertexClearingExponent, branchVertexClearing,
    MvPolynomial.eval₂_X] using h

lemma branchVertexSubstitution_eval (K : Type) [Field K]
    (a A D C B : K) (hA : A ≠ 0) :
    (fun j => MvPolynomial.eval₂ (Int.castRingHom K) ![a, A, D, C, B]
      (branchVertexSubstitution j) / A) =
        ![a, A, (-B - C) / A, (C + D) / A, (-D - A) / A] := by
  funext j
  fin_cases j <;> simp [branchVertexSubstitution, pow_two, hA]

lemma branchUniversalResultantFamily_eval (c : ℕ) (K : Type) [Field K]
    (x : Fin 5 → K) :
    (branchUniversalResultantFamily c).map
      (MvPolynomial.eval₂Hom (Int.castRingHom K) x) =
      branchResultantLabel (x 0) (x 1) c (x 2) (x 3) (x 4) := by
  rw [branchUniversalResultantFamily, branchResultantLabel_map]
  simp only [MvPolynomial.eval₂Hom_X', map_natCast]

/-- The integral family agrees with the rational branch equation away from
zero scale, up to a nonzero scalar power. This identity is valid over every
field, including the generic function field and actual branch residues. -/
theorem branchVertexFamily_eval (c : ℕ) (K : Type) [Field K]
    (a A D C B : K) (hA : A ≠ 0) :
    (branchVertexFamily c).map (MvPolynomial.eval₂Hom (Int.castRingHom K) ![a, A, D, C, B]) =
      Polynomial.C (A ^ branchVertexClearingExponent c) *
        branchResultantLabel a A c ((-B - C) / A) ((C + D) / A) ((-D - A) / A) := by
  rw [branchVertexClearing_spec c K ![a, A, D, C, B] hA]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [branchVertexSubstitution_eval K a A D C B hA]
  rw [branchUniversalResultantFamily_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]


/-- Evaluate the cleared family at an arbitrary five-coordinate tuple. -/
lemma branchVertexFamily_eval_vector (c : ℕ) (K : Type) [Field K]
    (x : Fin 5 → K) (hx : x 1 ≠ 0) :
    (branchVertexFamily c).map (MvPolynomial.eval₂Hom (Int.castRingHom K) x) =
      Polynomial.C (x 1 ^ branchVertexClearingExponent c) *
        branchResultantLabel (x 0) (x 1) c
          ((-x 4 - x 3) / x 1) ((x 3 + x 2) / x 1) ((-x 2 - x 1) / x 1) := by
  have he : ![x 0, x 1, x 2, x 3, x 4] = x := by
    funext j
    fin_cases j <;> rfl
  exact (congrArg (fun y => (branchVertexFamily c).map
    (MvPolynomial.eval₂Hom (Int.castRingHom K) y)) he).symm.trans
      (branchVertexFamily_eval c K (x 0) (x 1) (x 2) (x 3) (x 4) hx)

lemma branchVertexFamily_natDegree_le_of_injective_eval (c : ℕ) (K : Type) [Field K]
    (x : Fin 5 → K) (hx : x 1 ≠ 0)
    (hinj : Function.Injective (MvPolynomial.eval₂Hom (Int.castRingHom K) x)) :
    (branchVertexFamily c).natDegree ≤ 12 := by
  calc
    (branchVertexFamily c).natDegree =
        ((branchVertexFamily c).map (MvPolynomial.eval₂Hom (Int.castRingHom K) x)).natDegree :=
      (Polynomial.natDegree_map_eq_of_injective hinj (branchVertexFamily c)).symm
    _ = (Polynomial.C (x 1 ^ branchVertexClearingExponent c) *
        branchResultantLabel (x 0) (x 1) c
          ((-x 4 - x 3) / x 1) ((x 3 + x 2) / x 1) ((-x 2 - x 1) / x 1)).natDegree :=
      congrArg Polynomial.natDegree (branchVertexFamily_eval_vector c K x hx)
    _ ≤ 12 := (Polynomial.natDegree_C_mul_le _ _).trans
      (branchResultantLabel_natDegree_le _ _ _ _ _ _)

/-- Clearing vertex denominators does not increase the label degree. -/
theorem branchVertexFamily_natDegree_le (c : ℕ) : (branchVertexFamily c).natDegree ≤ 12 := by
  let R := MvPolynomial (Fin 5) ℤ
  let K := FractionRing R
  let φ := algebraMap R K
  let x := fun j : Fin 5 => φ (MvPolynomial.X j)
  have hA : x 1 ≠ 0 := by
    simpa only [x, map_zero] using
      (IsFractionRing.injective R K).ne (MvPolynomial.X_ne_zero (R := ℤ) 1)
  have he : MvPolynomial.eval₂Hom (Int.castRingHom K) x = φ := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp only [MvPolynomial.eval₂Hom_C]
      exact (map_intCast φ z).symm
    · intro j
      rw [MvPolynomial.eval₂Hom_X']
  have hinj : Function.Injective (MvPolynomial.eval₂Hom (Int.castRingHom K) x) := by
    rw [he]
    exact IsFractionRing.injective R K
  exact branchVertexFamily_natDegree_le_of_injective_eval c K x hA hinj

/-- Fixing the dividend also preserves the degree-twelve label bound. -/
lemma branchVertexFamilyAt_natDegree_le (a : ℤ) (c : ℕ) :
    (branchVertexFamilyAt a c).natDegree ≤ 12 :=
  Polynomial.natDegree_map_le.trans (branchVertexFamily_natDegree_le c)

/-- The four-vertex family specializes over arbitrary fields, with the dividend
already fixed as an integer. -/
theorem branchVertexFamilyAt_eval_field (a : ℤ) (c : ℕ) (K : Type) [Field K]
    (x : Fin 4 → K) (hx : x 0 ≠ 0) :
    (branchVertexFamilyAt a c).map (MvPolynomial.eval₂Hom (Int.castRingHom K) x) =
      Polynomial.C (x 0 ^ branchVertexClearingExponent c) *
        branchResultantLabel (a : K) (x 0) c
          ((-x 3 - x 2) / x 0) ((x 2 + x 1) / x 0) ((-x 1 - x 0) / x 0) := by
  have he : (MvPolynomial.eval₂Hom (Int.castRingHom K) x).comp (branchHeadSpecialization a) =
      MvPolynomial.eval₂Hom (Int.castRingHom K) (Fin.cons (a : K) x) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [branchHeadSpecialization]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [RingHom.comp_apply, branchHeadSpecialization, MvPolynomial.eval₂Hom_X',
          Fin.cases_zero, Fin.cons_zero]
        exact MvPolynomial.eval₂Hom_C _ _ a
      · simp [branchHeadSpecialization]
  rw [branchVertexFamilyAt, branchFamilyHead, Polynomial.map_map, he]
  have hx' : Fin.cons (a : K) x = ![(a : K), x 0, x 1, x 2, x 3] := by
    funext j
    fin_cases j <;> rfl
  rw [hx']
  exact branchVertexFamily_eval c K (a : K) (x 0) (x 1) (x 2) (x 3) hx

/-- Expose the evaluation map before substituting a concrete polynomial family. -/
lemma branchFamilyEval_eq_map {r : ℕ} (x : Fin r → ℤ)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) :
    branchFamilyEval x p = p.map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun j => (x j : ℚ))) := rfl

def branchFieldScale (K : Type) [Field K] (e : ℕ) (A : K)
    (q : Polynomial K) : Polynomial K := Polynomial.C (A ^ e) * q

lemma branchFieldScale_eq (K : Type) [Field K] (e : ℕ) (A : K)
    (q : Polynomial K) : branchFieldScale K e A q = Polynomial.C (A ^ e) * q := rfl

lemma branchVertexFamilyAt_eval_scaled (a : ℤ) (c : ℕ) (K : Type) [Field K]
    (x : Fin 4 → K) (hx : x 0 ≠ 0) :
    (branchVertexFamilyAt a c).map (MvPolynomial.eval₂Hom (Int.castRingHom K) x) =
      branchFieldScale K (branchVertexClearingExponent c) (x 0)
        (branchResultantLabel (a : K) (x 0) c
          ((-x 3 - x 2) / x 0) ((x 2 + x 1) / x 0) ((-x 1 - x 0) / x 0)) := by
  exact (branchVertexFamilyAt_eval_field a c K x hx).trans
    (branchFieldScale_eq K (branchVertexClearingExponent c) (x 0) _).symm

lemma branchFieldScale_rat (e : ℕ) (A : ℚ) (q : Polynomial ℚ) :
    branchFieldScale ℚ e A q = Polynomial.C (A ^ e) * q := rfl

lemma branchFieldScale_rat_coordinate (e : ℕ) (x : Fin 4 → ℤ) (q : Polynomial ℚ) :
    branchFieldScale ℚ e ((fun j => (x j : ℚ)) 0) q =
      Polynomial.C ((x 0 : ℚ) ^ e) * q := rfl

lemma branchResultantLabel_rat_cast (a : ℤ) (c : ℕ) (x : Fin 4 → ℤ) :
    @branchResultantLabel ℚ Rat.instField.toCommRing
      (Int.castRingHom ℚ a) ((fun j => (x j : ℚ)) 0) c
      ((-((fun j => (x j : ℚ)) 3) - ((fun j => (x j : ℚ)) 2)) /
        ((fun j => (x j : ℚ)) 0))
      ((((fun j => (x j : ℚ)) 2) + ((fun j => (x j : ℚ)) 1)) /
        ((fun j => (x j : ℚ)) 0))
      ((-((fun j => (x j : ℚ)) 1) - ((fun j => (x j : ℚ)) 0)) /
        ((fun j => (x j : ℚ)) 0)) =
    branchResultantLabel (a : ℚ) (x 0 : ℚ) c
      ((-(x 3 : ℚ) - x 2) / x 0) (((x 2 : ℚ) + x 1) / x 0)
      ((-(x 1 : ℚ) - x 0) / x 0) := rfl

lemma branchFieldScale_rat_cast (e : ℕ) (a : ℤ) (c : ℕ) (x : Fin 4 → ℤ) :
    branchFieldScale ℚ e ((fun j => (x j : ℚ)) 0)
      (@branchResultantLabel ℚ Rat.instField.toCommRing
        (Int.castRingHom ℚ a) ((fun j => (x j : ℚ)) 0) c
        ((-((fun j => (x j : ℚ)) 3) - ((fun j => (x j : ℚ)) 2)) /
          ((fun j => (x j : ℚ)) 0))
        ((((fun j => (x j : ℚ)) 2) + ((fun j => (x j : ℚ)) 1)) /
          ((fun j => (x j : ℚ)) 0))
        ((-((fun j => (x j : ℚ)) 1) - ((fun j => (x j : ℚ)) 0)) /
          ((fun j => (x j : ℚ)) 0))) =
      Polynomial.C ((x 0 : ℚ) ^ e) *
        branchResultantLabel (a : ℚ) (x 0 : ℚ) c
          ((-(x 3 : ℚ) - x 2) / x 0) (((x 2 : ℚ) + x 1) / x 0)
          ((-(x 1 : ℚ) - x 0) / x 0) := by
  exact (branchFieldScale_rat_coordinate e x _).trans
    (congrArg (fun q : Polynomial ℚ => Polynomial.C ((x 0 : ℚ) ^ e) * q)
      (branchResultantLabel_rat_cast a c x))

/-- Specialization at an integer dividend retains the same exact branch equation. -/
theorem branchVertexFamilyAt_eval (a : ℤ) (c : ℕ) (x : Fin 4 → ℤ) (hx : x 0 ≠ 0) :
    branchFamilyEval x (branchVertexFamilyAt a c) =
      Polynomial.C ((x 0 : ℚ) ^ branchVertexClearingExponent c) *
        branchResultantLabel (a : ℚ) (x 0 : ℚ) c
          ((-(x 3 : ℚ) - x 2) / x 0) (((x 2 : ℚ) + x 1) / x 0)
          ((-(x 1 : ℚ) - x 0) / x 0) := by
  exact (branchFamilyEval_eq_map x (branchVertexFamilyAt a c)).trans
    ((branchVertexFamilyAt_eval_scaled a c ℚ (fun j => (x j : ℚ))
      (by exact_mod_cast hx)).trans
        (branchFieldScale_rat_cast (branchVertexClearingExponent c) a c x))

/-- Every fixed integral polynomial family has finite degree and coefficient
height bounds, including all coefficients outside its finite support. -/
theorem branch_fixed_family_degree_height {r : ℕ}
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) :
    ∃ d H : ℕ, 0 < H ∧ p.natDegree ≤ d ∧
      (∀ j, (p.coeff j).totalDegree ≤ d) ∧
      ∀ j s, |(p.coeff j).coeff s| ≤ (H : ℤ) := by
  classical
  let d := p.natDegree + p.support.sup (fun j => (p.coeff j).totalDegree)
  let h := fun j => (p.coeff j).support.sup (fun s => ((p.coeff j).coeff s).natAbs)
  let H := p.support.sup h + 1
  refine ⟨d, H, by dsimp [H]; omega, by dsimp [d]; omega, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ p.support
    · have hh : (p.coeff j).totalDegree ≤
          p.support.sup (fun k => (p.coeff k).totalDegree) :=
        Finset.le_sup (f := fun k => (p.coeff k).totalDegree) hj
      exact hh.trans (Nat.le_add_left _ _)
    · have hz : p.coeff j = 0 := by simpa using hj
      simp [hz]
  · intro j s
    by_cases hj : j ∈ p.support
    · by_cases hs : s ∈ (p.coeff j).support
      · have h₁ : ((p.coeff j).coeff s).natAbs ≤ h j := by
          exact Finset.le_sup (f := fun s => ((p.coeff j).coeff s).natAbs) hs
        have h₂ : h j ≤ p.support.sup h := Finset.le_sup hj
        have hh : ((p.coeff j).coeff s).natAbs ≤ H := (h₁.trans h₂).trans (Nat.le_succ _)
        simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hh)
      · have hz : (p.coeff j).coeff s = 0 := by simpa using hs
        simp [hz]
    · have hz : p.coeff j = 0 := by simpa using hj
      simp [hz]

/-- Any fixed finite choice of integral families has common degree and height bounds. -/
theorem branch_bounded_slope_family_bounds {r : ℕ}
    (P : ℕ → Polynomial (MvPolynomial (Fin r) ℤ)) :
    ∃ d H : ℕ, 0 < H ∧ ∀ c : ℕ, c ≤ 144 →
      (P c).natDegree ≤ d ∧
      (∀ j, ((P c).coeff j).totalDegree ≤ d) ∧
      ∀ j s, |((P c).coeff j).coeff s| ≤ (H : ℤ) := by
  classical
  have hex (c : Fin 145) := branch_fixed_family_degree_height (P c)
  choose d h hh hd hp hH using hex
  let D := Finset.univ.sup d
  let H := Finset.univ.sup h + 1
  refine ⟨D, H, by dsimp [H]; omega, ?_⟩
  intro c hc
  let i : Fin 145 := ⟨c, by omega⟩
  have hi : d i ≤ D := Finset.le_sup (Finset.mem_univ i)
  have hhi : h i ≤ H := (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)
  refine ⟨(hd i).trans hi, fun j => (hp i j).trans hi, ?_⟩
  intro j s
  exact (hH i j s).trans (by exact_mod_cast hhi)

/-- The 145 permitted slopes have one common degree and height bound. -/
theorem branchVertexFamily_uniform_bounds :
    ∃ d H : ℕ, 0 < H ∧ ∀ c : ℕ, c ≤ 144 →
      (branchVertexFamily c).natDegree ≤ d ∧
      (∀ j, ((branchVertexFamily c).coeff j).totalDegree ≤ d) ∧
      ∀ j s, |((branchVertexFamily c).coeff j).coeff s| ≤ (H : ℤ) :=
  branch_bounded_slope_family_bounds branchVertexFamily

/-- Dividend specialization has polynomial coefficient height, with constants
uniform over all bounded slopes and independent of the dividend. -/
theorem branchVertexFamilyAt_uniform_bounds :
    ∃ d C : ℕ, 0 < C ∧ ∀ (a : ℤ) (c : ℕ), c ≤ 144 →
      (branchVertexFamilyAt a c).natDegree ≤ d ∧
      (∀ j, ((branchVertexFamilyAt a c).coeff j).totalDegree ≤ d) ∧
      ∀ j s, |((branchVertexFamilyAt a c).coeff j).coeff s| ≤
        (C * (a.natAbs + 1) ^ d : ℕ) := by
  obtain ⟨d, H, hH, hb⟩ := branchVertexFamily_uniform_bounds
  refine ⟨d, (d + 1) * H, by positivity, ?_⟩
  intro a c hc
  obtain ⟨hd, hp, hh⟩ := hb c hc
  exact branchFamilyHead_degree_height (branchVertexFamily c) hd hp hh (by omega)
    (show |a| ≤ ((a.natAbs + 1 : ℕ) : ℤ) by simp)

end
end PierceLengthBound.FixedDividend
