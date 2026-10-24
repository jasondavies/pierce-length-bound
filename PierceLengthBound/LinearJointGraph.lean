/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointGraph
public import PierceLengthBound.PoweredPoleOrder
public import PierceLengthBound.JointLiftOptimization
public import PierceLengthBound.GraphPoleDegree
public import PierceLengthBound.JointLiftCurvatureDegree
public import PierceLengthBound.JointLiftPointBox

/-!
# Linearly changed joint graphs

Replace the three curvature coordinates `W` by `G W` for a constant invertible matrix `G`. An
invertible constant matrix leaves the pole envelope unchanged at every branch, so the powered
graph `(nodes, (G W)ᵐ, Jⁿ)` satisfies `2δ ≥ (5n + 3m) d + 2m` and `10n + 7m ≤ δ ≤
((m + n) 247 + 1) d` (paper, Lemma 8.13 `lem:jointpowereddegree` and Lemma 9.9
`lem:latticedegree`). The powered graph of `PoweredJointGraph` is the case `G = 1`
(`orbitLinearJointGraphIdeal_one`), and `PoweredJointGraphLowerDegree` derives its bounds from
the ones here.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
attribute [local instance] FractionRing.liftAlgebra

/-- Constant coefficients cannot enlarge the pole envelope. -/
theorem branchPoleEnvelope_linear_le {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype ι] (ν : AddValuation L (WithTop ℤ)) (hK : ∀ c : K, 0 ≤ ν (algebraMap K L c))
    (G : Matrix ι ι K) (V : ι → L) :
    branchPoleEnvelope ν (fun j => ∑ l, algebraMap K L (G j l) * V l) ≤
      branchPoleEnvelope ν V :=
  Finset.sup_le fun j _ => combination_pole_order_le_envelope ν hK V (G j)

/-- **An invertible constant matrix preserves the pole envelope.** -/
theorem branchPoleEnvelope_linear_eq {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] (ν : AddValuation L (WithTop ℤ))
    (hK : ∀ c : K, 0 ≤ ν (algebraMap K L c)) (G : Matrix ι ι K) (V : ι → L)
    (hG : IsUnit G.det) :
    branchPoleEnvelope ν (fun j => ∑ l, algebraMap K L (G j l) * V l) =
      branchPoleEnvelope ν V := by
  apply le_antisymm (branchPoleEnvelope_linear_le ν hK G V)
  have hinv : V = fun l => ∑ j, algebraMap K L (G⁻¹ l j) *
      ∑ k, algebraMap K L (G j k) * V k := by
    funext l
    simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, Matrix.nonsing_inv_mul G hG,
      Matrix.one_apply]
    simp
  calc branchPoleEnvelope ν V = branchPoleEnvelope ν (fun l => ∑ j, algebraMap K L (G⁻¹ l j) *
        ∑ k, algebraMap K L (G j k) * V k) := congrArg _ hinv
    _ ≤ _ := branchPoleEnvelope_linear_le ν hK G⁻¹ _

/-- The three curvature numerators replaced by constant combinations; the rank-five
numerator is unchanged. -/
def linearJointNumerators {σ : Type*} (G : Matrix (Fin 3) (Fin 3) ℚ)
    (P : Fin 4 → MvPolynomial σ ℚ) : Fin 4 → MvPolynomial σ ℚ :=
  ![∑ l : Fin 3, C (G 0 l) * P l.castSucc, ∑ l : Fin 3, C (G 1 l) * P l.castSucc,
    ∑ l : Fin 3, C (G 2 l) * P l.castSucc, P 3]

@[simp] lemma linearJointNumerators_one {σ : Type*} (P : Fin 4 → MvPolynomial σ ℚ) :
    linearJointNumerators 1 P = P := by
  funext j
  fin_cases j <;> simp [linearJointNumerators, Matrix.one_apply]

lemma linearJointNumerators_castSucc {σ : Type*} (G : Matrix (Fin 3) (Fin 3) ℚ)
    (P : Fin 4 → MvPolynomial σ ℚ) (j : Fin 3) :
    linearJointNumerators G P j.castSucc = ∑ l : Fin 3, C (G j l) * P l.castSucc := by
  fin_cases j <;> rfl

lemma linearJointNumerators_totalDegree {σ : Type*} (G : Matrix (Fin 3) (Fin 3) ℚ)
    (P : Fin 4 → MvPolynomial σ ℚ) {D : ℕ} (hP : ∀ j, (P j).totalDegree ≤ D) (j : Fin 4) :
    (linearJointNumerators G P j).totalDegree ≤ D := by
  have hsum (r : Fin 3) : (∑ l : Fin 3, C (G r l) * P l.castSucc).totalDegree ≤ D :=
    (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ =>
      (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hP _))
  fin_cases j
  · exact hsum 0
  · exact hsum 1
  · exact hsum 2
  · exact hP 3

/-- In the function field, the curvature coordinates of `linearJointNumerators G P` are the
constant combinations, with coefficients `G`, of those of `P`. -/
lemma linear_jointGraphFieldCoordinates {σ F : Type*} [Field F] [Algebra ℚ F]
    (I : Ideal (MvPolynomial σ ℚ)) (G : Matrix (Fin 3) (Fin 3) ℚ)
    (P : Fin 4 → MvPolynomial σ ℚ) (D : MvPolynomial σ ℚ)
    (ι : (MvPolynomial σ ℚ ⧸ I) →ₐ[ℚ] F) (j : Fin 3) :
    jointGraphFieldCoordinates I (linearJointNumerators G P) D ι (Sum.inr j.castSucc) =
      ∑ l, algebraMap ℚ F (G j l) *
        jointGraphFieldCoordinates I P D ι (Sum.inr l.castSucc) := by
  simp only [jointGraphFieldCoordinates, Sum.elim_inr, linearJointNumerators_castSucc,
    map_sum, map_mul, Finset.sum_div, mul_div_assoc]
  congr 1
  funext l
  congr 1
  rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  exact ι.commutes _

/-- The powered numerators of the orbit graph `(nodes, (G W)ᵐ, Jⁿ)`. -/
def orbitLinearJointNumerators (G : Matrix (Fin 3) (Fin 3) ℚ) (a b i m n : ℕ) :
    Fin 4 → MvPolynomial (Fin 3) ℚ :=
  poweredGraphNumerators (linearJointNumerators G (orbitJointNumerators a b i))
    (orbitJointDenominator a b i) (jointCoordinatePowers m n) (m + n)

/-- The ideal of the orbit graph `(nodes, (G W)ᵐ, Jⁿ)` over the component `I`. -/
def orbitLinearJointGraphIdeal (G : Matrix (Fin 3) (Fin 3) ℚ) (a b i m n : ℕ)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) : Ideal (MvPolynomial (Fin 3 ⊕ Fin 4) ℚ) :=
  jointGraphIdeal I (orbitLinearJointNumerators G a b i m n)
    (orbitJointDenominator a b i ^ (m + n))

lemma orbitLinearJointGraphIdeal_one (a b i m n : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    orbitLinearJointGraphIdeal 1 a b i m n I = orbitPoweredJointGraphIdeal a b i m n I := by
  simp only [orbitLinearJointGraphIdeal, orbitLinearJointNumerators, linearJointNumerators_one,
    orbitPoweredJointGraphIdeal, orbitPoweredJointNumerators]

/-- The graph depends on the start only through its pattern. -/
lemma orbitLinearJointGraph_congr {a b i l : ℕ} (h : theta a b i = theta a b l)
    (G : Matrix (Fin 3) (Fin 3) ℚ) (m n : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    orbitLinearJointGraphIdeal G a b i m n I = orbitLinearJointGraphIdeal G a b l m n I := by
  obtain ⟨hP, hD⟩ := orbitJoint_polynomials_congr h
  simp only [orbitLinearJointGraphIdeal, orbitLinearJointNumerators, hP, hD]

/-- With `m = n = 1` the powered graph is the joint graph `orbitJointGraphIdeal`:
`P D / D² = P / D`. -/
lemma orbitPoweredJointGraphIdeal_one_one {a b i : ℕ} (I : Ideal (MvPolynomial (Fin 3) ℚ))
    [I.IsPrime] (hD : orbitJointDenominator a b i ∉ I) :
    orbitPoweredJointGraphIdeal a b i 1 1 I = orbitJointGraphIdeal a b i I := by
  refine jointGraphIdeal_congr I (fun h => hD (Ideal.IsPrime.mem_of_pow_mem ‹_› 2 h)) hD
    fun j => ?_
  have h1 : jointCoordinatePowers 1 1 j = 1 := by fin_cases j <;> rfl
  simp only [orbitPoweredJointNumerators, poweredGraphNumerators, h1, pow_one]
  rw [show orbitJointNumerators a b i j * orbitJointDenominator a b i ^ (1 + 1 - 1) *
      orbitJointDenominator a b i - orbitJointNumerators a b i j *
      orbitJointDenominator a b i ^ (1 + 1) = 0 by ring]
  exact I.zero_mem

/-- The linearly changed powered graph has the same uniform upper degree bound. -/
theorem orbitLinearJointGraph_degree_bounds {a b i d : ℕ} (G : Matrix (Fin 3) (Fin 3) ℚ)
    (hba : b < a) (hi : i + 7 < P a b) (m n : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ))
    [I.IsPrime] (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hd : ∃ M : ℕ, ∃ c : ℤ, ∀ k ≥ M,
      (Module.finrank ℚ (filteredCoordinateSpace I k) : ℤ) = (d : ℤ) * k + c) :
    (orbitLinearJointGraphIdeal G a b i m n I).IsPrime ∧
    ∃ δ : ℕ, d ≤ δ ∧ δ ≤ ((m + n) * 247 + 1) * d ∧ ∃ M : ℕ, ∃ c : ℤ, ∀ k ≥ M,
      (Module.finrank ℚ (filteredCoordinateSpace (orbitLinearJointGraphIdeal G a b i m n I) k)
        : ℤ) = (δ : ℤ) * k + c :=
  powered_jointGraph_degree_bounds I _ _ (orbitJoint_denominator_not_mem hba hi I hz)
    (jointCoordinatePowers m n) (m + n) 247 (jointCoordinatePowers_le m n)
    (linearJointNumerators_totalDegree G _ (orbitJoint_totalDegree_le a b i).1)
    ((orbitJoint_totalDegree_le a b i).2.trans (by norm_num)) hd

/-- The degree arithmetic behind `retained_linearJointGraph_degree_lower_bound_from_envelope`:
the infinity branches, of total weighted multiplicity `d = 2 Σ t`, contribute `5k/2 · d`. -/
private lemma pole_sum_degree_arith {α β : Type*} (B : Finset α) (E : Finset β)
    (μ t r : α → ℕ) (n s : β → ℕ) {d δ k m : ℕ}
    (hμ : ∀ p ∈ B, μ p = 2 * t p) (hsum : ∑ p ∈ B, μ p * r p = d)
    (hbound : ∑ p ∈ B, 5 * k * t p * r p + ∑ q ∈ E, m * n q * s q ≤ δ) :
    5 * k * d + 2 * m * ∑ q ∈ E, n q * s q ≤ 2 * δ := by
  have htwice : 2 * ∑ p ∈ B, t p * r p = d := by
    rw [← hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => by rw [hμ p hp, mul_assoc]
  have h1 : ∑ p ∈ B, 5 * k * t p * r p = 5 * k * ∑ p ∈ B, t p * r p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have h2 : ∑ q ∈ E, m * n q * s q = m * ∑ q ∈ E, n q * s q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [h1, h2] at hbound
  rw [← htwice]
  linarith

/-- At a normalized branch above old infinity, where the infinity coordinate vanishes to order
`2t`, the first node has a pole and the rank-five coordinate has pole order exactly `5t`. -/
theorem retained_infinity_branch_rank_five_pole
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    (hfrac : ∀ z : F, ∃ x y : MvPolynomial (Fin 3) ℚ ⧸ I, z = ι x / ι y)
    [IsFractionRing (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F]
    [IsDedekindDomain (integralClosure
      (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F)]
    (p : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F))
    (hp : algebraMap (projectiveChart I ι (Ideal.Quotient.mk I (X 0)))
      (integralClosure (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F)
      (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))) ∈ p.asIdeal) :
    let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
    let C := integralClosure S F
    let w := algebraMap S C (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0)))
    let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
    ∃ t : ℕ, 0 < t ∧ multiplicity p.asIdeal (Ideal.span {w}) = 2 * t ∧
      normalizedBranchOrder p F (ι (Ideal.Quotient.mk I (X 0))) < 0 ∧
      discretePoleOrder (normalizedBranchOrder p F)
        (jointGraphFieldCoordinates I (orbitJointNumerators a b i)
          (orbitJointDenominator a b i) ι (Sum.inr 3)) = 5 * t := by
  let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
  let C := integralClosure S F
  let w := algebraMap S C (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0)))
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  obtain ⟨ν, hcenter, hregular, hπ, t, ht, hwν, _, _, _, hJ⟩ :=
    retained_normalized_branch_joint_orders hba hi hne I hf hg hz hnorm hres
      ι hι hfrac hd hdegree p hp
  have hν : normalizedBranchOrder p F = ν := centered_branch_order_eq p ν
    (branch_order_nonnegative_on_normalization ν hregular) (fun r => (hcenter r).symm) hπ
  have hw' : ν (algebraMap C F w) = ((2 * t : ℤ) : WithTop ℤ) := hwν
  have hw0 : w ≠ 0 := by
    intro he
    rw [he, map_zero, ν.map_zero] at hw'
    exact WithTop.coe_ne_top hw'.symm
  have hmult := normalizedBranchOrder_eq_multiplicity p F hw0
  rw [hν, hw'] at hmult
  have hm : multiplicity p.asIdeal (Ideal.span {w}) = 2 * t.toNat := by
    have he : 2 * t = (multiplicity p.asIdeal (Ideal.span {w}) : ℤ) := by
      exact_mod_cast hmult
    omega
  refine ⟨t.toNat, by omega, hm, ?_, ?_⟩
  · rw [hν]
    have hl := congrArg (fun z : WithTop ℤ => -z) hwν
    rw [ν.map_inv, neg_neg] at hl
    rw [hl, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact_mod_cast (show -(2 * t) < 0 by omega)
  · rw [hν]
    have hJ' : ν (jointGraphFieldCoordinates I (orbitJointNumerators a b i)
        (orbitJointDenominator a b i) ι (Sum.inr 3)) = ((-5 * t : ℤ) : WithTop ℤ) := hJ
    rw [discretePoleOrder_eq ν hJ']
    omega

/-- On a branch of the affine normalization where the curvature coordinates have a pole, the
linearly changed powered graph has a coordinate whose pole order is at least `m` times their
pole envelope. -/
theorem linearJointGraph_envelope_pole_le {σ R F : Type*} [CommRing R] [Algebra ℚ R]
    [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
    [IsDedekindDomain (integralClosure R F)] [IsFractionRing (integralClosure R F) F]
    (I : Ideal (MvPolynomial σ ℚ)) (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : IsUnit G.det)
    (P : Fin 4 → MvPolynomial σ ℚ) (D : MvPolynomial σ ℚ)
    (ι : (MvPolynomial σ ℚ ⧸ I) →ₐ[ℚ] F) (hD : ι (Ideal.Quotient.mk I D) ≠ 0) (m k : ℕ)
    (q : IsDedekindDomain.HeightOneSpectrum (integralClosure R F))
    (hpos : 0 < branchPoleEnvelope (normalizedBranchOrder q F)
      (fun j : Fin 3 => jointGraphFieldCoordinates I P D ι (Sum.inr j.castSucc))) :
    ∃ j, m * branchPoleEnvelope (normalizedBranchOrder q F)
        (fun j : Fin 3 => jointGraphFieldCoordinates I P D ι (Sum.inr j.castSucc)) ≤
      discretePoleOrder (normalizedBranchOrder q F)
        (jointGraphFieldCoordinates I (poweredGraphNumerators (linearJointNumerators G P) D
          (jointCoordinatePowers m k) (m + k)) (D ^ (m + k)) ι j) := by
  let ν := normalizedBranchOrder q F
  let V := fun j : Fin 3 => jointGraphFieldCoordinates I P D ι (Sum.inr j.castSucc)
  let W' := jointGraphFieldCoordinates I (linearJointNumerators G P) D ι
  let V' := fun j : Fin 3 => W' (Sum.inr j.castSucc)
  have hV' : V' = fun j => ∑ l, algebraMap ℚ F (G j l) * V l := by
    funext j
    exact linear_jointGraphFieldCoordinates I G _ _ ι j
  have henv : branchPoleEnvelope ν V' = branchPoleEnvelope ν V := by
    rw [hV']
    refine branchPoleEnvelope_linear_eq _ (fun c => ?_) G V hG
    rw [IsScalarTower.algebraMap_apply ℚ R F,
      IsScalarTower.algebraMap_apply R (integralClosure R F) F]
    exact normalizedBranchOrder_nonnegative q F _
  have hpos' : 0 < branchPoleEnvelope ν V' := henv ▸ hpos
  obtain ⟨j, hj⟩ := branchPoleEnvelope_attained ν V' hpos'
  have he := (discretePoleOrder_eq_iff_of_pos ν (V' j) hpos').mpr hj
  refine ⟨Sum.inr j.castSucc, ?_⟩
  rw [powered_jointGraphFieldCoordinates I _ _ _ _ (jointCoordinatePowers_le m k) ι hD]
  change m * branchPoleEnvelope ν V ≤
    discretePoleOrder ν (V' j ^ jointCoordinatePowers m k j.castSucc)
  rw [jointCoordinatePowers_castSucc, discretePoleOrder_pow, he, henv]

/-- The pole bound for the degree `δ` of the linearly changed powered graph:
`5 k d + 2 m e ≤ 2 δ`, where `e` is the degree of the pole envelope of the affine curvature
coordinates. The branches above old infinity contribute the rank-five poles `k · 5t`, and the
affine branches the curvature poles `m` times the envelope. -/
theorem retained_linearJointGraph_degree_lower_bound_from_envelope
    {a b i d δ N m k : ℕ} {c₀ : ℤ}
    (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : IsUnit G.det) (hm : 0 < m) (hk : 0 < k)
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (hgraph : ∃ M : ℕ, ∃ c : ℤ, ∀ n ≥ M,
      (Module.finrank ℚ
        (filteredCoordinateSpace (orbitLinearJointGraphIdeal G a b i m k I) n) : ℤ) =
          (δ : ℤ) * n + c)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let A := integralClosure R F
    let : IsDedekindDomain A := (orbit_affine_normalization hba hi hne I hf hg hd hdegree F).1
    let : IsFractionRing A F := IsIntegralClosure.isFractionRing_of_finite_extension R F F A
    let ψ := (IsScalarTower.toAlgHom ℚ R F).comp (Ideal.Quotient.mkₐ ℚ I)
    5 * k * d + 2 * m * poleEnvelopeDegree A (fun j : Fin 3 =>
      ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)) ≤ 2 * δ := by
  classical
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
  let C := integralClosure S F
  let A := integralClosure R F
  let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))
  let hn := orbit_chart_normalization_in_field hba hi hne I hf hg
    (by omega : 0 < d) hdegree F
  let : IsFractionRing S F := hn.1
  let : IsDedekindDomain C := hn.2.1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  let : IsDedekindDomain A :=
    (orbit_affine_normalization hba hi hne I hf hg (by omega : 0 < d) hdegree F).1
  let : IsFractionRing A F := IsIntegralClosure.isFractionRing_of_finite_extension R F F A
  have hι : Function.Injective ι := IsFractionRing.injective R F
  have hfrac (z : F) : ∃ r s : R, z = ι r / ι s := by
    obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective R z
    exact ⟨r, s, hrs.symm⟩
  have hD : ι (Ideal.Quotient.mk I (orbitJointDenominator a b i)) ≠ 0 := by
    apply (map_ne_zero_iff _ hι).mpr
    intro hzero
    exact orbitJoint_denominator_not_mem hba hi I hz (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι (by omega : 0 < d) hdegree
  have hw : Transcendental ℚ w := nonexceptional_chart_parameter_transcendental hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι (by omega : 0 < d) hdegree
  obtain ⟨B, hB, hsum⟩ := normalized_parameter_branches (L := F) w hw
  have hdim : Module.finrank ℚ (S ⧸ Ideal.span {w}) = d :=
    (nonexceptional_chart_infinity_dimension hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι (by omega : 0 < d) hdegree).2
  let V := fun j : Fin 3 => ψ (orbitJointNumerators a b i j.castSucc) /
    ψ (orbitJointDenominator a b i)
  let W := jointGraphFieldCoordinates I (orbitJointNumerators a b i) (orbitJointDenominator a b i) ι
  have ht : ∀ p : IsDedekindDomain.HeightOneSpectrum C, ∃ t : ℕ, p ∈ B →
      0 < t ∧ multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) = 2 * t ∧
        normalizedBranchOrder p F (ι (Ideal.Quotient.mk I (X 0))) < 0 ∧
        discretePoleOrder (normalizedBranchOrder p F) (W (Sum.inr 3)) = 5 * t := by
    intro p
    by_cases hp : p ∈ B
    · obtain ⟨t, ht⟩ := retained_infinity_branch_rank_five_pole hba hi hne I hf hg hz hnorm
        hres (by omega : 0 < d) hdegree ι hι hfrac p ((hB p).mp hp)
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => False.elim (hp h)⟩
  choose t ht using ht
  let E := poleEnvelopeBranches A V
  let n := fun q : IsDedekindDomain.HeightOneSpectrum A =>
    branchPoleEnvelope (normalizedBranchOrder q F) V
  have hnpos (q) (hq : q ∈ E) : 0 < n q := (mem_poleEnvelopeBranches V q).mp hq
  have hdisjoint (p) (hp : p ∈ B) (q) (_ : q ∈ E) :
      normalizedBranchOrder p F ≠ normalizedBranchOrder q F := by
    intro he
    have hneg := (ht p hp).2.2.1
    rw [he] at hneg
    have hnonneg := normalizedBranchOrder_nonnegative q F
      (algebraMap R A (Ideal.Quotient.mk I (X 0)))
    rw [← IsScalarTower.algebraMap_apply R A F] at hnonneg
    exact (not_lt_of_ge hnonneg) hneg
  let Wp := jointGraphFieldCoordinates I (orbitLinearJointNumerators G a b i m k)
    (orbitJointDenominator a b i ^ (m + k)) ι
  have hfinitePole (q) (hq : q ∈ E) : ∃ j, m * n q ≤
      discretePoleOrder (normalizedBranchOrder q F) (Wp j) :=
    linearJointGraph_envelope_pole_le I G hG _ _ ι hD m k q (hnpos q hq)
  have hinfinityPole (p) (hp : p ∈ B) : ∃ j, (5 * k) * t p ≤
      discretePoleOrder (normalizedBranchOrder p F) (Wp j) := by
    refine ⟨Sum.inr 3, ?_⟩
    simp only [Wp, orbitLinearJointNumerators]
    rw [powered_jointGraphFieldCoordinates I _ _ _ _ (jointCoordinatePowers_le m k) ι hD]
    change (5 * k) * t p ≤ discretePoleOrder (normalizedBranchOrder p F)
      (W (Sum.inr 3) ^ k)
    rw [discretePoleOrder_pow, (ht p hp).2.2.2]
    exact le_of_eq (by ring)
  have hDp : ι (Ideal.Quotient.mk I (orbitJointDenominator a b i ^ (m + k))) ≠ 0 := by
    rw [map_pow, map_pow]
    exact pow_ne_zero _ hD
  have hbound := jointGraph_two_model_poles_degree_le I (orbitLinearJointNumerators G a b i m k)
    (orbitJointDenominator a b i ^ (m + k)) ι hι hDp hfrac hgraph B E
    (fun p => (5 * k) * t p) (fun q => m * n q)
    (fun p hp => Nat.mul_pos (Nat.mul_pos (by decide) hk) (ht p hp).1)
    (fun q hq => Nat.mul_pos hm (hnpos q hq)) hdisjoint hinfinityPole hfinitePole
  exact pole_sum_degree_arith B E _ t _ n _ (fun p hp => (ht p hp).2.1) (hsum.trans hdim) hbound

/-- **Lower bound for the linearly changed powered graph** (paper, `lem:jointpowereddegree`).
For `G` invertible the graph `(nodes, (G W)ᵐ, Jᵏ)` has `(5k + 3m) d + 2m ≤ 2δ`, combining
`retained_linearJointGraph_degree_lower_bound_from_envelope` with the curvature pole degree
`retained_curvature_pole_degree_lower_bound` (`lem:jointpoledegree`). -/
theorem retained_linearJointGraph_degree_lower_bound {a b i d δ N m k : ℕ} {c₀ : ℤ}
    (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : IsUnit G.det) (hm : 0 < m) (hk : 0 < k)
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (Q : MvPolynomial (Fin 3) ℚ) (hQ : Prime Q) (hQdeg : Q.totalDegree = 2) (hQI : Q ∈ I)
    (hd3 : 3 ≤ d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (hgraph : ∃ M : ℕ, ∃ c : ℤ, ∀ n ≥ M,
      (Module.finrank ℚ
        (filteredCoordinateSpace (orbitLinearJointGraphIdeal G a b i m k I) n) : ℤ) =
          (δ : ℤ) * n + c)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] : (5 * k + 3 * m) * d + 2 * m ≤ 2 * δ := by
  have hgraphbound := retained_linearJointGraph_degree_lower_bound_from_envelope G hG hm hk
    hba hi hne I hf hg hz hnorm hres (by omega : 0 < d) hdegree hgraph F
  have hcurv := retained_curvature_pole_degree_lower_bound hba hi hne I hf hg hz hnorm hres
    Q hQ hQdeg hQI hd3 hdegree F
  dsimp only at hgraphbound hcurv
  nlinarith [Nat.mul_le_mul_left m hcurv]

/-- The linearly changed powered graph has the degree range `10n + 7m ≤ δ ≤
((m + n) 247 + 1) d` required by the curve theorem, uniformly over components of degree
`d ≥ 4`. -/
theorem orbitLinearJointGraph_retained_degree_range {a b i d m n : ℕ}
    (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : IsUnit G.det)
    (hm : 0 < m) (hn : 0 < n) (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (Q : MvPolynomial (Fin 3) ℚ) (hQ : Prime Q) (hQdeg : Q.totalDegree = 2) (hQI : Q ∈ I)
    (hd4 : 4 ≤ d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ j ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I j) : ℤ) = (d : ℤ) * j + c) :
    ∃ δ : ℕ, 10 * n + 7 * m ≤ δ ∧ δ ≤ ((m + n) * 247 + 1) * d ∧
      ∃ N : ℕ, ∃ c : ℤ, ∀ j ≥ N,
        (Module.finrank ℚ (filteredCoordinateSpace (orbitLinearJointGraphIdeal G a b i m n I) j)
          : ℤ) = (δ : ℤ) * j + c := by
  obtain ⟨_, δ, _, hupper, hgraph⟩ :=
    orbitLinearJointGraph_degree_bounds G hba hi m n I hz hdegree
  obtain ⟨N, c₀, hbase⟩ := hdegree
  have hlower := retained_linearJointGraph_degree_lower_bound G hG hm hn hba hi hne I hf hg hz
    hnorm hres Q hQ hQdeg hQI (by omega : 3 ≤ d) hbase hgraph
    (FractionRing (MvPolynomial (Fin 3) ℚ ⧸ I))
  exact ⟨δ, joint_powered_degree_minimum hd4 hlower, hupper, hgraph⟩

end
end PierceLengthBound.FixedDividend
