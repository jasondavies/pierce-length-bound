/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendProjectiveChart
public import PierceLengthBound.FixedDividendSectionRegularity

/-!
# The infinity section in a concrete affine chart

This module identifies the kernel of the homogeneous-piece map to the affine
chart's infinity section. Eventual generation by the chart coordinate implies
that no extra kernel is introduced by dehomogenization.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

lemma filteredCoordinateSpace_pow_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) {l : MvPolynomial σ K ⧸ I}
    (hl : l ∈ filteredCoordinateSpace I 1) (n : ℕ) :
    l ^ n ∈ filteredCoordinateSpace I n := by
  induction n with
  | zero => simpa using filteredCoordinateSpace_algebraMap_mem I 0 1
  | succ n ih => simpa only [pow_succ] using filteredCoordinateSpace_mul_mem I ih hl

/-- A homogeneous numerator divided by the chart coordinate to its degree. -/
def chartMonomialMap {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (n : ℕ) :
    filteredCoordinateSpace I n →ₗ[K] projectiveChart I ι l where
  toFun a := ⟨ι a * (ι l)⁻¹ ^ n, projectiveChartPiece_le I ι l n
    ((mem_projectiveChartPiece I ι l n _).mpr ⟨a, a.property, rfl⟩)⟩
  map_add' a b := by apply Subtype.ext; simp [add_mul]
  map_smul' c a := by apply Subtype.ext; simp [Algebra.smul_def, mul_assoc]

@[simp] lemma chartMonomialMap_val {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (n : ℕ) (a : filteredCoordinateSpace I n) :
    (chartMonomialMap I ι l n a : F) = ι a * (ι l)⁻¹ ^ n := rfl

/-- The equation of infinity in the chosen chart. -/
def chartInfinityCoordinate {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) : projectiveChart I ι l :=
  ⟨(ι l)⁻¹, Subalgebra.mem_map.mpr ⟨Polynomial.X,
    (projectiveInfinityCoordinate I).property, by
      change Polynomial.eval₂ ι.toRingHom (ι l)⁻¹ Polynomial.X = _
      simp only [Polynomial.eval₂_X]⟩⟩

/-- Its principal ideal defines the finite infinity section of the chart. -/
def chartInfinityIdeal {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) : Ideal (projectiveChart I ι l) :=
  Ideal.span {chartInfinityCoordinate I ι l}

instance chartInfinityIdeal_twoSided {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) : (chartInfinityIdeal I ι l).IsTwoSided := by
  constructor
  intro a b ha
  simpa only [smul_eq_mul, mul_comm a b] using (chartInfinityIdeal I ι l).smul_mem b ha

/-- The homogeneous-piece map to the actual affine infinity section. -/
def chartPieceToInfinity {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (n : ℕ) :
    filteredCoordinateSpace I n →ₗ[K] projectiveChart I ι l ⧸ chartInfinityIdeal I ι l :=
  (Ideal.Quotient.mkₐ K (chartInfinityIdeal I ι l)).toLinearMap.comp
    (chartMonomialMap I ι l n)

/-- Dehomogenization introduces no extra kernel once the linear coordinate
surjects on the stable graded pieces. -/
theorem chartMonomial_mem_infinityIdeal {K σ F : Type*}
    [Field K] [Field F] [Algebra K F] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hι : Function.Injective ι)
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : ι l ≠ 0)
    {d N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (hspan : ∀ n ≥ N, filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
      filteredCoordinateSpace I (n + 2))
    (a : filteredCoordinateSpace I (N + 1)) :
    chartMonomialMap I ι l (N + 1) a ∈ chartInfinityIdeal I ι l ↔
      (a : MvPolynomial σ K ⧸ I) ∈ filteredCoordinateSpace I N := by
  rw [chartInfinityIdeal, Ideal.mem_span_singleton (α := projectiveChart I ι l)]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨m, c, hc, hcg⟩ := (mem_projectiveChart_iff I ι l hl hl0 (g : F)).mp g.property
    have he := congrArg (fun x : projectiveChart I ι l => (x : F)) hg
    change ι (a : MvPolynomial σ K ⧸ I) * (ι l)⁻¹ ^ (N + 1) = (ι l)⁻¹ * (g : F) at he
    rw [← hcg] at he
    have hmul : l ^ (m + 1) * (a : MvPolynomial σ K ⧸ I) = l ^ (N + 1) * c := by
      apply hι
      simp only [map_mul, map_pow]
      have he' : ι (a : MvPolynomial σ K ⧸ I) / (ι l) ^ (N + 1) =
          ι c / (ι l) ^ (m + 1) := by
        simpa only [div_eq_mul_inv, inv_pow, pow_succ, mul_inv_rev,
          mul_assoc, mul_left_comm, mul_comm] using he
      have ht := (div_eq_div_iff (pow_ne_zero _ hl0) (pow_ne_zero _ hl0)).mp he'
      simpa only [mul_comm] using ht
    have hln : l ≠ 0 := fun h => hl0 (by simp [h])
    apply filtered_linear_coordinate_saturation I l hl hln hdegree hspan le_rfl (m + 1)
      a.property
    rw [hmul]
    have hm := filteredCoordinateSpace_mul_mem I
      (filteredCoordinateSpace_pow_mem I hl (N + 1)) hc
    simpa only [show N + 1 + m = N + (m + 1) by omega] using hm
  · intro ha
    refine ⟨chartMonomialMap I ι l N ⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    change ι (a : MvPolynomial σ K ⧸ I) * (ι l)⁻¹ ^ (N + 1) =
      (ι l)⁻¹ * (ι (a : MvPolynomial σ K ⧸ I) * (ι l)⁻¹ ^ N)
    rw [pow_succ]
    ring

/-- The stable piece's image in the chart section has dimension exactly the
actual affine Hilbert degree. Surjectivity onto the whole section is separate. -/
theorem chartPieceToInfinity_finrank_range {K σ F : Type*}
    [Field K] [Field F] [Algebra K F] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hι : Function.Injective ι)
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : ι l ≠ 0)
    {d N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (hspan : ∀ n ≥ N, filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
      filteredCoordinateSpace I (n + 2)) :
    Module.finrank K (chartPieceToInfinity I ι l (N + 1)).range = d := by
  have hker : (chartPieceToInfinity I ι l (N + 1)).ker =
      (filteredCoordinateSpace I N).comap (filteredCoordinateSpace I (N + 1)).subtype := by
    ext a
    change Ideal.Quotient.mk (chartInfinityIdeal I ι l)
      (chartMonomialMap I ι l (N + 1) a) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem,
      chartMonomial_mem_infinityIdeal I ι hι l hl hl0 hdegree hspan]
    rfl
  have h := LinearMap.finrank_range_add_finrank_ker (chartPieceToInfinity I ι l (N + 1))
  rw [hker] at h
  have hk := Submodule.finrank_map_subtype_eq (filteredCoordinateSpace I (N + 1))
    ((filteredCoordinateSpace I N).comap (filteredCoordinateSpace I (N + 1)).subtype)
  rw [Submodule.map_comap_subtype,
    inf_eq_right.mpr (filteredCoordinateSpace_mono I (by omega))] at hk
  rw [← hk] at h
  have hd0 := hdegree N le_rfl
  have hd1 := hdegree (N + 1) (by omega)
  push_cast at hd1
  nlinarith

lemma chartPieceToInfinity_range_mono {K σ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : ι l ≠ 0) :
    Monotone (fun n => (chartPieceToInfinity I ι l n).range) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨⟨(a : MvPolynomial σ K ⧸ I) * l,
    filteredCoordinateSpace_mul_mem I a.property hl⟩, ?_⟩
  change Ideal.Quotient.mk _ (chartMonomialMap I ι l (n + 1) _) =
    Ideal.Quotient.mk _ (chartMonomialMap I ι l n a)
  congr 1
  apply Subtype.ext
  change ι ((a : MvPolynomial σ K ⧸ I) * l) * (ι l)⁻¹ ^ (n + 1) =
    ι (a : MvPolynomial σ K ⧸ I) * (ι l)⁻¹ ^ n
  rw [map_mul, pow_succ]
  field_simp

/-- Graded generation makes the successive chart-section images equal. -/
lemma chartPieceToInfinity_range_succ_le {K σ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (hl0 : ι l ≠ 0) (n : ℕ)
    (hspan : filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
      filteredCoordinateSpace I (n + 2)) :
    (chartPieceToInfinity I ι l (n + 2)).range ≤
      (chartPieceToInfinity I ι l (n + 1)).range := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  have ha : (a : MvPolynomial σ K ⧸ I) ∈ filteredCoordinateSpace I (n + 1) ⊔
      (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) := by
    simpa only [hspan] using a.property
  obtain ⟨b, hb, c, hc, he⟩ := Submodule.mem_sup.mp ha
  obtain ⟨c', hc', rfl⟩ := hc
  refine ⟨⟨c', hc'⟩, ?_⟩
  have hid : chartMonomialMap I ι l (n + 2) a =
      chartInfinityCoordinate I ι l * chartMonomialMap I ι l (n + 1) ⟨b, hb⟩ +
      chartMonomialMap I ι l (n + 1) ⟨c', hc'⟩ := by
    apply Subtype.ext
    change ι (a : MvPolynomial σ K ⧸ I) * (ι l)⁻¹ ^ (n + 2) =
      (ι l)⁻¹ * (ι b * (ι l)⁻¹ ^ (n + 1)) + ι c' * (ι l)⁻¹ ^ (n + 1)
    change b + l * c' = (a : MvPolynomial σ K ⧸ I) at he
    rw [← he, map_add, map_mul]
    simp only [pow_succ]
    field_simp
  have hw : Ideal.Quotient.mk (chartInfinityIdeal I ι l)
      (chartInfinityCoordinate I ι l) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  change Ideal.Quotient.mk _ (chartMonomialMap I ι l (n + 1) _) =
    Ideal.Quotient.mk _ (chartMonomialMap I ι l (n + 2) a)
  rw [hid, map_add, map_mul, hw, zero_mul, zero_add]

/-- Stable generation covers the entire affine section by a single homogeneous piece. -/
theorem chartPieceToInfinity_surjective {K σ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : ι l ≠ 0)
    (N : ℕ)
    (hspan : ∀ n ≥ N, filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
      filteredCoordinateSpace I (n + 2)) :
    Function.Surjective (chartPieceToInfinity I ι l (N + 1)) := by
  have hr : ∀ m, (chartPieceToInfinity I ι l m).range ≤
      (chartPieceToInfinity I ι l (N + 1)).range := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm : m ≤ N + 1
      · exact chartPieceToInfinity_range_mono I ι l hl hl0 hm
      have hn : N ≤ m - 2 := by omega
      have hs := chartPieceToInfinity_range_succ_le I ι l hl0 (m - 2) (hspan _ hn)
      rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at hs
      exact hs.trans (ih (m - 1) (by omega))
  intro x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨m, a, ha, hag⟩ := (mem_projectiveChart_iff I ι l hl hl0 (g : F)).mp g.property
  apply hr m
  refine ⟨⟨a, ha⟩, ?_⟩
  change Ideal.Quotient.mk _ (chartMonomialMap I ι l m _) = Ideal.Quotient.mk _ g
  congr 1
  exact Subtype.ext hag

/-- The actual affine-chart infinity section is finite-dimensional and its dimension
is exactly the certified affine Hilbert degree, provided the chart coordinate
eventually generates the homogeneous infinity pieces. -/
theorem chart_infinity_dimension_eq_degree {K σ F : Type*}
    [Field K] [Field F] [Algebra K F] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hι : Function.Injective ι)
    (l : MvPolynomial σ K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1) (hl0 : ι l ≠ 0)
    {d N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (hspan : ∀ n ≥ N, filteredCoordinateSpace I (n + 1) ⊔
        (filteredCoordinateSpace I (n + 1)).map (LinearMap.mulLeft K l) =
      filteredCoordinateSpace I (n + 2)) :
    Module.Finite K (projectiveChart I ι l ⧸ chartInfinityIdeal I ι l) ∧
      Module.finrank K (projectiveChart I ι l ⧸ chartInfinityIdeal I ι l) = d := by
  have hs := chartPieceToInfinity_surjective I ι l hl hl0 N hspan
  refine ⟨Module.Finite.of_surjective _ hs, ?_⟩
  have hd := chartPieceToInfinity_finrank_range I ι hι l hl hl0 hdegree hspan
  rwa [LinearMap.range_eq_top.mpr hs, finrank_top] at hd

end
end PierceLengthBound.FixedDividend
