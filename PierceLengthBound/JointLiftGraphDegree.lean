/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftGraph
public import PierceLengthBound.FixedDividendHilbertLinearity

/-! Clearing a common denominator bounds the actual filtered Hilbert function of a rational graph. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- Clear a common denominator in every monomial of a bounded-degree polynomial.
The identity holds in an arbitrary target algebra. -/
theorem rational_substitution_clearing {K σ τ R : Type*} [Field K] [CommRing R] [Algebra K R]
    (φ : MvPolynomial τ K →ₐ[K] R) (ψ : MvPolynomial σ K →ₐ[K] R)
    (Q : MvPolynomial σ K) (U : τ → MvPolynomial σ K) {D N : ℕ}
    (hQ : Q.totalDegree ≤ D) (hU : ∀ j, (U j).totalDegree ≤ D)
    (he : ∀ j, ψ (U j) = ψ Q * φ (X j))
    (f : MvPolynomial τ K) (hf : f.totalDegree ≤ N) :
    ∃ g : MvPolynomial σ K, g.totalDegree ≤ D * N ∧ ψ g = ψ Q ^ N * φ f := by
  classical
  let term (m : τ →₀ ℕ) (c : K) :=
    C c * Q ^ (N - m.sum (fun _ n => n)) * m.prod (fun j n => U j ^ n)
  have htdeg (m : τ →₀ ℕ) (c : K) (hm : m.sum (fun _ n => n) ≤ N) :
      (term m c).totalDegree ≤ D * N := by
    have hpow : (Q ^ (N - m.sum (fun _ n => n))).totalDegree ≤
        (N - m.sum (fun _ n => n)) * D :=
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hQ)
    have hprod : (m.prod (fun j n => U j ^ n)).totalDegree ≤ m.sum (fun _ n => n) * D := by
      unfold Finsupp.prod Finsupp.sum
      apply (totalDegree_finsetProd _ _).trans
      rw [sum_mul]
      exact sum_le_sum fun j _ => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hU j))
    have h := totalDegree_mul (C c * Q ^ (N - m.sum (fun _ n => n)))
      (m.prod (fun j n => U j ^ n))
    have h' := totalDegree_mul (C c) (Q ^ (N - m.sum (fun _ n => n)))
    rw [totalDegree_C] at h'
    have hs := Nat.sub_add_cancel hm
    nlinarith
  have hteval (m : τ →₀ ℕ) (c : K) (hm : m.sum (fun _ n => n) ≤ N) :
      ψ (term m c) = ψ Q ^ N * φ (monomial m c) := by
    have hcψ : ψ (C c) = algebraMap K R c := ψ.commutes c
    have hcφ : φ (C c) = algebraMap K R c := φ.commutes c
    simp only [term, map_mul, hcψ, map_pow, Finsupp.prod, map_prod, he, mul_pow,
      prod_mul_distrib]
    rw [prod_pow_eq_pow_sum]
    rw [monomial_eq, map_mul, hcφ]
    simp only [Finsupp.prod, map_prod, map_pow]
    have hp : ψ Q ^ (N - m.sum (fun _ n => n)) * ψ Q ^ m.sum (fun _ n => n) = ψ Q ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hm]
    change algebraMap K R c * ψ Q ^ (N - m.sum (fun _ n => n)) *
      (ψ Q ^ m.sum (fun _ n => n) * ∏ j ∈ m.support, φ (X j) ^ m j) = _
    rw [← mul_assoc, mul_assoc (algebraMap K R c), hp]
    ring
  refine ⟨∑ m ∈ f.support, term m (f.coeff m), ?_, ?_⟩
  · exact totalDegree_finsetSum_le fun m hm => htdeg m _ ((le_totalDegree hm).trans hf)
  · rw [map_sum]
    calc (∑ m ∈ f.support, ψ (term m (f.coeff m))) =
        ∑ m ∈ f.support, ψ Q ^ N * φ (monomial m (f.coeff m)) :=
          sum_congr rfl fun m hm => hteval m _ ((le_totalDegree hm).trans hf)
      _ = _ := by rw [← mul_sum, ← map_sum, ← f.as_sum]

/-- A rational substitution does not increase filtered dimension faster than
its common-denominator degree. -/
theorem rational_substitution_filtered_finrank {K σ τ R : Type*} [Field K]
    [Finite σ] [Finite τ] [CommRing R] [Algebra K R]
    (φ : MvPolynomial τ K →ₐ[K] R) (ψ : MvPolynomial σ K →ₐ[K] R)
    (Q : MvPolynomial σ K) (U : τ → MvPolynomial σ K) {D N : ℕ}
    (hQ : Q.totalDegree ≤ D) (hU : ∀ j, (U j).totalDegree ≤ D)
    (he : ∀ j, ψ (U j) = ψ Q * φ (X j))
    (hinj : Function.Injective (fun r : R => ψ Q ^ N * r)) :
    Module.finrank K ((restrictTotalDegree τ K N).map φ.toLinearMap) ≤
      Module.finrank K ((restrictTotalDegree σ K (D * N)).map ψ.toLinearMap) := by
  let V := (restrictTotalDegree τ K N).map φ.toLinearMap
  let W := (restrictTotalDegree σ K (D * N)).map ψ.toLinearMap
  let μ : R →ₗ[K] R := LinearMap.mulLeft K (ψ Q ^ N)
  have hle : V.map μ ≤ W := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨g, hg, heq⟩ := rational_substitution_clearing φ ψ Q U hQ hU he f
      ((mem_restrictTotalDegree _ _ _).mp hf)
    exact Submodule.mem_map.mpr ⟨g, (mem_restrictTotalDegree _ _ _).mpr hg, heq⟩
  calc Module.finrank K V = Module.finrank K (V.map μ) :=
        (Submodule.equivMapOfInjective μ hinj V).finrank_eq
    _ ≤ Module.finrank K W := Submodule.finrank_mono hle

/-- The quotient by an algebra map's kernel has the same filtered dimensions
as its polynomial image. -/
lemma filteredCoordinateSpace_ker_finrank {K σ R : Type*} [Field K]
    [CommRing R] [Algebra K R] (φ : MvPolynomial σ K →ₐ[K] R) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (RingHom.ker φ) N) =
      Module.finrank K ((restrictTotalDegree σ K N).map φ.toLinearMap) := by
  let ψ : (MvPolynomial σ K ⧸ RingHom.ker φ) →ₐ[K] R :=
    Ideal.Quotient.liftₐ _ φ (by intro f hf; exact hf)
  have hinj : Function.Injective ψ := RingHom.kerLift_injective φ.toRingHom
  have he : (filteredCoordinateSpace (RingHom.ker φ) N).map ψ.toLinearMap =
      (restrictTotalDegree σ K N).map φ.toLinearMap := by
    rw [filteredCoordinateSpace, ← Submodule.map_comp]
    rfl
  rw [← he]
  exact (Submodule.equivMapOfInjective ψ.toLinearMap hinj _).finrank_eq

/-- The filtered coordinate space of a rational graph embeds, after denominator
clearing, into a bounded-degree filtered space on its base. -/
theorem jointGraph_filtered_finrank_le {K σ ι : Type*} [Field K] [Finite σ] [Finite ι]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (P : ι → MvPolynomial σ K)
    (Q : MvPolynomial σ K) (hQ : Q ∉ I) {D : ℕ}
    (hQD : Q.totalDegree + 1 ≤ D) (hPD : ∀ j, (P j).totalDegree ≤ D) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace (jointGraphIdeal I P Q) N) ≤
      Module.finrank K (filteredCoordinateSpace I (D * N)) := by
  classical
  have hQ0 : Ideal.Quotient.mk I Q ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hQ
  let : IsDomain (graphLocalization I Q) := Localization.Away.isDomain hQ0
  let locMap : (MvPolynomial σ K ⧸ I) →ₐ[K] graphLocalization I Q :=
    IsScalarTower.toAlgHom K _ _
  let ψ : MvPolynomial σ K →ₐ[K] graphLocalization I Q := locMap.comp (Ideal.Quotient.mkₐ K I)
  have hinjLoc : Function.Injective locMap := by
    apply IsLocalization.injective (M := Submonoid.powers (Ideal.Quotient.mk I Q))
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hQ0)
  have hker : RingHom.ker ψ = I := by
    ext f
    change locMap (Ideal.Quotient.mk I f) = 0 ↔ f ∈ I
    rw [map_eq_zero_iff _ hinjLoc, Ideal.Quotient.eq_zero_iff_mem]
  let U : σ ⊕ ι → MvPolynomial σ K := Sum.elim (fun j => Q * X j) P
  have hU : ∀ j, (U j).totalDegree ≤ D := by
    intro j
    cases j with
    | inl j => exact (totalDegree_mul _ _).trans (by simpa [totalDegree_X] using hQD)
    | inr j => exact hPD j
  have he : ∀ j, ψ (U j) = ψ Q * jointGraphMap I P Q (X j) := by
    intro j
    cases j with
    | inl j => simp [ψ, locMap, U, jointGraphMap]
    | inr j =>
      simp only [jointGraphMap, aeval_X, Sum.elim_inr, U]
      change ψ (P j) = ψ Q * (ψ (P j) * IsLocalization.Away.invSelf (Ideal.Quotient.mk I Q))
      have hu : ψ Q * IsLocalization.Away.invSelf (Ideal.Quotient.mk I Q) = 1 := by
        change algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q)
          (Ideal.Quotient.mk I Q) * _ = 1
        exact IsLocalization.Away.mul_invSelf (S := graphLocalization I Q) _
      rw [mul_left_comm, hu, mul_one]
  have hψQ : ψ Q ≠ 0 := fun hz => hQ0 (hinjLoc (by simpa [ψ] using hz))
  have hh := rational_substitution_filtered_finrank (jointGraphMap I P Q) ψ Q U
    (by omega : Q.totalDegree ≤ D) hU he (N := N)
    (fun x y h => mul_left_cancel₀ (pow_ne_zero N hψQ) h)
  rw [← filteredCoordinateSpace_ker_finrank, ← filteredCoordinateSpace_ker_finrank, hker] at hh
  exact hh

/-- In particular, the unpowered joint graph has filtration growth at most
that of its original curve with the degree parameter multiplied by 247. -/
theorem orbitJointGraph_filtered_finrank_le {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) (N : ℕ) :
    Module.finrank ℚ (filteredCoordinateSpace (orbitJointGraphIdeal a b i I) N) ≤
      Module.finrank ℚ (filteredCoordinateSpace I (247 * N)) := by
  have hd := jointLift_polynomial_degrees (orbitLiftNumeratorQ a b i)
    (orbitLiftDenominatorQ a b i) (jointRankFivePolynomial a b i) (Lz a b i : ℚ)
    (jointGapPolynomials a b i) (orbitLift_polynomial_degrees a b i).1
    (orbitLift_polynomial_degrees a b i).2 (jointRankFivePolynomial_degree a b i)
    (jointGapPolynomials_degree a b i)
  apply jointGraph_filtered_finrank_le I _ _ (orbitJoint_denominator_not_mem hba hi I hz)
  · exact le_trans (Nat.add_le_add_right hd.1 1) (by norm_num)
  · intro j
    fin_cases j
    · exact (hd.2.1 0).trans (by norm_num)
    · exact (hd.2.1 1).trans (by norm_num)
    · exact (hd.2.1 2).trans (by norm_num)
    · exact hd.2.2

/-- Projection onto the original variables supplies the reverse filtered inequality. -/
theorem jointGraph_filtered_finrank_ge {K σ ι : Type*} [Field K] [Finite σ] [Finite ι]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (P : ι → MvPolynomial σ K)
    (Q : MvPolynomial σ K) (hQ : Q ∉ I) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank K (filteredCoordinateSpace (jointGraphIdeal I P Q) N) := by
  let J := jointGraphIdeal I P Q
  let ρ : MvPolynomial σ K →ₐ[K] (MvPolynomial (σ ⊕ ι) K ⧸ J) :=
    (Ideal.Quotient.mkₐ K J).comp (MvPolynomial.rename Sum.inl)
  have hker : RingHom.ker ρ = I := by
    ext f
    change Ideal.Quotient.mk J (rename Sum.inl f) = 0 ↔ f ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact jointGraph_rename_mem_iff I P Q f hQ
  have hle : (restrictTotalDegree σ K N).map ρ.toLinearMap ≤ filteredCoordinateSpace J N := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨rename Sum.inl f, ?_, rfl⟩
    rw [mem_restrictTotalDegree] at hf ⊢
    exact (totalDegree_rename_le _ _).trans hf
  calc Module.finrank K (filteredCoordinateSpace I N) =
        Module.finrank K ((restrictTotalDegree σ K N).map ρ.toLinearMap) := by
          rw [← hker, filteredCoordinateSpace_ker_finrank]
    _ ≤ _ := Submodule.finrank_mono hle

/-- An eventual affine Hilbert formula gives a uniform linear bound, including
all initial filtration levels. -/
lemma filtered_uniform_linear_bound {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) {d : ℕ}
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ C : ℕ, ∀ n, Module.finrank K (filteredCoordinateSpace I n) ≤ C * (n + 1) := by
  obtain ⟨N, c, hf⟩ := hd
  let C := Module.finrank K (filteredCoordinateSpace I N) + d + c.natAbs
  refine ⟨C, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have h := hf n hn
    have hc : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
    have hbound : Module.finrank K (filteredCoordinateSpace I n) ≤ d * n + c.natAbs := by
      exact_mod_cast (show (Module.finrank K (filteredCoordinateSpace I n) : ℤ) ≤
        (d : ℤ) * n + (c.natAbs : ℤ) by omega)
    apply hbound.trans
    calc d * n + c.natAbs ≤ d * n + c.natAbs * n + d + c.natAbs := by omega
      _ = (d + c.natAbs) * (n + 1) := by ring
      _ ≤ C * (n + 1) := Nat.mul_le_mul_right _ (by dsimp [C]; omega)
  · have hbound := Submodule.finrank_mono (filteredCoordinateSpace_mono I (by omega : n ≤ N))
    apply hbound.trans
    calc Module.finrank K (filteredCoordinateSpace I N) ≤ C := by dsimp [C]; omega
      _ = C * 1 := by simp
      _ ≤ C * (n + 1) := Nat.mul_le_mul_left _ (by omega)

lemma eventual_affine_slope_le {a b N : ℕ} {c e : ℤ}
    (h : ∀ n ≥ N, (a : ℤ) * n + c ≤ (b : ℤ) * n + e) : a ≤ b := by
  by_contra hab
  have hab' : (b : ℤ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
  have hn := h (N + c.natAbs + e.natAbs + 1) (by omega)
  have hc : -(c.natAbs : ℤ) ≤ c := by rw [Int.natCast_natAbs]; exact neg_abs_le c
  have he : e ≤ (e.natAbs : ℤ) := Int.le_natAbs
  push_cast only [Nat.cast_add, Nat.cast_one] at hn
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ a - b - 1 by omega)
    (show (0 : ℤ) ≤ N + c.natAbs + e.natAbs + 1 by positivity)]

/-- A rational graph over an affine curve is again an affine curve. Its degree
is between the base degree and the common-denominator degree times that degree. -/
theorem jointGraph_degree_bounds {K σ ι : Type*} [Field K] [Finite σ] [Finite ι]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (P : ι → MvPolynomial σ K)
    (Q : MvPolynomial σ K) (hQ : Q ∉ I) {D d : ℕ}
    (hQD : Q.totalDegree + 1 ≤ D) (hPD : ∀ j, (P j).totalDegree ≤ D)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ δ : ℕ, d ≤ δ ∧ δ ≤ D * d ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace (jointGraphIdeal I P Q) n) : ℤ) =
        (δ : ℤ) * n + c := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder (σ ⊕ ι) := LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _)
  obtain ⟨C, hC⟩ := filtered_uniform_linear_bound I hd
  have hD : 1 ≤ D := by omega
  have hub (n : ℕ) (_hn : 14 ≤ n) :
      Module.finrank K (filteredCoordinateSpace (jointGraphIdeal I P Q) n) ≤
        (C * (D + 1)) * (n + 2) := by
    have h := (jointGraph_filtered_finrank_le I P Q hQ hQD hPD n).trans (hC (D * n))
    nlinarith
  obtain ⟨δ, _, M, e, hg⟩ := filteredCoordinateSpace_eventually_linear
    (jointGraphIdeal I P Q) (C * (D + 1)) hub
  obtain ⟨N, c, hf⟩ := hd
  have hlo : d ≤ δ := by
    apply eventual_affine_slope_le (N := max N M) (c := c) (e := e)
    intro n hn
    have h := jointGraph_filtered_finrank_ge I P Q hQ n
    have h' : (Module.finrank K (filteredCoordinateSpace I n) : ℤ) ≤
        Module.finrank K (filteredCoordinateSpace (jointGraphIdeal I P Q) n) := by exact_mod_cast h
    rwa [hf n (by omega), hg n (by omega)] at h'
  have hhi : δ ≤ D * d := by
    apply eventual_affine_slope_le (N := max N M) (c := e) (e := c)
    intro n hn
    have h := jointGraph_filtered_finrank_le I P Q hQ hQD hPD n
    have h' : (Module.finrank K (filteredCoordinateSpace (jointGraphIdeal I P Q) n) : ℤ) ≤
        Module.finrank K (filteredCoordinateSpace I (D * n)) := by exact_mod_cast h
    rw [hg n (by omega), hf (D * n) (by
      calc N ≤ n := (le_max_left N M).trans hn
        _ = 1 * n := by simp
        _ ≤ D * n := Nat.mul_le_mul_right _ hD)] at h'
    push_cast at h' ⊢
    nlinarith
  exact ⟨δ, hlo, hhi, M, e, hg⟩

/-- The actual seven-dimensional joint graph has a well-defined degree at most
247 times its base degree; this proves the candidate's upper degree bound. -/
theorem orbitJointGraph_degree_bounds {a b i d : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ δ : ℕ, d ≤ δ ∧ δ ≤ 247 * d ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace (orbitJointGraphIdeal a b i I) n) : ℤ) =
        (δ : ℤ) * n + c := by
  have hp := jointLift_polynomial_degrees (orbitLiftNumeratorQ a b i)
    (orbitLiftDenominatorQ a b i) (jointRankFivePolynomial a b i) (Lz a b i : ℚ)
    (jointGapPolynomials a b i) (orbitLift_polynomial_degrees a b i).1
    (orbitLift_polynomial_degrees a b i).2 (jointRankFivePolynomial_degree a b i)
    (jointGapPolynomials_degree a b i)
  apply jointGraph_degree_bounds I _ _ (orbitJoint_denominator_not_mem hba hi I hz)
    (D := 247) _ _ hd
  · exact le_trans (Nat.add_le_add_right hp.1 1) (by norm_num)
  · intro j
    fin_cases j
    · exact (hp.2.1 0).trans (by norm_num)
    · exact (hp.2.1 1).trans (by norm_num)
    · exact (hp.2.1 2).trans (by norm_num)
    · exact hp.2.2

end
end PierceLengthBound.FixedDividend
