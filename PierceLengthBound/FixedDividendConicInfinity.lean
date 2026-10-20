/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendDegreeParity

/-!
# A degree-two infinity section has a unique residue point

Two distinct characters of a two-dimensional algebra separate all its elements.
Applied to the actual square/fourth-power identity, this would force the norm to
be divisible by infinity and contradict resultant invertibility there. This
establishes uniqueness of the conic's infinity point without normalization.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Distinct characters of a two-dimensional algebra jointly separate elements. -/
theorem two_dimensional_characters_injective {K S : Type*} [Field K]
    [CommRing S] [Algebra K S] [Module.Finite K S]
    (hdim : Module.finrank K S = 2) (φ ψ : S →ₐ[K] K) (hne : φ ≠ ψ) :
    Function.Injective (fun x : S => (φ x, ψ x)) := by
  obtain ⟨x, hx⟩ : ∃ x : S, φ x ≠ ψ x := by
    by_contra h
    push Not at h
    exact hne (AlgHom.ext h)
  let f : S →ₗ[K] K × K := φ.toLinearMap.prod ψ.toLinearMap
  have hsurj : Function.Surjective f := by
    rintro ⟨a, b⟩
    refine ⟨algebraMap K S ((b - a) / (ψ x - φ x)) *
      (x - algebraMap K S (φ x)) + algebraMap K S a, ?_⟩
    apply Prod.ext
    · change φ _ = a
      simp
    · change ψ _ = b
      simp only [map_add, map_mul, map_sub, AlgHom.commutes,
        Algebra.algebraMap_self, RingHom.id_apply]
      field_simp [sub_ne_zero.mpr hx.symm]
      ring
  have hd : Module.finrank K S = Module.finrank K (K × K) := by simp [hdim]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj

/-- The square/fourth-power equation forces a two-dimensional infinity section
to have at most one point over its algebraically closed coefficient field. -/
theorem square_fourth_two_dimensional_unique_character {K R : Type*}
    [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a) (hh : h ≠ 0)
    [Module.Finite K (R ⧸ Ideal.span {h})]
    (hdim : Module.finrank K (R ⧸ Ideal.span {h}) = 2)
    (hr : IsUnit (Ideal.Quotient.mk (Ideal.span {h}) r))
    (heq : A * h ^ 2 * r = a * δ ^ 4)
    (φ ψ : (R ⧸ Ideal.span {h}) →ₐ[K] K) : φ = ψ := by
  by_contra hne
  let S := R ⧸ Ideal.span {h}
  let q := Ideal.Quotient.mkₐ K (Ideal.span {h})
  have : Nontrivial S := Module.nontrivial_of_finrank_pos (R := K) (by
    change 0 < Module.finrank K (R ⧸ Ideal.span {h})
    rw [hdim]
    decide)
  have hq : q h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have hδ (χ : S →ₐ[K] K) : χ (q δ) = 0 := by
    have ht := congrArg (χ.comp q) heq
    simp only [AlgHom.comp_apply, map_mul, map_pow, hq, map_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul] at ht
    have ha' : χ (q a) ≠ 0 := ((ha.map q).map χ).ne_zero
    exact (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp
      ((mul_eq_zero.mp ht.symm).resolve_left ha')
  have hz : q δ = 0 := two_dimensional_characters_injective hdim φ ψ hne (by
    simp only [hδ, map_zero])
  have hmem : δ ∈ (Ideal.span {h} : Ideal R) := Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem
  have he : h ^ 2 * (A * r) = h ^ 2 * (a * h ^ 2 * t ^ 4) := by
    rw [ht] at heq
    convert heq using 1 <;> ring
  have hc := mul_left_cancel₀ (pow_ne_zero 2 hh) he
  have hcq := congrArg q hc
  simp only [map_mul, map_pow, hq, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at hcq
  exact ((hA.map q).mul hr).ne_zero hcq


/-- In a two-dimensional algebra, a nonzero common kernel vector forces two
characters into any overfield to agree. This also treats rational sections. -/
theorem two_dimensional_common_kernel_unique {K L S : Type*}
    [Field K] [Field L] [Algebra K L] [CommRing S] [Algebra K S]
    [Module.Finite K S] (hdim : Module.finrank K S = 2)
    (φ ψ : S →ₐ[K] L) {δ : S} (hδ : δ ≠ 0) (hφ : φ δ = 0) (hψ : ψ δ = 0) :
    φ = ψ := by
  have hi : LinearIndependent K (![1, δ] : Fin 2 → S) := by
    rw [linearIndependent_fin2]
    refine ⟨hδ, ?_⟩
    intro a ha
    have ht := congrArg φ ha
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_smul, hφ, smul_zero,
      map_one] at ht
    exact zero_ne_one ht
  have hr : Set.range (![1, δ] : Fin 2 → S) = {1, δ} := by
    ext x
    simp [or_comm]
  have hs : Submodule.span K ({1, δ} : Set S) = ⊤ := by
    rw [← hr]
    exact hi.span_eq_top_of_card_eq_finrank (by simp [hdim])
  apply AlgHom.ext
  intro x
  have hx : x ∈ Submodule.span K ({1, δ} : Set S) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => rcases hx with rfl | hx <;> simp_all
  | zero => simp
  | add x y hx hy hix hiy => simp only [map_add, hix, hiy]
  | smul a x hx hix => simp only [map_smul, hix]

/-- The uniqueness conclusion also holds for complex points of a rational
section: no base-change formula for Hilbert degrees is needed. -/
theorem square_fourth_two_dimensional_unique_closed_character {K L R : Type*}
    [Field K] [Field L] [Algebra K L] [CommRing R] [IsDomain R] [Algebra K R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a) (hh : h ≠ 0)
    [Module.Finite K (R ⧸ Ideal.span {h})]
    (hdim : Module.finrank K (R ⧸ Ideal.span {h}) = 2)
    (hr : IsUnit (Ideal.Quotient.mk (Ideal.span {h}) r))
    (heq : A * h ^ 2 * r = a * δ ^ 4)
    (φ ψ : (R ⧸ Ideal.span {h}) →ₐ[K] L) : φ = ψ := by
  let S := R ⧸ Ideal.span {h}
  let q := Ideal.Quotient.mkₐ K (Ideal.span {h})
  have : Nontrivial S := Module.nontrivial_of_finrank_pos (R := K) (by
    change 0 < Module.finrank K (R ⧸ Ideal.span {h})
    rw [hdim]
    decide)
  have hq : q h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have hδ (χ : S →ₐ[K] L) : χ (q δ) = 0 := by
    have ht := congrArg (χ.comp q) heq
    simp only [AlgHom.comp_apply, map_mul, map_pow, hq, map_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at ht
    have ha' : χ (q a) ≠ 0 := ((ha.map q).map χ).ne_zero
    exact (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp
      ((mul_eq_zero.mp ht.symm).resolve_left ha')
  apply two_dimensional_common_kernel_unique hdim φ ψ _ (hδ φ) (hδ ψ)
  intro hz
  have hmem : δ ∈ (Ideal.span {h} : Ideal R) := Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem
  have he : h ^ 2 * (A * r) = h ^ 2 * (a * h ^ 2 * t ^ 4) := by
    rw [ht] at heq
    convert heq using 1 <;> ring
  have hc := mul_left_cancel₀ (pow_ne_zero 2 hh) he
  have hcq := congrArg q hc
  simp only [map_mul, map_pow, hq, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at hcq
  exact ((hA.map q).mul hr).ne_zero hcq


/-- The norm has a nonzero nilpotent residue along infinity. It supplies the
nilpotent basis vector in every degree-two section. -/
theorem square_fourth_norm_residue {K R : Type*}
    [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a) (hh : h ≠ 0)
    [Nontrivial (R ⧸ Ideal.span {h})]
    (hr : IsUnit (Ideal.Quotient.mk (Ideal.span {h}) r))
    (heq : A * h ^ 2 * r = a * δ ^ 4) :
    Ideal.Quotient.mk (Ideal.span {h}) δ ≠ 0 ∧
      IsNilpotent (Ideal.Quotient.mk (Ideal.span {h}) δ) := by
  let q := Ideal.Quotient.mk (Ideal.span {h})
  have hq : q h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  constructor
  · intro hz
    have hmem : δ ∈ (Ideal.span {h} : Ideal R) := Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem
    have he : h ^ 2 * (A * r) = h ^ 2 * (a * h ^ 2 * t ^ 4) := by
      rw [ht] at heq
      convert heq using 1 <;> ring
    have hc := mul_left_cancel₀ (pow_ne_zero 2 hh) he
    have hcq := congrArg q hc
    simp only [map_mul, map_pow, hq, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at hcq
    exact ((hA.map q).mul hr).ne_zero hcq
  · refine ⟨4, ?_⟩
    have ht := congrArg q heq
    simp only [map_mul, map_pow, hq, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at ht
    exact (ha.map q).mul_right_eq_zero.mp ht.symm

end
end PierceLengthBound.FixedDividend
