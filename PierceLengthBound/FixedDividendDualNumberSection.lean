/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import PierceLengthBound.FixedDividendChartHomogenization
public import PierceLengthBound.FixedDividendLocalizationParity
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Quadratic relations in a two-dimensional nonreduced section

The square/fourth-power identity makes the norm a nonzero nilpotent residue
modulo the infinity coordinate. A nonzero nilpotent in a two-dimensional
algebra is square-zero and, together with one, forms a basis. A nonscalar
element therefore satisfies only quadratic relations with zero discriminant.
This supplies the algebraic parabola test for the infinity section of a
rational conic.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

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

lemma nilpotent_pow_finrank_eq_zero {K S : Type*} [Field K] [CommRing S]
    [Algebra K S] [Module.Finite K S] {δ : S} (hδ : IsNilpotent δ) :
    δ ^ Module.finrank K S = 0 := by
  let f := Algebra.lmul K S δ
  have hn : IsNilpotent f := hδ.map (Algebra.lmul K S)
  have hz : f ^ Module.finrank K S = 0 := by
    rw [← Polynomial.aeval_X_pow (R := K), ← hn.charpoly_eq_X_pow_finrank,
      LinearMap.aeval_self_charpoly]
  have he := congrArg (fun g : Module.End K S => g 1) hz
  simp only [f, ← map_pow, LinearMap.zero_apply] at he
  change δ ^ Module.finrank K S * 1 = 0 at he
  simpa only [mul_one] using he

lemma two_dimensional_nilpotent_span {K L S : Type*}
    [Field K] [Field L] [Algebra K L] [CommRing S] [Algebra K S]
    [Module.Finite K S] (hdim : Module.finrank K S = 2)
    (φ : S →ₐ[K] L) {δ : S} (hδ : δ ≠ 0) (hn : IsNilpotent δ) :
    Submodule.span K ({1, δ} : Set S) = ⊤ := by
  have hz : φ δ = 0 := (hn.map φ).eq_zero
  have hi : LinearIndependent K (![1, δ] : Fin 2 → S) := by
    rw [linearIndependent_fin2]
    refine ⟨hδ, ?_⟩
    intro a ha
    have ht := congrArg φ ha
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_smul, hz, smul_zero,
      map_one] at ht
    exact zero_ne_one ht
  have hr : Set.range (![1, δ] : Fin 2 → S) = {1, δ} := by
    ext x
    simp [or_comm]
  rw [← hr]
  exact hi.span_eq_top_of_card_eq_finrank (by simp [hdim])

/-- The discriminant vanishes for a quadratic relation on any nonscalar
coordinate of the two-dimensional nonreduced infinity section. -/
theorem two_dimensional_quadratic_discriminant_zero {K L S : Type*}
    [Field K] [Field L] [Algebra K L] [CommRing S] [Algebra K S]
    [Module.Finite K S] (hdim : Module.finrank K S = 2)
    (φ : S →ₐ[K] L) {δ : S} (hδ : δ ≠ 0) (hn : IsNilpotent δ)
    {t : S} (ht : ∀ c : K, t ≠ algebraMap K S c)
    {α β γ : K}
    (he : algebraMap K S α * t ^ 2 + algebraMap K S β * t + algebraMap K S γ = 0) :
    β ^ 2 - 4 * α * γ = 0 := by
  have hs := two_dimensional_nilpotent_span hdim φ hδ hn
  have hmem : t ∈ Submodule.span K ({1, δ} : Set S) := by rw [hs]; trivial
  obtain ⟨c, b, heq⟩ := Submodule.mem_span_pair.mp hmem
  have ht' : t = algebraMap K S c + algebraMap K S b * δ := by
    simpa only [Algebra.smul_def, mul_one] using heq.symm
  have hb : b ≠ 0 := by
    intro hz
    apply ht c
    simpa [hz] using ht'
  have hδ2 : δ ^ 2 = 0 := by simpa only [hdim] using nilpotent_pow_finrank_eq_zero (K := K) hn
  have hφδ : φ δ = 0 := (hn.map φ).eq_zero
  have hφt : φ t = algebraMap K L c := by simp [ht', hφδ]
  have hc : α * c ^ 2 + β * c + γ = 0 := by
    apply (algebraMap K L).injective
    have hh := congrArg φ he
    simpa only [map_add, map_mul, map_pow, AlgHom.commutes, hφt, map_zero] using hh
  have he' : algebraMap K S ((2 * α * c + β) * b) * δ = 0 := by
    have hid : algebraMap K S α * t ^ 2 + algebraMap K S β * t + algebraMap K S γ =
        algebraMap K S (α * c ^ 2 + β * c + γ) +
          algebraMap K S ((2 * α * c + β) * b) * δ +
          algebraMap K S (α * b ^ 2) * δ ^ 2 := by
      rw [ht']
      simp only [map_add, map_mul, map_pow, map_ofNat]
      ring
    rw [hid, hc, map_zero, hδ2, mul_zero, add_zero, zero_add] at he
    exact he
  have hb' : (2 * α * c + β) * b = 0 := by
    have hh : ((2 * α * c + β) * b) • δ = 0 := by
      simpa only [Algebra.smul_def] using he'
    exact (smul_eq_zero.mp hh).resolve_right hδ
  have hlin : 2 * α * c + β = 0 := (mul_eq_zero.mp hb').resolve_right hb
  have : β = -2 * α * c := by linear_combination hlin
  rw [this] at hc ⊢
  linear_combination -4 * α * hc

end
end PierceLengthBound.FixedDividend
