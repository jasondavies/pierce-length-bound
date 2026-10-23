/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib

/-!
# Parity of finite-dimensional principal sections

Multiplication gives a short exact sequence for principal sections. Consequently
an infinity equation whose square is a unit times a fourth power cuts out an
even-dimensional finite section. This argument works over the ground field and
does not require geometric component descent or a sum over local branches.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped Pointwise

lemma finrank_eq_add_of_exact {K M N P : Type*} [Field K]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module K M] [Module K N] [Module K P]
    [Module.Finite K M] [Module.Finite K P]
    (f : M →ₗ[K] N) (g : N →ₗ[K] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g) :
    Module.finrank K N = Module.finrank K M + Module.finrank K P := by
  let : Module.Finite K N := Module.Finite.of_exact he hg
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top,
    LinearMap.exact_iff.mp he, LinearMap.finrank_range_of_inj hf] at h
  omega

/-- The scalar multiplication ideal in the principal-section exact sequence. -/
lemma smul_span_singleton_eq {R : Type*} [CommRing R] (a b : R) :
    b • (Ideal.span {a} : Ideal R) = Ideal.span {a * b} := by
  have h : (({b} : Set R) • Ideal.span {a}) = Ideal.span {b * a} := by
    simp [← Ideal.submodule_span_eq, Submodule.set_smul_span]
  rw [Submodule.singleton_set_smul, mul_comm b a] at h
  exact h

/-- Finite dimensionality propagates from the two factors to their product. -/
lemma principal_product_quotient_finite {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (a b : R) (hb : b ≠ 0)
    [Module.Finite K (R ⧸ Ideal.span {a})] [Module.Finite K (R ⧸ Ideal.span {b})] :
    Module.Finite K (R ⧸ Ideal.span {a * b}) := by
  let f := (Ideal.mulQuot b (Ideal.span {a})).restrictScalars K
  let g := (Ideal.quotOfMul b (Ideal.span {a})).restrictScalars K
  have hi : Function.Injective f :=
    Ideal.mulQuot_injective _ (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  have hs : Function.Surjective g := Ideal.quotOfMul_surjective _
  have he : Function.Exact f g := Ideal.exact_mulQuot_quotOfMul _
  have ht : Module.Finite K (R ⧸ b • (Ideal.span {a} : Ideal R)) :=
    Module.Finite.of_exact he hs
  rwa [smul_span_singleton_eq] at ht

/-- The ground-field dimension of a product section is the sum of dimensions. -/
theorem principal_product_quotient_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (a b : R) (hb : b ≠ 0)
    [Module.Finite K (R ⧸ Ideal.span {a})] [Module.Finite K (R ⧸ Ideal.span {b})] :
    Module.finrank K (R ⧸ Ideal.span {a * b}) =
      Module.finrank K (R ⧸ Ideal.span {a}) + Module.finrank K (R ⧸ Ideal.span {b}) := by
  let f := (Ideal.mulQuot b (Ideal.span {a})).restrictScalars K
  let g := (Ideal.quotOfMul b (Ideal.span {a})).restrictScalars K
  have hi : Function.Injective f :=
    Ideal.mulQuot_injective _ (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  have hs : Function.Surjective g := Ideal.quotOfMul_surjective _
  have he : Function.Exact f g := Ideal.exact_mulQuot_quotOfMul _
  have ht := finrank_eq_add_of_exact f g hi hs he
  rwa [smul_span_singleton_eq] at ht

lemma principal_power_quotient_finite {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (a : R) (ha : a ≠ 0)
    [Module.Finite K (R ⧸ Ideal.span {a})] (n : ℕ) :
    Module.Finite K (R ⧸ Ideal.span {a ^ n}) := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    infer_instance
  | succ n ih =>
    let := ih
    rw [pow_succ]
    exact principal_product_quotient_finite (K := K) (a ^ n) a ha

/-- Ground-field section multiplicity scales by the exponent, without assuming
a regular local ring or rationality of any closed point. -/
theorem principal_power_quotient_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (a : R) (ha : a ≠ 0)
    [Module.Finite K (R ⧸ Ideal.span {a})] (n : ℕ) :
    Module.finrank K (R ⧸ Ideal.span {a ^ n}) =
      n * Module.finrank K (R ⧸ Ideal.span {a}) := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    simpa only [Nat.zero_mul] using
      (Module.finrank_zero_of_subsingleton (R := K) (M := R ⧸ (⊤ : Ideal R)))
  | succ n ih =>
    let := principal_power_quotient_finite (K := K) a ha n
    rw [pow_succ, principal_product_quotient_finrank (a ^ n) a ha, ih]
    ring

/-- The square/fourth-power identity forces even dimension of a finite section.
Both constants and the resultant are units in this chart ring. -/
theorem finite_section_even_of_square_unit_eq_fourth {K R : Type*}
    [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a) (hr : IsUnit r)
    (hh : h ≠ 0) (hδ : δ ≠ 0)
    [Module.Finite K (R ⧸ Ideal.span {h})] [Module.Finite K (R ⧸ Ideal.span {δ})]
    (heq : A * h ^ 2 * r = a * δ ^ 4) :
    Even (Module.finrank K (R ⧸ Ideal.span {h})) := by
  have hi : (Ideal.span {h ^ 2} : Ideal R) = Ideal.span {δ ^ 4} := by
    have ht := congrArg (fun x : R => Ideal.span {x}) heq
    simpa only [Ideal.span_singleton_mul_right_unit hr,
      Ideal.span_singleton_mul_left_unit hA, Ideal.span_singleton_mul_left_unit ha] using ht
  have hd := congrArg (fun J : Ideal R => Module.finrank K (R ⧸ J)) hi
  rw [principal_power_quotient_finrank h hh, principal_power_quotient_finrank δ hδ] at hd
  refine ⟨Module.finrank K (R ⧸ Ideal.span {δ}), ?_⟩
  omega

/-- It suffices to know finiteness of the infinity section: the norm section is
a quotient of its square section and therefore automatically finite. -/
theorem finite_infinity_section_even {K R : Type*}
    [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a) (hr : IsUnit r)
    (hh : h ≠ 0) [Module.Finite K (R ⧸ Ideal.span {h})]
    (heq : A * h ^ 2 * r = a * δ ^ 4) :
    Even (Module.finrank K (R ⧸ Ideal.span {h})) := by
  have hδ : δ ≠ 0 := by
    intro hz
    have hn := mul_ne_zero (mul_ne_zero hA.ne_zero (pow_ne_zero 2 hh)) hr.ne_zero
    exact hn (by simpa [hz] using heq)
  have hi : (Ideal.span {h ^ 2} : Ideal R) = Ideal.span {δ ^ 4} := by
    have ht := congrArg (fun x : R => Ideal.span {x}) heq
    simpa only [Ideal.span_singleton_mul_right_unit hr,
      Ideal.span_singleton_mul_left_unit hA, Ideal.span_singleton_mul_left_unit ha] using ht
  have hle : (Ideal.span {h ^ 2} : Ideal R) ≤ Ideal.span {δ} := by
    rw [hi, Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self δ (by decide : 4 ≠ 0)
  let := principal_power_quotient_finite (K := K) h hh 2
  let : Module.Finite K (R ⧸ Ideal.span {δ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ K hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  exact finite_section_even_of_square_unit_eq_fourth hA ha hr hh hδ heq

end
end PierceLengthBound.FixedDividend
