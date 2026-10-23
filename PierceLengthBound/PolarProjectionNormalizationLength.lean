/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendFiniteSectionParity
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Finite-colength sections are unchanged by an injective extension with
finite-dimensional defect. This is the linear-algebra step in comparing a
singular curve section with its normalization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open LinearMap Submodule

/-- Over a local algebra with finite residue field extension, finite module
length implies finite ground-field dimension. -/
theorem finite_of_finite_length_over_local {K R M : Type*} [Field K]
    [CommRing R] [IsLocalRing R] [Algebra K R]
    [Module.Finite K (IsLocalRing.ResidueField R)]
    [AddCommGroup M] [Module R M] [hKM : Module K M] [IsScalarTower K R M]
    (h : IsFiniteLength R M) : Module.Finite K M := by
  revert hKM
  induction h with
  | of_subsingleton => intros; infer_instance
  | @of_simple_quotient M _ _ N _ _ ih =>
    intro _ _
    let : Module.Finite K N := ih
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
      (inferInstance : IsSimpleModule R (M ⧸ N))
    have hm' : m = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
    subst m
    let : Module.Finite K (R ⧸ IsLocalRing.maximalIdeal R) :=
      inferInstanceAs (Module.Finite K (IsLocalRing.ResidueField R))
    let : Module.Finite K (M ⧸ N) := Module.Finite.equiv (e.restrictScalars K).symm
    exact Module.Finite.of_exact
      (show Function.Exact (N.subtype.restrictScalars K) (N.mkQ.restrictScalars K) from
        fun x => by
          change N.mkQ x = 0 ↔ ∃ y : N, (y : M) = x
          simp) N.mkQ_surjective

/-- Every nonzero section of a one-dimensional Noetherian local domain has
finite ground-field dimension when its residue field does. -/
theorem local_curve_section_finite {K R : Type*} [Field K]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Algebra K R]
    [Module.Finite K (IsLocalRing.ResidueField R)] (a : R) (ha : a ≠ 0) :
    Module.Finite K (R ⧸ Ideal.span {a}) :=
  finite_of_finite_length_over_local
    (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr ha))

/-- Restricting an injective endomorphism to an invariant subspace of finite
codimension preserves its cokernel dimension. Neither ambient space needs to
be finite-dimensional. -/
theorem section_finrank_eq_of_finite_defect {K U V : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (j : U →ₗ[K] V) (hj : Function.Injective j)
    (s : U →ₗ[K] U) (t : V →ₗ[K] V) (ht : Function.Injective t)
    (hcomm : ∀ x, t (j x) = j (s x))
    [Module.Finite K (V ⧸ range j)] [Module.Finite K (U ⧸ range s)] :
    Module.finrank K (V ⧸ range t) = Module.finrank K (U ⧸ range s) := by
  let N := range (j.comp s)
  have hNj : N ≤ range j := by
    rintro _ ⟨x, rfl⟩
    exact ⟨s x, rfl⟩
  have hNt : N ≤ range t := by
    rintro _ ⟨x, rfl⟩
    exact ⟨j x, hcomm x⟩
  let u : (U ⧸ range s) →ₗ[K] (V ⧸ N) := (range s).mapQ N j (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩)
  let v : (V ⧸ N) →ₗ[K] (V ⧸ range j) := N.mapQ (range j) LinearMap.id hNj
  have hu : Function.Injective u := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change N.mkQ (j x) = 0 at hx
      obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, hj hy⟩
  have hv : Function.Surjective v := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact ⟨N.mkQ x, rfl⟩
  have huv : Function.Exact u v := by
    intro x
    constructor
    · induction x using Submodule.Quotient.induction_on with
      | _ x =>
        intro hx
        obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
        exact ⟨(range s).mkQ y, congrArg N.mkQ hy⟩
    · rintro ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y => exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
  let : Module.Finite K (V ⧸ N) := Module.Finite.of_exact huv hv
  have he₁ := finrank_eq_add_of_exact u v hu hv huv
  let p : (V ⧸ range j) →ₗ[K] (V ⧸ N) := (range j).mapQ N t (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, (hcomm x).symm⟩)
  let q : (V ⧸ N) →ₗ[K] (V ⧸ range t) := N.mapQ (range t) LinearMap.id hNt
  have hp : Function.Injective p := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change N.mkQ (t x) = 0 at hx
      obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ⟨y, ht ((hcomm y).trans hy)⟩
  have hq : Function.Surjective q := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact ⟨N.mkQ x, rfl⟩
  have hpq : Function.Exact p q := by
    intro x
    constructor
    · induction x using Submodule.Quotient.induction_on with
      | _ x =>
        intro hx
        obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
        exact ⟨(range j).mkQ y, congrArg N.mkQ hy⟩
    · rintro ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y => exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
  let : Module.Finite K (V ⧸ range t) := Module.Finite.of_surjective q hq
  have he₂ := finrank_eq_add_of_exact p q hp hq hpq
  omega

/-- A nonzero section has the same colength before and after an injective
algebra extension whose additive defect is finite-dimensional. This applies
to a finite birational normalization at an isolated curve singularity. -/
theorem normalization_section_finrank {K R S : Type*} [Field K]
    [CommRing R] [Algebra K R] [CommRing S] [IsDomain S] [Algebra K S]
    (j : R →ₐ[K] S) (hj : Function.Injective j) (a : R) (ha : j a ≠ 0)
    [Module.Finite K (S ⧸ range j.toLinearMap)]
    [Module.Finite K (R ⧸ Ideal.span {a})] :
    Module.finrank K (S ⧸ Ideal.span {j a}) =
      Module.finrank K (R ⧸ Ideal.span {a}) := by
  let s := LinearMap.mul K R a
  let t := LinearMap.mul K S (j a)
  have hs : range s = (Ideal.span {a}).restrictScalars K := Ideal.range_mul R a
  have ht : range t = (Ideal.span {j a}).restrictScalars K := Ideal.range_mul S (j a)
  let : Module.Finite K (R ⧸ range s) := by
    rw [hs]
    exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv K (Ideal.span {a})).symm
  have he := section_finrank_eq_of_finite_defect j.toLinearMap hj s t
    (mul_right_injective₀ ha) (fun x => (j.map_mul a x).symm)
  rw [hs, ht] at he
  simpa only [(Submodule.Quotient.restrictScalarsEquiv K (Ideal.span {a})).finrank_eq,
    (Submodule.Quotient.restrictScalarsEquiv K (Ideal.span {j a})).finrank_eq] using he

/-- A finite intermediate algebra in the fraction field has a nonzero
conductor element: one common denominator clears every element of it. -/
theorem finite_birational_common_denominator {R S L : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field L] [Algebra R L] [IsFractionRing R L] [Algebra S L]
    [IsScalarTower R S L] (hS : Function.Injective (algebraMap S L)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x : S, ∃ r : R, algebraMap R S r = algebraMap R S c * x := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := S)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun i => algebraMap S L (v i))
  refine ⟨c, nonZeroDivisors.ne_zero c.property, ?_⟩
  have hall : ∀ x : S, IsLocalization.IsInteger R ((c : R) • algebraMap S L x) := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hc i
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by simp [map_add, smul_add, hr, hs]⟩
    | smul r x _ hx =>
      obtain ⟨s, hs⟩ := hx
      refine ⟨r * s, ?_⟩
      simp only [map_mul, hs, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply R S L]
      ring
  intro x
  obtain ⟨r, hr⟩ := hall x
  refine ⟨r, hS ?_⟩
  simpa only [map_mul, ← IsScalarTower.algebraMap_apply R S L, Algebra.smul_def] using hr

/-- A finite algebra extension preserves finite-dimensional quotient fibers. -/
theorem finite_algebra_quotient {K R S : Type*} [Field K]
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [Algebra R S]
    [IsScalarTower K R S] [Module.Finite R S]
    (I : Ideal R) [Module.Finite K (R ⧸ I)] :
    Module.Finite K (S ⧸ I.map (algebraMap R S)) := by
  let J := I.map (algebraMap R S)
  let : Module.Finite (R ⧸ I) (S ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) (S ⧸ J)
  let : IsScalarTower K (R ⧸ I) (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun x => by
    change Ideal.Quotient.mk J (algebraMap K S x) =
      Ideal.Quotient.mk J (algebraMap R S (algebraMap K R x))
    rw [← IsScalarTower.algebraMap_apply K R S])
  exact Module.Finite.trans (R ⧸ I) (S ⧸ J)

/-- A finite extension with a conductor has finite ground-field defect when
the conductor section of the original ring is finite-dimensional. -/
theorem finite_defect_of_conductor {K R S : Type*} [Field K]
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [Algebra R S]
    [IsScalarTower K R S] [Module.Finite R S]
    (c : R) (hc : ∀ x : S, ∃ r : R, algebraMap R S r = algebraMap R S c * x)
    [Module.Finite K (R ⧸ Ideal.span {c})] :
    Module.Finite K (S ⧸ range (IsScalarTower.toAlgHom K R S).toLinearMap) := by
  let I : Ideal R := Ideal.span {c}
  let J : Ideal S := I.map (algebraMap R S)
  let N := range (IsScalarTower.toAlgHom K R S).toLinearMap
  let : Module.Finite K (S ⧸ J) := finite_algebra_quotient I
  let : Module.Finite K (S ⧸ J.restrictScalars K) :=
    Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv K J).symm
  have hJN : J.restrictScalars K ≤ N := by
    intro x hx
    have hx' : x ∈ Ideal.span {algebraMap R S c} := by simpa [J, I, Ideal.map_span] using hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx'
    exact hc y
  exact Module.Finite.of_surjective
    (Submodule.factor hJN) (Submodule.factor_surjective hJN)

/-- In a finite birational extension, every finite nonzero section keeps its
ground-field dimension. Finiteness of nonzero sections of the original
curve ring supplies the finite-dimensional normalization defect. -/
theorem finite_birational_section_finrank {K R S L : Type*} [Field K]
    [CommRing R] [IsDomain R] [Algebra K R]
    [CommRing S] [IsDomain S] [Algebra K S] [Algebra R S]
    [IsScalarTower K R S] [Module.Finite R S]
    [Field L] [Algebra R L] [IsFractionRing R L]
    [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]
    (hfinite : ∀ c : R, c ≠ 0 → Module.Finite K (R ⧸ Ideal.span {c}))
    (a : R) (ha : a ≠ 0) :
    Module.finrank K (S ⧸ Ideal.span {algebraMap R S a}) =
      Module.finrank K (R ⧸ Ideal.span {a}) := by
  have hj : Function.Injective (algebraMap R S) :=
    fun x y h => IsFractionRing.injective R L (by
      rw [IsScalarTower.algebraMap_apply R S L x,
        IsScalarTower.algebraMap_apply R S L y, h])
  obtain ⟨c, hc, hclear⟩ := finite_birational_common_denominator
    (R := R) (S := S) (L := L) (IsFractionRing.injective S L)
  let := hfinite c hc
  let := finite_defect_of_conductor (K := K) c hclear
  let := hfinite a ha
  exact normalization_section_finrank (IsScalarTower.toAlgHom K R S) hj a
    (by change algebraMap R S a ≠ 0; simpa only [map_zero] using hj.ne ha)

/-- Normalization preserves the colength of every nonzero section of a
one-dimensional Noetherian local domain with finite residue extension. -/
theorem local_normalization_section_finrank {K R S L : Type*} [Field K]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Algebra K R]
    [Module.Finite K (IsLocalRing.ResidueField R)]
    [CommRing S] [IsDomain S] [Algebra K S] [Algebra R S]
    [IsScalarTower K R S] [Module.Finite R S]
    [Field L] [Algebra R L] [IsFractionRing R L]
    [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]
    (a : R) (ha : a ≠ 0) :
    Module.finrank K (S ⧸ Ideal.span {algebraMap R S a}) =
      Module.finrank K (R ⧸ Ideal.span {a}) :=
  finite_birational_section_finrank (L := L) local_curve_section_finite a ha

end
end PierceLengthBound.FixedDividend
