/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionSectionDVR
public import PierceLengthBound.PolarProjectionLocalCenter

/-! The local ring of the quadratic hyperplane section through the polar
base point. Its parameter and formal embedding are constructed explicitly. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
noncomputable section

/-- The centered quadric restricted to a hyperplane through the origin. -/
def smoothSectionQuadric {K : Type*} [CommRing K] (a b₀ b₁ c₁ c₂ : K) :
    MvPolynomial (Fin 2) K :=
  C a * X 1 ^ 2 + (C b₀ + C b₁ * X 0) * X 1 + C c₁ * X 0 + C c₂ * X 0 ^ 2

def smoothSectionIdeal {K : Type*} [CommRing K] (a b₀ b₁ c₁ c₂ : K) :
    Ideal (MvPolynomial (Fin 2) K) := Ideal.span {smoothSectionQuadric a b₀ b₁ c₁ c₂}

lemma smoothSection_origin {K : Type*} [Field K] (a b₀ b₁ c₁ c₂ : K) :
    (0 : Fin 2 → K) ∈ coordinateZeroLocus (smoothSectionIdeal a b₀ b₁ c₁ c₂) := by
  intro f hf
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
  simp [smoothSectionQuadric]

/-- The rational origin on the section curve. -/
def smoothSectionPoint {K : Type*} [Field K] (a b₀ b₁ c₁ c₂ : K) :
    (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) →ₐ[K] K :=
  coordinatePoint _ 0 (smoothSection_origin a b₀ b₁ c₁ c₂)

def smoothSectionBaseIdeal {K : Type*} [Field K] (a b₀ b₁ c₁ c₂ : K) :
    Ideal (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) :=
  RingHom.ker (smoothSectionPoint a b₀ b₁ c₁ c₂).toRingHom

instance smoothSectionBaseIdeal_isMaximal {K : Type*} [Field K] (a b₀ b₁ c₁ c₂ : K) :
    (smoothSectionBaseIdeal a b₀ b₁ c₁ c₂).IsMaximal :=
  coordinatePoint_kernel_isMaximal _ 0 (smoothSection_origin a b₀ b₁ c₁ c₂)

/-- Evaluation on a formal root extends to the local ring at the origin. -/
theorem smoothSection_local_formal_map {K R : Type*} [Field K]
    (a b₀ b₁ c₁ c₂ : K) [CommRing R]
    [Algebra (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) R]
    [IsLocalization.AtPrime R (smoothSectionBaseIdeal a b₀ b₁ c₁ c₂)]
    (y : PowerSeries K) (hy0 : PowerSeries.constantCoeff y = 0)
    (hy : PowerSeries.C a * y ^ 2 +
      (PowerSeries.C b₀ + PowerSeries.C b₁ * PowerSeries.X) * y +
        PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2 = 0) :
    ∃ φ : R →+* PowerSeries K,
      ∀ f : MvPolynomial (Fin 2) K,
        φ (algebraMap _ R (Ideal.Quotient.mk (smoothSectionIdeal a b₀ b₁ c₁ c₂) f)) =
          eval₂Hom PowerSeries.C ![PowerSeries.X, y] f := by
  let I := smoothSectionIdeal a b₀ b₁ c₁ c₂
  let A := MvPolynomial (Fin 2) K ⧸ I
  let p := smoothSectionBaseIdeal a b₀ b₁ c₁ c₂
  let e := eval₂Hom PowerSeries.C ![PowerSeries.X, y]
  have he : ∀ f ∈ I, e f = 0 := by
    intro f hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
    have hq : e (smoothSectionQuadric a b₀ b₁ c₁ c₂) = 0 := by
      simpa [e, smoothSectionQuadric] using hy
    rw [map_mul, hq, zero_mul]
  let g : A →+* PowerSeries K := Ideal.Quotient.lift I e he
  have hpoint : ∀ z : A, PowerSeries.constantCoeff (g z) =
      smoothSectionPoint a b₀ b₁ c₁ c₂ z := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    change PowerSeries.constantCoeff (e f) = eval 0 f
    have hc : (PowerSeries.constantCoeff (R := K)).comp e = eval (0 : Fin 2 → K) := by
      ext j
      · simp [e]
      · fin_cases j <;> simp [e, hy0]
    exact congrArg (fun h : MvPolynomial (Fin 2) K →+* K => h f) hc
  have hg : ∀ z : p.primeCompl, IsUnit (g z) := by
    intro z
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    rw [hpoint]
    exact z.property
  refine ⟨IsLocalization.lift (S := R) hg, ?_⟩
  intro f
  rw [IsLocalization.lift_eq]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The quotient and localization use definitionally equal nested algebra carriers.
/-- The first coordinate generates the maximal ideal of the actual local
quadratic section whenever its second-coordinate derivative is nonzero. -/
theorem smoothSection_local_parameter {K R : Type*} [Field K]
    (a b₀ b₁ c₁ c₂ : K) (hb₀ : b₀ ≠ 0) [CommRing R] [IsLocalRing R]
    [Algebra (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) R]
    [IsLocalization.AtPrime R (smoothSectionBaseIdeal a b₀ b₁ c₁ c₂)] :
    let ψ := (algebraMap (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) R).comp
      (Ideal.Quotient.mk (smoothSectionIdeal a b₀ b₁ c₁ c₂))
    IsLocalRing.maximalIdeal R = Ideal.span {ψ (X 0)} := by
  let I := smoothSectionIdeal a b₀ b₁ c₁ c₂
  let A := MvPolynomial (Fin 2) K ⧸ I
  let p := smoothSectionBaseIdeal a b₀ b₁ c₁ c₂
  let ψ := (algebraMap A R).comp (Ideal.Quotient.mk I)
  have hp : p = Ideal.span (Set.range (fun j : Fin 2 => Ideal.Quotient.mk I (X j))) := by
    simpa only [p, smoothSectionBaseIdeal, smoothSectionPoint, I,
      Pi.zero_apply, map_zero, sub_zero] using
      coordinatePoint_ker_eq_centered_ideal I 0 (smoothSection_origin a b₀ b₁ c₁ c₂)
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {ψ (X 0), ψ (X 1)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p R, hp, Ideal.map_span,
      ← Set.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [ψ, A, I]
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp hx).symm⟩
  have hb : IsUnit (ψ (C b₀) + ψ (C b₁) * ψ (X 0)) := by
    have hunit : IsUnit (algebraMap A R (Ideal.Quotient.mk I (C b₀ + C b₁ * X 0))) := by
      apply (IsLocalization.AtPrime.isUnit_to_map_iff R p _).mpr
      change smoothSectionPoint a b₀ b₁ c₁ c₂ (Ideal.Quotient.mk I _) ≠ 0
      simpa [smoothSectionPoint, I] using hb₀
    simp only [map_add, map_mul] at hunit
    exact hunit
  have hq : ψ (smoothSectionQuadric a b₀ b₁ c₁ c₂) = 0 := by
    change algebraMap A R (Ideal.Quotient.mk I _) = 0
    have hmem : smoothSectionQuadric a b₀ b₁ c₁ c₂ ∈ I := Ideal.subset_span rfl
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  have he : ψ (C a) * ψ (X 1) ^ 2 +
      (ψ (C b₀) + ψ (C b₁) * ψ (X 0)) * ψ (X 1) +
        (ψ (C c₁) * ψ (X 0) + ψ (C c₂) * ψ (X 0) ^ 2) = 0 := by
    simpa only [smoothSectionQuadric, map_add, map_mul, map_pow, add_assoc] using hq
  exact quadratic_section_maximalIdeal_eq_parameter (ψ (X 0)) (ψ (X 1))
    (ψ (C a)) (ψ (C b₀) + ψ (C b₁) * ψ (X 0))
    (ψ (C c₁) * ψ (X 0) + ψ (C c₂) * ψ (X 0) ^ 2) hm hb
    ⟨ψ (C c₁) + ψ (C c₂) * ψ (X 0), by ring⟩ he

/-- A checked formal initial coefficient determines the colength in the
actual local quadratic section. Its residue field is proved to be the
ground field, and its domain property follows from the formal parameter. -/
theorem smoothSection_local_colength {K R : Type*} [Field K]
    (a b₀ b₁ c₁ c₂ : K) (hb₀ : b₀ ≠ 0)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra K R]
    [Algebra (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) R]
    [IsScalarTower K (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) R]
    [IsLocalization.AtPrime R (smoothSectionBaseIdeal a b₀ b₁ c₁ c₂)]
    (y : PowerSeries K) (hy0 : PowerSeries.constantCoeff y = 0)
    (hy : PowerSeries.C a * y ^ 2 +
      (PowerSeries.C b₀ + PowerSeries.C b₁ * PowerSeries.X) * y +
        PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2 = 0)
    (f : MvPolynomial (Fin 2) K) (n : ℕ)
    (hlower : ∀ j < n, PowerSeries.coeff j (eval₂Hom PowerSeries.C ![PowerSeries.X, y] f) = 0)
    (hfirst : PowerSeries.coeff n (eval₂Hom PowerSeries.C ![PowerSeries.X, y] f) ≠ 0) :
    let ψ := (algebraMap (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) R).comp
      (Ideal.Quotient.mk (smoothSectionIdeal a b₀ b₁ c₁ c₂))
    Module.Finite K (R ⧸ Ideal.span {ψ f}) ∧
      Module.finrank K (R ⧸ Ideal.span {ψ f}) = n := by
  let I := smoothSectionIdeal a b₀ b₁ c₁ c₂
  let A := MvPolynomial (Fin 2) K ⧸ I
  let p := smoothSectionBaseIdeal a b₀ b₁ c₁ c₂
  let ψ := (algebraMap A R).comp (Ideal.Quotient.mk I)
  obtain ⟨φ, hφ⟩ := smoothSection_local_formal_map (R := R) a b₀ b₁ c₁ c₂ y hy0 hy
  have ht : (φ (ψ (X 0))).order = 1 := by
    change (φ (algebraMap A R (Ideal.Quotient.mk I (X 0)))).order = 1
    rw [hφ]
    simp
  have hres : Module.finrank K (IsLocalRing.ResidueField R) = 1 :=
    rational_point_local_residue_finrank (R := R) p (smoothSectionPoint a b₀ b₁ c₁ c₂) rfl
  let : Module.Finite K (IsLocalRing.ResidueField R) :=
    Module.finite_of_finrank_pos (by omega)
  have hφf : φ (ψ f) = eval₂Hom PowerSeries.C ![PowerSeries.X, y] f := hφ f
  have he := local_section_finrank_of_formal_coefficients (ψ (X 0))
    (smoothSection_local_parameter a b₀ b₁ c₁ c₂ hb₀) φ ht (ψ f) n
    (by rw [hφf]; exact hlower) (by rw [hφf]; exact hfirst)
  simpa only [hres, mul_one] using he

end
end PierceLengthBound.FixedDividend
