/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionSmoothSectionLocal

/-! Comparing a local curve section to a smooth coordinate section.
Surjectivity is proved through actual localization fractions, so no
unproved invariance of local intersection lengths is required. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

instance algebraPoint_kernel_isPrime {K A : Type*} [Field K]
    [CommRing A] [Algebra K A] (ε : A →ₐ[K] K) :
    (RingHom.ker ε.toRingHom).IsPrime := RingHom.ker_isPrime ε.toRingHom

lemma local_point_isUnit_of_image_ne_zero {K D : Type*} [Field K]
    [CommRing D] [IsLocalRing D] [Algebra K D] (δ : D →ₐ[K] K)
    {d : D} (hd : δ d ≠ 0) : IsUnit d := by
  have hmax : RingHom.ker δ.toRingHom = IsLocalRing.maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective δ.toRingHom
        (fun c => ⟨algebraMap K D c, δ.commutes c⟩))
  by_contra hunit
  apply hd
  change d ∈ RingHom.ker δ.toRingHom
  rw [hmax]
  exact hunit

/-- A coordinate map satisfying the explicit quadratic equation factors
through the smooth section model and preserves its rational origin. -/
theorem smoothSection_factor {K D : Type*} [Field K] [CommRing D] [Algebra K D]
    (a b₀ b₁ c₁ c₂ : K) (η : MvPolynomial (Fin 2) K →ₐ[K] D)
    (hq : η (smoothSectionQuadric a b₀ b₁ c₁ c₂) = 0) (δ : D →ₐ[K] K)
    (hδ : ∀ j : Fin 2, δ (η (MvPolynomial.X j)) = 0) :
    ∃ τ : (MvPolynomial (Fin 2) K ⧸ smoothSectionIdeal a b₀ b₁ c₁ c₂) →ₐ[K] D,
      (∀ f, τ (Ideal.Quotient.mk (smoothSectionIdeal a b₀ b₁ c₁ c₂) f) = η f) ∧
      ∀ x, δ (τ x) = smoothSectionPoint a b₀ b₁ c₁ c₂ x := by
  let I := smoothSectionIdeal a b₀ b₁ c₁ c₂
  let τ : (MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] D := Ideal.Quotient.liftₐ I η (by
    intro f hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
    rw [map_mul, hq, zero_mul])
  refine ⟨τ, fun _ => rfl, ?_⟩
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change δ (η f) = MvPolynomial.eval 0 f
  have he : δ.toRingHom.comp η.toRingHom = MvPolynomial.eval (0 : Fin 2 → K) := by
    ext j
    · simp
    · simpa using hδ j
  exact congrArg (fun h : MvPolynomial (Fin 2) K →+* K => h f) he

/-- A polynomial coordinate change that generates the target local section
extends to a surjection from the corresponding local source. -/
theorem local_coordinate_section_surjection
    {K A S R D σ : Type*} [Field K] [CommRing A] [Algebra K A]
    [CommRing S] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    (ε : A →ₐ[K] K) [IsLocalization.AtPrime S (RingHom.ker ε.toRingHom)]
    (I : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ coordinateZeroLocus I)
    [CommRing R] [Algebra K R] [Algebra (MvPolynomial σ K ⧸ I) R]
    [IsScalarTower K (MvPolynomial σ K ⧸ I) R]
    [IsLocalization.AtPrime R (RingHom.ker (coordinatePoint I z hz).toRingHom)]
    [CommRing D] [IsLocalRing D] [Algebra K D]
    (γ : R →ₐ[K] D) (hγ : Function.Surjective γ) (δ : D →ₐ[K] K)
    (θ : MvPolynomial σ K →ₐ[K] A) (τ : A →ₐ[K] D)
    (hpoint : ∀ f, ε (θ f) = MvPolynomial.eval z f)
    (hτ : ∀ a, δ (τ a) = ε a)
    (hdiagram : ∀ f, τ (θ f) =
      γ (algebraMap (MvPolynomial σ K ⧸ I) R (Ideal.Quotient.mk I f))) :
    ∃ φ : S →ₐ[K] D, Function.Surjective φ ∧
      ∀ a, φ (algebraMap A S a) = τ a := by
  let p := RingHom.ker ε.toRingHom
  let q := RingHom.ker (coordinatePoint I z hz).toRingHom
  let B := MvPolynomial σ K ⧸ I
  have hden : ∀ a : p.primeCompl, IsUnit (τ a) := by
    intro a
    apply local_point_isUnit_of_image_ne_zero δ
    rw [hτ]
    exact a.property
  let φ : S →ₐ[K] D := IsLocalization.liftAlgHom (f := τ) hden
  have hφ (a : A) : φ (algebraMap A S a) = τ a := IsLocalization.lift_eq hden a
  refine ⟨φ, ?_, hφ⟩
  intro d
  obtain ⟨r, rfl⟩ := hγ d
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl r
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (b : B)
  have hbg : ε (θ g) ≠ 0 := by
    rw [hpoint]
    have hb := b.property
    change coordinatePoint I z hz (b : B) ≠ 0 at hb
    rw [← hg] at hb
    simpa only [coordinatePoint_mk] using hb
  let e : p.primeCompl := ⟨θ g, hbg⟩
  refine ⟨IsLocalization.mk' S (θ f) e, ?_⟩
  apply ((IsLocalization.map_units R b).map γ).mul_right_cancel
  calc
    φ (IsLocalization.mk' S (θ f) e) * γ (algebraMap B R b) =
        φ (IsLocalization.mk' S (θ f) e) * τ (θ g) := by rw [hdiagram, hg]
    _ = τ (θ f) := by
      have he := congrArg φ (IsLocalization.mk'_spec S (θ f) e)
      simpa only [map_mul, hφ] using he
    _ = γ (algebraMap B R (Ideal.Quotient.mk I f)) := hdiagram f
    _ = γ (IsLocalization.mk' R (Ideal.Quotient.mk I f) b) * γ (algebraMap B R b) := by
      rw [← map_mul, IsLocalization.mk'_spec]

/-- A surjective local comparison bounds the target's colength by the
source equation's checked colength. -/
theorem local_section_finrank_le_of_surjection {K S D : Type*} [Field K]
    [CommRing S] [CommRing D] [Algebra K S] [Algebra K D]
    (φ : S →ₐ[K] D) (hφ : Function.Surjective φ) (f : S) (hf : φ f = 0)
    [Module.Finite K (S ⧸ Ideal.span {f})] :
    Module.Finite K D ∧ Module.finrank K D ≤ Module.finrank K (S ⧸ Ideal.span {f}) := by
  let ψ : (S ⧸ Ideal.span {f}) →ₐ[K] D := Ideal.Quotient.liftₐ _ φ (by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, hf, zero_mul])
  have hψ : Function.Surjective ψ := by
    intro d
    obtain ⟨s, rfl⟩ := hφ d
    exact ⟨Ideal.Quotient.mk _ s, rfl⟩
  exact ⟨Module.Finite.of_surjective ψ.toLinearMap hψ,
    LinearMap.finrank_le_finrank_of_surjective (f := ψ.toLinearMap) hψ⟩

end
end PierceLengthBound.FixedDividend
