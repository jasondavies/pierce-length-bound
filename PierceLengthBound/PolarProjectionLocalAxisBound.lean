/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionAxisColength
public import PierceLengthBound.PolarProjectionComponentSection

/-! The actual local component has a coordinate-axis section of colength at
most four. Every local ring, quotient, residue map, and comparison map used
in the proof is constructed. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Matrix
noncomputable section

/-- Centered gaps in a polynomially presented local coordinate ring. -/
def polarCenteredNodeGaps {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (ψ : MvPolynomial (Fin 3) K →ₐ[K] R) (z : Fin 3 → K) : Fin 3 → R :=
  ![ψ (X 0) - algebraMap K R (z 0), ψ (X 1) - ψ (X 0) - algebraMap K R (z 1),
    ψ (X 2) - ψ (X 1) - algebraMap K R (z 2)]

/-- On every component through the base point outside the fixed exceptional
locus, one of the two centered coordinate gaps cuts out a finite local
section of dimension at most four. -/
theorem polar_local_component_axis_colength_le_four {R : Type*}
    (q : Fin 6 → ℚ) (hguard : polarChartGuard q ≠ 0) (hminor : polarInitialMinor q ≠ 0)
    (A b : ℚ) (hA : A ≠ 0) (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hq : curveQuadratic (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) ∈ I)
    (hg : curveEquation (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) A b ∈ I)
    (hz : (let z := polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
      ![z 0, z 0 + z 1, z 0 + z 1 + z 2]) ∈ coordinateZeroLocus I)
    [CommRing R] [IsLocalRing R] [Algebra ℚ R] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) R]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) R]
    [IsLocalization.AtPrime R (RingHom.ker (coordinatePoint I _ hz).toRingHom)] :
    let ψ := (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) R).comp
      (Ideal.Quotient.mkₐ ℚ I)
    let z := polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
    ∃ j : Fin 3, (j = 1 ∨ j = 2) ∧
      Module.Finite ℚ (R ⧸ Ideal.span {polarCenteredNodeGaps ψ z j}) ∧
      Module.finrank ℚ (R ⧸ Ideal.span {polarCenteredNodeGaps ψ z j}) ≤ 4 := by
  let B := MvPolynomial (Fin 3) ℚ ⧸ I
  let z := polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  let znode : Fin 3 → ℚ := ![z 0, z 0 + z 1, z 0 + z 1 + z 2]
  let p := RingHom.ker (coordinatePoint I znode hz).toRingHom
  let ψ := (IsScalarTower.toAlgHom ℚ B R).comp (Ideal.Quotient.mkₐ ℚ I)
  let gap := polarCenteredNodeGaps ψ z
  have hden : ∀ d : p.primeCompl, IsUnit (coordinatePoint I znode hz d) :=
    fun d => isUnit_iff_ne_zero.mpr d.property
  let ε : R →ₐ[ℚ] ℚ := IsLocalization.liftAlgHom (f := coordinatePoint I znode hz) hden
  have hε (f : MvPolynomial (Fin 3) ℚ) : ε (ψ f) = eval znode f := by
    change ε (algebraMap B R (Ideal.Quotient.mk I f)) = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    exact coordinatePoint_mk I znode hz f
  have hgap0 (k : Fin 3) : ε (gap k) = 0 := by
    fin_cases k <;> simp [gap, polarCenteredNodeGaps, hε, znode]
  obtain ⟨s, t, haxis, hsource⟩ := polar_good_axis_local_colength_four q hguard hminor A b hA
  obtain ⟨j, l, hjl⟩ : ∃ j l : Fin 3,
      (s = 1 ∧ t = 0 ∧ j = 2 ∧ l = 1) ∨ (s = 0 ∧ t = 1 ∧ j = 1 ∧ l = 2) := by
    rcases haxis with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨2, 1, Or.inl ⟨hs, ht, rfl, rfl⟩⟩
    · exact ⟨1, 2, Or.inr ⟨hs, ht, rfl, rfl⟩⟩
  let H : Ideal R := Ideal.span {gap j}
  let D := R ⧸ H
  let γ : R →ₐ[ℚ] D := Ideal.Quotient.mkₐ ℚ H
  let δ : D →ₐ[ℚ] ℚ := Ideal.Quotient.liftₐ H ε (by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, hgap0 j, zero_mul])
  let : Nontrivial D := δ.toRingHom.domain_nontrivial
  let : IsLocalRing D := IsLocalRing.of_surjective' γ.toRingHom (Ideal.Quotient.mk_surjective)
  have hδγ (r : R) : δ (γ r) = ε r := rfl
  have hγh : γ (gap j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let φ₀ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] D := γ.comp ψ
  let η : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] D := aeval ![γ (gap l), γ (gap 0)]
  have hgap (k : Fin 3) : γ (gap k) = polarCenteredNodeGaps φ₀ z k := by
    fin_cases k <;> simp [gap, polarCenteredNodeGaps, φ₀]
  have hη : η.comp (polarSectionMap z s t) = φ₀ := by
    rcases hjl with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · have hfixed : φ₀ (X 2) - φ₀ (X 1) = algebraMap ℚ D (z 2) := by
        rw [hgap] at hγh
        exact sub_eq_zero.mp hγh
      simpa only [η, hgap, polarCenteredNodeGaps, Matrix.cons_val_zero,
        Matrix.cons_val_one] using polar_first_axis_reconstruction z φ₀ hfixed
    · have hfixed : φ₀ (X 1) - φ₀ (X 0) = algebraMap ℚ D (z 1) := by
        rw [hgap] at hγh
        exact sub_eq_zero.mp hγh
      simpa only [η, hgap, polarCenteredNodeGaps, Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
          polar_second_axis_reconstruction z φ₀ hfixed
  have hηpoint (k : Fin 2) : δ (η (X k)) = 0 := by
    fin_cases k <;> simp [η, hδγ, hgap0]
  let S := polarSectionLocalRing (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t
  let : CommRing S := inferInstance
  let f : S := polarSectionLocalEquation (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) A b s t
  have hfin : Module.Finite ℚ (S ⧸ Ideal.span {f}) := hsource.1
  let := hfin
  have hdegree : Module.finrank ℚ (S ⧸ Ideal.span {f}) = 4 := hsource.2
  obtain ⟨_, _, _, hG, _, _⟩ := polarChartGuard_conditions hguard
  obtain ⟨φ, hφ, hkill⟩ := polar_component_section_surjection (R := R) (S := S)
    (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) A b s t hG I hq hg hz γ
    Ideal.Quotient.mk_surjective δ η hηpoint
    (fun p => congrArg (fun θ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] D => θ p) hη)
  have he := local_section_finrank_le_of_surjection φ hφ f hkill
  refine ⟨j, ?_, he.1, he.2.trans_eq hdegree⟩
  rcases hjl with ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

end
end PierceLengthBound.FixedDividend
