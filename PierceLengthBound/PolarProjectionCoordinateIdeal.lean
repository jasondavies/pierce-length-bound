/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import PierceLengthBound.PolarProjectionPointSection
public import PierceLengthBound.PolarProjectionGeometry
public import PierceLengthBound.PolarProjectionCuts

/-! The exact polar coordinate ideal in the original cumulative-node
coordinate ring, including the nonzero scalar in the orbit identity. -/
@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix MvPolynomial
noncomputable section

theorem ideal_span_unit_mul {R ι : Type*} [CommRing R]
    (c : R) (hc : IsUnit c) (V : ι → R) :
    Ideal.span (Set.range (fun j => c * V j)) = Ideal.span (Set.range V) := by
  obtain ⟨u, rfl⟩ := hc
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.mul_mem_left _ _ Ideal.mem_span_range_self
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have h := Ideal.mul_mem_left (Ideal.span (Set.range (fun j => (u : R) * V j)))
      (↑u⁻¹ : R) (Ideal.mem_span_range_self (f := fun j => (u : R) * V j) (x := j))
    simpa using h

def independentNodeGaps {R : Type*} [CommRing R] (x : Fin 3 → R) : Fin 3 → R :=
  ![x 0, x 1 - x 0, x 2 - x 1]

theorem ideal_span_independentNodeGaps {R : Type*} [CommRing R] (x : Fin 3 → R) :
    Ideal.span (Set.range (independentNodeGaps x)) = Ideal.span (Set.range x) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact Ideal.mem_span_range_self
    · exact Ideal.sub_mem _ (Ideal.mem_span_range_self (x := 1))
        (Ideal.mem_span_range_self (x := 0))
    · exact Ideal.sub_mem _ (Ideal.mem_span_range_self (x := 2))
        (Ideal.mem_span_range_self (x := 1))
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have h0 := Ideal.mem_span_range_self (f := independentNodeGaps x) (x := 0)
    have h1 := Ideal.mem_span_range_self (f := independentNodeGaps x) (x := 1)
    have h2 := Ideal.mem_span_range_self (f := independentNodeGaps x) (x := 2)
    have hs1 : x 1 ∈ Ideal.span (Set.range (independentNodeGaps x)) := by
      simpa [independentNodeGaps] using Ideal.add_mem _ h1 h0
    fin_cases j
    · exact h0
    · exact hs1
    · simpa [independentNodeGaps] using Ideal.add_mem _ h2 hs1

/-- The polar base point in the original cumulative-node coordinates. -/
def polarCumulativeBasePoint {K : Type*} [Field K] (ρ u v ρ' u' v' : K) : Fin 3 → K :=
  let z := polarBasePoint ρ u v ρ' u' v'
  ![z 0, z 0 + z 1, z 0 + z 1 + z 2]

theorem polar_cumulative_baseIdeal {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (ρ u v ρ' u' v' : K) (hG : (polarMatrix ρ u v).det ≠ 0) (x : Fin 3 → R) :
    Ideal.span (Set.range (polarVector (algebraMap K R ρ) (algebraMap K R u)
      (algebraMap K R v) (algebraMap K R ρ') (algebraMap K R u') (algebraMap K R v')
      (independentNodeGaps x))) =
    Ideal.span (Set.range (fun j => x j -
      algebraMap K R (polarCumulativeBasePoint ρ u v ρ' u' v' j))) := by
  let z := polarBasePoint ρ u v ρ' u' v'
  have hu : IsUnit (polarMatrix (algebraMap K R ρ) (algebraMap K R u)
      (algebraMap K R v)).det := by
    rw [polarMatrix_det]
    have he : (algebraMap K R) ((polarMatrix ρ u v).det) =
        algebraMap K R ρ * (algebraMap K R ρ + algebraMap K R u) *
          (algebraMap K R u - algebraMap K R v) * (algebraMap K R v - 1) := by
      simp [polarMatrix_det]
    rw [← he]
    exact (isUnit_iff_ne_zero.mpr hG).map (algebraMap K R)
  have hz : polarVector (algebraMap K R ρ) (algebraMap K R u) (algebraMap K R v)
      (algebraMap K R ρ') (algebraMap K R u') (algebraMap K R v')
      (fun j => algebraMap K R (z j)) = 0 := by
    rw [← map_polarVector, polarBasePoint_polarVector _ _ _ _ _ _ hG]
    ext j
    exact map_zero _
  rw [polar_baseIdeal_eq _ _ _ _ _ _ hu _ _ hz]
  have hg : independentNodeGaps x - (fun j => algebraMap K R (z j)) =
      independentNodeGaps (fun j => x j -
        algebraMap K R (polarCumulativeBasePoint ρ u v ρ' u' v' j)) := by
    ext j
    fin_cases j <;> simp [independentNodeGaps, polarCumulativeBasePoint, z] <;> ring
  rw [hg, ideal_span_independentNodeGaps]

/-- The scalar-cleared orbit polar forms generate the centered point ideal
in every quotient coordinate ring. -/
theorem orbit_polar_coordinate_ideal (a b i : ℕ)
    (hA : (Lz a b i : ℚ) ≠ 0)
    (hG : (polarMatrix (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)).det ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    Ideal.span (Set.range (fun j : Fin 3 => Ideal.Quotient.mk I
      (C ((Lz a b i : ℚ) ^ 2) * orbitPolarPolynomial a b i j))) =
      Ideal.span (Set.range (fun j => Ideal.Quotient.mk I (X j) -
        algebraMap ℚ (MvPolynomial (Fin 3) ℚ ⧸ I)
          (polarCumulativeBasePoint (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
            (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1)) j))) := by
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  have hC (c : ℚ) : Ideal.Quotient.mk I (C c) = algebraMap ℚ R c := rfl
  have hv : (fun j : Fin 3 => Ideal.Quotient.mk I (orbitPolarPolynomial a b i j)) =
      polarVector (algebraMap ℚ R (patternRhoQ a b i)) (algebraMap ℚ R (patternUQ a b i))
        (algebraMap ℚ R (patternVQ a b i)) (algebraMap ℚ R (patternRhoQ a b (i + 1)))
        (algebraMap ℚ R (patternUQ a b (i + 1))) (algebraMap ℚ R (patternVQ a b (i + 1)))
        (independentNodeGaps (fun j => Ideal.Quotient.mk I (X j))) := by
    ext j
    fin_cases j <;> simp [orbitPolarPolynomial, polarVector, dotProduct,
      Fin.sum_univ_succ, jointGapPolynomials, lineGaps, independentNodeGaps, polarMatrix,
      polarLinear, hC] <;> ring
  simp only [map_mul, hC]
  rw [ideal_span_unit_mul _ ((isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hA)).map
    (algebraMap ℚ R)), hv]
  exact polar_cumulative_baseIdeal _ _ _ _ _ _ hG _

end
end PierceLengthBound.FixedDividend
