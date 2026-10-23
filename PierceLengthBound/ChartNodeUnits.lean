/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendChartGeneration
public import PierceLengthBound.FixedDividendRationalChartResultant

/-! The resultant unit on the actual infinity section forces every normalized
node difference to be a unit. This works in the possibly nonreduced section. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma map_completeDirection {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ρ u v : R) (z : Fin 3 → R) (j : Fin 5) :
    f (completeDirection ρ u v z j) =
      completeDirection (f ρ) (f u) (f v) (fun k => f (z k)) j := by
  fin_cases j <;> simp [completeDirection, fourthNode]

lemma map_completeNodes {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ρ u v : R) (z : Fin 3 → R) (j : Fin 4) :
    f (completeNodes ρ u v z j) =
      completeNodes (f ρ) (f u) (f v) (fun k => f (z k)) j := by
  fin_cases j <;> simp [completeNodes, fourthNode]

lemma map_nodeVandermonde {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : Fin 4 → R) :
    f (nodeVandermonde z) = nodeVandermonde (fun j => f (z j)) := by
  simp only [nodeVandermonde, map_mul, map_sub]

/-- A unit Vandermonde product makes each pairwise difference a unit. -/
lemma completeDirection_difference_unit {R : Type*} [CommRing R]
    (ρ u v : R) (z : Fin 3 → R)
    (h : IsUnit (nodeVandermonde (completeNodes ρ u v z)))
    (j k : Fin 5) (hjk : j ≠ k) :
    IsUnit (completeDirection ρ u v z j - completeDirection ρ u v z k) := by
  simp only [nodeVandermonde, IsUnit.mul_iff] at h
  fin_cases j <;> fin_cases k <;>
    simp_all only [completeDirection, completeNodes, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk, Fin.isValue, ne_eq,
      not_true_eq_false, zero_sub, sub_zero, IsUnit.neg_iff]
  all_goals first | tauto | apply IsUnit.sub_iff.mp; tauto

/-- Every normalized node difference is invertible modulo the infinity
equation of an actual nonexceptional component. -/
theorem rational_nonexceptional_chart_node_difference_unit
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (j k : Fin 5) (hjk : j ≠ k) :
    let l := Ideal.Quotient.mk I (X 0)
    let R := projectiveChart I ι l
    let z := completeDirection (algebraMap ℚ R ρ) (algebraMap ℚ R u)
      (algebraMap ℚ R v) (chartNode I ι l)
    IsUnit (Ideal.Quotient.mk (chartInfinityIdeal I ι l) (z j - z k)) := by
  dsimp only
  let l := Ideal.Quotient.mk I (X 0)
  let R := projectiveChart I ι l
  let q := Ideal.Quotient.mkₐ ℚ (chartInfinityIdeal I ι l)
  let z := fun j => q (chartNode I ι l j)
  have hres := rational_nonexceptional_chart_resultant_unit hρ hu hv hne
    ρ' u' v' A a ha I hf hg ι hι hd hdegree
  rw [chart_infinity_evaluation, curveResultant_at_infinity] at hres
  simp only [map_mul, aeval_C] at hres
  have hV := (IsUnit.mul_iff.mp hres).2
  have hV' : IsUnit (nodeVandermonde (completeNodes (algebraMap ℚ _ ρ)
      (algebraMap ℚ _ u) (algebraMap ℚ _ v) z)) := by
    change IsUnit ((aeval z).toRingHom
      (nodeVandermonde (completeNodes (C ρ) (C u) (C v) X))) at hV
    rw [map_nodeVandermonde] at hV
    simp_rw [map_completeNodes] at hV
    simpa using hV
  have hh := completeDirection_difference_unit (algebraMap ℚ _ ρ)
    (algebraMap ℚ _ u) (algebraMap ℚ _ v) z hV' j k hjk
  change IsUnit (q.toRingHom (completeDirection (algebraMap ℚ R ρ) (algebraMap ℚ R u)
    (algebraMap ℚ R v) (chartNode I ι l) j -
      completeDirection (algebraMap ℚ R ρ) (algebraMap ℚ R u)
        (algebraMap ℚ R v) (chartNode I ι l) k))
  rw [map_sub, map_completeDirection, map_completeDirection]
  change IsUnit (completeDirection (q (algebraMap ℚ R ρ)) (q (algebraMap ℚ R u))
    (q (algebraMap ℚ R v)) z j - completeDirection (q (algebraMap ℚ R ρ))
      (q (algebraMap ℚ R u)) (q (algebraMap ℚ R v)) z k)
  rw [q.commutes ρ, q.commutes u, q.commutes v]
  exact hh

end
end PierceLengthBound.FixedDividend
