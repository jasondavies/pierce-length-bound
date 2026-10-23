/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionBasePoint
public import PierceLengthBound.ValuationLinearCombination

/-! The polar base ideal and its order on every normalized branch. These
identities do not assume or compute a total base-divisor degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix Finset
noncomputable section

/-- Coordinates related by an invertible matrix generate the same ideal,
over an arbitrary commutative ring. -/
theorem ideal_span_mulVec_eq {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι R) (hG : IsUnit G.det) (x : ι → R) :
    Ideal.span (Set.range (G *ᵥ x)) = Ideal.span (Set.range x) := by
  have hle (M : Matrix ι ι R) (y : ι → R) :
      Ideal.span (Set.range (M *ᵥ y)) ≤ Ideal.span (Set.range y) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change (∑ k, M j k * y k) ∈ _
    exact Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_left _ _ Ideal.mem_span_range_self)
  apply le_antisymm (hle G x)
  have hinv : G⁻¹ *ᵥ (G *ᵥ x) = x := by
    rw [mulVec_mulVec, nonsing_inv_mul G hG, one_mulVec]
  simpa only [hinv] using hle G⁻¹ (G *ᵥ x)

/-- Translating to any common zero removes the affine term of the polar map. -/
theorem polarVector_eq_centered_mulVec {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (x z : Fin 3 → R)
    (hz : polarVector ρ u v ρ' u' v' z = 0) :
    polarVector ρ u v ρ' u' v' x = polarMatrix ρ u v *ᵥ (x - z) := by
  have he : polarMatrix ρ u v *ᵥ z = -polarLinear ρ u v ρ' u' v' :=
    eq_neg_of_add_eq_zero_left hz
  simp only [polarVector, mulVec_sub, he, sub_neg_eq_add]

/-- The three polar forms generate exactly the centered coordinate ideal.
This equality holds in coordinate rings and localizations as well as polynomial rings. -/
theorem polar_baseIdeal_eq {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (hG : IsUnit (polarMatrix ρ u v).det)
    (x z : Fin 3 → R) (hz : polarVector ρ u v ρ' u' v' z = 0) :
    Ideal.span (Set.range (polarVector ρ u v ρ' u' v' x)) =
      Ideal.span (Set.range (x - z)) := by
  rw [polarVector_eq_centered_mulVec ρ u v ρ' u' v' x z hz]
  exact ideal_span_mulVec_eq _ hG _

/-- On the quadric the cubic norm belongs to the polar base ideal. Thus its
order is at least the common order of the polar coordinates on every regular branch. -/
theorem polar_norm_mem_baseIdeal {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (x : Fin 3 → R)
    (hf : lineQuadratic ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) = 0) :
    lineNorm ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) ∈
      Ideal.span (Set.range (polarVector ρ u v ρ' u' v' x)) := by
  have he := polarVector_dot_moment_sub_norm ρ u v ρ' u' v' x
  dsimp only at he
  rw [hf, mul_zero, sub_eq_zero] at he
  rw [← he]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_right _ _ Ideal.mem_span_range_self

/-- A matrix whose entries are regular at a valuation preserves every common
lower bound on the coordinate orders. -/
theorem order_lower_bound_mulVec {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (G : Matrix ι ι L)
    (hG : ∀ j k, 0 ≤ ν (G j k)) (x : ι → L) (n : WithTop ℤ)
    (hx : ∀ j, n ≤ ν (x j)) :
    ∀ j, n ≤ ν ((G *ᵥ x) j) := by
  intro j
  apply ν.map_le_sum
  intro k _
  rw [ν.map_mul]
  simpa only [zero_add] using add_le_add (hG j k) (hx k)

/-- Invertible changes of coordinates regular together with their inverses
preserve all common order bounds, including positive vanishing orders. -/
theorem order_lower_bound_mulVec_iff {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]
    (ν : AddValuation L (WithTop ℤ)) (G : Matrix ι ι L) (hG : IsUnit G.det)
    (hregular : ∀ j k, 0 ≤ ν (G j k)) (hinverse : ∀ j k, 0 ≤ ν (G⁻¹ j k))
    (x : ι → L) (n : WithTop ℤ) :
    (∀ j, n ≤ ν ((G *ᵥ x) j)) ↔ ∀ j, n ≤ ν (x j) := by
  constructor
  · intro h
    have hh := order_lower_bound_mulVec ν G⁻¹ hinverse (G *ᵥ x) n h
    simpa only [mulVec_mulVec, nonsing_inv_mul G hG, one_mulVec] using hh
  · exact order_lower_bound_mulVec ν G hregular x n

/-- The common vanishing order of a finite coordinate family at a branch.
Unlike the pole envelope, this retains positive common orders. -/
def branchCoordinateOrder {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (x : ι → L) : WithTop ℤ :=
  Finset.univ.inf (fun j => ν (x j))

theorem le_branchCoordinateOrder_iff {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (x : ι → L) (n : WithTop ℤ) :
    n ≤ branchCoordinateOrder ν x ↔ ∀ j, n ≤ ν (x j) := by
  simp [branchCoordinateOrder, Finset.le_inf_iff]

/-- The common vanishing order is unchanged by a matrix regular with regular inverse. -/
theorem branchCoordinateOrder_mulVec {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]
    (ν : AddValuation L (WithTop ℤ)) (G : Matrix ι ι L) (hG : IsUnit G.det)
    (hregular : ∀ j k, 0 ≤ ν (G j k)) (hinverse : ∀ j k, 0 ≤ ν (G⁻¹ j k))
    (x : ι → L) :
    branchCoordinateOrder ν (G *ᵥ x) = branchCoordinateOrder ν x := by
  apply eq_of_forall_le_iff
  intro n
  rw [le_branchCoordinateOrder_iff, le_branchCoordinateOrder_iff]
  exact order_lower_bound_mulVec_iff ν G hG hregular hinverse x n

/-- One constant hyperplane simultaneously attains the common order at any
finite family of branches. This includes branches with extended residue fields. -/
theorem exists_section_attaining_common_orders {K L ι κ : Type*}
    [Field K] [Infinite K] [Field L] [Algebra K L] [Fintype ι] [Nonempty ι] [Finite κ]
    (ν : κ → AddValuation L (WithTop ℤ))
    (hK : ∀ k c, 0 ≤ ν k (algebraMap K L c)) (x : ι → L) (hx : ∃ j, x j ≠ 0) :
    ∃ c : ι → K, ∀ k,
      ν k (∑ j, algebraMap K L (c j) * x j) = branchCoordinateOrder (ν k) x := by
  classical
  have hn (k : κ) : ∃ n : ℤ, branchCoordinateOrder (ν k) x = (n : WithTop ℤ) := by
    obtain ⟨j, hj⟩ := hx
    have hlt : branchCoordinateOrder (ν k) x < ⊤ :=
      (Finset.inf_le (Finset.mem_univ j)).trans_lt
        (lt_top_iff_ne_top.mpr ((ν k).ne_top_iff.mpr hj))
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hlt.ne
    exact ⟨n, hn.symm⟩
  choose n hn using hn
  obtain ⟨c, hc⟩ := exists_combination_exact_orders ν hK x n
    (fun k => (le_branchCoordinateOrder_iff (ν k) x _).mp (le_of_eq (hn k).symm))
    (fun k => by
      obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf Finset.univ Finset.univ_nonempty
        (fun j => ν k (x j))
      exact ⟨j, hj.symm.trans (hn k)⟩)
  exact ⟨c, fun k => (hc k).trans (hn k).symm⟩

/-- Dividing a coordinate family by a scalar removes its common zero order
from the scalar's zero order when computing the resulting pole envelope. -/
theorem branchPoleEnvelope_div_of_orders {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (V : ι → L) (D : L) (n m : ℤ)
    (hD : ν D = (m : WithTop ℤ))
    (hlower : ∀ j, (n : WithTop ℤ) ≤ ν (V j))
    (hexact : ∃ j, ν (V j) = (n : WithTop ℤ)) (hnm : n ≤ m) :
    branchPoleEnvelope ν (fun j => V j / D) = (m - n).toNat := by
  have hnat : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (sub_nonneg.mpr hnm)
  have hcast : ((-((m - n).toNat : ℤ)) : WithTop ℤ) =
      (n : WithTop ℤ) - (m : WithTop ℤ) := by
    rw [hnat]
    norm_cast
    ring
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    rw [discretePoleOrder_le_iff, hcast]
    dsimp only
    rw [div_eq_mul_inv, ν.map_mul, ν.map_inv, hD]
    change (n : WithTop ℤ) + -(m : WithTop ℤ) ≤ ν (V j) + -(m : WithTop ℤ)
    exact add_le_add (hlower j) le_rfl
  · obtain ⟨j, hj⟩ := hexact
    have hv : ν (V j / D) = ((n - m : ℤ) : WithTop ℤ) := by
      rw [ν.map_div, hj, hD]
      norm_cast
    have he : discretePoleOrder ν (V j / D) = (m - n).toNat := by
      rw [discretePoleOrder_eq ν hv]
      congr 1
      ring
    rw [← he]
    exact pole_order_le_envelope ν (fun j => V j / D) j

/-- At every branch, the polar forms and the centered gap coordinates have
the same minimum order. No assertion about the sum over branches is needed. -/
theorem polar_base_orders_iff {L : Type*} [Field L]
    (ν : AddValuation L (WithTop ℤ)) (ρ u v ρ' u' v' : L)
    (hG : IsUnit (polarMatrix ρ u v).det)
    (hregular : ∀ j k, 0 ≤ ν (polarMatrix ρ u v j k))
    (hinverse : ∀ j k, 0 ≤ ν ((polarMatrix ρ u v)⁻¹ j k))
    (x z : Fin 3 → L) (hz : polarVector ρ u v ρ' u' v' z = 0)
    (n : WithTop ℤ) :
    (∀ j, n ≤ ν (polarVector ρ u v ρ' u' v' x j)) ↔
      ∀ j, n ≤ ν (x j - z j) := by
  rw [polarVector_eq_centered_mulVec ρ u v ρ' u' v' x z hz]
  exact order_lower_bound_mulVec_iff ν _ hG hregular hinverse (x - z) n

/-- The order of the polar base ideal is the order of the centered coordinate
ideal on each individual normalized branch. -/
theorem polar_base_order_eq {L : Type*} [Field L]
    (ν : AddValuation L (WithTop ℤ)) (ρ u v ρ' u' v' : L)
    (hG : IsUnit (polarMatrix ρ u v).det)
    (hregular : ∀ j k, 0 ≤ ν (polarMatrix ρ u v j k))
    (hinverse : ∀ j k, 0 ≤ ν ((polarMatrix ρ u v)⁻¹ j k))
    (x z : Fin 3 → L) (hz : polarVector ρ u v ρ' u' v' z = 0) :
    branchCoordinateOrder ν (polarVector ρ u v ρ' u' v' x) =
      branchCoordinateOrder ν (x - z) := by
  rw [polarVector_eq_centered_mulVec ρ u v ρ' u' v' x z hz]
  exact branchCoordinateOrder_mulVec ν _ hG hregular hinverse _

end
end PierceLengthBound.FixedDividend
