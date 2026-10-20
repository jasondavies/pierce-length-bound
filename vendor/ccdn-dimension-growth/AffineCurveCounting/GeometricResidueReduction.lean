module

public import AffineCurveCounting.PlaneCurveAssembly

/-! Reduce sharp finite-field counting to geometrically irreducible equations.
The nongeometric case is already bounded by the unconditional d² theorem. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The sharp point estimate needed on geometrically irreducible finite-field
plane equations. `SharpPlaneCount` proves the stronger estimate for every irreducible equation. -/
def SharpGeometricPlaneResidueBound (C : ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ f : MvPolynomial (Fin 2) (ZMod p),
    Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f) →
    27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) →
    (Nat.card {x : Fin 2 → ZMod p // eval x f = 0} : ℝ) ≤
      p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p

lemma finite_field_nonabsolute_zeros_le {k K : Type*}
    [Field k] [Fintype k] [Field K] [Algebra k K]
    (f : MvPolynomial (Fin 2) k) (hf : Irreducible f)
    (hred : ¬ Irreducible (MvPolynomial.map (algebraMap k K) f)) :
    Nat.card {x : Fin 2 → k // eval x f = 0} ≤ f.totalDegree ^ 2 := by
  classical
  let S := {x : Fin 2 → k // eval x f = 0}
  have hd := totalDegree_pos_of_nonzero_nonunit f hf.ne_zero hf.not_isUnit
  have hh := nonabsolute_plane_points_card_le f hf hd hred
    (fun x : S => x.val) Subtype.val_injective (fun x => x.property)
  simpa only [Nat.card_eq_fintype_card] using hh

lemma planeResidue_card_eq_zero_card (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Nat.card (PlaneResidue f p) =
      Nat.card {x : Fin 2 → ZMod p // eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  simp only [eval_map]

/-- Reduction of the sharp residue input to geometric equations;
reducible-over-the-closure curves cost at most d². -/
theorem sharpPlaneResidueBound_of_geometric {C : ℝ} (hC : 0 ≤ C)
    (hgeom : SharpGeometricPlaneResidueBound C) : SharpPlaneResidueBound C := by
  intro f hd p hp hsize hir
  let : Fact p.Prime := ⟨hp⟩
  let q := MvPolynomial.map (Int.castRingHom (ZMod p)) f
  have hqd : q.totalDegree ≤ f.totalDegree := by
    unfold totalDegree
    exact Finset.sup_mono (support_map_subset _ _)
  rw [planeResidue_card_eq_zero_card]
  by_cases hq : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) q)
  · have hs : 27 * (q.totalDegree : ℝ) ^ 4 < (p : ℝ) := by
      apply lt_of_le_of_lt _ hsize
      gcongr
    have hh := hgeom p q hq hs
    apply hh.trans
    gcongr
  · have hh := finite_field_nonabsolute_zeros_le q hir hq
    have ht : (Nat.card {x : Fin 2 → ZMod p // eval x q = 0} : ℝ) ≤ (q.totalDegree : ℝ) ^ 2 := by
      exact_mod_cast hh
    have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
    have hpow : (f.totalDegree : ℝ) ^ 2 ≤ (f.totalDegree : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((f.totalDegree : ℝ) ^ 2 - 1)]
    have hsq : (q.totalDegree : ℝ) ^ 2 ≤ (f.totalDegree : ℝ) ^ 2 := by gcongr
    have htail : 0 ≤ C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p := by positivity
    dsimp [q] at ht
    nlinarith

/-- The full rational plane target now reduces to sharp counting only for
geometrically irreducible finite-field curves. -/
theorem planeCurveBound_of_geometric_residue_bound {C : ℝ} (hC : 0 ≤ C)
    (hgeom : SharpGeometricPlaneResidueBound C) : PlaneCurveBound :=
  planeCurveBound_of_sharp_residue_bound hC (sharpPlaneResidueBound_of_geometric hC hgeom)

end
end AffineCurveCounting
