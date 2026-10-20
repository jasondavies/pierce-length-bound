module

public import AffineCurveCounting.StepanovRealBound
public import AffineCurveCounting.GeometricResidueReduction

/-! Unconditional sharp finite-field counting and the complete rational-plane
integral-point bound. The finite-field proof uses the constructed Stepanov
auxiliary and retains an explicit absolute error constant. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- An irreducible plane equation over the prime field has at most
p+161*d^2*sqrt(p) rational points when p>27*d^4. -/
theorem plane_finite_field_card_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (hsize : 27 * (f.totalDegree : ℝ) ^ 4 < p)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) :
    (Fintype.card ι : ℝ) ≤ p + 161 * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p := by
  have hd := totalDegree_pos_of_nonzero_nonunit f hf.ne_zero hf.not_isUnit
  have hp : 27 * f.totalDegree ^ 4 < p := by exact_mod_cast hsize
  have hchar : f.totalDegree < p := by
    have h1 := Nat.le_mul_self f.totalDegree
    have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
    nlinarith only [hp, h1, h2]
  obtain ⟨A, D, N, hA, hD, hDp, hNp, hN, hNpos, hx, hy, hpx⟩ :=
    exists_stepanov_integer_parameters f.totalDegree p hd hp
  have hdim := stepanov_hilbert_dimension_inequality f hf.ne_zero p A D N hd hp hA hD hx hy hN hNpos
  have hc := plane_stepanov_bound p f hf hd hchar z hz hzero hDp hNp hdim
  exact stepanov_real_bound f.totalDegree p A D N (Fintype.card ι) hd hp hDp hN hNpos hpx hc

/-- The sharp finite-field hypothesis used by the affine determinant argument
is discharged with the absolute constant 161. -/
theorem sharpPlaneResidueBound : SharpPlaneResidueBound 161 := by
  intro f _hd p hp hsize hir
  let : Fact p.Prime := ⟨hp⟩
  classical
  let q := MvPolynomial.map (Int.castRingHom (ZMod p)) f
  have hqd : q.totalDegree ≤ f.totalDegree := by
    unfold totalDegree
    exact Finset.sup_mono (support_map_subset _ _)
  have hs : 27 * (q.totalDegree : ℝ) ^ 4 < (p : ℝ) := by
    apply lt_of_le_of_lt _ hsize
    gcongr
  let S := {x : Fin 2 → ZMod p // eval x q = 0}
  have hh := plane_finite_field_card_bound p q hir hs (fun x : S => x.val)
    Subtype.val_injective (fun x => x.property)
  rw [planeResidue_card_eq_zero_card, Nat.card_eq_fintype_card]
  apply hh.trans
  gcongr

/-- The full coefficient-uniform rational-plane integral-point bound.
This theorem has no external counting hypothesis. -/
theorem planeCurveBound : PlaneCurveBound :=
  planeCurveBound_of_sharp_residue_bound (by norm_num : (0 : ℝ) ≤ 161) sharpPlaneResidueBound

end
end AffineCurveCounting
