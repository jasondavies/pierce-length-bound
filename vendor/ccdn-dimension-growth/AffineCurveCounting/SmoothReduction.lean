module

public import AffineCurveCounting.SmoothPlaneChart

/-! Smooth reduction classes of an actual plane equation, and their contribution
to the gcd of maximal evaluation minors. No residue partition is assumed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- Smooth rational points of the reduced plane equation. -/
def SmoothPlaneResidue (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :=
  {a : Fin 2 → ZMod p //
    MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) a f = 0 ∧
    ∃ j, MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) a (MvPolynomial.pderiv j f) ≠ 0}

instance (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [NeZero p] :
    Fintype (SmoothPlaneResidue f p) := by
  classical
  unfold SmoothPlaneResidue
  infer_instance

lemma cast_plane_eval {p : ℕ} (f : MvPolynomial (Fin 2) ℤ) (z : Fin 2 → ℤ) :
    (MvPolynomial.eval z f : ZMod p) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p)) (fun j => (z j : ZMod p)) f := by
  simpa only [MvPolynomial.eval₂_id, RingHom.comp_id, Function.comp_def, Int.coe_castRingHom] using
    MvPolynomial.eval₂_comp_left (Int.castRingHom (ZMod p)) (RingHom.id ℤ) z f

/-- The exponent at a prime is constructed from the actual reduced points.
Its quadratic lower bound depends only on the number of smooth rational points
of the reduced equation. The integral points must all reduce to smooth points. -/
theorem smooth_reduction_minorGcd {s N p : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin N → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ)
    (hf : ∀ i, MvPolynomial.eval (z i) f = 0)
    (hsmooth : ∀ i, ∃ j, (MvPolynomial.eval (z i) (MvPolynomial.pderiv j f) : ZMod p) ≠ 0) :
    ∃ e : ℕ,
      (s : ℝ)^2 / (2 * Fintype.card (SmoothPlaneResidue f p)) - s ≤ e ∧
      (p : ℤ)^e ∣ Int.Matrix.minorGcd (Matrix.of fun i k => MvPolynomial.eval (z i) (g k)) := by
  classical
  let red : Fin s → SmoothPlaneResidue f p := fun i =>
    ⟨(fun k => (z i k : ZMod p)), by rw [← cast_plane_eval, hf i]; simp,
      by simpa only [← cast_plane_eval] using hsmooth i⟩
  let c := Fintype.card (SmoothPlaneResidue f p)
  let E := Fintype.equivFin (SmoothPlaneResidue f p)
  let label : Fin s → Fin c := fun i => E (red i)
  let a : Fin c → Fin 2 → ℤ := fun i k => ((E.symm i).val k).val
  let j : Fin c → Fin 2 := fun i => Classical.choose (E.symm i).property.2
  have ha (i : Fin c) (k : Fin 2) : (a i k : ZMod p) = (E.symm i).val k := by
    simp [a]
  have hunit (i : Fin c) :
      IsCoprime (p : ℤ) (MvPolynomial.eval (a i) (MvPolynomial.pderiv (j i) f)) := by
    apply (ZMod.coe_int_isUnit_iff_isCoprime _ p).mp
    apply isUnit_iff_ne_zero.mpr
    rw [cast_plane_eval]
    simpa only [ha] using Classical.choose_spec (E.symm i).property.2
  have hz (i : Fin s) (k : Fin 2) : (p : ℤ) ∣ z i k - a (label i) k := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Int.cast_sub, ha]
    change (z i k : ZMod p) - (E.symm (E (red i))).val k = 0
    rw [E.symm_apply_apply]
    exact sub_self _
  have hc : 0 < c := Fintype.card_pos_iff.mpr ⟨red ⟨0, hs⟩⟩
  exact ⟨_, smooth_residue_exponent_lower label hc,
    smooth_plane_residue_minorGcd f g z label (p : ℤ) a j hunit hz hf⟩

end
end AffineCurveCounting
