module

public import AffineCurveCounting.PlaneMultiplicity
public import AffineCurveCounting.SmoothReduction

/-! All reduced points, their actual positive multiplicities, and the resulting
local determinant lower bound. No residue partition or multiplicity choice is
supplied by the caller. The sharp finite-field total-multiplicity estimate is a
separate geometric obligation. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- All affine rational points of the reduced plane equation. -/
def PlaneResidue (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :=
  {a : Fin 2 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) a f = 0}

instance (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [NeZero p] :
    Fintype (PlaneResidue f p) := by
  classical
  unfold PlaneResidue
  infer_instance

def planeResidueLift {f : MvPolynomial (Fin 2) ℤ} {p : ℕ} (a : PlaneResidue f p) :
    Fin 2 → ℤ := fun j => (a.val j).val

lemma cast_planeResidueLift {f : MvPolynomial (Fin 2) ℤ} {p : ℕ} [NeZero p]
    (a : PlaneResidue f p) (j : Fin 2) : (planeResidueLift a j : ZMod p) = a.val j := by
  simp [planeResidueLift]

lemma planeResidueLift_zero {f : MvPolynomial (Fin 2) ℤ} {p : ℕ} [NeZero p]
    (a : PlaneResidue f p) :
    eval₂ (Int.castRingHom (ZMod p)) (fun j => (planeResidueLift a j : ZMod p)) f = 0 := by
  simpa only [cast_planeResidueLift] using a.property

/-- Multiplicity is selected from the actual translated reduced equation. -/
def planeResidueMultiplicity (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [Fact p.Prime]
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0) (a : PlaneResidue f p) : ℕ :=
  Classical.choose (exists_reduction_multiplicity f (planeResidueLift a) hf
    (planeResidueLift_zero a))

theorem planeResidueMultiplicity_spec (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [Fact p.Prime]
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0) (a : PlaneResidue f p) :
    0 < planeResidueMultiplicity f p hf a ∧
      planeResidueMultiplicity f p hf a ≤ f.totalDegree ∧
      map (Int.castRingHom (ZMod p)) (planeTranslate (planeResidueLift a) f) ∈
        idealOfVars (Fin 2) (ZMod p) ^ planeResidueMultiplicity f p hf a ∧
      homogeneousComponent (planeResidueMultiplicity f p hf a)
        (map (Int.castRingHom (ZMod p)) (planeTranslate (planeResidueLift a) f)) ≠ 0 :=
  Classical.choose_spec (exists_reduction_multiplicity f (planeResidueLift a) hf
    (planeResidueLift_zero a))

/-- The actual finite-field total multiplicity appearing in the denominator
of the local determinant exponent. -/
def planeTotalMultiplicity (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [Fact p.Prime]
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0) : ℕ :=
  ∑ a : PlaneResidue f p, planeResidueMultiplicity f p hf a

lemma planeTotalMultiplicity_bounds (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [Fact p.Prime]
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0) :
    Fintype.card (PlaneResidue f p) ≤ planeTotalMultiplicity f p hf ∧
      planeTotalMultiplicity f p hf ≤ Fintype.card (PlaneResidue f p) * f.totalDegree := by
  constructor
  · calc _ = ∑ _a : PlaneResidue f p, 1 := by simp
         _ ≤ _ := Finset.sum_le_sum fun a _ => (planeResidueMultiplicity_spec f p hf a).1
  · calc _ ≤ ∑ _a : PlaneResidue f p, f.totalDegree :=
           Finset.sum_le_sum fun a _ => (planeResidueMultiplicity_spec f p hf a).2.1
         _ = _ := by simp

/-- Actual integral zeros supply all residue labels and multiplicities. The
sum of the local exponents has the full quadratic leading coefficient, with
no smoothness, local factorization, or supplied residue-partition hypothesis. -/
theorem singular_reduction_minorGcd {s N p : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin N → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hz : ∀ i, eval (z i) f = 0) :
    0 < planeTotalMultiplicity f p hf ∧ ∃ e : ℕ,
      s ^ 2 ≤ 2 * planeTotalMultiplicity f p hf * (e + s) ∧
      (s : ℝ) ^ 2 / (2 * planeTotalMultiplicity f p hf) - s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k)) := by
  classical
  let red : Fin s → PlaneResidue f p := fun i =>
    ⟨(fun k => (z i k : ZMod p)), by rw [← cast_plane_eval, hz i]; simp⟩
  let c := Fintype.card (PlaneResidue f p)
  let E := Fintype.equivFin (PlaneResidue f p)
  let label : Fin s → Fin c := fun i => E (red i)
  let a : Fin c → Fin 2 → ℤ := fun i => planeResidueLift (E.symm i)
  let μ : Fin c → ℕ := fun i => planeResidueMultiplicity f p hf (E.symm i)
  let n : Fin c → ℕ := fun i => Fintype.card {k : Fin s // label k = i}
  let e := ∑ i : Fin c, multiplicityExponent (n i) (μ i)
  have hμ (i : Fin c) := planeResidueMultiplicity_spec f p hf (E.symm i)
  have hsum : ∑ i : Fin c, μ i = planeTotalMultiplicity f p hf := by
    exact E.symm.sum_comp (planeResidueMultiplicity f p hf)
  have hsize : ∑ i : Fin c, n i = s := sum_residue_class_sizes label
  have hc : 0 < c := Fintype.card_pos_iff.mpr ⟨red ⟨0, hs⟩⟩
  have hpos : 0 < planeTotalMultiplicity f p hf :=
    hc.trans_le (planeTotalMultiplicity_bounds f p hf).1
  refine ⟨hpos, e, ?_, ?_, ?_⟩
  · simpa only [hsize, hsum] using aggregate_multiplicity_exponents Finset.univ n μ
      (fun i _ => (hμ i).1)
  · have h := aggregate_exponent_lower Finset.univ n μ
      (fun i => multiplicityExponent (n i) (μ i))
      (fun i _ => multiplicityExponent_lower_bound _ _ (hμ i).1)
      (N := (planeTotalMultiplicity f p hf : ℝ)) (by exact_mod_cast hpos)
      (by rw [hsum])
    simpa only [hsize] using h
  · apply singular_plane_residue_minorGcd f g z label a μ
    · intro i
      exact (hμ i).2.2.1
    · intro i
      exact (hμ i).2.2.2
    · intro i j
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      rw [Int.cast_sub, cast_planeResidueLift]
      change (z i j : ZMod p) - (E.symm (E (red i))).val j = 0
      rw [E.symm_apply_apply]
      exact sub_self _
    · exact hz

end
end AffineCurveCounting
