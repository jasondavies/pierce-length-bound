module

public import AffineCurveCounting.SingularLocalDeterminant
public import AffineCurveCounting.SmoothPlaneChart
import all ArithmeticHeights.BombieriVaaler

/-! Translation and residue-block assembly for the actual singular local
plane-curve determinant theorem. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def planeTranslate (a : Fin 2 → ℤ) :
    MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℤ :=
  eval₂Hom C (fun j => X j + C (a j))

lemma eval_planeTranslate (a x : Fin 2 → ℤ) (f : MvPolynomial (Fin 2) ℤ) :
    eval x (planeTranslate a f) = eval (fun j => x j + a j) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [planeTranslate]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    rw [map_mul, map_mul, hf, map_mul]
    simp only [planeTranslate, eval₂Hom_X', eval_add, eval_X, eval_C]

/-- Singular local divisibility at an arbitrary integral representative of a
residue point; multiplicity is measured on the translated reduction. -/
theorem singular_plane_chart_det_divisibility {p μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (F : Fin s → MvPolynomial (Fin 2) ℤ)
    (x : Fin s → Fin 2 → ℤ) (a : Fin 2 → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (planeTranslate a f) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (planeTranslate a f)) ≠ 0)
    (hx : ∀ i j, (p : ℤ) ∣ x i j - a j) (hfx : ∀ i, eval (x i) f = 0) :
    (p : ℤ) ^ multiplicityExponent s μ ∣
      (Matrix.of fun i j => eval (x i) (F j)).det := by
  have he (i : Fin s) (u : MvPolynomial (Fin 2) ℤ) :
      eval (fun j => x i j - a j) (planeTranslate a u) = eval (x i) u := by
    rw [eval_planeTranslate]
    simp only [sub_add_cancel]
  have h := singular_plane_pow_dvd_det (planeTranslate a f) hf hμ
    (fun i j => x i j - a j) hx (fun i => by rw [he]; exact hfx i)
    (fun j => planeTranslate a (F j))
  simpa only [he] using h

/-- All maximal minors have the same local multiplicity divisor. -/
theorem singular_plane_chart_minorGcd {p μ s N : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (F : Fin N → MvPolynomial (Fin 2) ℤ)
    (x : Fin s → Fin 2 → ℤ) (a : Fin 2 → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (planeTranslate a f) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (planeTranslate a f)) ≠ 0)
    (hx : ∀ i j, (p : ℤ) ∣ x i j - a j) (hfx : ∀ i, eval (x i) f = 0) :
    (p : ℤ) ^ multiplicityExponent s μ ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (x i) (F j)) := by
  classical
  unfold Int.Matrix.minorGcd
  apply Finset.dvd_gcd
  intro S _
  rw [Matrix.plucker_row_eq_det_submatrix]
  let t := (S : Finset (Fin N)).orderEmbOfFin (Set.powersetCard.card_eq S)
  exact singular_plane_chart_det_divisibility f (fun j => F (t j)) x a hf hμ hx hfx

/-- Summed multiplicity exponents for arbitrary residue blocks, including
singular blocks. Each local hypothesis describes the actual reduced equation. -/
theorem singular_plane_residue_minorGcd {p c s N : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (F : Fin N → MvPolynomial (Fin 2) ℤ)
    (x : Fin s → Fin 2 → ℤ) (label : Fin s → Fin c)
    (a : Fin c → Fin 2 → ℤ) (μ : Fin c → ℕ)
    (hf : ∀ i, map (Int.castRingHom (ZMod p)) (planeTranslate (a i) f) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ i)
    (hμ : ∀ i, homogeneousComponent (μ i)
      (map (Int.castRingHom (ZMod p)) (planeTranslate (a i) f)) ≠ 0)
    (hx : ∀ i j, (p : ℤ) ∣ x i j - a (label i) j) (hfx : ∀ i, eval (x i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, multiplicityExponent
      (Fintype.card {k : Fin s // label k = i}) (μ i)) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (x i) (F j)) := by
  apply residue_prime_powers_dvd_minorGcd _ label
  intro i cols
  apply singular_plane_chart_det_divisibility f (fun j => F (cols j))
    (fun k => x (residueRows label i k)) (a i) (hf i) (hμ i)
  · intro k j
    simpa only [residueRows_label] using hx (residueRows label i k) j
  · intro k
    exact hfx _

end
end AffineCurveCounting
