module

public import AffineCurveCounting.PlaneMultiplicitySmooth
public import AffineCurveCounting.PrimeSums
import all ArithmeticHeights.BombieriVaaler

/-! Global determinant lower bounds including singular reduction classes.
The local divisibility, actual residue partition, multiplicities, and singular
correction are proved. Sharp finite-field point counts and control of the
excluded primes remain explicit inputs. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Finset Real MvPolynomial

lemma irreducible_mvPolynomial_totalDegree_pos {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} (hf : Irreducible f) : 0 < f.totalDegree := by
  by_contra hn
  have hd : f.totalDegree = 0 := by omega
  have he : f = C (f.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : f.coeff 0 ≠ 0 := by
    intro hc
    apply hf.ne_zero
    rw [he, hc, map_zero]
  apply hf.not_isUnit
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- The local exponent can be bounded using the actual reduced point count
and the proved degree-dependent singular correction. -/
theorem singular_reduction_minorGcd_card_bound {s N p : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin N → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ) (hz : ∀ i, eval (z i) f = 0)
    (hf : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hchar : f.totalDegree < p) :
    let m : ℕ := Nat.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1)
    0 < m ∧ ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * m) - s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k)) := by
  dsimp only
  obtain ⟨hM, e, _, he, hdiv⟩ := singular_reduction_minorGcd hs f g z hf.ne_zero hz
  have hbound := planeTotalMultiplicity_le_card_add_correction f hf
    (irreducible_mvPolynomial_totalDegree_pos hf) hchar
  rw [← Nat.card_eq_fintype_card] at hbound
  refine ⟨hM.trans_le hbound, e, ?_, hdiv⟩
  apply le_trans (sub_le_sub_right ?_ (s : ℝ)) he
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbound) (by norm_num)

/-- A global logarithmic determinant estimate with the actual residue-point
count and the explicit singular correction retained in each denominator.
No finite-field point estimate is assumed in this form. -/
theorem singular_determinant_log_lower_exact {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin N → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ) (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hf : ∀ p ∈ P, Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hchar : ∀ p ∈ P, f.totalDegree < p) :
    (s : ℝ) ^ 2 / 2 * (∑ p ∈ P, Real.log p /
      (Nat.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1) : ℕ)) -
      s * (∑ p ∈ P, Real.log p) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  classical
  let D := Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))
  let m : ℕ → ℝ := fun p =>
    (Nat.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1) : ℕ)
  have hlocal (p : ℕ) (hp : p ∈ P) : 0 < m p ∧
      ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * m p) - s ≤ e ∧ (p : ℤ) ^ e ∣ D := by
    let : Fact p.Prime := ⟨hP p hp⟩
    obtain ⟨hm, e, he, hd⟩ := singular_reduction_minorGcd_card_bound hs f g z hz
      (hf p hp) (hchar p hp)
    exact ⟨by dsimp only [m]; exact_mod_cast hm, e, he, hd⟩
  let e : ℕ → ℕ := fun p => if hp : p ∈ P then (hlocal p hp).2.choose else 0
  apply log_lower_of_local_exponents P e m s
    (lt_of_lt_of_le (by norm_num) (Int.Matrix.one_le_minorGcd hrows)) hP
    (fun p hp => (hlocal p hp).1)
  · intro p hp
    rw [show e p = (hlocal p hp).2.choose from dite_eq_left hp]
    exact (hlocal p hp).2.choose_spec.1
  · intro p hp
    rw [show e p = (hlocal p hp).2.choose from dite_eq_left hp]
    exact (hlocal p hp).2.choose_spec.2

/-- The global prime-sum estimate for arbitrary reduction points, including
singular points. The hypothesis bounds the actual finite-field point count;
the singular correction and all local determinant divisibilities are derived.
The displayed degree-dependent error is explicit and is not the final sharp
CCDN dependence on degree. -/
theorem singular_determinant_log_lower {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin N → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ) (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {x C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C) (B : Finset ℕ)
    (hf : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hchar : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, f.totalDegree < p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * Real.sqrt p) :
    (s : ℝ) ^ 2 / 2 * (Real.log x - mertensError -
      (∑ p ∈ B, Real.log p / p) -
      (C + (f.totalDegree ^ 2 * (f.totalDegree - 1) : ℕ)) * primeErrorMass) -
      s * ((Real.log 4 + 4) * x) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  classical
  let S := ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B
  let D := Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))
  let m : ℕ → ℝ := fun p =>
    (Nat.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1) : ℕ)
  let E : ℝ := (f.totalDegree ^ 2 * (f.totalDegree - 1) : ℕ)
  have hp (p : ℕ) (h : p ∈ S) : p.Prime := (mem_filter.mp (mem_sdiff.mp h).1).2
  have hlocal (p : ℕ) (h : p ∈ S) : 0 < m p ∧
      ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * m p) - s ≤ e ∧ (p : ℤ) ^ e ∣ D := by
    let : Fact p.Prime := ⟨hp p h⟩
    obtain ⟨hm, e, he, hd⟩ := singular_reduction_minorGcd_card_bound hs f g z hz
      (hf p h) (hchar p h)
    exact ⟨by dsimp only [m]; exact_mod_cast hm, e, he, hd⟩
  let e : ℕ → ℕ := fun p => if h : p ∈ S then (hlocal p h).2.choose else 0
  have hE : 0 ≤ E := Nat.cast_nonneg _
  apply determinant_log_lower_from_local_bounds hx (add_nonneg hC hE) B m s e
    (D := D) (lt_of_lt_of_le (by norm_num) (Int.Matrix.one_le_minorGcd hrows))
    (fun p h => (hlocal p h).1)
  · intro p h
    have hsqrt : 1 ≤ Real.sqrt (p : ℝ) := by
      exact Real.one_le_sqrt.mpr (by exact_mod_cast (hp p h).one_le)
    change (Nat.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1) : ℕ) ≤
      (p : ℝ) + (C + E) * Real.sqrt p
    rw [Nat.cast_add]
    have hu := hupper p h
    have he := mul_le_mul_of_nonneg_left hsqrt hE
    dsimp only [E] at he ⊢
    nlinarith
  · intro p h
    rw [show e p = (hlocal p h).2.choose from dite_eq_left h]
    exact (hlocal p h).2.choose_spec.1
  · intro p h
    rw [show e p = (hlocal p h).2.choose from dite_eq_left h]
    exact (hlocal p h).2.choose_spec.2

end
end AffineCurveCounting
