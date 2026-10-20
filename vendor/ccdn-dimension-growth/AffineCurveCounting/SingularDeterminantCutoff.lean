module

public import AffineCurveCounting.PrimeCutoff
import all ArithmeticHeights.BombieriVaaler

/-! Fourth-power cutoff removes the polynomial-in-degree error from the
singular determinant prime sum, retaining an explicit logarithmic cutoff cost. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Finset Real MvPolynomial

lemma singular_correction_absorb {d p : ℕ} (hd : 0 < d) {L : ℝ}
    (hdL : (d : ℝ) ^ 4 ≤ L) (hpL : L < (p : ℝ)) :
    ((d ^ 2 * (d - 1) : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt p := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 := by nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  have hs : (d : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (hpow.trans (hdL.trans hpL.le))
  have hsub : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  push_cast
  exact mul_le_mul_of_nonneg_left (hsub.trans hs) (sq_nonneg _)

/-- The singular correction and sharp point-count term have a bounded total
prime-tail contribution above a fourth-power cutoff. Only logarithmic degree
loss remains when L is a constant multiple of d^4. -/
theorem singular_determinant_log_lower_cutoff {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (g : Fin N → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {x L C : ℝ} (hx : 1 ≤ x) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hdL : (f.totalDegree : ℝ) ^ 4 ≤ L) (B : Finset ℕ)
    (hf : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    (s : ℝ) ^ 2 / 2 * (Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ B, Real.log p / p) - 2 * primeBlockMass * (C + 1)) -
      s * ((Real.log 4 + 4) * x) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  classical
  let S := (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B).filter (fun p : ℕ => L < (p : ℝ))
  let D := Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))
  let m : ℕ → ℝ := fun p =>
    (Nat.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1) : ℕ)
  have hp (p : ℕ) (h : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp h).1).1).2
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hd4 : (f.totalDegree : ℝ) ≤ (f.totalDegree : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((f.totalDegree : ℝ) ^ 2 - 1)]
  have hlocal (p : ℕ) (h : p ∈ S) : 0 < m p ∧
      ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * m p) - s ≤ e ∧ (p : ℤ) ^ e ∣ D := by
    let : Fact p.Prime := ⟨hp p h⟩
    have hmem := mem_filter.mp h
    have hchar : f.totalDegree < p := by exact_mod_cast hd4.trans_lt (hdL.trans_lt hmem.2)
    obtain ⟨hm, e, he, hd⟩ := singular_reduction_minorGcd_card_bound hs f g z hz
      (hf p hmem.1 hmem.2) hchar
    exact ⟨by dsimp only [m]; exact_mod_cast hm, e, he, hd⟩
  let e : ℕ → ℕ := fun p => if h : p ∈ S then (hlocal p h).2.choose else 0
  have hglobal := determinant_log_lower_cutoff hx hL
    (show 0 ≤ (C + 1) * (f.totalDegree : ℝ) ^ 2 by positivity) B m s e
    (D := D) (lt_of_lt_of_le (by norm_num) (Int.Matrix.one_le_minorGcd hrows))
    (fun p hp hL => (hlocal p (mem_filter.mpr ⟨hp, hL⟩)).1) ?_ ?_ ?_
  · have hsqrt : (f.totalDegree : ℝ) ^ 2 ≤ Real.sqrt L := by
      apply Real.le_sqrt_of_sq_le
      convert hdL using 1
      ring
    have htail : (C + 1) * (f.totalDegree : ℝ) ^ 2 *
        (2 * primeBlockMass / Real.sqrt L) ≤ 2 * primeBlockMass * (C + 1) := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mpr
      have h := mul_le_mul_of_nonneg_left hsqrt
        (show 0 ≤ 2 * primeBlockMass * (C + 1) from
          mul_nonneg (mul_nonneg (by norm_num) primeBlockMass_pos.le) (by linarith))
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left htail (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity)
    linarith
  · intro p hp hL
    have hcorr := singular_correction_absorb hd hdL hL
    have hcount := hupper p hp hL
    dsimp only [m]
    rw [Nat.cast_add]
    nlinarith
  · intro p hp hL
    have hmem : p ∈ S := mem_filter.mpr ⟨hp, hL⟩
    rw [show e p = (hlocal p hmem).2.choose from dite_eq_left hmem]
    exact (hlocal p hmem).2.choose_spec.1
  · intro p hp hL
    have hmem : p ∈ S := mem_filter.mpr ⟨hp, hL⟩
    rw [show e p = (hlocal p hmem).2.choose from dite_eq_left hmem]
    exact (hlocal p hmem).2.choose_spec.2

/-- The paper's cutoff 27*d^4 leaves precisely a 4*log(d) degree loss,
plus absolute constants and the explicit bad-prime charge. -/
theorem singular_determinant_log_lower_degree_four {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (g : Fin N → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {x C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C) (B : Finset ℕ)
    (hf : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    (s : ℝ) ^ 2 / 2 * (Real.log x - 4 * Real.log f.totalDegree - Real.log 27 -
      2 * mertensError - (∑ p ∈ B, Real.log p / p) - 2 * primeBlockMass * (C + 1)) -
      s * ((Real.log 4 + 4) * x) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hL : 1 ≤ 27 * (f.totalDegree : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hd1 4
    norm_num at h
    linarith
  have h := singular_determinant_log_lower_cutoff hs f hd g z hz hrows hx hL hC
    (show (f.totalDegree : ℝ) ^ 4 ≤ 27 * (f.totalDegree : ℝ) ^ 4 from
      le_mul_of_one_le_left (by positivity) (by norm_num))
    B hf hupper
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1
  ring

def degreeFourDeterminantError (C : ℝ) : ℝ :=
  Real.log 27 + 2 * mertensError + 2 * primeBlockMass * (C + 1) + 2 * (Real.log 4 + 4)

/-- Choosing the prime upper endpoint to equal the row count yields the
plane-case shape of CCDN Proposition 3.2.6, with the geometric point-count and
bad-prime hypotheses still explicit. -/
theorem singular_determinant_log_lower_at_rank {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (g : Fin N → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {C : ℝ} (hC : 0 ≤ C) (B : Finset ℕ)
    (hf : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ B,
      27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hupper : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ B,
      27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log f.totalDegree -
      (∑ p ∈ B, Real.log p / p) - degreeFourDeterminantError C) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  have h := singular_determinant_log_lower_degree_four hs f hd g z hz hrows
    (x := (s : ℝ)) (by exact_mod_cast hs) hC B
    (by simpa only [Nat.floor_natCast] using hf)
    (by simpa only [Nat.floor_natCast] using hupper)
  convert h using 1
  dsimp only [degreeFourDeterminantError]
  ring

end
end AffineCurveCounting
