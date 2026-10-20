module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Power-series independence from distinct initial orders, including the
mixed products underlying the Frobenius nonvanishing step in point counting. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open PowerSeries

/-- A family with distinct initial nonzero coefficient positions is linearly
independent. The proof selects the smallest position with nonzero weight. -/
theorem powerSeries_linearIndependent_of_initial_coefficients
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (f : ι → PowerSeries K) (n : ι → ℕ) (hn : Function.Injective n)
    (hzero : ∀ i j, j < n i → PowerSeries.coeff j (f i) = 0)
    (hne : ∀ i, PowerSeries.coeff (n i) (f i) ≠ 0) : LinearIndependent K f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  by_contra hai
  let S := Finset.univ.filter (fun j => a j ≠ 0)
  have hS : S.Nonempty := ⟨i, by simp [S, hai]⟩
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image n hS
  have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
  have he := congrArg (PowerSeries.coeff (n j)) ha
  simp only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero] at he
  have hsum : ∑ k, a k * PowerSeries.coeff (n j) (f k) =
      a j * PowerSeries.coeff (n j) (f j) := by
    apply Finset.sum_eq_single j
    · intro k _ hkj
      by_cases hak : a k = 0
      · simp [hak]
      · have hk : k ∈ S := by simp [S, hak]
        have hlt : n j < n k := lt_of_le_of_ne (hmin k hk) (fun h => hkj (hn h.symm))
        rw [hzero k (n j) hlt, mul_zero]
    · simp
  rw [hsum] at he
  exact (mul_ne_zero haj (hne j)) he

/-- Distinct finite power-series orders give linear independence. -/
theorem powerSeries_linearIndependent_of_orders
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (f : ι → PowerSeries K) (n : ι → ℕ) (hn : Function.Injective n)
    (horder : ∀ i, (f i).order = n i) : LinearIndependent K f := by
  apply powerSeries_linearIndependent_of_initial_coefficients f n hn
  · intro i j hj
    exact PowerSeries.coeff_of_lt_order j (by rw [horder]; exact_mod_cast hj)
  · intro i
    exact (PowerSeries.order_eq_nat.mp (horder i)).1

lemma mixed_order_injective {ι κ : Type*} (n : ι → ℕ) (m : κ → ℕ) {q : ℕ}
    (hq : 0 < q) (hn : Function.Injective n) (hm : Function.Injective m)
    (hsmall : ∀ i, n i < q) : Function.Injective (fun t : ι × κ => n t.1 + q * m t.2) := by
  intro a b he
  change n a.1 + q * m a.2 = n b.1 + q * m b.2 at he
  have hfirst : n a.1 = n b.1 := by
    have hh := congrArg (fun x => x % q) he
    simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt (hsmall a.1), Nat.mod_eq_of_lt (hsmall b.1)] using hh
  have hsecond : m a.2 = m b.2 := by
    rw [hfirst] at he
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel he)
  exact Prod.ext (hn hfirst) (hm hsecond)

/-- Low-order series times q-th powers of another ordered family are jointly
independent when the low orders are smaller than q. No characteristic
assumption is needed for this noncancellation argument. -/
theorem powerSeries_mixed_powers_independent
    {K ι κ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : ι → PowerSeries K) (g : κ → PowerSeries K) (n : ι → ℕ) (m : κ → ℕ) {q : ℕ}
    (hq : 0 < q) (hn : Function.Injective n) (hm : Function.Injective m)
    (hsmall : ∀ i, n i < q) (hf : ∀ i, (f i).order = n i) (hg : ∀ j, (g j).order = m j) :
    LinearIndependent K (fun t : ι × κ => f t.1 * (g t.2) ^ q) := by
  apply powerSeries_linearIndependent_of_orders _ (fun t => n t.1 + q * m t.2)
    (mixed_order_injective n m hq hn hm hsmall)
  intro t
  rw [PowerSeries.order_mul, PowerSeries.order_pow, hf, hg]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]

end
end AffineCurveCounting
