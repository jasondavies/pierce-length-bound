/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib

/-! Clearing rational expressions on a principal neighborhood of a specified
rational point. `RationalNear p f` says that `f = N / D` wherever `D ≠ 0`, for polynomials
with `D(p) ≠ 0`. The predicate is closed under the field operations (inverses and quotients of
functions nonzero at `p`), finite sums and products, determinants, polynomial substitution and
composition. A function nonzero at `p` is nonzero off the zero set of one polynomial that does
not vanish at `p`, so the resulting exceptional polynomial has a concrete nonzero witness. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
noncomputable section

/-- Near `p`, `f` is a quotient `N / D` of polynomials with `D(p) ≠ 0`, valid wherever
`D ≠ 0`. -/
def RationalNear {σ : Type*} (p : σ → ℚ) (f : (σ → ℚ) → ℚ) : Prop :=
  ∃ N D : MvPolynomial σ ℚ, eval p D ≠ 0 ∧
    ∀ x, eval x D ≠ 0 → f x = eval x N / eval x D

namespace RationalNear
variable {σ : Type*} {p : σ → ℚ} {f g : (σ → ℚ) → ℚ}

theorem constant (c : ℚ) : RationalNear p (fun _ => c) :=
  ⟨C c, 1, by simp, by simp⟩

theorem coordinate (j : σ) : RationalNear p (fun x => x j) :=
  ⟨X j, 1, by simp, by simp⟩

theorem add (hf : RationalNear p f) (hg : RationalNear p g) :
    RationalNear p (fun x => f x + g x) := by
  obtain ⟨N, D, hD, hf⟩ := hf
  obtain ⟨M, E, hE, hg⟩ := hg
  refine ⟨N * E + M * D, D * E, by simpa using mul_ne_zero hD hE, ?_⟩
  intro x hx
  have hd := (mul_ne_zero_iff.mp (show eval x D * eval x E ≠ 0 by simpa using hx)).1
  have he := (mul_ne_zero_iff.mp (show eval x D * eval x E ≠ 0 by simpa using hx)).2
  simp only [hf x hd, hg x he, map_add, map_mul]
  simpa only [mul_comm (eval x D)] using div_add_div (eval x N) (eval x M) hd he

theorem neg (hf : RationalNear p f) : RationalNear p (fun x => -f x) := by
  obtain ⟨N, D, hD, hf⟩ := hf
  exact ⟨-N, D, hD, fun x hx => by simp [hf x hx, neg_div]⟩

theorem sub (hf : RationalNear p f) (hg : RationalNear p g) :
    RationalNear p (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : RationalNear p f) (hg : RationalNear p g) :
    RationalNear p (fun x => f x * g x) := by
  obtain ⟨N, D, hD, hf⟩ := hf
  obtain ⟨M, E, hE, hg⟩ := hg
  refine ⟨N * M, D * E, by simpa using mul_ne_zero hD hE, ?_⟩
  intro x hx
  have hd := (mul_ne_zero_iff.mp (show eval x D * eval x E ≠ 0 by simpa using hx)).1
  have he := (mul_ne_zero_iff.mp (show eval x D * eval x E ≠ 0 by simpa using hx)).2
  simp [hf x hd, hg x he, div_mul_div_comm]

theorem inv (hf : RationalNear p f) (hp : f p ≠ 0) :
    RationalNear p (fun x => (f x)⁻¹) := by
  obtain ⟨N, D, hD, hf⟩ := hf
  have hN : eval p N ≠ 0 := by
    intro h
    exact hp (by simp [hf p hD, h])
  refine ⟨D ^ 2, N * D, by simpa using mul_ne_zero hN hD, ?_⟩
  intro x hx
  have hn := (mul_ne_zero_iff.mp (show eval x N * eval x D ≠ 0 by simpa using hx)).1
  have hd := (mul_ne_zero_iff.mp (show eval x N * eval x D ≠ 0 by simpa using hx)).2
  simp only [hf x hd, inv_div, map_mul, map_pow]
  field_simp

theorem div (hf : RationalNear p f) (hg : RationalNear p g) (hp : g p ≠ 0) :
    RationalNear p (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hp)

theorem pow (hf : RationalNear p f) (n : ℕ) :
    RationalNear p (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using constant (p := p) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem sum {ι : Type*} (s : Finset ι) (F : ι → (σ → ℚ) → ℚ)
    (hF : ∀ i ∈ s, RationalNear p (F i)) :
    RationalNear p (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using constant (p := p) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hF i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem prod {ι : Type*} (s : Finset ι) (F : ι → (σ → ℚ) → ℚ)
    (hF : ∀ i ∈ s, RationalNear p (F i)) :
    RationalNear p (fun x => ∏ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using constant (p := p) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hF i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : (σ → ℚ) → Matrix ι ι ℚ)
    (hM : ∀ i j, RationalNear p (fun x => M x i j)) :
    RationalNear p (fun x => (M x).det) := by
  simp only [Matrix.det_apply']
  apply sum
  intro e _
  exact (constant _).mul (prod _ _ (fun i _ => hM _ _))

theorem polynomial {τ : Type*} (F : MvPolynomial τ ℚ)
    (g : (σ → ℚ) → τ → ℚ) (hg : ∀ j, RationalNear p (fun x => g x j)) :
    RationalNear p (fun x => eval (g x) F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simpa using constant (p := p) c
  | add F G hF hG => simpa using hF.add hG
  | mul_X F j hF => simpa using hF.mul (hg j)

/-- Composition with a map `g` that is rational near `p` with `g p = q`. -/
theorem comp {τ : Type*} {q : τ → ℚ} {f : (τ → ℚ) → ℚ}
    (hf : RationalNear q f) (g : (σ → ℚ) → τ → ℚ)
    (hg : ∀ j, RationalNear p (fun x => g x j)) (hp : g p = q) :
    RationalNear p (fun x => f (g x)) := by
  obtain ⟨N, D, hD, hf⟩ := hf
  obtain ⟨M, E, hE, he⟩ := polynomial (p := p) D g hg
  obtain ⟨L, F, hF, hl⟩ := (polynomial (p := p) N g hg).div
    (polynomial (p := p) D g hg) (hp ▸ hD)
  dsimp only at he hl
  refine ⟨L * E * M, F * E * M, ?_, ?_⟩
  · have hM : eval p M ≠ 0 := by
      have h := hp ▸ hD
      rw [he p hE] at h
      exact (div_ne_zero_iff.mp h).1
    simpa using mul_ne_zero (mul_ne_zero hF hE) hM
  · intro x hx
    dsimp only
    have hx' : (eval x F * eval x E) * eval x M ≠ 0 := by simpa using hx
    obtain ⟨hfe, hm⟩ := mul_ne_zero_iff.mp hx'
    obtain ⟨hf', he'⟩ := mul_ne_zero_iff.mp hfe
    have hd : eval (g x) D ≠ 0 := by rw [he x he']; exact div_ne_zero hm he'
    rw [hf _ hd, hl x hf']
    simp only [map_mul]
    field_simp

/-- A rational expression nonzero at the chosen point remains nonzero
outside the zero set of one polynomial that also misses that point. -/
theorem exists_nonvanishing_polynomial (hf : RationalNear p f) (hp : f p ≠ 0) :
    ∃ F : MvPolynomial σ ℚ, eval p F ≠ 0 ∧
      ∀ x, eval x F ≠ 0 → f x ≠ 0 := by
  obtain ⟨N, D, hD, hf⟩ := hf
  have hN : eval p N ≠ 0 := by
    intro h
    exact hp (by simp [hf p hD, h])
  refine ⟨N * D, by simpa using mul_ne_zero hN hD, ?_⟩
  intro x hx
  obtain ⟨hn, hd⟩ := mul_ne_zero_iff.mp (show eval x N * eval x D ≠ 0 by simpa using hx)
  rw [hf x hd]
  exact div_ne_zero hn hd

end RationalNear
end
end PierceLengthBound.FixedDividend
