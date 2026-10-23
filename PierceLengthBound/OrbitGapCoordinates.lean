/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalOrbit

/-! The three node coordinates distinguish complete gap vectors within a fixed minor pattern,
by the two linear gap identities. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- Within a fixed pattern the node coordinates determine the gap vector: the final two gaps
are recovered from the first three using the positive consecutive minors. -/
theorem kap_eq_of_orbitFreeNodesQ_eq {a b i l : ℕ} (hba : b < a)
    (hi : i + 6 < P a b) (hθ : theta a b i = theta a b l)
    (hz : orbitFreeNodesQ a b i = orbitFreeNodesQ a b l) :
    kap a b i = kap a b l := by
  have hs (j : Fin 3) : sq a b i (j.val + 1) = sq a b l (j.val + 1) := by
    have h := congrFun hz j
    dsimp only [orbitFreeNodesQ] at h
    dsimp only [sq]
    exact_mod_cast h
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two] at hs0 hs1 hs2
  have h0 : kq a b i = kq a b l := by simpa only [sq, kq] using hs0
  have h1 : kq a b (i + 1) = kq a b (l + 1) := by
    dsimp only [sq] at hs0 hs1
    simp only [kq, Nat.add_assoc, Nat.reduceAdd]
    omega
  have h2 : kq a b (i + 2) = kq a b (l + 2) := by
    dsimp only [sq] at hs1 hs2
    simp only [kq, Nat.add_assoc, Nat.reduceAdd]
    omega
  have ht0 := congrFun hθ 0
  have ht1 := congrFun hθ 1
  have ht2 := congrFun hθ 2
  have ht3 := congrFun hθ 3
  have ht4 := congrFun hθ 4
  have ht5 := congrFun hθ 5
  have ht6 := congrFun hθ 6
  simp only [theta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
    at ht0 ht1 ht2 ht3 ht4 ht5 ht6
  have hL0 : Lz a b i ≠ 0 := by have := Lz_pos hba (i := i) (by omega); omega
  have hL1 : Lz a b (i + 1) ≠ 0 := by
    have := Lz_pos hba (i := i + 1) (by omega)
    omega
  have h3 : kq a b (i + 3) = kq a b (l + 3) := by
    have he := e0_at (a := a) (b := b) i
    have he' := e0_at (a := a) (b := b) l
    rw [← ht0, ← ht1, ← ht3, ← ht4, ← h0, ← h1, ← h2] at he'
    apply mul_left_cancel₀ hL0
    linarith
  have h4 : kq a b (i + 4) = kq a b (l + 4) := by
    have he := e0_at (a := a) (b := b) (i + 1)
    have he' := e0_at (a := a) (b := b) (l + 1)
    simp only [Nat.add_assoc, Nat.reduceAdd] at he he'
    rw [← ht1, ← ht2, ← ht5, ← ht6, ← h1, ← h2, ← h3] at he'
    apply mul_left_cancel₀ hL1
    linarith
  funext j
  fin_cases j <;> simpa only [kap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons,
    Matrix.tail_cons] using (by assumption)

/-- Pick one start for each distinct gap vector. The resulting rational node points are
injective, as required by both conic and joint-graph counts. -/
theorem gap_image_representatives {a b i : ℕ} (hba : b < a) (G : Finset ℕ)
    (hmargin : ∀ l ∈ G, l + 6 < P a b)
    (hθ : ∀ l ∈ G, theta a b i = theta a b l) :
    ∃ l : (G.image (kap a b)) → ℕ,
      (∀ j, l j ∈ G) ∧ (∀ j, kap a b (l j) = j.val) ∧
      Function.Injective (fun j => orbitFreeNodesQ a b (l j)) := by
  classical
  have hex (j : G.image (kap a b)) : ∃ l ∈ G, kap a b l = j.val :=
    mem_image.mp j.property
  choose l hl hk using hex
  refine ⟨l, hl, hk, ?_⟩
  intro j k he
  apply Subtype.ext
  rw [← hk j, ← hk k]
  exact kap_eq_of_orbitFreeNodesQ_eq hba (hmargin _ (hl j))
    ((hθ _ (hl j)).symm.trans (hθ _ (hl k))) he

end
end PierceLengthBound.FixedDividend
