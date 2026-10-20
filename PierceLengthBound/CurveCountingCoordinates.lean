/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.CurveCountingDegreeRange
public import PierceLengthBound.FixedDividendAffineTransport

/-! Transport the counting theorem to arbitrary finite coordinate index types,
including Fin 3 ⊕ Fin 4 for the actual seven-coordinate joint graph. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Renaming coordinates preserves the point count, box and exact Hilbert
function, so the external theorem applies to the actual graph's index type. -/
theorem affine_curve_points_finite_coordinates (σ : Type*) [Fintype σ]
    (lo hi : ℕ) (hn : 2 ≤ Fintype.card σ) (hlo : 0 < lo) (hhi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (MvPolynomial σ ℚ), I.IsPrime →
      ∀ d : ℕ, lo ≤ d → d ≤ hi →
        (∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (σ → ℤ),
        (∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ B) →
        (∀ z ∈ S, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I) →
        (S.card : ℝ) ≤ C * B ^ (1 / (lo : ℝ)) * (Real.log B + 1) := by
  classical
  obtain ⟨C, hC, hcount⟩ := affine_curve_points_degree_range (Fintype.card σ) lo hi hn hlo hhi
  refine ⟨C, hC, ?_⟩
  intro I hI d hdlo hdhi hdegree B hB S hbox hpoints
  let : I.IsPrime := hI
  let e := Fintype.equivFin σ
  let φ := renameEquiv ℚ e
  let J := I.map φ.toRingHom
  have hJ : J.IsPrime := by
    apply Ideal.map_isPrime_of_surjective (f := φ.toRingHom) φ.surjective
    intro f hf
    have he : φ f = 0 := hf
    have hf0 : f = 0 := φ.injective (he.trans (map_zero φ).symm)
    exact hf0 ▸ I.zero_mem
  have hφ (j : σ) : (φ (X j)).totalDegree ≤ 1 := by simp [φ]
  have hφ' (j : Fin (Fintype.card σ)) : (φ.symm (X j)).totalDegree ≤ 1 := by simp [φ]
  have hJdegree := affine_equiv_degree φ hφ hφ' I d hdegree
  let π (z : σ → ℤ) : Fin (Fintype.card σ) → ℤ := fun j => z (e.symm j)
  have hπ : Function.Injective π := by
    intro z w he
    funext j
    have hh := congrFun he (e j)
    simpa only [π, Equiv.symm_apply_apply] using hh
  have hbox' : ∀ z ∈ S.image π, ∀ j, |(z j : ℝ)| ≤ B := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact fun j => hbox z hz (e.symm j)
  have hpoints' : ∀ z ∈ S.image π,
      (fun j => (z j : ℚ)) ∈ coordinateZeroLocus J := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    intro f hf
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ.toRingHom φ.surjective).mp hf
    change eval (fun j => (z (e.symm j) : ℚ)) (rename e g) = 0
    rw [eval_rename]
    have heval : ((fun j => (z (e.symm j) : ℚ)) ∘ e) = (fun j => (z j : ℚ)) := by
      funext j
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [heval]
    exact hpoints z hz g hg
  have hh := hcount J hJ d hdlo hdhi hJdegree B hB (S.image π) hbox' hpoints'
  rwa [Finset.card_image_of_injective S hπ] at hh

end
end PierceLengthBound.FixedDividend
