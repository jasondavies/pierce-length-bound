/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormalizedBranchValuation
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

/-! An infinity fiber of positive vector-space dimension has branches in the normalization.
This ensures that the constructed infinity orders are not merely statements
about a potentially empty family of primes. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

theorem normalization_branch_exists_of_fiber_dimension
    {K S L : Type*} [Field K] [CommRing S] [IsDomain S] [Algebra K S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    (w : S) (hw : w ≠ 0)
    (hpos : 0 < Module.finrank K (S ⧸ Ideal.span {w})) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (integralClosure S L),
      algebraMap S (integralClosure S L) w ∈ p.asIdeal := by
  let C := integralClosure S L
  have hinj : Function.Injective (algebraMap S C) := by
    intro x y hxy
    apply IsFractionRing.injective S L
    rw [IsScalarTower.algebraMap_apply S C L, IsScalarTower.algebraMap_apply S C L, hxy]
  have hproper : (Ideal.span {w} : Ideal S) ≠ ⊤ := by
    intro he
    rw [he, Module.finrank_zero_of_subsingleton] at hpos
    exact lt_irrefl _ hpos
  have hm : (Ideal.span {w}).map (algebraMap S C) ≠ ⊤ := by
    rw [ne_eq, Ideal.map_eq_top_iff _ hinj (fun x => integralClosure.isIntegral x)]
    exact hproper
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hm
  have hwp : algebraMap S C w ∈ p :=
    hle (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton w)))
  have hpb : p ≠ ⊥ := by
    intro he
    rw [he, Ideal.mem_bot] at hwp
    exact hw (hinj (by simpa only [map_zero] using hwp))
  exact ⟨⟨p, hp.isPrime, hpb⟩, hwp⟩

end
end PierceLengthBound.FixedDividend
