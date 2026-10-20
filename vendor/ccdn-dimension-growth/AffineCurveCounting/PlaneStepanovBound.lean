module

public import AffineCurveCounting.PlaneFrobeniusSystem

/-! The Stepanov point bound with an explicit finite-dimensional inequality.
The polynomial bases, auxiliary coefficients, formal branches and multiplicity
argument are constructed; only the numerical choice of degrees remains. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Lift a basis of the filtered coordinate ring to bounded-degree polynomials. -/
theorem exists_filtered_polynomial_basis {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (D : ℕ) :
    ∃ h : Fin (Module.finrank K (filteredCoordinateSpace I D)) → MvPolynomial σ K,
      (∀ i, (h i).totalDegree ≤ D) ∧
      LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K I) (h i)) := by
  classical
  let b := Module.finBasis K (filteredCoordinateSpace I D)
  have hlift (i : Fin (Module.finrank K (filteredCoordinateSpace I D))) :
      ∃ h : MvPolynomial σ K, h.totalDegree ≤ D ∧
        (Ideal.Quotient.mkₐ K I) h = (b i).val := by
    obtain ⟨h, hh, he⟩ := Submodule.mem_map.mp (b i).property
    exact ⟨h, (mem_restrictTotalDegree _ _ _).mp hh, he⟩
  choose h hd he using hlift
  refine ⟨h, hd, ?_⟩
  simp only [he]
  exact b.linearIndependent.map' (filteredCoordinateSpace I D).subtype (Submodule.ker_subtype _)

/-- A strict dimension inequality gives the smooth prime-field point count.
There is no supplied auxiliary polynomial or counting theorem in the hypotheses. -/
theorem plane_stepanov_smooth_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) (j : Fin 2)
    (hsmooth : ∀ i, eval (z i) (pderiv j.rev f) ≠ 0)
    {D A N : ℕ} (hD : f.totalDegree * D < p) (hN : N ≤ p)
    (hdim : (∑ r : Fin N, Module.finrank (ZMod p)
      (filteredCoordinateSpace (Ideal.span {f}) (D + A + r.val * f.totalDegree))) <
      Module.finrank (ZMod p) (filteredCoordinateSpace (Ideal.span {f}) D) *
      Module.finrank (ZMod p) (filteredCoordinateSpace (Ideal.span {f}) A)) :
    Fintype.card ι * N ≤ f.totalDegree * (D + p * A) := by
  classical
  obtain ⟨h, hd, hi⟩ := exists_filtered_polynomial_basis (Ideal.span {f}) D
  obtain ⟨b, hb, hbi⟩ := exists_filtered_polynomial_basis (Ideal.span {f}) A
  obtain ⟨a, ha, hne, hdiv⟩ := exists_planeFrobenius_coefficients f j h b hd hb hbi
    (by simpa only [Fintype.card_fin] using hdim)
  exact planeFrobeniusAuxiliary_point_bound p f hf z hz hzero j hsmooth h a hD hN hd ha hi hne hdiv

/-- Include the points where the selected partial derivative vanishes.
Their number is bounded by d(d-1) using the actual proper derivative section. -/
theorem plane_stepanov_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0)
    {D A N : ℕ} (hD : f.totalDegree * D < p) (hN : N ≤ p)
    (hdim : (∑ r : Fin N, Module.finrank (ZMod p)
      (filteredCoordinateSpace (Ideal.span {f}) (D + A + r.val * f.totalDegree))) <
      Module.finrank (ZMod p) (filteredCoordinateSpace (Ideal.span {f}) D) *
      Module.finrank (ZMod p) (filteredCoordinateSpace (Ideal.span {f}) A)) :
    Fintype.card ι * N ≤ f.totalDegree * (D + p * A) +
      f.totalDegree * (f.totalDegree - 1) * N := by
  classical
  obtain ⟨k, hk⟩ := exists_pderiv_ne_zero_of_degree_lt_char f hpos hchar
  let P (i : ι) := eval (z i) (pderiv k f) = 0
  have hgood := plane_stepanov_smooth_bound p f hf
    (fun i : {i // ¬ P i} => z i.val) (hz.comp Subtype.val_injective)
    (fun i => hzero i.val) k.rev (by simpa only [Fin.rev_rev] using fun i : {i // ¬ P i} => i.property)
    hD hN hdim
  have hnd : ¬ f ∣ pderiv k f := by
    rintro ⟨u, hu⟩
    have hun : u ≠ 0 := by intro h; apply hk; simp [hu, h]
    have he := totalDegree_mul_of_isDomain hf.ne_zero hun
    rw [← hu] at he
    have hd := pderiv_totalDegree_le f k
    omega
  have hbad := (plane_common_zeros_card_le f (pderiv k f) hf hnd
    (fun i : {i // P i} => z i.val) (hz.comp Subtype.val_injective)
    (fun i => hzero i.val) (fun i => i.property)).trans
    (Nat.mul_le_mul_left _ (pderiv_totalDegree_le f k))
  have hpartition : Fintype.card {i // P i} + Fintype.card {i // ¬ P i} = Fintype.card ι := by
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le P)
  nlinarith

end
end AffineCurveCounting
