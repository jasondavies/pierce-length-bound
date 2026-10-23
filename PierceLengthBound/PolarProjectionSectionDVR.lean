/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendFiniteSectionParity
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Filtration

/-! Local rings with principal maximal ideal. A quadratic relation with unit
linear coefficient makes the section parameter `t` generate the maximal ideal.
A map to power series sending `t` to a series of order one is then injective,
and the order of the image of `f` gives `(f) = 𝔪ⁿ` and the colength of `f`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- If `𝔪 = (t, y)` and `a y² + b y + c = 0` with `b` a unit and `t ∣ c`,
then `𝔪 = (t)`. -/
theorem quadratic_section_maximalIdeal_eq_parameter
    {R : Type*} [CommRing R] [IsLocalRing R]
    (t y a b c : R) (hm : IsLocalRing.maximalIdeal R = Ideal.span {t, y})
    (hb : IsUnit b) (hc : t ∣ c) (hq : a * y ^ 2 + b * y + c = 0) :
    IsLocalRing.maximalIdeal R = Ideal.span {t} := by
  have hy : y ∈ IsLocalRing.maximalIdeal R := by
    rw [hm]
    exact Ideal.subset_span (by simp)
  have hu : IsUnit (a * y + b) := by
    by_contra hnu
    have hu' : a * y + b ∈ IsLocalRing.maximalIdeal R := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hnu
    have hb' : b ∈ IsLocalRing.maximalIdeal R := by
      convert (IsLocalRing.maximalIdeal R).sub_mem hu'
        ((IsLocalRing.maximalIdeal R).mul_mem_left a hy) using 1
      ring
    exact (show ¬ IsUnit b by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hb') hb
  have he : y * (a * y + b) = -c := by linear_combination hq
  have hd : t ∣ y * (a * y + b) := by rw [he]; exact dvd_neg.mpr hc
  rw [hm, Ideal.span_pair_eq_span_left_iff_dvd]
  exact (hu.dvd_mul_right).mp hd

/-- A parameter-preserving map from a Noetherian local ring with principal
maximal ideal into a domain is injective. Applied to a formal section, this
shows that the local quadratic section is a domain. -/
theorem local_principal_parameter_map_injective
    {R S : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] (t : R)
    (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (φ : R →+* S) (hφt : φ t ≠ 0) : Function.Injective φ := by
  classical
  apply (RingHom.injective_iff_ker_eq_bot φ).mpr
  apply le_antisymm _ bot_le
  intro r hr
  change φ r = 0 at hr
  change r = 0
  by_contra hr0
  have hn : ∃ n : ℕ, r ∉ IsLocalRing.maximalIdeal R ^ n := by
    by_contra! h
    have hm : r ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n := Ideal.mem_iInf.mpr h
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hm
    exact hr0 hm
  have hfind : Nat.find hn ≠ 0 := by
    intro hz
    have he := Nat.find_spec hn
    simp only [hz, pow_zero, Ideal.one_eq_top, Submodule.mem_top, not_true_eq_false] at he
  obtain ⟨n, hfind⟩ := Nat.exists_eq_succ_of_ne_zero hfind
  have hnot : r ∉ IsLocalRing.maximalIdeal R ^ (n + 1) := by
    simpa only [hfind] using Nat.find_spec hn
  have hmem : r ∈ IsLocalRing.maximalIdeal R ^ n := by
    apply not_not.mp
    exact Nat.find_min hn (by omega)
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨u, hu⟩ := hmem
  have hunit : IsUnit u := by
    by_contra hnu
    have hum : u ∈ IsLocalRing.maximalIdeal R := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hnu
    have htm : t ^ n ∈ IsLocalRing.maximalIdeal R ^ n := by
      rw [ht, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    apply hnot
    rw [hu, pow_succ]
    exact Ideal.mul_mem_mul htm hum
  have he : φ r ≠ 0 := by
    rw [hu, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero n hφt) (hunit.map φ).ne_zero
  exact he hr

/-- If `φ` sends the parameter `t` to a series of order one and `f` to a
series with first nonzero coefficient in degree `n`, then `(f) = 𝔪ⁿ`. -/
theorem local_section_ideal_power_of_formal_coefficients
    {K R : Type*} [Field K] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (φ : R →+* PowerSeries K) (hφt : (φ t).order = 1)
    (f : R) (n : ℕ)
    (hlower : ∀ j < n, PowerSeries.coeff j (φ f) = 0)
    (hfirst : PowerSeries.coeff n (φ f) ≠ 0) :
    Ideal.span {f} = IsLocalRing.maximalIdeal R ^ n := by
  have hf : f ≠ 0 := by intro he; simp [he] at hfirst
  have hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal := by
    rw [ht]
    infer_instance
  obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_eq_of_principal R hprincipal
    (Ideal.span {f}) (by
      intro hzero
      exact hf (Ideal.span_singleton_eq_bot.mp hzero))
  have ha : Associated f (t ^ m) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    simpa only [ht, Ideal.span_singleton_pow] using hm
  obtain ⟨u, hu⟩ := ha.map φ
  have ho := congrArg PowerSeries.order hu
  have hunit : (u : PowerSeries K).order = 0 :=
    PowerSeries.order_zero_of_isUnit u.isUnit
  have hfOrder : (φ f).order = n := PowerSeries.order_eq_nat.mpr ⟨hfirst, hlower⟩
  simp only [PowerSeries.order_mul, hunit, add_zero, map_pow,
    PowerSeries.order_pow, hφt, hfOrder, nsmul_eq_mul, mul_one] at ho
  have hmn : m = n := by exact_mod_cast ho.symm
  simpa only [hmn] using hm

/-- If `φ` sends the parameter `t` to a series of order one and `f` to a series
of order `n`, then `R/(f)` is finite-dimensional of dimension `n` times the
residue-field degree. -/
theorem local_section_finrank_of_formal_coefficients
    {K R : Type*} [Field K] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Algebra K R] [Module.Finite K (IsLocalRing.ResidueField R)]
    (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (φ : R →+* PowerSeries K) (hφt : (φ t).order = 1)
    (f : R) (n : ℕ)
    (hlower : ∀ j < n, PowerSeries.coeff j (φ f) = 0)
    (hfirst : PowerSeries.coeff n (φ f) ≠ 0) :
    Module.Finite K (R ⧸ Ideal.span {f}) ∧
      Module.finrank K (R ⧸ Ideal.span {f}) =
        n * Module.finrank K (IsLocalRing.ResidueField R) := by
  have ht0 : φ t ≠ 0 := by intro hz; simp [hz] at hφt
  have hφ := local_principal_parameter_map_injective t ht φ ht0
  let : IsDomain R := hφ.isDomain φ
  have htR : t ≠ 0 := by intro hz; exact ht0 (by simp [hz])
  have hideal := local_section_ideal_power_of_formal_coefficients t ht φ hφt f n hlower hfirst
  have hres : Module.Finite K (R ⧸ Ideal.span {t}) := by
    rw [← ht]
    exact inferInstanceAs (Module.Finite K (IsLocalRing.ResidueField R))
  let := hres
  rw [hideal, ht, Ideal.span_singleton_pow]
  refine ⟨principal_power_quotient_finite t htR n, ?_⟩
  rw [principal_power_quotient_finrank t htR n, ← ht]
  rfl

end
end PierceLengthBound.FixedDividend
