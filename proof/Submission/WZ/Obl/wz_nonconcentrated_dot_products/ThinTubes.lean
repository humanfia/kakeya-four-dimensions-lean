-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.ThinTubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

/-- Indexed thin tubes, with `c` denoting the fraction of discarded pairs. -/
def IndexedThinTubes {I J : Type*} [Fintype I] [Fintype J]
    (δ σ K c : ℝ) (f : I → Plane) (g : J → Plane) : Prop :=
  ∃ R : I → J → Prop,
    ((Finset.univ.filter (fun p : I × J => ¬R p.1 p.2)).card : ℝ) ≤
      c * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ∧
    ∀ (i : I) (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
      ((Finset.univ.filter (fun j => R i j ∧ |inner ℝ (g j - f i) u| < r)).card : ℝ) ≤
        K * r ^ σ * (Fintype.card J : ℝ)

def SymmetricThinTubes {I J : Type*} [Fintype I] [Fintype J]
    (δ σ K c : ℝ) (f : I → Plane) (g : J → Plane) : Prop :=
  IndexedThinTubes δ σ K c f g ∧ IndexedThinTubes δ σ K c g f

theorem IndexedThinTubes.mono_constant {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ σ K L c : ℝ}
    (h : IndexedThinTubes δ σ K c f g) (hδ : 0 ≤ δ) (hKL : K ≤ L) :
    IndexedThinTubes δ σ L c f g := by
  obtain ⟨R, hbad, hthin⟩ := h
  refine ⟨R, hbad, ?_⟩
  intro i u r hu hr
  exact (hthin i u r hu hr).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg (hδ.trans hr) _)) (Nat.cast_nonneg _))

theorem IndexedThinTubes.mono_error {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ σ K c d : ℝ}
    (h : IndexedThinTubes δ σ K c f g) (hcd : c ≤ d) :
    IndexedThinTubes δ σ K d f g := by
  obtain ⟨R, hbad, hthin⟩ := h
  exact ⟨R, hbad.trans (by gcongr), hthin⟩

/-- Decreasing the exponent preserves thin tubes when the counting constant
is at least one. Large radii use the trivial cardinality bound. -/
theorem IndexedThinTubes.decrease_exponent {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ σ τ K c : ℝ}
    (h : IndexedThinTubes δ σ K c f g) (hδ : 0 < δ) (hK : 1 ≤ K)
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) : IndexedThinTubes δ τ K c f g := by
  obtain ⟨R, hbad, hthin⟩ := h
  refine ⟨R, hbad, ?_⟩
  intro i u r hu hr
  have hrpos : 0 < r := hδ.trans_le hr
  by_cases hr1 : r ≤ 1
  · exact (hthin i u r hu hr).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hrpos hr1 hτσ)
        (zero_le_one.trans hK)) (Nat.cast_nonneg _))
  · have hp : 1 ≤ r ^ τ := Real.one_le_rpow (le_of_not_ge hr1) hτ
    have hfac : 1 ≤ K * r ^ τ := by
      have hh := mul_le_mul hK hp (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ K)
      simpa only [one_mul] using hh
    have hc : ((Finset.univ.filter (fun j => R i j ∧ |inner ℝ (g j - f i) u| < r)).card : ℝ) ≤
        (Fintype.card J : ℝ) := by
      exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset J) _).trans_eq Finset.card_univ
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)])

/-- Increasing the exponent costs the expected power of the base scale. -/
theorem IndexedThinTubes.increase_exponent {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ σ τ K c : ℝ}
    (h : IndexedThinTubes δ σ K c f g) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hστ : σ ≤ τ) : IndexedThinTubes δ τ (δ ^ (σ - τ) * K) c f g := by
  obtain ⟨R, hbad, hthin⟩ := h
  refine ⟨R, hbad, ?_⟩
  intro i u r hu hr
  have hrpos : 0 < r := hδ.trans_le hr
  have hp : r ^ σ ≤ δ ^ (σ - τ) * r ^ τ := by
    calc r ^ σ = r ^ (σ - τ) * r ^ τ := by rw [← Real.rpow_add hrpos]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hδ hr (sub_nonpos.mpr hστ)) (by positivity)
  calc _ ≤ K * r ^ σ * (Fintype.card J : ℝ) := hthin i u r hu hr
    _ ≤ K * (δ ^ (σ - τ) * r ^ τ) * (Fintype.card J : ℝ) := by gcongr
    _ = _ := by ring

theorem SymmetricThinTubes.mono_constant {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ σ K L c : ℝ}
    (h : SymmetricThinTubes δ σ K c f g) (hδ : 0 ≤ δ) (hKL : K ≤ L) :
    SymmetricThinTubes δ σ L c f g :=
  ⟨h.1.mono_constant hδ hKL, h.2.mono_constant hδ hKL⟩

theorem SymmetricThinTubes.mono_error {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ σ K c d : ℝ}
    (h : SymmetricThinTubes δ σ K c f g) (hcd : c ≤ d) :
    SymmetricThinTubes δ σ K d f g := ⟨h.1.mono_error hcd, h.2.mono_error hcd⟩

theorem SymmetricThinTubes.decrease_exponent {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ σ τ K c : ℝ}
    (h : SymmetricThinTubes δ σ K c f g) (hδ : 0 < δ) (hK : 1 ≤ K)
    (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) : SymmetricThinTubes δ τ K c f g :=
  ⟨h.1.decrease_exponent hδ hK hτ hτσ, h.2.decrease_exponent hδ hK hτ hτσ⟩

theorem SymmetricThinTubes.increase_exponent {I J : Type*} [Fintype I] [Fintype J]
    {f : I → Plane} {g : J → Plane} {δ σ τ K c : ℝ}
    (h : SymmetricThinTubes δ σ K c f g) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hστ : σ ≤ τ) : SymmetricThinTubes δ τ (δ ^ (σ - τ) * K) c f g :=
  ⟨h.1.increase_exponent hδ hK hστ, h.2.increase_exponent hδ hK hστ⟩

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
