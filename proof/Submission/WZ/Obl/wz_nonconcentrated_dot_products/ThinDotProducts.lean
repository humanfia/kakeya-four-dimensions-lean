-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.ThinDotProducts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.ThinFamily
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.TripleFibers
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PowerBudget

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- A thin-tube relation, whose exceptional fraction is less than the triple
density, gives a lower covering bound for the entire dot-product set. -/
theorem thin_dot_energy_gain {δ K c d γ : ℝ} {F G₁ G₂ : Finset Plane}
    {H : Finset Triple} (R : Plane → Plane → Prop)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hK : 1 ≤ K) (hdc : 0 < d - c)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hF : ClosedFiniteFrostman δ K F)
    (hH : H ⊆ F ×ˢ (G₁ ×ˢ G₂)) (hHne : H.Nonempty)
    (hsep : ∀ b ∈ G₁, ∀ x ∈ G₂, 1 / 4 ≤ ‖b - x‖)
    (hfar : ∀ b ∈ G₁, ∀ x ∈ G₂, ‖b - x‖ ≤ 8)
    (hthin : ∀ b ∈ G₁, ∀ (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
      ((G₂.filter (fun x => R b x ∧ |inner ℝ (x - b) u| < r)).card : ℝ) ≤ K * r * (G₂.card : ℝ))
    (hbad : (((G₁ ×ˢ G₂).filter (fun p => ¬R p.1 p.2)).card : ℝ) ≤
      c * (G₁.card : ℝ) * (G₂.card : ℝ))
    (hdensity : d * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ) ≤ (H.card : ℝ)) :
    ∀ (m : ℕ) (cc : Fin m → ℝ), Covers δ (DotSet (↑H : Set Triple)) cc →
      (d - c) ^ 4 ≤ (2312 * K ^ 2 * energyConstant γ * (4 * δ) ^ γ) * (m : ℝ) := by
  classical
  obtain ⟨p, hp⟩ := hHne
  have hp' := Finset.mem_product.mp (hH hp)
  have hp'' := Finset.mem_product.mp hp'.2
  obtain ⟨b, hb, x, hx, hR, hg⟩ := thin_family_projection_gain F G₁ G₂
    (tripleFiber F H) R hδ hδ1 hK hdc hγ hγ1 hF
    ⟨p.1, hp'.1⟩ ⟨p.2.1, hp''.1⟩ ⟨p.2.2, hp''.2⟩ hsep hfar
    (fun b hb x hx => Finset.filter_subset _ _) hthin hbad
    (by rw [sum_tripleFiber_card_real hH]; exact hdensity)
  intro m cc hcov
  have hg' := hg m cc (hcov.mono_set (tripleFiber_dot_subset F H b x))
  have hmul := mul_le_mul_of_nonneg_right hg' (sq_nonneg (d - c))
  have heq : ((8 * (17 * K / (d - c)) ^ 2 * energyConstant γ * (4 * δ) ^ γ) *
      (m : ℝ)) * (d - c) ^ 2 =
      (2312 * K ^ 2 * energyConstant γ * (4 * δ) ^ γ) * (m : ℝ) := by
    field_simp [hdc.ne']
    <;> ring
  rw [heq] at hmul
  nlinarith only [hmul]

/-- Quantitative thin-tube-to-projection implication, with all fixed constants
absorbed in a small-scale cutoff. No uniformity assumption on triple fibers is needed. -/
theorem thin_dot_projection_count (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (δ K c d : ℝ) (F G₁ G₂ : Finset Plane) (H : Finset Triple)
      (R : Plane → Plane → Prop),
      0 < δ → δ ≤ δ₀ → 1 ≤ K → 0 < d - c → ClosedFiniteFrostman δ K F →
      H ⊆ F ×ˢ (G₁ ×ˢ G₂) → H.Nonempty →
      (∀ b ∈ G₁, ∀ x ∈ G₂, 1 / 4 ≤ ‖b - x‖ ∧ ‖b - x‖ ≤ 8) →
      (∀ b ∈ G₁, ∀ (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
        ((G₂.filter (fun x => R b x ∧ |inner ℝ (x - b) u| < r)).card : ℝ) ≤ K * r * (G₂.card : ℝ)) →
      (((G₁ ×ˢ G₂).filter (fun p => ¬R p.1 p.2)).card : ℝ) ≤
        c * (G₁.card : ℝ) * (G₂.card : ℝ) →
      d * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ) ≤ (H.card : ℝ) →
      ∀ (m : ℕ) (cc : Fin m → ℝ), Covers δ (DotSet (↑H : Set Triple)) cc →
        (d - c) ^ 4 * δ ^ (ε - 1) ≤ K ^ 2 * (m : ℝ) := by
  let γ : ℝ := 1 - min (ε / 2) (1 / 2)
  have hγ : 0 ≤ γ := by dsimp [γ]; linarith [min_le_right (ε / 2) (1 / 2 : ℝ)]
  have hγ1 : γ < 1 := by
    dsimp [γ]
    have hp : 0 < min (ε / 2) (1 / 2 : ℝ) := by positivity
    linarith
  have hslack : 0 < ε + γ - 1 := by dsimp [γ]; linarith [min_le_left (ε / 2) (1 / 2 : ℝ)]
  obtain ⟨δ₁, hδ₁, hδ₁1, hbudget⟩ :=
    exists_monomial_bound (2312 * energyConstant γ * (4 : ℝ) ^ γ)
      (a := ε + γ - 1) (b := 0) hslack
  refine ⟨min δ₁ (1 / 4), by positivity, ?_⟩
  intro δ K c d F G₁ G₂ H R hδ hsmall hK hdc hF hH hHne hsep hthin hbad hdensity m cc hcov
  have hg := thin_dot_energy_gain R hδ (hsmall.trans (min_le_right _ _)) hK hdc hγ hγ1
    hF hH hHne (fun b hb x hx => (hsep b hb x hx).1)
    (fun b hb x hx => (hsep b hb x hx).2) hthin hbad hdensity m cc hcov
  have hb : 2312 * energyConstant γ * (4 : ℝ) ^ γ * δ ^ (ε + γ - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using hbudget δ hδ (hsmall.trans (min_le_left _ _))
  calc (d - c) ^ 4 * δ ^ (ε - 1) ≤
      ((2312 * K ^ 2 * energyConstant γ * (4 * δ) ^ γ) * (m : ℝ)) * δ ^ (ε - 1) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
    _ = (K ^ 2 * (m : ℝ)) * (2312 * energyConstant γ * (4 : ℝ) ^ γ * δ ^ (ε + γ - 1)) := by
        rw [show ε + γ - 1 = γ + (ε - 1) by ring, Real.rpow_add hδ,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hδ.le]
        ring
    _ ≤ (K ^ 2 * (m : ℝ)) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := mul_one _

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
