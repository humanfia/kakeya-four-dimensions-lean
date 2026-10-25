-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_kaufman_projection_count.KaufmanCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_kaufman_projection_count.FiberCover
import Submission.WZ.Obl.wz_kaufman_projection_count.WeightedSelection

/- Adapted from this tree’s o103 branch x0272, commit f2e1c96. -/

namespace WangZahlLot.Obl.wz_kaufman_projection_count

open Set Metric
open scoped BigOperators

theorem finite_kaufman_energy_gain {δ C d γ : ℝ} {F Λ : Finset Plane}
    {H : Finset (Plane × Plane)}
    (hF : ClosedFiniteFrostman δ C F) (hΛ : ClosedFiniteFrostman δ C Λ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hd : 0 < d)
    (hunit : ∀ θ ∈ Λ, ‖θ‖ = 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hH : H ⊆ Λ ×ˢ F) (hHne : H.Nonempty)
    (hdensity : d * (Λ.card : ℝ) * (F.card : ℝ) ≤ (H.card : ℝ)) :
    ∃ θ ∈ Λ, ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun x => inner ℝ θ x) '' (↑(graphFiber F H θ) : Set Plane)) cc →
      d ^ 2 ≤ (8 * C ^ 2 * energyConstant γ * δ ^ γ) * (m : ℝ) := by
  classical
  obtain ⟨p, hp⟩ := hHne
  have hΛpos : (0 : ℝ) < Λ.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨p.1, (Finset.mem_product.mp (hH hp)).1⟩
  have hFpos : (0 : ℝ) < F.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨p.2, (Finset.mem_product.mp (hH hp)).2⟩
  let n (θ : Plane) : ℝ := (graphFiber F H θ).card
  let W : ℝ := ∑ θ ∈ Λ, (n θ) ^ 2
  let K : ℝ := 8 * C ^ 2 * energyConstant γ * δ ^ γ
  have hsum : ∑ θ ∈ Λ, n θ = (H.card : ℝ) := by
    dsimp [n]
    exact_mod_cast sum_graphFiber_card hH
  have hcauchy : (H.card : ℝ) ^ 2 ≤ (Λ.card : ℝ) * W := by
    simpa only [hsum] using sq_sum_le_card_mul_sum_sq (s := Λ) (f := n)
  have hsquare : (d * (Λ.card : ℝ) * (F.card : ℝ)) ^ 2 ≤ (H.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hdensity 2
  have hWlower : d ^ 2 * (Λ.card : ℝ) * (F.card : ℝ) ^ 2 ≤ W := by
    apply (mul_le_mul_iff_right₀ hΛpos).mp
    calc (Λ.card : ℝ) * (d ^ 2 * (Λ.card : ℝ) * (F.card : ℝ) ^ 2) =
          (d * (Λ.card : ℝ) * (F.card : ℝ)) ^ 2 := by ring
      _ ≤ (H.card : ℝ) ^ 2 := hsquare
      _ ≤ (Λ.card : ℝ) * W := hcauchy
  have hWpos : 0 < W := (by positivity : 0 < d ^ 2 * (Λ.card : ℝ) * (F.card : ℝ) ^ 2).trans_le hWlower
  obtain ⟨θ, hθ, hn, hselect⟩ := exists_weighted_ratio Λ
    (fun θ => projectionEnergy F θ δ) (fun θ => (n θ) ^ 2)
    (fun θ _ => projectionEnergy_nonneg F θ δ) (fun θ _ => sq_nonneg _) hWpos
  have hmoment : ∑ θ ∈ Λ, projectionEnergy F θ δ ≤ K * (Λ.card : ℝ) * (F.card : ℝ) ^ 2 :=
    sum_projectionEnergy_le hF hΛ hδ hδ1 hC hunit hγ hγ1
  have hscale : 0 < (Λ.card : ℝ) * (F.card : ℝ) ^ 2 := by positivity
  have hrow : projectionEnergy F θ δ * d ^ 2 ≤ K * (n θ) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hscale).mp
    calc (projectionEnergy F θ δ * d ^ 2) * ((Λ.card : ℝ) * (F.card : ℝ) ^ 2) =
          projectionEnergy F θ δ * (d ^ 2 * (Λ.card : ℝ) * (F.card : ℝ) ^ 2) := by ring
      _ ≤ projectionEnergy F θ δ * W :=
        mul_le_mul_of_nonneg_left hWlower (projectionEnergy_nonneg F θ δ)
      _ ≤ (∑ u ∈ Λ, projectionEnergy F u δ) * (n θ) ^ 2 := hselect
      _ ≤ (K * (Λ.card : ℝ) * (F.card : ℝ) ^ 2) * (n θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hmoment (sq_nonneg _)
      _ = (K * (n θ) ^ 2) * ((Λ.card : ℝ) * (F.card : ℝ) ^ 2) := by ring
  refine ⟨θ, hθ, ?_⟩
  intro m cc hc
  have hcover : (n θ) ^ 2 ≤ (m : ℝ) * projectionEnergy F θ δ :=
    card_sq_le_cover_mul_projectionEnergy (graphFiber_subset F H θ) θ δ hc
  apply (mul_le_mul_iff_left₀ hn).mp
  calc d ^ 2 * (n θ) ^ 2 ≤ d ^ 2 * ((m : ℝ) * projectionEnergy F θ δ) :=
        mul_le_mul_of_nonneg_left hcover (sq_nonneg d)
    _ = (m : ℝ) * (projectionEnergy F θ δ * d ^ 2) := by ring
    _ ≤ (m : ℝ) * (K * (n θ) ^ 2) := mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg m)
    _ = (K * (m : ℝ)) * (n θ) ^ 2 := by ring

end WangZahlLot.Obl.wz_kaufman_projection_count
