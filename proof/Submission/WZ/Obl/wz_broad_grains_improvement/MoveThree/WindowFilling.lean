-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.WindowFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/WindowFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, WindowFilling.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SecondPacketFilling
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrescribedWindows

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- The second filling works for any finite family with a controlled number
of occupied rows, including common spatial windows of the packet labels. -/
theorem cordoba_count_filling_uniform {β t s u h ε vLoss L Ccount Cvol : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t) (hhu : h < u)
    (hgap : 3 * u + s + vLoss < ε) (hL : 0 < L)
    (hCcount : 0 < Ccount) (hCvol : 0 < Cvol) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ d θ M₀ : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ d → d ≤ 1 / 100 → 2 * d ≤ L →
      δ ^ (-t) * d ≤ θ → θ ≤ 1 → 0 ≤ M₀ →
      ∀ {κ : Type*} [Fintype κ] (n : ℕ) (x v : Fin n → V)
        (Y : κ → Fin n → Set V),
      (∀ i, ‖v i‖ = 1) → (∀ k i, MeasurableSet (Y k i)) →
      (∀ k i, Y k i ⊆ T d (x i) (v i)) →
      (∑ k, q n {i | (Y k i).Nonempty}) ≤ Ccount * M₀ →
      O (δ ^ h * M₀ * d ^ 2) ≤ ∑ k, ∑ i, μ (Y k i) →
      (∀ k p u' r, d ≤ r → q n {i | p ∈ Y k i ∧ pd (v i) u' ≤ r} ≤
        2 * (r / θ) ^ β * q n {i | p ∈ Y k i}) →
      ∀ (z : κ → V) (U : κ → Set V),
      (∀ k i, Y k i ⊆ ball (z k) (L / 2)) →
      (∀ k i, Y k i ⊆ U k) →
      (∀ k, μ (U k) ≤ O (Cvol * δ ^ (-vLoss) * d * θ)) →
      ∃ Z : κ → Fin n → Set V,
        (∀ k i, MeasurableSet (Z k i) ∧ Z k i ⊆ Y k i) ∧
        (∀ k i, Z k i ⊆ U k) ∧
        (1 / 2 : ENNReal) * (∑ k, ∑ i, μ (Y k i)) ≤ ∑ k, ∑ i, μ (Z k i) ∧
        (∀ k i, (Z k i).Nonempty → O (δ ^ u * d ^ 2) ≤ μ (Z k i)) ∧
        (∀ k p, p ∈ ⋃ i, Z k i → q n {i | p ∈ Y k i} ≤ 4 * q n {i | p ∈ Z k i}) ∧
        (∀ k p u' r, d ≤ r → q n {i | p ∈ Z k i ∧ pd (v i) u' ≤ r} ≤
          8 * (r / θ) ^ β * q n {i | p ∈ Z k i}) ∧
        ∀ k, (⋃ i, Z k i).Nonempty → O (δ ^ ε) * μ (U k) ≤ μ (⋃ i, Z k i) := by
  classical
  obtain ⟨d₁, hd₁, hd₁small, Hfill⟩ := second_filling_width_parameters hβ hs hst hgap hL hCvol
  obtain ⟨d₂, hd₂, Hcost⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (sub_pos.mpr hhu) (K := 1 / (4 * Ccount)) (by positivity)
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, (min_le_left _ _).trans hd₁small, ?_⟩
  intro δ d θ M₀ hδ hδ0 hδd hd1 hLd hgrow hθ1 hM₀ κ inst n x v Y
    hv hYm hYT hcount hmass hBr z U hball hU hUvol
  have hd : 0 < d := hδ.trans_le hδd
  have hθ : 0 < θ := (mul_pos (Real.rpow_pos_of_pos hδ _) hd).trans_le hgrow
  obtain ⟨hr, hr1, hangle, hnum⟩ := Hfill δ d θ hδ
    (hδ0.trans (min_le_left _ _)) hδd hgrow hθ1
  have hconst : Ccount * δ ^ u ≤ δ ^ h / 4 := by
    have hh := Hcost δ hδ (hδ0.trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0 < 4 * Ccount)).mp hh
    have hp : δ ^ u = δ ^ (u - h) * δ ^ h := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [hp]
    nlinarith [mul_le_mul_of_nonneg_right hh' (Real.rpow_nonneg hδ.le h)]
  let cost := fun k i => if (Y k i).Nonempty then O (δ ^ u * d ^ 2) else 0
  have hbudget : (∑ k, ∑ i, cost k i) ≤
      (1 / 4 : ENNReal) * ∑ k, ∑ i, μ (Y k i) := by
    calc
      _ = O ((δ ^ u * d ^ 2) * ∑ k, q n {i | (Y k i).Nonempty}) :=
        occupied_row_cost Y (by positivity)
      _ ≤ O ((δ ^ u * d ^ 2) * (Ccount * M₀)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcount (by positivity))
      _ ≤ O ((1 / 4 : ℝ) * (δ ^ h * M₀ * d ^ 2)) :=
        ENNReal.ofReal_le_ofReal (by
          have hh := mul_le_mul_of_nonneg_right hconst (show 0 ≤ M₀ * d ^ 2 by positivity)
          nlinarith)
      _ = (1 / 4 : ENNReal) * O (δ ^ h * M₀ * d ^ 2) := by
        dsimp only [O]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
          ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      _ ≤ _ := mul_le_mul' le_rfl hmass
  exact cordoba_family_filling hd hd1 hLd (fun _ => θ) (fun _ => θ * δ ^ s)
    (fun _ => δ ^ u * d ^ 2) (fun _ => δ ^ ε) (fun _ => Cvol * δ ^ (-vLoss) * d * θ)
    (fun _ => hθ) (fun _ => ⟨hr, hr1⟩) (fun _ => by positivity) (fun _ => by positivity)
    (fun _ => x) (fun _ => v) (fun _ => hv) Y hYm hYT z hball U hU hUvol hBr cost
    (fun k i hi => by simp [cost, hi]) hbudget (fun _ => hangle) (fun _ => hnum)

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
