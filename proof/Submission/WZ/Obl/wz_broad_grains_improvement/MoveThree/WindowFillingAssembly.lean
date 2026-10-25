-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.WindowFillingAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/WindowFillingAssembly.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, WindowFillingAssembly.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.WindowRows

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- Filling after the spatial-window cut retains half the original total
incidence mass. Only the fixed number of windows enters the row cost; there
is no uniform upper point-multiplicity assumption. -/
theorem window_filling_uniform {β t s u h ε vLoss L Ccount Cvol : ℝ} {N : ℕ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t) (hhu : h < u)
    (hgap : 3 * u + s + vLoss < ε) (hL : 0 < L)
    (hCcount : 0 < Ccount) (hCvol : 0 < Cvol) (hN : 0 < N) :
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
      ∀ (z : κ → V) (windows : κ → Fin N → Set V) (U : κ × Fin N → Set V),
      (∀ k i, Y k i ⊆ ball (z k) (L / 2)) →
      (∀ k j, MeasurableSet (windows k j)) →
      (∀ k i, Y k i ⊆ ⋃ j, windows k j) →
      (∀ p i, windowRows Y windows p i ⊆ U p) →
      (∀ p, μ (U p) ≤ O (Cvol * δ ^ (-vLoss) * d * θ)) →
      ∃ Z : (κ × Fin N) → Fin n → Set V,
        (∀ p i, MeasurableSet (Z p i) ∧ Z p i ⊆ windowRows Y windows p i) ∧
        (∀ p i, Z p i ⊆ U p) ∧
        (1 / 2 : ENNReal) * (∑ k, ∑ i, μ (Y k i)) ≤ ∑ p, ∑ i, μ (Z p i) ∧
        (∀ p i, (Z p i).Nonempty → O (δ ^ u * d ^ 2) ≤ μ (Z p i)) ∧
        (∀ p x', x' ∈ ⋃ i, Z p i →
          q n {i | x' ∈ windowRows Y windows p i} ≤ 4 * q n {i | x' ∈ Z p i}) ∧
        (∀ p x' u' r, d ≤ r → q n {i | x' ∈ Z p i ∧ pd (v i) u' ≤ r} ≤
          8 * (r / θ) ^ β * q n {i | x' ∈ Z p i}) ∧
        ∀ p, (⋃ i, Z p i).Nonempty → O (δ ^ ε) * μ (U p) ≤ μ (⋃ i, Z p i) := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  obtain ⟨d₀, hd₀, hd₀small, Hfill⟩ := cordoba_count_filling_uniform
    (Ccount := N * Ccount) hβ hs hst hhu hgap hL (mul_pos hNr hCcount) hCvol
  refine ⟨d₀, hd₀, hd₀small, ?_⟩
  intro δ d θ M₀ hδ hδ0 hδd hd1 hLd hgrow hθ1 hM₀ κ inst n x v Y
    hv hYm hYT hcount hmass hBr z windows U hball hwm hcover hU hUvol
  have hd : 0 < d := hδ.trans_le hδd
  have hθ : 0 < θ := (mul_pos (Real.rpow_pos_of_pos hδ _) hd).trans_le hgrow
  have hrow : (∑ p : κ × Fin N, q n {i | (windowRows Y windows p i).Nonempty}) ≤
      (N * Ccount) * M₀ := by
    calc
      _ ≤ (N : ℝ) * ∑ k, q n {i | (Y k i).Nonempty} := window_rows_count Y windows
      _ ≤ (N : ℝ) * (Ccount * M₀) := mul_le_mul_of_nonneg_left hcount hNr.le
      _ = _ := by ring
  have hkeep := window_rows_mass Y windows hcover
  obtain ⟨Z, hZ, hZU, hretain, hrows, hcounts, hbroad, hdense⟩ :=
    Hfill δ d θ M₀ hδ hδ0 hδd hd1 hLd hgrow hθ1 hM₀ n x v (windowRows Y windows)
      hv (window_rows_measurable Y windows hYm hwm)
      (fun p i => inter_subset_left.trans (hYT p.1 i)) hrow (hmass.trans hkeep)
      (fun p q u' r hr => window_rows_cap Y windows v p q u' r (2 * (r / θ) ^ β)
        (by have hr0 := hd.trans_le hr; positivity) (hBr p.1 q u' r hr))
      (fun p => z p.1) U (fun p i => inter_subset_left.trans (hball p.1 i)) hU hUvol
  exact ⟨Z, hZ, hZU, (mul_le_mul' le_rfl hkeep).trans hretain, hrows, hcounts, hbroad, hdense⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
