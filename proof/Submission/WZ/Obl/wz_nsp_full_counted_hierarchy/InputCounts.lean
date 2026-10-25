-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.InputCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.FineCounts
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.BufferGeometry
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Budgets
import Submission.WZ.Obl.wz_essentially_distinct_tube_count

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts counts_mono)

/-- The part of the supplied covers used to prepare the counted source tower. -/
abbrev CoverSupply (δ η : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ,
    ρ₀ ≤ ρ ∧ ρ ≤ δ ^ (-η) * ρ₀ ∧
    ∃ (k : ℕ) (y w : Fin k → Space) (f : Fin n → Fin k),
      (∀ j, ‖w j‖ = 1) ∧
      (∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i))) ∧
      Counts ρ (δ ^ (-η)) k y w

/-- The cover at the bottom scale transfers a small global count bound to
the original essentially distinct family. -/
theorem fine_counts_from_supply : ∃ C : ℝ, 0 < C ∧
    ∀ δ η : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → η ≤ 1 →
      ∀ (n : ℕ) (x v : Fin n → Space),
        (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
        (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
          (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
        CoverSupply δ η n x v → Counts δ (C * δ ^ (-5 * η)) n x v := by
  obtain ⟨C, hC, hc⟩ := counts_from_coarse_cover
  refine ⟨C, hC, ?_⟩
  intro δ η hδ hδ100 hη n x v hv hball hsep hsupply
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨ρ, hδρ, hρ, k, y, w, f, hw, hsub, hcounts⟩ := hsupply δ le_rfl hδ1
  have hρ1 : ρ ≤ 1 := by
    calc
      ρ ≤ δ ^ (-η) * δ := hρ
      _ = δ ^ (1 - η) := by rw [show 1 - η = -η + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
      _ ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith)
  have hh := hc δ ρ (δ ^ (-η)) hδ hδ100 (hδ.trans_le hδρ) hρ1
    (Real.rpow_nonneg hδ.le _) n k x v y w f hv hw hball hsep hsub hcounts
  have hρpos : 0 ≤ ρ := hδ.le.trans hδρ
  apply counts_mono hh
  apply (div_le_iff₀ (pow_pos hδ 4)).mpr
  calc
    C * δ ^ (-η) * ρ ^ 4 ≤ C * δ ^ (-η) * (δ ^ (-η) * δ) ^ 4 := by
      gcongr
    _ = C * δ ^ (-5 * η) * δ ^ 4 := by
      have he : δ ^ (-η) * (δ ^ (-η)) ^ (4 : ℕ) = δ ^ (-5 * η) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
        congr 1
        push_cast
        ring
      rw [mul_pow]
      calc
        C * δ ^ (-η) * ((δ ^ (-η)) ^ (4 : ℕ) * δ ^ (4 : ℕ)) =
          C * (δ ^ (-η) * (δ ^ (-η)) ^ (4 : ℕ)) * δ ^ (4 : ℕ) := by ring
        _ = _ := by rw [he]

/-- One small cutoff handles all source-level counting constants and the
polynomial cardinality required for logarithmic regularization. -/
theorem source_count_cutoff {u : ℝ} (hu : 0 < u) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ η : ℝ, 0 < δ → δ ≤ d →
      0 < η → η ≤ 1 → 10 * η ≤ u →
      32 ^ 2 * δ ^ (-η) ≤ δ ^ (-u) ∧
      ∀ (n : ℕ) (x v : Fin n → Space),
        (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
        (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
          (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
        CoverSupply δ η n x v → Counts δ (δ ^ (-u)) n x v ∧ (n : ℝ) ≤ δ ^ (-7 : ℝ) := by
  obtain ⟨C, hC, hcounts⟩ := fine_counts_from_supply
  obtain ⟨C₀, hC₀, hcard⟩ := WangZahlLot.wz_essentially_distinct_tube_count
  obtain ⟨d₁, hd₁, hCsmall⟩ := constant_power_cutoff hC (show 0 < u / 2 by positivity)
  obtain ⟨d₂, hd₂, h32small⟩ := constant_power_cutoff (show (0 : ℝ) < 32 ^ 2 by norm_num)
    (show 0 < u / 2 by positivity)
  obtain ⟨d₃, hd₃, hC₀small⟩ := constant_power_cutoff hC₀ (show (0 : ℝ) < 1 by norm_num)
  refine ⟨min (1 / 100) (min d₁ (min d₂ d₃)), lt_min (by norm_num) (lt_min hd₁ (lt_min hd₂ hd₃)), ?_⟩
  intro δ η hδ hδd hη hη1 hηu
  have hδ100 : δ ≤ 1 / 100 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδd' := hδd.trans (min_le_right _ _)
  have hc : C ≤ δ ^ (-(u / 2)) := hCsmall δ hδ (hδd'.trans (min_le_left _ _))
  have hc32 : 32 ^ 2 ≤ δ ^ (-(u / 2)) :=
    h32small δ hδ ((hδd'.trans (min_le_right _ _)).trans (min_le_left _ _))
  have hc₀ : C₀ ≤ δ ^ (-(1 : ℝ)) :=
    hC₀small δ hδ ((hδd'.trans (min_le_right _ _)).trans (min_le_right _ _))
  refine ⟨?_, ?_⟩
  · calc
      32 ^ 2 * δ ^ (-η) ≤ δ ^ (-(u / 2)) * δ ^ (-η) := by gcongr
      _ = δ ^ (-(u / 2) - η) := by rw [← Real.rpow_add hδ]; congr 1
      _ ≤ δ ^ (-u) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  · intro n x v hv hball hsep hsupply
    refine ⟨counts_mono (hcounts δ η hδ hδ100 hη1 n x v hv hball hsep hsupply) ?_, ?_⟩
    · calc
        C * δ ^ (-5 * η) ≤ δ ^ (-(u / 2)) * δ ^ (-5 * η) := by gcongr
        _ = δ ^ (-(u / 2) - 5 * η) := by rw [← Real.rpow_add hδ]; congr 1; ring
        _ ≤ δ ^ (-u) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    · have hn := (hcard δ hδ hδ100 n x v hv hball hsep).trans hc₀
      have he : δ ^ (-7 : ℝ) * δ ^ (6 : ℕ) = δ ^ (-(1 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hδ]
        norm_num
      apply le_of_mul_le_mul_right (a := δ ^ (6 : ℕ))
      · rwa [he]
      · positivity

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
