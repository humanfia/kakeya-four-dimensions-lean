-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Budgets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Arithmetic
import Submission.WZ.Obl.wz_tower_convex_count_composition.Arithmetic
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

/-- Absorb any fixed positive constant into a prescribed negative power. -/
theorem constant_power_cutoff {C u : ℝ} (hC : 0 < C) (hu : 0 < u) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C ≤ δ ^ (-u) := by
  refine ⟨C ^ (-1 / u), Real.rpow_pos_of_pos hC _, ?_⟩
  intro δ hδ hδd
  have he : (C ^ (-1 / u)) ^ (-u) = C := by
    rw [← Real.rpow_mul hC.le]
    have hx : (-1 / u) * (-u) = 1 := by field_simp
    rw [hx, Real.rpow_one]
  rw [← he]
  exact Real.rpow_le_rpow_of_nonpos hδ hδd (by linarith)

/-- Choose the source loss before the single-scale constant is known. After
that constant is chosen, shrinking the cutoff handles all count and fullness
budgets uniformly over the bounded height. -/
theorem iteration_budgets {a b κ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (B : ℕ) :
    ∃ u : ℝ, 0 < u ∧ u * ((B : ℝ) + 1) ≤ a ∧
      ∀ C : ℝ, 0 < C → ∃ d : ℝ, 0 < d ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d →
          ∀ (j : ℕ) (L : ℝ), j ≤ B → 0 ≤ L → L ≤ C * δ ^ (-3 * u) →
            (131072 * max 1 L) ^ j ≤ δ ^ (-b) ∧ δ ^ b ≤ κ ^ j := by
  obtain ⟨θ, hθ, hθb, d₁, hd₁, hpower⟩ :=
    WangZahlLot.Obl.wz_tower_convex_count_composition.power_budget 131072 (by norm_num) B b hb
  let u := min (θ / 4) (a / ((B : ℝ) + 1))
  have hden : 0 < (B : ℝ) + 1 := by positivity
  have hu : 0 < u := lt_min (by positivity) (div_pos ha hden)
  have huθ : 4 * u ≤ θ := by have := min_le_left (θ / 4) (a / ((B : ℝ) + 1)); dsimp [u]; linarith
  have hua : u * ((B : ℝ) + 1) ≤ a :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨u, hu, hua, ?_⟩
  intro C hC
  obtain ⟨d₂, hd₂, hconstant⟩ := constant_power_cutoff hC hu
  obtain ⟨d₃, hd₃, hsmall⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff hb (pow_pos hκ B)
  refine ⟨min d₁ (min d₂ d₃), lt_min hd₁ (lt_min hd₂ hd₃), ?_⟩
  intro δ hδ hδ1 hδd j L hj hL hLC
  have hδd₁ : δ ≤ d₁ := hδd.trans (min_le_left _ _)
  have hδd₂ : δ ≤ d₂ := (hδd.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδd₃ : δ ≤ d₃ := (hδd.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hLθ : L ≤ δ ^ (-θ) := by
    calc
      L ≤ C * δ ^ (-3 * u) := hLC
      _ ≤ δ ^ (-u) * δ ^ (-3 * u) :=
        mul_le_mul_of_nonneg_right (hconstant δ hδ hδd₂) (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-4 * u) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (-θ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have h1θ : 1 ≤ δ ^ (-θ) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -θ ≤ 0 by linarith)
  refine ⟨?_, (hsmall δ hδ hδd₃).trans (pow_le_pow_of_le_one hκ.le hκ1 hj)⟩
  apply le_trans _ (hpower δ hδ hδ1 hδd₁ j hj)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_left (max_le h1θ hLθ) (by norm_num)

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
