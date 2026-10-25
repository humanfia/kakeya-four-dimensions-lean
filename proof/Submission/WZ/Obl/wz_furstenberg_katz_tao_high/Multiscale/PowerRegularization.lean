-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.PowerRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0572, Multiscale/PowerRegularization.lean; namespace renamed.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.Regularization
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.ColorBudget
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PowerBudget

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- A bounded number of arbitrary incidence partitions can be balanced with
an arbitrarily small power loss, uniformly over polynomially sized families. -/
theorem regularize_finite_partitions_power (ε : ℝ) (hε : 0 < ε) (B : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ {α I : Type*} [DecidableEq α] [Fintype I] [DecidableEq I] [Nonempty I]
        {Y : I → Type*} [∀ i, DecidableEq (Y i)],
        Fintype.card I ≤ B →
        ∀ (H : Finset α), H.Nonempty → (H.card : ℝ) ≤ δ ^ (-7 : ℝ) →
        ∀ f : ∀ i, α → Y i,
        ∃ S ⊆ H, S.Nonempty ∧ δ ^ ε * (H.card : ℝ) ≤ S.card ∧
          ∀ i, Balanced S (f i) (δ ^ (-ε)) := by
  classical
  obtain ⟨d₁, hd₁, hcolors⟩ :=
    WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.regularization_color_budget
      (show 0 < ε / 2 by linarith) B
  obtain ⟨d₂, hd₂, hd₂1, hconst⟩ :=
    WangZahlLot.Obl.wz_nonconcentrated_dot_products.exists_power_bound
      (8 * ((B : ℝ) + 1)) (show 0 < ε / 2 by linarith)
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, (min_le_right _ _).trans hd₂1, ?_⟩
  intro δ hδ hδsmall α I _ _ _ _ Y _ hIB H hH hHbound f
  have hδ1 : δ ≤ 1 := (hδsmall.trans (min_le_right _ _)).trans hd₂1
  obtain ⟨q, hq, hqB, color, hc⟩ := hcolors δ H.card hδ hδ1
    (hδsmall.trans (min_le_left _ _)) (Finset.card_pos.mpr hH) hHbound
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqI : (q : ℝ) ^ Fintype.card I ≤ δ ^ (-(ε / 2)) :=
    (pow_le_pow_right₀ hq1 hIB).trans hqB
  have hconstant := hconst δ hδ (hδsmall.trans (min_le_right _ _))
  have hpow : δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) = δ ^ (-ε) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hIBR : (Fintype.card I : ℝ) ≤ B := by exact_mod_cast hIB
  have hmassloss : 2 * (q : ℝ) ^ Fintype.card I ≤ δ ^ (-ε) := by
    calc
      _ ≤ (8 * ((B : ℝ) + 1)) * δ ^ (-(ε / 2)) := by
        apply mul_le_mul (by have hb0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _; linarith) hqI (by positivity) (by positivity)
      _ ≤ δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) :=
        mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hδ.le _)
      _ = _ := hpow
  have hballoss : 8 * (Fintype.card I : ℝ) * (q : ℝ) ^ Fintype.card I ≤ δ ^ (-ε) := by
    calc
      _ ≤ (8 * ((B : ℝ) + 1)) * δ ^ (-(ε / 2)) := by
        apply mul_le_mul (by linarith) hqI (by positivity) (by positivity)
      _ ≤ δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) :=
        mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hδ.le _)
      _ = _ := hpow
  obtain ⟨S, hSH, hSne, hmass, hbal⟩ := regularize_finite_partitions H hH f hq color (by
    intro a b ha han hb hbn hab
    have hh := hc a b ha han hb hbn hab
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    linarith)
  refine ⟨S, hSH, hSne, ?_, ?_⟩
  · calc
      δ ^ ε * (H.card : ℝ) ≤ δ ^ ε * ((2 * (q : ℝ) ^ Fintype.card I) * S.card) :=
        mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hδ.le _)
      _ ≤ δ ^ ε * (δ ^ (-ε) * S.card) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
        exact mul_le_mul_of_nonneg_right hmassloss (Nat.cast_nonneg _)
      _ = S.card := by rw [← mul_assoc, ← Real.rpow_add hδ]; simp
  · intro i x hx y hy
    exact (hbal i x hx y hy).trans
      (mul_le_mul_of_nonneg_right hballoss (Nat.cast_nonneg _))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
