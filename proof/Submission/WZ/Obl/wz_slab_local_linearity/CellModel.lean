-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellModel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellPowerBounds
import Submission.WZ.Obl.wz_slab_local_linearity.CellScaleBounds
import Submission.WZ.Obl.wz_slab_local_linearity.CellParameters
import Submission.WZ.Obl.wz_slab_local_linearity.BlockCount

namespace WangZahlLot.Obl.wz_slab_local_linearity

open CellProofs

/-- The finite projection dichotomy proves the local-linearity statement for a
normalized family of cells. The covering constant may have any fixed prefactor. -/
theorem finite_cell_linearity {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hfinite : FiniteDichotomy σ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∀ ε : ℝ, 0 < ε → ∃ η ρ₀ : ℝ, 0 < η ∧ 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (M : ℕ) (β : ℝ) (f : ℝ → ℝ)
        (V : Space → Space) (P : Finset (ℤ × ℤ × ℤ))
        (A : ℤ → Set ℝ) (AL : ℤ × ℤ × ℤ → Set ℝ),
      1 / Real.sqrt ρ ≤ (M : ℝ) → (M : ℝ) ≤ 2 / Real.sqrt ρ →
      CellHyp ρ M 0 (C₀ * ρ ^ (-(1 - σ) / 2 - η)) (ρ ^ η) β f V P A AL →
      ρ ^ (-2 + σ / 2 + η) ≤ (P.card : ℝ) →
      (∀ k, Assouad ρ (1 - σ) (ρ ^ (-η)) (A k)) →
      ∃ a b : ℝ, |b| ≤ 2 ∧ ∃ S : Finset ℤ,
        S ⊆ P.image (fun q => q.2.2) ∧ ρ ^ ((ε - 1) / 2) ≤ (S.card : ℝ) ∧
        ∀ k ∈ S, |f (ρ * k) - (a + b * (ρ * k))| ≤ ρ / 8 := by
  intro ε hε
  let ε' := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨τ, δ₀, hτ, hδ₀, hLD⟩ := hfinite.linearityDichotomy.instance hε'
  obtain ⟨η, ρ₀, hη, hρ₀, hparams⟩ := exists_cell_parameters hσ hτ hC₀ hδ₀
  refine ⟨η, ρ₀, hη, hρ₀, ?_⟩
  intro ρ hρ hρsmall M β f V P A AL hMlo hMhi hcell hP hA
  obtain ⟨hρ100, hδsmall, hκsmall, hrichbudget, htriplebudget, hADbudget⟩ := hparams ρ hρ hρsmall
  have hρ1 : ρ ≤ 1 := by linarith
  have hκ : 0 < ρ ^ η := Real.rpow_pos_of_pos hρ _
  have hκ1 : ρ ^ η ≤ 1 := by linarith
  obtain ⟨hδ, hδ1, hN₀a, hN₀b, n7, n10⟩ := cell_scale_bounds hρ hρ1 hκ hκsmall hMlo hMhi
  obtain ⟨n4, n5, n8⟩ := cell_ad_budgets hρ hτ hκ1 hADbudget
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < P.card := (Real.rpow_pos_of_pos hρ _).trans_le hP
    exact_mod_cast hp
  have hNB : ((P.image (blockOf M)).card : ℝ) ≤ 4 / Real.sqrt ρ := by
    calc ((P.image (blockOf M)).card : ℝ) ≤ 4 / ((M : ℝ) * ρ) :=
          card_blocks_le hρ hcell.hM hcell.hs P hcell.ybound
      _ ≤ 4 / Real.sqrt ρ := div_le_div_of_nonneg_left (by norm_num)
        (Real.sqrt_pos.mpr hρ) (cell_layer_scale hρ hMlo hMhi).1
  have hrich := cell_rich_budget hρ hC₀.le hκ1 hMhi hP hrichbudget
  have n6 := cell_triple_budget hρ hC₀.le hτ hκ1 hcell.hM hMhi hP htriplebudget
  obtain ⟨a, b, hb, S, hSP, hS, hfS⟩ := hcell.exists_affine_of_bounds hPne (by positivity) hNB
    (by positivity) hrich hσ hσ1.le (Real.rpow_nonneg hρ.le _) hA hε'1 hδ hδ1
    (hLD _ hδ hδsmall) hN₀a hN₀b n4 n5 n6 n7 n8 n10
  refine ⟨a, b, hb, S, hSP, ?_, hfS⟩
  exact (cell_entropy_lower hρ hρ1 (min_le_left _ _) hε'1).trans hS

end WangZahlLot.Obl.wz_slab_local_linearity
