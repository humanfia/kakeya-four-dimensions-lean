-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.UniformPackingPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PackingDensity
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PieceRefinement
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.DyadicPower

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

/-- Uniformize prism pieces using any common packing-volume budget.
The error scale is independent of the physical prism dimensions. -/
theorem packing_prism_uniform_refinement {D ν : ℝ} (hD : 0 < D) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ (n : ℕ), (n : ℝ) ≤ δ ^ (-D) →
      ∀ (a b c K₀ B density : ℝ),
      0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ K₀ → 0 ≤ density →
      ∀ (e : V ≃ₗᵢ[ℝ] V) (F : Finset V) (Y Z : Fin n → Set V)
        (H : V → Set V) (C : Fin n → V → Prop),
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) →
      (↑F : Set V).PairwiseDisjoint (fun z => P a b c z e) →
      (∀ z ∈ F, MeasurableSet (H z) ∧ H z ⊆ P a b c z e) →
      o ((F.card : ℝ) * (a * b * c)) ≤ o (K₀ * B) →
      (⋃ z ∈ F, H z) = ⋃ i, Z i →
      (∀ i z, z ∈ F → (Z i ∩ H z).Nonempty →
        Z i ∩ P a b c z e ⊆ H z ∧ C i z) →
      ∀ (M K : ENNReal), M ≠ 0 → M ≠ ⊤ →
      (∀ p ∈ ⋃ i, Y i, M ≤ multiplicity Y p) →
      (∀ p, multiplicity Y p ≤ 2 * M) →
      (∑ i, μ (Y i)) ≤ K * ∑ i, μ (Z i) →
      o (density * B) ≤ μ (⋃ i, Y i) →
      ∃ (k : ℕ) (F' : Finset V) (W : Fin n → Set V) (H' : V → Set V),
        F' ⊆ F ∧ (∀ z, H' z ⊆ H z) ∧
        (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
        (↑F' : Set V).PairwiseDisjoint (fun z => P a b c z e) ∧
        (∀ z ∈ F', MeasurableSet (H' z) ∧ H' z ⊆ P a b c z e ∧ (H' z).Nonempty) ∧
        (⋃ z ∈ F', H' z) = ⋃ i, W i ∧
        (∑ i, μ (Y i)) ≤ (K * o (δ ^ (-ν))) * ∑ i, μ (W i) ∧
        o (density * F'.card * (a * b * c)) ≤
          (o (2 * K₀) * K * o (δ ^ (-ν))) * ∑ z ∈ F', μ (H' z) ∧
        (∀ i z, z ∈ F' → (W i ∩ H' z).Nonempty →
          W i ∩ P a b c z e ⊆ H' z ∧ C i z) ∧
        ∀ p ∈ ⋃ i, W i,
          2 ^ k ≤ (Finset.univ.filter fun i => p ∈ W i).card ∧
          (Finset.univ.filter fun i => p ∈ W i).card < 2 ^ (k + 1) := by
  classical
  obtain ⟨d, hd, hdyadic⟩ := dyadic_shading_refinement_power hD hν
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd n hn a b c K₀ B density ha hb hc hK₀ hdensity
    e F Y Z H C hY hZ hdisj hH hpacking hunion hcross M K hM0 hMtop hlower hupper hmass hvol
  obtain ⟨k, W, hW, hkeep, hlevel⟩ := hdyadic δ hδ hδd n hn Z (fun i => (hZ i).1)
  obtain ⟨F', H', hFF, hHH, hH', hunion', hcross'⟩ :=
    finite_piece_subshading F (fun z => P a b c z e) H Z W C hW
      (fun z hz => (hH z hz).1) hunion hcross
  have hinv : o (δ ^ (-ν)) * o (δ ^ ν) = 1 := by
    dsimp only [o]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
    simp
  have hmass' : (∑ i, μ (Y i)) ≤ (K * o (δ ^ (-ν))) * ∑ i, μ (W i) := by
    calc
      _ ≤ K * ∑ i, μ (Z i) := hmass
      _ = (K * o (δ ^ (-ν))) * (o (δ ^ ν) * ∑ i, μ (Z i)) := by
        rw [mul_assoc, ← mul_assoc (o (δ ^ (-ν))), hinv, one_mul]
      _ ≤ _ := mul_le_mul_right hkeep _
  have hWY : ∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i :=
    fun i => ⟨(hW i).1, ((hW i).2).trans (hZ i).2⟩
  have hdisj' : (↑F' : Set V).PairwiseDisjoint (fun z => P a b c z e) :=
    fun z hz z' hz' hne => hdisj (hFF hz) (hFF hz') hne
  have hpiece : ∀ z ∈ F', MeasurableSet (H' z) ∧
      H' z ⊆ P a b c z e ∧ (H' z).Nonempty := fun z hz =>
    ⟨(hH' z hz).1, (hHH z).trans (hH z (hFF hz)).2, (hH' z hz).2⟩
  have hpacking' : o ((F'.card : ℝ) * (a * b * c)) ≤ o (K₀ * B) := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hpacking
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hFF) (by positivity)
  have hden := prism_piece_density_of_packing hK₀ hdensity
    e F' Y W H' hY hWY hdisj' (fun z hz => ⟨(hpiece z hz).1, (hpiece z hz).2.1⟩)
    hunion' hM0 hMtop hlower hupper hmass' hpacking' hvol
  refine ⟨k, F', W, H', hFF, hHH, hW, hdisj', hpiece, hunion', hmass', ?_, hcross', hlevel⟩
  simpa only [mul_assoc] using hden

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
