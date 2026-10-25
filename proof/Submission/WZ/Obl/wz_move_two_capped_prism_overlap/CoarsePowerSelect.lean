-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CoarsePowerSelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CoarseSelect

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, CoarsePowerSelect.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V X)

/-- Iterated whole-coarse-fibre selection makes an arbitrary fixed dyadic
enlargement essentially distinct, with only a fixed loss of incidence mass. -/
theorem select_power_two_coarse {n : ℕ} (D : PrismData n) (t : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (ht : (2 : ℝ) ^ t * ρ ≤ 1) (hw : ∀ k, ‖D.w k‖ = 1)
    (hX : X ρ D.N D.y D.w)
    (hpos : 0 < ∑ i, ∑ j, volume (D.W i j)) :
    ∃ L N : ℕ, ∃ f : Fin L → Fin D.L, ∃ g : Fin N → Fin D.N,
      ∃ γ : Fin L → Fin N,
        Function.Injective f ∧ Function.Injective g ∧
        (∀ j, g (γ j) = D.γ (f j)) ∧
        X ((2 : ℝ) ^ t * ρ) N (D.y ∘ g) (D.w ∘ g) ∧
        (∑ i, ∑ j, volume (D.W i j)) ≤
          (((10 ^ 40 + 1 : ℕ) : ENNReal) ^ t) * ∑ i, ∑ j, volume (D.W i (f j)) := by
  induction t generalizing D with
  | zero =>
    refine ⟨D.L, D.N, id, id, D.γ, Function.injective_id, Function.injective_id,
      fun _ => rfl, ?_, ?_⟩
    · simpa using hX
    · simp
  | succ t ih =>
    have he : (2 : ℝ) ^ (t + 1) * ρ = 2 * ((2 : ℝ) ^ t * ρ) := by rw [pow_succ]; ring
    have htpos : 0 < (2 : ℝ) ^ t * ρ := by positivity
    have hthalf : (2 : ℝ) ^ t * ρ ≤ 1 / 2 := by rw [he] at ht; linarith
    obtain ⟨L₁, N₁, f₁, g₁, γ₁, hf₁, hg₁, hγ₁, hX₁, hmass₁⟩ :=
      ih D (by linarith) hw hX hpos
    let D₁ := D.select ((2 : ℝ) ^ t * ρ) f₁ g₁ γ₁
    have hp₁ : 0 < ∑ i, ∑ j, volume (D₁.W i j) := by
      apply pos_iff_ne_zero.mpr
      intro hz
      change (∑ i, ∑ j, volume (D.W i (f₁ j))) = 0 at hz
      rw [hz, mul_zero] at hmass₁
      exact (not_le_of_gt hpos) hmass₁
    obtain ⟨L₂, N₂, f₂, g₂, γ₂, hf₂, hg₂, hγ₂, hX₂, hmass₂⟩ :=
      select_doubled_coarse D₁ htpos hthalf (fun k => hw (g₁ k)) hX₁ hp₁
    refine ⟨L₂, N₂, f₁ ∘ f₂, g₁ ∘ g₂, γ₂, hf₁.comp hf₂, hg₁.comp hg₂, ?_, ?_, ?_⟩
    · intro j
      change g₁ (g₂ (γ₂ j)) = D.γ (f₁ (f₂ j))
      rw [hγ₂ j]
      exact hγ₁ (f₂ j)
    · rw [he]
      exact hX₂
    · calc
        _ ≤ (((10 ^ 40 + 1 : ℕ) : ENNReal) ^ t) * ∑ i, ∑ j, volume (D₁.W i j) := hmass₁
        _ ≤ (((10 ^ 40 + 1 : ℕ) : ENNReal) ^ t) *
            (((10 ^ 40 + 1 : ℕ) : ENNReal) * ∑ i, ∑ j, volume (D₁.W i (f₂ j))) :=
          mul_le_mul' le_rfl hmass₂
        _ = _ := by
          rw [pow_succ (((10 ^ 40 + 1 : ℕ) : ENNReal)) t, mul_assoc]
          rfl

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
