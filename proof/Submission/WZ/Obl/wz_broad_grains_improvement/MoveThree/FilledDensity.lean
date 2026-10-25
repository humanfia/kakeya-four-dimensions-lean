-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FilledDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FilledDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FilledDensity.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.Box

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal

/-- Density of an adapted filled prism survives flat normalization and a uniform
contraction, measured against the square of the new round-carrier radius. -/
theorem filled_round_density {δ a b r k D : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (hrhi : r ≤ 4 * a) (hk : 0 < k) (hD : 0 ≤ D)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V) (Γ B : Set V)
    (hvol : ∀ Q : Set V, μ (f '' Q) = O (k ^ 3 / (4 * a * b)) * μ Q)
    (hcover : f '' P (10 * δ) (6 * b * δ / r) 2 z e ⊆ B)
    (hden : O D * μ (P (10 * δ) (6 * b * δ / r) 2 z e) ≤
      μ (P (10 * δ) (6 * b * δ / r) 2 z e ∩ Γ)) :
    O ((D * k / 1000) * (64 * k * δ / a) ^ 2) ≤ μ (B ∩ f '' Γ) := by
  have hscale : (512 / 125 : ℝ) / a ^ 2 ≤ 30 / (a * r) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos ha) (mul_pos ha hr)]
    nlinarith [mul_le_mul_of_nonneg_left hrhi ha.le, sq_nonneg a]
  have hscalar : (D * k / 1000) * (64 * k * δ / a) ^ 2 ≤
      (k ^ 3 / (4 * a * b)) * (D * ((10 * δ) * (6 * b * δ / r) * 2)) := by
    calc
      _ = (D * k ^ 3 * δ ^ 2) * ((512 / 125 : ℝ) / a ^ 2) := by ring
      _ ≤ (D * k ^ 3 * δ ^ 2) * (30 / (a * r)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by field_simp <;> ring
  have hsub : f '' (P (10 * δ) (6 * b * δ / r) 2 z e ∩ Γ) ⊆ B ∩ f '' Γ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨hcover ⟨p, hp.1, rfl⟩, ⟨p, hp.2, rfl⟩⟩
  have hVP : μ (P (10 * δ) (6 * b * δ / r) 2 z e) =
      O ((10 * δ) * (6 * b * δ / r) * 2) :=
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P
      (by positivity) (by positivity) (by norm_num) z e
  calc
    _ ≤ O ((k ^ 3 / (4 * a * b)) * (D * ((10 * δ) * (6 * b * δ / r) * 2))) :=
      ENNReal.ofReal_le_ofReal hscalar
    _ = O (k ^ 3 / (4 * a * b)) *
        (O D * μ (P (10 * δ) (6 * b * δ / r) 2 z e)) := by
      rw [hVP]
      dsimp only [O, WangZahlLot.Obl.wz_move_three_thick_grains_gain.O]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hD]
    _ ≤ O (k ^ 3 / (4 * a * b)) * μ (P (10 * δ) (6 * b * δ / r) 2 z e ∩ Γ) :=
      mul_le_mul' le_rfl hden
    _ = μ (f '' (P (10 * δ) (6 * b * δ / r) 2 z e ∩ Γ)) := (hvol _).symm
    _ ≤ _ := measure_mono hsub

/-- Density of an adapted filled prism survives flat normalization and a uniform
contraction, measured against the square of the new round-carrier radius. -/
theorem filled_round_density_wide {δ a b r k D : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (hrhi : r ≤ 4 * a) (hk : 0 < k) (hD : 0 ≤ D)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V) (Γ B : Set V)
    (hvol : ∀ Q : Set V, μ (f '' Q) = O (k ^ 3 / (4 * a * b)) * μ Q)
    (hcover : f '' P (10 * δ) (6 * b * δ / r) 2 z e ⊆ B)
    (hden : O D * μ (P (10 * δ) (6 * b * δ / r) 2 z e) ≤
      μ (P (10 * δ) (6 * b * δ / r) 2 z e ∩ Γ)) :
    O ((D * k / 16000) * (256 * k * δ / a) ^ 2) ≤ μ (B ∩ f '' Γ)  := by
  have he : (D * k / 16000) * (256 * k * δ / a) ^ 2 =
      (D * k / 1000) * (64 * k * δ / a) ^ 2 := by ring
  rw [he]
  exact filled_round_density hδ ha hb hr hrhi hk hD z e f Γ B hvol hcover hden

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
