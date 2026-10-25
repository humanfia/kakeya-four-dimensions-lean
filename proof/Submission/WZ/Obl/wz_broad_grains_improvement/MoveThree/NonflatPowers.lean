-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NonflatPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NonflatPowers.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NormalizedBlockDensity

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- The concentration gain absorbs both packing errors and a moderate
aspect ratio loss. -/
theorem nonflat_density_factor {δ ζ σ ω ε t M P r : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 < ζ) (hσ : 0 < σ) (hω : 0 ≤ ω)
    (hε : ε ≤ ζ / 16) (ht : t ≤ ζ * σ / 16)
    (hM : δ ^ (-ζ) ≤ M) (hP : 0 < P) (hPbound : P ≤ δ ^ (-ε))
    (hr : δ ^ (ζ * σ / (4 * (σ + ω))) ≤ r) :
    δ ^ (-(ζ * σ / 4)) ≤ δ ^ t * M ^ (σ / 2) * P ^ (-σ) *
      r ^ ((σ + ω) / 2) := by
  have hMpos : 0 < M := (Real.rpow_pos_of_pos hδ _).trans_le hM
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hδ _).trans_le hr
  have hMp : δ ^ (-(ζ * σ / 2)) ≤ M ^ (σ / 2) := by
    calc
      _ = (δ ^ (-ζ)) ^ (σ / 2) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hM (by positivity)
  have hPp : δ ^ (ε * σ) ≤ P ^ (-σ) := by
    calc
      _ = (δ ^ (-ε)) ^ (-σ) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hP hPbound (by linarith)
  have hrp : δ ^ (ζ * σ / 8) ≤ r ^ ((σ + ω) / 2) := by
    calc
      _ = (δ ^ (ζ * σ / (4 * (σ + ω)))) ^ ((σ + ω) / 2) := by
        rw [← Real.rpow_mul hδ.le]
        congr 1
        field_simp
        ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hr (by positivity)
  calc
    _ ≤ δ ^ (t - ζ * σ / 2 + ε * σ + ζ * σ / 8) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
    _ = δ ^ t * δ ^ (-(ζ * σ / 2)) * δ ^ (ε * σ) * δ ^ (ζ * σ / 8) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1
    _ ≤ _ := by gcongr

theorem sharp_nonflat_density_factor {δ ζ σ ε t M P r : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 < ζ) (hσ : 0 < σ)
    (hε : ε ≤ ζ / 16) (ht : t ≤ ζ * σ / 16)
    (hM : δ ^ (-ζ) ≤ M) (hP : 0 < P) (hPbound : P ≤ δ ^ (-ε))
    (hr : δ ^ (ζ / 4) ≤ r) :
    δ ^ (-(ζ * σ / 4)) ≤ δ ^ t * M ^ (σ / 2) * P ^ (-σ) * r ^ (σ / 2) := by
  have he : ζ * σ / (4 * (σ + 0)) = ζ / 4 := by simp only [add_zero]; field_simp
  simpa only [add_zero] using nonflat_density_factor (ω := 0) hδ hδ1 hζ hσ le_rfl
    hε ht hM hP hPbound (by simpa only [he] using hr)

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
