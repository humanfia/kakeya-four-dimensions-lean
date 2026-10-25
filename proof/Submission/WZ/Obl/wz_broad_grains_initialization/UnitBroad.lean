-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.UnitBroad.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketPower
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitCover

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_measurable_angular_selection (pd)
open wz_clustered_cover_volume_gain (T)

/-- Packets at a sufficiently large angular scale are already broad at the
unit scale, after spending the prescribed error. -/
theorem PacketRefinement.unit_broad {n : ℕ} {β δ θ ε : ℝ} {v : Fin n → Space}
    {Y Z : Fin n → Set Space} {P : Space → Finset (Finset (Fin n))}
    {a : Space → Finset (Fin n) → Fin n} (h : PacketRefinement β δ θ v Y Z P a)
    (hδ : 0 < δ) (hβ : 0 < β) (hθ : δ ^ (ε / (2 * β)) ≤ θ)
    (hconst : 2 ≤ δ ^ (-(ε / 2))) (p u : Space) (r : ℝ) (hr : δ ≤ r) :
    ({i | p ∈ Z i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
      δ ^ (-ε) * r ^ β * ({i | p ∈ Z i}.ncard : ℝ) := by
  have hθpos : 0 < θ := (Real.rpow_pos_of_pos hδ _).trans_le hθ
  have hrpos : 0 < r := hδ.trans_le hr
  have hi : θ ^ (-β) ≤ δ ^ (-(ε / 2)) := by
    calc
      _ ≤ (δ ^ (ε / (2 * β))) ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hδ _) hθ (by linarith)
      _ = _ := by
        rw [← Real.rpow_mul hδ.le]
        congr 1
        field_simp
  have hc : 2 * θ ^ (-β) ≤ δ ^ (-ε) := by
    calc
      _ ≤ δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) :=
        mul_le_mul hconst hi (Real.rpow_nonneg hθpos.le _) (by positivity)
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  calc
    _ ≤ 2 * (r / θ) ^ β * ({i | p ∈ Z i}.ncard : ℝ) := h.broad_union p u r hr
    _ = (2 * θ ^ (-β)) * r ^ β * ({i | p ∈ Z i}.ncard : ℝ) := by
      rw [Real.div_rpow hrpos.le hθpos.le, Real.rpow_neg hθpos.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hrpos.le _)) (Nat.cast_nonneg _)

/-- A retained shading fits the exact initialization cover at radius one. -/
theorem unit_scale_cover_refinement {δ h : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h)
    {n : ℕ} (x v : Fin n → Space) (Y Z : Fin n → Set Space)
    (hYm : ∀ i, MeasurableSet (Y i))
    (hball : ∀ i, T δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1)
    (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i)
    (hmass : ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i)) :
    ∃ y w : Fin 1 → Space,
      Cover δ h n x v Y Finset.univ Z 1 1 y w (fun _ => 0) True := by
  obtain ⟨y, w, hcover⟩ := unit_scale_cover hδ hδ1 hh x v Y hYm hball
  refine ⟨y, w, ?_⟩
  exact ⟨fun i => ⟨(hZ i).1, (hZ i).2, by simp⟩, by simpa using hmass, hcover.2.2⟩

end WangZahlLot.Obl.wz_broad_grains_initialization
