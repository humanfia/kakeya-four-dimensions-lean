import Submission.Obl.k4_narrow_projected_row_parents.NarrowVel
import Submission.Obl.k4_narrow_projected_row_parents.NaturalCommonScales
import Submission.Obl.k4_narrow_projected_row_parents.CompareMap

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Filter
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type} [MeasurableSpace α]

/-- Package the comparison on refined assignments into the sequence interface.
The exact natural scales are preserved, and collapsing the projected labels
does not increase the partner lists. -/
theorem compareSeq_of_refined (cfg : Model α) (s mOld : ℝ)
    (β χ ρ R M : ℕ → ℝ) (n n' : ℕ → ℕ)
    (C : (k : ℕ) → Fin (n k) → Set α)
    (C' : (k : ℕ) → Fin (n' k) → Set α)
    (toOld : (k : ℕ) → Fin (n' k) → Fin (n k))
    (hC : ∀ k i, C' k i ⊆ C k (toOld k i))
    (hM : ∀ k, 1 ≤ M k) (hMsub : Model.Subpow cfg.N M)
    (hR : ∀ k, 0 < R k)
    (sc : (k : ℕ) → CommonScaleChoice ((Model.prepared cfg).q k s) (β k)
      (cfg.N k ^ (-cfg.ℓ * s)) (χ k) (ρ k) (R k))
    (hχ : ∀ᶠ k in atTop, 0 < χ k ∧
      min (cfg.N k ^ (-mOld))
          (cfg.N k ^ (-s) * ((Model.prepared cfg).q k s * cfg.N k ^ (-cfg.ℓ * s))) /
        (2 * R k) ≤ χ k)
    (hRM : ∀ᶠ k in atTop, 2 * R k ≤ M k)
    (hcmp : ∀ᶠ k in atTop,
      Nonempty (Compared (Model.prepared cfg) k s (C' k) (sc k).q (χ k)
        (cfg.N k ^ (-cfg.ℓ * s)) (sc k).m (M k))) :
    CompareSeq cfg s mOld β n C := by
  refine ⟨M, hM, hMsub, ?_⟩
  filter_upwards [hχ, hRM, hcmp] with k hχk hRMk hcmpk
  refine ⟨(sc k).q, χ k, (sc k).q_pos, hχk.1, ?_, ?_, ?_⟩
  · rw [(sc k).natural_time]
    exact mul_le_mul_of_nonneg_right (by linarith [hR k]) (sc k).q_pos.le
  · have hnatural := (div_le_iff₀ (mul_pos (by norm_num) (hR k))).mp hχk.2
    calc
      _ ≤ χ k * (2 * R k) := hnatural
      _ ≤ χ k * M k := mul_le_mul_of_nonneg_left hRMk hχk.1.le
      _ = M k * χ k := mul_comm _ _
  · obtain ⟨cmp⟩ := hcmpk
    rw [(sc k).area]
    exact ⟨cmp.map_projected (toOld k) (hC k)⟩

end Submission.Obl.k4_narrow_projected_row_parents
