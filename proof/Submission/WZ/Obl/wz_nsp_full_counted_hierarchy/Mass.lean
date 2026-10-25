-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Mass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Hierarchy
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Basic

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts)

/-- Global convex counts bound the total fine mass assigned to any parent. -/
theorem fiber_mass_bound {r ρ L : ℝ} {n k : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hL : 0 ≤ L) (x v : Fin n → Space) (f : Fin n → Fin k)
    (y w : Space) (hw : ‖w‖ = 1) (i : Fin k)
    (hsub : ∀ s, f s = i → Tube r (x s) (v s) ⊆ Tube ρ y w)
    (hcount : Counts r L n x v) :
    (Set.ncard {s | f s = i} : ℝ) * r ^ 2 ≤ 384 * L * ρ ^ 2 := by
  have hc : Set.ncard {s | f s = i} ≤ Set.ncard {s | Tube r (x s) (v s) ⊆ Tube ρ y w} :=
    Set.ncard_le_ncard (fun s hs => hsub s hs)
  have hv := WangZahlLot.Obl.wz_affine_packet_counting_transfer.tube_volume_upper hρ hρ1 y w hw
  have hh := (hcount (Tube ρ y w) ((convex_segment y (y + w)).thickening ρ))
  have he : ENNReal.ofReal ((Set.ncard {s | f s = i} : ℝ) * r ^ 2) ≤
      ENNReal.ofReal (384 * L * ρ ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal ((Set.ncard {s | Tube r (x s) (v s) ⊆ Tube ρ y w} : ℝ) * r ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (sq_nonneg r))
      _ ≤ ENNReal.ofReal L * volume (Tube ρ y w) := hh
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (384 * ρ ^ 2) := mul_le_mul' le_rfl hv
      _ = ENNReal.ofReal (384 * L * ρ ^ 2) := by
        rw [← ENNReal.ofReal_mul hL]
        congr 1
        ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he

/-- A factor-two regular fiber controls the common upper branch count. -/
theorem regular_fiber_mass_bound {r ρ L M : ℝ} {n k : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hL : 0 ≤ L) (x v : Fin n → Space) (f : Fin n → Fin k)
    (y w : Space) (hw : ‖w‖ = 1) (i : Fin k)
    (hsub : ∀ s, f s = i → Tube r (x s) (v s) ⊆ Tube ρ y w)
    (hcount : Counts r L n x v)
    (hregular : M / 2 ≤ (Set.ncard {s | f s = i} : ℝ)) :
    M * r ^ 2 ≤ 768 * L * ρ ^ 2 := by
  have hf := fiber_mass_bound hρ hρ1 hL x v f y w hw i hsub hcount
  have hm := mul_le_mul_of_nonneg_right hregular (sq_nonneg r)
  nlinarith

/-- A single tube has convex-count constant one at every positive radius. -/
theorem singleton_convex_counts {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : n = 1)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1) : Counts r 1 n x v := by
  classical
  intro W hW
  let S : Set (Fin n) := {i | Tube r (x i) (v i) ⊆ W}
  change ENNReal.ofReal ((S.ncard : ℝ) * r ^ 2) ≤ ENNReal.ofReal 1 * volume W
  rcases S.eq_empty_or_nonempty with he | ⟨i, hi⟩
  · simp only [he, Set.ncard_empty, Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]
    exact bot_le
  · have hc : S.ncard ≤ 1 := by simpa only [hn, Nat.card_fin] using Set.ncard_le_card S
    have hm : (S.ncard : ℝ) * r ^ 2 ≤ r ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (S.ncard : ℝ) ≤ 1 by exact_mod_cast hc) (sq_nonneg r)
    have hl := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hr (x i) (v i) (hv i)
    simpa only [ENNReal.ofReal_one, one_mul] using
      (ENNReal.ofReal_le_ofReal hm).trans (hl.trans (measure_mono hi))

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
