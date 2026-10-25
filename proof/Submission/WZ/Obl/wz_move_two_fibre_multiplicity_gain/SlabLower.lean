-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain.SlabLower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_fibre_multiplicity_gain.Defs
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Nondegenerate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorBox

/-!
# A slab count lower bound for admissible families

A single tube lies in a slab of half-width `δ`, so the Frostman slab condition with
constant `L` forces `1 ≤ L n (8 δ)`.

Ported from x0418's `SlabLower.lean` on o152's branches (namespace renamed).
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- A tube lies in the slab of half-width `δ` around any plane containing its axis. -/
lemma tube_subset_slab {δ : ℝ} {x v u : Space} (hu : ‖u‖ = 1) (huv : inner ℝ u v = 0) :
    Tube δ x v ⊆ {p | |inner ℝ u p - inner ℝ u x| ≤ δ} := by
  intro q hq
  obtain ⟨s, hs, hqs⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at hs
  obtain ⟨τ, -, rfl⟩ := hs
  have he : inner ℝ u q - inner ℝ u x = inner ℝ u (q - (x + τ • (x + v - x))) := by
    simp only [add_sub_cancel_left, inner_sub_right, inner_add_right, inner_smul_right, huv,
      mul_zero, add_zero]
  show |inner ℝ u q - inner ℝ u x| ≤ δ
  rw [he]
  calc |inner ℝ u (q - (x + τ • (x + v - x)))| ≤ ‖u‖ * ‖q - (x + τ • (x + v - x))‖ :=
        abs_real_inner_le_norm _ _
    _ = dist q (x + τ • (x + v - x)) := by rw [hu, one_mul, dist_eq_norm]
    _ ≤ δ := hqs.le

/-- The slab count forces `1 ≤ L n (8 δ)`. -/
lemma one_le_slab_count {δ η M L : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hA : Admissible δ η M L n x v Y) : 1 ≤ L * n * (8 * δ) := by
  obtain ⟨hn, hT, -, -, -, hF⟩ := hA
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨u, hu, hvu⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.exists_orth_unit (hT i₀).1
  have huv : inner ℝ u (v i₀) = 0 := hvu
  set t := inner ℝ u (x i₀)
  have hsub : Tube δ (x i₀) (v i₀) ⊆ ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ δ} :=
    fun q hq => ⟨(hT i₀).2.1 hq, tube_subset_slab hu huv hq⟩
  have hpos : 0 < Set.ncard {i | Tube δ (x i) (v i) ⊆ ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ δ}} :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨i₀, hsub⟩
  have h1 := hF u t δ hu hδ
  have h2 := WangZahlLot.Obl.wz_grains_nonsingular_slices.nd_slab_volume_le hu t δ hδ.le
  have h3 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (L * n) * ENNReal.ofReal (8 * δ) := by
    refine le_trans ?_ (h1.trans (by gcongr))
    apply ENNReal.ofReal_le_ofReal
    exact_mod_cast hpos
  by_contra hlt
  rw [not_le] at hlt
  rcases le_or_gt (L * n) 0 with hL | hL
  · rw [ENNReal.ofReal_of_nonpos hL, zero_mul] at h3
    simp at h3
  · rw [← ENNReal.ofReal_mul hL.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    linarith

end WangZahlLot.Obl.wz_move_two_fibre_multiplicity_gain
