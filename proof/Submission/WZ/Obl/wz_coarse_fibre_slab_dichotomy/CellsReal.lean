-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.CellsReal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.Cells
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.Extraction

/-!
# Real-valued forms of the cell bookkeeping
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells

local notation "Sp" => LeanEval.Analysis.WangZahlKakeya.Space

section
variable {n m : ℕ} {C : Fin m → ShadedCell (Fin n)} {F : Finset (Fin n)}
  {U Y : Fin n → Set Sp} {θ : ℝ} {Good : Finset (Fin n) → Set Sp → Prop}

lemma cells_mass_real (hθ : 0 ≤ θ) (hC : ∀ j, (C j).Valid F U Y (ENNReal.ofReal θ) Good)
    (hdisj : Pairwise (fun j k => Disjoint (C j).support (C k).support))
    (hUt : ∀ i, volume (U i) ≠ ⊤) (hYU : ∀ i, Y i ⊆ U i) (J : Finset (Fin m)) :
    θ * ∑ j ∈ J, ∑ i ∈ (C j).indices, (volume (U i)).toReal ≤
      ∑ i ∈ J.biUnion (fun j => (C j).indices), (volume (Y i)).toReal := by
  have h := cells_mass_le hC hdisj J
  have hYt : ∀ i, volume (Y i) ≠ ⊤ := fun i => ne_top_of_le_ne_top (hUt i) (measure_mono (hYU i))
  have hfin : ∑ i ∈ J.biUnion (fun j => (C j).indices), volume (Y i) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => hYt i)
  have := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ, ENNReal.toReal_sum (fun j _ =>
    ENNReal.sum_ne_top.mpr (fun i _ => hUt i)), ENNReal.toReal_sum (fun i _ => hYt i)] at this
  simpa only [ENNReal.toReal_sum (fun i _ => hUt i)] using this

lemma cells_card_real (hθ : 0 ≤ θ) (hC : ∀ j, (C j).Valid F U Y (ENNReal.ofReal θ) Good)
    (hdisj : Pairwise (fun j k => Disjoint (C j).support (C k).support))
    (hYU : ∀ i ∈ F, Y i ⊆ U i) (hU0 : ∀ i, volume (U i) ≠ 0) (hUt : ∀ i, volume (U i) ≠ ⊤)
    (J : Finset (Fin m)) :
    θ * ∑ j ∈ J, ((C j).indices.card : ℝ) ≤ ((J.biUnion (fun j => (C j).indices)).card : ℝ) := by
  have h := cells_card_le hC hdisj hYU hU0 hUt J
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ, ENNReal.toReal_sum
    (fun j _ => ENNReal.natCast_ne_top _)] at this
  simpa using this

/-- The greedy mass inequality, for `2θ`-dense shadings, in real form. -/
lemma fibre_mass_real {L : ℝ} (hθ : 0 ≤ θ) (hL : 0 ≤ L)
    (hUt : ∀ i, volume (U i) ≠ ⊤) (hYU : ∀ i, Y i ⊆ U i)
    (hdense : ∀ i ∈ F, ENNReal.ofReal (2 * θ) * volume (U i) ≤ volume (Y i))
    (hmass : ∑ i ∈ F, volume (Y i) ≤ ENNReal.ofReal θ * ∑ i ∈ F, volume (U i) +
        ENNReal.ofReal L * ∑ j, ∑ i ∈ (C j).indices, volume (U i)) :
    ∑ i ∈ F, (volume (Y i)).toReal ≤ 2 * L * ∑ j, ∑ i ∈ (C j).indices, (volume (U i)).toReal := by
  have hYt : ∀ i, volume (Y i) ≠ ⊤ := fun i => ne_top_of_le_ne_top (hUt i) (measure_mono (hYU i))
  have hsU : ∀ (s : Finset (Fin n)), ∑ i ∈ s, volume (U i) ≠ ⊤ :=
    fun s => ENNReal.sum_ne_top.mpr (fun i _ => hUt i)
  have hcells : ∑ j, ∑ i ∈ (C j).indices, volume (U i) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => hsU _)
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (hsU F), ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcells⟩) hmass
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hsU F))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcells), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hθ, ENNReal.toReal_ofReal hL, ENNReal.toReal_sum (fun i _ => hYt i),
    ENNReal.toReal_sum (fun i _ => hUt i), ENNReal.toReal_sum (fun j _ => hsU _)] at hr
  simp only [ENNReal.toReal_sum (fun i _ => hUt i)] at hr
  have hd : 2 * θ * ∑ i ∈ F, (volume (U i)).toReal ≤ ∑ i ∈ F, (volume (Y i)).toReal := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have := ENNReal.toReal_mono (hYt i) (hdense i hi)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  linarith

end

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
