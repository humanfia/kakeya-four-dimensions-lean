-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.TubeCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Geometry
import Submission.WZ.Obl.wz_separated_scales_gain.CellSelection

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- Turn any lower estimate for restricted shadings into a uniform density on coarse cells. -/
theorem tube_cells_of_estimate {b δ lam θ F : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hδ : 0 < δ) (hlam : 0 < lam) (hθ : 0 < θ) (hF : 0 ≤ F)
    {K : ℕ} (hK : 0 < K) (hcut : 288 * θ ^ K * b ^ 2 ≤ lam * δ ^ 2 / 2)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (a u : Space) (hu : ‖u‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hYB : ∀ i, Y i ⊆ ball (0 : Space) 5) (hYP : ∀ i, Y i ⊆ tube b a u)
    (hind : ∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i))
    (hestimate : ∀ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) →
      (∀ i, Z i ⊆ Y i) → lam * n * δ ^ 2 / (2 * K) ≤ ∑ i, volume.real (Z i) →
        ENNReal.ofReal F ≤ volume (⋃ i, Z i)) :
    ∃ s : Finset (Fin 3 → ℤ),
      (∀ z ∈ s, (tube b a u ∩ gridCell b z).Nonempty) ∧
      ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s) ∧
      ∀ z ∈ s, ENNReal.ofReal (θ * F / (288 * b ^ 2)) * volume (gridCell b z) ≤
        volume ((⋃ i, Y i) ∩ gridCell b z) := by
  classical
  let s₀ := (gridKeys (b / 6)).filter (fun z => (tube b a u ∩ gridCell b z).Nonempty)
  have hmeet (z : Fin 3 → ℤ) (hz : z ∈ s₀) := (Finset.mem_filter.mp hz).2
  have hcover (i : Fin n) : Y i ⊆ gridUnion b s₀ := by
    intro p hp
    refine mem_iUnion₂.mpr ⟨gridKey b p, ?_, mem_gridCell_key hb p⟩
    exact Finset.mem_filter.mpr ⟨gridKey_mem_five hb hb1 (hYB i hp),
      ⟨p, hYP i hp, mem_gridCell_key hb p⟩⟩
  obtain ⟨e, he⟩ := tube_in_square_prism hb1 a u hu
  have hvol : volume.real (gridUnion b s₀) ≤ 288 * b ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [measureReal_def, ENNReal.ofReal_toReal (gridUnion_volume_ne_top hb s₀)]
    exact gridUnion_prism_volume hb le_rfl hb1 s₀ e (fun z hz => by
      obtain ⟨p, hp, hpz⟩ := hmeet z hz
      exact ⟨p, he hp, hpz⟩)
  have hYfin (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top (gridUnion_volume_ne_top hb s₀) (measure_mono (hcover i))
  have hmass : lam * n * δ ^ 2 ≤ ∑ i, volume.real (Y i) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (ENNReal.ofReal_le_iff_le_toReal (hYfin i)).mp (hind i))
    simpa only [measureReal_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (n : ℝ) * (lam * δ ^ 2) = lam * n * δ ^ 2 by ring] using hh
  have hcut' : (n : ℝ) * θ ^ K * (288 * b ^ 2) ≤ (lam * n * δ ^ 2) / 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg n)]
  obtain ⟨s, t, hss, ht, hretain, hd, htotal⟩ :=
    bounded_cell_selection hb hθ hK s₀ Y hYm hcover hvol hmass hcut'
  let Z : Fin n → Set Space := fun i => Y i ∩ gridUnion b s
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hYm i).inter (gridUnion_measurable b s)
  have hZsub : ∀ i, Z i ⊆ Y i := fun _ => inter_subset_left
  have hZfin : volume (⋃ i, Z i) ≠ ⊤ :=
    ne_top_of_le_ne_top (gridUnion_volume_ne_top hb s) (measure_mono (iUnion_subset fun _ => inter_subset_right))
  have hFbound : F ≤ volume.real (⋃ i, Z i) :=
    (ENNReal.ofReal_le_iff_le_toReal hZfin).mp (hestimate Z hZm hZsub hretain)
  have heZ : (⋃ i, Y i) ∩ gridUnion b s = ⋃ i, Z i := by
    simp only [Z, iUnion_inter]
  rw [heZ] at htotal
  have hFt : θ * F / (288 * b ^ 2) ≤ t := by
    apply (div_le_iff₀ (by positivity : 0 < 288 * b ^ 2)).mpr
    exact (mul_le_mul_of_nonneg_left hFbound hθ.le).trans htotal
  have hcoarse : lam / (32 * K) * b ^ 2 ≤ volume.real (gridUnion b s) := by
    have hh : (∑ i, volume.real (Z i)) ≤
        (n : ℝ) * (16 * δ ^ 2 / b ^ 2) * volume.real (gridUnion b s) := by
      calc
        _ ≤ ∑ _i : Fin n, (16 * δ ^ 2 / b ^ 2) * volume.real (gridUnion b s) :=
          Finset.sum_le_sum fun i _ =>
            (measureReal_mono (inter_subset_inter_left _ (hYT i))
              (ne_top_of_le_ne_top (gridUnion_volume_ne_top hb s) (measure_mono inter_subset_right))).trans
                (tube_gridUnion_volumeReal hb δ (x i) (v i) (hv i) s)
        _ = _ := by simp; ring
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < (n : ℝ) * (16 * δ ^ 2 / b ^ 2))).mp
    have heq : (n : ℝ) * (16 * δ ^ 2 / b ^ 2) * (lam / (32 * K) * b ^ 2) =
        lam * n * δ ^ 2 / (2 * K) := by field_simp; ring
    rw [heq]
    exact hretain.trans hh
  refine ⟨s, fun z hz => hmeet z (hss hz),
    (ENNReal.ofReal_le_iff_le_toReal (gridUnion_volume_ne_top hb s)).mpr hcoarse, ?_⟩
  intro z hz
  rw [gridCell_volume hb.le, ← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_le_iff_le_toReal
    (ne_top_of_le_ne_top (gridCell_volume_ne_top hb z) (measure_mono inter_subset_right))).mpr
  exact (mul_le_mul_of_nonneg_right hFt (by positivity)).trans (hd z hz)

end WangZahlLot.Obl.wz_separated_scales_gain
