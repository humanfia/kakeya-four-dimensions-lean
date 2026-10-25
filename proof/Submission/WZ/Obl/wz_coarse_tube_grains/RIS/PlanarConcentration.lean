-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PlanarConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BrushSelection
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Basic

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

/-- A small-volume broad family concentrates in a thin slab. Both angular
scales and the numerical error budgets are explicit; no grains or hierarchy
are assumed. -/
theorem planar_concentration_numeric :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      ∀ b₀ b₁ δ lam U r : ℝ, 0 < b₀ → b₀ ≤ 1 → 0 < b₁ → b₁ ≤ 1 →
        0 < δ → δ ≤ 1 / 100 → 0 < lam → lam ≤ 1 → 0 < U → 0 < r → r ≤ 1 →
        128 * (8 * (δ + r) / b₀ + δ) ≤ a * lam / 2 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
        (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
        (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
        ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (U * δ) →
        (∀ p u, ‖u‖ = 1 →
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b₀}.ncard : ℝ) ≤
            (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) →
        (∀ p u, ‖u‖ = 1 →
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b₁}.ncard : ℝ) ≤
            (a ^ 2 * b₀ * lam ^ 3 / (4 * U) / 1536) * incidence Y p) →
        ∃ (e : Space) (t : ℝ) (F : Finset (Fin n)), ‖e‖ = 1 ∧
          (∀ i ∈ F, Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 15 * δ / r}) ∧
          ENNReal.ofReal (b₁ * (a ^ 2 * b₀ * lam ^ 3 / (4 * U)) ^ 3 / (25165824 * U)) *
            (∑ i, volume (Y i)) ≤ ∑ i ∈ F, volume (Y i) := by
  obtain ⟨a, ha, ha1, hselect⟩ := selected_off_stem_brush
  refine ⟨a, ha, ha1, ?_⟩
  intro b₀ b₁ δ lam U r hb₀ hb₀1 hb₁ hb₁1 hδ hδ100 hlam hlam1 hU hr hr1
    hbudget n x v Y hn hv hT hY hYT hdense hvol hbroad hcap
  have hδ1 : δ ≤ 1 := by linarith
  let L := a ^ 2 * b₀ * lam ^ 3 / (4 * U)
  have hL : 0 < L := by dsimp [L]; positivity
  let θ := L / 768
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono ((hYT i).trans (hT i)))
  have hmassY : shadingMass Y ≤ 384 * (n : ℝ) * δ ^ 2 := by
    have hsingle : ∀ i, (volume (Y i)).toReal ≤ 384 * δ ^ 2 := fun i =>
      ENNReal.toReal_le_of_le_ofReal (by positivity)
        ((measure_mono (hYT i)).trans
          (wz_affine_packet_counting_transfer.tube_volume_upper hδ hδ1 (x i) (v i) (hv i)))
    simpa [shadingMass, mul_assoc, mul_comm, mul_left_comm] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsingle i)
  obtain ⟨i₀, Z, hZ, hZout, hstem, hmassZ⟩ :=
    hselect b₀ δ lam U r hb₀ hb₀1 hδ hδ100 hlam hlam1 hU hr hbudget n x v Y
      hn hv hT hY hYT hdense hvol hbroad
  have hmassZ' : 2 * L * (n : ℝ) * δ ^ 2 ≤ shadingMass Z := by
    convert hmassZ using 1
    dsimp [L]
    ring
  obtain ⟨W, hW, hkeep, hrelative⟩ := relative_incidence_refinement hY
    (fun i => (hZ i).1) hYfin (fun i => (hZ i).2) hθ
  have hWY : ∀ i, W i ⊆ Y i := fun i => (hW i).2.trans (hZ i).2
  have hWfin : ∀ i, volume (W i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hYfin i) (measure_mono (hWY i))
  have hsumW : (∑ i, volume (W i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hWfin i
  have hWmass : L * (n : ℝ) * δ ^ 2 ≤ shadingMass W := by
    have hcost := mul_le_mul_of_nonneg_left hmassY hθ
    have he : θ * (384 * (n : ℝ) * δ ^ 2) = L / 2 * (n : ℝ) * δ ^ 2 := by
      dsimp [θ]
      ring
    rw [he] at hcost
    nlinarith [mul_nonneg hL.le (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity)]
  have hWrelative : L / 384 * shadingMass Y ≤ shadingMass W := by
    calc
      _ ≤ L / 384 * (384 * (n : ℝ) * δ ^ 2) :=
        mul_le_mul_of_nonneg_left hmassY (by positivity)
      _ = L * (n : ℝ) * δ ^ 2 := by ring
      _ ≤ _ := hWmass
  have hWbroad := broadness_of_relative_incidence v hWY hrelative
    (show L / 1536 ≤ θ / 2 by exact le_of_eq (by dsimp [θ]; ring))
    (by simpa only [L] using hcap)
  have hWdense : ENNReal.ofReal (L * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (W i) := by
    apply (ENNReal.ofReal_le_iff_le_toReal hsumW).mpr
    simpa only [shadingMass, ENNReal.toReal_sum (fun i _ => hWfin i)] using hWmass
  have hWvol : volume (⋃ i, W i) ≤ ENNReal.ofReal (U * δ) :=
    (measure_mono (iUnion_mono hWY)).trans hvol
  obtain ⟨e, t, F, he, hslab, hFmass⟩ := off_stem_broad_planar_average hδ hr hr1 hb₁ hb₁1
    hL hU hn x v W (x i₀) (v i₀) hv (fun i => (hW i).1)
    (fun i => (hW i).2.trans (hZout i)) hWdense hWvol
    (fun i hi => hstem i (hi.mono (hW i).2)) hWbroad
  have hFWfin : (∑ i ∈ F, volume (W i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hWfin i
  have hFreal : b₁ * L ^ 2 / (65536 * U) * shadingMass W ≤ ∑ i ∈ F, (volume (W i)).toReal := by
    have hh := ENNReal.toReal_mono hFWfin hFmass
    simpa only [shadingMass, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ b₁ * L ^ 2 / (65536 * U)),
      ENNReal.toReal_sum (fun i _ => hWfin i)] using hh
  have hfinal : b₁ * L ^ 3 / (25165824 * U) * shadingMass Y ≤ ∑ i ∈ F, (volume (Y i)).toReal := by
    calc
      _ = b₁ * L ^ 2 / (65536 * U) * (L / 384 * shadingMass Y) := by ring
      _ ≤ b₁ * L ^ 2 / (65536 * U) * shadingMass W :=
        mul_le_mul_of_nonneg_left hWrelative (by positivity)
      _ ≤ _ := hFreal
      _ ≤ _ := Finset.sum_le_sum fun i _ => ENNReal.toReal_mono (hYfin i) (measure_mono (hWY i))
  refine ⟨e, t, F, he, hslab, ?_⟩
  change ENNReal.ofReal (b₁ * L ^ 3 / (25165824 * U)) *
    (∑ i, volume (Y i)) ≤ ∑ i ∈ F, volume (Y i)
  have hsumY : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  have hFYfin : (∑ i ∈ F, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsumY) hFYfin).mp
  simpa only [shadingMass, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ b₁ * L ^ 3 / (25165824 * U)),
    ENNReal.toReal_sum (fun i _ => hYfin i)] using hfinal

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
