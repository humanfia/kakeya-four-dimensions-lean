-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Elementary.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.TubeCells
import Submission.WZ.Obl.wz_nonflat_factored_improvement.AffineNet

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- Average shading mass gives a lower bound for the union without a rescaling hypothesis. -/
theorem average_union_lower {n : ℕ} (hn : 0 < n) (Z : Fin n → Set Space)
    {a : ℝ} (h : a * n ≤ ∑ i, volume.real (Z i))
    (hfin : volume (⋃ i, Z i) ≠ ⊤) : ENNReal.ofReal a ≤ volume (⋃ i, Z i) := by
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  have hs : (∑ i, volume.real (Z i)) ≤ (n : ℝ) * volume.real (⋃ i, Z i) := by
    calc
      _ ≤ ∑ _i : Fin n, volume.real (⋃ i, Z i) :=
        Finset.sum_le_sum fun i _ => measureReal_mono (subset_iUnion Z i) hfin
      _ = _ := by simp
  have hh := h.trans hs
  rw [mul_comm a] at hh
  exact (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hn)).mp hh

/-- The elementary cell estimate remains available at ratios close to one. -/
theorem elementary_cells {b δ lam θ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hδ : 0 < δ) (hlam : 0 < lam) (hθ : 0 < θ)
    {K : ℕ} (hK : 0 < K) (hcut : 288 * θ ^ K * b ^ 2 ≤ lam * δ ^ 2 / 2)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (a u : Space) (hu : ‖u‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hYB : ∀ i, Y i ⊆ ball (0 : Space) 5) (hYP : ∀ i, Y i ⊆ tube b a u)
    (hind : ∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) :
    ∃ s : Finset (Fin 3 → ℤ),
      (∀ z ∈ s, (tube b a u ∩ gridCell b z).Nonempty) ∧
      ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s) ∧
      ∀ z ∈ s, ENNReal.ofReal (lam * θ / (576 * K) * (δ / b) ^ 2) * volume (gridCell b z) ≤
        volume ((⋃ i, Y i) ∩ gridCell b z) := by
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  obtain ⟨s, hs, hmass, hlocal⟩ := tube_cells_of_estimate hb hb1 hδ hlam hθ
    (F := lam * δ ^ 2 / (2 * K)) (by positivity) hK hcut hn x v Y a u hu hv
    hYm hYT hYB hYP hind (by
      intro Z hZm hZY hmass
      apply average_union_lower hn Z
      · convert hmass using 1 <;> ring
      · exact ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (iUnion_subset fun i =>
          (hZY i).trans (hYB i))))
  refine ⟨s, hs, hmass, ?_⟩
  intro z hz
  convert hlocal z hz using 2
  congr 1
  field_simp
  ring

/-- Packing bounds the dimensionless cardinality within a parent tube. -/
theorem relative_packing_bound {b δ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hδ : 0 < δ)
    {n : ℕ} (x v : Fin n → Space) (a u : Space)
    (hu : ‖u‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (hTP : ∀ i, tube δ (x i) (v i) ⊆ tube b a u)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) :
    (n : ℝ) * (δ / b) ^ 4 ≤ 3136000000 := by
  have hvol := tube_volume_upper hb.le hb1 a u hu
  have hp := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ x v
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol) hv hTP hover
  have hh : ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal (3136000000 * b ^ 4) := by
    apply hp.trans
    calc
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal (56 * b ^ 2)) ^ 2 := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  rw [div_pow, ← mul_div_assoc]
  exact (div_le_iff₀ (pow_pos hb 4)).mpr hr

/-- A uniform bound on the dimensionless cardinality bounds all exponents used here. -/
theorem normalized_power_le {N C s : ℝ} (hN : 0 ≤ N) (hC : 1 ≤ C)
    (hNC : N ≤ C) (hs : 0 ≤ s) (hs1 : s ≤ 1) : N ^ s ≤ C := by
  by_cases hN1 : N ≤ 1
  · exact (Real.rpow_le_one hN hN1 hs).trans hC
  · have h1N := (not_le.mp hN1).le
    exact (Real.rpow_le_rpow_of_exponent_le h1N hs1).trans (by simpa using hNC)

/-- Positive cellwise mass ensures that the cell meets the actual parent tube. -/
theorem cell_meets_parent {b d : ℝ} (hb : 0 < b) (hd : 0 < d)
    {S P : Set Space} (hSP : S ⊆ P) (z : Fin 3 → ℤ)
    (h : ENNReal.ofReal d * volume (gridCell b z) ≤ volume (S ∩ gridCell b z)) :
    (P ∩ gridCell b z).Nonempty := by
  have hpos : 0 < volume (S ∩ gridCell b z) := by
    apply lt_of_lt_of_le _ h
    rw [gridCell_volume hb.le]
    rw [← ENNReal.ofReal_mul hd.le]
    exact ENNReal.ofReal_pos.mpr (mul_pos hd (pow_pos hb 3))
  by_contra hnone
  have hS : S ∩ gridCell b z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact hnone ⟨p, hSP hp.1, hp.2⟩
  rw [hS, measure_empty] at hpos
  exact (lt_irrefl 0) hpos

end WangZahlLot.Obl.wz_separated_scales_gain
