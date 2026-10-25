-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ThinNeighborhood.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AngularAnnuli

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

theorem cTube_coordinate_bounds {b : ℝ} {c p : V} {u : Fin 3 → V}
    (hu : Orthonormal ℝ u) (hp : p ∈ cTube b c u) :
    (∀ i : Fin 3, i ≠ 2 → |inner ℝ (u i) (p - c)| ≤ 4 * b) ∧
      ‖p - c‖ ≤ 4 * b + 1 / 2 := by
  let v := axisDir u
  have hv : ‖v‖ = 1 := norm_axisDir hu
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hstart : c - (1 / 2 : ℝ) • v ∈ closedBall c (1 / 2 : ℝ) := by
    change ‖c - (1 / 2 : ℝ) • v - c‖ ≤ 1 / 2
    rw [show c - (1 / 2 : ℝ) • v - c = -((1 / 2 : ℝ) • v) by abel]
    simp [norm_smul, hv]
  have hend : c - (1 / 2 : ℝ) • v + v ∈ closedBall c (1 / 2 : ℝ) := by
    change ‖c - (1 / 2 : ℝ) • v + v - c‖ ≤ 1 / 2
    rw [show c - (1 / 2 : ℝ) • v + v - c = (1 / 2 : ℝ) • v by module]
    simp [norm_smul, hv]
  have hqc : ‖q - c‖ ≤ 1 / 2 :=
    (convex_closedBall c (1 / 2 : ℝ)).segment_subset hstart hend hq
  have hpq' : ‖p - q‖ ≤ 4 * b := by simpa only [dist_eq_norm] using hpq.le
  refine ⟨?_, (norm_sub_le_norm_sub_add_norm_sub p q c).trans (add_le_add hpq' hqc)⟩
  intro i hi
  have hiv : inner ℝ (u i) v = 0 := by
    have hz := (orthonormal_iff_ite.mp hu) i 2
    simp only [hi, ite_false] at hz
    dsimp [v, axisDir]
    split_ifs <;> simp only [inner_neg_right, hz, neg_zero]
  change inner ℝ (u i) (axisDir u) = 0 at hiv
  have hplane : Convex ℝ {z : V | inner ℝ (u i) (z - c) = 0} := by
    have hh : Convex ℝ ((fun z : V => inner ℝ (u i) z) ⁻¹' ({0} : Set ℝ)) :=
      (convex_singleton (0 : ℝ)).linear_preimage (innerSL ℝ (u i)).toLinearMap
    have ht := hh.translate_preimage_left (-c)
    change Convex ℝ {z : V | inner ℝ (u i) (z + -c) = 0} at ht
    simpa only [sub_eq_add_neg] using ht
  have hq0 : inner ℝ (u i) (q - c) = 0 := hplane.segment_subset
    (by simp [inner_sub_right, inner_smul_right, hiv])
    (by simp [inner_sub_right, inner_add_right, inner_smul_right, hiv]) hq
  have he : inner ℝ (u i) (p - c) = inner ℝ (u i) (p - q) + inner ℝ (u i) (q - c) := by
    simp only [inner_sub_right]
    ring
  rw [he, hq0, add_zero]
  calc
    _ ≤ ‖u i‖ * ‖p - q‖ := abs_real_inner_le_norm _ _
    _ = ‖p - q‖ := by rw [hu.1 i, one_mul]
    _ ≤ 4 * b := hpq'

/-- The containing neighbourhood has the same angular factor as the filling
estimate, so division by its volume loses no further angular power. -/
theorem thin_neighborhood_volume_upper {a b θ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1 / 1000)
    (haθ : a ≤ 2 * θ * b) (c : V) (u : Fin 3 → V) (hu : Orthonormal ℝ u) :
    μ ({p | |inner ℝ (u 0) (p - c)| ≤ 3 * a + 2 * θ * b} ∩ cTube b c u) ≤
      O (256 * θ * b ^ 2) := by
  have hc := volume_le_of_coords hu ![c, c, c] ![3 * a + 2 * θ * b, 4 * b, 1]
    ({p | |inner ℝ (u 0) (p - c)| ≤ 3 * a + 2 * θ * b} ∩ cTube b c u) (by
      intro p hp i
      have hh := cTube_coordinate_bounds hu hp.2
      fin_cases i
      · exact hp.1
      · exact hh.1 1 (by decide)
      · calc
          _ ≤ ‖u 2‖ * ‖p - c‖ := abs_real_inner_le_norm _ _
          _ = ‖p - c‖ := by rw [hu.1 2, one_mul]
          _ ≤ 4 * b + 1 / 2 := hh.2
          _ ≤ 1 := by linarith)
  apply hc.trans
  apply ENNReal.ofReal_le_ofReal
  change 8 * ((3 * a + 2 * θ * b) * (4 * b) * 1) ≤ 256 * θ * b ^ 2
  nlinarith [mul_le_mul_of_nonneg_right haθ hb.le]

theorem thin_neighborhood_density_of_filling {a b θ q : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1 / 1000) (haθ : a ≤ 2 * θ * b) (hq : 0 ≤ q)
    (c : V) (u : Fin 3 → V) (hu : Orthonormal ℝ u) (E : Set V)
    (hfill : O (q * θ * b ^ 2) ≤
      μ (({p | |inner ℝ (u 0) (p - c)| ≤ 3 * a + 2 * θ * b} ∩ cTube b c u) ∩ E)) :
    O (q / 256) * μ ({p | |inner ℝ (u 0) (p - c)| ≤ 3 * a + 2 * θ * b} ∩ cTube b c u) ≤
      μ (({p | |inner ℝ (u 0) (p - c)| ≤ 3 * a + 2 * θ * b} ∩ cTube b c u) ∩ E) := by
  calc
    _ ≤ O (q / 256) * O (256 * θ * b ^ 2) :=
      mul_le_mul' le_rfl (thin_neighborhood_volume_upper hb hb1 haθ c u hu)
    _ = O (q * θ * b ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ q / 256)]
      congr 1
      ring
    _ ≤ _ := hfill

/-- Pointwise transverse incidence fills a thin prism neighbourhood with
density independent of the selected absolute angle. -/
theorem transverse_global_density {n : ℕ} {a b h lam s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hlam : 0 < lam) (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ s * b)
    (c : Fin n → V) (u : Fin n → Fin 3 → V) (H : Fin n → Set V)
    (c₀ : V) (u₀ : Fin 3 → V) (H₀ : Set V)
    (hu : ∀ i, Orthonormal ℝ (u i)) (hHm : ∀ i, MeasurableSet (H i))
    (hHU : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i p, p ∈ H i →
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hH₀m : MeasurableSet H₀) (hH₀ : H₀ ⊆ prism a b c₀ u₀)
    (hdense₀ : O lam * μ (prism a b c₀ u₀) ≤ μ H₀)
    (htrans : ∀ p ∈ H₀, ∃ i, p ∈ H i ∧ s ≤ pd (u i 0) (u₀ 0)) :
    ∃ θ : ℝ, s / 2 ≤ θ ∧ θ ≤ 1 ∧
      O (((lam / (Scale.dyExp 1 (s / 2) + 1 : ℕ) / 16000) ^ 2 * h ^ 2 /
        (52428800000000 * (257 ^ 4 : ℕ) * (1 + Real.log (b / a)))) / 256) *
        μ ({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + 2 * θ * b} ∩ cTube b c₀ u₀) ≤
        μ (({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + 2 * θ * b} ∩ cTube b c₀ u₀) ∩
          ⋃ i, H i) := by
  obtain ⟨θ, hsθ, hθ1, hfill⟩ := transverse_global_filling ha hab hb hh hlam hs hs1
    c u H c₀ u₀ H₀ hu hHm hHU hregular hu₀ hH₀m hH₀ hdense₀ htrans
  have hb0 : 0 < b := ha.trans_le hab
  have hlog : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).mpr hab)
  refine ⟨θ, hsθ, hθ1, ?_⟩
  apply thin_neighborhood_density_of_filling hb0 (hb.trans (by norm_num))
    (by nlinarith [mul_le_mul_of_nonneg_right hsθ hb0.le]) (by positivity) c₀ u₀ hu₀ (⋃ i, H i)
  convert hfill using 1
  · congr 1
    ring
  · rw [inter_assoc]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
