-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.Packing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs
import Submission.WZ.Obl.wz_convex_container_tube_packing.Packing
import Submission.WZ.Obl.wz_transverse_brush_selection.Geometry
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

/-!
# Packing bounds for essentially distinct coarse tubes

Three counting statements for a family of unit `ρ`-tubes `T ρ (y k) (w k)` which is
essentially distinct (`X ρ N y w`):

* `conflict_card`: after doubling the radius, a fixed tube has a large overlap with
  boundedly many others;
* `big_cover_card`: for `ρ > 1/2`, boundedly many such tubes meet the unit ball;
* `mult_card`: boundedly many of them contain a given fine tube.

All three follow from the endpoint-product packing of
`WangZahlLot.Obl.wz_convex_container_tube_packing`: the endpoint products of essentially
distinct tubes are disjoint, each has measure `≥ ρ⁴/10⁶`, and they lie in the square of a
container of volume `O(ρ²)`.
-/

set_option linter.unusedVariables false
noncomputable section
namespace WangZahlLot.Obl.wz_coarse_grains_assembly
open MeasureTheory

/-! ### Elementary tube geometry -/

/-- A point of a tube is close to a point of its axis. -/
theorem pk_param {r : ℝ} {x v q : V} (h : q ∈ T r x v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ‖q - (x + t • v)‖ < r := by
  obtain ⟨z, hz, hqz⟩ := Metric.mem_thickening_iff.mp h
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨t, ht.1, ht.2, ?_⟩
  simpa [dist_eq_norm] using hqz

/-- A point close to a point of the axis lies in the tube. -/
theorem pk_mem_T {r t : ℝ} {x v q : V} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ‖q - (x + t • v)‖ < r) : q ∈ T r x v := by
  refine Metric.mem_thickening_iff.mpr ⟨x + t • v, ?_, by rwa [dist_eq_norm]⟩
  rw [segment_eq_image']
  exact ⟨t, ⟨ht0, ht1⟩, by simp⟩

theorem pk_norm4 (a b c d : V) : ‖a - b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  linarith [norm_add_le (a - b + c) d, norm_add_le (a - b) c, norm_sub_le a b]

/-- Volume of a unit tube of any radius. -/
theorem pk_tube_vol_le {r : ℝ} (hr : 0 < r) (x v : V) (hv : ‖v‖ = 1) :
    μ (T r x v) ≤ ENNReal.ofReal (128 * (2 + r) * r ^ 2) := by
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
    (T := Set.Icc 0 1) subset_rfl (r := r) (A := 1) hr zero_le_one (by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have hseg : (fun t : ℝ => x + t • v) '' Set.Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  rw [hseg, show (2 : ℝ) * 1 + r = 2 + r by ring] at h
  exact h

/-- A tube whose two endpoints lie near a convex set lies near that set. -/
theorem pk_tube_subset_conv {ρ r : ℝ} {S : Set V} (hS : Convex ℝ S) {y w : V}
    (hy : y ∈ Metric.thickening r S) (hyw : y + w ∈ Metric.thickening r S) :
    T ρ y w ⊆ Metric.thickening (ρ + r) S := by
  intro q hq
  have h1 : segment ℝ y (y + w) ⊆ Metric.thickening r S :=
    (hS.thickening r).segment_subset hy hyw
  exact Metric.thickening_thickening_subset ρ r S (Metric.thickening_subset_of_subset ρ h1 hq)

/-- If a unit `ρ`-tube contains both endpoints of a unit segment, then it lies in the
`4ρ`-tube around that segment. -/
theorem pk_ends_subset {ρ : ℝ} {x v y w : V} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h0 : x ∈ T ρ y w) (h1 : x + v ∈ T ρ y w) :
    T ρ y w ⊆ T (4 * ρ) x v := by
  obtain ⟨s, hs0, hs1, hs⟩ := pk_param h0
  obtain ⟨t, ht0, ht1, ht⟩ := pk_param h1
  have hvt : ‖v - (t - s) • w‖ < 2 * ρ := by
    have heq : v - (t - s) • w = (x + v - (y + t • w)) - (x - (y + s • w)) := by module
    rw [heq]
    linarith [norm_sub_le (x + v - (y + t • w)) (x - (y + s • w))]
  have hlen : 1 < 2 * ρ + |t - s| := by
    have h := norm_sub_norm_le v ((t - s) • w)
    rw [hv, norm_smul, hw, mul_one, Real.norm_eq_abs] at h
    linarith
  have hsw : ∀ c : ℝ, 0 ≤ c → ‖c • w‖ = c := fun c hc => by
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg hc]
  have key : y ∈ Metric.thickening (3 * ρ) (segment ℝ x (x + v)) ∧
      y + w ∈ Metric.thickening (3 * ρ) (segment ℝ x (x + v)) := by
    rcases le_total s t with hst | hst
    · rw [abs_of_nonneg (show (0 : ℝ) ≤ t - s by linarith)] at hlen
      constructor
      · refine Metric.mem_thickening_iff.mpr ⟨x, left_mem_segment ℝ x (x + v), ?_⟩
        rw [dist_eq_norm]
        have heq : y - x = -(x - (y + s • w)) - s • w := by module
        rw [heq]
        have h6 := norm_sub_le (-(x - (y + s • w))) (s • w)
        rw [norm_neg, hsw s hs0] at h6
        linarith
      · refine Metric.mem_thickening_iff.mpr ⟨x + v, right_mem_segment ℝ x (x + v), ?_⟩
        rw [dist_eq_norm]
        have heq : y + w - (x + v) = -(x + v - (y + t • w)) + (1 - t) • w := by module
        rw [heq]
        have h6 := norm_add_le (-(x + v - (y + t • w))) ((1 - t) • w)
        rw [norm_neg, hsw (1 - t) (by linarith)] at h6
        linarith
    · rw [abs_of_nonpos (show t - s ≤ 0 by linarith)] at hlen
      constructor
      · refine Metric.mem_thickening_iff.mpr ⟨x + v, right_mem_segment ℝ x (x + v), ?_⟩
        rw [dist_eq_norm]
        have heq : y - (x + v) = -(x + v - (y + t • w)) - t • w := by module
        rw [heq]
        have h6 := norm_sub_le (-(x + v - (y + t • w))) (t • w)
        rw [norm_neg, hsw t ht0] at h6
        linarith
      · refine Metric.mem_thickening_iff.mpr ⟨x, left_mem_segment ℝ x (x + v), ?_⟩
        rw [dist_eq_norm]
        have heq : y + w - x = -(x - (y + s • w)) + (1 - s) • w := by module
        rw [heq]
        have h6 := norm_add_le (-(x - (y + s • w))) ((1 - s) • w)
        rw [norm_neg, hsw (1 - s) (by linarith)] at h6
        linarith
  have hsub := pk_tube_subset_conv (ρ := ρ) (convex_segment (𝕜 := ℝ) x (x + v)) key.1 key.2
  rw [show ρ + 3 * ρ = 4 * ρ by ring] at hsub
  exact hsub

/-- Three consecutive unit tubes along the line through `y₀` with direction `w₀`. -/
def pk_W3 (R : ℝ) (y₀ w₀ : V) : Set V :=
  T R (y₀ - w₀) w₀ ∪ T R y₀ w₀ ∪ T R (y₀ + w₀) w₀

theorem pk_W3_mem {R τ : ℝ} {q y₀ w₀ : V} (hτ0 : -1 ≤ τ) (hτ1 : τ ≤ 2)
    (hq : ‖q - (y₀ + τ • w₀)‖ < R) : q ∈ pk_W3 R y₀ w₀ := by
  unfold pk_W3
  rcases le_total τ 0 with h0 | h0
  · refine Or.inl (Or.inl (pk_mem_T (t := τ + 1) (by linarith) (by linarith) ?_))
    have heq : y₀ - w₀ + (τ + 1) • w₀ = y₀ + τ • w₀ := by module
    rw [heq]
    exact hq
  · rcases le_total τ 1 with h1 | h1
    · exact Or.inl (Or.inr (pk_mem_T h0 h1 hq))
    · refine Or.inr (pk_mem_T (t := τ - 1) (by linarith) (by linarith) ?_)
      have heq : y₀ + w₀ + (τ - 1) • w₀ = y₀ + τ • w₀ := by module
      rw [heq]
      exact hq

theorem pk_W3_vol {R : ℝ} (hR : 0 < R) (y₀ w₀ : V) (hw₀ : ‖w₀‖ = 1) :
    μ (pk_W3 R y₀ w₀) ≤ ENNReal.ofReal (3 * (128 * (2 + R) * R ^ 2)) := by
  unfold pk_W3
  have h1 := pk_tube_vol_le hR (y₀ - w₀) w₀ hw₀
  have h2 := pk_tube_vol_le hR y₀ w₀ hw₀
  have h3 := pk_tube_vol_le hR (y₀ + w₀) w₀ hw₀
  have hnn : 0 ≤ 128 * (2 + R) * R ^ 2 := by positivity
  calc μ (T R (y₀ - w₀) w₀ ∪ T R y₀ w₀ ∪ T R (y₀ + w₀) w₀)
      ≤ μ (T R (y₀ - w₀) w₀ ∪ T R y₀ w₀) + μ (T R (y₀ + w₀) w₀) := measure_union_le _ _
    _ ≤ μ (T R (y₀ - w₀) w₀) + μ (T R y₀ w₀) + μ (T R (y₀ + w₀) w₀) := by
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (128 * (2 + R) * R ^ 2) + ENNReal.ofReal (128 * (2 + R) * R ^ 2) +
          ENNReal.ofReal (128 * (2 + R) * R ^ 2) := by gcongr
    _ = ENNReal.ofReal (3 * (128 * (2 + R) * R ^ 2)) := by
        rw [← ENNReal.ofReal_add hnn hnn, ← ENNReal.ofReal_add (by positivity) hnn]
        congr 1
        ring

/-- A tube meeting the `2ρ`-thickening of another one, with nearly parallel direction, lies
in three consecutive tubes along the other one. -/
theorem pk_conflict_subset {ρ θ : ℝ} {y₀ w₀ y w : V}
    (hdir : min ‖w₀ - w‖ ‖w₀ + w‖ < θ)
    (hmeet : (T (2 * ρ) y₀ w₀ ∩ T (2 * ρ) y w).Nonempty) :
    T ρ y w ⊆ pk_W3 (5 * ρ + θ) y₀ w₀ := by
  obtain ⟨p, hp0, hp⟩ := hmeet
  obtain ⟨s₀, hs₀0, hs₀1, hs₀⟩ := pk_param hp0
  obtain ⟨s, hs0, hs1, hs⟩ := pk_param hp
  intro q hq
  obtain ⟨t, ht0, ht1, ht⟩ := pk_param hq
  have hts : |t - s| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rcases min_lt_iff.mp hdir with hd | hd
  · apply pk_W3_mem (τ := s₀ + (t - s)) (by linarith) (by linarith)
    have heq : q - (y₀ + (s₀ + (t - s)) • w₀) =
        (q - (y + t • w)) - (p - (y + s • w)) + (p - (y₀ + s₀ • w₀)) + (t - s) • (w - w₀) := by
      module
    rw [heq]
    have hd' : ‖(t - s) • (w - w₀)‖ < θ := by
      rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
      calc |t - s| * ‖w₀ - w‖ ≤ 1 * ‖w₀ - w‖ := mul_le_mul_of_nonneg_right hts (norm_nonneg _)
        _ < θ := by rw [one_mul]; exact hd
    have h4 := pk_norm4 (q - (y + t • w)) (p - (y + s • w)) (p - (y₀ + s₀ • w₀))
      ((t - s) • (w - w₀))
    linarith
  · apply pk_W3_mem (τ := s₀ - (t - s)) (by linarith) (by linarith)
    have heq : q - (y₀ + (s₀ - (t - s)) • w₀) =
        (q - (y + t • w)) - (p - (y + s • w)) + (p - (y₀ + s₀ • w₀)) + (t - s) • (w + w₀) := by
      module
    rw [heq]
    have hd' : ‖(t - s) • (w + w₀)‖ < θ := by
      rw [norm_smul, Real.norm_eq_abs, add_comm w w₀]
      calc |t - s| * ‖w₀ + w‖ ≤ 1 * ‖w₀ + w‖ := mul_le_mul_of_nonneg_right hts (norm_nonneg _)
        _ < θ := by rw [one_mul]; exact hd
    have h4 := pk_norm4 (q - (y + t • w)) (p - (y + s • w)) (p - (y₀ + s₀ • w₀))
      ((t - s) • (w + w₀))
    linarith

/-- A large overlap of two `2ρ`-tubes forces nearly parallel directions. -/
theorem pk_conflict_dir {ρ : ℝ} (hρ : 0 < ρ) {x v y w : V} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h : ENNReal.ofReal (2 * ρ ^ 2) < μ (T (2 * ρ) x v ∩ T (2 * ρ) y w)) :
    min ‖v - w‖ ‖v + w‖ < 32768 * ρ := by
  by_contra hcon
  rw [not_lt] at hcon
  by_cases hsmall : 16384 * ρ ≤ 1
  · have hb : 0 < 16384 * ρ := by positivity
    have hsep : 16384 * ρ ≤ min ‖v - w‖ ‖v + w‖ := le_trans (by linarith) hcon
    have hT := WangZahlLot.Obl.wz_transverse_brush_selection.transverse_intersection_volume
      (δ := 2 * ρ) (b := 16384 * ρ) (by positivity) hb hsmall (x := x) (y := y) hv hw hsep
    have heq : 4096 * (2 * ρ) ^ 3 / (16384 * ρ) = 2 * ρ ^ 2 := by
      rw [div_eq_iff hb.ne']
      ring
    rw [heq] at hT
    exact lt_irrefl _ (lt_of_lt_of_le h hT)
  · rw [not_le] at hsmall
    have h2 : min ‖v - w‖ ‖v + w‖ ≤ 2 := by
      have := norm_sub_le v w
      rw [hv, hw] at this
      exact (min_le_left _ _).trans (by linarith)
    linarith

theorem pk_half_lower {ρ : ℝ} (hρ : 0 < ρ) (x v : V) (hv : ‖v‖ = 1) :
    ENNReal.ofReal (2 * ρ ^ 2) ≤ 1/2 * μ (T (2 * ρ) x v) := by
  have h := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower
    (by positivity : 0 < 2 * ρ) x v hv
  calc ENNReal.ofReal (2 * ρ ^ 2) = ENNReal.ofReal ((1 / 2 : ℝ) * (2 * ρ) ^ 2) := by
        congr 1
        ring
    _ = (1 / 2 : ENNReal) * ENNReal.ofReal ((2 * ρ) ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
    _ ≤ 1/2 * μ (T (2 * ρ) x v) := by gcongr

/-! ### Endpoint-product packing -/

open WangZahlLot.Obl.wz_convex_container_tube_packing in
/-- Packing of essentially distinct unit tubes in a container of finite volume. -/
theorem pk_packing {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (y w : Fin N → V) (s : Finset (Fin N))
    {W : Set V} (hWfin : μ W ≠ ⊤) (hw : ∀ k, ‖w k‖ = 1)
    (hTW : ∀ k ∈ s, T δ (y k) (w k) ⊆ W)
    (hX : ∀ k k', k ≠ k' → μ (T δ (y k) (w k) ∩ T δ (y k') (w k')) ≤ 1/2 * μ (T δ (y k) (w k))) :
    (s.card : ENNReal) * ENNReal.ofReal (δ ^ 4 / 1000000) ≤ (μ W) ^ 2 := by
  classical
  have hdisj : (s : Set (Fin N)).PairwiseDisjoint (fun k => endpointProduct δ (y k) (w k)) := by
    intro i hi j hj hij
    exact endpointProduct_disjoint hδ (ne_top_of_le_ne_top hWfin (measure_mono (hTW i hi)))
      (hX i j hij)
  have hsub : (⋃ k ∈ s, endpointProduct δ (y k) (w k)) ⊆ W ×ˢ W := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz
    exact Set.prod_mono (hTW k hk) (hTW k hk) (endpointProduct_subset hδ (y k) (w k) hzk)
  calc (s.card : ENNReal) * ENNReal.ofReal (δ ^ 4 / 1000000)
      = ∑ k ∈ s, ENNReal.ofReal (δ ^ 4 / 1000000) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ s, (volume.prod volume) (endpointProduct δ (y k) (w k)) :=
        Finset.sum_le_sum (fun k _ => endpointProduct_volume_lower hδ (y k) (w k) (hw k))
    _ = (volume.prod volume) (⋃ k ∈ s, endpointProduct δ (y k) (w k)) :=
        (measure_biUnion_finset hdisj (fun k _ => endpointProduct_measurable δ (y k) (w k))).symm
    _ ≤ (volume.prod volume) (W ×ˢ W) := measure_mono hsub
    _ = (μ W) ^ 2 := by rw [Measure.prod_prod, pow_two]

/-- Turning the packing inequality into a count. -/
theorem pk_card_le {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) {n : ℕ} {W : Set V}
    (h1 : (n : ENNReal) * ENNReal.ofReal (δ ^ 4 / 1000000) ≤ (μ W) ^ 2)
    (h2 : μ W ≤ ENNReal.ofReal (C * δ ^ 2)) : (n : ℝ) ≤ 1000000 * C ^ 2 := by
  have h3 : (μ W) ^ 2 ≤ ENNReal.ofReal (C * δ ^ 2) ^ 2 := by gcongr
  have h4 : (n : ENNReal) * ENNReal.ofReal (δ ^ 4 / 1000000) =
      ENNReal.ofReal (n * (δ ^ 4 / 1000000)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  have h5 : ENNReal.ofReal (C * δ ^ 2) ^ 2 = ENNReal.ofReal ((C * δ ^ 2) ^ 2) :=
    (ENNReal.ofReal_pow (by positivity) 2).symm
  have h6 : ENNReal.ofReal (n * (δ ^ 4 / 1000000)) ≤ ENNReal.ofReal ((C * δ ^ 2) ^ 2) := by
    rw [← h4, ← h5]
    exact h1.trans h3
  have h7 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h6
  have hδ4 : 0 < δ ^ 4 := by positivity
  have h8 : (n : ℝ) * δ ^ 4 ≤ (1000000 * C ^ 2) * δ ^ 4 := by
    calc (n : ℝ) * δ ^ 4 = 1000000 * (n * (δ ^ 4 / 1000000)) := by ring
      _ ≤ 1000000 * (C * δ ^ 2) ^ 2 := by gcongr
      _ = (1000000 * C ^ 2) * δ ^ 4 := by ring
  exact le_of_mul_le_mul_right h8 hδ4

/-! ### (P3) Few coarse tubes contain a given fine tube -/

theorem pk_mult_aux {d ρ : ℝ} (hd : 0 < d) (hdρ : d ≤ ρ) (hρ1 : ρ ≤ 1) {N : ℕ}
    (y w : Fin N → V) (hw : ∀ k, ‖w k‖ = 1)
    (hX : ∀ k k', k ≠ k' → μ (T ρ (y k) (w k) ∩ T ρ (y k') (w k')) ≤ 1/2 * μ (T ρ (y k) (w k)))
    (x v : V) (hv : ‖v‖ = 1) (s : Finset (Fin N))
    (hs : ∀ k ∈ s, T d x v ⊆ T ρ (y k) (w k)) :
    (s.card : ℝ) ≤ 10 ^ 15 := by
  have hρ : 0 < ρ := hd.trans_le hdρ
  have hx0 : x ∈ T d x v := Metric.self_subset_thickening hd _ (left_mem_segment ℝ x (x + v))
  have hx1 : x + v ∈ T d x v :=
    Metric.self_subset_thickening hd _ (right_mem_segment ℝ x (x + v))
  have hTW : ∀ k ∈ s, T ρ (y k) (w k) ⊆ T (4 * ρ) x v := fun k hk =>
    pk_ends_subset hv (hw k) (hs k hk hx0) (hs k hk hx1)
  have hvol : μ (T (4 * ρ) x v) ≤ ENNReal.ofReal (12288 * ρ ^ 2) := by
    refine (pk_tube_vol_le (by positivity) x v hv).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [sq_nonneg ρ, mul_le_mul_of_nonneg_left hρ1 (sq_nonneg ρ)]
  have hfin : μ (T (4 * ρ) x v) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have h1 := pk_packing hρ y w s hfin hw hTW hX
  have h2 := pk_card_le hρ (by norm_num : (0 : ℝ) ≤ 12288) h1 hvol
  calc (s.card : ℝ) ≤ 1000000 * 12288 ^ 2 := h2
    _ ≤ 10 ^ 15 := by norm_num

open Classical in
/-- **(P3)** Few essentially distinct coarse tubes contain a given fine tube. -/
theorem mult_card {d ρ : ℝ} (hd : 0 < d) (hdρ : d ≤ ρ) (hρ1 : ρ ≤ 1) {N : ℕ} (y w : Fin N → V)
    (hw : ∀ k, ‖w k‖ = 1)
    (hX : ∀ k k', k ≠ k' → μ (T ρ (y k) (w k) ∩ T ρ (y k') (w k')) ≤ 1/2 * μ (T ρ (y k) (w k)))
    (x v : V) (hv : ‖v‖ = 1) :
    ((Finset.univ.filter (fun k : Fin N => T d x v ⊆ T ρ (y k) (w k))).card : ℝ) ≤ 10 ^ 15 :=
  pk_mult_aux hd hdρ hρ1 y w hw hX x v hv _ (fun k hk => (Finset.mem_filter.mp hk).2)

/-- `mult_card` in the `q`/`Set.ncard` form of the frozen predicates (no decidability). -/
theorem mult_ncard {d ρ : ℝ} (hd : 0 < d) (hdρ : d ≤ ρ) (hρ1 : ρ ≤ 1) {N : ℕ}
    (y w : Fin N → V) (hw : ∀ k, ‖w k‖ = 1)
    (hX : ∀ k k', k ≠ k' → μ (T ρ (y k) (w k) ∩ T ρ (y k') (w k')) ≤ 1/2 * μ (T ρ (y k) (w k)))
    (x v : V) (hv : ‖v‖ = 1) :
    q N {k | T d x v ⊆ T ρ (y k) (w k)} ≤ 10 ^ 15 := by
  classical
  have e : {k : Fin N | T d x v ⊆ T ρ (y k) (w k)} =
      ↑(Finset.univ.filter (fun k : Fin N => T d x v ⊆ T ρ (y k) (w k))) := by
    ext k
    simp
  show (({k : Fin N | T d x v ⊆ T ρ (y k) (w k)}).ncard : ℝ) ≤ 10 ^ 15
  rw [e, Set.ncard_coe_finset]
  exact pk_mult_aux hd hdρ hρ1 y w hw hX x v hv _ (fun k hk => (Finset.mem_filter.mp hk).2)

/-! ### (P1) Bounded conflict degree after doubling the radius -/

theorem pk_conflict_card_aux {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) {N : ℕ} (y w : Fin N → V)
    (hw : ∀ k, ‖w k‖ = 1)
    (hX : ∀ k k', k ≠ k' → μ (T ρ (y k) (w k) ∩ T ρ (y k') (w k')) ≤ 1/2 * μ (T ρ (y k) (w k)))
    (k₀ : Fin N) (s : Finset (Fin N))
    (hs : ∀ k ∈ s, ENNReal.ofReal (2 * ρ ^ 2) <
      μ (T (2 * ρ) (y k₀) (w k₀) ∩ T (2 * ρ) (y k) (w k))) :
    s.card ≤ 10 ^ 40 := by
  have hTW : ∀ k ∈ s, T ρ (y k) (w k) ⊆ pk_W3 (5 * ρ + 32768 * ρ) (y k₀) (w k₀) := by
    intro k hk
    have hbig := hs k hk
    have hdir := pk_conflict_dir hρ (hw k₀) (hw k) hbig
    have hne : (T (2 * ρ) (y k₀) (w k₀) ∩ T (2 * ρ) (y k) (w k)).Nonempty :=
      nonempty_of_measure_ne_zero (ne_of_gt (lt_of_le_of_lt zero_le hbig))
    exact pk_conflict_subset hdir hne
  have hR : 0 < 5 * ρ + 32768 * ρ := by positivity
  have hvolW : μ (pk_W3 (5 * ρ + 32768 * ρ) (y k₀) (w k₀)) ≤
      ENNReal.ofReal (10 ^ 16 * ρ ^ 2) := by
    refine (pk_W3_vol hR (y k₀) (w k₀) (hw k₀)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 2 + (5 * ρ + 32768 * ρ) ≤ 16389 := by linarith
    have h2 : (5 * ρ + 32768 * ρ) ^ 2 = 32773 ^ 2 * ρ ^ 2 := by ring
    rw [h2]
    have h3 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    calc 3 * (128 * (2 + (5 * ρ + 32768 * ρ)) * (32773 ^ 2 * ρ ^ 2))
        ≤ 3 * (128 * 16389 * (32773 ^ 2 * ρ ^ 2)) := by gcongr
      _ = (3 * 128 * 16389 * 32773 ^ 2) * ρ ^ 2 := by ring
      _ ≤ 10 ^ 16 * ρ ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) h3
  have hfin : μ (pk_W3 (5 * ρ + 32768 * ρ) (y k₀) (w k₀)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolW
  have h1 := pk_packing hρ y w s hfin hw hTW hX
  have h2 := pk_card_le hρ (by norm_num : (0 : ℝ) ≤ 10 ^ 16) h1 hvolW
  have h3 : (s.card : ℝ) ≤ 10 ^ 40 := h2.trans (by norm_num)
  exact_mod_cast h3

/-- **(P1)** Bounded conflict degree after doubling the radius. -/
theorem conflict_card {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) {N : ℕ} (y w : Fin N → V)
    (hw : ∀ k, ‖w k‖ = 1)
    (hX : ∀ k k', k ≠ k' → μ (T ρ (y k) (w k) ∩ T ρ (y k') (w k')) ≤ 1/2 * μ (T ρ (y k) (w k)))
    (k₀ : Fin N) :
    (Finset.univ.filter (fun k : Fin N =>
        1/2 * μ (T (2*ρ) (y k₀) (w k₀)) < μ (T (2*ρ) (y k₀) (w k₀) ∩ T (2*ρ) (y k) (w k)) ∨
        1/2 * μ (T (2*ρ) (y k) (w k)) < μ (T (2*ρ) (y k₀) (w k₀) ∩ T (2*ρ) (y k) (w k)))).card
      ≤ 10 ^ 40 := by
  apply pk_conflict_card_aux hρ hρ1 y w hw hX k₀
  intro k hk
  rcases (Finset.mem_filter.mp hk).2 with h | h
  · exact lt_of_le_of_lt (pk_half_lower hρ _ _ (hw k₀)) h
  · exact lt_of_le_of_lt (pk_half_lower hρ _ _ (hw k)) h

/-- `conflict_card` in the `q`/`Set.ncard` form of the frozen predicates. -/
theorem conflict_ncard {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) {N : ℕ} (y w : Fin N → V)
    (hw : ∀ k, ‖w k‖ = 1)
    (hX : ∀ k k', k ≠ k' → μ (T ρ (y k) (w k) ∩ T ρ (y k') (w k')) ≤ 1/2 * μ (T ρ (y k) (w k)))
    (k₀ : Fin N) :
    q N {k : Fin N |
        1/2 * μ (T (2*ρ) (y k₀) (w k₀)) < μ (T (2*ρ) (y k₀) (w k₀) ∩ T (2*ρ) (y k) (w k)) ∨
        1/2 * μ (T (2*ρ) (y k) (w k)) < μ (T (2*ρ) (y k₀) (w k₀) ∩ T (2*ρ) (y k) (w k))}
      ≤ 10 ^ 40 := by
  classical
  set P : Fin N → Prop := fun k =>
    1/2 * μ (T (2*ρ) (y k₀) (w k₀)) < μ (T (2*ρ) (y k₀) (w k₀) ∩ T (2*ρ) (y k) (w k)) ∨
      1/2 * μ (T (2*ρ) (y k) (w k)) < μ (T (2*ρ) (y k₀) (w k₀) ∩ T (2*ρ) (y k) (w k)) with hP
  have e : {k : Fin N | P k} = ↑(Finset.univ.filter P) := by
    ext k
    simp
  show (({k : Fin N | P k}).ncard : ℝ) ≤ 10 ^ 40
  rw [e, Set.ncard_coe_finset]
  have h := pk_conflict_card_aux hρ hρ1 y w hw hX k₀ (Finset.univ.filter P) (by
    intro k hk
    rcases (Finset.mem_filter.mp hk).2 with h | h
    · exact lt_of_le_of_lt (pk_half_lower hρ _ _ (hw k₀)) h
    · exact lt_of_le_of_lt (pk_half_lower hρ _ _ (hw k)) h)
  exact_mod_cast h

/-! ### (P2) Few fat coarse tubes near the unit ball -/

/-- **(P2)** Few essentially distinct fat tubes meet the unit ball. -/
theorem big_cover_card {ρ : ℝ} (hρ : 1/2 < ρ) (hρ1 : ρ ≤ 1) {N : ℕ} (y w : Fin N → V)
    (hw : ∀ k, ‖w k‖ = 1)
    (hX : ∀ k k', k ≠ k' → μ (T ρ (y k) (w k) ∩ T ρ (y k') (w k')) ≤ 1/2 * μ (T ρ (y k) (w k)))
    (hnear : ∀ k, ∃ p ∈ T ρ (y k) (w k), ‖p‖ < 1) :
    (N : ℝ) ≤ 10 ^ 13 := by
  have hρ0 : 0 < ρ := by linarith
  have hTW : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      T ρ (y k) (w k) ⊆ Metric.ball (0 : V) 4 := by
    intro k _ q hq
    obtain ⟨p, hp, hp1⟩ := hnear k
    obtain ⟨s, hs0, hs1, hs⟩ := pk_param hp
    obtain ⟨t, ht0, ht1, ht⟩ := pk_param hq
    rw [Metric.mem_ball, dist_zero_right]
    have heq : q = (q - (y k + t • w k)) - (p - (y k + s • w k)) + p + (t - s) • w k := by
      module
    have hts : ‖(t - s) • w k‖ ≤ 1 := by
      rw [norm_smul, hw k, mul_one, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have h4 := pk_norm4 (q - (y k + t • w k)) (p - (y k + s • w k)) p ((t - s) • w k)
    rw [← heq] at h4
    linarith
  have hvol : μ (Metric.ball (0 : V) 4) ≤ ENNReal.ofReal (1600 * ρ ^ 2) := by
    have hb : (volume : Measure V) (Metric.ball (0 : V) 4) =
        ENNReal.ofReal 4 ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) :=
      EuclideanSpace.volume_ball_fin_three 0 4
    show (volume : Measure V) (Metric.ball (0 : V) 4) ≤ _
    rw [hb, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hρ2 : 1 / 4 < ρ ^ 2 := by nlinarith
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hfin : μ (Metric.ball (0 : V) 4) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have h1 := pk_packing hρ0 y w Finset.univ hfin hw hTW hX
  have h2 := pk_card_le hρ0 (by norm_num : (0 : ℝ) ≤ 1600) h1 hvol
  rw [Finset.card_univ, Fintype.card_fin] at h2
  calc (N : ℝ) ≤ 1000000 * 1600 ^ 2 := h2
    _ ≤ 10 ^ 13 := by norm_num

end WangZahlLot.Obl.wz_coarse_grains_assembly
