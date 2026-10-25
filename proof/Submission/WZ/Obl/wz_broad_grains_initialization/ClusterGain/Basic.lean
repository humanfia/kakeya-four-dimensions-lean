-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.PrismCarrier
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CordobaSlab
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

/-!
# Cluster gain: basic geometry

A doubled carrier met by a slab that contains one of the carrier's fine unit tubes has volume
`≥ min(ρ,r)ρ/8`. This drives the relative slab count of a cluster from the global Frostman bound.
-/

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

namespace WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain

theorem exists_unit_orth_two (u v : Space) :
    ∃ n : Space, ‖n‖ = 1 ∧ inner ℝ n u = 0 ∧ inner ℝ n v = 0 := by
  classical
  set S : Submodule ℝ Space := Submodule.span ℝ {u, v}
  have hS : Module.finrank ℝ S ≤ 2 := by
    have := finrank_span_le_card (R := ℝ) ({u, v} : Set Space)
    refine this.trans ?_
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hdim : Module.finrank ℝ S + Module.finrank ℝ Sᗮ = 3 := by
    rw [Submodule.finrank_add_finrank_orthogonal]; simp
  have hpos : 0 < Module.finrank ℝ Sᗮ := by omega
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hpos)
  have hmu : inner ℝ m u = 0 :=
    (Submodule.mem_orthogonal' S m).mp hm u (Submodule.subset_span (by simp))
  have hmv : inner ℝ m v = 0 :=
    (Submodule.mem_orthogonal' S m).mp hm v (Submodule.subset_span (by simp))
  have hnm : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  refine ⟨‖m‖⁻¹ • m, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnm.ne']
  · rw [real_inner_smul_left, hmu, mul_zero]
  · rw [real_inner_smul_left, hmv, mul_zero]

/-- A point within `ρ` of a carrier lies in the doubled carrier. -/
theorem mem_dilated_carrier {L ρ : ℝ} (hL : 0 < L) {y w p q : Space}
    (hq : q ∈ Carrier L ρ y w) (hpq : ‖p - q‖ < ρ) :
    p ∈ Carrier (2 * L) (2 * ρ) y w := by
  obtain ⟨c, hc, hqc⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at hc
  obtain ⟨s, hs, rfl⟩ := hc
  apply mem_thickening_iff.mpr
  refine ⟨y + ((1 - L) / 2) • w + s • (L • w), ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨s / 2 + 1 / 4, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    simp only [add_sub_cancel_left, smul_smul]
    have : y + ((1 - 2 * L) / 2) • w + ((s / 2 + 1 / 4) * (2 * L)) • w =
        y + ((1 - L) / 2) • w + (s * L) • w := by
      rw [add_assoc, add_assoc, ← add_smul, ← add_smul]; congr 2; ring
    rw [this]
  · simp only [add_sub_cancel_left] at hqc
    rw [dist_eq_norm] at hqc ⊢
    calc ‖p - (y + ((1 - L) / 2) • w + s • L • w)‖
        ≤ ‖p - q‖ + ‖q - (y + ((1 - L) / 2) • w + s • L • w)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ρ + ρ := add_lt_add hpq hqc
      _ = 2 * ρ := by ring


/-- A doubled carrier meets a slab containing one of its unit tubes in volume `≳ min(ρ,r)ρ`. -/
theorem carrier_slab_volume {δ ρ r L : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hr : 0 < r) (hL : 0 < L)
    {x v y w u : Space} {t : ℝ} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hcar : thickening δ (segment ℝ x (x + v)) ⊆ Carrier L ρ y w)
    (hslab : thickening δ (segment ℝ x (x + v)) ⊆ {p | |inner ℝ u p - t| ≤ r}) :
    ENNReal.ofReal (min ρ r * ρ / 8) ≤
      volume (Carrier (2 * L) (2 * ρ) y w ∩ {p | |inner ℝ u p - t| ≤ r}) := by
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • v ∈ thickening δ (segment ℝ x (x + v)) := by
    intro s hs
    apply self_subset_thickening hδ
    rw [segment_eq_image']
    exact ⟨s, hs, by simp⟩
  set κ := inner ℝ u v with hκ
  set φ₀ := inner ℝ u x - t with hφ₀
  have h0 : |φ₀| ≤ r := by
    have := hslab (hseg 0 ⟨le_refl _, zero_le_one⟩)
    simpa [φ₀] using this
  have h1 : |φ₀ + κ| ≤ r := by
    have := hslab (hseg 1 ⟨zero_le_one, le_refl _⟩)
    simp only [one_smul, mem_ofPred_eq, inner_add_right] at this
    have e : inner ℝ u x + inner ℝ u v - t = φ₀ + κ := by simp only [φ₀, κ]; ring
    rwa [e] at this
  have hκr : |κ| ≤ 2 * r := by
    have := abs_sub (φ₀ + κ) φ₀
    simp only [add_sub_cancel_left] at this
    linarith
  set φm := φ₀ + κ / 2 with hφm
  have hφm : |φm| + |κ| / 2 ≤ r := by
    rcases le_total 0 κ with hk | hk
    · rw [abs_of_nonneg hk]
      rcases abs_le.mp h0 with ⟨a0, b0⟩
      rcases abs_le.mp h1 with ⟨a1, b1⟩
      rcases le_total 0 φm with hm | hm
      · rw [abs_of_nonneg hm]; linarith
      · rw [abs_of_nonpos hm]; linarith
    · rw [abs_of_nonpos hk]
      rcases abs_le.mp h0 with ⟨a0, b0⟩
      rcases abs_le.mp h1 with ⟨a1, b1⟩
      rcases le_total 0 φm with hm | hm
      · rw [abs_of_nonneg hm]; linarith
      · rw [abs_of_nonpos hm]; linarith
  obtain ⟨n, hn, hnu, hnv⟩ := exists_unit_orth_two u v
  have hvn : inner ℝ v n = 0 := by rw [real_inner_comm]; exact hnv
  obtain ⟨b, hb1, hb2⟩ := Factor.exists_frame hv hn hvn
  set ν := b 0 with hν
  have hνn : ‖ν‖ = 1 := b.orthonormal.1 0
  set α := inner ℝ u ν with hα
  have hα1 : |α| ≤ 1 := by
    have := abs_real_inner_le_norm u ν
    rw [hu, hνn, one_mul] at this
    exact this
  set ℓ := min ρ r / 2 with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  have hℓρ : ℓ ≤ ρ / 2 := by have := min_le_left ρ r; linarith
  have hℓr : ℓ ≤ r / 2 := by have := min_le_right ρ r; linarith
  -- the offset of the box along `ν`, pushing the slab value towards the middle
  obtain ⟨ca, hca, hgood⟩ : ∃ ca : ℝ, |ca| ≤ ℓ / 2 ∧
      ∀ a, |a - ca| ≤ ℓ / 2 → |φm + α * a| + |κ| / 4 ≤ r := by
    have hαa := abs_le.mp hα1
    have key : ∀ a, (φm ≥ 0 → -ℓ ≤ α * a ∧ α * a ≤ 0) → (φm < 0 → 0 ≤ α * a ∧ α * a ≤ ℓ) →
        |φm + α * a| + |κ| / 4 ≤ r := by
      intro a hp hn'
      rcases le_or_gt 0 φm with hm | hm
      · obtain ⟨l1, l2⟩ := hp hm
        rcases le_or_gt 0 (φm + α * a) with hs | hs
        · rw [abs_of_nonneg hs]; linarith [le_abs_self φm, abs_nonneg κ]
        · rw [abs_of_neg hs]; linarith [abs_nonneg κ]
      · obtain ⟨l1, l2⟩ := hn' hm
        rcases le_or_gt 0 (φm + α * a) with hs | hs
        · rw [abs_of_nonneg hs]; linarith [abs_nonneg κ]
        · rw [abs_of_neg hs]; linarith [neg_abs_le φm, abs_nonneg κ]
    rcases le_or_gt 0 φm with hm | hm <;> rcases le_or_gt 0 α with ha | ha
    · refine ⟨-(ℓ / 2), by rw [abs_neg, abs_of_pos (by positivity)], fun a h => key a ?_ ?_⟩
      · intro _
        obtain ⟨h1, h2⟩ := abs_le.mp h
        have p1 := mul_nonneg ha (show 0 ≤ a + ℓ by linarith)
        have p2 := mul_nonneg (show 0 ≤ 1 - α by linarith) hℓ0.le
        have p3 := mul_nonneg ha (show 0 ≤ -a by linarith)
        constructor <;> linarith
      · intro h'; exact absurd hm (not_le.mpr h')
    · refine ⟨ℓ / 2, by rw [abs_of_pos (by positivity)], fun a h => key a ?_ ?_⟩
      · intro _
        obtain ⟨h1, h2⟩ := abs_le.mp h
        have p1 := mul_nonneg (show 0 ≤ α + 1 by linarith) (show 0 ≤ a by linarith)
        have p3 := mul_nonneg (show 0 ≤ -α by linarith) (show 0 ≤ a by linarith)
        constructor <;> linarith
      · intro h'; exact absurd hm (not_le.mpr h')
    · refine ⟨ℓ / 2, by rw [abs_of_pos (by positivity)], fun a h => key a ?_ ?_⟩
      · intro h'; exact absurd h' (not_le.mpr hm)
      · intro _
        obtain ⟨h1, h2⟩ := abs_le.mp h
        have p1 := mul_nonneg ha (show 0 ≤ a by linarith)
        have p2 := mul_nonneg (show 0 ≤ 1 - α by linarith) (show 0 ≤ a by linarith)
        constructor <;> linarith
    · refine ⟨-(ℓ / 2), by rw [abs_neg, abs_of_pos (by positivity)], fun a h => key a ?_ ?_⟩
      · intro h'; exact absurd h' (not_le.mpr hm)
      · intro _
        obtain ⟨h1, h2⟩ := abs_le.mp h
        have p1 := mul_nonneg (show 0 ≤ -α by linarith) (show 0 ≤ -a by linarith)
        have p2 := mul_nonneg (show 0 ≤ α + 1 by linarith) (show 0 ≤ -a by linarith)
        constructor <;> linarith
  have hun : inner ℝ u n = 0 := by rw [real_inner_comm]; exact hnu
  set z : Space := x + (1 / 2 : ℝ) • v + ca • ν with hz
  have hsub : Factor.box ℓ (1 / 2) (ρ / 2) z b.repr ⊆
      Carrier (2 * L) (2 * ρ) y w ∩ {p | |inner ℝ u p - t| ≤ r} := by
    intro p hp
    obtain ⟨hp0, hp1, hp2⟩ := hp
    set c0 := b.repr (p - z) 0 with hc0
    set c1 := b.repr (p - z) 1 with hc1
    set c2 := b.repr (p - z) 2 with hc2
    have hexp : p - z = c0 • ν + c1 • v + c2 • n := by
      have := (b.sum_repr (p - z)).symm
      rw [Fin.sum_univ_three, hb1, hb2] at this
      exact this
    have hp_eq : p = z + (c0 • ν + c1 • v + c2 • n) := by rw [← hexp]; abel
    constructor
    · -- carrier
      have hc1' : (1 / 2 + c1) ∈ Icc (0 : ℝ) 1 := by
        have := abs_le.mp hp1
        constructor <;> linarith [this.1, this.2]
      have hq := hcar (hseg _ hc1')
      apply mem_dilated_carrier hL hq
      have heq : p - (x + (1 / 2 + c1) • v) = (c0 + ca) • ν + c2 • n := by
        rw [hp_eq, hz]; module
      rw [heq]
      calc ‖(c0 + ca) • ν + c2 • n‖ ≤ ‖(c0 + ca) • ν‖ + ‖c2 • n‖ := norm_add_le _ _
        _ = |c0 + ca| + |c2| := by
          rw [norm_smul, norm_smul, hνn, hn, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one]
        _ ≤ (|c0| + |ca|) + |c2| := by gcongr; exact abs_add_le _ _
        _ < ρ := by linarith
    · -- slab
      show |inner ℝ u p - t| ≤ r
      have hval : inner ℝ u p - t = (φm + α * (ca + c0)) + κ * c1 := by
        rw [hp_eq, hz]
        simp only [inner_add_right, inner_smul_right, hun]
        simp only [φm, φ₀, κ, α]
        ring
      rw [hval]
      have hg := hgood (ca + c0) (by rw [add_sub_cancel_left]; exact hp0)
      calc |φm + α * (ca + c0) + κ * c1| ≤ |φm + α * (ca + c0)| + |κ * c1| := abs_add_le _ _
        _ ≤ |φm + α * (ca + c0)| + |κ| / 4 := by
          rw [abs_mul]
          gcongr
          calc |κ| * |c1| ≤ |κ| * (1 / 4) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg κ)
                linarith
            _ = |κ| / 4 := by ring
        _ ≤ r := hg
  calc ENNReal.ofReal (min ρ r * ρ / 8) = volume (Factor.box ℓ (1 / 2) (ρ / 2) z b.repr) := by
        rw [Factor.box_volume hℓ0.le (by norm_num) (by positivity)]
        congr 1
        rw [hℓ]; ring
    _ ≤ _ := measure_mono hsub

end WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain
