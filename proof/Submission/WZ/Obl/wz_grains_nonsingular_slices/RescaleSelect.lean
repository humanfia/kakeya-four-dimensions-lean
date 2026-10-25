-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.RescaleSelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Defs

/-!
# Selecting distinct representatives with balanced clusters

From a finite family of unit `δ`-tubes, select representatives that are pairwise half-volume
distinct, each carrying a cluster of the family contained in a fixed homothetic enlargement of
the representative, with all selected clusters of comparable size and covering a
`1 / log` fraction of the family.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- Parameters of the axis of the tube `(x, v)` lying `2δ`-close to the axis of `(y, w)`. -/
private def rselS (δ : ℝ) (x v y w : Space) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧ x + t • v ∈ thickening (2 * δ) (segment ℝ y (y + w))}

/-- The parameter set of `(x, v)` relative to `(y, w)` has two points more than `10⁻⁴` apart. -/
private def rselWide (δ : ℝ) (x v y w : Space) : Prop :=
  ∃ s ∈ rselS δ x v y w, ∃ t ∈ rselS δ x v y w, (1 / 10000 : ℝ) < |s - t|

private lemma rsel_mem_seg {y w : Space} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    y + s • w ∈ segment ℝ y (y + w) := by
  rw [segment_eq_image']
  exact ⟨s, hs, by simp⟩

private lemma rsel_mem_thick {y w q : Space} {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (h : ‖q - (y + s • w)‖ < r) : q ∈ thickening r (segment ℝ y (y + w)) :=
  mem_thickening_iff.mpr ⟨y + s • w, rsel_mem_seg hs, by rwa [dist_eq_norm]⟩

private lemma rsel_inter_subset (δ : ℝ) (x v y w : Space) :
    Tube δ x v ∩ Tube δ y w ⊆ thickening δ ((fun t : ℝ => x + t • v) '' rselS δ x v y w) := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp.1
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp.2
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  apply mem_thickening_iff.mpr
  refine ⟨x + t • v, ⟨t, ⟨ht, ?_⟩, rfl⟩, hpq⟩
  apply mem_thickening_iff.mpr
  refine ⟨z, hz, ?_⟩
  have := dist_triangle (x + t • v) p z
  rw [dist_comm (x + t • v) p] at this
  linarith

private lemma rsel_half {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) {x v y w : Space}
    (hv : ‖v‖ = 1)
    (hdiam : ∀ s ∈ rselS δ x v y w, ∀ t ∈ rselS δ x v y w, |s - t| ≤ 1 / 10000) :
    volume (Tube δ x v ∩ Tube δ y w) ≤ (1 / 2 : ℝ≥0∞) * volume (Tube δ x v) := by
  have hlow := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ x v hv
  suffices h : volume (Tube δ x v ∩ Tube δ y w) ≤ ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ 2) by
    calc _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ 2) := h
      _ = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (δ ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      _ ≤ _ := by gcongr
  have hsub := rsel_inter_subset δ x v y w
  rcases le_or_gt δ (1 / 1000) with hsmall | hlarge
  · calc _ ≤ volume (thickening δ ((fun t : ℝ => x + t • v) '' rselS δ x v y w)) :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (128 * (2 * (1 / 10000) + δ) * δ ^ 2) :=
        WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
          (fun _ ht => ht.1) hδ (by norm_num)
          (fun s hs t ht => by rw [Real.dist_eq]; exact hdiam s hs t ht)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
        linarith
  · rcases (rselS δ x v y w).eq_empty_or_nonempty with he | ⟨t₀, ht₀⟩
    · rw [he, image_empty, thickening_empty] at hsub
      rw [subset_empty_iff.mp hsub, measure_empty]
      exact bot_le
    · have hball : thickening δ ((fun t : ℝ => x + t • v) '' rselS δ x v y w) ⊆
          ball (x + t₀ • v) (1 / 10000 + δ) := by
        intro p hp
        obtain ⟨_, ⟨t, ht, rfl⟩, hpt⟩ := mem_thickening_iff.mp hp
        rw [mem_ball]
        have h1 :=
          WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.dist_segment_param x v hv t t₀
        have h2 := hdiam t ht t₀ ht₀
        rw [Real.dist_eq] at h1
        linarith [dist_triangle p (x + t • v) (x + t₀ • v)]
      calc _ ≤ volume (ball (x + t₀ • v) (1 / 10000 + δ)) := measure_mono (hsub.trans hball)
        _ = ENNReal.ofReal ((1 / 10000 + δ) ^ 3 * (Real.pi * 4 / 3)) := by
          rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hpi := Real.pi_lt_four
          have h1 : 1 / 10000 + δ ≤ 2 * δ := by linarith
          have h2 : (1 / 10000 + δ) ^ 3 ≤ (2 * δ) ^ 3 := by
            apply pow_le_pow_left₀ (by positivity) h1
          have h3 : (1 / 10000 + δ) ^ 3 * (Real.pi * 4 / 3) ≤ (2 * δ) ^ 3 * (16 / 3) := by
            apply mul_le_mul h2 (by linarith) (by positivity) (by positivity)
          have h4 : (2 * δ) ^ 3 * (16 / 3) ≤ 1 / 2 * δ ^ 2 := by
            have : (2 * δ) ^ 3 * (16 / 3) = (128 / 3 * δ) * δ ^ 2 := by ring
            rw [this]
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
            linarith
          linarith

private lemma rsel_finish {δ : ℝ} {y w p : Space} {lam : ℝ} (hlam : |lam - 1 / 2| ≤ 500000)
    (hp : ‖p - (y + lam • w)‖ < 1000000 * δ) :
    (y + (1 / 2 : ℝ) • w) + ((1 : ℝ) / 1000000) • (p - (y + (1 / 2 : ℝ) • w)) ∈
      Tube δ y w := by
  rw [abs_le] at hlam
  apply rsel_mem_thick (s := 1 / 2 + (lam - 1 / 2) / 1000000)
  · constructor <;> linarith [hlam.1, hlam.2]
  · have he : (y + (1 / 2 : ℝ) • w) + ((1 : ℝ) / 1000000) • (p - (y + (1 / 2 : ℝ) • w)) -
        (y + (1 / 2 + (lam - 1 / 2) / 1000000) • w) =
        ((1 : ℝ) / 1000000) • (p - (y + lam • w)) := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith

private lemma rsel_core {δ τ : ℝ} (hτ : 0 < τ) {x v y w : Space} {a b u α β : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) (hα : α ∈ Icc (0 : ℝ) 1)
    (hβ : β ∈ Icc (0 : ℝ) 1) (hab : τ ≤ |a - b|)
    (h1 : ‖x + a • v - (y + α • w)‖ < 2 * δ) (h2 : ‖x + b • v - (y + β • w)‖ < 2 * δ) :
    ∃ lam : ℝ, |lam| ≤ 1 + 1 / τ ∧
      ‖x + u • v - (y + lam • w)‖ ≤ (1 + 2 / τ) * (2 * δ) := by
  have hab0 : 0 < |b - a| := by rw [abs_sub_comm]; linarith
  have hba : b - a ≠ 0 := abs_pos.mp hab0
  set μ := (u - a) / (b - a) with hμdef
  have hua : |u - a| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hu.1, hu.2]
  have hμ : |μ| ≤ 1 / τ := by
    rw [hμdef, abs_div, div_le_div_iff₀ hab0 hτ, one_mul, abs_sub_comm b a]
    calc |u - a| * τ ≤ 1 * τ := by gcongr
      _ = τ := one_mul τ
      _ ≤ |a - b| := hab
  have hβα : |β - α| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
  have hαabs : |α| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hα.1, hα.2]
  have hδ : 0 ≤ δ := by
    have := norm_nonneg (x + a • v - (y + α • w))
    linarith
  refine ⟨α + μ * (β - α), ?_, ?_⟩
  · calc |α + μ * (β - α)| ≤ |α| + |μ| * |β - α| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 + 1 / τ * 1 := by
          gcongr
      _ = 1 + 1 / τ := by ring
  · have hu' : u = a + μ * (b - a) := by
      rw [hμdef, div_mul_cancel₀ _ hba]; ring
    have he : x + u • v - (y + (α + μ * (β - α)) • w) =
        (1 - μ) • (x + a • v - (y + α • w)) + μ • (x + b • v - (y + β • w)) := by
      rw [hu']; module
    rw [he]
    have h1μ : |1 - μ| ≤ 1 + |μ| := by
      calc |1 - μ| ≤ |1| + |μ| := abs_sub _ _
        _ = 1 + |μ| := by rw [abs_one]
    calc ‖(1 - μ) • (x + a • v - (y + α • w)) + μ • (x + b • v - (y + β • w))‖
        ≤ ‖(1 - μ) • (x + a • v - (y + α • w))‖ + ‖μ • (x + b • v - (y + β • w))‖ :=
          norm_add_le _ _
      _ = |1 - μ| * ‖x + a • v - (y + α • w)‖ + |μ| * ‖x + b • v - (y + β • w)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (1 + |μ|) * (2 * δ) + |μ| * (2 * δ) := by
          gcongr
      _ = (1 + 2 * |μ|) * (2 * δ) := by ring
      _ ≤ (1 + 2 * (1 / τ)) * (2 * δ) := by gcongr
      _ = (1 + 2 / τ) * (2 * δ) := by ring

private lemma rsel_contain_of_far {δ : ℝ} {x v y w p : Space} {a b : ℝ}
    (ha : a ∈ rselS δ x v y w) (hb : b ∈ rselS δ x v y w) (hab : 1 / 20000 ≤ |a - b|)
    (hp : p ∈ Tube δ x v) :
    (y + (1 / 2 : ℝ) • w) + ((1 : ℝ) / 1000000) • (p - (y + (1 / 2 : ℝ) • w)) ∈
      Tube δ y w := by
  obtain ⟨u, hu, hpu⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  obtain ⟨α, hα, hα'⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube ha.2
  obtain ⟨β, hβ, hβ'⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hb.2
  obtain ⟨lam, hlam, hlamd⟩ := rsel_core (τ := 1 / 20000) (by norm_num) ha.1 hu hα hβ hab hα' hβ'
  have hδ : 0 ≤ δ := by
    have := norm_nonneg (p - (x + u • v))
    linarith
  apply rsel_finish (lam := lam)
  · have h := abs_sub lam (1 / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    linarith
  · calc ‖p - (y + lam • w)‖ ≤ ‖p - (x + u • v)‖ + ‖x + u • v - (y + lam • w)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < δ + (1 + 2 / (1 / 20000)) * (2 * δ) := by linarith
      _ ≤ 1000000 * δ := by linarith

private lemma rsel_contain_of_near {δ : ℝ} (hδ : 1 / 100000 ≤ δ) {x v y w p : Space}
    (hv : ‖v‖ = 1) {a α : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hα : α ∈ Icc (0 : ℝ) 1)
    (h : ‖x + a • v - (y + α • w)‖ < 2 * δ) (hp : p ∈ Tube δ x v) :
    (y + (1 / 2 : ℝ) • w) + ((1 : ℝ) / 1000000) • (p - (y + (1 / 2 : ℝ) • w)) ∈
      Tube δ y w := by
  obtain ⟨u, hu, hpu⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  apply rsel_finish (lam := α)
  · rw [abs_le]; constructor <;> linarith [hα.1, hα.2]
  · have hua : ‖x + u • v - (x + a • v)‖ ≤ 1 := by
      rw [show x + u • v - (x + a • v) = (u - a) • v by module, norm_smul, hv, mul_one,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ha.1, ha.2, hu.1, hu.2]
    calc ‖p - (y + α • w)‖ ≤ ‖p - (x + u • v)‖ + ‖x + u • v - (y + α • w)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖p - (x + u • v)‖ + (‖x + u • v - (x + a • v)‖ + ‖x + a • v - (y + α • w)‖) := by
          gcongr
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < δ + (1 + 2 * δ) := by linarith
      _ ≤ 1000000 * δ := by linarith

private lemma rsel_contain {δ : ℝ} (hδ : 0 < δ) {x v y w p : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (h : rselWide δ x v y w ∨ rselWide δ y w x v)
    (hp : p ∈ Tube δ x v) :
    (y + (1 / 2 : ℝ) • w) + ((1 : ℝ) / 1000000) • (p - (y + (1 / 2 : ℝ) • w)) ∈
      Tube δ y w := by
  rcases le_or_gt (1 / 100000) δ with hbig | hsmall
  · rcases h with ⟨s, hs, _, _, _⟩ | ⟨s, hs, _, _, _⟩
    · obtain ⟨α, hα, hα'⟩ :=
        WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hs.2
      exact rsel_contain_of_near hbig hv hs.1 hα hα' hp
    · obtain ⟨a, ha, ha'⟩ :=
        WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hs.2
      rw [norm_sub_rev] at ha'
      exact rsel_contain_of_near hbig hv ha hs.1 ha' hp
  · rcases h with ⟨s, hs, t, ht, hst⟩ | ⟨s, hs, t, ht, hst⟩
    · exact rsel_contain_of_far hs ht (by linarith) hp
    · obtain ⟨a, ha, ha'⟩ :=
        WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hs.2
      obtain ⟨b, hb, hb'⟩ :=
        WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube ht.2
      have haS : a ∈ rselS δ x v y w :=
        ⟨ha, rsel_mem_thick hs.1 (by rw [norm_sub_rev]; exact ha')⟩
      have hbS : b ∈ rselS δ x v y w :=
        ⟨hb, rsel_mem_thick ht.1 (by rw [norm_sub_rev]; exact hb')⟩
      have hab : |s - t| ≤ |a - b| + 4 * δ := by
        have he : (s - t) • w = (y + s • w - (x + a • v)) - (y + t • w - (x + b • v)) +
            (a - b) • v := by module
        have hn : ‖(s - t) • w‖ ≤ ‖y + s • w - (x + a • v)‖ + ‖y + t • w - (x + b • v)‖ +
            ‖(a - b) • v‖ := by
          rw [he]
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
        rw [norm_smul, norm_smul, hw, hv, mul_one, mul_one, Real.norm_eq_abs,
          Real.norm_eq_abs] at hn
        linarith
      exact rsel_contain_of_far haS hbS (by linarith) hp

private lemma rsel_refl {δ : ℝ} (hδ : 0 < δ) (x v : Space) : rselWide δ x v x v := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨0, ⟨h0, rsel_mem_thick h0 (by simp; positivity)⟩, 1,
    ⟨h1, rsel_mem_thick h1 (by simp; positivity)⟩, by norm_num⟩

private lemma rsel_greedy {ι : Type*} [DecidableEq ι] (G : Finset ι) (rel : ι → ι → Prop)
    (hsymm : ∀ i j, rel i j → rel j i) (hrefl : ∀ i ∈ G, rel i i) :
    ∃ (Reps : Finset ι) (assign : ι → ι), Reps ⊆ G ∧
      (∀ r ∈ Reps, ∀ r' ∈ Reps, r ≠ r' → ¬ rel r r') ∧
      (∀ i ∈ G, assign i ∈ Reps ∧ rel i (assign i)) := by
  classical
  let P : Finset (Finset ι) :=
    G.powerset.filter (fun S => ∀ r ∈ S, ∀ r' ∈ S, r ≠ r' → ¬ rel r r')
  have hP : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨Reps, hReps, hmax⟩ := P.exists_max_image Finset.card hP
  simp only [P, Finset.mem_filter, Finset.mem_powerset] at hReps
  have hcover : ∀ i ∈ G, ∃ r ∈ Reps, rel i r := by
    intro i hi
    by_contra hne
    push Not at hne
    have hi' : i ∉ Reps := fun h => hne i h (hrefl i hi)
    have hins : insert i Reps ∈ P := by
      simp only [P, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hi hReps.1, ?_⟩
      intro r hr r' hr' hne'
      rw [Finset.mem_insert] at hr hr'
      rcases hr with rfl | hr <;> rcases hr' with rfl | hr'
      · exact absurd rfl hne'
      · exact hne r' hr'
      · exact fun h => hne r hr (hsymm _ _ h)
      · exact hReps.2 r hr r' hr' hne'
    have := hmax _ hins
    rw [Finset.card_insert_of_notMem hi'] at this
    omega
  refine ⟨Reps, fun i => if h : ∃ r ∈ Reps, rel i r then h.choose else i, hReps.1, hReps.2, ?_⟩
  intro i hi
  have h := hcover i hi
  simp only [h, ↓reduceDIte]
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

private lemma rsel_dyadic {ι : Type*} [DecidableEq ι] (G Reps : Finset ι) (hG : G.Nonempty)
    (assign : ι → ι) (hassign : ∀ i ∈ G, assign i ∈ Reps) :
    ∃ (R : Finset ι) (N : ℕ), R ⊆ Reps ∧ R.Nonempty ∧ 0 < N ∧
      (∀ r ∈ R, N ≤ (G.filter (fun i => assign i = r)).card ∧
        (G.filter (fun i => assign i = r)).card ≤ 2 * N) ∧
      G.card ≤ 2 * (Nat.log 2 G.card + 1) * N * R.card := by
  set C : ι → ℕ := fun r => (G.filter (fun i => assign i = r)).card with hC
  set L := Nat.log 2 G.card with hL
  have htot : G.card = ∑ r ∈ Reps, C r :=
    Finset.card_eq_sum_card_fiberwise (fun i hi => hassign i hi)
  set Reps' := Reps.filter (fun r => C r ≠ 0) with hReps'
  have htot' : ∑ r ∈ Reps', C r = G.card := by
    rw [htot, hReps', Finset.sum_filter_ne_zero]
  have hmaps : ∀ r ∈ Reps', Nat.log 2 (C r) ∈ Finset.range (L + 1) := by
    intro r _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right (Finset.card_filter_le _ _)
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps C
  have hex : ∃ k ∈ Finset.range (L + 1),
      G.card ≤ (L + 1) * ∑ r ∈ Reps' with Nat.log 2 (C r) = k, C r := by
    apply Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    rw [Finset.sum_const, Finset.card_range, ← Finset.mul_sum, hfib, htot', smul_eq_mul]
  obtain ⟨k, _, hle⟩ := hex
  set R := Reps'.filter (fun r => Nat.log 2 (C r) = k) with hR
  have hRsub : R ⊆ Reps := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hRbounds : ∀ r ∈ R, 2 ^ k ≤ C r ∧ C r ≤ 2 * 2 ^ k := by
    intro r hr
    rw [hR, Finset.mem_filter, hReps', Finset.mem_filter] at hr
    obtain ⟨⟨_, hne⟩, hlog⟩ := hr
    constructor
    · rw [← hlog]; exact Nat.pow_log_le_self 2 hne
    · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (C r)
      rw [hlog, pow_succ] at this
      omega
  have hsum : ∑ r ∈ R, C r ≤ R.card * (2 * 2 ^ k) := by
    calc ∑ r ∈ R, C r ≤ ∑ _r ∈ R, 2 * 2 ^ k := Finset.sum_le_sum (fun r hr => (hRbounds r hr).2)
      _ = R.card * (2 * 2 ^ k) := by rw [Finset.sum_const, smul_eq_mul]
  have hGpos : 0 < G.card := Finset.card_pos.mpr hG
  refine ⟨R, 2 ^ k, hRsub, ?_, by positivity, hRbounds, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hRe
    have : ∑ r ∈ R, C r = 0 := by rw [hRe, Finset.sum_empty]
    rw [this, mul_zero] at hle
    omega
  · calc G.card ≤ (L + 1) * ∑ r ∈ R, C r := hle
      _ ≤ (L + 1) * (R.card * (2 * 2 ^ k)) := Nat.mul_le_mul_left _ hsum
      _ = 2 * (L + 1) * 2 ^ k * R.card := by ring

theorem select_clusters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) {ι : Type*} [DecidableEq ι]
    (G : Finset ι) (hG : G.Nonempty) (x w : ι → Space) (hw : ∀ i ∈ G, ‖w i‖ = 1) :
    ∃ (R : Finset ι) (N : ℕ) (mem : ι → Finset ι), R ⊆ G ∧ R.Nonempty ∧ 0 < N ∧
      (∀ r ∈ R, mem r ⊆ G) ∧
      (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → Disjoint (mem r) (mem r')) ∧
      (∀ r ∈ R, N ≤ (mem r).card ∧ (mem r).card ≤ 2 * N) ∧
      G.card ≤ 2 * (Nat.log 2 G.card + 1) * N * R.card ∧
      (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' →
        volume (Tube δ (x r) (w r) ∩ Tube δ (x r') (w r')) ≤
          (1 / 2 : ENNReal) * volume (Tube δ (x r) (w r))) ∧
      (∀ r ∈ R, ∀ i ∈ mem r, ∀ p ∈ Tube δ (x i) (w i),
        (x r + (1 / 2 : ℝ) • w r) + ((1 : ℝ) / 1000000) • (p - (x r + (1 / 2 : ℝ) • w r)) ∈
          Tube δ (x r) (w r)) := by
  classical
  obtain ⟨Reps, assign, hRG, hpair, hassign⟩ := rsel_greedy G
    (fun i j => rselWide δ (x i) (w i) (x j) (w j) ∨ rselWide δ (x j) (w j) (x i) (w i))
    (fun _ _ h => h.symm) (fun i _ => Or.inl (rsel_refl hδ (x i) (w i)))
  obtain ⟨R, N, hRR, hRne, hN, hcard, hbound⟩ :=
    rsel_dyadic G Reps hG assign (fun i hi => (hassign i hi).1)
  refine ⟨R, N, fun r => G.filter (fun i => assign i = r), hRR.trans hRG, hRne, hN,
    fun r _ => Finset.filter_subset _ _, ?_, hcard, hbound, ?_, ?_⟩
  · intro r _ r' _ hne
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    exact hne (h1.symm.trans h2)
  · intro r hr r' hr' hne
    have hnrel := hpair r (hRR hr) r' (hRR hr') hne
    apply rsel_half hδ hδ1 (hw r (hRG (hRR hr)))
    intro s hs t ht
    by_contra hlt
    exact hnrel (Or.inl ⟨s, hs, t, ht, lt_of_not_ge hlt⟩)
  · intro r hr i hi p hp
    rw [Finset.mem_filter] at hi
    obtain ⟨hiG, hir⟩ := hi
    have hrel := (hassign i hiG).2
    rw [hir] at hrel
    exact rsel_contain hδ (hw i hiG) (hw r (hRG (hRR hr))) hrel hp

end WangZahlLot.Obl.wz_grains_nonsingular_slices
