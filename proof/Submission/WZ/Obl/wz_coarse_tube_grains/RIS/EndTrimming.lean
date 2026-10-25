-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.EndTrimming.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalScale
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.GrainConstruction

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- The portions within `2c` of either axis endpoint, thickened by the tube radius. -/
def tubeEnds (δ c : ℝ) (x v : Space) : Set Space :=
  thickening δ ((fun t : ℝ => x + t • v) '' Icc 0 (2 * c)) ∪
    thickening δ ((fun t : ℝ => x + t • v) '' Icc (1 - 2 * c) 1)

theorem measurableSet_tubeEnds (δ c : ℝ) (x v : Space) :
    MeasurableSet (tubeEnds δ c x v) :=
  isOpen_thickening.measurableSet.union isOpen_thickening.measurableSet

/-- Endpoint trimming costs at most a constant times the relative axis length. -/
theorem tubeEnds_volume_upper {δ c : ℝ} (hδ : 0 < δ) (hδc : δ ≤ c)
    (hc : c ≤ 1 / 2) (x v : Space) (hv : ‖v‖ = 1) :
    volume (tubeEnds δ c x v) ≤ ENNReal.ofReal (1280 * c * δ ^ 2) := by
  have hc0 : 0 < c := hδ.trans_le hδc
  have hleft : Icc (0 : ℝ) (2 * c) ⊆ Icc 0 1 := by
    intro t ht
    exact ⟨ht.1, ht.2.trans (by linarith)⟩
  have hright : Icc (1 - 2 * c) (1 : ℝ) ⊆ Icc 0 1 := by
    intro t ht
    exact ⟨(by linarith : (0 : ℝ) ≤ 1 - 2 * c).trans ht.1, ht.2⟩
  have hdiam (a : ℝ) : ∀ s ∈ Icc a (a + 2 * c), ∀ t ∈ Icc a (a + 2 * c),
      dist s t ≤ 2 * c := by
    intro s hs t ht
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hL := wz_direction_density_transfer.segment_piece_volume_upper x v hv hleft hδ
    (by positivity : 0 ≤ 2 * c) (by simpa using hdiam 0)
  have hR := wz_direction_density_transfer.segment_piece_volume_upper x v hv hright hδ
    (by positivity : 0 ≤ 2 * c) (by
      simpa only [show 1 - 2 * c + 2 * c = 1 by ring] using hdiam (1 - 2 * c))
  calc
    volume (tubeEnds δ c x v) ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (128 * (2 * (2 * c) + δ) * δ ^ 2) +
        ENNReal.ofReal (128 * (2 * (2 * c) + δ) * δ ^ 2) := add_le_add hL hR
    _ = ENNReal.ofReal (256 * (4 * c + δ) * δ ^ 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg δ])

/-- Outside the trimmed ends, every witnessing point on the axis has its
parameter between `2c` and `1-2c`. -/
theorem axis_witness_away_from_ends {δ c : ℝ} {x v p : Space}
    (hp : p ∈ Tube δ x v \ tubeEnds δ c x v) :
    ∃ t : ℝ, 2 * c < t ∧ t < 1 - 2 * c ∧ dist p (x + t • v) < δ := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp.1
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  refine ⟨t, ?_, ?_, hpq⟩
  · by_contra hn
    exact hp.2 (Or.inl (mem_thickening_iff.mpr
      ⟨_, ⟨t, ⟨ht.1, le_of_not_gt hn⟩, rfl⟩, hpq⟩))
  · by_contra hn
    exact hp.2 (Or.inr (mem_thickening_iff.mpr
      ⟨_, ⟨t, ⟨le_of_not_gt hn, ht.2⟩, rfl⟩, hpq⟩))

/-- A uniformly short endpoint deletion retains half the mass of an
average-dense family, without a separate density assumption on each tube. -/
theorem trim_tube_ends_half {δ c lam : ℝ} {n : ℕ}
    (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hδ : 0 < δ) (hδc : δ ≤ c) (hc : c ≤ 1 / 2)
    (hbudget : 2560 * c ≤ lam)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hdense : ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)) :
    ∃ Z : Fin n → Set Space,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ Disjoint (Z i) (tubeEnds δ c (x i) (v i))) ∧
      (1 / 2 : ENNReal) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) := by
  let Z := fun i => Y i \ tubeEnds δ c (x i) (v i)
  have hcut : ∀ i, volume (Y i) ≤ volume (Z i) +
      ENNReal.ofReal (1280 * c * δ ^ 2) := by
    intro i
    have hcover : Y i ⊆ Z i ∪ tubeEnds δ c (x i) (v i) := by
      intro p hp
      by_cases he : p ∈ tubeEnds δ c (x i) (v i)
      · exact Or.inr he
      · exact Or.inl ⟨hp, he⟩
    exact (measure_mono hcover).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl (tubeEnds_volume_upper hδ hδc hc (x i) (v i) (hv i))))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcut i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)] at hsum
  have hcost : ENNReal.ofReal ((n : ℝ) * (1280 * c * δ ^ 2)) ≤
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (lam * n * δ ^ 2)) :=
        ENNReal.ofReal_le_ofReal (by
          have hh := mul_le_mul_of_nonneg_right hbudget
            (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg δ))
          nlinarith)
      _ = (1 / 2 : ENNReal) * ENNReal.ofReal (lam * n * δ ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      _ ≤ _ := mul_le_mul_right hdense _
  refine ⟨Z, fun i => ⟨(hY i).diff (measurableSet_tubeEnds _ _ _ _),
    sdiff_subset, disjoint_sdiff_left⟩, ?_⟩
  have htotal := hsum.trans (add_le_add le_rfl hcost)
  by_cases hfin : (∑ i, volume (Y i)) = ⊤
  · have hz : (∑ i, volume (Z i)) = ⊤ := by
      have hcfin : ENNReal.ofReal ((n : ℝ) * (1280 * c * δ ^ 2)) ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [hfin, top_le_iff, ENNReal.add_eq_top] at hsum
      exact hsum.resolve_right hcfin
    rw [hz]
    exact le_top
  · apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by norm_num) hfin)
      (ne_top_of_le_ne_top hfin (Finset.sum_le_sum fun i _ => measure_mono sdiff_subset))).mp
    have hZfin : (∑ i, volume (Z i)) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (Finset.sum_le_sum fun i _ => measure_mono sdiff_subset)
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨hZfin, ENNReal.mul_ne_top (by norm_num) hfin⟩) htotal
    rw [ENNReal.toReal_add hZfin (ENNReal.mul_ne_top (by norm_num) hfin),
      ENNReal.toReal_mul] at hh
    rw [ENNReal.toReal_mul]
    norm_num at hh ⊢
    linarith

namespace Interfaces

/-- A surviving shaded point in the core of a box gives the exact long-face
crossing conditions. The axis point and its endpoint margin are obtained from
the endpoint cut, so they need not be supplied separately. -/
theorem prism_crossing_of_core_point {δ a b c : ℝ} {x v z q : V}
    (e : V ≃ₗᵢ[ℝ] V) (hδ : 0 < δ)
    (hδa : 16 * δ ≤ a) (hδb : 16 * δ ≤ b) (hδc : 16 * δ ≤ c)
    (hlong : 1 / 2 ≤ |e v 2|)
    (hdir0 : c * |e v 0| ≤ a / 16) (hdir1 : c * |e v 1| ≤ b / 16)
    (hq : q ∈ (T δ x v \ tubeEnds δ c x v) ∩ P (a / 8) (b / 8) (c / 8) z e) :
    (∀ p ∈ T δ x v ∩ frontier (P a b c z e), |e (p - z) 2| = c / 2) ∧
    (∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t) := by
  obtain ⟨s, hs0, hs1, hsq⟩ := axis_witness_away_from_ends hq.1
  have hcoord (i : Fin 3) :
      |e (q - z) i - e (x + s • v - z) i| < δ := by
    have hh := (abs_rotated_coord_le e (q - (x + s • v)) i).trans_lt
      (show ‖q - (x + s • v)‖ < δ by simpa only [dist_eq_norm] using hsq)
    rwa [show q - (x + s • v) = (q - z) - (x + s • v - z) by abel, map_sub] at hh
  have hbase (i : Fin 3) (r : ℝ) (hr : 16 * δ ≤ r)
      (hq' : |e (q - z) i| ≤ (r / 8) / 2) :
      |e (x + s • v - z) i| ≤ r / 8 := by
    have hh := abs_sub (e (q - z) i) (e (q - z) i - e (x + s • v - z) i)
    simp only [sub_sub_cancel] at hh
    linarith [hcoord i]
  have hbase' : |e (x + s • v - z) 0| ≤ a / 8 ∧
      |e (x + s • v - z) 1| ≤ b / 8 ∧ |e (x + s • v - z) 2| ≤ c / 8 :=
    ⟨hbase 0 a hδa hq.2.1,
    hbase 1 b hδb hq.2.2.1, hbase 2 c hδc hq.2.2.2⟩
  exact ⟨prism_only_long_face_exits e hδ hδa hδb hδc hlong hbase' hdir0 hdir1,
    prism_both_long_faces e hδ hδa hδb hδc hs0.le hs1.le hlong hbase' hdir0 hdir1⟩

end Interfaces

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
