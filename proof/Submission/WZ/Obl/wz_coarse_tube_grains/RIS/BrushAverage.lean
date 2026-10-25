-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushAverage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped Classical

/-- Average density suffices for planar concentration of an off-stem broad
brush. Empty shadings are allowed, and only occupied tubes need meet the stem. -/
theorem off_stem_broad_planar_average {δ r b lam U : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hlam : 0 < lam) (hU : 0 < U) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space) (y w : Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hshade : ∀ i, Y i ⊆ Tube δ (x i) (v i) \ Metric.thickening r (Set.range fun t : ℝ => y + t • w))
    (hdense : ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i))
    (hvol : volume (⋃ i, Y i) ≤ ENNReal.ofReal (U * δ))
    (hstem : ∀ i, (Y i).Nonempty → (Tube δ (x i) (v i) ∩ Tube δ y w).Nonempty)
    (hbroad : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) :
    ∃ (e : Space) (t : ℝ) (F : Finset (Fin n)), ‖e‖ = 1 ∧
      (∀ i ∈ F, Tube δ (x i) (v i) ⊆ {p | |inner ℝ e p - t| ≤ 15 * δ / r}) ∧
      ENNReal.ofReal (b * lam ^ 2 / (65536 * U)) * (∑ i, volume (Y i)) ≤
        ∑ i ∈ F, volume (Y i) := by
  have hfin : volume (⋃ i, Y i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hfin (measure_mono (subset_iUnion Y i))
  have hsum : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  let S := ∑ i, (volume (Y i)).toReal
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hS : lam * (n : ℝ) * δ ^ 2 ≤ S := by
    have hr := (ENNReal.ofReal_le_iff_le_toReal hsum).mp hdense
    simpa only [S, ENNReal.toReal_sum (fun i _ => hYfin i)] using hr
  have hpos : 0 < (volume (⋃ i, Y i)).toReal := by
    have hSn : S ≤ (n : ℝ) * (volume (⋃ i, Y i)).toReal := by
      simpa [S] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        ENNReal.toReal_mono hfin (measure_mono (subset_iUnion Y i)))
    have hP : 0 < (n : ℝ) * (volume (⋃ i, Y i)).toReal :=
      (show 0 < lam * (n : ℝ) * δ ^ 2 by positivity).trans_le (hS.trans hSn)
    exact (mul_pos_iff_of_pos_left (Nat.cast_pos.mpr hn)).mp hP
  let threshold := lam * δ ^ 2 / 2
  have ht0 : 0 ≤ threshold := by dsimp [threshold]; positivity
  let D : Finset (Fin n) := Finset.univ.filter fun i => threshold ≤ (volume (Y i)).toReal
  have hsmall : (∑ i ∈ Finset.univ.filter (fun i => ¬threshold ≤ (volume (Y i)).toReal),
      (volume (Y i)).toReal) ≤ (n : ℝ) * threshold := by
    rw [Finset.sum_filter]
    calc
      _ ≤ ∑ _i : Fin n, threshold := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact ht0
        · exact (lt_of_not_ge hi).le
      _ = _ := by simp
  have hDmass : S / 2 ≤ ∑ i ∈ D, (volume (Y i)).toReal := by
    have he := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => threshold ≤ (volume (Y i)).toReal) (fun i => (volume (Y i)).toReal)
    change (∑ i ∈ D, (volume (Y i)).toReal) + _ = S at he
    dsimp [threshold] at hsmall
    nlinarith
  obtain ⟨e, t, F, hFD, he, hslab, hmass⟩ :=
    off_stem_subset_broad_slab hδ hr hr1 hb hb1 hn x v Y D y w hv hY hshade hfin hpos hstem hbroad
  let W := ∑ i ∈ F, (volume (Y i)).toReal
  have hW : lam / 2 * (F.card : ℝ) * δ ^ 2 ≤ W := by
    have hlower : ∀ i ∈ F, threshold ≤ (volume (Y i)).toReal := fun i hi =>
      (Finset.mem_filter.mp (hFD hi)).2
    simpa [W, threshold, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using
      Finset.sum_le_sum (fun i (hi : i ∈ F) => hlower i hi)
  have hq : (volume (⋃ i, Y i)).toReal ≤ U * δ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
  have hhalf : (S / 2) ^ 2 ≤ 8192 * U * (n : ℝ) * F.card * δ ^ 4 / b := by
    refine (pow_le_pow_left₀ (by positivity) hDmass 2).trans (hmass.trans ?_)
    calc
      _ ≤ 8192 * (U * δ) * (n : ℝ) * F.card * δ ^ 3 / b := by gcongr
      _ = _ := by ring
  have hmass' : S ^ 2 ≤ 32768 * U * (n : ℝ) * F.card * δ ^ 4 / b := by
    have hh := mul_le_mul_of_nonneg_left hhalf (by norm_num : (0 : ℝ) ≤ 4)
    convert hh using 1 <;> ring
  have hcancel : lam * S ≤ 32768 * U * (F.card : ℝ) * δ ^ 2 / b := by
    apply (mul_le_mul_iff_left₀ (show 0 < (n : ℝ) * δ ^ 2 by positivity)).mp
    calc
      (lam * S) * ((n : ℝ) * δ ^ 2) = S * (lam * (n : ℝ) * δ ^ 2) := by ring
      _ ≤ S * S := mul_le_mul_of_nonneg_left hS hS0
      _ = S ^ 2 := (pow_two S).symm
      _ ≤ _ := hmass'
      _ = _ := by ring
  have hretain : b * lam ^ 2 / (65536 * U) * S ≤ W := by
    calc
      _ = (b * lam / (65536 * U)) * (lam * S) := by ring
      _ ≤ (b * lam / (65536 * U)) * (32768 * U * (F.card : ℝ) * δ ^ 2 / b) :=
        mul_le_mul_of_nonneg_left hcancel (by positivity)
      _ = lam / 2 * (F.card : ℝ) * δ ^ 2 := by field_simp; ring
      _ ≤ _ := hW
  refine ⟨e, t, F, he, hslab, ?_⟩
  have hsumF : (∑ i ∈ F, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hYfin i
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum) hsumF).mp
  simpa only [S, W, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ b * lam ^ 2 / (65536 * U)),
    ENNReal.toReal_sum (fun i _ => hYfin i)] using hretain

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
