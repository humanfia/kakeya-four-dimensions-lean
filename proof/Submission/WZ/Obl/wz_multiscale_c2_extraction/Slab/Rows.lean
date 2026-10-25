-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Rows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Plank

/-!
# Masses of rows and the output of the slab lemma

* `heightMass Y H`: the total shading mass at heights in `H`; it is additive over rows.
* `heavy_rows`: the rows of a window carrying at least a quarter of the average carry three
  quarters of the mass of the window.
* `slope_le_two`, `rows_fit`: an affine fit of error `s` on a set of heights of measure at
  least `8 s` has slope at most `2`, and then extends to the whole grid rows meeting the set
  with error `4 s`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- The shading mass at heights in `H`. -/
noncomputable def heightMass {n : ℕ} (Y : Fin n → Set Space) (H : Set ℝ) : ℝ≥0∞ :=
  ∑ i, volume (Y i ∩ (fun p : Space => p 2) ⁻¹' H)

lemma heightMass_mono {n : ℕ} (Y : Fin n → Set Space) {H H' : Set ℝ} (h : H ⊆ H') :
    heightMass Y H ≤ heightMass Y H' :=
  Finset.sum_le_sum fun i _ => measure_mono (inter_subset_inter_right _ (preimage_mono h))

lemma heightMass_rowUnion {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    {s : ℝ} (hs : 0 < s) (R : Finset ℤ) :
    heightMass Y (rowUnion s R) = ∑ m ∈ R, heightMass Y (row s m) := by
  unfold heightMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowUnion, preimage_iUnion₂, inter_iUnion₂]
  exact measure_biUnion_finset
    (fun m _ m' _ hmm => (Disjoint.preimage _ (row_disjoint hs hmm)).mono
      inter_subset_right inter_subset_right)
    (fun m _ => (hY i).inter
      ((by fun_prop : Continuous fun p : Space => p 2).measurable (measurableSet_row s m)))

lemma heightMass_ne_top {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, Y i ⊆ ball (0 : Space) 1)
    (H : Set ℝ) : heightMass Y H ≠ ∞ := by
  apply ne_of_lt
  apply ENNReal.sum_lt_top.mpr
  intro i _
  exact (measure_mono (inter_subset_left.trans (hY i))).trans_lt measure_ball_lt_top

/-- Heavy rows carry three quarters of the mass of a window. -/
theorem heavy_rows {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    (hYb : ∀ i, Y i ⊆ ball (0 : Space) 1) {s : ℝ} (hs : 0 < s) (W : Finset ℤ) {L : ℕ}
    (hW : (W.card : ℝ) ≤ L) (hL : 0 < L) :
    let Mw := (heightMass Y (rowUnion s W)).toReal
    3 * Mw / 4 ≤ (heightMass Y (rowUnion s
      (W.filter fun m => Mw / (4 * L) ≤ (heightMass Y (row s m)).toReal))).toReal := by
  intro Mw
  classical
  set h : ℤ → ℝ := fun m => (heightMass Y (row s m)).toReal
  have hMw : Mw = ∑ m ∈ W, h m := by
    simp only [Mw, h]
    rw [heightMass_rowUnion hY hs, ENNReal.toReal_sum fun m _ => heightMass_ne_top hYb _]
  set R := W.filter fun m => Mw / (4 * L) ≤ h m
  have hR : (heightMass Y (rowUnion s R)).toReal = ∑ m ∈ R, h m := by
    rw [heightMass_rowUnion hY hs, ENNReal.toReal_sum fun m _ => heightMass_ne_top hYb _]
  show 3 * Mw / 4 ≤ (heightMass Y (rowUnion s R)).toReal
  rw [hR]
  have hsplit := Finset.sum_filter_add_sum_filter_not W (fun m => Mw / (4 * L) ≤ h m) h
  have hlight : ∑ m ∈ W.filter (fun m => ¬ Mw / (4 * L) ≤ h m), h m ≤ Mw / 4 := by
    calc ∑ m ∈ W.filter (fun m => ¬ Mw / (4 * L) ≤ h m), h m
        ≤ ∑ _m ∈ W.filter (fun m => ¬ Mw / (4 * L) ≤ h m), Mw / (4 * L) := by
          apply Finset.sum_le_sum
          intro m hm
          exact (not_le.mp (Finset.mem_filter.mp hm).2).le
      _ = ((W.filter (fun m => ¬ Mw / (4 * L) ≤ h m)).card : ℝ) * (Mw / (4 * L)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (L : ℝ) * (Mw / (4 * L)) := by
          have h0 : 0 ≤ Mw := ENNReal.toReal_nonneg
          exact mul_le_mul_of_nonneg_right
            ((Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hW) (by positivity)
      _ = Mw / 4 := by
          have : (0 : ℝ) < L := by exact_mod_cast hL
          field_simp
  linarith

/-- A fit of error `s` on a set of heights of measure at least `8 s` has slope at most `2`. -/
theorem slope_le_two {f : ℝ → ℝ} (hf : LipschitzWith 1 f) {Zl : Set ℝ} {T s a b : ℝ}
    (hT : 0 < T) (hs : 0 ≤ s) (hTs : 8 * s ≤ T) (hvol : ENNReal.ofReal T ≤ volume Zl)
    (hfit : ∀ z ∈ Zl, |f z - (a + b * z)| ≤ s) : |b| ≤ 2 := by
  have hne : Zl.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hvol
    linarith
  obtain ⟨z₁, hz₁⟩ := hne
  have hfar : ∃ z₂ ∈ Zl, T / 4 ≤ |z₂ - z₁| := by
    by_contra h
    push Not at h
    have hsub : Zl ⊆ Icc (z₁ - T / 4) (z₁ + T / 4) := by
      intro z hz
      have := (abs_lt.mp (h z hz))
      constructor <;> linarith
    have := (hvol.trans (measure_mono hsub))
    rw [Real.volume_Icc, ENNReal.ofReal_le_ofReal_iff (by linarith)] at this
    linarith
  obtain ⟨z₂, hz₂, hd⟩ := hfar
  have hd0 : 0 < |z₂ - z₁| := by linarith
  have h1 := hfit z₁ hz₁
  have h2 := hfit z₂ hz₂
  have hlip : |f z₂ - f z₁| ≤ |z₂ - z₁| := by
    have := hf.dist_le_mul z₂ z₁
    simpa [Real.dist_eq] using this
  have hb : |b| * |z₂ - z₁| ≤ |z₂ - z₁| + 2 * s := by
    rw [← abs_mul]
    have e : b * (z₂ - z₁) = (f z₂ - f z₁) - (f z₂ - (a + b * z₂)) + (f z₁ - (a + b * z₁)) := by
      ring
    rw [e]
    calc |(f z₂ - f z₁) - (f z₂ - (a + b * z₂)) + (f z₁ - (a + b * z₁))|
        ≤ |f z₂ - f z₁| + |f z₂ - (a + b * z₂)| + |f z₁ - (a + b * z₁)| := by
          have := abs_add_le ((f z₂ - f z₁) - (f z₂ - (a + b * z₂))) (f z₁ - (a + b * z₁))
          have := abs_sub (f z₂ - f z₁) (f z₂ - (a + b * z₂))
          linarith
      _ ≤ |z₂ - z₁| + 2 * s := by linarith
  by_contra hcon
  push Not at hcon
  have : 2 * |z₂ - z₁| < |b| * |z₂ - z₁| := mul_lt_mul_of_pos_right hcon hd0
  nlinarith

/-- The fit extends to whole rows meeting the fit set. -/
theorem rows_fit {f : ℝ → ℝ} (hf : LipschitzWith 1 f) {s a b : ℝ} (hb : |b| ≤ 2)
    {m : ℤ} {z₁ : ℝ} (hz₁ : z₁ ∈ row s m) (hfit : |f z₁ - (a + b * z₁)| ≤ s) :
    ∀ z ∈ row s m, |f z - (a + b * z)| ≤ 4 * s := by
  intro z hz
  have hzz : |z - z₁| ≤ s := by
    obtain ⟨h1, h2⟩ := hz; obtain ⟨h3, h4⟩ := hz₁
    rw [abs_le]; constructor <;> nlinarith
  have hlip : |f z - f z₁| ≤ |z - z₁| := by
    have := hf.dist_le_mul z z₁
    simpa [Real.dist_eq] using this
  have e : f z - (a + b * z) = (f z₁ - (a + b * z₁)) + (f z - f z₁) - b * (z - z₁) := by ring
  rw [e]
  calc |(f z₁ - (a + b * z₁)) + (f z - f z₁) - b * (z - z₁)|
      ≤ |f z₁ - (a + b * z₁)| + |f z - f z₁| + |b| * |z - z₁| := by
        rw [← abs_mul]
        have := abs_sub ((f z₁ - (a + b * z₁)) + (f z - f z₁)) (b * (z - z₁))
        have := abs_add_le (f z₁ - (a + b * z₁)) (f z - f z₁)
        linarith
    _ ≤ s + s + 2 * s := by
        have h1 : |f z - f z₁| ≤ s := hlip.trans hzz
        have h2 : |b| * |z - z₁| ≤ 2 * s := mul_le_mul hb hzz (abs_nonneg _) (by norm_num)
        linarith
    _ = 4 * s := by ring

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
