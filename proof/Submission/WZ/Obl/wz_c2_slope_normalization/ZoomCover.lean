-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomPack

/-!
# Conflict relations of zoomed pieces and their degrees

At one scale, two coarse pieces conflict when both coarse tubes pass near the zoom centre and
either a candidate fine piece lies in both tenfold dilates, or one piece covers more than half
of the other.  Fine pieces conflict when one covers more than half of the other.  Each relation
has degree at most a constant times `r ^ 4`.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace Classical

noncomputable section

/-- A coarse tube passes near the zoom centre. -/
def CNear (r : ℝ) (c z w : Space) : Prop :=
  ‖cpt c z w - c‖ ≤ 1 / (4 * r) ∧ cpar c z w ∈ Icc (-(1 / 4) : ℝ) (5 / 4)

/-- A fine tube passes near the zoom centre, with its closest point essentially on its axis. -/
def FNear (r : ℝ) (c x v : Space) : Prop :=
  ‖cpt c x v - c‖ ≤ 1 / (8 * r) ∧ cpar c x v ∈ Icc (-(1 / (8 * r))) (1 + 1 / (8 * r))

/-- The zoomed coarse piece. -/
def cpiece (r ρ : ℝ) (c z w : Space) : Set Space := Tube (8 * r * ρ) (pieceBase r c z w) w

/-- The tenfold dilate of the zoomed coarse piece. -/
def cdil (r ρ : ℝ) (c z w : Space) : Set Space := Dilate (8 * r * ρ) (pieceBase r c z w) w

/-- The zoomed fine piece. -/
def fpiece (r δ : ℝ) (c x v : Space) : Set Space := Tube (r * δ) (pieceBase r c x v) v

/-- Conflicts of coarse pieces at one scale. -/
def CConf {n k : ℕ} (r δ ρ : ℝ) (c : Space) (I₀ : Finset (Fin n)) (x v : Fin n → Space)
    (z w : Fin k → Space) (j j' : Fin k) : Prop :=
  CNear r c (z j) (w j) ∧ CNear r c (z j') (w j') ∧
    ((∃ i ∈ I₀, fpiece r δ c (x i) (v i) ⊆ cdil r ρ c (z j) (w j) ∧
        fpiece r δ c (x i) (v i) ⊆ cdil r ρ c (z j') (w j')) ∨
      (1 / 2 : ℝ≥0∞) * volume (cpiece r ρ c (z j) (w j)) <
        volume (cpiece r ρ c (z j) (w j) ∩ cpiece r ρ c (z j') (w j')) ∨
      (1 / 2 : ℝ≥0∞) * volume (cpiece r ρ c (z j') (w j')) <
        volume (cpiece r ρ c (z j') (w j') ∩ cpiece r ρ c (z j) (w j)))

theorem CConf.symm {n k : ℕ} {r δ ρ : ℝ} {c : Space} {I₀ : Finset (Fin n)}
    {x v : Fin n → Space} {z w : Fin k → Space} {j j' : Fin k}
    (h : CConf r δ ρ c I₀ x v z w j j') : CConf r δ ρ c I₀ x v z w j' j := by
  obtain ⟨h1, h2, h3 | h3 | h3⟩ := h
  · obtain ⟨i, hi, ha, hb⟩ := h3
    exact ⟨h2, h1, Or.inl ⟨i, hi, hb, ha⟩⟩
  · exact ⟨h2, h1, Or.inr (Or.inr h3)⟩
  · exact ⟨h2, h1, Or.inr (Or.inl h3)⟩

/-- Conflicts of fine pieces. -/
def FConf {n : ℕ} (r δ : ℝ) (c : Space) (x v : Fin n → Space) (i i' : Fin n) : Prop :=
  cpar c (x i) (v i) ∈ Icc (-(1 / 4) : ℝ) (5 / 4) ∧
    cpar c (x i') (v i') ∈ Icc (-(1 / 4) : ℝ) (5 / 4) ∧
    ((1 / 2 : ℝ≥0∞) * volume (fpiece r δ c (x i) (v i)) <
        volume (fpiece r δ c (x i) (v i) ∩ fpiece r δ c (x i') (v i')) ∨
      (1 / 2 : ℝ≥0∞) * volume (fpiece r δ c (x i') (v i')) <
        volume (fpiece r δ c (x i') (v i') ∩ fpiece r δ c (x i) (v i)))

theorem FConf.symm {n : ℕ} {r δ : ℝ} {c : Space} {x v : Fin n → Space} {i i' : Fin n}
    (h : FConf r δ c x v i i') : FConf r δ c x v i' i := by
  obtain ⟨h1, h2, h3 | h3⟩ := h
  · exact ⟨h2, h1, Or.inr h3⟩
  · exact ⟨h2, h1, Or.inl h3⟩

theorem container_mono {Λ Λ' : ℝ} (h : Λ ≤ Λ') (z w : Space) :
    Container Λ z w ⊆ Container Λ' z w := by
  apply image_mono
  apply thickening_mono
  linarith

/-- The constant bounding the number of conflicts, divided by `r ^ 4`. -/
def conflictConst : ℝ := 1000000 * (200000000000 * 787 ^ 2) ^ 2

theorem cconf_card_le {n k : ℕ} {r δ ρ : ℝ} (hr : 16 ≤ r) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρr : ρ ≤ 1 / (131072 * r)) {c : Space} (I₀ : Finset (Fin n)) (x v : Fin n → Space)
    (z w : Fin k → Space) (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ j, ‖w j‖ = 1)
    (hsep : ∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube ρ (z j) (w j))) (j : Fin k) :
    ((Finset.univ.filter (CConf r δ ρ c I₀ x v z w j)).card : ℝ) ≤ conflictConst * r ^ 4 := by
  classical
  have hr0 : 0 < r := by linarith
  have hρ : 0 < ρ := hδ.trans_le hδρ
  by_cases hj : CNear r c (z j) (w j)
  swap
  · have : Finset.univ.filter (CConf r δ ρ c I₀ x v z w j) = ∅ := by
      apply Finset.filter_false_of_mem
      intro j' _ h
      exact hj h.1
    rw [this, Finset.card_empty, Nat.cast_zero]
    unfold conflictConst; positivity
  have hρr' : ρ ≤ 1 / (1280 * r) := hρr.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
  have hΛ1 : 787 * r * ρ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hρr (show (0 : ℝ) ≤ 787 * r by positivity)
    calc 787 * r * ρ ≤ 787 * r * (1 / (131072 * r)) := by linarith
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; nlinarith
  have ha1 : 8 * r * ρ ≤ 1 / 1024 := by
    have := mul_le_mul_of_nonneg_left hρr (show (0 : ℝ) ≤ 8 * r by positivity)
    calc 8 * r * ρ ≤ 8 * r * (1 / (131072 * r)) := this
      _ = 1 / 16384 := by field_simp; ring
      _ ≤ 1 / 1024 := by norm_num
  have h8ρ : 8 * ρ ≤ 1 / (16384 * r) := by
    have := mul_le_mul_of_nonneg_left hρr (show (0 : ℝ) ≤ 8 by norm_num)
    calc 8 * ρ ≤ 8 * (1 / (131072 * r)) := this
      _ = 1 / (16384 * r) := by field_simp; ring
  have h8ρ' : 8 * ρ ≤ 1 / (8192 * r) := h8ρ.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
  have hsub : ∀ j' ∈ Finset.univ.filter (CConf r δ ρ c I₀ x v z w j),
      Tube ρ (z j') (w j') ⊆ Container (787 * r * ρ) (cpt c (z j) (w j)) (w j) := by
    intro j' hj'
    obtain ⟨-, hn', h3 | h3 | h3⟩ := (Finset.mem_filter.mp hj').2
    · obtain ⟨i, -, ha, hb⟩ := h3
      exact (dilate_container hr hδ hρ hρr' (hv i) (hw j) (hw j') hn'.2 ha hb).trans
        (container_mono (by nlinarith) _ _)
    · exact overlap_container (a := 8 * r * ρ) (ρ₀ := 8 * ρ) (by linarith) (by ring)
        (by positivity) ha1 h8ρ' (by
          have e : 3 * (16 * (8 * ρ) / (1 / (1024 * r))) = 393216 * r * ρ := by
            field_simp; ring
          rw [e]; nlinarith) (hw j) (hw j') hn'.2 h3
    · exact overlap_container_rev (a := 8 * r * ρ) (ρ₀ := 8 * ρ) (by linarith) (by ring)
        (by positivity) ha1 h8ρ (by
          have e : 3 * (16 * (8 * ρ) / (1 / (2048 * r))) = 786432 * r * ρ := by
            field_simp; ring
          rw [e]; nlinarith) (hw j) (hw j') hn'.2 h3
  have h := card_le_of_container hρ (by positivity) hΛ1 z w hw hsep (cpt c (z j) (w j)) (w j)
    (hw j) _ hsub
  have hρ4 : 0 < ρ ^ 4 := by positivity
  have he : 1000000 * (200000000000 * (787 * r * ρ) ^ 2) ^ 2 = conflictConst * r ^ 4 * ρ ^ 4 := by
    unfold conflictConst; ring
  rw [he] at h
  exact le_of_mul_le_mul_right h hρ4

theorem fconf_card_le {n : ℕ} {r δ : ℝ} (hr : 16 ≤ r) (hδ : 0 < δ)
    (hδr : δ ≤ 1 / (131072 * r)) {c : Space} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i i', i ≠ i' → volume (Tube δ (x i) (v i) ∩ Tube δ (x i') (v i')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) (i : Fin n) :
    ((Finset.univ.filter (FConf r δ c x v i)).card : ℝ) ≤ conflictConst * r ^ 4 := by
  classical
  have hr0 : 0 < r := by linarith
  by_cases hi : cpar c (x i) (v i) ∈ Icc (-(1 / 4) : ℝ) (5 / 4)
  swap
  · have : Finset.univ.filter (FConf r δ c x v i) = ∅ := by
      apply Finset.filter_false_of_mem
      intro i' _ h
      exact hi h.1
    rw [this, Finset.card_empty, Nat.cast_zero]
    unfold conflictConst; positivity
  have hΛ1 : 787 * r * δ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hδr (show (0 : ℝ) ≤ 787 * r by positivity)
    calc 787 * r * δ ≤ 787 * r * (1 / (131072 * r)) := by linarith
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; nlinarith
  have ha1 : r * δ ≤ 1 / 1024 := by
    have := mul_le_mul_of_nonneg_left hδr (show (0 : ℝ) ≤ r by positivity)
    calc r * δ ≤ r * (1 / (131072 * r)) := this
      _ = 1 / 131072 := by field_simp
      _ ≤ 1 / 1024 := by norm_num
  have hδ' : δ ≤ 1 / (16384 * r) := hδr.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
  have hδ'' : δ ≤ 1 / (8192 * r) := hδ'.trans (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
  have hsub : ∀ i' ∈ Finset.univ.filter (FConf r δ c x v i),
      Tube δ (x i') (v i') ⊆ Container (787 * r * δ) (cpt c (x i) (v i)) (v i) := by
    intro i' hi'
    obtain ⟨-, hn', h3 | h3⟩ := (Finset.mem_filter.mp hi').2
    · exact overlap_container (a := r * δ) (ρ₀ := δ) (by linarith) rfl hδ ha1 hδ'' (by
          have e : 3 * (16 * δ / (1 / (1024 * r))) = 49152 * r * δ := by field_simp; ring
          rw [e]; nlinarith) (hv i) (hv i') hn' h3
    · exact overlap_container_rev (a := r * δ) (ρ₀ := δ) (by linarith) rfl hδ ha1 hδ' (by
          have e : 3 * (16 * δ / (1 / (2048 * r))) = 98304 * r * δ := by field_simp; ring
          rw [e]; nlinarith) (hv i) (hv i') hn' h3
  have h := card_le_of_container hδ (by positivity) hΛ1 x v hv hsep (cpt c (x i) (v i)) (v i)
    (hv i) _ hsub
  have hδ4 : 0 < δ ^ 4 := by positivity
  have he : 1000000 * (200000000000 * (787 * r * δ) ^ 2) ^ 2 = conflictConst * r ^ 4 * δ ^ 4 := by
    unfold conflictConst; ring
  rw [he] at h
  exact le_of_mul_le_mul_right h hδ4

end

end WangZahlLot.Obl.wz_c2_slope_normalization
