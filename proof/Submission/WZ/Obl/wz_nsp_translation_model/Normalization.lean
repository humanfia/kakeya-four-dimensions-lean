-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_translation_model.Normalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_translation_model.Counting

namespace WangZahlLot.Obl.wz_nsp_translation_model

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

lemma rounded_copies {r ρ M : ℝ} (hr : 0 < r) (hM : 0 < M) :
    ∃ N : ℕ, ρ ^ 2 ≤ (N : ℝ) * M * r ^ 2 ∧
      (N : ℝ) * M * r ^ 2 ≤ ρ ^ 2 + M * r ^ 2 ∧
      (N : ℝ) ≤ ρ ^ 2 / (M * r ^ 2) + 1 := by
  have hd : 0 < M * r ^ 2 := mul_pos hM (sq_pos_of_pos hr)
  refine ⟨⌈ρ ^ 2 / (M * r ^ 2)⌉₊, ?_, ?_, (Nat.ceil_lt_add_one (by positivity)).le⟩
  · have h := (div_le_iff₀ hd).mp (Nat.le_ceil (ρ ^ 2 / (M * r ^ 2)))
    simpa only [mul_assoc] using h
  · have h := mul_le_mul_of_nonneg_right
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ ρ ^ 2 / (M * r ^ 2))).le hd.le
    rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at h
    simpa only [mul_assoc] using h

lemma count_real {r L : ℝ} (hL : 0 ≤ L) {W : Set Space} (hW : volume W ≠ ⊤)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ENNReal.ofReal (c * r ^ 2) ≤ ENNReal.ofReal L * volume W) :
    c * r ^ 2 ≤ L * volume.real W := by
  have hh := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hc (sq_nonneg r)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hL, Measure.real] using hh

lemma normalized_load_bounds {q r L V : ℝ} (hq : 0 ≤ q) (hL : 0 < L) (hV : 0 < V)
    (hq1 : q * r ^ 2 ≤ L * V) :
    0 ≤ q * r ^ 2 / (L * V) ∧ q * r ^ 2 / (L * V) ≤ 1 := by
  exact ⟨by positivity, (div_le_one (mul_pos hL hV)).mpr hq1⟩

lemma normalized_average {r ρ M L V : ℝ} {m N : ℕ} (q : Fin m → ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hM : 0 < M) (hL : 1 ≤ 384 * L) (hV : 0 < V)
    (hN : (N : ℝ) ≤ ρ ^ 2 / (M * r ^ 2) + 1)
    (hq0 : ∀ s, 0 ≤ q s) (hq1 : ∀ s, q s * r ^ 2 ≤ L * V)
    (hqavg : (∑ s, q s) * ρ ^ 2 ≤ 4096 * (m : ℝ) * M * V) :
    (N : ℝ) * ∑ s, q s * r ^ 2 / (L * V) ≤ 1572865 * (m : ℝ) := by
  have hLpos : 0 < L := by linarith
  let E : ℝ := ∑ s, q s * r ^ 2 / (L * V)
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun s _ =>
    (normalized_load_bounds (hq0 s) hLpos hV (hq1 s)).1)
  have hE1 : E ≤ (m : ℝ) := by
    calc
      E ≤ ∑ _s : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun s _ =>
        (normalized_load_bounds (hq0 s) hLpos hV (hq1 s)).2)
      _ = m := by simp
  have hEG : E ≤ 4096 * (m : ℝ) * M * r ^ 2 / (L * ρ ^ 2) := by
    apply (le_div_iff₀ (mul_pos hLpos (sq_pos_of_pos hρ))).mpr
    have hS : E = (∑ s, q s) * r ^ 2 / (L * V) := by
      simp only [E, Finset.sum_div, Finset.sum_mul]
    rw [hS]
    calc
      (∑ s, q s) * r ^ 2 / (L * V) * (L * ρ ^ 2) =
          (((∑ s, q s) * ρ ^ 2) / V) * r ^ 2 := by field_simp [hLpos.ne', hV.ne', hr.ne', hM.ne', hρ.ne']
      _ ≤ ((4096 * (m : ℝ) * M * V) / V) * r ^ 2 := by gcongr
      _ = 4096 * (m : ℝ) * M * r ^ 2 := by rw [mul_div_cancel_right₀ _ hV.ne']
  change (N : ℝ) * E ≤ _
  have hInv : 1 / L ≤ 384 := (div_le_iff₀ hLpos).mpr (by linarith)
  calc
    (N : ℝ) * E ≤ (ρ ^ 2 / (M * r ^ 2) + 1) * E :=
      mul_le_mul_of_nonneg_right hN hE0
    _ = (ρ ^ 2 / (M * r ^ 2)) * E + E := by ring
    _ ≤ (ρ ^ 2 / (M * r ^ 2)) *
        (4096 * (m : ℝ) * M * r ^ 2 / (L * ρ ^ 2)) + (m : ℝ) := by gcongr
    _ = 4096 * (m : ℝ) * (1 / L) + (m : ℝ) := by field_simp [hLpos.ne', hV.ne', hr.ne', hM.ne', hρ.ne']
    _ ≤ 4096 * (m : ℝ) * 384 + (m : ℝ) := by gcongr
    _ = 1572865 * (m : ℝ) := by ring

lemma reconstruct_loads {r L : ℝ} (hL : 0 < L) {W : Set Space}
    (hWpos : 0 < volume W) (hWfin : volume W ≠ ⊤)
    {n N m : ℕ} (p : Fin m → Fin n → Prop) (f : Fin N → Fin m) (u : ℝ)
    (hu : 0 ≤ u)
    (hsum : (∑ j, (ncard {i : Fin n | p (f j) i} : ℝ) * r ^ 2 /
      (L * volume.real W)) ≤ u) :
    ENNReal.ofReal ((ncard {q : Fin N × Fin n | p (f q.1) q.2} : ℝ) * r ^ 2)
      ≤ ENNReal.ofReal (u * L) * volume W := by
  have hV : 0 < volume.real W := ENNReal.toReal_pos hWpos.ne' hWfin
  have hr : (ncard {q : Fin N × Fin n | p (f q.1) q.2} : ℝ) * r ^ 2 ≤
      (u * L) * volume.real W := by
    rw [ncard_prod_sum (fun j i => p (f j) i)]
    have h := (div_le_iff₀ (mul_pos hL hV)).mp (show
      (∑ j, (ncard {i : Fin n | p (f j) i} : ℝ)) * r ^ 2 / (L * volume.real W) ≤ u by
        simpa only [Finset.sum_div, Finset.sum_mul] using hsum)
    simpa only [mul_assoc] using h
  have h := ENNReal.ofReal_le_ofReal hr
  rwa [ENNReal.ofReal_mul (mul_nonneg hu hL.le),
    Measure.real, ENNReal.ofReal_toReal hWfin] at h

end WangZahlLot.Obl.wz_nsp_translation_model
