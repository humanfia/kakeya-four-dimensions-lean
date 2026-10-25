-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Regularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Counts

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Discarding weights below half the average retains at least half the total weight. -/
theorem heavy_weights {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) (hw : 0 < ∑ i, w i) :
    ∃ S : Finset (Fin n), S.Nonempty ∧
      (∑ i, w i) / 2 ≤ ∑ i ∈ S, w i ∧
      ∀ i ∈ S, (∑ j, w j) / (2 * n) ≤ w i := by
  classical
  let t : ℝ := (∑ i, w i) / (2 * n)
  let S := Finset.univ.filter (fun i => t ≤ w i)
  let R := Finset.univ.filter (fun i => ¬t ≤ w i)
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hRcard : (R.card : ℝ) ≤ n := by
    exact_mod_cast (show R.card ≤ n from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))
  have hsmall : (∑ i ∈ R, w i) ≤ (∑ i, w i) / 2 := by
    calc
      _ ≤ ∑ i ∈ R, t := Finset.sum_le_sum fun i hi =>
        (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
      _ = (R.card : ℝ) * t := by simp
      _ ≤ n * t := mul_le_mul_of_nonneg_right hRcard ht
      _ = (∑ i, w i) / 2 := by dsimp [t]; field_simp
  have hsplit : (∑ i ∈ S, w i) + (∑ i ∈ R, w i) = ∑ i, w i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hlarge : (∑ i, w i) / 2 ≤ ∑ i ∈ S, w i := by linarith
  have hS : S.Nonempty := by
    by_contra hS
    have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [this, Finset.sum_empty] at hlarge
    linarith
  exact ⟨S, hS, hlarge, fun i hi => (Finset.mem_filter.mp hi).2⟩

/-- A dense admissible shading has a nonempty half-mass part with a pointwise density bound. -/
theorem Admissible.heavy_indices {d η M L : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Admissible d η M L n x v Y) (hd : 0 < d) :
    ∃ S : Finset (Fin n), S.Nonempty ∧
      (1 / 2 : ENNReal) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Y i) ∧
      ∀ i ∈ S, ENNReal.ofReal (d ^ η * d ^ 2 / 2) ≤ volume (Y i) := by
  classical
  have hfin : ∀ i, volume (Y i) ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top measure_ball_ne_top
      (measure_mono ((h.2.1 i).2.2.2.trans (h.2.1 i).2.1))
  have hsum : (∑ i, volume (Y i)).toReal = ∑ i, (volume (Y i)).toReal :=
    ENNReal.toReal_sum (fun i _ => hfin i)
  have hpos : 0 < ∑ i, (volume (Y i)).toReal := by
    rw [← hsum]
    exact ENNReal.toReal_pos (ne_of_gt (h.mass_pos hd)) h.mass_ne_top
  obtain ⟨S, hS, hmass, hpoint⟩ := heavy_weights h.1 (fun i => (volume (Y i)).toReal) hpos
  refine ⟨S, hS, ?_, ?_⟩
  · have hmass' := ENNReal.ofReal_le_ofReal hmass
    have hhalf : ENNReal.ofReal ((∑ i, (volume (Y i)).toReal) / 2) =
        (1 / 2 : ENNReal) * (∑ i, volume (Y i)) := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)),
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
      simp only [ENNReal.ofReal_toReal (hfin _)]
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num [mul_comm]
    rw [hhalf, ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)] at hmass'
    simpa only [ENNReal.ofReal_toReal (hfin _)] using hmass'
  · intro i hi
    have hden := ENNReal.toReal_mono h.mass_ne_top h.2.2.2.1
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ d ^ η * (n : ℝ) * d ^ 2), hsum] at hden
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr h.1
    have hlow : d ^ η * d ^ 2 / 2 ≤ (∑ j, (volume (Y j)).toReal) / (2 * n) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
      nlinarith
    have hreal := hlow.trans (hpoint i hi)
    have hbound := ENNReal.ofReal_le_ofReal hreal
    simpa only [ENNReal.ofReal_toReal (hfin i)] using hbound

end WangZahlLot.Obl.wz_multiscale_finite_tower
