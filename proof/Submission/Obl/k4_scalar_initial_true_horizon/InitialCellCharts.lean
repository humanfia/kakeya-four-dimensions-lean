import Submission.Obl.k4_scalar_initial_true_horizon.InitialCellDefs
import Submission.Obl.k4_scalar_initial_true_horizon.Format

/-! Per-cell geometric and format clauses for x0444's initial atlas cells. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial)
open scoped ENNReal BigOperators

theorem cellJ_pos {q : ℝ} (hq : 0 < q) (k : ℕ) : 0 < cellJ q k :=
  div_pos hq (by positivity)

theorem cellJ_le {q : ℝ} (hq : 0 ≤ q) (k : ℕ) : cellJ q k ≤ q := by
  exact (div_le_self hq (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))

theorem cellSet_measurable (Nb Kb aL q t₀ : ℝ) (m : ℤ) (k : ℕ) (c : ℤ × ℤ) :
    MeasurableSet (cellSet Nb Kb aL q t₀ m k c) := by
  have hB : MeasurableSet {l : Coeff | bddTraj Nb Kb l} := by
    have heq : {l : Coeff | bddTraj Nb Kb l} =
        {l : Coeff | (l.1 : ℝ) ≤ Nb} ∩ ⋂ e : Fin 5, {l : Coeff | |l.2 e| ≤ Kb} := by
      ext l
      simp only [bddTraj, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [heq]
    apply (measurableSet_le ((measurable_of_countable (fun z : ℕ => (z : ℝ))).comp measurable_fst) measurable_const).inter
    apply MeasurableSet.iInter
    intro e
    exact measurableSet_le ((measurable_pi_apply e).comp measurable_snd).abs measurable_const
  have hX : Measurable (xBin aL t₀) := by
    unfold xBin Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden
    fun_prop
  have hC : Measurable (cellIdx q t₀ k) := by
    unfold cellIdx spatial
    fun_prop
  exact hB.inter ((hX (measurableSet_singleton m)).inter (hC (measurableSet_singleton c)))

theorem measurableSet_cellIncidences (Nb Kb aL q t₀ : ℝ) (m : ℤ) (k : ℕ) (c : ℤ × ℤ)
    {E : Set (Coeff × ℝ)} (hE : MeasurableSet E) (T : ℕ) (j : Fin (2 ^ T)) :
    MeasurableSet (E ∩ (cellSet Nb Kb aL q t₀ m k c ×ˢ I T j)) :=
  hE.inter ((cellSet_measurable Nb Kb aL q t₀ m k c).prod measurableSet_Icc)

/-- Floor-cell membership controls the intercept, slope and Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden value at
its block start, before any event is selected. -/
theorem cellSet_coordinate_bounds {Nb Kb aL q t₀ : ℝ} {m : ℤ} {k : ℕ} {c : ℤ × ℤ}
    (ha : 0 < aL) (hq : 0 < q) {l : Coeff}
    (hl : l ∈ cellSet Nb Kb aL q t₀ m k c) :
    bddTraj Nb Kb l ∧
      |spatial l t₀ - (c.1 : ℝ) * cellJ q k| ≤ cellJ q k ∧
      |l.2 1 - cellV k c| ≤ (2 ^ k : ℝ)⁻¹ ∧
      |Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t₀ - ((m : ℝ) + 1 / 2) * aL| ≤ aL / 2 := by
  rcases hl with ⟨hB, hX, hC⟩
  have hj : 0 < cellJ q k := cellJ_pos hq k
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hyEq : ⌊spatial l t₀ / cellJ q k⌋ = c.1 := congrArg Prod.fst hC
  have hvEq : ⌊l.2 1 * (2 : ℝ) ^ k⌋ = c.2 := congrArg Prod.snd hC
  have hy := Int.floor_eq_iff.mp hyEq
  have hv := Int.floor_eq_iff.mp hvEq
  have hx := Int.floor_eq_iff.mp hX
  refine ⟨hB, ?_, ?_, ?_⟩
  · have hy0 : (c.1 : ℝ) * cellJ q k ≤ spatial l t₀ := (le_div_iff₀ hj).mp hy.1
    have hy1 : spatial l t₀ < ((c.1 : ℝ) + 1) * cellJ q k := (div_lt_iff₀ hj).mp hy.2
    exact abs_le.mpr ⟨by linarith, by nlinarith⟩
  · have hv0 : (c.2 : ℝ) / (2 : ℝ) ^ k ≤ l.2 1 := (div_le_iff₀ hpow).mpr hv.1
    have hv1 : l.2 1 < ((c.2 : ℝ) + 1) / (2 : ℝ) ^ k := (lt_div_iff₀ hpow).mpr hv.2
    dsimp [cellV]
    rw [← one_div]
    have hpinv : 0 ≤ 1 / (2 : ℝ) ^ k := by positivity
    exact abs_le.mpr ⟨by linarith, by rw [add_div] at hv1; linarith⟩
  · change (m : ℝ) ≤ Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t₀ / aL ∧ Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t₀ / aL < (m : ℝ) + 1 at hx
    have hx0 := (le_div_iff₀ ha).mp hx.1
    have hx1 := (div_lt_iff₀ ha).mp hx.2
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem cellSet_spatial_fit {Nb Kb aL q t₀ : ℝ} {m : ℤ} {k : ℕ} {c : ℤ × ℤ}
    (ha : 0 < aL) (hq : 0 < q) {l : Coeff}
    (hl : l ∈ cellSet Nb Kb aL q t₀ m k c) {t : ℝ} (ht : t ∈ Icc t₀ (t₀ + q)) :
    |spatial l t - cellU q t₀ k c - t * cellV k c| ≤ 2 * cellJ q k := by
  have h := cellSet_coordinate_bounds ha hq hl
  have hdist : |t - t₀| ≤ q := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq : spatial l t - cellU q t₀ k c - t * cellV k c =
      (spatial l t₀ - (c.1 : ℝ) * cellJ q k) + (t - t₀) * (l.2 1 - cellV k c) := by
    simp only [spatial, cellU]
    ring
  rw [heq]
  calc
    _ ≤ |spatial l t₀ - (c.1 : ℝ) * cellJ q k| + |t - t₀| * |l.2 1 - cellV k c| := by
      simpa only [abs_mul] using abs_add_le
        (spatial l t₀ - (c.1 : ℝ) * cellJ q k) ((t - t₀) * (l.2 1 - cellV k c))
    _ ≤ cellJ q k + q * (2 ^ k : ℝ)⁻¹ :=
      add_le_add h.2.1 (mul_le_mul hdist h.2.2.1 (abs_nonneg _) hq.le)
    _ = _ := by simp only [cellJ, div_eq_mul_inv]; ring

private theorem hidden_time_difference {Kb : ℝ} (hK : 0 ≤ Kb) {l : Coeff}
    (hl : ∀ e, |l.2 e| ≤ Kb) {t s q : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (hd : |t - s| ≤ q) :
    |Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t - Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l s| ≤ 3 * Kb * q := by
  have heq : Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t - Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l s = (t - s) * (l.2 3 + (t + s) * l.2 4) := by
    unfold Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden
    ring
  have hts : |t + s| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩
  have hbr : |l.2 3 + (t + s) * l.2 4| ≤ 3 * Kb := by
    calc
      _ ≤ |l.2 3| + |t + s| * |l.2 4| := by simpa only [abs_mul] using abs_add_le (l.2 3) ((t + s) * l.2 4)
      _ ≤ Kb + 2 * Kb := add_le_add (hl 3) (mul_le_mul hts (hl 4) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  rw [heq, abs_mul]
  calc
    _ ≤ q * (3 * Kb) := mul_le_mul hd hbr (abs_nonneg _) (le_trans (abs_nonneg _) hd)
    _ = _ := by ring

theorem cellSet_hidden_fit {Nb Kb aL q t₀ : ℝ} {m : ℤ} {k : ℕ} {c : ℤ × ℤ}
    (hK : 0 ≤ Kb) (ha : 0 < aL) (hq : 0 < q) (hqa : q ≤ aL)
    (hs : t₀ ∈ Icc (0 : ℝ) 1) {l : Coeff}
    (hl : l ∈ cellSet Nb Kb aL q t₀ m k c) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hblock : t ∈ Icc t₀ (t₀ + q)) :
    |Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t - MvPolynomial.eval ![t, spatial l t] (cellP aL m)| ≤ (3 * Kb + 1) * aL := by
  have h := cellSet_coordinate_bounds ha hq hl
  have hd : |t - t₀| ≤ q := abs_le.mpr ⟨by linarith [hblock.1], by linarith [hblock.2]⟩
  have hdiff := hidden_time_difference hK h.1.2 ht hs hd
  simp only [cellP, MvPolynomial.eval_C]
  calc
    _ ≤ |Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t - Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t₀| + |Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t₀ - ((m : ℝ) + 1 / 2) * aL| :=
      abs_sub_le _ _ _
    _ ≤ 3 * Kb * q + aL / 2 := add_le_add hdiff h.2.2.2
    _ ≤ _ := by nlinarith

/-- Choosing any original trace in a nonempty cell bounds its geometric
chart centre, independent of the level. -/
theorem cellSet_center_bound {Nb Kb aL q t₀ : ℝ} {m : ℤ} {k : ℕ} {c : ℤ × ℤ}
    (hK : 0 ≤ Kb) (ha : 0 < aL) (hq : 0 < q) (hq1 : q ≤ 1)
    (hs : t₀ ∈ Icc (0 : ℝ) 1) (hne : (cellSet Nb Kb aL q t₀ m k c).Nonempty) :
    |cellU q t₀ k c| + |cellV k c| ≤ 4 * Kb + 3 := by
  obtain ⟨l, hl⟩ := hne
  have h := cellSet_coordinate_bounds ha hq hl
  have hJ : cellJ q k ≤ 1 := (cellJ_le hq.le k).trans hq1
  have hp : (2 ^ k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hsabs : |t₀| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hy : |spatial l t₀| ≤ 2 * Kb := by
    unfold spatial
    calc
      _ ≤ |l.2 0| + |t₀| * |l.2 1| := by simpa only [abs_mul] using abs_add_le (l.2 0) (t₀ * l.2 1)
      _ ≤ Kb + 1 * Kb := add_le_add (h.1.2 0) (mul_le_mul hsabs (h.1.2 1) (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have hv : |cellV k c| ≤ Kb + 1 := by
    calc
      _ = |l.2 1 - (l.2 1 - cellV k c)| := by congr 1; ring
      _ ≤ |l.2 1| + |l.2 1 - cellV k c| := abs_sub _ _
      _ ≤ _ := add_le_add (h.1.2 1) (h.2.2.1.trans hp)
  have hb : |(c.1 : ℝ) * cellJ q k| ≤ 2 * Kb + 1 := by
    calc
      _ = |spatial l t₀ - (spatial l t₀ - (c.1 : ℝ) * cellJ q k)| := by congr 1; ring
      _ ≤ |spatial l t₀| + |spatial l t₀ - (c.1 : ℝ) * cellJ q k| := abs_sub _ _
      _ ≤ _ := add_le_add hy (h.2.1.trans hJ)
  calc
    _ ≤ |(c.1 : ℝ) * cellJ q k| + |t₀| * |cellV k c| + |cellV k c| := by
      unfold cellU
      have hu := abs_sub ((c.1 : ℝ) * cellJ q k) (t₀ * cellV k c)
      rw [abs_mul t₀ (cellV k c)] at hu
      exact add_le_add hu le_rfl
    _ ≤ (2 * Kb + 1) + 1 * (Kb + 1) + (Kb + 1) := by
      exact add_le_add (add_le_add hb (mul_le_mul hsabs hv (abs_nonneg _) zero_le_one)) hv
    _ = _ := by ring

theorem cellP_degree (aL : ℝ) (m : ℤ) : (cellP aL m).totalDegree ≤ 2 := by
  unfold cellP
  rw [MvPolynomial.totalDegree_C]
  omega

theorem cellP_coeff_bound {Nb Kb aL q t₀ : ℝ} {m : ℤ} {k : ℕ} {c : ℤ × ℤ}
    (hK : 0 ≤ Kb) (ha : 0 < aL) (ha1 : aL ≤ 1) (hq : 0 < q)
    (hs : t₀ ∈ Icc (0 : ℝ) 1) (hne : (cellSet Nb Kb aL q t₀ m k c).Nonempty) :
    ∀ b, |(cellP aL m).coeff b| ≤ 3 * Kb + 1 := by
  obtain ⟨l, hl⟩ := hne
  have h := cellSet_coordinate_bounds ha hq hl
  have hsabs : |t₀| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hs2 : |t₀ ^ 2| ≤ 1 := by rw [abs_pow]; nlinarith [abs_nonneg t₀]
  have hx : |Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t₀| ≤ 3 * Kb := by
    unfold Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden
    calc
      _ ≤ |l.2 2| + |t₀| * |l.2 3| + |t₀ ^ 2| * |l.2 4| := by
        calc
          _ ≤ |l.2 2 + t₀ * l.2 3| + |t₀ ^ 2 * l.2 4| := abs_add_le _ _
          _ ≤ (|l.2 2| + |t₀ * l.2 3|) + |t₀ ^ 2 * l.2 4| :=
            add_le_add (abs_add_le _ _) le_rfl
          _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ Kb + 1 * Kb + 1 * Kb :=
        add_le_add (add_le_add (h.1.2 2) (mul_le_mul hsabs (h.1.2 3) (abs_nonneg _) zero_le_one))
          (mul_le_mul hs2 (h.1.2 4) (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have hmid : |((m : ℝ) + 1 / 2) * aL| ≤ 3 * Kb + 1 := by
    have hh := abs_sub_le (((m : ℝ) + 1 / 2) * aL) (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t₀) 0
    rw [sub_zero, sub_zero, abs_sub_comm] at hh
    linarith [h.2.2.2]
  intro b
  classical
  by_cases hb : b = 0
  · unfold cellP
    simpa only [hb, MvPolynomial.coeff_C, ite_true] using hmid
  · unfold cellP
    rw [MvPolynomial.coeff_C_of_ne_zero hb, abs_zero]
    positivity

/-- A trajectory in the hidden start-bin `m` stays in a uniformly bounded
integer-bin window throughout a block of length at most `aL`. -/
theorem bounded_group_hidden_bin_window {Nb Kb aL s t : ℝ} {l : Coeff} {m : ℤ}
    (hK : 0 ≤ Kb) (ha : 0 < aL) (hl : bddTraj Nb Kb l) (hm : xBin aL s l = m)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hd : |t - s| ≤ aL)
    (R : ℕ) (hR : 3 * Kb + 1 ≤ (R : ℝ)) :
    ⌊Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden l t / aL⌋ ∈
      Icc (m - R) (m + R) := by
  let x := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden
  have hdiff : |x l t - x l s| ≤ 3 * Kb * aL := hidden_time_difference hK hl.2 ht hs hd
  have hm' := Int.floor_eq_iff.mp hm
  change (m : ℝ) ≤ x l s / aL ∧ x l s / aL < (m : ℝ) + 1 at hm'
  have hm0 := (le_div_iff₀ ha).mp hm'.1
  have hm1 := (div_lt_iff₀ ha).mp hm'.2
  have hlo : (m : ℝ) - 3 * Kb ≤ x l t / aL := by
    apply (le_div_iff₀ ha).mpr
    nlinarith [(abs_le.mp hdiff).1]
  have hhi : x l t / aL < (m : ℝ) + 1 + 3 * Kb := by
    apply (div_lt_iff₀ ha).mpr
    nlinarith [(abs_le.mp hdiff).2]
  have hfl := Int.floor_le (x l t / aL)
  have hfu := Int.lt_floor_add_one (x l t / aL)
  have hlower : (m : ℝ) - (R : ℝ) ≤ (⌊x l t / aL⌋ : ℤ) := by linarith
  have hupper : ((⌊x l t / aL⌋ : ℤ) : ℝ) ≤ (m : ℝ) + (R : ℝ) := by linarith
  constructor
  · exact_mod_cast hlower
  · exact_mod_cast hupper

end Submission.Obl.k4_scalar_initial_true_horizon
