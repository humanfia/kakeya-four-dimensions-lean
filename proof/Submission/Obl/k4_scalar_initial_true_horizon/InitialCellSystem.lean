import Submission.Obl.k4_scalar_initial_true_horizon.InitialCellCharts
import Submission.Obl.k4_scalar_initial_true_horizon.InitialCellFormat
import Submission.Obl.k4_scalar_initial_true_horizon.Basic
import Submission.Obl.k4_scalar_initial_true_horizon.Raw

/-! Assemble a finite family of original-law good cells into a raw true chart. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial)

noncomputable def initialAssignment (p : Data) (k T : ℕ) (j : Fin (2 ^ T))
    (m : ℤ) (lev : ℕ) (c : ℤ × ℤ) : Set Trajectory :=
  cellSet (N p k ^ (M p : ℝ)) (K p k) (N p k ^ (-L p)) (1 / (2 : ℝ) ^ T)
    ((j : ℕ) / (2 : ℝ) ^ T) m lev c

noncomputable def initialIncidences (p : Data) (k T : ℕ) (a : Fin (worlds p k))
    (j : Fin (2 ^ T)) (m : ℤ) (lev : ℕ) (c : ℤ × ℤ) : Set Incidence :=
  event p k a ∩ (initialAssignment p k T j m lev c ×ˢ I T j)

/-- Adding the already selected original event to a cell does not change
its mass under the original incidence law. -/
theorem initialIncidences_mu_eq {p : Data} (hp : Exact p) (k T : ℕ)
    (a : Fin (worlds p k)) (j : Fin (2 ^ T)) (m : ℤ) (lev : ℕ) (c : ℤ × ℤ) :
    mu p k a (initialIncidences p k T a j m lev c) =
      mu p k a (initialAssignment p k T j m lev c ×ˢ I T j) := by
  have hA : MeasurableSet (initialAssignment p k T j m lev c) :=
    cellSet_measurable _ _ _ _ _ _ _ _
  have hS := hA.prod (measurableSet_Icc : MeasurableSet (I T j))
  change (((prior p k a).prod volume).restrict (event p k a))
      (event p k a ∩ (initialAssignment p k T j m lev c ×ˢ I T j)) =
    (((prior p k a).prod volume).restrict (event p k a)) (initialAssignment p k T j m lev c ×ˢ I T j)
  dsimp only [I]
  rw [Measure.restrict_apply ((hp.event_measurable k a).inter hS), Measure.restrict_apply hS]
  congr 1
  ext z
  simp only [mem_inter_iff]
  tauto

/-- All geometric/format clauses are automatic for a family of initial cells.
The covering argument need only supply disjointness, counting, widths, true
original-law floors, and the total selected original mass. -/
theorem rawChart_of_cells {p : Data} (hp : Exact p) {k T n B : ℕ} {h ε : ℝ}
    (hB : 1 ≤ B) (hMB : M p ≤ B) (hDB : D p ≤ B)
    (γ : Fin n → Fin (worlds p k)) (j : Fin n → Fin (2 ^ T))
    (m : Fin n → ℤ) (lev : Fin n → ℕ) (c : Fin n → ℤ × ℤ)
    (hT : (2 : ℝ) ^ T ≤ N p k ^ h) (hn : (n : ℝ) ≤ N p k ^ (B : ℝ))
    (hqL : 1 / (2 : ℝ) ^ T ≤ N p k ^ (-L p))
    (hformat : N p k ^ (M p : ℝ) + 18 ≤ N p k ^ (B : ℝ))
    (hslack : 4 * K p k + 3 ≤ N p k ^ ε)
    (hparam : 4 * K p k + 3 ≤ N p k ^ (B : ℝ))
    (hinv : ∀ i, (cellJ (1 / (2 : ℝ) ^ T) (lev i))⁻¹ ≤ N p k ^ (B : ℝ))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' →
      Disjoint (initialAssignment p k T (j i) (m i) (lev i) (c i))
        (initialAssignment p k T (j i') (m i') (lev i') (c i')))
    (hfloor : ∀ i, ENNReal.ofReal (N p k ^ (-profile p (L p)) *
        cellJ (1 / (2 : ℝ) ^ T) (lev i) / (N p k ^ ε * (2 : ℝ) ^ T)) ≤
      mu p k (γ i) (initialIncidences p k T (γ i) (j i) (m i) (lev i) (c i)))
    (hmass : ENNReal.ofReal (N p k ^ (-ε)) ≤ ∑ a, ENNReal.ofReal (weight p k a) *
      mu p k a {z | ∃ i, γ i = a ∧ z ∈ initialIncidences p k T (γ i) (j i) (m i) (lev i) (c i)}) :
    RawChart p B (L p) (L p) h ε true k := by
  let q := 1 / (2 : ℝ) ^ T
  let s := fun i => ((j i : ℕ) : ℝ) / (2 : ℝ) ^ T
  let aL := N p k ^ (-L p)
  let A := fun i => initialAssignment p k T (j i) (m i) (lev i) (c i)
  let C := fun i => initialIncidences p k T (γ i) (j i) (m i) (lev i) (c i)
  let u := fun i => cellU q (s i) (lev i) (c i)
  let v := fun i => cellV (lev i) (c i)
  let J := fun i => cellJ q (lev i)
  let P := fun i => cellP aL (m i)
  have hN : 1 ≤ N p k := by linarith [hp.resolution_ge k]
  have hN0 : 0 < N p k := zero_lt_one.trans_le hN
  have hK : 0 ≤ K p k := by linarith [hp.slack_ge k]
  have hq : 0 < q := by dsimp [q]; positivity
  have ha : 0 < aL := Real.rpow_pos_of_pos hN0 _
  have ha1 : aL ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith [hp.length_pos])
  have hq1 : q ≤ 1 := hqL.trans ha1
  have hΛ : 1 ≤ N p k ^ ε := by linarith [hp.slack_ge k]
  have hΛ2 : 2 ≤ N p k ^ ε := by linarith [hp.slack_ge k]
  have hKM : K p k ≤ N p k ^ ε := by linarith
  have hpoly : 3 * K p k + 1 ≤ N p k ^ (B : ℝ) := by linarith
  have hNM : 1 ≤ N p k ^ (M p : ℝ) := Real.one_le_rpow hN (Nat.cast_nonneg _)
  have h16 : (16 : ℝ) ≤ N p k ^ (B : ℝ) := by linarith
  have hheight : N p k ^ (M p : ℝ) ≤ N p k ^ (B : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by exact_mod_cast hMB)
  have hI : ∀ i, I T (j i) = Icc (s i) (s i + q) := by
    intro i
    dsimp [I, s, q]
    congr 1
    ring
  have hs : ∀ i, s i ∈ Icc (0 : ℝ) 1 := by
    intro i
    apply I_subset_unit T (j i)
    rw [hI i]
    exact ⟨le_rfl, by linarith⟩
  have hpos : ∀ i, 0 < mu p k (γ i) (C i) := by
    intro i
    apply lt_of_lt_of_le _ (hfloor i)
    apply ENNReal.ofReal_pos.mpr
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hN0 _) (cellJ_pos hq (lev i)))
      (mul_pos (Real.rpow_pos_of_pos hN0 _) (by positivity))
  have hne : ∀ i, (A i).Nonempty := by
    intro i
    obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero (ne_of_gt (hpos i))
    exact ⟨z.1, hz.2.1⟩
  refine ⟨T, n, γ, j, A, C, u, v, J, P, hT, hn, ?_, hdisj, ?_, ?_, hmass⟩
  · intro i
    exact ⟨cellSet_measurable _ _ _ _ _ _ _ _,
      measurableSet_cellIncidences _ _ _ _ _ _ _ _ (hp.event_measurable k (γ i)) T (j i)⟩
  · intro i
    exact subset_rfl
  · intro i
    refine ⟨hpos i, cellJ_pos hq (lev i), hinv i, ?_, ?_, cellP_degree _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        J i ≤ q := cellJ_le hq.le (lev i)
        _ ≤ N p k ^ ε * q := le_mul_of_one_le_left hq.le hΛ
        _ = _ := by dsimp [q]; ring
    · exact (cellSet_center_bound hK ha hq hq1 (hs i) (hne i)).trans hslack
    · intro b
      exact (cellP_coeff_bound hK ha ha1 hq (hs i) (hne i) b).trans hpoly
    · intro l hl
      exact ⟨hl.1.1.trans hheight, fun e => (hl.1.2 e).trans hKM⟩
    · intro z
      exact (cellSet_fiber_format _ _ _ _ _ ha hq (m i) (lev i) (c i) z).mono h16 hB
    · intro z
      have hf := cellIncidences_fiber_format (Nb := N p k ^ (M p : ℝ)) (Kb := K p k) (t₀ := s i) ha hq hNM (m i) (lev i) (c i) T (j i)
        (event p k (γ i)) (((hp.2.1 k).2.2.2.1 (γ i)).2.2.2.2.2.2) z
      exact hf.mono hformat (max_le hDB hB)
    · intro l hl t ht
      have ht' : t ∈ Icc (s i) (s i + q) := by simpa only [hI i] using ht
      have ht1 := I_subset_unit T (j i) ht
      constructor
      · exact (cellSet_spatial_fit ha hq hl ht').trans
          (mul_le_mul_of_nonneg_right hΛ2 (cellJ_pos hq (lev i)).le)
      · exact (cellSet_hidden_fit hK ha hq hqL (hs i) hl ht1 ht').trans
          (mul_le_mul_of_nonneg_right (by linarith : 3 * K p k + 1 ≤ N p k ^ ε) ha.le)
    · intro _
      exact hfloor i

end Submission.Obl.k4_scalar_initial_true_horizon
