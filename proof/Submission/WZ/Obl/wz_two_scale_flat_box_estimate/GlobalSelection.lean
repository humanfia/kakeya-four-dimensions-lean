-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.GlobalSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Fibers
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.DenseBoxes
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.DenseFine
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Packets

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open Set MeasureTheory Metric

lemma select_dense_fine_with_budget {δ D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : 112 ≤ D) {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hYB : ∀ i, Y i ⊆ ball (0 : Space) 1)
    (hmass : ENNReal.ofReal ((1 / D) * n * δ ^ 2) ≤ ∑ i, volume (Y i)) :
    ∃ (m : ℕ) (j : Fin m → Fin n), 0 < m ∧ Function.Injective j ∧
      (n : ℝ) ≤ D ^ (2 : ℕ) * m ∧
      ∀ i, ENNReal.ofReal ((1 / D ^ (2 : ℕ)) * δ ^ 2) ≤ volume (Y (j i)) := by
  have hDpos : 0 < D := by linarith
  obtain ⟨m, j, hm, hj, hret, hd⟩ := select_dense_fine hδ hδ1 (by positivity : 0 < 1 / D)
    hn x v Y hv hYT hYB hmass
  have h112 : 1 / D ^ (2 : ℕ) ≤ (1 / D) / 112 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 112)).mpr
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hD hDpos.le]
  refine ⟨m, j, hm, hj, ?_, ?_⟩
  · have hh := (mul_le_mul_of_nonneg_right h112 (Nat.cast_nonneg n)).trans hret
    rw [one_div, inv_mul_eq_div] at hh
    simpa only [mul_comm] using (div_le_iff₀ (pow_pos hDpos 2)).mp hh
  · intro i
    have hh : 1 / D ^ (2 : ℕ) ≤ (1 / D) / 2 :=
      h112.trans (by apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num))
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hh (sq_nonneg δ))).trans (hd i)

/-- Select boxes from a dense fine subfamily, retaining one common reference
fiber size and an upper bound for every original parent fiber. -/
lemma select_box_fibers {n N L m : ℕ} (hn : 0 < n) (hN : 0 < N) (hL : 0 < L)
    (f : Fin n → Fin N) (g : Fin N → Fin L) (j : Fin m → Fin n) (hj : Function.Injective j)
    {D : ℝ} (hD : 2 ≤ D)
    (hf : ∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ D * Set.ncard {i | f i = k'})
    (hg : ∀ k k', (Set.ncard {i | g i = k} : ℝ) ≤ D * Set.ncard {i | g i = k'})
    (hret : (n : ℝ) ≤ D ^ (2 : ℕ) * m) :
    ∃ (F q : ℕ) (k : Fin q → Fin L), 0 < F ∧ 0 < q ∧ Function.Injective k ∧
      (∀ l, F ≤ Set.ncard {i | g (f i) = l}) ∧
      (∀ l, (Set.ncard {i | g (f i) = l} : ℝ) ≤ D ^ (3 : ℕ) * F) ∧
      (n : ℝ) ≤ D ^ (9 : ℕ) * ((F : ℝ) * q) ∧
      (∀ l, (F : ℝ) ≤ D ^ (3 : ℕ) * Set.ncard {i | g (f (j i)) = k l}) ∧
      (∀ p, (Set.ncard {i | f i = p} : ℝ) ≤ D * n / N) ∧
      ∀ l, (D * n / N) * Set.ncard {p | g p = l} ≤ D ^ (5 : ℕ) * F := by
  have hDpos : 0 < D := by linarith
  have hcomp := balanced_composed_assignments hN f g hDpos.le hf hg
  have hsurj := balanced_assignment_surjective hn (g ∘ f) hcomp
  obtain ⟨F, hF, hmin, hmax, _⟩ :=
    WangZahlLot.Obl.wz_nonflat_factored_improvement.balanced_cover_minimum hL
      (fun i l => g (f i) = l) (by positivity : 0 ≤ D ^ (3 : ℕ))
      (fun i => ⟨g (f i), rfl⟩)
      (fun l => (Set.ncard_pos (Set.toFinite _)).mpr (hsurj l)) hcomp
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hret' : (1 / D ^ (2 : ℕ)) * n ≤ m := by
    rw [one_div, inv_mul_eq_div]
    exact (div_le_iff₀ (pow_pos hDpos 2)).mpr (by simpa only [mul_comm] using hret)
  obtain ⟨q, k, hq, hk, hsize, hlocal⟩ := select_dense_assigned_boxes hL (g ∘ f) j hj hF'
    (by positivity : 0 < D ^ (3 : ℕ)) (by positivity : 0 < 1 / D ^ (2 : ℕ))
    (fun l => Nat.cast_le.mpr (hmin l)) hmax hret'
  obtain ⟨hparent, hbudget⟩ := parent_fiber_budget hN f g hDpos.le hf hmax
  refine ⟨F, q, k, hF, hq, hk, hmin, hmax, ?_, ?_, hparent, hbudget⟩
  · have hs : (n : ℝ) ≤ 2 * D ^ (8 : ℕ) * q * F := by
      rw [one_div, inv_mul_eq_div] at hsize
      have hh := (div_le_iff₀ (by positivity)).mp hsize
      nlinarith only [hh]
    have hh := mul_le_mul_of_nonneg_right hD (by positivity : 0 ≤ D ^ 8 * q * F)
    nlinarith only [hs, hh]
  · intro l
    have he : ((1 / D ^ (2 : ℕ)) / 2) * (F : ℝ) = F / (2 * D ^ 2) := by ring
    have hh := hlocal l
    rw [he] at hh
    have hh' := (div_le_iff₀ (by positivity)).mp hh
    simp only [Function.comp_apply] at hh'
    have hmult := mul_le_mul_of_nonneg_right hD
      (by positivity : 0 ≤ D ^ 2 * (Set.ncard {i | g (f (j i)) = k l} : ℝ))
    nlinarith only [hh', hmult]

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
