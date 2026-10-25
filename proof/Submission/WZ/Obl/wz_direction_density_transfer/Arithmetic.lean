-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_direction_density_transfer.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_direction_density_transfer.Basic

namespace WangZahlLot.Obl.wz_direction_density_transfer

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Any finite family of positive-radius tubes admits a finite slab bound. -/
theorem finite_slab_bound {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space) :
    ∃ l : ℝ, 1 ≤ l ∧ ∀ W : Set Space,
      ENNReal.ofReal ((ncard {i : Fin n | Tube δ (x i) (v i) ⊆ W} : ℕ) : ℝ) ≤
        ENNReal.ofReal (l * (n : ℝ)) * volume W := by
  classical
  let b : ℝ := (volume (ball (0 : Space) δ)).toReal
  have hb : 0 < b := ENNReal.toReal_pos
    (measure_ball_pos volume _ hδ).ne' measure_ball_lt_top.ne
  refine ⟨max 1 b⁻¹, le_max_left _ _, fun W => ?_⟩
  by_cases he : {i : Fin n | Tube δ (x i) (v i) ⊆ W} = ∅
  · simp [he]
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr he
  have hball : ball (x i) δ ⊆ W :=
    (ball_subset_thickening (left_mem_segment ℝ (x i) (x i + v i)) δ).trans hi
  have hbW : ENNReal.ofReal b ≤ volume W := by
    rw [ENNReal.ofReal_toReal measure_ball_lt_top.ne]
    calc
      volume (ball (0 : Space) δ) = volume (ball (x i) δ) := by
        exact (Measure.addHaar_ball_center volume (x i) δ).symm
      _ ≤ volume W := measure_mono hball
  have hcard : (ncard {i : Fin n | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤ n := by
    exact_mod_cast ((Set.ncard_le_card {i : Fin n | Tube δ (x i) (v i) ⊆ W}).trans_eq (Nat.card_fin n))
  calc
    ENNReal.ofReal ((ncard {i : Fin n | Tube δ (x i) (v i) ⊆ W} : ℕ) : ℝ)
      ≤ ENNReal.ofReal (n : ℝ) := ENNReal.ofReal_le_ofReal hcard
    _ = ENNReal.ofReal (b⁻¹ * (n : ℝ)) * ENNReal.ofReal b := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (max 1 b⁻¹ * (n : ℝ)) * volume W := by
      gcongr
      exact le_max_right _ _

/-- The convex count for the unit ball gives a global bound on the tube count. -/
theorem global_count {δ M : ℝ} (hM : 0 ≤ M) {n : ℕ} {x v : Fin n → Space}
    (hc : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((ncard {i : Fin n | Tube δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal M * volume W)
    (hcont : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) :
    (n : ℝ) * δ ^ 2 ≤ M * (volume (ball (0 : Space) 1)).toReal := by
  have h := hc (ball 0 1) (convex_ball (0 : Space) 1)
  simp only [hcont, Set.ofPred_true, Set.ncard_univ, Nat.card_fin] at h
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    measure_ball_lt_top.ne) h
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hM] at h'
  exact h'

/-- Once a positive proportion is essentially distinct, the endpoint gives every density. -/
theorem transfer_of_extraction (hExtract : Extraction) (hCount : UniformConvexCount)
    (hEndpoint : Endpoint) : DirectionEstimate := by
  classical
  obtain ⟨C, hC, hExtract⟩ := hExtract
  obtain ⟨M, hM, hCount⟩ := hCount
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  intro ε hε
  obtain ⟨a, ha, η, hη, hEndpoint⟩ := hEndpoint ε hε
  let B : ℝ := M * (volume (ball (0 : Space) 1)).toReal
  have hB : 0 < B := mul_pos hM0 (ENNReal.toReal_pos
    (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne)
  let c : ℝ := min (a / (M * C)) B⁻¹
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hc₁ : c ≤ a / (M * C) := min_le_left _ _
  have hc₂ : c ≤ B⁻¹ := min_le_right _ _
  refine ⟨2 / η + 1, c, hc, 1 / 100, by norm_num, ?_⟩
  intro δ hδ hδ1 lam hlam hlam1 n x v Y hv hsep hcont hYm hY hden
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hδ01 : δ ≤ 1 := by linarith
  have hδpow : 0 ≤ δ ^ ε := Real.rpow_nonneg hδ.le _
  have hδpow1 : δ ^ ε ≤ 1 := Real.rpow_le_one hδ.le hδ01 hε.le
  have hconv := hCount δ hδ hδ1 n x v hv hsep hcont
  by_cases hdense : δ ^ η ≤ lam
  · obtain ⟨k, e, hk, he, hnk, hdist⟩ :=
      hExtract δ hδ hδ1 n x v hn0 hv hsep hcont
    obtain ⟨l, hl, hslab⟩ := finite_slab_bound hδ (x ∘ e) (v ∘ e)
    have hconv' := hCount δ hδ hδ1 k (x ∘ e) (v ∘ e)
      (fun i => hv (e i)) (fun i j hij => hsep (e i) (e j) (he.ne hij))
      (fun i => hcont (e i))
    have hsum : ENNReal.ofReal (δ ^ η * (k : ℝ) * δ ^ 2) ≤
        ∑ i : Fin k, volume (Y (e i)) := by
      calc
        ENNReal.ofReal (δ ^ η * (k : ℝ) * δ ^ 2) =
            ∑ _i : Fin k, ENNReal.ofReal (δ ^ η * δ ^ 2) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          congr 1
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
        _ ≤ _ := Finset.sum_le_sum (fun i _ =>
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hdense (sq_nonneg δ))).trans
            (hden (e i)))
    have hend := hEndpoint δ hδ hδ1 M l hM hl k (x ∘ e) (v ∘ e) (Y ∘ e) hk
      (fun i => hv (e i)) (fun i => hcont (e i)) hdist
      (fun i => hYm (e i)) (fun i => hY (e i)) hsum hconv'
      (fun u t r _ _ => hslab (ball 0 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r}))
    simp only [zero_add, neg_zero, Real.rpow_zero, mul_one] at hend
    have hlamκ : lam ^ (2 / η + 1) ≤ 1 :=
      Real.rpow_le_one hlam.le hlam1 (by positivity)
    have hbound : c * δ ^ ε * lam ^ (2 / η + 1) * ((n : ℝ) * δ ^ 2) ≤
        a * δ ^ ε * M⁻¹ * ((k : ℝ) * δ ^ 2) := by
      calc
        c * δ ^ ε * lam ^ (2 / η + 1) * ((n : ℝ) * δ ^ 2) ≤
            (a / (M * C)) * δ ^ ε * 1 * ((C * (k : ℝ)) * δ ^ 2) := by
          gcongr
        _ = _ := by field_simp
    exact ((ENNReal.ofReal_le_ofReal hbound).trans hend).trans
      (measure_mono (iUnion_subset (fun i => subset_iUnion Y (e i))))
  · have hpack : (n : ℝ) * δ ^ 2 ≤ B := global_count hM0.le hconv hcont
    have hlam_pow : lam ^ (2 / η) ≤ δ ^ 2 := by
      calc
        lam ^ (2 / η) ≤ (δ ^ η) ^ (2 / η) :=
          Real.rpow_le_rpow hlam.le (le_of_not_ge hdense) (by positivity)
        _ = δ ^ 2 := by
          rw [← Real.rpow_mul hδ.le, show η * (2 / η) = (2 : ℝ) by field_simp,
            Real.rpow_two]
    have hbound : c * δ ^ ε * lam ^ (2 / η + 1) * ((n : ℝ) * δ ^ 2) ≤ lam * δ ^ 2 := by
      calc
        c * δ ^ ε * lam ^ (2 / η + 1) * ((n : ℝ) * δ ^ 2) =
            lam * δ ^ 2 * (c * δ ^ ε * (lam ^ (2 / η) * (n : ℝ))) := by
          rw [Real.rpow_add_one hlam.ne']
          ring
        _ ≤ lam * δ ^ 2 * (c * 1 * (δ ^ 2 * (n : ℝ))) := by gcongr
        _ ≤ lam * δ ^ 2 * (B⁻¹ * 1 * B) := by
          gcongr
          simpa [mul_comm] using hpack
        _ = lam * δ ^ 2 := by rw [mul_one, inv_mul_cancel₀ hB.ne', mul_one]
    exact ((ENNReal.ofReal_le_ofReal hbound).trans (hden ⟨0, hn0⟩)).trans
      (measure_mono (subset_iUnion Y ⟨0, hn0⟩))

end WangZahlLot.Obl.wz_direction_density_transfer
