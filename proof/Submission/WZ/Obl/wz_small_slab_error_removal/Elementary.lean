-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_slab_error_removal.Elementary.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_slab_error_removal.Interfaces

namespace WangZahlLot.Obl.wz_small_slab_error_removal

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Model

theorem family_mono : MonotoneFamily Family := by
  intro d d' δ m l l' hd hl n U h
  obtain ⟨x, v, Y, hA, hK, hS, rfl⟩ := h
  obtain ⟨hn, hv, hb, ho, hY, hsub, hden⟩ := hA
  refine ⟨x, v, Y, ⟨hn, hv, hb, ho, hY, hsub, ?_⟩, hK, ?_, rfl⟩
  · apply le_trans (ENNReal.ofReal_le_ofReal _) hden
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n)) (sq_nonneg δ)
  · intro u t r hu hr
    apply (hS u t r hu hr).trans
    gcongr

theorem admissible_union_lower {d δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible d δ n x v Y) :
    ENNReal.ofReal (d * δ ^ 2) ≤ volume (⋃ i, Y i) := by
  have hn : 0 < n := h.1
  have hsum : (∑ i, volume (Y i)) ≤
      ∑ _i : Fin n, volume (⋃ i, Y i) :=
    Finset.sum_le_sum fun i _ => measure_mono (Set.subset_iUnion Y i)
  have hden := h.2.2.2.2.2.2.trans hsum
  rw [show d * (n : ℝ) * δ ^ 2 = (n : ℝ) * (d * δ ^ 2) by ring,
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast] at hden
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hden
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  have hntop : (n : ENNReal) ≠ ⊤ := by simp
  exact (ENNReal.mul_le_mul_iff_right hn0 hntop).mp hden

/-- The only bounds on a realized family needed by the abstract transfer. -/
theorem family_bounds (hpack : Packing) : ∃ C : ℝ, 1 ≤ C ∧ Bounds Family C := by
  obtain ⟨C₀, hC₀, hpack⟩ := hpack
  let b : ℝ := (volume (Metric.ball (0 : Space) 1)).toReal
  let C : ℝ := max 1 (max (C₀ * b ^ 2) b)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCp : C₀ * b ^ 2 ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCb : b ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC1, ?_⟩
  intro d δ m l hδ hδ100 hm n U hF
  obtain ⟨x, v, Y, hA, hK, hS, rfl⟩ := hF
  obtain ⟨hn, hv, hb, ho, hY, hsub, hden⟩ := hA
  have hP := hpack δ hδ hδ100 n x v (Metric.ball (0 : Space) 1)
    (convex_ball _ _) (Set.Subset.refl _) hv hb ho
  have hfinite : volume (Metric.ball (0 : Space) 1) ≠ ⊤ := measure_ball_ne_top
  have hPr : (n : ℝ) * δ ^ 4 ≤ C₀ * b ^ 2 := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hfinite)) hP
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (n : ℝ) * δ ^ 4),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ C₀),
      ENNReal.toReal_pow] using h
  have hKball := hK (Metric.ball (0 : Space) 1) (convex_ball _ _)
  have hcount : {i : Fin n | Tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1} =
      Set.univ := Set.eq_univ_of_forall hb
  rw [hcount] at hKball
  simp only [Set.ncard_univ, Nat.card_fin] at hKball
  have hKr : (n : ℝ) * δ ^ 2 ≤ m * b := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hKball
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (n : ℝ) * δ ^ 2),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ m)] using h
  refine ⟨hn, hPr.trans hCp, ?_, admissible_union_lower
    ⟨hn, hv, hb, ho, hY, hsub, hden⟩⟩
  calc
    (n : ℝ) * δ ^ 2 ≤ m * b := hKr
    _ ≤ m * C := mul_le_mul_of_nonneg_left hCb (by linarith)
    _ = C * m := mul_comm _ _

end WangZahlLot.Obl.wz_small_slab_error_removal
