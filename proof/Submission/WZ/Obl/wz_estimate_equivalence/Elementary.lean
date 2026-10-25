-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.Elementary.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_estimate_equivalence.Estimates
import Submission.WZ.Obl.wz_estimate_equivalence.Descent

namespace WangZahlLot.Obl.wz_estimate_equivalence

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The average shading density gives a lower bound for the union without any geometry. -/
theorem average_density_le_union {n : ℕ} (hn : 0 < n) (Y : Fin n → Set Space)
    {r : ℝ} (hr : 0 ≤ r)
    (hdens : ENNReal.ofReal (r * (n : ℝ)) ≤
      Finset.sum Finset.univ (fun i : Fin n => volume (Y i))) :
    ENNReal.ofReal r ≤ volume (⋃ i : Fin n, Y i) := by
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  apply (ENNReal.mul_le_mul_iff_right hn0 (by simp)).mp
  calc
    (n : ENNReal) * ENNReal.ofReal r = ENNReal.ofReal (r * (n : ℝ)) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n), mul_comm]
    _ ≤ Finset.sum Finset.univ (fun i : Fin n => volume (Y i)) := hdens
    _ ≤ Finset.sum Finset.univ (fun _ : Fin n => volume (⋃ i : Fin n, Y i)) := by
      exact Finset.sum_le_sum fun i _ => measure_mono (Set.subset_iUnion Y i)
    _ = (n : ENNReal) * volume (⋃ i : Fin n, Y i) := by simp [nsmul_eq_mul]

/-- At `σ = 0`, the trivial starting estimate requires only the convex count in the unit ball. -/
theorem e_zero_two : E 0 2 := by
  intro ε hε
  let C : ℝ := Real.pi * 4 / 3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C⁻¹, inv_pos.mpr hC, ε, hε, ?_⟩
  intro δ hδ hδmax m l hm hl n x v Y hn hv hT hsep hY hYT hdens hK hF
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hcount : {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.ball (0 : Space) 1} = Set.univ := Set.eq_univ_of_forall hT
  have hmass : (n : ℝ) * δ ^ 2 ≤ m * C := by
    have h := hK (Metric.ball (0 : Space) 1) (convex_ball (0 : Space) 1)
    simp only [hcount, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
      EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul] at h
    rw [← ENNReal.ofReal_mul hm0.le] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hm0.le hC.le)).mp h
  have hnorm : C⁻¹ * m⁻¹ * ((n : ℝ) * δ ^ 2) ≤ 1 := by
    calc
      C⁻¹ * m⁻¹ * ((n : ℝ) * δ ^ 2) ≤ C⁻¹ * m⁻¹ * (m * C) := by gcongr
      _ = 1 := by field_simp
  have hδpow : δ ^ ((2 : ℝ) + ε) = δ ^ ε * δ ^ 2 := by
    rw [add_comm, Real.rpow_add hδ, Real.rpow_two]
  have hbound : C⁻¹ * δ ^ ((2 : ℝ) + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) ≤
      δ ^ ε * δ ^ 2 := by
    calc
      C⁻¹ * δ ^ ((2 : ℝ) + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) =
          (δ ^ ε * δ ^ 2) * (C⁻¹ * m⁻¹ * ((n : ℝ) * δ ^ 2)) := by
        rw [hδpow]
        ring
      _ ≤ (δ ^ ε * δ ^ 2) * 1 := by gcongr
      _ = _ := mul_one _
  have hdens' : ENNReal.ofReal ((δ ^ ε * δ ^ 2) * (n : ℝ)) ≤
      Finset.sum Finset.univ (fun i : Fin n => volume (Y i)) := by
    convert hdens using 1
    congr 1
    ring
  have hU := average_density_le_union hn Y (by positivity) hdens'
  simpa only [neg_zero, Real.rpow_zero, mul_one] using
    (ENNReal.ofReal_le_ofReal hbound).trans hU

theorem e_zero_of_two_le {ω : ℝ} (hω : 2 ≤ ω) : E 0 ω :=
  e_mono_omega hω e_zero_two

end WangZahlLot.Obl.wz_estimate_equivalence
