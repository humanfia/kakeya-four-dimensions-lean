-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.PairWidth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Diagonal

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric

theorem wideSection_of_pair {U : Set Space} {r κ : ℝ} (hr : 0 ≤ r) (hκ : 0 ≤ κ)
    (c e f : Space)
    (hlower : ∀ s t : ℝ, κ * |s| ≤ ‖s • e + t • f‖ ∧
      κ * |t| ≤ ‖s • e + t • f‖)
    (hdiamond : ∀ s t : ℝ, |s| + |t| ≤ r → c + s • e + t • f ∈ U) :
    WideSection U (κ * r / 2) := by
  intro ℓ
  have hc : c ∈ U := by simpa using hdiamond 0 0 (by simpa using hr)
  have hcase (e f : Space)
      (hlo : ∀ s t : ℝ, κ * |s| ≤ ‖s • e + t • f‖)
      (hdi : ∀ s t : ℝ, |s| + |t| ≤ r → c + s • e + t • f ∈ U)
      (hcmp : |ℓ e| ≤ |ℓ f|) :
      ∃ p ∈ U, ∃ q ∈ U, ℓ (p - q) = 0 ∧ κ * r / 2 ≤ dist p q := by
    by_cases hz : ℓ f = 0
    · have hz' : ℓ e = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hz] using hcmp) (abs_nonneg _))
      refine ⟨c + (r / 2) • e, ?_, c, hc, ?_, ?_⟩
      · simpa using hdi (r / 2) 0 (by rw [abs_of_nonneg (by positivity)]; simp; linarith)
      · simp [hz']
      · have hh := hlo (r / 2) 0
        simpa [dist_eq_norm, abs_of_nonneg (by positivity : 0 ≤ r / 2), mul_div_assoc] using hh
    · let t : ℝ := -(r / 2) * (ℓ e / ℓ f)
      have ht : |t| ≤ r / 2 := by
        have hh : |ℓ e / ℓ f| ≤ 1 := by
          rw [abs_div, div_le_one (abs_pos.mpr hz)]
          exact hcmp
        calc
          |t| = (r / 2) * |ℓ e / ℓ f| := by
            rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
          _ ≤ (r / 2) * 1 := mul_le_mul_of_nonneg_left hh (by positivity)
          _ = _ := mul_one _
      let p := c + (r / 2) • e + t • f
      have hdiff : p - c = (r / 2) • e + t • f := by dsimp [p]; abel
      refine ⟨p, hdi _ _ (by rw [abs_of_nonneg (by positivity)]; linarith), c, hc, ?_, ?_⟩
      · rw [hdiff, map_add, map_smul, map_smul]
        dsimp [t]
        field_simp
        ring
      · rw [dist_eq_norm, hdiff]
        simpa [abs_of_nonneg (by positivity : 0 ≤ r / 2), mul_div_assoc] using hlo (r / 2) t
  rcases le_total |ℓ e| |ℓ f| with hcmp | hcmp
  · exact hcase e f (fun s t => (hlower s t).1) hdiamond hcmp
  · apply hcase f e (fun s t => by simpa [add_comm] using (hlower t s).2) _ hcmp
    intro s t hst
    simpa [add_assoc, add_left_comm, add_comm] using hdiamond t s (by simpa [add_comm] using hst)

/-- A direction with a definite transverse coordinate forms a quantitative plane
with the shortest coordinate axis. -/
theorem coordinate_pair_lower {v : Space} (hv0 : |v 0| ≤ 1 / 2)
    {j : Fin 3} (hj : j ≠ 0) (hvj : 1 / 32 ≤ |v j|) (s t : ℝ) :
    (1 / 32 : ℝ) * |s| ≤ ‖s • EuclideanSpace.basisFun (Fin 3) ℝ 0 + t • v‖ ∧
    (1 / 32 : ℝ) * |t| ≤ ‖s • EuclideanSpace.basisFun (Fin 3) ℝ 0 + t • v‖ := by
  let p := s • EuclideanSpace.basisFun (Fin 3) ℝ 0 + t • v
  have hp0 : p 0 = s + t * v 0 := by simp [p, EuclideanSpace.basisFun_apply]
  have hpj : p j = t * v j := by simp [p, EuclideanSpace.basisFun_apply, EuclideanSpace.single, hj, Ne.symm hj]
  have h0 : |p 0| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have hj' : |p j| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p j
  have ht : (1 / 32 : ℝ) * |t| ≤ ‖p‖ := by
    rw [hpj, abs_mul] at hj'
    nlinarith [mul_le_mul_of_nonneg_left hvj (abs_nonneg t)]
  have hs : |s| ≤ ‖p‖ + |t| / 2 := by
    have habs := abs_sub (s + t * v 0) (t * v 0)
    rw [add_sub_cancel_right, abs_mul] at habs
    rw [hp0] at h0
    nlinarith [mul_le_mul_of_nonneg_left hv0 (abs_nonneg t)]
  exact ⟨by dsimp [p] at *; nlinarith [norm_nonneg p], ht⟩

theorem wideSection_of_coordinate_pair {U : Set Space} {r : ℝ} (hr : 0 ≤ r)
    (c v : Space) (hv0 : |v 0| ≤ 1 / 2)
    {j : Fin 3} (hj : j ≠ 0) (hvj : 1 / 32 ≤ |v j|)
    (hdiamond : ∀ s t : ℝ, |s| + |t| ≤ r →
      c + s • EuclideanSpace.basisFun (Fin 3) ℝ 0 + t • v ∈ U) :
    WideSection U (r / 64) := by
  convert wideSection_of_pair hr (by norm_num : (0 : ℝ) ≤ 1 / 32) c
    (EuclideanSpace.basisFun (Fin 3) ℝ 0) v (coordinate_pair_lower hv0 hj hvj) hdiamond using 1
  ring

end WangZahlLot.Obl.wz_flat_factored_improvement
