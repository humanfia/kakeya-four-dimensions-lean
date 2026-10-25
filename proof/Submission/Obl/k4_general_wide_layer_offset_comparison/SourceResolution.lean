import Submission.Obl.k4_general_wide_layer_offset_comparison.BasicFacts
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeSourceCaps
import Submission.Obl.k4_general_wide_layer_offset_comparison.DomainCoordinates

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/SourceResolution.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- A sufficiently fine primitive base mesh resolves every projected
polynomial at the required native thickness. Only the projected coefficients
are bounded; the native polynomial is kept at its original source event. -/
theorem projected_variation_on_good {k : ℕ} {r smax B : ℝ}
    (hN : 1 ≤ p.N k) (hK : 1 ≤ p.K k) (hr : 0 ≤ r) (hB : 0 ≤ B)
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (hcoeff : ∀ e, |G.coeff e| ≤ B)
    (hresolution : 54 * B * (p.K k + 1) ^ 4 * p.N k ^ (-r) ≤ p.N k ^ (-smax))
    {ω : α × ℝ} (hω : ω ∈ p.baseGood k) (y : Fin 3 → ℝ)
    (hclose : ∀ i, |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i - y i| ≤
      p.N k ^ (-r)) :
    |eval ![ω.2, (p.x k ω.1 ω.2) 2] G - eval ![y 0, y 2] G| ≤ p.N k ^ (-smax) := by
  have hNp : 0 < p.N k := zero_lt_one.trans_le hN
  have hbase := p.baseGood_base_bound hK hω
  have hx : ∀ i : Fin 3,
      |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i| ≤ p.K k := by
    intro i
    fin_cases i
    · exact hbase 0
    · exact hbase 1
    · exact hbase 2
  exact (projected_predictor_variation G hG hB hK
    (Real.rpow_nonneg hNp.le _) (Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hr))
    hcoeff _ y hx hclose).trans hresolution

/-- A source domain's time and velocity anchors are controlled by the
original bounded line, regardless of the size of its integer code. -/
theorem baseGood_domain_bounds {k : ℕ} {h g b : ℝ}
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b)
    {ω : α × ℝ} (hω : ω ∈ p.baseGood k) :
    let d := p.domainCode k h g b ω
    0 ≤ domainTime h d ∧ domainTime h d ≤ 1 ∧
      |domainVelocity g d| ≤ p.K k + g := by
  obtain ⟨ht, hclip⟩ := hω
  have hK4 : |p.b k ω.1 4| ≤ p.K k := by
    linarith [abs_nonneg (p.b k ω.1 0), abs_nonneg (p.b k ω.1 1), abs_nonneg (p.b k ω.1 3)]
  have htime0 : (0 : ℝ) ≤ (⌊ω.2 / h⌋ : ℤ) := by
    exact_mod_cast Int.floor_nonneg.mpr (div_nonneg ht.1 hh.le)
  have htime1 : (⌊ω.2 / h⌋ : ℝ) * h ≤ ω.2 := (le_div_iff₀ hh).mp (Int.floor_le (ω.2 / h))
  have hbin : |p.b k ω.1 4 - (⌊p.b k ω.1 4 / g⌋ : ℝ) * g| ≤ g := by
    simpa using normalized_bin_bound (show (0 : ℝ) < 1 by norm_num) hg
      (x := p.b k ω.1 4) (center := 0) (j := ⌊p.b k ω.1 4 / g⌋) (by simp)
  refine ⟨?_, ?_, ?_⟩
  · change 0 ≤ (⌊ω.2 / h⌋ : ℝ) * h
    exact mul_nonneg htime0 hh.le
  · change (⌊ω.2 / h⌋ : ℝ) * h ≤ 1
    exact htime1.trans ht.2
  · change |(⌊p.b k ω.1 4 / g⌋ : ℝ) * g| ≤ p.K k + g
    calc
      _ ≤ |(⌊p.b k ω.1 4 / g⌋ : ℝ) * g - p.b k ω.1 4| + |p.b k ω.1 4| := by
        simpa only [sub_zero] using abs_sub_le ((⌊p.b k ω.1 4 / g⌋ : ℝ) * g) (p.b k ω.1 4) 0
      _ ≤ g + p.K k := add_le_add (by simpa only [abs_sub_comm] using hbin) hK4
      _ = _ := add_comm _ _

/-- The actual original velocity bin has a bounded physical anchor. -/
theorem baseGood_major_velocity_bound {k : ℕ} {m : ℝ} (hN : 0 < p.N k)
    {ω : α × ℝ} (hω : ω ∈ p.baseGood k) :
    |(⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)| ≤ p.K k + p.N k ^ (-m) := by
  have hK3 : |p.b k ω.1 3| ≤ p.K k := by
    linarith [hω.2, abs_nonneg (p.b k ω.1 0), abs_nonneg (p.b k ω.1 1), abs_nonneg (p.b k ω.1 4)]
  have hbin : |p.b k ω.1 3 - (⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)| ≤ p.N k ^ (-m) := by
    simpa using normalized_bin_bound (show (0 : ℝ) < 1 by norm_num) (Real.rpow_pos_of_pos hN _)
      (x := p.b k ω.1 3) (center := 0) (j := ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋) (by simp)
  calc
    _ ≤ |(⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m) - p.b k ω.1 3| + |p.b k ω.1 3| := by
      simpa only [sub_zero] using abs_sub_le ((⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)) (p.b k ω.1 3) 0
    _ ≤ p.N k ^ (-m) + p.K k := add_le_add (by simpa only [abs_sub_comm] using hbin) hK3
    _ = _ := add_comm _ _

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
