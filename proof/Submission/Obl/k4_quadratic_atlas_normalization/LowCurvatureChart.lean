import Submission.Obl.k4_quadratic_atlas_normalization.HighCurvatureChart

-- Adapted from this LOT tree, o104, session x0350, commit 0e2b59568680,
-- Submission/Obl/k4_terminal_time_extension/LowCurvatureChart.lean.

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set MvPolynomial

/-- Exact chart assembly after the low-curvature derivative-size refinement.
The new assignment and selection are subsets of the original ones; the only
extra selection condition is the normalized derivative floor. -/
theorem low_curvature_chart
    {N κ κ' j L a r B v : ℝ} {M M' D D' T : ℕ}
    {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A A' : Set (ℕ × (Fin 6 → ℝ))}
    {F F' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (hN : 1 ≤ N) (hM : M ≤ M') (hκ : 1 ≤ κ) (hκκ' : κ ≤ κ')
    (hκ' : 2 ≤ κ') (hB : 0 < B) (hv : 0 < v)
    (hthick : δ N L * N ^ a / v ≤ δ N r)
    (hcoef : N ^ M / v ≤ N ^ M')
    (hcurv : |curvature R (3 : Fin 4)| / v ≤ κ' * B ^ 2 / δ N r)
    (hAA' : A' ⊆ A) (hFF' : F' ⊆ F) (hFA' : ∀ p ∈ F', p.1 ∈ A')
    (hA' : MeasurableSet A') (hF' : MeasurableSet F')
    (hformat' : ∀ i,
      fmt 6 (N ^ M') D' {z | (i, z) ∈ A'} ∧
      fmt 7 (N ^ M') D' {z : Fin 7 → ℝ |
        ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ F'})
    (hupper : ∀ l ∈ A', ∀ t ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T),
      |eval (x l t) (pderiv (3 : Fin 4) R)| ≤ κ' * v * B)
    (hfloor : ∀ p ∈ F', v * B / κ' ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) R)|)
    (h : rough N M D κ T j L a B E c u Q R A F ex) (hext : ex') :
    chart N M' D' κ' T j r B E c u Q (C v⁻¹ * R) A' F' ex' := by
  have hpow : N ^ M ≤ N ^ M' := pow_le_pow_right₀ hN hM
  have hδ : 0 < δ N r := by unfold δ; positivity
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  rcases h with ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, _hA, _hF,
    _hformat, hwhole, hselected, _hdiscriminant, _hext⟩
  have hscale (S : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) :
      |eval z (C v⁻¹ * S)| = |eval z S| / v := by
    simp [abs_mul, abs_of_pos hv, div_eq_mul_inv, mul_comm]
  have hd : pderiv (3 : Fin 4) (C v⁻¹ * R) = C v⁻¹ * pderiv 3 R := pderiv_C_mul
  have hdd : pderiv (3 : Fin 4) (pderiv 3 (C v⁻¹ * R)) =
      C v⁻¹ * C (curvature R 3) := by
    rw [hd, pderiv_C_mul, second_pderiv_eq_curvature R hdeg 3]
  refine ⟨hdet, hcu.trans hpow, hframe.trans hpow,
    hsize.trans (div_le_div_of_nonneg_right hκκ' (by positivity)), ?_, ?_,
    hA', hF', hformat', ?_, ?_, hext⟩
  · apply (totalDegree_mul _ _).trans
    simpa only [totalDegree_C, zero_add] using hdeg
  · intro e
    simp only [coeff_C_mul, abs_mul, abs_inv, abs_of_pos hv]
    calc
      v⁻¹ * |R.coeff e| ≤ v⁻¹ * N ^ M :=
        mul_le_mul_of_nonneg_left (hcoeff e) (by positivity)
      _ = N ^ M / v := by ring
      _ ≤ _ := hcoef
  · intro l hl
    obtain ⟨htag, hcoords, hfits⟩ := hwhole l (hAA' hl)
    refine ⟨htag.trans hpow, fun e => (hcoords e).trans hpow, ?_⟩
    intro t ht
    obtain ⟨hspatial, hvalue, _hderiv, _hcurv⟩ := hfits t ht
    refine ⟨hspatial.trans hκκ', ?_, ?_, ?_⟩
    · rw [hscale]
      calc
        |eval (x l t) R| / v ≤ (κ * δ N L * N ^ a) / v :=
          div_le_div_of_nonneg_right hvalue hv.le
        _ = κ * (δ N L * N ^ a / v) := by ring
        _ ≤ κ * δ N r := mul_le_mul_of_nonneg_left hthick hκpos.le
        _ ≤ κ' * δ N r := mul_le_mul_of_nonneg_right hκκ' hδ.le
    · rw [hd, hscale]
      calc
        |eval (x l t) (pderiv 3 R)| / v ≤ (κ' * v * B) / v :=
          div_le_div_of_nonneg_right (hupper l hl t ht) hv.le
        _ = κ' * B := by field_simp
    · rw [hdd, hscale, eval_C]
      exact hcurv
  · intro p hp
    obtain ⟨hpE, _hpA, htime⟩ := hselected p (hFF' hp)
    refine ⟨hpE, hFA' p hp, htime, ?_⟩
    rw [hd, hscale]
    apply (le_div_iff₀ hv).mpr
    convert hfloor p hp using 1 <;> ring

end Submission.Obl.k4_quadratic_atlas_normalization
