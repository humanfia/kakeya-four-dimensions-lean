/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/CandidateRestore.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_intercept_concentration.OriginalMass
import Submission.Obl.k4_critical_intercept_concentration.Inherited.AffinePrimitive
import Submission.Obl.k4_seven_direction_local_degree_restoration.Affine

namespace Submission.Obl.k4_critical_intercept_concentration

open MeasureTheory MvPolynomial Set
open scoped ENNReal

noncomputable section

/-- The affine test produced by a heavy intercept has polynomially bounded
coefficients whenever its primitive and offset do. -/
theorem affine_hidden_test_coefficients (L : Fin 4 → ℝ) (offset Z : ℝ)
    (hZ : 1 ≤ Z) (hL₀ : L 0 = 0) (hL : ∀ i : Fin 3, |L i.succ| ≤ Z)
    (hoffset : |offset| ≤ Z) (e : Fin 4 →₀ ℕ) :
    |(Inherited.affineHiddenTest L offset).coeff e| ≤ 5 * Z := by
  have heq : Inherited.affineHiddenTest L offset =
      Submission.Obl.k4_seven_direction_local_degree_restoration.affinePoly
        (-offset) ![-L 1, -L 2, -L 3, 1] := by
    simp [Inherited.affineHiddenTest,
      Submission.Obl.k4_seven_direction_local_degree_restoration.affinePoly,
      Fin.sum_univ_four, hL₀]
    ring
  rw [heq]
  apply Submission.Obl.k4_seven_direction_local_degree_restoration.affinePoly_coeff_le
    (by linarith) (by simpa using hoffset)
  intro i
  fin_cases i
  · simpa using hL 0
  · simpa using hL 1
  · simpa using hL 2
  · simpa using hZ

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The quadratic alternative, at a fixed actual true label. -/
def QuadraticCandidate (cfg : Data α) (k : ℕ) (s v ε R : ℝ)
    (i : Fin (cfg.n k s)) : Prop :=
  ∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧
    (∀ e, |Q.coeff e| ≤ cfg.N k ^ R *
      ((1 + ∑ e ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff e|) +
        ∑ e ∈ (cfg.P k).support, |(cfg.P k).coeff e|) ^ R) ∧
    ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
        cfg.fit k (cfg.N k ^ ε) (cfg.N k ^ (-s - v)) Q p.1
          (I (cfg.T k s) (cfg.j k s i)) ∧
        cfg.N k ^ (-ε) ≤ |eval (cfg.x k p.1 p.2) (pderiv (3 : Fin 4) Q)|}

/-- A source event with a whole-block affine test gives the exact frozen
quadratic alternative, with its original measure and true assignment prior. -/
theorem quadratic_candidate_of_affine_source (h : cfg.Valid)
    (k : ℕ) (s v ε R Z offset : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (E : Set (α × ℝ)) (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hZ : 1 ≤ Z) (hL₀ : L 0 = 0) (hL : ∀ j : Fin 3, |L j.succ| ≤ Z)
    (hoffset : |offset| ≤ Z) (hcoeff : 5 * Z ≤ cfg.N k ^ R)
    (hsource : ∀ p ∈ E, p.1 ∈ cfg.B k s i ∧
      p.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
      ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |eval (cfg.x k p.1 t) (Inherited.affineHiddenTest L offset)| ≤
          cfg.N k ^ ε * cfg.N k ^ (-s - v))
    (hmass : ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤ cfg.ρ k E) :
    cfg.QuadraticCandidate k s v ε R i := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hpower : 1 ≤ cfg.N k ^ ε := Real.one_le_rpow hN1 hε
  have hsmall : cfg.N k ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hnorm : 1 ≤
      ((1 + ∑ e ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff e|) +
        ∑ e ∈ (cfg.P k).support, |(cfg.P k).coeff e|) := by
    have hf : 0 ≤ ∑ e ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff e| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hp : 0 ≤ ∑ e ∈ (cfg.P k).support, |(cfg.P k).coeff e| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  refine ⟨Inherited.affineHiddenTest L offset,
    (Inherited.affineHiddenTest_totalDegree _ _).trans (by norm_num), ?_, ?_⟩
  · intro e
    calc
      _ ≤ 5 * Z := affine_hidden_test_coefficients L offset Z hZ hL₀ hL hoffset e
      _ ≤ cfg.N k ^ R := hcoeff
      _ ≤ _ := le_mul_of_one_le_right (Real.rpow_nonneg hN.le _)
        (Real.one_le_rpow hnorm hR)
  · refine hmass.trans (measure_mono ?_)
    intro p hp
    obtain ⟨hb, ht, hfit⟩ := hsource p hp
    refine ⟨hb, ht, ?_, ?_⟩
    · intro t ht
      refine ⟨hfit t ht, ?_, ?_⟩
      · simpa only [Inherited.affineHiddenTest_hidden_derivative, map_one, abs_one] using hpower
      · simp only [Inherited.affineHiddenTest_hidden_second, map_zero, abs_zero]
        positivity
    · simpa only [Inherited.affineHiddenTest_hidden_derivative, map_one, abs_one] using hsmall


/-- Enlarging the single fixed coefficient exponent preserves a candidate. -/
theorem QuadraticCandidate.mono_exponent (h : cfg.Valid) {k : ℕ} {s v ε R R' : ℝ}
    {i : Fin (cfg.n k s)} (a : cfg.QuadraticCandidate k s v ε R i) (hRR' : R ≤ R') :
    cfg.QuadraticCandidate k s v ε R' i := by
  obtain ⟨Q, hQ, hc, hm⟩ := a
  refine ⟨Q, hQ, ?_, hm⟩
  have hN : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hnorm : 1 ≤
      ((1 + ∑ e ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff e|) +
        ∑ e ∈ (cfg.P k).support, |(cfg.P k).coeff e|) := by
    have hf : 0 ≤ ∑ e ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff e| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hp : 0 ≤ ∑ e ∈ (cfg.P k).support, |(cfg.P k).coeff e| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith
  intro e
  refine (hc e).trans ?_
  gcongr

/-- A fixed positive gain and a fixed coefficient exponent suffice for the
complete quantifier order of the frozen critical candidate assertion. -/
theorem candidates_of_fixed_gain (h : cfg.Valid) {s v R₀ : ℝ}
    (hs : 0 < s) (hv : 0 < v) (hsU : s + v ≤ cfg.U)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      ∃ i : Fin (cfg.n k s), cfg.QuadraticCandidate k s v ε R₀ i) :
    cfg.Candidates := by
  let R := 2 + |R₀| + s + v + s⁻¹ + v⁻¹
  have hs' : 0 < s⁻¹ := inv_pos.mpr hs
  have hv' : 0 < v⁻¹ := inv_pos.mpr hv
  have hR : 1 < R := by dsimp [R]; linarith [abs_nonneg R₀]
  have hRs : s ≤ R := by dsimp [R]; linarith [abs_nonneg R₀]
  have hRv : v ≤ R := by dsimp [R]; linarith [abs_nonneg R₀]
  have hR₀ : R₀ ≤ R := by dsimp [R]; linarith [le_abs_self R₀]
  have hsi : R⁻¹ ≤ s := (inv_le_comm₀ (by linarith) hs).mpr (by dsimp [R]; linarith [abs_nonneg R₀])
  have hvi : R⁻¹ ≤ v := (inv_le_comm₀ (by linarith) hv).mpr (by dsimp [R]; linarith [abs_nonneg R₀])
  refine ⟨R, hR, ?_⟩
  intro ε hε
  apply (hc ε hε).mono
  rintro k ⟨i, hi⟩
  exact ⟨s, v, i, hsi, hRs, hvi, hRv, hsU, Or.inl (hi.mono_exponent h hR₀)⟩

end Data

end

end Submission.Obl.k4_critical_intercept_concentration
