import Submission.Obl.k4_scalar_critical_path_terminal.Interfaces

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_critical_path_terminal.Split

open MeasureTheory Filter

/-- Encode the checked framework data in the Mathlib-only frozen carrier. -/
noncomputable def encode (ed : Data) : Code :=
  ⟨ed.W, ed.N, ed.K, ed.M, ed.D, ed.L, ed.d, ed.S, ed.U,
    ed.ω, ed.ν, ed.E, ed.g, ed.G, ed.f⟩

theorem exact_encode (ed : Data) : Exact (encode ed) ↔ ed.Exact := by
  rfl

/-- Discard the additional temperedness and knowledge certificates, and enlarge
selected incidence sets to the original assignments times their blocks. -/
theorem chart_readout (ed : Data) (B k : ℕ) (h ε : ℝ)
    (hc : Chart (encode ed) B ed.L ed.L h ε true k) : ed.SystemAt h ε k := by
  obtain ⟨T, n, γ, j, A, C, u, v, J, P, Λ, ht, hn, hm, hd, hC, hg,
    hsize, hmeas, hlist, hmass⟩ := hc
  refine ⟨T, n, γ, j, A, u, v, J, P, ht, fun i => (hm i).1, hd, ?_, ?_⟩
  · intro i
    obtain ⟨hpos, hJ, hinv, hwidth, hcenter, hdegree, hcoeff, hsupport,
      hAfmt, hCfmt, hfit, hfloor⟩ := hg i
    refine ⟨hJ, hwidth, hcenter, hdegree, hfit, (hfloor rfl).trans ?_⟩
    exact measure_mono fun z hz => (hC i hz).2
  · refine hmass.trans (Finset.sum_le_sum fun a _ => ?_)
    apply mul_le_mul_of_nonneg_left ?_ zero_le
    apply measure_mono
    rintro z ⟨i, hi, hz⟩
    exact ⟨i, hi, (hC i hz).2.1, (hC i hz).2.2⟩

/-- Increasing either requested budget preserves the raw true system. -/
theorem systemAt_mono (ed : Data) (k : ℕ) (h h' ε ε' : ℝ)
    (hN : 1 ≤ ed.N k) (hh : h ≤ h') (hε : ε ≤ ε') :
    ed.SystemAt h ε k → ed.SystemAt h' ε' k := by
  intro hs
  obtain ⟨T, n, γ, j, A, u, v, J, P, htime, hmeas, hdisj, hg, hmass⟩ := hs
  have hpow := Real.rpow_le_rpow_of_exponent_le hN hε
  have hbase : 0 < ed.N k := lt_of_lt_of_le zero_lt_one hN
  have hq : 0 < (2 : ℝ) ^ T := by positivity
  refine ⟨T, n, γ, j, A, u, v, J, P,
    htime.trans (Real.rpow_le_rpow_of_exponent_le hN hh), hmeas, hdisj, ?_, ?_⟩
  · intro i
    obtain ⟨hJ, hwidth, hcenter, hdegree, hfit, hfloor⟩ := hg i
    refine ⟨hJ, hwidth.trans (div_le_div_of_nonneg_right hpow hq.le),
      hcenter.trans hpow, hdegree, ?_, ?_⟩
    · intro l hl t ht
      obtain ⟨hy, hx⟩ := hfit l hl t ht
      exact ⟨hy.trans (mul_le_mul_of_nonneg_right hpow hJ.le),
        hx.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hbase.le _))⟩
    · refine (ENNReal.ofReal_le_ofReal ?_).trans hfloor
      exact div_le_div_of_nonneg_left
        (mul_nonneg (Real.rpow_nonneg hbase.le _) hJ.le)
        (mul_pos (Real.rpow_pos_of_pos hbase _) hq)
        (mul_le_mul_of_nonneg_right hpow hq.le)
  · exact (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hε))).trans hmass

/-- Initial systems make the horizon infimum a nonempty, nonnegative one. -/
theorem horizon_nonnegative (hI : Initial) (p : Code) (hp : Exact p) :
    0 ≤ Horizon p := by
  exact horizon_nonneg ⟨L p, hI p hp⟩ fun h hh => hh.1

/-- The extremizer selection only needs the numerical conclusions. The
actual refinement remains available to the guarded tangent child. -/
theorem calculus_weak (hc : Calculus) : WeakCalculus := by
  obtain ⟨hs, hco, hn⟩ := hc
  refine ⟨hs, hco, ?_⟩
  intro p r b h d' hp hr hrL hrb hbL hd hd1 hf hk
  obtain ⟨q, hq, hL, hD, hS, hU, hRef, hH, hProf, hEq⟩ :=
    hn p r b h d' hp hr hrL hrb hbL hd hd1 hf hk
  exact ⟨q, hq, hL, hD, hS, hU, hH, hProf, hEq⟩

/-- Zero rich horizon gives the exact frozen raw-system conclusion. No
normalization of a selected incidence law enters this readout. -/
theorem exactConclusion_of_zero (hI : Initial)
    (hz : ∀ p : Code, Exact p → Horizon p = 0) : ExactConclusion := by
  apply exactConclusion_of
  intro ed hed h ε hh hε
  let p := encode ed
  have hp : Exact p := (exact_encode ed).2 hed
  have hlt : sInf {a : ℝ | Cost p a} < h / 2 := by
    change Horizon p < h / 2
    rw [hz p hp]
    positivity
  obtain ⟨a, ha, hah⟩ := exists_lt_of_csInf_lt ⟨L p, hI p hp⟩ hlt
  obtain ⟨ha0, B, hB, hsystems⟩ := ha
  let δ := min ε (h / 2)
  have hδ : 0 < δ := lt_min hε (half_pos hh)
  have hδε : δ ≤ ε := min_le_left _ _
  have had : a + δ ≤ h := by
    have hd := min_le_right ε (h / 2)
    dsimp [δ]
    linarith
  apply (hsystems δ hδ).mono
  intro k hk
  exact systemAt_mono ed k (a + δ) h δ ε
    (by have hn := hed.1.1 k; linarith) had hδε (chart_readout ed B k (a + δ) δ hk)

end Submission.Obl.k4_scalar_critical_path_terminal.Split
