import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Jets

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/FiniteJets.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open Set Filter
open scoped Topology

/-- A geometric Taylor remainder and a macroscopic value force one of finitely many jets. -/
theorem exists_finite_real_jet (C : ℝ) (hC : 0 < C) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (g : ℝ → ℝ), ContDiffOn ℝ q g (Ioo (-2 : ℝ) 2) →
      ∀ t ∈ Icc (0 : ℝ) 1, (1 : ℝ) / 2 ≤ |g t| →
      (∀ x ∈ Icc (0 : ℝ) t,
        |iteratedDeriv q g x| ≤ (q.factorial : ℝ) * C * (4 / 5 : ℝ) ^ q) →
      ∃ j : ℕ, j < q ∧ c ≤ |iteratedDeriv j g 0| := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 4 / 5)
    (by norm_num : (4 / 5 : ℝ) < 1)
  have hlim : Tendsto (fun q : ℕ => C * (4 / 5 : ℝ) ^ q) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  obtain ⟨q, hqsmall, hq⟩ := ((hlim.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and (eventually_ge_atTop 1)).exists
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  let c := 1 / (8 * (q : ℝ))
  refine ⟨q, hq, c, by positivity, ?_⟩
  intro g hg t ht hlarge htop
  by_contra hjet
  push Not at hjet
  have hseg : uIcc (0 : ℝ) t ⊆ Ioo (-2 : ℝ) 2 := by
    rw [uIcc_of_le ht.1]
    intro x hx
    constructor <;> linarith [hx.1, hx.2, ht.2]
  have hrem := Submission.Obl.k4_matching_switching_target_certificate.taylor_iteratedDeriv_bound
    isOpen_Ioo hg hseg (by
      rw [uIcc_of_le ht.1]
      exact htop) (j := 0) (by omega)
  simp only [iteratedDeriv_zero, Nat.sub_zero, zero_add, sub_zero] at hrem
  have htpow (j : ℕ) : |t| ^ j ≤ (1 : ℝ) := by
    exact pow_le_one₀ (abs_nonneg t) (by simpa [abs_of_nonneg ht.1] using ht.2)
  have hfac : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hr : |g t - ∑ i ∈ Finset.range q,
      iteratedDeriv i g 0 * t ^ i / (i.factorial : ℝ)| ≤ C * (4 / 5 : ℝ) ^ q := by
    apply hrem.trans
    calc
      _ ≤ ((q.factorial : ℝ) * C * (4 / 5 : ℝ) ^ q) * 1 / (q.factorial : ℝ) := by
        gcongr
        exact htpow q
      _ = C * (4 / 5 : ℝ) ^ q := by field_simp <;> ring
  have hterm (i : ℕ) (hi : i ∈ Finset.range q) :
      |iteratedDeriv i g 0 * t ^ i / (i.factorial : ℝ)| ≤ c := by
    have hi' : i < q := Finset.mem_range.mp hi
    have hfaci : (1 : ℝ) ≤ i.factorial := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos i))
    rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
    calc
      _ ≤ c * 1 / 1 := by
        gcongr
        · exact (hjet i hi').le
        · exact htpow i
      _ = c := by ring
  have hsum : |∑ i ∈ Finset.range q, iteratedDeriv i g 0 * t ^ i / (i.factorial : ℝ)| ≤ 1 / 8 := by
    calc
      _ ≤ ∑ i ∈ Finset.range q, |iteratedDeriv i g 0 * t ^ i / (i.factorial : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range q, c := Finset.sum_le_sum hterm
      _ = 1 / 8 := by simp [c]; field_simp <;> ring
  have htri : |g t| ≤
      |g t - ∑ i ∈ Finset.range q, iteratedDeriv i g 0 * t ^ i / (i.factorial : ℝ)| +
      |∑ i ∈ Finset.range q, iteratedDeriv i g 0 * t ^ i / (i.factorial : ℝ)| := by
    simpa using abs_add_le
      (g t - ∑ i ∈ Finset.range q, iteratedDeriv i g 0 * t ^ i / (i.factorial : ℝ))
      (∑ i ∈ Finset.range q, iteratedDeriv i g 0 * t ^ i / (i.factorial : ℝ))
  linarith

end Submission.Obl.k4_algebraic_real_jet_comparison
