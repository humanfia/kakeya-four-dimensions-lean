import Mathlib
import Submission.Lib.K4QuadraticSheets.Tube

/-!
# Simple sheets on tubes around broken segments

A lower bound `m ≤ |disc|` on the `r`-tube around a segment keeps the roots of the discriminant
along the segment's line `r / |b - a|`-far from the parameter interval.  With a perturbation bound
on a thinner tube this gives a square root of the discriminant there; the two square roots of a
broken segment glue, and the resulting root branch is a simple holomorphic sheet on the thin tube
around the broken segment, in the form the continuation input asks for.  Two simple root branches
that agree at one point of a preconnected set agree on all of it.
-/

namespace Submission.Lib.K4QuadraticSheets

open MvPolynomial Polynomial

variable {n : ℕ}

local notation "E" => EuclideanSpace ℂ (Fin n)

theorem coord_line_complex (a b : E) (x : ℂ) (j : Fin n) :
    (a + x • (b - a)) j = a j + x * (b j - a j) := by
  simp

theorem real_smul_eq_complex_smul (s : ℝ) (v : E) : s • v = (s : ℂ) • v :=
  (Complex.coe_smul s v).symm

/-- A lower bound for the discriminant on a tube keeps the roots along the segment far from the
parameter interval. -/
theorem discLine_roots_far {P : MvPolynomial (Fin (n + 1)) ℂ} (a b : E) {r m : ℝ}
    (hr : 0 < r) (hm : 0 < m)
    (hdisc : ∀ z ∈ Metric.thickening r (segment ℝ a b), m ≤ ‖qdisc P (fun j => z j)‖) :
    discLine P (fun j => a j) (fun j => b j - a j) ≠ 0 ∧
      ∀ x ∈ (discLine P (fun j => a j) (fun j => b j - a j)).roots,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, r / ‖b - a‖ ≤ ‖(s : ℂ) - x‖ := by
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, a + s • (b - a) ∈ segment ℝ a b := by
    intro s hs
    rw [segment_eq_image']
    exact ⟨s, hs, rfl⟩
  constructor
  · intro h0
    have hz : a ∈ Metric.thickening r (segment ℝ a b) :=
      Metric.self_subset_thickening hr _ (left_mem_segment ℝ a b)
    have h1 := hdisc a hz
    have h2 : (discLine P (fun j => a j) (fun j => b j - a j)).eval 0 =
        qdisc P (fun j => a j) := by
      rw [eval_discLine]
      simp
    rw [h0, Polynomial.eval_zero] at h2
    rw [← h2, norm_zero] at h1
    linarith
  · intro x hx s hs
    by_contra hlt
    rw [not_le] at hlt
    have hroot : (discLine P (fun j => a j) (fun j => b j - a j)).eval x = 0 :=
      (Polynomial.mem_roots'.mp hx).2
    rw [eval_discLine] at hroot
    set z : E := a + x • (b - a) with hzdef
    have hz : z ∈ Metric.thickening r (segment ℝ a b) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨a + s • (b - a), hseg s hs, ?_⟩
      rw [dist_eq_norm, hzdef, real_smul_eq_complex_smul]
      have : a + x • (b - a) - (a + (s : ℂ) • (b - a)) = (x - s) • (b - a) := by
        rw [sub_smul]; abel
      rw [this, norm_smul]
      by_cases hba : ‖b - a‖ = 0
      · rw [hba, mul_zero]; exact hr
      · have hpos : 0 < ‖b - a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hba)
        rw [lt_div_iff₀ hpos] at hlt
        rw [norm_sub_rev]
        exact hlt
    have h1 := hdisc z hz
    have hzc : (fun j => z j) = (fun j => a j + x * (b j - a j)) := by
      funext j; rw [hzdef, coord_line_complex]
    rw [hzc, hroot, norm_zero] at h1
    linarith

/-- A square root of the discriminant on a ball where it moves less than its size. -/
theorem exists_sqrt_on_ball {P : MvPolynomial (Fin (n + 1)) ℂ} (a : E) {r : ℝ}
    (hpert : ∀ z ∈ Metric.ball a r,
      ‖qdisc P (fun j => z j) - qdisc P (fun j => a j)‖ < ‖qdisc P (fun j => a j)‖) :
    ∃ S : E → ℂ, AnalyticOnNhd ℂ S (Metric.ball a r) ∧
      ∀ z ∈ Metric.ball a r, S z ^ 2 = qdisc P (fun j => z j) ∧
        qdisc P (fun j => z j) ≠ 0 := by
  by_cases hr : r ≤ 0
  · refine ⟨fun _ => 0, fun _ _ => analyticAt_const, ?_⟩
    intro z hz
    rw [Metric.ball_eq_empty.mpr hr] at hz
    exact absurd hz (Set.notMem_empty z)
  rw [not_le] at hr
  have ha0 : qdisc P (fun j => a j) ≠ 0 := by
    intro h0
    have := hpert a (Metric.mem_ball_self hr)
    rw [h0, sub_zero, norm_zero] at this
    exact lt_irrefl _ this
  set lam := qdisc P (fun j => a j) with hlam
  set μ : ℂ := lam ^ (1 / 2 : ℂ) with hμ
  have hμ2 : μ ^ 2 = lam := by
    have := Complex.cpow_nat_inv_pow lam (n := 2) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    rw [hμ, one_div]
    exact this
  have hmem : ∀ z ∈ Metric.ball a r, qdisc P (fun j => z j) / lam ∈ Complex.slitPlane := by
    intro z hz
    have heq : qdisc P (fun j => z j) / lam = 1 + (qdisc P (fun j => z j) - lam) / lam := by
      field_simp
      ring
    rw [heq]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_div, div_lt_one (norm_pos_iff.mpr ha0)]
    exact hpert z hz
  refine ⟨fun z => rotSqrt lam μ (qdisc P (fun j => z j)), ?_, ?_⟩
  · exact analyticOnNhd_rotSqrt (fun z _ => analyticAt_qdisc P z) hmem
  · intro z hz
    refine ⟨rotSqrt_sq ha0 hμ2 _, ?_⟩
    intro h0
    have := hmem z hz
    rw [h0, zero_div] at this
    exact Complex.slitPlane_ne_zero this rfl

/-- **Square root on a segment tube from a discriminant lower bound.**  If `m ≤ |disc|` on the
`r`-tube around `[a, b]`, and the discriminant moves by less than `m / (2 (1 + |b - a| / r) ^ 2)`
across the thinner `r'`-tube, then it has a holomorphic square root on the `r'`-tube. -/
theorem exists_sqrt_on_segment_tube' {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P.totalDegree ≤ 2) (a b : E) {r r' m : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hdisc : ∀ z ∈ Metric.thickening r (segment ℝ a b), m ≤ ‖qdisc P (fun j => z j)‖)
    (hpert : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : E, dist z (a + s • (b - a)) < r' →
      ‖qdisc P (fun j => z j) - qdisc P (fun j => (a + s • (b - a)) j)‖ *
        (2 * (1 + ‖b - a‖ / r) ^ 2) < m) :
    ∃ S : E → ℂ, AnalyticOnNhd ℂ S (Metric.thickening r' (segment ℝ a b)) ∧
      ∀ z ∈ Metric.thickening r' (segment ℝ a b),
        S z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0 := by
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, a + s • (b - a) ∈ segment ℝ a b := by
    intro s hs
    rw [segment_eq_image']
    exact ⟨s, hs, rfl⟩
  have hlow : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      m ≤ ‖qdisc P (fun j => (a + s • (b - a)) j)‖ := fun s hs =>
    hdisc _ (Metric.self_subset_thickening hr _ (hseg s hs))
  by_cases hab : b = a
  · -- a degenerate segment: its tube is a ball
    subst hab
    have hsegpt : segment ℝ b b = {b} := segment_same ℝ b
    rw [hsegpt, Metric.thickening_singleton]
    apply exists_sqrt_on_ball
    intro z hz
    have h1 := hpert 0 ⟨le_refl _, zero_le_one⟩ z (by simpa using hz)
    have h2 := hlow 0 ⟨le_refl _, zero_le_one⟩
    simp only [sub_self, smul_zero, add_zero, norm_zero, zero_div] at h1 h2
    have hpos : 0 < 2 * (1 + 0) ^ 2 := by norm_num
    nlinarith [norm_nonneg (qdisc P (fun j => z j) - qdisc P (fun j => b j))]
  · have hba : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
    obtain ⟨hq, hfar⟩ := discLine_roots_far (P := P) a b hr hm hdisc
    have hρ : 0 < r / ‖b - a‖ := div_pos hr hba
    have hinv : 1 / (r / ‖b - a‖) = ‖b - a‖ / r := by field_simp
    apply exists_sqrt_on_segment_tube a b hρ hq hfar (natDegree_discLine_le hP _ _)
    intro s hs z hz
    rw [hinv]
    have h1 := hpert s hs z hz
    have h2 := hlow s hs
    linarith

/-- **A simple sheet on the tube around a broken segment.**  Square roots on the two segment
tubes glue over their convex overlap; the selected root is a holomorphic simple root of the test
on the whole tube. -/
theorem exists_sqrt_on_broken_tube {P : MvPolynomial (Fin (n + 1)) ℂ}
    (a b c : E) {r' : ℝ} (hr' : 0 < r')
    (S₁ S₂ : E → ℂ)
    (h₁ : AnalyticOnNhd ℂ S₁ (Metric.thickening r' (segment ℝ a b)) ∧
      ∀ z ∈ Metric.thickening r' (segment ℝ a b),
        S₁ z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0)
    (h₂ : AnalyticOnNhd ℂ S₂ (Metric.thickening r' (segment ℝ b c)) ∧
      ∀ z ∈ Metric.thickening r' (segment ℝ b c),
        S₂ z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0) :
    ∃ S : E → ℂ,
      AnalyticOnNhd ℂ S (Metric.thickening r' (segment ℝ a b ∪ segment ℝ b c)) ∧
      ∀ z ∈ Metric.thickening r' (segment ℝ a b ∪ segment ℝ b c),
        S z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0 := by
  rw [Metric.thickening_union]
  have hb : b ∈ Metric.thickening r' (segment ℝ a b) ∩ Metric.thickening r' (segment ℝ b c) :=
    ⟨Metric.self_subset_thickening hr' _ (right_mem_segment ℝ a b),
      Metric.self_subset_thickening hr' _ (left_mem_segment ℝ b c)⟩
  have hpre : IsPreconnected
      (Metric.thickening r' (segment ℝ a b) ∩ Metric.thickening r' (segment ℝ b c)) :=
    (((convex_segment a b).thickening r').inter ((convex_segment b c).thickening r')).isPreconnected
  have hd : ∀ z ∈ Metric.thickening r' (segment ℝ a b) ∪ Metric.thickening r' (segment ℝ b c),
      qdisc P (fun j => z j) ≠ 0 := by
    intro z hz
    rcases hz with hz | hz
    · exact (h₁.2 z hz).2
    · exact (h₂.2 z hz).2
  obtain ⟨S, hSd, hS⟩ := glue_sqrt Metric.isOpen_thickening Metric.isOpen_thickening hpre hb
    h₁.1 h₂.1 (fun z hz => (h₁.2 z hz).1) (fun z hz => (h₂.2 z hz).1) hd
  exact ⟨S, hSd, fun z hz => ⟨hS z hz, hd z hz⟩⟩

/-- Two simple holomorphic root branches of a quadratic test that agree at one point of a
preconnected set where the discriminant does not vanish agree on the whole set. -/
theorem root_branch_eq_of_eq_at {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P.totalDegree ≤ 2)
    {f g : E → ℂ} {s : Set E} (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (hg : ContinuousOn g s)
    (hfr : ∀ z ∈ s, eval (Fin.snoc (fun j : Fin n => z j) (f z) : Fin (n + 1) → ℂ) P = 0)
    (hgr : ∀ z ∈ s, eval (Fin.snoc (fun j : Fin n => z j) (g z) : Fin (n + 1) → ℂ) P = 0)
    (hd : ∀ z ∈ s, qdisc P (fun j => z j) ≠ 0) {b : E} (hb : b ∈ s) (hfg : f b = g b) :
    ∀ z ∈ s, f z = g z := by
  -- compare the hidden derivatives, which are square roots of the discriminant
  set Sf : E → ℂ := fun z => qb P (fun j => z j) + qc P * f z
  set Sg : E → ℂ := fun z => qb P (fun j => z j) + qc P * g z
  have hSf : ∀ z ∈ s, Sf z ^ 2 = qdisc P (fun j => z j) := by
    intro z hz
    have := pderiv_sq_eq_qdisc_of_root P hP (fun j => z j) (f z) (hfr z hz)
    rw [eval_snoc_pderiv P hP] at this
    exact this
  have hSg : ∀ z ∈ s, Sg z ^ 2 = qdisc P (fun j => z j) := by
    intro z hz
    have := pderiv_sq_eq_qdisc_of_root P hP (fun j => z j) (g z) (hgr z hz)
    rw [eval_snoc_pderiv P hP] at this
    exact this
  have hcf : ContinuousOn Sf s :=
    (differentiable_qb P).continuous.continuousOn.add (continuousOn_const.mul hf)
  have hcg : ContinuousOn Sg s :=
    (differentiable_qb P).continuous.continuousOn.add (continuousOn_const.mul hg)
  have hSeq := sqrt_sign_constant hs hcf hcg hSf hSg hd hb (by simp only [Sf, Sg, hfg])
  intro z hz
  by_cases hc : qc P = 0
  · -- the linear case: the root is unique
    have hb0 : qb P (fun j => z j) ≠ 0 := by
      intro h0
      apply hd z hz
      rw [qdisc, h0, hc]
      ring
    have h1 := hfr z hz
    have h2 := hgr z hz
    rw [eval_snoc_quadratic P hP, hc] at h1 h2
    have : qb P (fun j => z j) * (f z - g z) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb0
    · exact sub_eq_zero.mp h
  · have := hSeq z hz
    simp only [Sf, Sg] at this
    have h3 : qc P * (f z - g z) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hc
    · exact sub_eq_zero.mp h

end Submission.Lib.K4QuadraticSheets
