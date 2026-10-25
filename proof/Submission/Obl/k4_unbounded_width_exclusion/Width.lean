import Submission.Obl.k4_unbounded_width_exclusion.Problems

namespace Submission.Obl.k4_unbounded_width_exclusion

open Filter

theorem Problem.Narrow.mono {p : Problem} (hN : ∀ k, 1 ≤ p.N k)
    {h h' w w' : ℝ} (hnt : p.Narrow h w) (hh : h ≤ h') (hw : w' ≤ w) :
    p.Narrow h' w' := by
  obtain ⟨M, D, hMD⟩ := hnt
  refine ⟨M, D, fun ε hε => ?_⟩
  apply (hMD ε hε).mono
  intro k hk
  obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    htime, hwidth, hcount, hdisj, hcharts, hmass⟩ := hk
  refine ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    htime.trans ?_, ?_, hcount, hdisj, hcharts, hmass⟩
  · exact Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
  · intro b
    exact (hwidth b).trans
      (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith))

theorem Problem.Valid.scale_ge_one {p : Problem} {S η : ℝ}
    (h : p.Valid S η) (k : ℕ) : 1 ≤ p.N k :=
  le_trans (by norm_num) (h.1 k)

/-- Failure of bounded width allows simultaneous prescribed accuracy,
horizon margin, and narrowness, without interchanging their quantifiers. -/
theorem exists_narrow_near {ds kr S η : ℝ} (hes : es ds kr S η)
    (hnb : ¬ BoundedWidth ds kr S η)
    {a w t : ℝ} (ha : 0 < a) (hw : 0 ≤ w) (ht : 0 < t) :
    ∃ p : Problem, Near ds kr S η t p ∧ p.Narrow (kr + a) w := by
  obtain ⟨t', ht', hnarrow⟩ := (not_boundedWidth_iff ds kr S η).mp hnb a ha w hw
  obtain ⟨p, hp⟩ := exists_near hes (lt_min ht ht')
  exact ⟨p, hp.mono (min_le_left _ _), hnarrow p (hp.mono (min_le_right _ _))⟩

/-- Each outer index may demand its own fixed narrowness and horizon
margin. The inner exact problem still has all fixed-format quantifiers. -/
theorem exists_narrow_sequence {ds kr S η : ℝ} (hes : es ds kr S η)
    (hnb : ¬ BoundedWidth ds kr S η) (a w t : ℕ → ℝ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) :
    ∃ p : ℕ → Problem, ∀ i,
      Near ds kr S η (t i) (p i) ∧ (p i).Narrow (kr + a i) (w i) := by
  classical
  exact Classical.axiomOfChoice fun i => exists_narrow_near hes hnb (ha i) (hw i) (ht i)

end Submission.Obl.k4_unbounded_width_exclusion
