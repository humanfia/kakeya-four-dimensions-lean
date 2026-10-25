import Submission.Obl.k4_scalar_capped_heavy_potential.PlanarEnergy

namespace Submission.Obl.k4_scalar_capped_heavy_potential

noncomputable section

/-- Whole groups with a poor current-to-prior ratio cost only their
share of the original prior budget. Zero-mass groups cost nothing. -/
theorem efficient_group_mass_budget {ι : Type*} (F : Finset ι) (m p : ι → ℝ)
    {α P : ℝ} (hα : 0 ≤ α) (hm : ∀ c ∈ F, 0 ≤ m c) (hp : ∀ c ∈ F, 0 ≤ p c)
    (hprior : ∑ c ∈ F, p c ≤ P) :
    (∑ c ∈ F, m c) ≤
      (∑ c ∈ F.filter (fun c => 0 < m c ∧ α * p c ≤ m c), m c) + α * P := by
  classical
  let G := F.filter (fun c => 0 < m c ∧ α * p c ≤ m c)
  have hsub : G ⊆ F := Finset.filter_subset _ _
  have hbad : ∀ c ∈ F \ G, m c ≤ α * p c := by
    intro c hc
    obtain ⟨hcF, hcG⟩ := Finset.mem_sdiff.mp hc
    by_cases hmc : 0 < m c
    · have hfail : ¬α * p c ≤ m c := by
        intro h
        exact hcG (Finset.mem_filter.mpr ⟨hcF, hmc, h⟩)
      exact (lt_of_not_ge hfail).le
    · exact (le_of_not_gt hmc).trans (mul_nonneg hα (hp c hcF))
  calc
    (∑ c ∈ F, m c) = (∑ c ∈ G, m c) + ∑ c ∈ F \ G, m c := by
      simpa only [add_comm] using (Finset.sum_sdiff (f := m) hsub).symm
    _ ≤ (∑ c ∈ G, m c) + ∑ c ∈ F \ G, α * p c :=
      add_le_add le_rfl (Finset.sum_le_sum hbad)
    _ ≤ (∑ c ∈ G, m c) + α * P := by
      apply add_le_add le_rfl
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hα
      exact (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (by intro c hc _; exact hp c hc)).trans hprior

/-- Selecting efficient groups before using their Kakeya area floors
produces the required heavy group at the original support-count scale. -/
theorem efficient_heavy_group_of_cell_budget {ι β : Type*}
    (F : Finset ι) (m p : ι → ℝ) (cells : ι → Finset β)
    {α P M L T : ℝ} (hα : 0 ≤ α) (hM : α * P < M) (hL : 0 < L)
    (hm : ∀ c ∈ F, 0 ≤ m c) (hp : ∀ c ∈ F, 0 ≤ p c)
    (hprior : ∑ c ∈ F, p c ≤ P) (hmass : M ≤ ∑ c ∈ F, m c)
    (hfloor : ∀ c ∈ F, 0 < m c → α * p c ≤ m c → L ≤ (cells c).card)
    (hbudget : (∑ c ∈ F, ((cells c).card : ℝ)) ≤ T) :
    ∃ c ∈ F, 0 < m c ∧ α * p c ≤ m c ∧ (M - α * P) * L ≤ T * m c := by
  classical
  let G := F.filter (fun c => 0 < m c ∧ α * p c ≤ m c)
  have hsub : G ⊆ F := Finset.filter_subset _ _
  have hsum : M - α * P ≤ ∑ c ∈ G, m c := by
    have h := efficient_group_mass_budget F m p hα hm hp hprior
    linarith
  have hbudget' : (∑ c ∈ G, ((cells c).card : ℝ)) ≤ T := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans hbudget
  obtain ⟨c, hc, hheavy⟩ := heavy_group_of_cell_budget G cells m (by linarith) hL
    (fun c hc => hm c (hsub hc)) hsum
    (fun c hc => hfloor c (hsub hc) (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc).2.2)
    hbudget'
  exact ⟨c, hsub hc, (Finset.mem_filter.mp hc).2.1, (Finset.mem_filter.mp hc).2.2, hheavy⟩


/-- Quantitative selection of the scalar heavy intercept group. The
original prior budget occurs only once, so the width gain is exactly
`R⁻¹`, where `R = (a / w)^d`. -/
theorem heavy_intercept_group_selection {ι βtype : Type*}
    (F : Finset ι) (m p : ι → ℝ) (cells : ι → Finset βtype)
    {H C ξ h prior R β : ℝ}
    (hH : 1 ≤ H) (hC : 0 < C) (hξ : 0 < ξ) (hh : 0 < h)
    (hprior : 0 < prior) (hR : 0 < R) (hβ : 0 < β)
    (hm : ∀ c ∈ F, 0 ≤ m c) (hp : ∀ c ∈ F, 0 ≤ p c)
    (hpriorsum : ∑ c ∈ F, p c ≤ prior)
    (hmass : h * prior / (2 * H) ≤ ∑ c ∈ F, m c)
    (hfloor : ∀ c ∈ F, 0 < m c → h / (4 * H) * p c ≤ m c →
      β / (28800 * C * H ^ 4 * ξ ^ 2) ≤ (cells c).card)
    (hbudget : (∑ c ∈ F, ((cells c).card : ℝ)) ≤ 117 * H / ξ ^ 2 * R) :
    ∃ c ∈ F, 0 < m c ∧ h / (4 * H) * p c ≤ m c ∧
      h * prior * β / (13478400 * C * H ^ 6 * R) ≤ m c := by
  have hH₀ : 0 < H := by linarith
  have hmasspos : h / (4 * H) * prior < h * prior / (2 * H) := by
    have hpos : 0 < h * prior / (4 * H) := by positivity
    nlinarith [show h / (4 * H) * prior = h * prior / (4 * H) by ring,
      show h * prior / (2 * H) = 2 * (h * prior / (4 * H)) by field_simp [hH₀.ne']; ring]
  obtain ⟨c, hc, hmc, heff, hheavy⟩ := efficient_heavy_group_of_cell_budget F m p cells
    (by positivity : 0 ≤ h / (4 * H)) hmasspos
    (by positivity : 0 < β / (28800 * C * H ^ 4 * ξ ^ 2)) hm hp hpriorsum hmass hfloor hbudget
  refine ⟨c, hc, hmc, heff, ?_⟩
  have hT : 0 < 117 * H / ξ ^ 2 * R := by positivity
  have hquot :
      ((h * prior / (2 * H) - h / (4 * H) * prior) *
        (β / (28800 * C * H ^ 4 * ξ ^ 2))) /
        (117 * H / ξ ^ 2 * R) ≤ m c :=
    (div_le_iff₀ hT).2 (by simpa only [mul_comm] using hheavy)
  convert hquot using 1 <;>
    field_simp [hH₀.ne', hC.ne', hξ.ne', hR.ne'] <;> ring

end
end Submission.Obl.k4_scalar_capped_heavy_potential
