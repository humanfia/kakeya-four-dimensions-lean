import Submission.Lib.K4ExactProblemOps.Coarsening
import Submission.Lib.K4ExactProblemOps.Horizon

/-!
# Capped depths and the initial horizon bound at intermediate depths

A nearly linear relative profile of slope `ds` has, just below any target depth `b`,
a depth `r` (a tilted minimizer of `f x - (ds + δ) x` on `[0, b]`) with the endpoint
cap `ds + δ` back to `0`.  Coarsening there gives a valid problem of length `r`, to
which the frozen initial horizon bound applies: true systems at depth `r` exist at
every horizon above `r` (paper Corollary 4.4 / Lemma 10.3: "the universal initial
bound provides these packets", which for the frozen IH needs the cap).
-/

noncomputable section

namespace Submission.Lib.K4ExactProblemOps

open MeasureTheory Filter

/-- A tilted minimizer gives a capped depth just below the target. -/
theorem exists_cap_depth {f : ℝ → ℝ} {L ds ε δ b : ℝ}
    (hf : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r)
    (hlin : ∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - ds * r| ≤ ε)
    (hδ : 0 < δ) (hb0 : 0 < b) (hbL : b ≤ L) (hb : 2 * ε / δ < b) :
    ∃ r : ℝ, b - 2 * ε / δ ≤ r ∧ r ≤ b ∧ 0 < r ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ r → f r - f s ≤ (ds + δ) * (r - s) := by
  have hL0 : 0 ≤ L := hb0.le.trans hbL
  have hε : 0 ≤ ε := by
    have := hlin 0 le_rfl hL0
    simpa using this
  -- continuity of `f` on `[0, b]` from the Lipschitz bound
  have hcont : ContinuousOn (fun x => f x - (ds + δ) * x) (Set.Icc 0 b) := by
    refine ContinuousOn.sub ?_ (continuousOn_const.mul continuousOn_id)
    intro x hx
    rw [Metric.continuousWithinAt_iff]
    intro e he
    refine ⟨e, he, fun y hy hxy => ?_⟩
    rw [Real.dist_eq] at hxy ⊢
    rcases le_total x y with hle | hle
    · obtain ⟨h1, h2⟩ := hf x y hx.1 hle (hy.2.trans hbL)
      rw [abs_lt] at hxy ⊢
      constructor <;> linarith [abs_sub_comm y x, hxy.1, hxy.2]
    · obtain ⟨h1, h2⟩ := hf y x hy.1 hle (hx.2.trans hbL)
      rw [abs_lt] at hxy ⊢
      constructor <;> linarith [hxy.1, hxy.2]
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, Set.left_mem_Icc.2 hb0.le⟩ hcont
  have hcap : ∀ s : ℝ, 0 ≤ s → s ≤ r → f r - f s ≤ (ds + δ) * (r - s) := by
    intro s hs hsr
    have := isMinOn_iff.1 hmin s ⟨hs, hsr.trans hr.2⟩
    rw [mul_sub]
    linarith
  have hnear : b - 2 * ε / δ ≤ r := by
    have h1 := isMinOn_iff.1 hmin b (Set.right_mem_Icc.2 hb0.le)
    have h2 := hlin b hb0.le hbL
    have h3 := hlin r hr.1 (hr.2.trans hbL)
    rw [abs_le] at h2 h3
    have h4 : δ * (b - r) ≤ 2 * ε := by
      have : (ds + δ) * (b - r) ≤ f b - f r := by rw [mul_sub]; linarith
      nlinarith
    have h5 : b - r ≤ 2 * ε / δ := by
      rw [le_div_iff₀ hδ]
      linarith
    linarith
  exact ⟨r, hnear, hr.2, lt_of_lt_of_le (by linarith) hnear, hcap⟩

section

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {f : ℝ → ℝ} {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}

/-- A valid problem with a nearly linear relative profile of slope `ds` coarsens to a
valid problem at a depth just below any target, with cap `ds + δ < 1`. -/
theorem exists_capped_coarsening (hp : prob N K L d S η W ω ν E P B f g G) {ds ε δ b : ℝ}
    (hlin : ∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - ds * r| ≤ ε)
    (hδ : 0 < δ) (hds : 0 < ds + δ) (hds1 : ds + δ < 1) (hb0 : 0 < b) (hbL : b ≤ L)
    (hb : 2 * ε / δ < b) :
    ∃ r : ℝ, b - 2 * ε / δ ≤ r ∧ r ≤ b ∧ 0 < r ∧
      prob N K r (ds + δ) S η W ω ν E P B f g
        (fun k γ u => fiberSumJ (dsteps (N k) r L) (G k γ u)) := by
  obtain ⟨r, hr1, hr2, hr0, hcap⟩ :=
    exists_cap_depth hp.2.2.2.2.2.2.2.2.2.2.2.1 hlin hδ hb0 hbL hb
  exact ⟨r, hr1, hr2, hr0, prob_coarsen hp hr0 (hr2.trans hbL) hds hds1 hcap⟩

/-- True systems at a capped intermediate depth exist at every horizon above it. -/
theorem term_at_capped_depth (hIH : InitialHorizonBound)
    (hp : prob N K L d S η W ω ν E P B f g G) {ds ε δ b : ℝ}
    (hlin : ∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - ds * r| ≤ ε)
    (hδ : 0 < δ) (hds : 0 < ds + δ) (hds1 : ds + δ < 1) (hb0 : 0 < b) (hbL : b ≤ L)
    (hb : 2 * ε / δ < b) :
    ∃ r : ℝ, b - 2 * ε / δ ≤ r ∧ r ≤ b ∧ 0 < r ∧
      ∀ h : ℝ, r < h → term N K r W ω ν E B f h := by
  obtain ⟨r, hr1, hr2, hr0, hpr⟩ := exists_capped_coarsening hp hlin hδ hds hds1 hb0 hbL hb
  exact ⟨r, hr1, hr2, hr0, fun h hh => hIH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpr h hh⟩

end

end Submission.Lib.K4ExactProblemOps
