import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameMeasure

/-!
# Masses and priors of the residual labels

For a residual label at grid level `h` with node `(oi, u)`:

* its node lies in the parent block and the parent history;
* its history keeps the prior `θ * ν(A_oi) / K` (an incidence floor forces a
  prior floor), and so does the parent history;
* its residual incidence mass is at least `θ` times its residual block length
  times its residual prior.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

open Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

theorem FrameGood.inside (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) :
    f.block h (f.node h i).1 ⊆ f.block 0 f.i₀ ∧
      f.hist h (f.node h i).1 (f.node h i).2 ⊆ f.parentSet :=
  hg.core_inside h hh _ _ (f.node_retained h i)

theorem FrameGood.parent_retained (hg : FrameGood f Rk θ K₂ e₀') :
    (f.event 0 f.i₀ f.u₀ ∩ f.core).Nonempty := by
  obtain ⟨p, hp⟩ := hg.core_nonempty
  exact ⟨p, hg.core_parent_event hp, hp⟩

/-- An incidence floor of a node gives the prior floor of its history. -/
theorem FrameGood.prior_floor (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.nl h)) (u : EntryHistory f.M h)
    (hne : (f.event h i u ∩ f.core).Nonempty) :
    ENNReal.ofReal θ * D.ν k (D.A k (f.depth h) i) ≤
      ENNReal.ofReal (D.K k) * D.ν k (f.hist h i u) := by
  apply incidence_floor_implies_prior_floor (D.ν k) (D.μ k) _ _ (f.event h i u ∩ f.core)
    (f.ql_pos h) hg.θ_pos.le hg.dom
  · intro p hp
    have hp1 := hp.1
    simp only [event, mem_prod] at hp1
    rw [block_eq_Icc] at hp1
    exact ⟨hp1.1, hp1.2⟩
  · exact hg.core_floor h hh i u hne

theorem FrameGood.parent_prior (hg : FrameGood f Rk θ K₂ e₀') :
    ENNReal.ofReal θ * D.ν k (D.A k (f.depth 0) f.i₀) ≤
      ENNReal.ofReal (D.K k) * D.ν k f.parentSet :=
  hg.prior_floor (Nat.zero_le _) f.i₀ f.u₀ hg.parent_retained

theorem FrameGood.ν_A_pos (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.nl h)) : 0 < D.ν k (D.A k (f.depth h) i) := by
  refine lt_of_lt_of_le ?_ (hg.floor h hh i)
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hK : 0 < D.K k := by linarith [hg.K_ge]
  have := f.ql_pos h
  apply ENNReal.ofReal_pos.mpr
  positivity

theorem FrameGood.parent_pos (hg : FrameGood f Rk θ K₂ e₀') : 0 < D.ν k f.parentSet := by
  have h1 := hg.parent_prior
  have h2 : 0 < ENNReal.ofReal θ * D.ν k (D.A k (f.depth 0) f.i₀) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hg.θ_pos).ne' (hg.ν_A_pos (Nat.zero_le _) _).ne'
  have h3 := h2.trans_le h1
  rcases (ENNReal.mul_pos_iff.mp h3) with ⟨_, h4⟩
  exact h4

theorem FrameGood.parent_ne_top (hg : FrameGood f Rk θ K₂ e₀') : D.ν k f.parentSet ≠ ⊤ := by
  haveI := hg.νprob
  exact measure_ne_top _ _

theorem FrameGood.scale_pos (hg : FrameGood f Rk θ K₂ e₀') : 0 < f.scale :=
  ENNReal.mul_pos (ENNReal.ofReal_pos.mpr f.q₀_pos).ne' hg.parent_pos.ne'

theorem FrameGood.scale_ne_top (hg : FrameGood f Rk θ K₂ e₀') : f.scale ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.parent_ne_top

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
