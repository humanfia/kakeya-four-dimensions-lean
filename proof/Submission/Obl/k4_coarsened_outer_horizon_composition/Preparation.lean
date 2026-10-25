import Submission.Obl.k4_coarsened_outer_horizon_composition.PrunedSystem
import Submission.Obl.k4_coarsened_outer_horizon_composition.SamplePruning
import Submission.Obl.k4_coarsened_outer_horizon_composition.PruningNumerics
import Submission.Obl.k4_coarsened_outer_horizon_composition.Finish
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set Filter
open scoped ENNReal

/-- True terminal floors and homogeneous typicality supply short lists at the
same terminal observation, with a fixed polynomial format for every tolerance. -/
theorem own_depth_preparation : OwnDepthPreparation := by
  intro N K L d S η W ω ν E P B f g G hp h ht
  rcases ht with ⟨M, D, ht⟩
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hbase,
    hpure, hangular, hreg, htyp, hcap, hang⟩
  rcases hbase with ⟨Mb, Db, hbase⟩
  refine ⟨prunedExponent M Mb L, max D 4, ?_⟩
  intro ε hε
  obtain ⟨c₀, hc₀, htypical⟩ := htyp L (ε / 100) hL.le le_rfl (by positivity)
  obtain ⟨σ, hσ, hσε, hσc, hparameters⟩ := pruning_parameters hNt hε hc₀
  apply ((ht σ hσ).and_eventually (htypical.and hparameters)).mono
  intro k hk
  obtain ⟨κ, hκ, hKκ, hκmax, T, C, γ, j, a, u, Q, R, A, F,
    hT, hC, hdisj, hcharts, hmass⟩ := hk.1
  obtain ⟨hdouble, hθmax, hloss⟩ := hk.2.2 κ hκ hκmax
  obtain ⟨hW, hω0, hω1, hworld, hprobmass⟩ := hbase k
  have hν (w) : IsProbabilityMeasure (ν k w) := (hworld w).1
  have hB (w) : 0 < B k w := (hworld w).2.1
  have hBmax (w) : B k w ≤ N k ^ Mb := (hworld w).2.2.1
  have hE (w) : E k w ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    rcases hworld w with ⟨_, _, _, _, _, _, _, _, hE, _⟩
    exact hE
  have hN0 : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hκ0 : 0 < κ := by linarith
  let θ := N k ^ (ε / 2)
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos hN0 _
  have hκθ : κ ≤ θ := by dsimp [θ]; linarith
  have hθ1 : 1 ≤ θ := hκ.trans hκθ
  obtain ⟨F', lst, hsub, hlist, hnew, hcover⟩ := pruned_chart_system (hN k) hκ hκθ
    (B k) hB hBmax (E k) hE γ j a u Q R A F
    (fun b => ENNReal.ofReal (N k ^ (-f L) * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
      ((ν k (γ b)).prod volume) (F b)) hC hcharts
  let Cr := fun b => crossing κ (((j b : ℕ) : ℝ) / (2 : ℝ) ^ T)
    ((((j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) (δ (N k) L / B k (γ b)) (B k (γ b))
    (a b) (u b) (Q b) (R b)
  let deleted := fun b => F b ∩ {p | ENNReal.ofReal θ <
    crossCount (Finset.univ.filter (fun b' => γ b' = γ b)) Cr
      (obs (B k (γ b)) (δ (N k) L) p)}
  have hupper : ∑ w, ENNReal.ofReal (ω k w) * selected (ν k w) (E k w)
      {p | ENNReal.ofReal (N k ^ (-f L + ε / 100)) <
        g k w L (obs (B k w) (δ (N k) L) p)} ≤ ENNReal.ofReal (N k ^ (-c₀)) := by
    apply le_trans _ hk.2.1
    apply Finset.sum_le_sum
    intro w _
    exact mul_le_mul le_rfl (measure_mono (fun p hp => Or.inr hp)) zero_le zero_le
  have hdeleted : ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod volume) (deleted b) ≤
      ENNReal.ofReal (2 * N k ^ (-c₀) + 1024 * κ ^ 5 * N k ^ (ε / 100) / θ) :=
    sample_pruning_loss (hN k) hκ hθ0 (ω k) hω0 hω1 (ν k) hν (E k) hE (B k) hB
      (fun w => g k w L) (fun w => (hpure k w L hL.le le_rfl).1)
      (fun w => (hpure k w L hL.le le_rfl).2)
      γ j a u Q R A F hdisj hcharts hupper
  have hinv : (2 * κ)⁻¹ = κ⁻¹ / 2 := by ring
  have hdeletedhalf : ∑ b, ENNReal.ofReal (ω k (γ b)) *
      ((ν k (γ b)).prod volume) (deleted b) ≤ ENNReal.ofReal (κ⁻¹ / 2) := by
    apply hdeleted.trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [θ, hinv] using hloss
  have hcovermass :=
    Submission.Obl.k4_quadratic_atlas_normalization.weighted_mass_le_retained_add_deleted
      (fun b => (ν k (γ b)).prod volume) (fun b => ENNReal.ofReal (ω k (γ b)))
      F F' deleted hcover
  have hretained := Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    _ _ _ κ⁻¹ (by positivity) hmass hcovermass hdeletedhalf
  have hθinv : θ⁻¹ ≤ κ⁻¹ / 2 := by
    rw [← hinv]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 2 * κ) hdouble
  refine ⟨θ, hθ1, hθmax, T, C, γ, j, a, u, Q, R, A, F', lst, ?_, ?_,
    hdisj, hlist, hnew, (ENNReal.ofReal_le_ofReal hθinv).trans hretained⟩
  · exact hT.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  · exact hC.trans (pow_le_pow_right₀ hN1 (by unfold prunedExponent; omega))

end Submission.Obl.k4_coarsened_outer_horizon_composition
