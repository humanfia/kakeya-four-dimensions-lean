import Submission.Obl.k4_true_forest_own_depth_preparation.Sample
import Submission.Obl.k4_true_forest_own_depth_preparation.Layers
import Submission.Obl.k4_true_forest_own_depth_preparation.Numerics

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set Filter Classical
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- Preparation at the fixed finite list of actual depths of an exact problem. -/
theorem preparation : Preparation := by
  intro N K L d S η W ω ν E P B f g G hp m r hm hr M D
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hbase,
    hpure, hangular, hreg, htyp, hcap, hang⟩
  rcases hbase with ⟨Mb, Db, hbase⟩
  let M₁ := prunedExponent M Mb L
  refine ⟨M + M₁ + 2, max D 4, by omega, le_max_left _ _, ?_⟩
  intro σ hσ
  let X : ℕ → ℕ → ENNReal := fun k i =>
    ∑ w, ENNReal.ofReal (ω k w) * selected (ν k w) (E k w)
      {p | ENNReal.ofReal (N k ^ (-f (r i) + σ / 100)) <
        g k w (r i) (obs (B k w) (δ (N k) (r i)) p)}
  have htail (i) (hi : i < m) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      X k i ≤ ENNReal.ofReal (N k ^ (-c)) := by
    obtain ⟨c, hc, ht⟩ := htyp (r i) (σ / 100) (hr i hi).1.le (hr i hi).2 (by positivity)
    refine ⟨c, hc, ht.mono ?_⟩
    intro k hk
    apply le_trans _ hk
    apply Finset.sum_le_sum
    intro w _
    exact mul_le_mul le_rfl (measure_mono (fun p hp => Or.inr hp)) zero_le zero_le
  obtain ⟨c₀, hc₀, htypical⟩ := uniform_tail_constant (fun k => by linarith [hN k]) X htail
  obtain ⟨ρ, hρ, hρσ, hparameters⟩ := forest_numerics hNt m hσ hc₀
  refine ⟨ρ, hρ, by linarith, ?_⟩
  filter_upwards [htypical, hparameters] with k htypk hparam
  intro T C lev par γ j c u Q R A F htime hcore
  have hcore₀ := hcore
  rcases hcore with ⟨hκ, hKκ, hC, hfloors, hdisj, hnodes⟩
  obtain ⟨hW, hω0, hω1, hworld, hproblemMass⟩ := hbase k
  have hν (w) : IsProbabilityMeasure (ν k w) := (hworld w).1
  have hB (w) : 0 < B k w := (hworld w).2.1
  have hBmax (w) : B k w ≤ N k ^ Mb := (hworld w).2.2.1
  have hE (w) : E k w ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    rcases hworld w with ⟨_, _, _, _, _, _, _, _, hE, _⟩
    exact hE
  have hN0 : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hκ0 : 0 < N k ^ ρ := Real.rpow_pos_of_pos hN0 _
  let θ := N k ^ (σ / 4)
  have hκθ : N k ^ ρ ≤ θ := Real.rpow_le_rpow_of_exponent_le hN1 hρσ
  have hθκ : θ ≤ N k ^ σ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hlev (b) : lev b < m := (hnodes b).1
  have hcharts (b) := (hnodes b).2.2.1
  have hmeas (i) (hi : i < m) (w) : Measurable (g k w (r i)) :=
    (hpure k w (r i) (hr i hi).1.le (hr i hi).2).1
  have hlaw (i) (hi : i < m) (w) :
      (selected (ν k w) (E k w)).map (obs (B k w) (δ (N k) (r i))) =
        (volume.prod Measure.count).withDensity (g k w (r i)) :=
    (hpure k w (r i) (hr i hi).1.le (hr i hi).2).2
  obtain ⟨H, lst, hsub, hlist, hH, hdelete⟩ := prune_layers (hN k) hκ hκθ
    (ω k) hω0 hω1 (ν k) hν (E k) hE (B k) hB hBmax
    r (fun i hi => (hr i hi).2) f (fun w s => g k w s) hmeas hlaw htypk
    T lev γ j c u Q R A F hC hlev (fun b => (hnodes b).2.1) hdisj hcharts
  let Ecut : ℝ := 2 * N k ^ (-c₀) + 1024 * (N k ^ ρ) ^ 5 * N k ^ (σ / 100) / θ
  let Eheavy : ℝ := 2 * N k ^ (-c₀) + 256 * (N k ^ ρ) ^ 4 * N k ^ (σ / 100 - σ)
  let heavyMass : Fin C → ENNReal := fun b =>
    if ¬ν k (γ b) (A b) ≤ ENNReal.ofReal (N k ^ σ * N k ^ (-f (r (lev b))) * |(Q b).det|) then
      ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod volume) (F b) else 0
  have htrue (b) : chart (N k) M D (N k ^ ρ) (T (lev b)) (j b : ℝ) (r (lev b))
      (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) True :=
    Submission.Obl.k4_quadratic_atlas_normalization.chart_mono hN1 le_rfl le_rfl
      hκ0 le_rfl (hB _).le (hcharts b) (fun _ => trivial)
  have hheavyLayer (i) (hi : i < m) :
      (∑ b, if lev b = i then heavyMass b else 0) ≤ ENNReal.ofReal Eheavy := by
    let I := Finset.univ.filter (fun b => lev b = i)
    have heq (b) (hb : b ∈ I) : lev b = i := (Finset.mem_filter.mp hb).2
    have hh := heavy_mass_le (σ := σ) I hN0 hκ (ω k) hω0 hω1 (ν k) hν (E k) (B k) hB
      (fun w => g k w (r i)) (hmeas i hi) (hlaw i hi) γ j
      (fun b hb => by simpa only [heq b hb] using (hnodes b).2.1)
      c u Q R A F (fun _ => True)
      (fun b hb b' hb' hne hγ hj => hdisj b b' hne ((heq b hb).trans (heq b' hb').symm) hγ hj)
      (fun b hb => by simpa only [heq b hb] using htrue b) (htypk i hi)
    have hconst : 2 * ENNReal.ofReal (N k ^ (-c₀)) +
        ENNReal.ofReal (256 * (N k ^ ρ) ^ 4 * N k ^ (σ / 100 - σ)) =
        ENNReal.ofReal Eheavy := by
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply le_trans _ (hh.trans_eq hconst)
    apply le_of_eq
    simp only [I, Finset.filter_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : lev b = i <;> simp [heavyMass, hb, not_le]
  have hheavy := sum_le_depth_mul lev hlev heavyMass (ENNReal.ofReal Eheavy) hheavyLayer
  have hLoss : (2 + 4 * (m : ENNReal)) * ((m : ENNReal) * ENNReal.ofReal Ecut) +
      (m : ENNReal) * ENNReal.ofReal Eheavy ≤ ENNReal.ofReal ((N k ^ ρ)⁻¹ / 2) := by
    have hmCut : (m : ENNReal) * ENNReal.ofReal Ecut = ENNReal.ofReal ((m : ℝ) * Ecut) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have hmHeavy : (m : ENNReal) * ENNReal.ofReal Eheavy = ENNReal.ofReal ((m : ℝ) * Eheavy) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have hcoeff : (2 + 4 * (m : ENNReal)) = ENNReal.ofReal (2 + 4 * (m : ℝ)) := by
      rw [ENNReal.ofReal_add (by norm_num) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
      norm_num
    rw [hmCut, hmHeavy, hcoeff,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 + 4 * m),
      ← ENNReal.ofReal_add (by dsimp [Ecut, θ]; positivity) (by dsimp [Eheavy]; positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn := hparam.2
    change ((2 + 4 * (m : ℝ)) * m) * Ecut + (m : ℝ) * Eheavy ≤ (N k ^ ρ)⁻¹ / 2 at hn
    nlinarith
  exact prepare_sample (hN k) hν hE hB
    (show M ≤ M₁ by dsimp only [M₁, prunedExponent]; omega) (le_max_left _ _) hκθ hθκ hparam.1
    hcore₀ H lst hlist hH ((m : ENNReal) * ENNReal.ofReal Ecut)
    ((m : ENNReal) * ENNReal.ofReal Eheavy) hdelete hheavy hLoss

end Submission.Obl.k4_true_forest_own_depth_preparation
