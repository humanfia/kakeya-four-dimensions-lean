import Submission.Obl.k4_critical_intercept_concentration.HeavyBinRestore
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic

namespace Submission.Obl.k4_critical_intercept_concentration

open Set MeasureTheory Filter Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Original-source midpoint bins at a fixed depth and fixed positive gain.
All losses may be made arbitrarily small, while both depths stay fixed. -/
def HeavyMidpointBins (cfg : Data α) (s v : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ᶠ k in atTop,
    ∃ (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (source : Set (α × ℝ)) (j : ℤ),
      L 0 = 0 ∧ (∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) ∧
      source ⊆ cfg.primitiveEvent k s i L (cfg.N k ^ ζ * cfg.N k ^ (-s)) ∧
      (∀ p ∈ source, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k) ∧
      ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ζ) / (2 : ℝ) ^ cfg.T k s) *
        cfg.ν k (cfg.A k s i) ≤
        cfg.ρ k (source ∩ {p | ⌊cfg.midpointValue k s i L p / cfg.N k ^ (-s - v)⌋ = j})

/-- Subpower primitive slopes in an actual true parent have a single
polynomial bound, independent of all subsequent positive losses. -/
theorem AssignmentLevel.primitive_slopes_polynomial (h : cfg.Valid)
    {k : ℕ} {s ζ : ℝ} (parent : cfg.AssignmentLevel k s) (hs : 0 ≤ s)
    (hs1 : s ≤ 1) (hζ : ζ ≤ 1) (hK : cfg.K k ≤ cfg.N k)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) :
    ∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ (3 : ℕ) := by
  have hN : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hpowζ : cfg.N k ^ ζ ≤ cfg.N k := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN hζ
  have hκs : cfg.κ * s ≤ 1 := by nlinarith [h.rate_le_one, h.rate_pos]
  have hpowκ : cfg.N k ^ (cfg.κ * s) ≤ cfg.N k := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN hκs
  intro e
  calc
    _ ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s := hL e
    _ ≤ cfg.N k ^ ζ * (cfg.K k * cfg.N k ^ (cfg.κ * s)) :=
      mul_le_mul_of_nonneg_left parent.time_upper (Real.rpow_nonneg (by linarith) _)
    _ ≤ cfg.N k * (cfg.N k * cfg.N k) := by
      gcongr
      exact mul_nonneg (by linarith [h.subpower.1 k]) (Real.rpow_nonneg (by linarith) _)
    _ = _ := by ring

/-- A strict positive depth gap absorbs the primitive's integrated slope
error using the original subpower time-comparison loss. -/
theorem AssignmentLevel.integrated_primitive_error (h : cfg.Valid)
    {k : ℕ} {s v ζ : ℝ} (parent : cfg.AssignmentLevel k s)
    (hK : cfg.K k ≤ cfg.N k ^ (cfg.κ * s - v - ζ)) :
    (cfg.N k ^ ζ * cfg.N k ^ (-s)) * cfg.timeLength k s ≤ cfg.N k ^ (-s - v) := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hKpos : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have htime : cfg.timeLength k s ≤ cfg.K k * cfg.N k ^ (-cfg.κ * s) := by
    have hh := (time_length_comparison hN hKpos parent.time_lower parent.time_upper).1
    exact (div_le_iff₀ hKpos).mp hh |>.trans_eq (mul_comm _ _)
  calc
    _ ≤ (cfg.N k ^ ζ * cfg.N k ^ (-s)) * (cfg.K k * cfg.N k ^ (-cfg.κ * s)) := by
      gcongr
    _ ≤ (cfg.N k ^ ζ * cfg.N k ^ (-s)) *
        (cfg.N k ^ (cfg.κ * s - v - ζ) * cfg.N k ^ (-cfg.κ * s)) := by gcongr
    _ = _ := by
      simp only [← Real.rpow_add hN]
      congr 1
      ring

/-- Fixed-depth heavy midpoint bins yield exactly the frozen candidate
quantifiers, including the unchanged original assignment floor and the
homogeneous coefficient bound. -/
theorem candidates_of_heavy_midpoint_bins (h : cfg.Valid) {s v : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hv : 0 < v) (hgain : v < cfg.κ * s)
    (hsU : s + v ≤ cfg.U) (hbins : cfg.HeavyMidpointBins s v) : cfg.Candidates := by
  apply candidates_of_fixed_gain h hs hv hsU (R₀ := 12)
  intro ε hε
  let ζ := min (min ε 1) ((cfg.κ * s - v) / 2)
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζε : ζ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hζ1 : ζ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hζgap : ζ ≤ (cfg.κ * s - v) / 2 := min_le_right _ _
  have hgap : 0 < cfg.κ * s - v - ζ := by linarith
  have hlate : ∀ᶠ k in atTop, cfg.AssignmentLevel k s ∧ cfg.K k ≤ cfg.N k ∧
      cfg.K k ≤ cfg.N k ^ (cfg.κ * s - v - ζ) ∧ 2 ≤ cfg.N k ^ ε := by
    filter_upwards [h.eventually_assignment_level hs (by linarith),
      h.subpower.2 1 (by norm_num), h.subpower.2 _ hgap,
      Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow h.scale_limit hε 2]
      with k hk hK hKg htwo
    exact ⟨hk, by simpa using hK, hKg, htwo⟩
  apply ((hbins ζ hζ).and_eventually hlate).mono
  rintro k ⟨⟨i, L, source, j, hL₀, hL, hsource, hcoeff, hmass⟩, parent, hK, hKg, htwo⟩
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hmass' : ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s i) ≤
      cfg.ρ k (source ∩ {p | ⌊cfg.midpointValue k s i L p / cfg.N k ^ (-s - v)⌋ = j}) := by
    refine le_trans ?_ hmass
    gcongr
  have herror := parent.integrated_primitive_error h hKg
  have herror' : (cfg.N k ^ ζ * cfg.N k ^ (-s)) * cfg.timeLength k s +
      cfg.N k ^ (-s - v) ≤ cfg.N k ^ ε * cfg.N k ^ (-s - v) := by
    calc
      _ ≤ cfg.N k ^ (-s - v) + cfg.N k ^ (-s - v) := add_le_add herror le_rfl
      _ = 2 * cfg.N k ^ (-s - v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hN.le _)
  exact ⟨i, parent.quadratic_candidate_of_midpoint_bin h i L source j hs.le hv.le hε.le
    (by positivity) hK hL₀ (parent.primitive_slopes_polynomial h hs.le hs1.le hζ1 hK i L hL)
    hsource hcoeff herror' hmass'⟩

end Data

end

end Submission.Obl.k4_critical_intercept_concentration
