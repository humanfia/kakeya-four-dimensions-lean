/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/AsymptoticUpper.lean.
   Existing source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.SourceRegularity
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/- The next lemma is adapted from o212/x0762, commit ecff5a0a89fd,
   AsymptoticRestore.lean, in the same owned subtree. -/
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

/-- The large physical primitive slopes cancel against the actual parent
time length in contact coordinates. -/
theorem sourcePredictorSlope_le (h : cfg.Valid) (k : ℕ) (s ζ : ℝ) (hζ : 0 ≤ ζ) :
    cfg.sourcePredictorSlope k s (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) ≤
      108 * cfg.K k ^ 6 * cfg.N k ^ ζ := by
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hcancel : cfg.timeLength k s * (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) = cfg.N k ^ ζ := by
    simp [timeLength, mul_comm, mul_left_comm, mul_assoc]
  have hH : cfg.timeLength k s ≤ cfg.N k ^ ζ :=
    (cfg.timeLength_le_one k s).trans (Real.one_le_rpow hN1 hζ)
  have hK26 : cfg.K k ^ 2 ≤ cfg.K k ^ 6 := pow_le_pow_right₀ hK (by norm_num)
  calc
    _ = 96 * cfg.K k ^ 6 * cfg.timeLength k s + 12 * cfg.K k ^ 2 *
        (cfg.timeLength k s * (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s)) := by
      dsimp [sourcePredictorSlope]
      ring
    _ = 96 * cfg.K k ^ 6 * cfg.timeLength k s + 12 * cfg.K k ^ 2 * cfg.N k ^ ζ := by rw [hcancel]
    _ ≤ 96 * cfg.K k ^ 6 * cfg.N k ^ ζ + 12 * cfg.K k ^ 6 * cfg.N k ^ ζ := by gcongr
    _ = _ := by ring

/-- One fixed fine mesh works for every actual source table at these fixed
depths; all remaining geometric losses are powers of the original subpower K. -/
theorem Valid.eventually_pair_parameters (h : cfg.Valid) {s v ζ : ℝ}
    (hs : 0 < s) (hv : 0 < v) (hvs : v ≤ s) (hsU : s + v ≤ cfg.U)
    (hζ : 0 < ζ) (hζs : ζ ≤ s) (hgap : 0 < cfg.κ * s - v - ζ) :
    ∀ᶠ k in atTop, cfg.AssignmentLevel k s ∧ cfg.AssignmentLevel k (s + v) ∧
      cfg.timeLength k s * (cfg.N k ^ ζ * cfg.N k ^ (-s)) ≤ cfg.K k * cfg.N k ^ (-(s + v)) ∧
      3 * cfg.sourcePredictorSlope k s (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) * cfg.N k ^ (-10 * s) ≤
        (4 * cfg.K k ^ 4) * cfg.N k ^ (-(s + v)) ∧
      cfg.N k ^ (-10 * s) ≤ cfg.timeLength k (s + v) ^ 2 := by
  have hconst := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k) h.scale_limit h.subpower.1 h.subpower.2
    6 (show -9 * s < -2 * s by linarith) (A := 324) (by norm_num)
  filter_upwards [h.eventually_assignment_level hs (by linarith),
    h.eventually_assignment_level (show 0 < s + v by linarith) hsU,
    h.subpower.2 s hs, h.subpower.2 _ hgap, hconst]
    with k parent child hKs hKg hconst
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have ha : 0 < cfg.N k ^ (-(s + v)) := Real.rpow_pos_of_pos hN _
  have hK4 : 1 ≤ 4 * cfg.K k ^ 4 := by have hh := one_le_pow₀ hK (n := 4); linarith
  refine ⟨parent, child, ?_, ?_, ?_⟩
  · calc
      _ = (cfg.N k ^ ζ * cfg.N k ^ (-s)) * cfg.timeLength k s := by ring
      _ ≤ cfg.N k ^ (-s - v) := parent.integrated_primitive_error h hKg
      _ ≤ cfg.K k * cfg.N k ^ (-(s + v)) := by
        rw [show -s - v = -(s + v) by ring]
        exact le_mul_of_one_le_left ha.le hK
  · have hpred := sourcePredictorSlope_le h k s ζ hζ.le
    have hζpow := Real.rpow_le_rpow_of_exponent_le hN1 hζs
    have hprod : cfg.N k ^ s * cfg.N k ^ (-10 * s) = cfg.N k ^ (-9 * s) := by
      rw [← Real.rpow_add hN]
      congr 1
      ring
    calc
      _ ≤ 3 * (108 * cfg.K k ^ 6 * cfg.N k ^ ζ) * cfg.N k ^ (-10 * s) := by gcongr
      _ ≤ 3 * (108 * cfg.K k ^ 6 * cfg.N k ^ s) * cfg.N k ^ (-10 * s) := by gcongr
      _ = 324 * cfg.K k ^ 6 * cfg.N k ^ (-9 * s) := by rw [← hprod]; ring
      _ ≤ cfg.N k ^ (-2 * s) := hconst.le
      _ ≤ cfg.N k ^ (-(s + v)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ _ := le_mul_of_one_le_left ha.le hK4
  · have hκt : cfg.κ * (s + v) ≤ 2 * s := by
      nlinarith [h.rate_le_one, h.rate_pos]
    have htime : (2 : ℝ) ^ cfg.T k (s + v) ≤ cfg.N k ^ (3 * s) := by
      calc
        _ ≤ cfg.K k * cfg.N k ^ (cfg.κ * (s + v)) := child.time_upper
        _ ≤ cfg.N k ^ s * cfg.N k ^ (2 * s) := by
          apply mul_le_mul hKs (Real.rpow_le_rpow_of_exponent_le hN1 hκt)
            (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
        _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
    have hlow : cfg.N k ^ (-(3 * s)) ≤ cfg.timeLength k (s + v) :=
      Submission.Obl.k4_discrete_of_terminal_charts.dyadic_time_lower_bound hN htime
    calc
      _ ≤ cfg.N k ^ (-(3 * s) + -(3 * s)) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (cfg.N k ^ (-(3 * s))) ^ 2 := by rw [Real.rpow_add hN, pow_two]
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hlow 2

/-- The original-source upper bound in fixed power meshes: there are at
most2^30*K^20*N^(d*v)/omega^3 actual midpoint-bin/base-cell pairs. -/
theorem Valid.eventually_source_pair_upper (h : cfg.Valid) {s v ζ : ℝ}
    (hs : 0 < s) (hv : 0 < v) (hvs : v ≤ s) (hsU : s + v ≤ cfg.U)
    (hζ : 0 < ζ) (hζs : ζ ≤ s) (hgap : 0 < cfg.κ * s - v - ζ) :
    ∀ᶠ k in atTop, ∀ (ip : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (source : Set (α × ℝ)),
      L 0 = 0 → (∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) →
      source ⊆ cfg.primitiveEvent k s ip L (cfg.N k ^ ζ * cfg.N k ^ (-s)) →
      (∀ p ∈ source, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k) →
      (∀ p ∈ source, ∃ i : Fin (cfg.n k (s + v)),
        p.1 ∈ cfg.B k (s + v) i ∧ p.2 ∈ I (cfg.T k (s + v)) (cfg.j k (s + v) i) ∧
        cfg.A k (s + v) i ⊆ cfg.A k s ip ∧
        I (cfg.T k (s + v)) (cfg.j k (s + v) i) ⊆ I (cfg.T k s) (cfg.j k s ip)) →
      ∃ F : Finset (ℤ × (Fin 3 → ℤ)),
        (∀ u, u ∈ F ↔ ∃ p ∈ source,
          cfg.sourcePair k s ip L (cfg.N k ^ (-s - v)) (cfg.N k ^ (-10 * s)) p = u) ∧
        (F.card : ℝ) * (cfg.N k ^ (-10 * s)) ^ 3 ≤
          1073741824 * cfg.K k ^ 20 * cfg.N k ^ (cfg.d * v) := by
  classical
  filter_upwards [h.eventually_pair_parameters hs hv hvs hsU hζ hζs hgap]
    with k hk ip L source hL₀ hL hsource hcoeff hcover
  obtain ⟨parent, child, hsmall, hmesh, hδbase⟩ := hk
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK := h.subpower.1 k
  have hδ : 0 < cfg.N k ^ (-10 * s) := Real.rpow_pos_of_pos hN _
  have hd : (cfg.N k ^ (-s) / cfg.N k ^ (-(s + v))) ^ cfg.d = cfg.N k ^ (cfg.d * v) := by
    have hr : cfg.N k ^ (-s) / cfg.N k ^ (-(s + v)) = cfg.N k ^ v := by
      rw [← Real.rpow_sub hN]
      congr 1
      ring
    rw [hr, ← Real.rpow_mul hN.le]
    congr 1
    ring
  by_cases hnonempty : source.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hnonempty
    obtain ⟨i₀, hi₀, hit₀, hA₀, hI₀⟩ := hcover p₀ hp₀
    have hT := time_depth_le_of_block_subset _ _ hI₀
    have hHorder : cfg.timeLength k (s + v) ≤ cfg.timeLength k s := by
      unfold timeLength
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hT)
    have hrel : cfg.timeLength k (s + v) / cfg.timeLength k s ≤ 1 :=
      (div_le_one (cfg.timeLength_pos k s)).mpr hHorder
    have hδrel : cfg.N k ^ (-10 * s) ≤
        (cfg.timeLength k (s + v) / cfg.timeLength k s) ^ 2 := by
      apply hδbase.trans
      apply pow_le_pow_left₀ (cfg.timeLength_pos k (s + v)).le _ 2
      exact (le_div_iff₀ (cfg.timeLength_pos k s)).mpr
        ((mul_le_mul_of_nonneg_left (cfg.timeLength_le_one k s)
          (cfg.timeLength_pos k (s + v)).le).trans_eq (mul_one _))
    have hM : 1 ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s := by
      have h₁ : 1 ≤ cfg.N k ^ ζ := Real.one_le_rpow (by linarith [h.scale k]) hζ.le
      have h₂ : 1 ≤ (2 : ℝ) ^ cfg.T k s := one_le_pow₀ (by norm_num)
      nlinarith
    obtain ⟨F, hF, hcard⟩ := parent.exists_source_pair_table h child ip (by linarith : 0 ≤ s + v)
      L (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) (cfg.N k ^ ζ * cfg.N k ^ (-s))
      (4 * cfg.K k ^ 4) (cfg.N k ^ (-10 * s))
      (16 * cfg.K k * (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s))
      (by positivity) hL le_rfl hδ hrel hδrel hsmall hmesh source
      (fun p hp => hsource hp) hcover
      (fun p hp => midpointValue_bound k s ip L (cfg.K k) _ hK hM hL₀ hL p (hcoeff p hp))
    rw [hd] at hcard
    refine ⟨F, ?_, ?_⟩
    · simpa only [show -(s + v) = -s - v by ring] using hF
    · convert hcard using 1 <;> ring
  · refine ⟨∅, ?_, ?_⟩
    · have hsource_empty := Set.not_nonempty_iff_eq_empty.mp hnonempty
      simp [hsource_empty]
    · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity

/-- Any prescribed positive power absorbs the entire original upper-count
constant and its subpower geometric losses. -/
theorem Valid.eventually_source_pair_upper_power (h : cfg.Valid) {s v ζ δ : ℝ}
    (hs : 0 < s) (hv : 0 < v) (hvs : v ≤ s) (hsU : s + v ≤ cfg.U)
    (hζ : 0 < ζ) (hζs : ζ ≤ s) (hgap : 0 < cfg.κ * s - v - ζ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ (ip : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (source : Set (α × ℝ)),
      L 0 = 0 → (∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) →
      source ⊆ cfg.primitiveEvent k s ip L (cfg.N k ^ ζ * cfg.N k ^ (-s)) →
      (∀ p ∈ source, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k) →
      (∀ p ∈ source, ∃ i : Fin (cfg.n k (s + v)),
        p.1 ∈ cfg.B k (s + v) i ∧ p.2 ∈ I (cfg.T k (s + v)) (cfg.j k (s + v) i) ∧
        cfg.A k (s + v) i ⊆ cfg.A k s ip ∧
        I (cfg.T k (s + v)) (cfg.j k (s + v) i) ⊆ I (cfg.T k s) (cfg.j k s ip)) →
      ∃ F : Finset (ℤ × (Fin 3 → ℤ)),
        (∀ u, u ∈ F ↔ ∃ p ∈ source,
          cfg.sourcePair k s ip L (cfg.N k ^ (-s - v)) (cfg.N k ^ (-10 * s)) p = u) ∧
        (F.card : ℝ) * (cfg.N k ^ (-10 * s)) ^ 3 ≤ cfg.N k ^ (cfg.d * v + δ) := by
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k) h.scale_limit h.subpower.1 h.subpower.2
    20 (show cfg.d * v < cfg.d * v + δ by linarith) (A := 1073741824) (by norm_num)
  filter_upwards [h.eventually_source_pair_upper hs hv hvs hsU hζ hζs hgap, hcost]
    with k hk hc ip L source hL₀ hL hsource hcoeff hcover
  obtain ⟨F, hF, hcard⟩ := hk ip L source hL₀ hL hsource hcoeff hcover
  exact ⟨F, hF, hcard.trans hc.le⟩


end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
