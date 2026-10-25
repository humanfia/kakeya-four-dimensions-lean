import Submission.Obl.k4_extremal_profile_setup.Horizon

namespace Submission.Obl.k4_extremal_profile_setup

open Set Filter
open scoped Topology

/-- A bounded scalar parameter can be fixed while retaining arbitrarily small
tolerances and arbitrarily large resolutions.  The format is fixed before this
extraction; it is not selected afresh for each tolerance.
-/
theorem compact_frequency_extraction (A : ℝ → ℕ → ℝ → Prop) (z : ℝ)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ∃ t ∈ Icc (0 : ℝ) z, A ε k t)
    (hmono : ∀ ε ε' : ℝ, ε ≤ ε' → ∀ k t, A ε k t → A ε' k t) :
    ∃ h ∈ Icc (0 : ℝ) z, ∀ ε : ℝ, 0 < ε →
      ∃ᶠ k in atTop, ∃ t ∈ Icc (0 : ℝ) z, A ε k t ∧ |t - h| ≤ ε := by
  classical
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hτ (n : ℕ) : 0 < τ n := by dsimp [τ]; positivity
  have hτlim : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) : ∃ k, n ≤ k ∧ ∃ t ∈ Icc (0 : ℝ) z, A (τ n) k t :=
    (frequently_atTop.mp (hA (τ n) (hτ n))) n
  choose k hk t ht hw using hex
  obtain ⟨h, hh, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq ht
  have hkT : Tendsto k atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop n] with i hi
    exact hi.trans (hk i)
  refine ⟨h, hh, fun ε hε => ?_⟩
  have hsmall : ∀ᶠ n in atTop, τ (φ n) < ε :=
    (hτlim.comp hφ.tendsto_atTop).eventually (Iio_mem_nhds hε)
  have hnear : ∀ᶠ n in atTop, |t (φ n) - h| < ε := by
    simpa only [Function.comp_apply, Metric.mem_ball, Real.dist_eq] using
      hlim.eventually (Metric.ball_mem_nhds h hε)
  have hevent : ∀ᶠ n in atTop,
      ∃ t ∈ Icc (0 : ℝ) z, A ε (k (φ n)) t ∧ |t - h| ≤ ε := by
    filter_upwards [hsmall, hnear] with n hn hnear
    exact ⟨t (φ n), ht (φ n), hmono _ _ hn.le _ _ (hw (φ n)), hnear.le⟩
  by_contra hn
  have hneg := (hkT.comp hφ.tendsto_atTop).eventually (not_frequently.mp hn)
  obtain ⟨n, hn⟩ := (hevent.and hneg).exists
  exact hn.2 hn.1

/-- A true terminal chart system with a two-sided time window at one sample. -/
def TimeBandedAt (p : Data) (M D : ℕ) (h ε : ℝ) (k : ℕ) : Prop :=
  ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
    p.N k ^ (h - ε) ≤ (2 : ℝ) ^ a.T ∧ (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧
    a.TrueAt M D p.L

def TimeBanded (p : Data) (h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, TimeBandedAt p M D h ε k

/-- True terminal systems have a convergent subsequence of their logarithmic
time exponents, with the original format bounds kept fixed.
-/
theorem Terminal.exists_timeBanded {p : Data} (hp : p.Valid) {z : ℝ}
    (ht : Terminal p z) : ∃ h ∈ Icc (0 : ℝ) z, TimeBanded p h := by
  classical
  obtain ⟨M, D, ht⟩ := ht
  let A (ε : ℝ) (k : ℕ) (t : ℝ) : Prop :=
    ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
      a.TrueAt M D p.L ∧ (2 : ℝ) ^ a.T = p.N k ^ t
  have hA : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ∃ t ∈ Icc (0 : ℝ) z, A ε k t := by
    intro ε hε
    apply (ht ε hε).mono
    intro k hk
    obtain ⟨a, hκ, hK, hε, hT, htrue⟩ := hk
    let t := Real.logb (p.N k) ((2 : ℝ) ^ a.T)
    have hN : 1 < p.N k := lt_of_lt_of_le (by norm_num) (hp.N_ge k)
    have he : p.N k ^ t = (2 : ℝ) ^ a.T :=
      Real.rpow_logb (zero_lt_one.trans hN) hN.ne' (by positivity)
    have ht0 : 0 ≤ t := by
      apply (Real.rpow_le_rpow_left_iff hN).mp
      simpa only [Real.rpow_zero, he] using one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have htz : t ≤ z := by
      apply (Real.rpow_le_rpow_left_iff hN).mp
      rwa [he]
    exact ⟨t, ⟨ht0, htz⟩, a, hκ, hK, hε, htrue, he.symm⟩
  have hmono : ∀ ε ε' : ℝ, ε ≤ ε' → ∀ k t, A ε k t → A ε' k t := by
    rintro ε ε' hε k t ⟨a, hκ, hK, haε, htrue, he⟩
    exact ⟨a, hκ, hK, haε.trans (Real.rpow_le_rpow_of_exponent_le
      (le_trans (by norm_num) (hp.N_ge k)) hε), htrue, he⟩
  obtain ⟨h, hh, hband⟩ := compact_frequency_extraction A z hA hmono
  refine ⟨h, hh, M, D, fun ε hε => (hband ε hε).mono fun k hk => ?_⟩
  obtain ⟨t, _, ha, hdist⟩ := hk
  obtain ⟨a, hκ, hK, haε, htrue, he⟩ := ha
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (hp.N_ge k)
  have hdist' := abs_le.mp hdist
  refine ⟨a, hκ, hK, haε, ?_, ?_, htrue⟩
  · rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith [hdist'.1])
  · rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith [hdist'.2])

/-- A two-sided system is a terminal system at every slightly larger time cost. -/
theorem TimeBanded.terminal {p : Data} (hp : p.Valid) {h z : ℝ}
    (ht : TimeBanded p h) (hz : h < z) : Terminal p z := by
  obtain ⟨M, D, ht⟩ := ht
  refine ⟨M, D, fun ε hε => ?_⟩
  let δ := min ε (z - h)
  have hδ : 0 < δ := lt_min hε (sub_pos.mpr hz)
  apply (ht δ hδ).mono
  rintro k ⟨a, hκ, hK, haδ, _, hT, htrue⟩
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (hp.N_ge k)
  refine ⟨a, hκ, hK, haδ.trans ?_, hT.trans ?_, htrue⟩
  · exact Real.rpow_le_rpow_of_exponent_le hN (min_le_left _ _)
  · exact Real.rpow_le_rpow_of_exponent_le hN (by dsimp [δ]; linarith [min_le_right ε (z - h)])

theorem horizon_le_timeBanded {p : Data} (hp : p.Valid) {h : ℝ}
    (ht : TimeBanded p h) : horizon p ≤ h := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact horizon_le hp (ht.terminal hp (by linarith))

/-- The extracted time exponent lies above the original horizon infimum. -/
theorem Terminal.exists_timeBanded_above_horizon {p : Data} (hp : p.Valid) {z : ℝ}
    (ht : Terminal p z) : ∃ h : ℝ, horizon p ≤ h ∧ h ≤ z ∧ TimeBanded p h := by
  obtain ⟨h, hh, hband⟩ := ht.exists_timeBanded hp
  exact ⟨h, horizon_le_timeBanded hp hband, hh.2, hband⟩

end Submission.Obl.k4_extremal_profile_setup
