import Submission.Obl.k4_critical_switching_state_preparation.NativePaletteCaps
import Submission.Obl.k4_critical_switching_state_preparation.FineUpper

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited
open scoped ENNReal

noncomputable section

/-- All contact-volume constants are powers of the original subpower slack. -/
theorem native_pair_cap_constant {K : ℝ} (hK : 1 ≤ K) :
    128 * K * (K ^ 2 + 2) * (1 + K + 2) ≤ 1536 * K ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have h₁ : K ^ 2 + 2 ≤ 3 * K ^ 2 := by linarith
  have h₂ : 1 + K + 2 ≤ 4 * K := by linarith
  calc
    _ ≤ 128 * K * (3 * K ^ 2) * (4 * K) := by gcongr
    _ = _ := by ring

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- One prescribed native mesh resolves every frozen fine switching state,
while the original contact-volume and hidden-scale factors remain intact. -/
theorem Valid.eventually_fine_palette_parameters (h : cfg.Valid) {s η : ℝ}
    (hs : 0 < s) (hsU : s + s / 16 ≤ cfg.U) (hη : 0 < η) (hηs : η ≤ s / 100) :
    ∀ᶠ k in atTop, cfg.AssignmentLevel k s ∧
      cfg.JointPaletteCap k (400 * s) (s + s / 16) (200 * s) ∧
      3 * (12 * cfg.K k * cfg.timeLength k s *
        (cfg.N k ^ η * (2 : ℝ) ^ cfg.T k s)) * cfg.N k ^ (-200 * s) ≤
          cfg.N k ^ (-(s + s / 16)) ∧
      cfg.timeLength k s * (cfg.N k ^ η * cfg.N k ^ (-s)) ≤
        cfg.K k * cfg.N k ^ (-(s + s / 16)) ∧
      cfg.N k ^ (-400 * s) ≤ cfg.timeLength k s * cfg.N k ^ (-200 * s) ∧
      6 * cfg.K k * cfg.N k ^ (-400 * s) ≤
        cfg.timeLength k s * cfg.N k ^ (-200 * s) ∧
      9 * cfg.K k * cfg.N k ^ (-400 * s) ≤
        (cfg.K k ^ 2 + 2) * cfg.timeLength k s ^ 2 * cfg.N k ^ (-200 * s) := by
  have hκ : cfg.κ = 1 / 2 := by linarith [h.critical_rate]
  have hgap : 0 < cfg.κ * s - s / 16 - η := by rw [hκ]; linarith
  have hpred := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k) h.scale_limit
    h.subpower.1 h.subpower.2 1 (show η - 200 * s < -(s + s / 16) by linarith)
    (A := 36) (by norm_num)
  have hZ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k) h.scale_limit
    h.subpower.1 h.subpower.2 1 (show -400 * s < -202 * s by linarith)
    (A := 6) (by norm_num)
  have hY := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k) h.scale_limit
    h.subpower.1 h.subpower.2 1 (show -400 * s < -204 * s by linarith)
    (A := 9) (by norm_num)
  filter_upwards [h.eventually_pair_parameters hs (by positivity) (by linarith) hsU
      hη (by linarith) hgap,
    h.eventually_joint_palette_cap (by positivity : 0 < 400 * s)
      (by linarith : 0 ≤ s + s / 16) (by positivity : 0 < 200 * s),
    h.subpower.2 s hs, hpred, hZ, hY]
    with k hp cap hKs hpred hZ hY
  obtain ⟨parent, child, hsmall, _, _⟩ := hp
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK := h.subpower.1 k
  have hH := cfg.timeLength_pos k s
  have hω : 0 < cfg.N k ^ (-200 * s) := Real.rpow_pos_of_pos hN _
  have hcancel : cfg.timeLength k s * (cfg.N k ^ η * (2 : ℝ) ^ cfg.T k s) = cfg.N k ^ η := by
    simp [timeLength, mul_comm, mul_left_comm, mul_assoc]
  have htime : (2 : ℝ) ^ cfg.T k s ≤ cfg.N k ^ (2 * s) := by
    calc
      _ ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) := parent.time_upper
      _ ≤ cfg.N k ^ s * cfg.N k ^ s := by
        apply mul_le_mul hKs (Real.rpow_le_rpow_of_exponent_le hN1 _)
          (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
        nlinarith [h.rate_le_one]
      _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
  have hlow : cfg.N k ^ (-(2 * s)) ≤ cfg.timeLength k s :=
    Submission.Obl.k4_discrete_of_terminal_charts.dyadic_time_lower_bound hN htime
  have hbase : cfg.N k ^ (-202 * s) ≤ cfg.timeLength k s * cfg.N k ^ (-200 * s) := by
    calc
      _ = cfg.N k ^ (-(2 * s)) * cfg.N k ^ (-200 * s) := by
        rw [← Real.rpow_add hN]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlow hω.le
  have hbase₂ : cfg.N k ^ (-204 * s) ≤ cfg.timeLength k s ^ 2 * cfg.N k ^ (-200 * s) := by
    calc
      _ = (cfg.N k ^ (-(2 * s))) ^ 2 * cfg.N k ^ (-200 * s) := by
        rw [pow_two, ← Real.rpow_add hN, ← Real.rpow_add hN]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hlow 2) hω.le
  refine ⟨parent, cap, ?_, hsmall, ?_, ?_, ?_⟩
  · calc
      _ = 36 * cfg.K k * (cfg.timeLength k s *
          (cfg.N k ^ η * (2 : ℝ) ^ cfg.T k s)) * cfg.N k ^ (-200 * s) := by ring
      _ = 36 * cfg.K k * cfg.N k ^ (η - 200 * s) := by
        rw [hcancel, mul_assoc (36 * cfg.K k), ← Real.rpow_add hN]
        congr 1
        ring
      _ ≤ _ := by simpa using hpred.le
  · exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hbase
  · exact (show 6 * cfg.K k * cfg.N k ^ (-400 * s) ≤ cfg.N k ^ (-202 * s) by
      simpa using hZ.le).trans hbase
  · apply (show 9 * cfg.K k * cfg.N k ^ (-400 * s) ≤ cfg.N k ^ (-204 * s) by
      simpa using hY.le).trans
    apply hbase₂.trans
    have hfac : 1 ≤ cfg.K k ^ 2 + 2 := by nlinarith [sq_nonneg (cfg.K k)]
    nlinarith [mul_le_mul_of_nonneg_right hfac (mul_nonneg (sq_nonneg (cfg.timeLength k s)) hω.le)]

/-- Fine-state joint caps in exactly the same original units as the source
mass and finite reference count. No source probability is introduced here. -/
theorem Valid.eventually_fine_original_palette_bound (h : cfg.Valid) {s η : ℝ}
    (hs : 0 < s) (hsU : s + s / 16 ≤ cfg.U) (hη : 0 < η) (hηs : η ≤ s / 100) :
    ∀ᶠ k in atTop, ∀ (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (source : Set (α × ℝ)),
      (∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ η * (2 : ℝ) ^ cfg.T k s) →
      source ⊆ cfg.primitiveEvent k s i L (cfg.N k ^ η * cfg.N k ^ (-s)) →
      ∀ (u : ℤ × (Fin 3 → ℤ)) (z : ℤ),
        cfg.μ k {p | p ∈ source ∧ cfg.sourcePair k s i L
          (cfg.N k ^ (-(s + s / 16))) (cfg.N k ^ (-200 * s)) p = u ∧
          ⌊cfg.b k p.1 3 / cfg.N k ^ (-200 * s)⌋ = z} ≤
        ENNReal.ofReal (1536 * cfg.K k ^ 4 * cfg.timeLength k s ^ 4 *
          (cfg.N k ^ (-200 * s)) ^ 3 * (cfg.N k ^ (-(s + s / 16))) ^ cfg.d) *
            cfg.π k {w | ⌊w / cfg.N k ^ (-200 * s)⌋ = z} := by
  classical
  filter_upwards [h.eventually_fine_palette_parameters hs hsU hη hηs]
    with k hp i L source hL hsource u z
  obtain ⟨parent, cap, hmesh, hsmall, hξt, hξZ, hξY⟩ := hp
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  by_cases hnonempty : ∃ p ∈ source, cfg.sourcePair k s i L
      (cfg.N k ^ (-(s + s / 16))) (cfg.N k ^ (-200 * s)) p = u
  · obtain ⟨p₀, hp₀, hcode⟩ := hnonempty
    have hh := parent.original_pair_palette_cap h i cap L source (cfg.N k ^ (-200 * s))
      (cfg.N k ^ η * (2 : ℝ) ^ cfg.T k s) (cfg.N k ^ η * cfg.N k ^ (-s)) 1 u p₀
      (Real.rpow_pos_of_pos hN _) (by positivity) (by norm_num) hp₀ hcode hL
      (fun p hp => hsource hp) (by simpa using hmesh) hsmall
      (by simpa only [neg_mul] using hξt)
      (by simpa only [neg_mul] using hξZ)
      (by simpa only [neg_mul] using hξY) z
    simp only [neg_mul] at hh ⊢
    apply hh.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (native_pair_cap_constant (h.subpower.1 k)) (by positivity))
        (by positivity)) (by positivity)
  · have heq : {p | p ∈ source ∧ cfg.sourcePair k s i L
        (cfg.N k ^ (-(s + s / 16))) (cfg.N k ^ (-200 * s)) p = u ∧
        ⌊cfg.b k p.1 3 / cfg.N k ^ (-200 * s)⌋ = z} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hnonempty ⟨p, hp.1, hp.2.1⟩
    rw [heq, measure_empty]
    exact bot_le

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
