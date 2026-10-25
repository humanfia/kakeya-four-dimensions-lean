import Submission.Obl.k4_critical_intercept_concentration.SourceRegularity
import Submission.Obl.k4_critical_intercept_concentration.CandidateRestore

namespace Submission.Obl.k4_critical_intercept_concentration

open Set MeasureTheory Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- A heavy original-source midpoint bin gives the exact frozen quadratic
alternative. The coefficient exponent is the fixed number12, independent
of the final positive loss. -/
theorem AssignmentLevel.quadratic_candidate_of_midpoint_bin (h : cfg.Valid)
    {k : ℕ} {s v ε E : ℝ} (parent : cfg.AssignmentLevel k s)
    (ip : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (source : Set (α × ℝ)) (j : ℤ)
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hε : 0 ≤ ε) (hE : 0 ≤ E)
    (hK : cfg.K k ≤ cfg.N k) (hL₀ : L 0 = 0)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ (3 : ℕ))
    (hsource : source ⊆ cfg.primitiveEvent k s ip L E)
    (hcoeff : ∀ p ∈ source, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k)
    (herror : E * cfg.timeLength k s + cfg.N k ^ (-s - v) ≤
      cfg.N k ^ ε * cfg.N k ^ (-s - v))
    (hmass : ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) *
      cfg.ν k (cfg.A k s ip) ≤
      cfg.ρ k (source ∩ {p | ⌊cfg.midpointValue k s ip L p / cfg.N k ^ (-s - v)⌋ = j})) :
    cfg.QuadraticCandidate k s v ε 12 ip := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK0 : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hH : 0 < cfg.timeLength k s := cfg.timeLength_pos k s
  have ha : 0 < cfg.N k ^ (-s - v) := Real.rpow_pos_of_pos hN _
  have ha1 : cfg.N k ^ (-s - v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hprior : 0 < cfg.ν k (cfg.A k s ip) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) (parent.prior_lower ip)
  have hmasspos : 0 < cfg.ρ k
      (source ∩ {p | ⌊cfg.midpointValue k s ip L p / cfg.N k ^ (-s - v)⌋ = j}) := by
    refine lt_of_lt_of_le ?_ hmass
    positivity
  have hnonempty : (source ∩
      {p | ⌊cfg.midpointValue k s ip L p / cfg.N k ^ (-s - v)⌋ = j}).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty] at hmasspos
    exact (lt_irrefl 0) hmasspos
  obtain ⟨p₀, hp₀, hbin₀⟩ := hnonempty
  have hM : 1 ≤ cfg.N k ^ (3 : ℕ) := one_le_pow₀ hN1
  have hvalue := midpointValue_bound k s ip L (cfg.K k) (cfg.N k ^ (3 : ℕ))
    (h.subpower.1 k) hM hL₀ hL p₀ (hcoeff p₀ hp₀)
  have hvalue' : |cfg.midpointValue k s ip L p₀| ≤ 16 * cfg.N k ^ (4 : ℕ) := by
    refine hvalue.trans ?_
    calc
      _ ≤ 16 * cfg.N k * cfg.N k ^ (3 : ℕ) := by gcongr
      _ = _ := by ring
  have hround := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error
    ha (cfg.midpointValue k s ip L p₀)
  rw [hbin₀] at hround
  have hfour : 1 ≤ cfg.N k ^ (4 : ℕ) := one_le_pow₀ hN1
  have hconstant : 17 ≤ cfg.N k ^ (5 : ℕ) :=
    (by norm_num : (17 : ℝ) ≤ 2 ^ (5 : ℕ)).trans
      (pow_le_pow_left₀ (by norm_num) (h.scale k) 5)
  have hoffset : |cfg.N k ^ (-s - v) * (j : ℝ)| ≤ cfg.N k ^ (9 : ℕ) := by
    calc
      _ ≤ |cfg.midpointValue k s ip L p₀ - cfg.N k ^ (-s - v) * (j : ℝ)| +
          |cfg.midpointValue k s ip L p₀| := by
        simpa only [abs_sub_comm, sub_zero] using
          abs_sub_le (cfg.N k ^ (-s - v) * (j : ℝ)) (cfg.midpointValue k s ip L p₀) 0
      _ ≤ 1 + 16 * cfg.N k ^ (4 : ℕ) := add_le_add (hround.trans ha1) hvalue'
      _ ≤ 17 * cfg.N k ^ (4 : ℕ) := by linarith
      _ ≤ cfg.N k ^ (5 : ℕ) * cfg.N k ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_right hconstant (by positivity)
      _ = _ := by ring
  have hZ : 1 ≤ cfg.N k ^ (9 : ℕ) := one_le_pow₀ hN1
  have hL' : ∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ (9 : ℕ) := fun e =>
    (hL e).trans (pow_le_pow_right₀ hN1 (by norm_num))
  have hconstant5 : 5 ≤ cfg.N k ^ (3 : ℕ) :=
    (by norm_num : (5 : ℝ) ≤ 2 ^ (3 : ℕ)).trans
      (pow_le_pow_left₀ (by norm_num) (h.scale k) 3)
  have hcoeff12 : 5 * cfg.N k ^ (9 : ℕ) ≤ cfg.N k ^ (12 : ℝ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc
      _ ≤ cfg.N k ^ (3 : ℕ) * cfg.N k ^ (9 : ℕ) :=
        mul_le_mul_of_nonneg_right hconstant5 (by positivity)
      _ = _ := by ring
  refine quadratic_candidate_of_affine_source h k s v ε 12 (cfg.N k ^ (9 : ℕ))
    (cfg.N k ^ (-s - v) * (j : ℝ)) ip L
    (source ∩ {p | ⌊cfg.midpointValue k s ip L p / cfg.N k ^ (-s - v)⌋ = j})
    hε (by norm_num) hZ hL₀ hL' hoffset hcoeff12 ?_ hmass
  intro p hp
  have hsrc := hsource hp.1
  refine ⟨hsrc.1, hsrc.2.1, ?_⟩
  have hbin : ⌊(affineResidualIntercept L (cfg.b k p.1) +
      (cfg.blockLeft k s ip + cfg.timeLength k s / 2) *
        affineResidualSlope L (cfg.b k p.1)) / cfg.N k ^ (-s - v)⌋ = j := by
    simpa only [mem_setOf_eq, midpointValue, cfg.midpoint_eq_blockLeft] using hp.2
  have hwhole := affineHiddenTest_whole_block L (cfg.b k p.1) (cfg.N k ^ (-s - v))
    E (cfg.timeLength k s) (cfg.blockLeft k s ip) j ha hE
    (cfg.timeLength_pos k s).le hsrc.2.2 hbin
  intro t ht
  rw [cfg.block_interval] at ht
  exact (hwhole t ht).trans herror

end Data

end

end Submission.Obl.k4_critical_intercept_concentration
