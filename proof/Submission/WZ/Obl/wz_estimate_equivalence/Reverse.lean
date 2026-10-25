-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.Reverse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_estimate_equivalence.Estimates

namespace WangZahlLot.Obl.wz_estimate_equivalence

/-- The loss from specializing both error constants to `δ ^ (-η)` is at most `δ ^ η`. -/
theorem small_error_coefficient_le {σ ω ε ε' η δ a N : ℝ}
    (hσ : 0 ≤ σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η)
    (ha : 0 ≤ a) (hN : 0 < N) (hε : ε' + η ≤ ε) :
    a * δ ^ (ω + ε) * (N * δ ^ 2) * (N * δ) ^ (-σ) ≤
      a * δ ^ (ω + ε') * (δ ^ (-η))⁻¹ * (N * δ ^ 2) *
        ((δ ^ (-η)) ^ (-(3 / 2 : ℝ)) * δ ^ (-η) * (N * δ)) ^ (-σ) := by
  let m := δ ^ (-η)
  have hm : 1 ≤ m :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hη)
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmfac : m ^ (-(3 / 2 : ℝ)) * m ≤ 1 := by
    calc
      m ^ (-(3 / 2 : ℝ)) * m ≤ m ^ (-1 : ℝ) * m := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hm (by norm_num)) hm0.le
      _ = 1 := by rw [Real.rpow_neg_one, inv_mul_cancel₀ hm0.ne']
  have harg : m ^ (-(3 / 2 : ℝ)) * m * (N * δ) ≤ N * δ := by
    simpa using mul_le_mul_of_nonneg_right hmfac (mul_nonneg hN.le hδ.le)
  have hpow : (N * δ) ^ (-σ) ≤
      (m ^ (-(3 / 2 : ℝ)) * m * (N * δ)) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) harg (neg_nonpos.mpr hσ)
  have hinv : m⁻¹ = δ ^ η := by
    dsimp [m]
    rw [Real.rpow_neg hδ.le, inv_inv]
  have hδpow : δ ^ (ω + ε) ≤ δ ^ (ω + ε') * m⁻¹ := by
    rw [hinv, ← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  change _ ≤ a * δ ^ (ω + ε') * m⁻¹ * (N * δ ^ 2) *
    (m ^ (-(3 / 2 : ℝ)) * m * (N * δ)) ^ (-σ)
  calc
    a * δ ^ (ω + ε) * (N * δ ^ 2) * (N * δ) ^ (-σ) ≤
        a * (δ ^ (ω + ε') * m⁻¹) * (N * δ ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * m * (N * δ)) ^ (-σ) := by
      gcongr
    _ = _ := by ring

/-- The bounded-error estimate implies the small-error estimate. -/
theorem d_of_eBounded {σ ω : ℝ} (hσ : 0 ≤ σ) (hE : EBounded σ ω) : D σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hE (ε / 2) (by positivity)
  let η' := min η (ε / 2)
  have hη' : 0 < η' := lt_min hη (by positivity)
  refine ⟨a, ha, η', hη', ?_⟩
  intro δ hδ hδmax n x v Y hn hv hT hsep hY hYT hdens hK hF
  have hδ1 : δ ≤ 1 := le_trans hδmax (by norm_num)
  have hm : 1 ≤ δ ^ (-η') :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hdens' : ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤
      Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hdens
    have hp : δ ^ η ≤ δ ^ η' :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)
    gcongr
  have hbound := h δ hδ hδmax (δ ^ (-η')) (δ ^ (-η')) hm hm
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg (min_le_left _ _)))
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg (min_le_left _ _)))
    n x v Y hn hv hT hsep hY hYT hdens' hK hF
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
  exact small_error_coefficient_le hσ hδ hδ1 hη'.le ha.le
    (by exact_mod_cast hn) (by have := min_le_right η (ε / 2); dsimp [η']; linarith)

/-- Restricting the allowed values of the counting constants. -/
theorem eBounded_of_e {σ ω : ℝ} (hE : E σ ω) : EBounded σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hE ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδmax m l hm hl _ _
  exact h δ hδ hδmax m l hm hl

/-- The arbitrary-error estimate implies the small-error estimate. -/
theorem d_of_e {σ ω : ℝ} (hσ : 0 ≤ σ) (hE : E σ ω) : D σ ω :=
  d_of_eBounded hσ (eBounded_of_e hE)

end WangZahlLot.Obl.wz_estimate_equivalence
