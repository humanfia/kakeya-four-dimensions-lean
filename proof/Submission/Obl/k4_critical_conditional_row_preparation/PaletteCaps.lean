/- Adapted from our LOT tree o211, session x0736, commit fb9fb2638e83e4e42cdf985859ec4b5deb228222,
`Submission/Obl/k4_critical_affine_derivative_preparation/PaletteCaps.lean`.
Earlier provenance comments in that file are retained below. -/

import Submission.Obl.k4_critical_conditional_row_preparation.Model
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_scalar_initial_true_horizon.InitialCells

namespace Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

/-- Four grid cells suffice to cover a closed interval of twice the mesh
length. The measure need not be its own velocity marginal. -/
theorem interval_cap_of_floor_cell_caps (π : Measure ℝ) (r C x : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hcap : ∀ j : ℤ, π {w | ⌊w / r⌋ = j} ≤ ENNReal.ofReal C) :
    π (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (4 * C) := by
  let F := Finset.Icc ⌊(x - r) / r⌋ ⌊(x + r) / r⌋
  have hcard : (F.card : ℝ) ≤ 4 := by
    have hc := Submission.Obl.k4_scalar_initial_true_horizon.card_Icc_floor_le
      (show (x - r) / r ≤ (x + r) / r by gcongr; linarith)
    have heq : (x + r) / r - (x - r) / r + 2 = 4 := by field_simp; ring
    simpa only [F, heq] using hc
  have hcover : Icc (x - r) (x + r) ⊆ ⋃ j ∈ F, {w : ℝ | ⌊w / r⌋ = j} := by
    intro w hw
    refine mem_iUnion₂.mpr ⟨⌊w / r⌋, Finset.mem_Icc.mpr ?_, rfl⟩
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hw.1 hr.le),
      Int.floor_mono (div_le_div_of_nonneg_right hw.2 hr.le)⟩
  calc
    _ ≤ π (⋃ j ∈ F, {w : ℝ | ⌊w / r⌋ = j}) := measure_mono hcover
    _ ≤ ∑ j ∈ F, π {w : ℝ | ⌊w / r⌋ = j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ F, ENNReal.ofReal C := Finset.sum_le_sum (fun j _ => hcap j)
    _ = ENNReal.ofReal ((F.card : ℝ) * C) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hC)

/-- Grid palette caps on all exponent scales between v0 and a give the
whole interval cap above the mesh N^-a; larger radii use probability alone. -/
theorem interval_cap_from_power_grid_caps
    (π : Measure ℝ) [IsProbabilityMeasure π] (N K S a v₀ ε : ℝ)
    (hN : 1 < N) (hK : 0 ≤ K) (hS : 0 < S) (_hv₀ : 0 < v₀)
    (_hv₀a : v₀ ≤ a) (hv₀ε : v₀ * S ≤ ε) (hKε : 4 * K ≤ N ^ ε)
    (hcap : ∀ v : ℝ, v₀ ≤ v → v ≤ a → ∀ j : ℤ,
      π {w | ⌊w / (N ^ (-v))⌋ = j} ≤ ENNReal.ofReal (K * N ^ (-S * v))) :
    ∀ x r : ℝ, N ^ (-a) ≤ r → r ≤ 1 →
      π (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ ε * r ^ S) := by
  intro x r hr hrone
  have hNpos : 0 < N := by linarith
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hNpos _).trans_le hr
  by_cases hrlarge : N ^ (-v₀) ≤ r
  · have hrlower : N ^ (-v₀ * S) ≤ r ^ S := by
      rw [Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hrlarge hS.le
    have hunit : 1 ≤ N ^ ε * r ^ S := by
      calc
        1 ≤ N ^ (ε + -v₀ * S) := Real.one_le_rpow hN.le (by linarith)
        _ = N ^ ε * N ^ (-v₀ * S) := Real.rpow_add hNpos _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hrlower (Real.rpow_nonneg hNpos.le _)
    calc
      _ ≤ π univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hunit
  · let v : ℝ := -Real.logb N r
    have hvlo : v₀ ≤ v := by
      have hl := (Real.logb_le_iff_le_rpow hN hrpos).mpr (lt_of_not_ge hrlarge).le
      dsimp [v]
      linarith
    have hvhi : v ≤ a := by
      have hl := (Real.le_logb_iff_rpow_le hN hrpos).mpr hr
      dsimp [v]
      linarith
    have hpow : N ^ (-v) = r := by
      dsimp [v]
      rw [neg_neg]
      exact Real.rpow_logb hNpos hN.ne' hrpos
    have hSscale : N ^ (-S * v) = r ^ S := by
      rw [← hpow, ← Real.rpow_mul hNpos.le]
      congr 1
      ring
    have hcells : ∀ j : ℤ, π {w | ⌊w / r⌋ = j} ≤ ENNReal.ofReal (K * r ^ S) := by
      simpa only [hpow, hSscale] using hcap v hvlo hvhi
    have hbound := interval_cap_of_floor_cell_caps π r (K * r ^ S) x hrpos
      (by positivity) hcells
    apply hbound.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      4 * (K * r ^ S) = (4 * K) * r ^ S := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKε (Real.rpow_nonneg hrpos.le _)

namespace Data

/-- The original external palette satisfies Row's interval bound uniformly
above each fixed power mesh, with every prescribed positive subpower loss. -/
theorem Valid.eventually_palette_interval_cap
    {α : Type} [MeasurableSpace α] {cfg : Data α} (h : cfg.Valid)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x r : ℝ, cfg.N k ^ (-a) ≤ r → r ≤ 1 →
      cfg.π k (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (cfg.N k ^ ε * r ^ cfg.S) := by
  let v₀ := min a (ε / (2 * cfg.S))
  have hv₀ : 0 < v₀ := lt_min ha (by have := h.palette_pos; positivity : 0 < ε / (2 * cfg.S))
  have hv₀a : v₀ ≤ a := min_le_left _ _
  have hv₀ε : v₀ * cfg.S ≤ ε := by
    have hs : 0 < cfg.S := h.palette_pos
    have hv := mul_le_mul_of_nonneg_right (min_le_right a (ε / (2 * cfg.S))) hs.le
    have heq : (ε / (2 * cfg.S)) * cfg.S = ε / 2 := by field_simp
    rw [heq] at hv
    linarith
  let R := 2 + a + v₀⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hv₀]
  have hRpos : 0 < R := by linarith
  have haR : a ≤ R := by dsimp [R]; linarith [inv_pos.mpr hv₀]
  have hRv₀ : R⁻¹ ≤ v₀ := by
    apply (inv_le_comm₀ hRpos hv₀).mpr
    dsimp [R]
    linarith
  have hRone : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR.le
  have hKε := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => (by linarith [h.scale k] : 1 ≤ cfg.N k)) h.scale_limit
    h.subpower.1 h.subpower.2 1 (show (0 : ℝ) < ε from hε)
    (show (0 : ℝ) ≤ 4 by norm_num)
  filter_upwards [h.caps R hR, hKε] with k hcaps hk
  have hN : 1 < cfg.N k := by linarith [h.scale k]
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  let : IsProbabilityMeasure (cfg.π k) := (h.basic k).2.2.1
  apply interval_cap_from_power_grid_caps (cfg.π k) (cfg.N k) (cfg.K k) cfg.S a v₀ ε
    hN hK h.palette_pos hv₀ hv₀a hv₀ε
    (by simpa only [pow_one, Real.rpow_zero, mul_one] using hk.le)
  intro v hvlo hvhi
  exact (hcaps 1 0 v hRone hR.le le_rfl (by linarith) (hRv₀.trans hvlo) (hvhi.trans haR)).1

end Data

end

end Submission.Obl.k4_critical_conditional_row_preparation
