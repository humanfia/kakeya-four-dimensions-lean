import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Pool
import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Geometry
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# The pooling contract from deep native-signal confinement

Adapted from accepted o248 (`k4_wide_velocity_lists_scalar_preparation`, files
`DeepMargins.lean`, `PoolContract.lean` and `PoolFinal.lean`). The deep depth is the
depth `t` supplied by `Parent.DeepConfinement`; since `r + 3 m / κ ≤ t`, the deep
blocks have length at most `K N^(-3m)`, which resolves the scalar mesh and the
terminal residual bin.
-/

set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- Deep true blocks resolve the two scalar base coordinates and the terminal
scalar residual bin, with all budgets fixed before incoming losses. -/
structure DeepMargins (p : Parent α) (k : ℕ) (t r v m : ℝ) : Prop where
  base : 2 * (6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) * (p.N k ^ (m / 10)) ^ 2 ≤
    p.N k ^ (-m)
  signal : 216 * p.N k ^ (m / 10) * (2 * p.K k) ^ 2 *
    (6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) ≤ p.N k ^ (-(r + v)) / 2
  diameter_le_one : 6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹ ≤ 1

theorem Valid.eventually_deep_margins (h : p.Valid)
    {r v m t : ℝ} (hr : 0 < r) (hm : 100 * (r + v) < m) (hv : 0 < v)
    (hrt : r + 3 * m / p.κ ≤ t) (htU : t ≤ p.U) :
    ∀ᶠ k in atTop, DeepMargins p k t r v m := by
  have hm0 : 0 < m := by linarith
  have hκ := h.rate_pos
  have hκt : 3 * m ≤ p.κ * t := by
    have h1 : p.κ * (r + 3 * m / p.κ) ≤ p.κ * t := mul_le_mul_of_nonneg_left hrt hκ.le
    have h2 : p.κ * (r + 3 * m / p.κ) = p.κ * r + 3 * m := by
      field_simp
    have h3 : 0 < p.κ * r := mul_pos hκ hr
    linarith
  have ht0 : 0 < t := by
    have : 0 < 3 * m / p.κ := by positivity
    linarith
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [h.scale k]
  have hbase := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 3
    (show -(3 * m) + m / 5 < -m by linarith) (show (0 : ℝ) ≤ 12 by norm_num)
  have hsignal := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 5
    (show -(3 * m) + m / 10 < -(r + v) by linarith) (show (0 : ℝ) ≤ 10368 by norm_num)
  let R := 2 + t⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr ht0]
  have hRt : R⁻¹ ≤ t := by
    apply (inv_le_comm₀ (by linarith : 0 < R) ht0).mpr
    dsimp [R]
    linarith
  filter_upwards [h.prepared R hR, hbase, hsignal] with k hprep hbase hsignal
  have hat := hprep t hRt htU
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hK0 : 0 < p.K k := by linarith
  set H := p.N k ^ (m / 10) with hH
  set q := ((2 : ℝ) ^ p.T k t)⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hqbound : q ≤ p.K k * p.N k ^ (-(3 * m)) := by
    have hlo : p.N k ^ (p.κ * t) / p.K k ≤ (2 : ℝ) ^ p.T k t := hat.1
    have hpow : 0 < p.N k ^ (p.κ * t) := Real.rpow_pos_of_pos hN _
    have h1 : q ≤ p.K k * (p.N k ^ (p.κ * t))⁻¹ := by
      calc q ≤ (p.N k ^ (p.κ * t) / p.K k)⁻¹ := inv_anti₀ (div_pos hpow hK0) hlo
        _ = p.K k * (p.N k ^ (p.κ * t))⁻¹ := by rw [inv_div, div_eq_mul_inv]
    have h2 : (p.N k ^ (p.κ * t))⁻¹ ≤ p.N k ^ (-(3 * m)) := by
      rw [← Real.rpow_neg hN.le]
      exact Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
    calc q ≤ p.K k * (p.N k ^ (p.κ * t))⁻¹ := h1
      _ ≤ p.K k * p.N k ^ (-(3 * m)) := mul_le_mul_of_nonneg_left h2 hK0.le
  have hHsq : H ^ 2 = p.N k ^ (m / 5) := by
    rw [hH, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  have hbase' : 2 * (6 * p.K k ^ 2 * q) * H ^ 2 ≤ p.N k ^ (-m) := by
    calc
      _ ≤ 2 * (6 * p.K k ^ 2 * (p.K k * p.N k ^ (-(3 * m)))) * H ^ 2 := by gcongr
      _ = 12 * p.K k ^ 3 * p.N k ^ (-(3 * m) + m / 5) := by
        rw [Real.rpow_add hN, ← hHsq]
        ring
      _ ≤ _ := hbase.le
  have hsignal' : 216 * H * (2 * p.K k) ^ 2 * (6 * p.K k ^ 2 * q) ≤
      p.N k ^ (-(r + v)) / 2 := by
    have hHpow : H = p.N k ^ (m / 10) := hH
    calc
      _ ≤ 216 * H * (2 * p.K k) ^ 2 * (6 * p.K k ^ 2 * (p.K k * p.N k ^ (-(3 * m)))) := by
        gcongr
      _ = 5184 * p.K k ^ 5 * p.N k ^ (-(3 * m) + m / 10) := by
        rw [Real.rpow_add hN, hHpow]
        ring
      _ ≤ _ := by linarith [hsignal]
  have hdiam : 6 * p.K k ^ 2 * q ≤ 1 := by
    have hξ1 : p.N k ^ (-m) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
    have hH1 : 1 ≤ H ^ 2 := one_le_pow₀ (Real.one_le_rpow (hN1 k) (by positivity))
    have hD0 : 0 ≤ 6 * p.K k ^ 2 * q := by positivity
    nlinarith
  exact ⟨hbase', hsignal', hdiam⟩

/-- The required output of original-history pruning and palette pooling. -/
def Pooling (p : Parent α) (r v m : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ᶠ k in atTop, ∀ f : p.ListFrame k r v m ε,
    ∃ law : Measure (α × ℝ), law ≤ f.law ∧
      ENNReal.ofReal (p.N k ^ (-ε) / 2) ≤ law univ ∧
      ∃ terminal : Finset ((Fin 2 → ℤ) × ℤ),
        (terminal.card : ℝ) * (p.N k ^ (-m)) ^ 2 ≤
          216 * p.K k * p.N k ^ (2 * ε) * p.N k ^ (p.d * v) ∧
        ∀ᵐ ω ∂law,
          (scalarCell (f.coeff ω.1) ω.2 (p.N k ^ (-m)),
            ⌊scalarX (f.coeff ω.1) ω.2 / p.N k ^ (-r - v)⌋) ∈ terminal

/-- Uniform original preparation at the deep confinement depth produces one pooled
terminal list, with the original palette and full parent factor. -/
theorem Valid.pooling (h : p.Valid) {r v m : ℝ} (hexp : p.ListExponents r v m)
    (hconf : p.DeepConfinement r v m) : Pooling p r v m := by
  obtain ⟨hr, hv, _hvr, hm, _hℓm, _hU⟩ := hexp
  obtain ⟨t, ε₀, hrt, htU, hε₀, hconf⟩ := hconf
  have hm0 : 0 < m := by linarith
  have hκ := h.rate_pos
  have h3m : 0 < 3 * m / p.κ := by positivity
  have hrt' : r < t := by linarith
  have hrU : r ≤ p.U := by linarith
  have ht0 : 0 < t := by linarith
  let R := 2 + r + m + r⁻¹ + m⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr hm0]
  have hR0 : 0 < R := by linarith
  have hRr : R⁻¹ ≤ r := by
    apply (inv_le_comm₀ hR0 hr).mpr
    dsimp [R]
    linarith [inv_pos.mpr hm0]
  have hRm : R⁻¹ ≤ m := by
    apply (inv_le_comm₀ hR0 hm0).mpr
    dsimp [R]
    linarith [inv_pos.mpr hr]
  have hmR : m ≤ R := by dsimp [R]; linarith [inv_pos.mpr hr, inv_pos.mpr hm0]
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεε₀
  filter_upwards [h.prepared R hR, h.nested R hR,
    h.eventually_deep_margins hr hm hv hrt htU, h.eventually_parent_geometry hr hrU,
    hconf ε hε hεε₀] with k prep nest margins parent conf
  intro f
  have ar := prep r hRr hrU
  have ad := prep t (hRr.trans hrt'.le) htU
  have hn := nest r t hRr hrt' htU
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [h.scale k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hνpar : p.ν k (p.A k r f.parent) ≠ 0 := by
    have hf := parent.prior_lower f.parent
    have hpositive : 0 < ENNReal.ofReal
        ((p.N k ^ (-r)) ^ p.d * (((2 : ℝ) ^ p.T k r)⁻¹) ^ 2 *
          p.N k ^ (-p.ℓ * r) / p.K k) := by
      apply ENNReal.ofReal_pos.mpr
      have hK0 : 0 < p.K k := by linarith
      positivity
    exact (hpositive.trans_le hf).ne'
  obtain ⟨grp, bad, hgrp, hbad, hbadmass, hsig⟩ := conf f
  exact f.pooled_of_setup h ar.2.2.2.1 (fun i => (ar.2.2.1 i).2.2) hνpar ad.2.2.1
    ad.2.2.2.1
    (by
      intro i a
      have hh := ad.2.2.2.2.2.2 i m a hRm hmR
      simpa only [zpow_neg, zpow_natCast] using hh)
    ad.2.2.2.2.2.1 hn (D := 6 * p.K k ^ 2 * ((2 : ℝ) ^ p.T k t)⁻¹) (by positivity)
    (fun i l hl l' hl' τ hτ τ' hτ' e => ad.base_diameter hN1 hK h.transverse_pos ht0.le i
      ((ad.2.2.1 i).2.2 hl) ((ad.2.2.1 i).2.2 hl') hτ hτ' e)
    margins.base margins.signal margins.diameter_le_one grp hgrp bad hbad hbadmass hsig

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
