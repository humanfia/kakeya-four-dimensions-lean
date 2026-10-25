/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformResidualRange.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformResidualRange.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformResidualSlopes
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformLoss

/-! Residual concentration at every sufficiently small original resolution. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

universe u


open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open WangZahlLot.Obl.wz_slab_local_linearity

theorem residual_slope_budgets_eventually_below (N K : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a d ε : ℝ} (ha : 0 < a) (hd : d < 1) (hε : 0 < ε) (j : ℝ) :
    ∀ᶠ k in atTop, ∀ p : ℝ, 0 < p → p ≤ N k ^ (-a) →
      let τ := N k ^ (-ε / 4)
      let η := N k ^ (-ε)
      let γ := (1 - d) / 4
      τ * K k + (p ^ j * τ) * (K k * p ^ (-j)) ≤ (K k)⁻¹ / 2 ∧
      (3 * (K k * ((2 * K k) / p) ^ d)) *
        (((η / τ) / (p ^ j * τ) * (K k * p ^ (j + d))) * K k +
          (2 * (p + 2 * (K k * p)) / (p ^ γ)) * K k ^ 2) < ((K k)⁻¹ / 2) ^ 2 := by
  have hK0 : ∀ k, 0 ≤ K k := fun k => zero_le_one.trans (hK k)
  have hdecay₀ := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 2
    (a := ε / 4) (b := 1) (C := 4) (by positivity) (by norm_num) (by norm_num)
  have hdecay₁ := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 6
    (a := ε / 2) (b := 1 / 8) (C := 6) (by positivity) (by norm_num) (by norm_num)
  have hrate : 0 < a * (1 - d - (1 - d) / 4) :=
    mul_pos ha (by linarith)
  have hdecay₂ := subpower_polynomial_decay_eventually N K hN hNt hK0 hsub 7
    (a := a * (1 - d - (1 - d) / 4)) (b := 1 / 8) (C := 36) hrate (by norm_num) (by norm_num)
  filter_upwards [hdecay₀, hdecay₁, hdecay₂] with k hsmall₀ hsmall₁ hsmall₂
  intro p hp hple
  dsimp only
  let τ := N k ^ (-ε / 4)
  let η := N k ^ (-ε)
  let γ := (1 - d) / 4
  have hNpos : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hNpos _
  have hη : 0 ≤ η := (Real.rpow_pos_of_pos hNpos _).le
  have hητ : η / τ ^ 2 = N k ^ (-ε / 2) := by
    dsimp [η, τ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_sub hNpos]
    congr 1
    ring
  have hpRate : p ^ (1 - d - γ) ≤ N k ^ (-(a * (1 - d - (1 - d) / 4))) := by
    calc
      _ ≤ (N k ^ (-a)) ^ (1 - d - γ) :=
        Real.rpow_le_rpow hp.le hple (by dsimp [γ]; linarith)
      _ = _ := by
        rw [← Real.rpow_mul hNpos.le]
        congr 1
        dsimp [γ]
        ring
  have hτsmall : 4 * K k ^ 2 * τ < 1 := by simpa only [τ, neg_div] using hsmall₀
  constructor
  · calc
      τ * K k + (p ^ j * τ) * (K k * p ^ (-j)) ≤ 2 * K k * τ :=
        scalar_slope_pruning_cost hp hKpos.le hτ.le le_rfl le_rfl
      _ ≤ (K k)⁻¹ / 2 := by
        rw [inv_eq_one_div, div_div]
        apply (le_div_iff₀ (by positivity : 0 < K k * 2)).mpr
        nlinarith only [hτsmall.le]
  · have hMsmall :
        (6 * K k ^ 4 * η / τ ^ 2 + 36 * K k ^ 5 * p ^ (1 - d - γ)) * K k ^ 2 < 1 / 4 := by
      calc
        _ = 6 * K k ^ 6 * (η / τ ^ 2) + 36 * K k ^ 7 * p ^ (1 - d - γ) := by ring
        _ ≤ 6 * K k ^ 6 * N k ^ (-ε / 2) +
            36 * K k ^ 7 * N k ^ (-(a * (1 - d - (1 - d) / 4))) := by
          rw [hητ]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpRate
            (show 0 ≤ 36 * K k ^ 7 by positivity))
        _ < 1 / 4 := by
          have hsmall₁' : 6 * K k ^ 6 * N k ^ (-ε / 2) < 1 / 8 := by
            simpa only [neg_div] using hsmall₁
          linarith
    have hR : ((K k)⁻¹ / 2) ^ 2 * K k ^ 2 = 1 / 4 := by
      field_simp
      norm_num
    have hbound : 6 * K k ^ 4 * η / τ ^ 2 + 36 * K k ^ 5 * p ^ (1 - d - γ) < ((K k)⁻¹ / 2) ^ 2 := by
      apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hKpos)).mp
      simpa only [mul_comm] using hMsmall.trans_eq hR.symm
    exact (scalar_slope_collision_cost hp (hK k) hτ hη hd.le).trans_lt hbound


def OriginalScalarResidualAt {d j : ℝ} (Λ ι : Type*)
    [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K p duration : ℝ) : Prop :=
  ∀ (ν : Measure Λ) [IsFiniteMeasure ν] (E : Set (Λ × ℝ)) (A : Set Λ)
    (F : ℝ × Λ → ℝ) (b slope : Λ → ℝ) (code : Λ → ι) (J : Finset ι) (S : ℝ → Set ℝ),
    MeasurableSet E → E ⊆ A ×ˢ Icc (0 : ℝ) 1 → Measurable F → Measurable slope → Measurable code →
    ν.real univ ≤ K → (K)⁻¹ ≤ (ν.prod volume).real E →
    (J.card : ℝ) ≤ K * p ^ (-j) →
    (∀ l t, (l, t) ∈ E → code l ∈ J) →
    (∀ t, IntervalAD p d (K) (S t)) →
    (∀ l t, (l, t) ∈ E → F (t, l) ∈ S t ∩ Icc (-K) (K)) →
    (∀ l t, (l, t) ∈ E → |F (t, l) - (b l + slope l * t)| ≤ K * p) →
    (∀ l ∈ A, ∀ l' ∈ A, code l = code l' → |slope l - slope l'| ≤ K * p) →
    (∀ t c, c ∈ J → ∀ z : ℤ,
      ν.real {l | (l, t) ∈ E ∧ code l = c ∧ (⌊F (t, l) / p⌋ : ℤ) = z} ≤ K * p ^ (j + d)) →
    ∃ c : ℝ, duration < (ν.prod volume).real
      (E ∩ ({l | |slope l - c| ≤ p ^ ((1 - d) / 4) + K * p} ×ˢ univ))

theorem uniform_original_residual_slopes_below_all_labels {ι : Type*}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a d ε : ℝ} (ha : 0 < a) (hd0 : 0 ≤ d) (hd : d < 1) (hε : 0 < ε) (j : ℝ) :
    ∀ᶠ k in atTop, ∀ (Λ : Type u) [MeasurableSpace Λ], ∀ p : ℝ, 0 < p → p ≤ N k ^ (-a) →
      OriginalScalarResidualAt (d := d) (j := j) Λ ι (K k) p (N k ^ (-ε)) := by
  filter_upwards [residual_slope_budgets_eventually_below N K hN hNt hK hsub ha hd hε j]
    with k hbudgets
  intro Λ _ p hp hple
  have hk := hbudgets p hp hple
  dsimp only [OriginalScalarResidualAt] at ⊢
  dsimp only at hk
  intro ν _ E A F b slope code J S hE hEsub hF hslope hcode hν hmass hJ hcover hS hsupport hfit hspread hjoint
  let τ := N k ^ (-ε / 4)
  let η := N k ^ (-ε)
  let γ := (1 - d) / 4
  have hNpos : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hNpos _
  have hη : 0 ≤ η := (Real.rpow_pos_of_pos hNpos _).le
  have hp1 : p ≤ 1 := by
    exact hple.trans (by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le (hN k) (show -a ≤ 0 by linarith))
  have hpR : p ≤ 2 * K k := by linarith [hK k]
  have hm : 0 < p ^ j * τ := mul_pos (Real.rpow_pos_of_pos hp _) hτ
  have hC : 0 ≤ K k * p ^ (j + d) := mul_nonneg hKpos.le (Real.rpow_nonneg hp.le _)
  have hΔ : 0 < p ^ γ := Real.rpow_pos_of_pos hp _
  have hbudget : τ * ν.real univ + (p ^ j * τ) * (J.card : ℝ) ≤ (K k)⁻¹ / 2 := by
    apply le_trans ?_ hk.1
    gcongr
  have hgap : (3 * (K k * ((2 * K k) / p) ^ d)) *
      (((η / τ) / (p ^ j * τ) * (K k * p ^ (j + d))) * ν.real univ +
        (2 * (p + 2 * (K k * p)) / (p ^ γ)) * (ν.real univ) ^ 2) < ((K k)⁻¹ / 2) ^ 2 := by
    apply lt_of_le_of_lt ?_ hk.2
    have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
    gcongr
  apply exists_heavy_residual_slope_of_original_data ν hE hEsub hF b slope hslope hcode J hcover
    hp hpR hKpos.le hC hΔ hm hτ hη (mul_nonneg hKpos.le hp.le) (inv_pos.mpr hKpos) S hS
  · intro l t ht
    obtain ⟨hs, hlo, hhi⟩ := hsupport l t ht
    exact ⟨hs, hlo, by linarith⟩
  · exact hfit
  · exact hspread
  · exact hjoint
  · exact hmass
  · exact hbudget
  · exact hgap


theorem uniform_original_residual_slopes_below {Λ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a d ε : ℝ} (ha : 0 < a) (hd0 : 0 ≤ d) (hd : d < 1) (hε : 0 < ε) (j : ℝ) :
    ∀ᶠ k in atTop, ∀ p : ℝ, 0 < p → p ≤ N k ^ (-a) →
      OriginalScalarResidualAt (d := d) (j := j) Λ ι (K k) p (N k ^ (-ε)) := by
  filter_upwards [uniform_original_residual_slopes_below_all_labels (ι := ι)
    N K hN hNt hK hsub ha hd0 hd hε j] with k hk
  exact hk Λ


theorem uniform_subpower_original_residual_slopes_below_all_labels {ι : Type*}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a d : ℝ} (ha : 0 < a) (hd0 : 0 ≤ d) (hd : d < 1) (j : ℝ) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, ∀ (Λ : Type u) [MeasurableSpace Λ], ∀ p : ℝ, 0 < p → p ≤ N k ^ (-a) →
        OriginalScalarResidualAt (d := d) (j := j) Λ ι (K k) p (Q k)⁻¹ := by
  obtain ⟨ε, Q, _, _, hQeq, hQ, hQsub, hgood⟩ := exists_uniform_subpower_tolerance N hN
    (fun ε k => ∀ (Λ : Type u) [MeasurableSpace Λ], ∀ p : ℝ, 0 < p → p ≤ N k ^ (-a) →
      OriginalScalarResidualAt (d := d) (j := j) Λ ι (K k) p (N k ^ (-ε)))
    (fun ε hε => uniform_original_residual_slopes_below_all_labels (ι := ι) N K hN hNt hK hsub ha hd0 hd hε j)
  refine ⟨Q, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  have he : N k ^ (-ε k) = (Q k)⁻¹ := by rw [hQeq k, Real.rpow_neg (zero_le_one.trans (hN k))]
  simpa only [he] using hk


theorem uniform_subpower_original_residual_slopes_below {Λ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a d : ℝ} (ha : 0 < a) (hd0 : 0 ≤ d) (hd : d < 1) (j : ℝ) :
    ∃ Q : ℕ → ℝ, (∀ k, 1 ≤ Q k) ∧ SubpowerBound N Q ∧
      ∀ᶠ k in atTop, ∀ p : ℝ, 0 < p → p ≤ N k ^ (-a) →
        OriginalScalarResidualAt (d := d) (j := j) Λ ι (K k) p (Q k)⁻¹ := by
  obtain ⟨Q, hQ, hQsub, hgood⟩ := uniform_subpower_original_residual_slopes_below_all_labels
    (ι := ι) N K hN hNt hK hsub ha hd0 hd j
  refine ⟨Q, hQ, hQsub, ?_⟩
  filter_upwards [hgood] with k hk
  exact hk Λ

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
