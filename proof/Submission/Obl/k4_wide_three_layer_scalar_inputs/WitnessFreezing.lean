import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses
import Submission.Obl.k4_wide_three_layer_scalar_inputs.KeyOffsets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.KeyDomain
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CodeVelocity

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context

open Set MeasureTheory MvPolynomial
open Inherited.Native Inherited.Core
open Submission.Obl.k4_scalar_guarded_tangent_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] (W : Context α)

def physicalOffset (γ : W.Coarse) (h : Fin 3) (j : Fin (W.layers.np h)) : ℝ :=
  eval ![W.t₀, domY W.χ W.m W.q (W.key γ) 0 0]
    (W.layers.G h j - W.layers.G 0 (W.coarseIndex γ))

theorem fine_key_freezing (hN : 0 < W.cfg.N W.k) (hχ : 0 < W.χ) (hD : 0 < W.D)
    (hmD : W.m ≤ W.D) (hdrift : W.ζ + W.χ ≤ W.D / 4)
    (γ : W.Coarse) (h : Fin 3) (j : Fin (W.layers.np h)) (hj : W.fineValid γ h j) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |eval ![W.t₀ + W.q * τ, domY W.χ W.m W.q (W.key γ) τ y]
        (W.layers.G h j - W.layers.G 0 (W.coarseIndex γ)) - W.physicalOffset γ h j| ≤
          98304 * W.E * (W.q + W.m / W.D) := by
  have hq : 0 < W.q := slotLen_pos W.cfg.comparisonData W.k W.s
  have hm : 0 < W.m := mul_pos hq (Real.rpow_pos_of_pos hN _)
  have hu : 0 ≤ W.t₀ ∧ W.t₀ + W.q ≤ 1 :=
    slot_unit W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)
  obtain ⟨l, hl0, hlh, hk, hh⟩ := hj.2.2
  have hbins := W.datum.mem_bins hl0
  have hintercept : |W.cfg.b W.k l 1 - (W.layers.qp 0 (W.coarseIndex γ) 2 : ℝ) * W.D| ≤ W.D :=
    floor_center_error hD _ hbins.2.2.1
  have hfloor0 : |W.cfg.b W.k l 0 - (W.key γ 1 : ℝ) * W.χ| ≤ W.χ :=
    floor_center_error hχ _ (congrFun hk 1)
  have hvelocity : |W.cfg.b W.k l 4 + (W.key γ 1 : ℝ) * W.χ| ≤ W.ζ + W.χ := by
    calc _ = |(W.cfg.b W.k l 4 + W.cfg.b W.k l 0) -
          (W.cfg.b W.k l 0 - (W.key γ 1 : ℝ) * W.χ)| := by congr 1; ring
      _ ≤ _ := (abs_sub _ _).trans (add_le_add hh hfloor0)
  have hkey1 : W.layers.qp 0 (W.coarseIndex γ) 1 = W.key γ 1 :=
    hbins.2.1.symm.trans (congrFun hk 1)
  have htube := key_tube_of_label (q := W.q) hm hD hmD
    (show W.t₀ ∈ Icc (0 : ℝ) 1 from ⟨hu.1, by linarith [hu.2]⟩)
    hk hintercept hvelocity hdrift
  exact difference_freezes_on_enlarged_key
    (G := W.layers.G h j) (H := W.layers.G 0 (W.coarseIndex γ)) (W.datum.degree h j)
    (W.datum.degree 0 (W.coarseIndex γ)) hD hm hq
    (by dsimp [E, a]; positivity) hu (W.key γ)
    (by simpa only [hkey1] using hj.2.1)
    (fun τ _ y hy => htube τ y hy)

theorem fine_offset_bound (hN : 0 < W.cfg.N W.k)
    (γ : W.Coarse) (h : Fin 3) (j : Fin (W.layers.np h)) (hj : W.fineValid γ h j)
    {ah H : ℝ} (hah : ah = W.cfg.N W.k ^ (-(![W.s, W.s + W.u, W.s + W.v] h)))
    (haA : ah ≤ W.a) (hH : 2 * W.cfg.N W.k ^ W.ε + 1 ≤ H)
    (hfreeze : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |eval ![W.t₀ + W.q * τ, domY W.χ W.m W.q (W.key γ) τ y]
        (W.layers.G h j - W.layers.G 0 (W.coarseIndex γ)) - W.physicalOffset γ h j| ≤ ah) :
    |W.physicalOffset γ h j| ≤ H * W.a := by
  have hq : 0 < W.q := slotLen_pos W.cfg.comparisonData W.k W.s
  have hm : 0 < W.m := mul_pos hq (Real.rpow_pos_of_pos hN _)
  have hu : 0 ≤ W.t₀ ∧ W.t₀ + W.q ≤ 1 :=
    slot_unit W.cfg.comparisonData W.k W.s (W.cfg.j W.k W.s W.i)
  have ht : W.t₀ ∈ Icc (0 : ℝ) 1 := ⟨hu.1, by linarith [hu.2]⟩
  obtain ⟨l, hl0, hlh, hk, -⟩ := hj.2.2
  have heq := label_Y_eq (q := W.q) hm.ne' hk 0
  simp only [mul_zero, add_zero, zero_mul] at heq
  have hs := sliceY_mem (W.cfg.b W.k) W.m W.t₀ l
  have hys : sliceY (W.cfg.b W.k) W.m W.t₀ l ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hf := hfreeze 0 ⟨le_rfl, zero_le_one⟩ _ hys
  simp only [mul_zero, add_zero, ← heq, map_sub] at hf
  have hc : |W.cfg.b W.k l 2 + W.t₀ * W.cfg.b W.k l 5 -
      eval ![W.t₀, W.cfg.b W.k l 1 + W.t₀ * W.cfg.b W.k l 4]
        (W.layers.G 0 (W.coarseIndex γ))| ≤ W.cfg.N W.k ^ W.ε * W.a := W.datum.fit hl0 ht
  have hfi : |W.cfg.b W.k l 2 + W.t₀ * W.cfg.b W.k l 5 -
      eval ![W.t₀, W.cfg.b W.k l 1 + W.t₀ * W.cfg.b W.k l 4]
        (W.layers.G h j)| ≤ W.cfg.N W.k ^ W.ε * ah := by
    rw [hah]
    exact W.datum.fit hlh ht
  have hb := frozen_offset_bound hc hfi hf
  have ha0 : 0 ≤ W.a := (Real.rpow_pos_of_pos hN _).le
  have hP : 0 ≤ W.cfg.N W.k ^ W.ε := (Real.rpow_pos_of_pos hN _).le
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left haA hP,
    mul_le_mul_of_nonneg_right hH ha0])

/-- The frozen whole-key estimate applies at the original physical
incidences, before any chart replacement or normalization. -/
theorem fine_freezing_at_label (hχ : 0 < W.χ) (hm : 0 < W.m)
    (γ : W.Coarse) (h : Fin 3) (j : Fin (W.layers.np h)) {ah : ℝ}
    (hfreeze : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |eval ![W.t₀ + W.q * τ, domY W.χ W.m W.q (W.key γ) τ y]
        (W.layers.G h j - W.layers.G 0 (W.coarseIndex γ)) - W.physicalOffset γ h j| ≤ ah)
    {l : α} {t : ℝ} (hk : slotKey (W.cfg.b W.k) W.χ W.m W.t₀ l = W.key γ)
    (hh : |W.cfg.b W.k l 4 + W.cfg.b W.k l 0| ≤ W.ζ)
    (hsmall : W.q * (W.ζ + W.χ) ≤ W.m / 2) (ht : t ∈ Icc W.t₀ (W.t₀ + W.q)) :
    |eval ![t, W.cfg.b W.k l 1 + t * W.cfg.b W.k l 4] (W.layers.G h j) -
      eval ![t, W.cfg.b W.k l 1 + t * W.cfg.b W.k l 4] (W.layers.G 0 (W.coarseIndex γ)) -
        W.physicalOffset γ h j| ≤ ah := by
  obtain ⟨τ, hτ, y, hy, heqt, heqy⟩ := actual_point_in_key_domain (q := W.q) hχ hm
    (slotLen_pos W.cfg.comparisonData W.k W.s) hk hh hsmall ht
  have hf := hfreeze τ hτ y hy
  rw [← heqt, ← heqy, map_sub] at hf
  exact hf

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortWitnesses.Context
