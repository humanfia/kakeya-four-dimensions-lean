-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/SubpowerWeakDiscoveryRepair.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.WeakDiscoveryTools
import Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair

/-! A requested power loss in the narrow atlas mass is paid by the output slack.
This variant avoids imposing a fixed mass fraction on geometric strip selection.
The refinement and all original path data are the same as the fixed-mass repair.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.SubpowerWeakDiscoveryRepair

open MeasureTheory WeakWidthBridge UniformGridRefinement WeakUniformDiscoveryRepair
open Submission.Obl.k4_quadratic_finite_greedy_cover

/-- A middle-level alternative allowing an arbitrarily small power loss in mass.
Only its original chart events and their actual lists are needed here. -/
def NarrowAlternative (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure Ln)
    (E : Fin W → Set Ev) (B : Fin W → ℝ) (m Mi Di : ℕ)
    (s r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ α u₀ : ℝ) (H : Fin W → Set Ev) : Prop :=
  ∃ (i : ℕ) (β : ℝ)
    (aux : Fin W → Fin (2 ^ T i) → Set Ln → Set Ev → Prop → Prop),
    i < m ∧ s i ≤ 1 / 2 ∧ u₀ ≤ β ∧
    (∀ w jt A F known, aux w jt A F known → known) ∧
    originalMassAtlas Nk L W ω ν E B Mi Di α (r i) (T i)
      (fun Q => |Q.det| * (4 : ℝ) ^ T i ≤ Nk ^ (-(nw i + β * L))) aux
      (ENNReal.ofReal ((κ * Nk ^ α)⁻¹ / 8)) (fun w F => ((ν w).prod volume) (F ∩ H w))

/-- Weak discovery at one uniform grid. The middle alternative is not required
to have determinant gain equal to the quadratic candidate's gain. Output format
precedes both the requested output slack and the middle-atlas slack. -/
def WeakDiscoveryAt (d₁ κ₁ S η ρ : ℝ) (m : ℕ) (gain δ₀ u₀ : ℝ) : Prop :=
  ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - d₁ * r| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mi Di : ℕ, ∀ τ : ℝ, 0 < τ → ∀ α : ℝ, 0 < α → α ≤ 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    ∀ r T nw κ C lev par γ j c u Q R A F lst,
      path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m (uniformGrid m) δ₀ Mp Dp σ
        r T nw κ C lev par γ j c u Q R A F lst →
      ∀ H : Fin (W k) → Set Ev,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ {p | ∃ b : Fin C, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b}) →
      ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w) →
      width (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mi Di τ ∨
      candidate (N k) L (W k) (ν k) (B k) Mi d₁ ρ gain τ r T C lev γ j A H ∨
      NarrowAlternative (N k) L (W k) (ω k) (ν k) (E k) (B k) m Mi Di
        (uniformGrid m) r T nw κ α u₀ H

/-- A weak uniform discovery engine allowing a requested power loss in narrow mass. This is an explicit
geometric hypothesis, not an assertion of an unaccepted theorem. -/
def WeakUniformDiscovery : Prop :=
  O106Repair.mk → ∀ d₁ κ₁ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∃ (m : ℕ) (gain δ₀ u₀ : ℝ), 0 < m ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧
      0 < δ₀ ∧ δ₀ ≤ ρ * gain ∧ 0 < u₀ ∧ WeakDiscoveryAt d₁ κ₁ S η ρ m gain δ₀ u₀

theorem kappa_power_mass_floor {Nk κ σ α τ : ℝ}
    (hN : 1 ≤ Nk) (hκ : 0 < κ) (hκN : κ ≤ Nk ^ σ)
    (hστ : σ ≤ τ / 4) (hατ : α ≤ τ / 4) (hlarge : 8 ≤ Nk ^ (τ / 2)) :
    Nk ^ (-τ) ≤ (κ * Nk ^ α)⁻¹ / 8 := by
  have hNpos : 0 < Nk := zero_lt_one.trans_le hN
  have hκpower : κ * Nk ^ α ≤ Nk ^ (σ + α) := by
    rw [Real.rpow_add hNpos]
    exact mul_le_mul_of_nonneg_right hκN (Real.rpow_pos_of_pos hNpos _).le
  exact eight_kappa_mass_floor hN (mul_pos hκ (Real.rpow_pos_of_pos hNpos _))
    hκpower (by linarith) hlarge

theorem kappa_power_mass_identity (Nk κ α : ℝ) (hN : 0 ≤ Nk) :
    (κ * Nk ^ α)⁻¹ / 8 = Nk ^ (-α) * (κ⁻¹ / 8) := by
  simp only [mul_inv_rev, Real.rpow_neg hN, div_eq_mul_inv, mul_assoc]

/-- Exact repaired discovery from weak uniform discovery. The caller refines
the grid before any sample, so fine-grid control is not a new geometric input. -/
theorem repaired_discovery_of_weak (hWeak : WeakUniformDiscovery) : O106Repair.O116' := by
  intro hMK d₁ κ₁ S η ρ θ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ hθ
  obtain ⟨m, gain, δold, u₀, hm, hgain, hgain8, hδold, hδρ, hu₀, hweak⟩ :=
    hWeak hMK d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  obtain ⟨q, hq, hmesh⟩ := exists_fine_uniform_refinement hm (mul_pos hθ hgain)
  let δnew := min δold (θ * gain)
  let gainW := min u₀ (min (θ * gain) (gain / 8))
  have hδnew : 0 < δnew := lt_min hδold (mul_pos hθ hgain)
  have hδnewOld : δnew ≤ δold := min_le_left _ _
  have hgainW : 0 < gainW := lt_min hu₀ (lt_min (mul_pos hθ hgain) (by positivity))
  have hgainWθ : gainW ≤ θ * gain := (min_le_right _ _).trans (min_le_left _ _)
  have hgainWu : gainW ≤ u₀ := min_le_left _ _
  have hgainWgain : gainW ≤ gain := by
    have hh : gainW ≤ gain / 8 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hgainW8 : gainW ≤ 1 / 8 := hgainWgain.trans hgain8
  have hδold8 : δold ≤ 1 / 8 := by
    have hρ1 : ρ < 1 := by linarith
    nlinarith
  have hcompat : ∀ i, i < m →
      uniformGrid (m * q) (coarseIndex q i) = uniformGrid m i := by
    intro i hi
    simpa only [uniformGrid, coarseIndex, uniformIndex] using uniformIndex_coordinate q hq ⟨i, hi⟩
  refine ⟨m * q, uniformGrid (m * q), gain, gainW, δnew,
    uniform_grid_spec (Nat.mul_pos hm hq), hgain, hgain8, hgainW, hgainWθ,
    hδnew, hδnewOld.trans hδρ, min_le_right _ _, ?_, ?_, ?_⟩
  · simpa only [uniformGrid, Nat.cast_zero, zero_add] using hmesh
  · intro i hi
    rw [uniform_grid_gap]
    exact hmesh
  · intro N K L d W ω ν E P B f g G hprob hprofile Mp Dp
    have hL : 0 < L := hprob.2.2.2.1
    have hprofileOld : ∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - d₁ * r| ≤ δold * L := by
      intro r hr hrL
      exact (hprofile r hr hrL).trans (mul_le_mul_of_nonneg_right hδnewOld hL.le)
    obtain ⟨Mi, Di, hstage⟩ := hweak N K L d W ω ν E P B f g G hprob hprofileOld Mp Dp
    refine ⟨Mi, Di, ?_⟩
    intro τ hτ
    let α := min (τ / 4) 1
    have hα : 0 < α := lt_min (by positivity) (by norm_num)
    have hαquarter : α ≤ τ / 4 := min_le_left _ _
    have hατ : α ≤ τ := by linarith
    have hα1 : α ≤ 1 := min_le_right _ _
    obtain ⟨σ, hσ, k₀, hlate⟩ := hstage τ hτ α hα hα1
    have hev : ∀ᶠ k in Filter.atTop, 8 ≤ N k ^ (τ / 2) :=
      ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp hprob.2.1).eventually
        (Filter.eventually_ge_atTop 8)
    obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp hev
    refine ⟨min σ (τ / 4), lt_min hσ (by positivity), max k₀ k₁, ?_⟩
    intro k hk r T nw κ C lev par γ j c u Q R A F lst hp H hH hmass
    have hN : 1 ≤ N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hprob.1 k)
    have hB : ∀ w, 0 ≤ B k w := fun w =>
      ((prob_basic N K L d S η W ω ν E P B f g G hprob).2.2.2.2.2.2.1 k w).le
    obtain ⟨parC, hpC⟩ := UniformPathRestriction.path_restrict_uniform hm hq hcompat hp
    have hpWide := UniformPathRestriction.path_tolerance_mono hN hL.le hδnewOld hpC
    have hpOld := path_slack_mono (σ' := σ) (hN := hN)
      (hσ := min_le_left σ (τ / 4)) (hp := hpWide)
    let Cc := GridPacketRestriction.count lev m q
    let idx : Fin Cc → Fin C := GridPacketRestriction.index
    let lv : Fin Cc → ℕ := GridPacketRestriction.level
    let ls : ℕ → Fin (W k) → Ob → Finset (Fin Cc) := fun i w o =>
      GridPacketRestriction.pullList (lst (coarseIndex q i) w o) i
    have hcover := UniformPathRestriction.top_cover_restrict_uniform (m := m) (k := q)
      hm hq (fun w => (hH w).2)
    have hHc : ∀ w, MeasurableSet (H w) ∧ H w ⊆
        {p | ∃ b : Fin Cc, lv b = m - 1 ∧ (γ ∘ idx) b = w ∧ p ∈ (F ∘ idx) b} :=
      fun w => ⟨(hH w).1, hcover w⟩
    have hout := hlate k ((le_max_left _ _).trans hk)
      (r ∘ coarseIndex q) (T ∘ coarseIndex q) (nw ∘ coarseIndex q) κ Cc lv parC
      (γ ∘ idx) (j ∘ idx) (c ∘ idx) (u ∘ idx) (Q ∘ idx) (R ∘ idx) (A ∘ idx) (F ∘ idx) ls
      hpOld H hHc hmass
    rcases hout with hw | hc | hnarrow
    · exact Or.inl (UniformPathRestriction.width_lift_uniform hq
        (width_weaken_gain hN hL.le hB hgainWgain hw))
    · exact Or.inr (UniformPathRestriction.candidate_lift_uniform (m := m) (k := q) hc)
    · obtain ⟨i, β, aux, hi, hsi, hβ, haux, ha⟩ := hnarrow
      have hfloor := kappa_power_mass_floor hN (zero_lt_one.trans_le hp.1)
        hp.2.1 (min_le_right σ (τ / 4)) hαquarter
        (hk₁ k ((le_max_right _ _).trans hk))
      have hwidth := width_of_original_mass_atlas hN hL.le hατ hB hi
        (middle_node_width_margin hL.le hsi ((hpWide.2.2.2.2.1 i hi).1) hδold8 hgainW8)
        (hgainWu.trans hβ) haux hfloor ha
      exact Or.inl (UniformPathRestriction.width_lift_uniform hq hwidth)

/-- Literal repaired frozen interface, ready for the existing parent glue. -/
theorem frozen_repaired_discovery_of_weak (hWeak : WeakUniformDiscovery) :
    O106Repair.frozen116 := repaired_discovery_of_weak hWeak

end Submission.Obl.k4_isotropic_path_improvement.Repair.SubpowerWeakDiscoveryRepair
