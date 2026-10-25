-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.VelocityPalette, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/VelocityPalette.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/VelocityPalette.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/VelocityPalette.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/VelocityPalette.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames
import Submission.Obl.k4_finite_row_graph_assembly.Projection
import Submission.Obl.k4_matching_cofinal_palette_selection.Continuous
import Submission.Obl.k4_matching_palette_likelihood

/-! Velocity palettes under one fixed probability law. The finite-code and
entropy estimates are imported from the accepted matching library. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable def velocityPalette (a : ℝ) (z : Fin 2 → ℝ) : ℤ × ℤ :=
  (⌊z 0 / a⌋, ⌊z 1 / a⌋)

theorem measurable_velocityPalette {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ) {V : Ω → Fin 2 → ℝ} (hV : Measurable V) :
    Measurable (fun x => velocityPalette a (V x)) :=
  (((measurable_pi_apply 0).comp hV).div_const a).floor.prodMk
    (((measurable_pi_apply 1).comp hV).div_const a).floor

/-- The whole physical velocity range bounds the palette independently of
the number of packets, world labels, or semialgebraic format. -/
theorem velocityPalette_card {Ω : Type*} (S : Set Ω) (hSne : S.Nonempty)
    (V : Ω → Fin 2 → ℝ) {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a)
    (hV : ∀ x ∈ S, ∀ j, |V x j| ≤ K) :
    ∃ M : ℕ, 1 ≤ M ∧
      ((fun x => velocityPalette a (V x)) '' S).Finite ∧
      ((fun x => velocityPalette a (V x)) '' S).ncard ≤ M ∧
      Real.log (M : ℝ) ≤ 2 * Real.log (4 * K / a + 6) := by
  classical
  let Z : Ω → ℤ × ℤ := fun x => velocityPalette a (V x)
  let box := Finset.Icc ⌊-K / a⌋ ⌊K / a⌋ ×ˢ Finset.Icc ⌊-K / a⌋ ⌊K / a⌋
  have hsub : Z '' S ⊆ (box : Set (ℤ × ℤ)) := by
    rintro _ ⟨x, hx, rfl⟩
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr
    · exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right (abs_le.mp (hV x hx 0)).1 ha.le),
        Int.floor_le_floor (div_le_div_of_nonneg_right (abs_le.mp (hV x hx 0)).2 ha.le)⟩
    · exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right (abs_le.mp (hV x hx 1)).1 ha.le),
        Int.floor_le_floor (div_le_div_of_nonneg_right (abs_le.mp (hV x hx 1)).2 ha.le)⟩
  have hfin : (Z '' S).Finite := box.finite_toSet.subset hsub
  let P := hfin.toFinset
  have hdiam : ∀ p ∈ P, ∀ p' ∈ P,
      |(p.1 : ℝ) - p'.1| ≤ 2 * K / a + 2 ∧
      |(p.2 : ℝ) - p'.2| ≤ 2 * K / a + 2 := by
    intro p hp p' hp'
    obtain ⟨x, hx, rfl⟩ := hfin.mem_toFinset.mp hp
    obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.mp hp'
    have hcoord (j : Fin 2) :
        |(⌊V x j / a⌋ : ℝ) - ⌊V y j / a⌋| ≤ 2 * K / a + 2 := by
      have hbound : |V x j / a - V y j / a| ≤ 2 * K / a := by
        rw [← sub_div, abs_div, abs_of_pos ha]
        exact div_le_div_of_nonneg_right
          ((abs_sub _ _).trans (by linarith [hV x hx j, hV y hy j])) ha.le
      exact (Submission.Obl.k4_finite_row_graph_assembly.abs_sub_floor_le _ _).trans
        (by linarith)
    exact ⟨hcoord 0, hcoord 1⟩
  have hcard := Submission.Obl.k4_finite_row_graph_assembly.card_pair_grid_of_diameter P
    (R := 2 * K / a + 2) (by positivity) hdiam
  have hcard' : (P.card : ℝ) ≤ (4 * K / a + 6) ^ 2 := by
    convert hcard using 1 <;> ring
  have hpos : 0 < P.card := Finset.card_pos.mpr (by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨Z x, hfin.mem_toFinset.mpr ⟨x, hx, rfl⟩⟩)
  refine ⟨P.card, by omega, hfin, ?_, ?_⟩
  · exact le_of_eq (Set.ncard_eq_toFinset_card _ hfin)
  · calc
      Real.log (P.card : ℝ) ≤ Real.log ((4 * K / a + 6) ^ 2) :=
        Real.log_le_log (by exact_mod_cast hpos) hcard'
      _ = 2 * Real.log (4 * K / a + 6) := by rw [Real.log_pow]; norm_num

theorem velocityPalette_log_budget {N σ u : ℝ} (hN : 1 ≤ N)
    (hσ : 0 ≤ σ) (hu : 0 ≤ u) :
    2 * Real.log (4 * N ^ σ / N ^ (-u) + 6) ≤
      2 * Real.log 10 + 2 * (σ + u) * Real.log N := by
  have hNpos : 0 < N := by linarith
  have hpow : N ^ σ / N ^ (-u) = N ^ (σ + u) := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  rw [mul_div_assoc, hpow]
  have hge : 1 ≤ N ^ (σ + u) := Real.one_le_rpow hN (by positivity)
  have hle : 4 * N ^ (σ + u) + 6 ≤ 10 * N ^ (σ + u) := by linarith
  have hlog := Real.log_le_log (show 0 < 4 * N ^ (σ + u) + 6 by positivity) hle
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hNpos] at hlog
  linarith

/-- One fixed probability law controls the number of large palette-likelihood
windows. Later packet restrictions do not change the law in this estimate. -/
theorem continuous_velocity_bad_steps_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (hμS : μ Sᶜ = 0)
    (F : ℕ → Ω → ℕ) (V : Ω → Fin 2 → ℝ) (q C : ℕ) (hC : 1 ≤ C)
    (hFm : ∀ k, k ≤ q → Measurable (F k))
    (hFfin : ∀ k, k ≤ q → (F k '' S).Finite)
    (hnest : ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S, ∀ y ∈ S,
      F b x = F b y → F a x = F a y)
    (hVm : Measurable V) (A : Finset ℕ)
    (hA : ∀ k ∈ A, k < q ∧ k + C ≤ q)
    (N σ u τ α : ℝ) (hN : 1 ≤ N) (hσ : 0 ≤ σ) (hu : 0 ≤ u)
    (hτ : 0 ≤ τ) (hα : 0 ≤ α)
    (hV : ∀ x ∈ S, ∀ j, |V x j| ≤ N ^ σ) :
    (((A.filter fun k => ENNReal.ofReal α <
      Submission.Obl.k4_matching_cofinal_palette_selection.badMass μ S F
        (fun x => velocityPalette (N ^ (-u)) (V x)) C k (N ^ τ)).card : ℝ) *
      (τ * Real.log N * α)) ≤
        (C : ℝ) * (2 * Real.log 10 + 2 * (σ + u) * Real.log N) + (q : ℝ) := by
  classical
  have hSne : S.Nonempty := nonempty_of_measure_ne_zero (by
    have hmass : μ S = 1 := by
      simpa [hμS] using measure_add_measure_compl (μ := μ) hS
    rw [hmass]
    exact one_ne_zero)
  obtain ⟨M, hM, hfin, hcard, hlog⟩ := velocityPalette_card S hSne V
    (K := N ^ σ) (by positivity) (show 0 < N ^ (-u) by positivity) hV
  have h := Submission.Obl.k4_matching_cofinal_palette_selection.continuous_pair_bad_steps_bound
    Submission.k4_matching_palette_likelihood μ S hS hμS F
    (fun x => velocityPalette (N ^ (-u)) (V x)) q 0 C M (by omega) hC hM
    hFm hFfin hnest (measurable_velocityPalette _ hVm)
    (fun x hx => ⟨hfin.subset (Set.image_mono (fun y hy => hy.1)),
      (Set.ncard_le_ncard (Set.image_mono (fun y hy => hy.1)) hfin).trans hcard⟩)
    A (fun k hk => ⟨(hA k hk).1, Nat.zero_le _, (hA k hk).2⟩)
    N τ α hN hτ hα
  have hbudget := mul_le_mul_of_nonneg_left
    (hlog.trans (velocityPalette_log_budget hN hσ hu)) (Nat.cast_nonneg C)
  linarith

/-- If there are more potential windows than the likelihood budget allows to
be bad, one window loses at most the prescribed probability mass. -/
theorem exists_good_velocity_window
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (hμS : μ Sᶜ = 0)
    (F : ℕ → Ω → ℕ) (V : Ω → Fin 2 → ℝ) (q C : ℕ) (hC : 1 ≤ C)
    (hFm : ∀ k, k ≤ q → Measurable (F k))
    (hFfin : ∀ k, k ≤ q → (F k '' S).Finite)
    (hnest : ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S, ∀ y ∈ S,
      F b x = F b y → F a x = F a y)
    (hVm : Measurable V) (A : Finset ℕ)
    (hA : ∀ k ∈ A, k < q ∧ k + C ≤ q)
    (N σ u τ α : ℝ) (hN : 1 ≤ N) (hσ : 0 ≤ σ) (hu : 0 ≤ u)
    (hτ : 0 ≤ τ) (hα : 0 ≤ α)
    (hV : ∀ x ∈ S, ∀ j, |V x j| ≤ N ^ σ)
    (hbudget : (C : ℝ) * (2 * Real.log 10 + 2 * (σ + u) * Real.log N) + (q : ℝ) <
      (A.card : ℝ) * (τ * Real.log N * α)) :
    ∃ k ∈ A, Submission.Obl.k4_matching_cofinal_palette_selection.badMass μ S F
      (fun x => velocityPalette (N ^ (-u)) (V x)) C k (N ^ τ) ≤ ENNReal.ofReal α := by
  classical
  by_contra hnone
  have hall : A.filter (fun k => ENNReal.ofReal α <
      Submission.Obl.k4_matching_cofinal_palette_selection.badMass μ S F
        (fun x => velocityPalette (N ^ (-u)) (V x)) C k (N ^ τ)) = A := by
    apply Finset.filter_eq_self.mpr
    intro k hk
    exact lt_of_not_ge (fun hgood => hnone ⟨k, hk, hgood⟩)
  have h := continuous_velocity_bad_steps_bound μ S hS hμS F V q C hC hFm hFfin
    hnest hVm A hA N σ u τ α hN hσ hu hτ hα hV
  rw [hall] at h
  linarith

/-- The grid size and all velocity exponents can be fixed before the problem.
Only the eventual scale cutoff depends on its growth sequence. -/
theorem eventually_velocity_window_budget (N : ℕ → ℝ)
    (hN : Filter.Tendsto N Filter.atTop Filter.atTop) (A : Finset ℕ) (q C : ℕ)
    (σ u τ α : ℝ)
    (hgap : 2 * (C : ℝ) * (σ + u) < (A.card : ℝ) * (τ * α)) :
    ∀ᶠ k in Filter.atTop,
      (C : ℝ) * (2 * Real.log 10 + 2 * (σ + u) * Real.log (N k)) + (q : ℝ) <
        (A.card : ℝ) * (τ * Real.log (N k) * α) := by
  let gap : ℝ := (A.card : ℝ) * (τ * α) - 2 * (C : ℝ) * (σ + u)
  have hgap0 : 0 < gap := by dsimp [gap]; linarith
  have hlog := (Real.tendsto_log_atTop.comp hN).eventually
    (Filter.eventually_gt_atTop ((2 * (C : ℝ) * Real.log 10 + (q : ℝ)) / gap))
  filter_upwards [hlog] with k hk
  have hmul := (div_lt_iff₀ hgap0).mp hk
  dsimp [gap] at hmul
  nlinarith

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
