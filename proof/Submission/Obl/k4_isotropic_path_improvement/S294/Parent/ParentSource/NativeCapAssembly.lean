-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativeCapAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativeCapAssembly.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativeCapAssembly.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCapAssembly.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativePacketCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.BaseCapChange
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path

/-! # Actual native packet caps in full old reference units -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory
open scoped ENNReal

/-- The actual old affine chart, without a new choice of frame. -/
noncomputable def nativeOldBaseFrame {W : ℕ} (p : Native.PathData W) (a : Fin p.C) :
    Submission.Lib.K4ChartLifting.Frame where
  t₀ := (p.j a : ℝ) / (2 : ℝ) ^ p.T (p.lev a)
  q := ((2 : ℝ) ^ p.T (p.lev a))⁻¹
  c := p.c a
  u := p.u a
  D := p.Q a

/-- A finer band of the OLD native signal inherits the actual fine
observation cap, in the same old reference units. -/
theorem original_native_signal_cap_in_old_packet_units
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk)
    (b : Fin p.C) {K a : ℝ} (hκK : p.κ ≤ K) (hB : 0 < B (p.γ b))
    (ha : 0 < a) (haδ : a ≤ δ Nk (p.r (p.lev b)))
    (ρ : Measure Event)
    (hρ : ρ ≤ ((ν (p.γ b)).prod volume).restrict (E (p.γ b)))
    (g : BaseObservation → ENNReal) (hg : Measurable g)
    (hlaw : (((ν (p.γ b)).prod volume).restrict (E (p.γ b))).map
      (obs (B (p.γ b)) a) = (volume.prod Measure.count).withDensity g)
    (M : ENNReal) (z : ℝ) (hF : ∀ᵐ q ∂ρ, q ∈ p.F b)
    (hy : ∀ᵐ q ∂ρ, ‖y q.1 q.2‖ ≤ K)
    (hband : ∀ᵐ q ∂ρ, |MvPolynomial.eval (x q.1 q.2) (p.R b) - z| ≤ K * a)
    (htypical : ∀ᵐ q ∂ρ, g (obs (B (p.γ b)) a q) ≤ M) :
    (ν (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹ •
      ρ.map (fun q => (nativeOldBaseFrame p b).obsBase (obs (B (p.γ b)) a q).1) ≤
      ((M * ENNReal.ofReal (64 * K ^ 2)) *
        ENNReal.ofReal (p.κ * Nk ^ f (p.r (p.lev b)))) • volume := by
  have hraw : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ p.r p.T p.nw p.κ
      p.C p.lev p.par p.γ p.j p.c p.u p.Q p.R p.A p.F p.lst := hp
  have hcap := path_packet_native_signal_cap hraw b hκK hB ha haδ ρ hρ g hg hlaw M z
    hF hy hband htypical
  have hD : (p.Q b).det ≠ 0 := (hp.2.2.2.2.2.2.2 b).2.2.1
  exact base_cap_in_old_packet_units ρ
    (fun q => (obs (B (p.γ b)) a q).1) (by unfold obs x; fun_prop)
    (nativeOldBaseFrame p b) (by change 0 < ((2 : ℝ) ^ p.T (p.lev b))⁻¹; positivity) hD hNk
    (lt_of_lt_of_le zero_lt_one hp.1) (f (p.r (p.lev b)))
    (ν (p.γ b) (p.A b)) (M * ENNReal.ofReal (64 * K ^ 2))
    (hp.assignment_mass_bounds hNk b).1 hcap

/-- A physical rectangle restricts the old native signal to a finer band
and its normalized base to a measurable set. Its original mass is bounded
in FULL old packet units, with the same fine source density ceiling. -/
theorem original_native_rectangle_mass_cap
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk)
    (b : Fin p.C) {K a : ℝ} (hκK : p.κ ≤ K) (hB : 0 < B (p.γ b))
    (ha : 0 < a) (haδ : a ≤ δ Nk (p.r (p.lev b)))
    (ρ : Measure Event)
    (hρ : ρ ≤ ((ν (p.γ b)).prod volume).restrict (E (p.γ b)))
    (g : BaseObservation → ENNReal) (hg : Measurable g)
    (hlaw : (((ν (p.γ b)).prod volume).restrict (E (p.γ b))).map
      (obs (B (p.γ b)) a) = (volume.prod Measure.count).withDensity g)
    (M : ENNReal) (z : ℝ) (hF : ∀ᵐ q ∂ρ, q ∈ p.F b)
    (hy : ∀ᵐ q ∂ρ, ‖y q.1 q.2‖ ≤ K)
    (hband : ∀ᵐ q ∂ρ, |MvPolynomial.eval (x q.1 q.2) (p.R b) - z| ≤ K * a)
    (htypical : ∀ᵐ q ∂ρ, g (obs (B (p.γ b)) a q) ≤ M)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U)
    (hbase : ∀ᵐ q ∂ρ,
      (nativeOldBaseFrame p b).obsBase (obs (B (p.γ b)) a q).1 ∈ U) :
    (ν (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹ * ρ Set.univ ≤
      ((M * ENNReal.ofReal (64 * K ^ 2)) *
        ENNReal.ofReal (p.κ * Nk ^ f (p.r (p.lev b)))) * volume U := by
  have hcap := original_native_signal_cap_in_old_packet_units hp hNk b hκK hB ha haδ
    ρ hρ g hg hlaw M z hF hy hband htypical
  have hmap : Measurable (fun q : Event =>
      (nativeOldBaseFrame p b).obsBase (obs (B (p.γ b)) a q).1) :=
    (nativeOldBaseFrame p b).measurable_obsBase.comp (by unfold obs x; fun_prop)
  have hmass : (ρ.map (fun q =>
      (nativeOldBaseFrame p b).obsBase (obs (B (p.γ b)) a q).1)) U = ρ Set.univ := by
    rw [Measure.map_apply hmap hU]
    apply measure_congr
    filter_upwards [hbase] with q hq
    exact propext (iff_true_intro hq)
  simpa only [Measure.smul_apply, smul_eq_mul, hmass] using hcap U

/-- An original fine native incidence submeasure, capped by its original
observation density, has a continuous base cap in a fixed old frame and
FULL old assignment units. No counted-set mass occurs in the denominator. -/
theorem original_native_cap_in_old_packet_units
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk)
    (a b : Fin p.C) {K : ℝ} (hκK : p.κ ≤ K) (hB : 0 < B (p.γ b))
    (ρ : Measure Event)
    (hρ : ρ ≤ ((ν (p.γ b)).prod volume).restrict (E (p.γ b)))
    (g : BaseObservation → ENNReal) (hg : Measurable g)
    (hlaw : (((ν (p.γ b)).prod volume).restrict (E (p.γ b))).map
      (obs (B (p.γ b)) (δ Nk (p.r (p.lev b)))) =
        (volume.prod Measure.count).withDensity g)
    (M : ENNReal) (hF : ∀ᵐ x ∂ρ, x ∈ p.F b)
    (hy : ∀ᵐ x ∂ρ, ‖y x.1 x.2‖ ≤ K)
    (htypical : ∀ᵐ x ∂ρ, g (obs (B (p.γ b)) (δ Nk (p.r (p.lev b))) x) ≤ M) :
    (ν (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))⁻¹ •
      ρ.map (fun x => (nativeOldBaseFrame p a).obsBase
        (obs (B (p.γ b)) (δ Nk (p.r (p.lev b))) x).1) ≤
      ((M * ENNReal.ofReal (64 * K ^ 2)) *
        ENNReal.ofReal (p.κ * Nk ^ f (p.r (p.lev a)))) • volume := by
  have hraw : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ p.r p.T p.nw p.κ
      p.C p.lev p.par p.γ p.j p.c p.u p.Q p.R p.A p.F p.lst := hp
  have hcap := path_packet_native_base_cap hraw b hκK hB ρ hρ g hg hlaw M hF hy htypical
  have hD : (p.Q a).det ≠ 0 := (hp.2.2.2.2.2.2.2 a).2.2.1
  exact base_cap_in_old_packet_units ρ
    (fun x => (obs (B (p.γ b)) (δ Nk (p.r (p.lev b))) x).1)
    (by unfold obs x; fun_prop) (nativeOldBaseFrame p a)
    (by change 0 < ((2 : ℝ) ^ p.T (p.lev a))⁻¹; positivity) hD
    hNk (lt_of_lt_of_le zero_lt_one hp.1) (f (p.r (p.lev a)))
    (ν (p.γ a) (p.A a)) (M * ENNReal.ofReal (64 * K ^ 2))
    (hp.assignment_mass_bounds hNk a).1 hcap

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
