-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceNativeBranches, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceNativeBranches.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceNativeBranches.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeBranches.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeBranches.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceNativeCenters
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.OriginalNativeBranches

/-! # Coded local branches for an actual original fine packet entry -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic k4_stable_native_signal_oscillation

noncomputable section

/-- The actual original fine packet, original density ceiling, value bin
and FULL original assignment floor produce a uniformly coded quarter-core
branch family, including its rational presentations and algebraic jets.
Both exponents precede all path, source and format data. -/
theorem source_original_native_quarter_branches (qexp : ℕ) :
    ∃ e R : ℕ, 4 ≤ e ∧ 1 ≤ R ∧
    ∀ {d : Native.ProblemData}, d.Valid →
      ∀ {k : ℕ} {p : Native.PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      ∀ (b : Fin p.C) (r' : ℝ), 0 ≤ r' → r' ≤ d.L →
      δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev b)) →
      ∀ K ε : ℝ, 2 ≤ K → 3 * p.κ ≤ K → 0 < ε → ε ≤ (K ^ 6)⁻¹ →
      δ (d.N k) (p.r (p.lev b)) * ε ≤ δ (d.N k) r' →
      ∀ (ρ : Measure Event), ρ ≤ d.μ k (p.γ b) → ∀ (M : ENNReal) (center : ℝ),
      (∀ᵐ z ∂ρ, z ∈ p.F b) →
      (∀ᵐ z ∂ρ, |eval (fun j => packetNativeCubePoint (d.N k) (d.B k) p b z j)
        (packetNativeCubeTest (d.N k) (d.B k) p b) - center| ≤ ε) →
      (∀ᵐ z ∂ρ, d.g k (p.γ b) r' (obs (d.B k (p.γ b)) (δ (d.N k) r') z) ≤ M) →
      let α := (d.ν k (p.γ b) (p.A b) *
        ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹
      let C := ((M * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
        ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev b)))) *
          ENNReal.ofReal (36 * p.κ ^ 2)
      ENNReal.ofReal ((K ^ qexp)⁻¹) ≤ α * ρ univ → C ≤ ENNReal.ofReal (K ^ qexp) →
      NativeQuarterBranchCover e R K (packetNativeValueTest (d.N k) (d.B k) p b center)
        (α • ρ) (fun z j => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc) := by
  obtain ⟨e, R, he, hR, hbranches⟩ := original_native_quarter_branch_cover qexp
  refine ⟨e, R, he, hR, ?_⟩
  intro d hd k p κ₁ m s δ₀ Mp Dp σ hp b r' hr' hr'L hscale K ε hK hκK hε hεK
    hεwidth ρ hρ M center hF hbin htypical
  dsimp only
  intro hmass hC
  let α := (d.ν k (p.γ b) (p.A b) *
    ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹
  let Z := fun z : Event => fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc
  let w := fun z : Event => packetNativeCubePoint (d.N k) (d.B k) p b z 3
  let P := packetNativeValueTest (d.N k) (d.B k) p b center
  have hB : 0 < d.B k (p.γ b) := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 (p.γ b)).2.1
  have hN : 0 < d.N k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hd.1 k)
  have hZ : Measurable (fun z => WithLp.toLp 2 (Z z)) := by
    have hfun : (fun z => WithLp.toLp 2 (Z z)) =
        nativeCubeBase (3 * p.κ) ∘ packetBase p b := by
      funext z
      exact packetNativeCube_base_eq _ _ _ _ _
    rw [hfun]
    exact (measurable_nativeCubeBase _).comp (measurable_packetBase p b)
  have hcap := source_value_bin_native_cube_cap hd hp b r' hr' hr'L hscale hε hεwidth
    ρ hρ M center hF hbin htypical
  have hcap' : (α • ρ).map (fun z => WithLp.toLp 2 (Z z)) ≤ ENNReal.ofReal (K ^ qexp) • volume := by
    apply hcap.trans
    intro U
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' hC le_rfl
  obtain ⟨hdeg, hcurv, hsmall⟩ := packetNativeValueTest_global_data hp hN b hB hK hκK hε hεK center
  apply hbranches (α • ρ) Z w P hdeg K ε hK hε hcurv hsmall
  · simpa only [Measure.smul_apply, smul_eq_mul] using hmass
  · intro U hU
    exact original_base_cap_coordinate_preimages (α • ρ) (fun z => WithLp.toLp 2 (Z z))
      hZ (ENNReal.ofReal (K ^ qexp)) hcap' U hU
  · filter_upwards [Measure.ae_smul_measure hF α, Measure.ae_smul_measure hbin α] with z hz hzbin
    have hh := packetNativeValueTest_source_data hp hN b hB hK hκK hε hεK center hz
      (hzbin.trans (le_mul_of_one_le_left hε.le (by linarith : 1 ≤ K)))
    have hsnoc : (Fin.snoc (Z z) (w z) : Fin 4 → ℝ) =
        fun j => packetNativeCubePoint (d.N k) (d.B k) p b z j :=
      Fin.snoc_init_self _
    simpa only [hsnoc] using hh.2.2.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
