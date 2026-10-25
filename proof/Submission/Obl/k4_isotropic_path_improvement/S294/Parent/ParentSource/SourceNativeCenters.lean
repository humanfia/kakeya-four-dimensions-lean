-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceNativeCenters, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceNativeCenters.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceNativeCenters.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeCenters.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeCenters.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceNativeCubeCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeValueBins
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.OriginalNativeCenters

/-! # Good branch centers from the actual original fine entry -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic k4_stable_native_signal_oscillation

noncomputable section

/-- The value-bin condition in actual fine native units implies the
original raw band used by the source cap. The reference denominator is
still the FULL original assignment, rather than the value-bin mass. -/
theorem source_value_bin_native_cube_cap
    {d : Native.ProblemData} (hd : d.Valid) {k : ℕ} {p : Native.PathData (d.W k)}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev b)))
    {ε : ℝ} (hε : 0 < ε)
    (hεwidth : δ (d.N k) (p.r (p.lev b)) * ε ≤ δ (d.N k) r')
    (ρ : Measure Event) (hρ : ρ ≤ d.μ k (p.γ b)) (M : ENNReal) (center : ℝ)
    (hF : ∀ᵐ q ∂ρ, q ∈ p.F b)
    (hbin : ∀ᵐ q ∂ρ, |eval (fun j => packetNativeCubePoint (d.N k) (d.B k) p b q j)
      (packetNativeCubeTest (d.N k) (d.B k) p b) - center| ≤ ε)
    (htypical : ∀ᵐ q ∂ρ, d.g k (p.γ b) r'
      (obs (d.B k (p.γ b)) (δ (d.N k) r') q) ≤ M) :
    let α := (d.ν k (p.γ b) (p.A b) *
      ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹
    let C := ((M * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
      ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev b)))) *
        ENNReal.ofReal (36 * p.κ ^ 2)
    (α • ρ).map (fun q => WithLp.toLp 2
      (fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b q j.castSucc)) ≤ C • volume := by
  have hB : 0 < d.B k (p.γ b) := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 (p.γ b)).2.1
  have hδ : 0 < δ (d.N k) (p.r (p.lev b)) := by unfold δ; positivity
  apply source_native_cube_cap hd hp b r' hr' hr'L hscale ρ hρ M
    (δ (d.N k) (p.r (p.lev b)) * center) hF ?_ htypical
  filter_upwards [hbin] with q hq
  have heval := (packetNativeCubePolynomial_original_values hp b hB (p.R b) q).1
  change eval (fun j => packetNativeCubePoint (d.N k) (d.B k) p b q j)
    (packetNativeCubeTest (d.N k) (d.B k) p b) = _ at heval
  rw [heval] at hq
  have hid : eval (xp q.1 q.2) (p.R b) - δ (d.N k) (p.r (p.lev b)) * center =
      δ (d.N k) (p.r (p.lev b)) *
        ((δ (d.N k) (p.r (p.lev b)))⁻¹ * eval (xp q.1 q.2) (p.R b) - center) := by
    field_simp
  change |eval (xp q.1 q.2) (p.R b) - δ (d.N k) (p.r (p.lev b)) * center| ≤ _
  rw [hid, abs_mul, abs_of_pos hδ]
  calc
    _ ≤ δ (d.N k) (p.r (p.lev b)) * ε := mul_le_mul_of_nonneg_left hq hδ.le
    _ ≤ δ (d.N k) r' := hεwidth
    _ ≤ max p.κ (d.K k) * δ (d.N k) r' :=
      le_mul_of_one_le_left (by unfold δ; positivity) (hp.1.trans (le_max_left _ _))

/-- Actual original source data, an EARLIER full-reference entry floor,
and a numeric bound for the original source cap give the good-center
preparation. The coefficient exponent is chosen BEFORE all path and format
data. No later common-potential selection appears in the denominator. -/
theorem source_original_native_centers (qexp : ℕ) :
    ∃ e : ℕ, 4 ≤ e ∧ ∀ {d : Native.ProblemData}, d.Valid →
      ∀ {k : ℕ} {p : Native.PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      ∀ (b : Fin p.C) (r' : ℝ), 0 ≤ r' → r' ≤ d.L →
      δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev b)) →
      ∀ K ε : ℝ, 2 ≤ K → 3 * p.κ ≤ K → 0 < ε → ε ≤ (K ^ 6)⁻¹ →
      δ (d.N k) (p.r (p.lev b)) * ε ≤ δ (d.N k) r' →
      ∀ (ρ : Measure Event), ρ ≤ d.μ k (p.γ b) → ∀ (M : ENNReal) (center : ℝ),
      (∀ᵐ q ∂ρ, q ∈ p.F b) →
      (∀ᵐ q ∂ρ, |eval (fun j => packetNativeCubePoint (d.N k) (d.B k) p b q j)
        (packetNativeCubeTest (d.N k) (d.B k) p b) - center| ≤ ε) →
      (∀ᵐ q ∂ρ, d.g k (p.γ b) r' (obs (d.B k (p.γ b)) (δ (d.N k) r') q) ≤ M) →
      let α := (d.ν k (p.γ b) (p.A b) *
        ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹
      let C := ((M * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
        ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev b)))) *
          ENNReal.ofReal (36 * p.κ ^ 2)
      let P := packetNativeValueTest (d.N k) (d.B k) p b center
      let Z := fun q : Event => fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b q j.castSucc
      ENNReal.ofReal ((K ^ qexp)⁻¹) ≤ α * ρ univ → C ≤ ENNReal.ofReal (K ^ qexp) →
      (∀ d, |(baseDiscriminant P).coeff d| ≤ K ^ e) ∧
      ∀ R : ℕ, ∃ S : Finset (EuclideanSpace ℝ (Fin 3)),
        (S.card : ℝ) ≤ K ^ (3 * R + 12) ∧
        (∀ c ∈ S, (fun j => c j) ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
          ((K ^ e)⁻¹) ^ 2 ≤ eval (fun j => c j) (baseDiscriminant P)) ∧
        ∀ᵐ x ∂(α • ρ), ∃ c ∈ S, ‖WithLp.toLp 2 (Z x) - c‖ ≤ (K ^ R)⁻¹ := by
  obtain ⟨e, he, hcenters⟩ := original_native_discriminant_centers qexp
  refine ⟨e, he, ?_⟩
  intro d hd k p κ₁ m s δ₀ Mp Dp σ hp b r' hr' hr'L hscale K ε hK hκK hε hεK
    hεwidth ρ hρ M center hF hbin htypical
  dsimp only
  intro hmass hC
  let α := (d.ν k (p.γ b) (p.A b) *
    ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹
  let Z := fun q : Event => fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b q j.castSucc
  let w := fun q : Event => packetNativeCubePoint (d.N k) (d.B k) p b q 3
  let P := packetNativeValueTest (d.N k) (d.B k) p b center
  have hB : 0 < d.B k (p.γ b) := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 (p.γ b)).2.1
  have hN : 0 < d.N k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hd.1 k)
  have hZ : Measurable (fun q => WithLp.toLp 2 (Z q)) := by
    have hfun : (fun q => WithLp.toLp 2 (Z q)) =
        nativeCubeBase (3 * p.κ) ∘ packetBase p b := by
      funext q
      exact packetNativeCube_base_eq _ _ _ _ _
    rw [hfun]
    exact (measurable_nativeCubeBase _).comp (measurable_packetBase p b)
  have hcap := source_value_bin_native_cube_cap hd hp b r' hr' hr'L hscale hε hεwidth
    ρ hρ M center hF hbin htypical
  have hcap' : (α • ρ).map (fun q => WithLp.toLp 2 (Z q)) ≤ ENNReal.ofReal (K ^ qexp) • volume := by
    apply hcap.trans
    intro U
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' hC le_rfl
  obtain ⟨hdeg, hcurv, hsmall⟩ := packetNativeValueTest_global_data hp hN b hB hK hκK hε hεK center
  apply hcenters (α • ρ) Z w P hdeg K ε hK hε hcurv hsmall
  · simpa only [Measure.smul_apply, smul_eq_mul] using hmass
  · intro U hU
    exact original_base_cap_coordinate_preimages (α • ρ) (fun q => WithLp.toLp 2 (Z q))
      hZ (ENNReal.ofReal (K ^ qexp)) hcap' U hU
  · filter_upwards [Measure.ae_smul_measure hF α, Measure.ae_smul_measure hbin α] with q hq hqbin
    have hh := packetNativeValueTest_source_data hp hN b hB hK hκK hε hεK center hq
      (hqbin.trans (le_mul_of_one_le_left hε.le (by linarith : 1 ≤ K)))
    have hsnoc : (Fin.snoc (Z q) (w q) : Fin 4 → ℝ) =
        fun j => packetNativeCubePoint (d.N k) (d.B k) p b q j :=
      Fin.snoc_init_self _
    simpa only [hsnoc] using hh.2.2.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
