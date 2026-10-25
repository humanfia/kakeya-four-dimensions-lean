-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceValueBranches, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceValueBranches.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceValueBranches.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceValueBranches.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceValueBranches.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketValueEntries
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceNativeBranches

/-! # Original heavy value entries with their actual coded native branches -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic

noncomputable section

/-- Original pure-density tests and the actual fine value partition give
heavy full-reference entries together with their coded branch covers.
All floors are established BEFORE potential, sign or common-intercept
selection. No hypothesis supplies a preselected value-bin entry. -/
theorem source_heavy_original_value_branches (qexp : ℕ) :
    ∃ e R : ℕ, 4 ≤ e ∧ 1 ≤ R ∧
    ∀ {d : Native.ProblemData}, d.Valid →
    ∀ {k : ℕ} {p : Native.PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
    ∀ (H : Fin (d.W k) → Set Event), (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
    ∀ i : ℕ, i < m → ∀ K r' : ℝ, 2 ≤ K → 3 * p.κ ≤ K →
      0 ≤ r' → r' ≤ d.L → δ (d.N k) r' ≤ δ (d.N k) (p.r i) →
      δ (d.N k) (p.r i) * (K ^ 6)⁻¹ ≤ δ (d.N k) r' →
    ∀ MCap : ENNReal,
      (∀ w z, z ∈ H w → d.g k w r' (obs (d.B k w) (δ (d.N k) r') z) ≤ MCap) →
      (∀ b, p.lev b = i →
        ((MCap * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
          ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r i))) * ENNReal.ofReal (36 * p.κ ^ 2) ≤
            ENNReal.ofReal (K ^ qexp)) →
    ∃ M : ℕ, ∃ center : Fin M → ℝ,
    ∃ U V : Fin p.C → Fin M → Set Event, ∃ H' : Fin (d.W k) → Set Event,
      (M : ℝ) ≤ K ^ 10 ∧
      (∀ b a, MeasurableSet (U b a) ∧ MeasurableSet (V b a)) ∧
      (∀ b, Pairwise fun a a' => Disjoint (V b a) (V b a')) ∧
      (∀ b a, V b a ⊆ U b a ∧ U b a ⊆ H (p.γ b) ∩ p.F b) ∧
      (∀ b a z, z ∈ U b a → |packetSignal (d.N k) p b z - center a| ≤ (K ^ 6)⁻¹) ∧
      (∀ w, MeasurableSet (H' w) ∧ H' w ⊆ H w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w \ H' w)) ≤
        ENNReal.ofReal (K ^ 10) * ENNReal.ofReal ((K ^ qexp)⁻¹) ∧
      (∀ b, p.lev b = i → ∀ a, (V b a).Nonempty →
        ENNReal.ofReal ((K ^ qexp)⁻¹) *
          (ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * d.ν k (p.γ b) (p.A b)) ≤
            ((d.ν k (p.γ b)).prod volume) (U b a)) ∧
      (∀ b, p.lev b = i → ∀ a, (V b a).Nonempty →
        NativeQuarterBranchCover e R K (packetNativeValueTest (d.N k) (d.B k) p b (center a))
          (((d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹))⁻¹) •
            (((d.ν k (p.γ b)).prod volume).restrict (U b a)))
          (fun z j => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc)) ∧
      ∀ w z, z ∈ H' w → ∃ b a, p.lev b = i ∧ p.γ b = w ∧ z ∈ V b a := by
  obtain ⟨e, R, he, hR, hbranches⟩ := source_original_native_quarter_branches qexp
  refine ⟨e, R, he, hR, ?_⟩
  intro d hd k p κ₁ m s δ₀ Mp Dp σ hp H hH hterminal i hi K r' hK hκK
    hr' hr'L hscale hεwidth MCap htypical hcapnum
  obtain ⟨hweight, hsum, hν⟩ := hd.weights k
  obtain ⟨M, center, U, V, H', hM, hUVm, hVd, hUV, hfit, hH', hloss, hfloor, hcover⟩ :=
    path_heavy_original_value_entries hp hν hweight hsum H hH hterminal i hi hK
      (by linarith [hp.1]) (ENNReal.ofReal ((K ^ qexp)⁻¹))
  refine ⟨M, center, U, V, H', hM, hUVm, hVd, hUV, hfit, hH', hloss, hfloor, ?_, hcover⟩
  intro b hb a ha
  let ρ := ((d.ν k (p.γ b)).prod volume).restrict (U b a)
  let ref := d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹)
  have hKp : 0 < K := by linarith
  have hN : 0 < d.N k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hd.1 k)
  letI : IsProbabilityMeasure (d.ν k (p.γ b)) := hν _
  have href0 : ref ≠ 0 := mul_ne_zero (hp.assignment_mass_pos hN b).ne'
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hrefTop : ref ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hmass : ENNReal.ofReal ((K ^ qexp)⁻¹) ≤ ref⁻¹ * ρ univ := by
    have hh : ENNReal.ofReal ((K ^ qexp)⁻¹) * ref ≤ ρ univ := by
      simpa only [ref, ρ, Measure.restrict_apply_univ, mul_comm] using hfloor b hb a ha
    calc
      _ = ref⁻¹ * (ENNReal.ofReal ((K ^ qexp)⁻¹) * ref) := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel href0 hrefTop, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hh zero_le
  have hρ : ρ ≤ d.μ k (p.γ b) := by
    apply Measure.restrict_mono_set
    intro z hz
    exact (path_packet_support hp b ((hUV b a).2 hz).2).1
  have hsupp : ∀ᵐ z ∂ρ, z ∈ U b a := ae_restrict_mem (hUVm b a).1
  have hB : 0 < d.B k (p.γ b) := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 (p.γ b)).2.1
  have hbin : ∀ᵐ z ∂ρ, |eval (fun j => packetNativeCubePoint (d.N k) (d.B k) p b z j)
      (packetNativeCubeTest (d.N k) (d.B k) p b) - center a| ≤ (K ^ 6)⁻¹ := by
    filter_upwards [hsupp] with z hz
    have heval := (packetNativeCubePolynomial_original_values hp b hB (p.R b) z).1
    change eval (fun j => packetNativeCubePoint (d.N k) (d.B k) p b z j)
      (packetNativeCubeTest (d.N k) (d.B k) p b) = packetSignal (d.N k) p b z at heval
    rw [heval]
    exact hfit b a z hz
  rw [← hb]
  exact hbranches hd hp b r' hr' hr'L (by simpa only [hb] using hscale) K (K ^ 6)⁻¹
    hK hκK (by positivity) le_rfl (by simpa only [hb] using hεwidth)
    ρ hρ MCap (center a)
    (hsupp.mono (fun z hz => ((hUV b a).2 hz).2)) hbin
    (hsupp.mono (fun z hz => htypical _ z ((hUV b a).2 hz).1))
    (by simpa only [hb, ref] using hmass) (by simpa only [hb] using hcapnum b hb)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
