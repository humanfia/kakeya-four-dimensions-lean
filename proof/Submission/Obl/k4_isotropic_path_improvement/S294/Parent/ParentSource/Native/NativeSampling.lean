-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeSampling, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeSampling.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeSampling.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeSampling.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.GeneralPositionSampling
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteBinDomination

/-! Seven common direction bins for actual retained original fine packets.
Their fixed reference palette is the original current-parent velocity law. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

/-- Each state here is an actual original fine packet and retains its fixed
original code. The loss depends on `A`, not on the number of states or packets. -/
theorem PaletteFamily.exists_seven_native_bins {ι : Type*} [Fintype ι]
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (b : Fin p.C) (hb : F.active b) (fine : ι → Fin p.C)
    (hfine : ∀ v, p.lev (fine v) = stop) (hworld : ∀ v, p.γ (fine v) = p.γ b)
    (r fraction : ℝ) (hr : 0 < r) (ha : 0 < a) (hfraction : 0 ≤ fraction) (hA : 0 ≤ A)
    (hnarrow : ∀ v, F.coding.code (fine v) ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b)
    (hretained : ∀ v, F.coding.code (fine v) ∉
      fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)))
    (hgood : 686 * ENNReal.ofReal (8 * fraction) < 1)
    (weight : ι → ENNReal) (hweight : ∑ v, weight v ≠ 0) (hweight_top : ∑ v, weight v ≠ ∞) :
    ∃ β : Fin 7 → Fin 2 → ℤ,
      (∀ l j t : Fin 7, l ≠ j → l ≠ t → j ≠ t →
        r ^ 2 - 4 * a * (4 * p.κ + a / 2) ≤
          |Sampling.tripleDet (Sampling.binCenter a (β l)) (Sampling.binCenter a (β j))
            (Sampling.binCenter a (β t))|) ∧
      (∀ l c, |Sampling.binCenter a (β l) c| ≤ 2 * p.κ + a / 2) ∧
      (∀ l, Q.velocityPosterior b (Sampling.bin a (β l)) ≠ 0) ∧
      (∀ v, ∀ᵐ z ∂F.fineLaw b (F.coding.code (fine v)),
        z.2 ∈ p.packetWitness m stop (p.γ b) (fine v)) ∧
      (1 - 686 * ENNReal.ofReal (8 * fraction)) * (∑ v, weight v) ≤
        2 * ENNReal.ofReal (8 * A) ^ 7 * ∑ v ∈ Finset.univ.filter (fun v =>
          (1 - 686 * ENNReal.ofReal (8 * fraction)) * (∑ v, weight v) *
              ∏ l, Q.velocityPosterior b (Sampling.bin a (β l)) ≤
            2 * (∑ v, weight v) *
              ∏ l, F.fineVelocityLaw b (F.coding.code (fine v)) (Sampling.bin a (β l))), weight v ∧
      ∀ v, (1 - 686 * ENNReal.ofReal (8 * fraction)) * (∑ v, weight v) *
            ∏ l, Q.velocityPosterior b (Sampling.bin a (β l)) ≤
          2 * (∑ v, weight v) *
            ∏ l, F.fineVelocityLaw b (F.coding.code (fine v)) (Sampling.bin a (β l)) →
        ∀ l, 0 < F.fineVelocityLaw b (F.coding.code (fine v)) (Sampling.bin a (β l)) ∧
          (1 - 686 * ENNReal.ofReal (8 * fraction)) * (∑ v, weight v) *
            Q.velocityPosterior b (Sampling.bin a (β l)) ≤
          2 * (∑ v, weight v) * ENNReal.ofReal (8 * A) ^ 6 *
            F.fineVelocityLaw b (F.coding.code (fine v)) (Sampling.bin a (β l)) := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  let μ : ι → Measure (EuclideanSpace ℝ (Fin 2)) :=
    fun v => F.fineVelocityLaw b (F.coding.code (fine v))
  letI : ∀ v, IsProbabilityMeasure (μ v) := fun v =>
    (F.broad_fine_velocity_law hF r fraction hfraction b hb _ (hnarrow v) (hretained v)).1
  let := Q.velocity_posterior_probability hd b (F.current_positive b hb)
  have hdom : ∀ v β, μ v (Sampling.bin a β) ≤
      ENNReal.ofReal (8 * A) * Q.velocityPosterior b (Sampling.bin a β) :=
    fun v β => F.fine_bin_domination hF hA b hb _ (hretained v) β
  have hbreadth : ∀ v, Sampling.StripBreadth (μ v) r (ENNReal.ofReal (8 * fraction)) := by
    intro v n c hn
    have hbound := F.fine_strip_mass_le hF r fraction hfraction b hb _
      (hnarrow v) (hretained v) n c hn
    simpa only [Submission.Lib.K4VelocityStrips.affineStrip, real_inner_comm] using hbound
  have htail : ∀ v, μ v {x | 2 * p.κ < ‖x‖} ≤ 0 := fun v => by
    rw [show μ v {x | 2 * p.κ < ‖x‖} = 0 from F.fine_velocity_tail_zero hp b hb _]
  have h := Sampling.exists_seven_bins_states_of_bin_domination weight μ (Q.velocityPosterior b)
    (by simp) (K := ENNReal.ofReal (8 * A)) ENNReal.ofReal_ne_top hdom hr ha hbreadth htail
    (by simpa only [mul_zero, add_zero] using hgood) hweight hweight_top
  have hκ : 2 * (2 * p.κ) = 4 * p.κ := by ring
  simp only [μ, measure_univ, one_pow, div_one, mul_zero, add_zero, hκ] at h
  obtain ⟨β, hdet, hcenter, hpositive, hmass, hbin⟩ := h
  refine ⟨β, hdet, hcenter, hpositive, ?_, hmass, ?_⟩
  · intro v
    simpa only [hworld v] using
      F.fine_law_original_packet hp hH b hb (fine v) (hfine v) (hworld v)
  · intro v hv l
    have hbound := hbin v hv l
    refine ⟨?_, hbound⟩
    by_contra hn
    have hz : F.fineVelocityLaw b (F.coding.code (fine v)) (Sampling.bin a (β l)) = 0 :=
      le_antisymm (le_of_not_gt hn) zero_le
    rw [hz, mul_zero] at hbound
    have hpos : 0 < (1 - 686 * ENNReal.ofReal (8 * fraction)) * (∑ v, weight v) *
        Q.velocityPosterior b (Sampling.bin a (β l)) :=
      ENNReal.mul_pos (mul_ne_zero (tsub_pos_of_lt hgood).ne' hweight) (hpositive l)
    exact not_le_of_gt hpos hbound

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
