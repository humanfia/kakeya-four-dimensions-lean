-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripObservation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripObservation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripObservation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripObservation.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripObservation.lean.
   Original comments and attributions are preserved below. -/
import Submission.Lib.K4VelocityStrips
import Submission.Lib.K4XInterface.Formats

/-! The midpoint-bin lists are functions of the original terminal observation.
Normalization uses only the supplied parent frame, center and time block. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

def packetPosition (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : StripSpace)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : StripSpace :=
  Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)

def packetVelocity (q : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (u : StripSpace)
    (l : ℕ × (Fin 6 → ℝ)) : StripSpace :=
  q • Matrix.toEuclideanLin Q⁻¹ (gv l - u)

def observedPacketPosition (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : StripSpace)
    (o : EuclideanSpace ℝ (Fin 3) × ℤ) : StripSpace :=
  Matrix.toEuclideanLin Q⁻¹
    (WithLp.toLp 2 ![o.1 1, o.1 2] - c - (o.1 0) • u)

theorem continuous_packetPosition (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : StripSpace) (t : ℝ) :
    Continuous (fun l : ℕ × (Fin 6 → ℝ) => packetPosition Q c u l t) := by
  have hL : Continuous (Matrix.toEuclideanLin Q⁻¹) :=
    (Matrix.toEuclideanLin Q⁻¹).continuous_of_finiteDimensional
  apply hL.comp
  fun_prop [gy, gx]

theorem continuous_packetVelocity (q : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (u : StripSpace) :
    Continuous (packetVelocity q Q u) := by
  have hL : Continuous (Matrix.toEuclideanLin Q⁻¹) :=
    (Matrix.toEuclideanLin Q⁻¹).continuous_of_finiteDimensional
  unfold packetVelocity
  fun_prop [gv]

theorem observedPacketPosition_obs (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : StripSpace)
    (B a : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    observedPacketPosition Q c u (gobs B a p) = packetPosition Q c u p.1 p.2 := by
  rfl

theorem packetPosition_affine (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : StripSpace)
    (l : ℕ × (Fin 6 → ℝ)) (t₀ q t : ℝ) :
    packetPosition Q c u l (t₀ + q * t) =
      packetPosition Q c u l t₀ + t • packetVelocity q Q u l := by
  unfold packetPosition packetVelocity
  rw [gy_offset_eq l c u t₀ (t₀ + q * t)]
  simp only [map_add, map_smul, smul_smul]
  congr 1
  congr 1
  ring

/-- Every counted incidence in a strip has its midpoint label in a fixed short
list evaluated at its original terminal observation. -/
theorem packet_midpoint_bin_known (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u n : StripSpace)
    (B a t₀ q r β : ℝ) (C : ℕ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hq : 0 < q) (hr : 0 < r) (ht : p.2 ∈ Set.Icc t₀ (t₀ + q))
    (hvel : |inner ℝ (packetVelocity q Q u p.1) n - β| ≤ (C : ℝ) * r) :
    ⌊inner ℝ (packetPosition Q c u p.1 (t₀ + q / 2)) n / r⌋ ∈
      midpointBinList r n β (((gobs B a p).1 0 - t₀) / q)
        (observedPacketPosition Q c u (gobs B a p)) C := by
  let t : ℝ := (p.2 - t₀) / q
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by linarith [ht.1]) hq.le, ?_⟩
    exact (div_le_one hq).mpr (by linarith [ht.2])
  have htime : t₀ + q * t = p.2 := by dsimp [t]; field_simp; ring
  have hmid : t₀ + q * (1 / 2 : ℝ) = t₀ + q / 2 := by ring
  have h := midpoint_bin_mem_list (a := packetPosition Q c u p.1 t₀)
    (v := packetVelocity q Q u p.1) (n := n) (β := β) hr ht' hvel
  rw [← packetPosition_affine Q c u p.1 t₀ q (1 / 2),
    ← packetPosition_affine Q c u p.1 t₀ q t, hmid, htime] at h
  rw [observedPacketPosition_obs]
  exact h

theorem packet_midpoint_bin_known_of_obs_eq
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u n : StripSpace)
    (B a t₀ q r β : ℝ) (C : ℕ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (o : EuclideanSpace ℝ (Fin 3) × ℤ)
    (hq : 0 < q) (hr : 0 < r) (ht : p.2 ∈ Set.Icc t₀ (t₀ + q))
    (hvel : |inner ℝ (packetVelocity q Q u p.1) n - β| ≤ (C : ℝ) * r)
    (ho : gobs B a p = o) :
    ⌊inner ℝ (packetPosition Q c u p.1 (t₀ + q / 2)) n / r⌋ ∈
      midpointBinList r n β ((o.1 0 - t₀) / q) (observedPacketPosition Q c u o) C := by
  subst o
  exact packet_midpoint_bin_known Q c u n B a t₀ q r β C p hq hr ht hvel

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
