/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/NativeCoarseningTail.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.NativeCoarsening

/-! The fixed-sample angular estimate for truncating an exact Problem to a
smaller depth. All three exceptional sets use the original sampled law. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open Submission.Lib.K4Homogenization
open scoped ENNReal

theorem Data.Valid.angular_coarsening_tail {p : Data} (hp : p.Valid)
    {r u : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L) (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (k : ℕ) (γ : Fin (p.W k)) (c lo hi U : ℝ≥0∞) (hscale : hi ≤ c * lo) :
    p.selected k γ {z | 2 * c * U <
      coarsenedAngularDensity p r k γ u
        (nativeJointObs (p.B k γ) (p.N k) r u z)} ≤
      2 * (p.selected k γ {z | p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) < lo} +
        p.selected k γ {z | hi < p.G k γ u
          (nativeJointObs (p.B k γ) (p.N k) p.L u z)}) +
      p.selected k γ {z | U < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z)} := by
  letI := hp.selected_finite k γ
  have hN : 1 ≤ p.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1 k)
  have hL : 0 ≤ p.L := hr.trans hrL
  have hpoint : ∀ z : Incidence,
      coarsenObservation (p.N k) r p.L (obs (p.B k γ) (δ (p.N k) p.L) z) =
        obs (p.B k γ) (δ (p.N k) r) z :=
    fun z => (obs_coarsening (p.B k γ) hN hrL z).symm
  have hnew := hp.coarsened_angular_law hr hrL k γ u
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, hg, hG, _⟩
  have hgr := hg k γ r hr hrL
  have hgL := hg k γ p.L hL le_rfl
  have hGu := hG k γ u hu huη
  have hang : Measurable (fun z : Incidence => fun j => ⌊(v z.1) j / δ (p.N k) u⌋) := by
    unfold v
    fun_prop
  have hpure' : (p.selected k γ).map
      (coarsenObservation (p.N k) r p.L ∘ obs (p.B k γ) (δ (p.N k) p.L)) =
      (volume.prod Measure.count).withDensity (p.g k γ r) := by
    simpa only [Function.comp_def, hpoint, Data.selected] using hgr.2
  have hjoint' : (p.selected k γ).map
      (fun z => (coarsenObservation (p.N k) r p.L
        (obs (p.B k γ) (δ (p.N k) p.L) z),
        fun j => ⌊(v z.1) j / δ (p.N k) u⌋)) =
      ((volume.prod Measure.count).prod Measure.count).withDensity
        (coarsenedAngularDensity p r k γ u) := by
    simp only [hpoint]
    exact hnew
  have htail := angular_absolute_tail_after_coarsening
    (p.selected k γ) (volume.prod Measure.count) (volume.prod Measure.count) Measure.count
    (obs (p.B k γ) (δ (p.N k) p.L))
    (measurable_native_obs (p.B k γ) (δ (p.N k) p.L))
    (fun z : Incidence => fun j => ⌊(v z.1) j / δ (p.N k) u⌋) hang
    (coarsenObservation (p.N k) r p.L) (measurable_coarsenObservation _ _ _)
    c lo hi U hscale (p.g k γ p.L) hgL.1 (p.G k γ u) hGu.1
    (p.g k γ r) hgr.1 (coarsenedAngularDensity p r k γ u)
    (measurable_coarsenedAngularDensity p r k γ u) hgL.2 hGu.2 hpure' hjoint'
  simpa only [hpoint, nativeJointObs] using htail

end Submission.Obl.k4_balanced_native_packet_transport.CPF
