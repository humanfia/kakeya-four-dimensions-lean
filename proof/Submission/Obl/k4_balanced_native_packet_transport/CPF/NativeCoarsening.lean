/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/NativeCoarsening.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.AngularCoarsening
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.CountedDensity
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.IncidenceTransport

/-! The native angular law at any smaller pure-observation depth. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open Submission.Lib.K4Homogenization
open scoped ENNReal

noncomputable def Data.selected (p : Data) (k : ℕ) (γ : Fin (p.W k)) :
    Measure Incidence := ((p.ν k γ).prod volume).restrict (p.E k γ)

theorem Data.Valid.selected_finite {p : Data} (hp : p.Valid)
    (k : ℕ) (γ : Fin (p.W k)) : IsFiniteMeasure (p.selected k γ) := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, htemp, _⟩
  obtain ⟨M, D, htemp⟩ := htemp
  obtain ⟨hprob, _, _, _, _, _, _, _, hunit, _⟩ := (htemp k).2.2.2.1 γ
  letI := hprob
  exact Submission.Obl.k4_dyadic_crop_affine_laws.Framework.finite_selected_incidence
    (p.ν k γ) (p.E k γ) hunit

theorem measurable_native_obs (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  fun_prop

noncomputable def nativeJointObs (B N r u : ℝ) (p : Incidence) : JointObservation :=
  (obs B (δ N r) p, fun j => ⌊(v p.1) j / δ N u⌋)

theorem measurable_nativeJointObs (B N r u : ℝ) :
    Measurable (nativeJointObs B N r u) := by
  apply (measurable_native_obs B (δ N r)).prodMk
  unfold v
  fun_prop

/-- A canonical measurable representative of the angular density after coarsening. -/
noncomputable def coarsenedAngularDensity (p : Data) (r : ℝ) (k : ℕ)
    (γ : Fin (p.W k)) (u : ℝ) : JointObservation → ℝ≥0∞ :=
  ((p.selected k γ).map (nativeJointObs (p.B k γ) (p.N k) r u)).rnDeriv
    ((volume.prod Measure.count).prod Measure.count)

theorem measurable_coarsenedAngularDensity (p : Data) (r : ℝ) (k : ℕ)
    (γ : Fin (p.W k)) (u : ℝ) : Measurable (coarsenedAngularDensity p r k γ u) :=
  Measure.measurable_rnDeriv _ _

/-- Pure densities already supplied by Problem give the full joint law at every
smaller depth; adjoining the countable angular label preserves absolute continuity. -/
theorem Data.Valid.coarsened_angular_law {p : Data} (hp : p.Valid)
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L) (k : ℕ) (γ : Fin (p.W k)) (u : ℝ) :
    (p.selected k γ).map (nativeJointObs (p.B k γ) (p.N k) r u) =
      ((volume.prod Measure.count).prod Measure.count).withDensity
        (coarsenedAngularDensity p r k γ u) := by
  letI := hp.selected_finite k γ
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, hg, _⟩
  have hobs := measurable_nativeJointObs (p.B k γ) (p.N k) r u
  have hbase : ((p.selected k γ).map
      (nativeJointObs (p.B k γ) (p.N k) r u)).map Prod.fst ≪
      volume.prod Measure.count := by
    rw [Measure.map_map measurable_fst hobs]
    change (((p.ν k γ).prod volume).restrict (p.E k γ)).map
      (obs (p.B k γ) (δ (p.N k) r)) ≪ _
    rw [(hg k γ r hr hrL).2]
    exact withDensity_absolutelyContinuous _ _
  have hac := Submission.Obl.k4_dyadic_crop_affine_laws.Framework.absolutelyContinuous_prod_count_of_fst
    _ _ hbase
  exact (Measure.withDensity_rnDeriv_eq _ _ hac).symm

end Submission.Obl.k4_balanced_native_packet_transport.CPF
