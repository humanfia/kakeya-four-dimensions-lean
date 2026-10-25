import Submission.Obl.k4_raw_localized_native_systems.C.ProblemDensities
import Submission.Obl.k4_coarsened_outer_horizon_composition.Crossings
import Submission.Lib.K4XInterface.Basic

/-
Adapted from this LOT tree, o178, session x0596, `LabelBadMass.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The bad-pair mass charged to one earlier label

In the full-time localization (paper, Section 10, Proposition 10.2), the bad
incidences charged to one first label lie, at the second time, in the
extrapolated parallelogram of that label, pass the depth-zero native hidden-bin
test, are typical at depth zero, are good for the terminal angular cap, and have
their velocity bin in a short list determined by the terminal observation.
Their mass is at most

  `N^(-S u + 2τ) * m * N^(-f 0 + τ) * 256 κ⁴ |det Q|`,

using the accepted crossing volume of o148 (`reference_crossing`).
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Depth-zero typicality ceiling for an incidence. -/
def Typ0 (p : Data) (k : ℕ) (γ : Fin (p.W k)) (τ : ℝ) (q : Point) : Prop :=
  p.g k γ 0 (obs (p.B k γ) (δ (p.N k) 0) q) ≤ ENNReal.ofReal (p.N k ^ (-p.f 0 + τ))

/-- The depth-zero crossing set of a frame for the native test of a world. -/
def nativeCrossing (p : Data) (k : ℕ) (γ : Fin (p.W k)) (κ : ℝ) (c u : Plane)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Set Observation :=
  Submission.Obl.k4_coarsened_outer_horizon_composition.crossing κ 0 1 (1 / p.B k γ)
    (p.B k γ) c u Q (p.P k γ)

theorem measurableSet_nativeCrossing (p : Data) (k : ℕ) (γ : Fin (p.W k)) (κ : ℝ)
    (c u : Plane) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    MeasurableSet (nativeCrossing p k γ κ c u Q) :=
  Submission.Obl.k4_coarsened_outer_horizon_composition.measurableSet_crossing _ _ _ _ _ _ _ _ _

theorem measurable_coarsenObs (n : ℕ) :
    Measurable (Submission.Lib.K4XInterface.coarsenObs n) := by
  unfold Submission.Lib.K4XInterface.coarsenObs
  exact measurable_fst.prodMk
    ((measurable_of_countable (fun z : ℤ => z / (2 : ℤ) ^ n)).comp measurable_snd)

/-- The depth-zero observation is a coarsening of the terminal one. -/
theorem obs_zero_eq_coarsen {N L : ℝ} (hN : 1 ≤ N) (hL : 0 ≤ L) (B : ℝ) (q : Point) :
    obs B (δ N 0) q = Submission.Lib.K4XInterface.coarsenObs
      (Submission.Lib.K4XInterface.depthIdx N L - Submission.Lib.K4XInterface.depthIdx N 0)
      (obs B (δ N L) q) :=
  Submission.Lib.K4XInterface.gobs_coarsen hN le_rfl hL B q

/-- **Per-label bad mass.** -/
theorem label_bad_mass_le {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {u τ : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L) {κ : ℝ} (hκ : 1 ≤ κ)
    (c u₀ : Plane) (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (bins : Observation → Finset (Fin 2 → ℤ)) (m : ℕ)
    (hbins : ∀ w, MeasurableSet {o | w ∈ bins o}) (hcard : ∀ o, (bins o).card ≤ m) :
    selected p k γ {q | AngGood p k γ u τ q ∧ Typ0 p k γ τ q ∧
        obs (p.B k γ) (δ (p.N k) 0) q ∈ nativeCrossing p k γ κ c u₀ Q ∧
        velBin (p.N k) u q ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) q)} ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * m *
        (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
          ENNReal.ofReal (256 * κ ^ 4 * (1 - 0) * |Q.det|)) := by
  have hN : 0 < p.N k := hp.scale_pos k
  have hN1 : 1 ≤ p.N k := hp.scale_ge_one k
  have hL : 0 ≤ p.L := hp.length_pos.le
  set n := Submission.Lib.K4XInterface.depthIdx (p.N k) p.L -
    Submission.Lib.K4XInterface.depthIdx (p.N k) 0 with hn
  set co := Submission.Lib.K4XInterface.coarsenObs n with hco
  have hcom : Measurable co := measurable_coarsenObs n
  obtain ⟨hGm, hG⟩ := valid_G_spec hp k γ hu huη
  obtain ⟨hgm, hg⟩ := valid_g_spec hp k γ hL le_rfl
  obtain ⟨hg0m, hg0⟩ := valid_g_spec hp k γ le_rfl hL
  -- the support of the listed bins, in terminal observations
  set C0 := ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) with hC0
  set S : Set Observation := {o | co o ∈ nativeCrossing p k γ κ c u₀ Q ∧ p.g k γ 0 (co o) ≤ C0}
    with hSdef
  have hSm : MeasurableSet S :=
    (hcom (measurableSet_nativeCrossing p k γ κ c u₀ Q)).inter
      (measurableSet_le (hg0m.comp hcom) measurable_const)
  classical
  set bins' : Observation → Finset (Fin 2 → ℤ) := fun o => if o ∈ S then bins o else ∅
    with hbins'
  have hbins'm : ∀ w, MeasurableSet {o | w ∈ bins' o} := by
    intro w
    have : {o | w ∈ bins' o} = S ∩ {o | w ∈ bins o} := by
      ext o
      simp only [hbins', Set.mem_setOf_eq, Set.mem_inter_iff]
      split_ifs with h <;> simp [h]
    rw [this]
    exact hSm.inter (hbins w)
  have hcard' : ∀ o, (bins' o).card ≤ m := by
    intro o
    simp only [hbins']
    split_ifs
    · exact hcard o
    · simp
  have hsupp : ∀ o, o ∉ S → bins' o = ∅ := by
    intro o ho
    simp [hbins', ho]
  -- the bad set is inside the charged set
  have hsub : {q | AngGood p k γ u τ q ∧ Typ0 p k γ τ q ∧
        obs (p.B k γ) (δ (p.N k) 0) q ∈ nativeCrossing p k γ κ c u₀ Q ∧
        velBin (p.N k) u q ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) q)} ⊆
      {q | p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) q, velBin (p.N k) u q) ≤
          ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
            p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) q) ∧
        velBin (p.N k) u q ∈ bins' (obs (p.B k γ) (δ (p.N k) p.L) q)} := by
    intro q hq
    obtain ⟨hgood, htyp, hcross, hbin⟩ := hq
    refine ⟨hgood.G_le hN, ?_⟩
    have hco_eq : co (obs (p.B k γ) (δ (p.N k) p.L) q) = obs (p.B k γ) (δ (p.N k) 0) q :=
      (obs_zero_eq_coarsen hN1 hL (p.B k γ) q).symm
    have hS : obs (p.B k γ) (δ (p.N k) p.L) q ∈ S := by
      refine ⟨?_, ?_⟩
      · rw [hco_eq]; exact hcross
      · rw [hco_eq]; exact htyp
    simp only [hbins', if_pos hS]
    exact hbin
  refine (measure_mono hsub).trans ?_
  rw [jointObs_eq] at hG
  have hcharge := listed_bins_mass_le_support (selected p k γ) (volume.prod Measure.count)
    (obs (p.B k γ) (δ (p.N k) p.L)) (velBin (p.N k) u) (measurable_obs' _ _)
    (measurable_velBin _ _) (p.G k γ u) (p.g k γ p.L) hGm hgm hG hg
    (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ))) bins' m hbins'm hcard' S hSm hsupp
  refine hcharge.trans ?_
  gcongr
  -- the support mass through the depth-zero density
  have hpre : obs (p.B k γ) (δ (p.N k) p.L) ⁻¹' S =
      obs (p.B k γ) (δ (p.N k) 0) ⁻¹'
        (nativeCrossing p k γ κ c u₀ Q ∩ {o | p.g k γ 0 o ≤ C0}) := by
    ext q
    simp only [Set.mem_preimage, hSdef, Set.mem_setOf_eq, Set.mem_inter_iff]
    have hq : co (obs (p.B k γ) (δ (p.N k) p.L) q) = obs (p.B k γ) (δ (p.N k) 0) q :=
      (obs_zero_eq_coarsen hN1 hL (p.B k γ) q).symm
    rw [hq]
  have hTm : MeasurableSet (nativeCrossing p k γ κ c u₀ Q ∩ {o | p.g k γ 0 o ≤ C0}) :=
    (measurableSet_nativeCrossing p k γ κ c u₀ Q).inter (measurableSet_le hg0m measurable_const)
  rw [hpre, ← Measure.map_apply (measurable_obs' _ _) hTm, hg0, withDensity_apply _ hTm]
  calc ∫⁻ o in nativeCrossing p k γ κ c u₀ Q ∩ {o | p.g k γ 0 o ≤ C0}, p.g k γ 0 o
        ∂(volume.prod Measure.count)
      ≤ ∫⁻ _o in nativeCrossing p k γ κ c u₀ Q ∩ {o | p.g k γ 0 o ≤ C0}, C0
          ∂(volume.prod Measure.count) := by
        apply setLIntegral_mono' hTm
        intro o ho
        exact ho.2
    _ = C0 * (volume.prod Measure.count)
          (nativeCrossing p k γ κ c u₀ Q ∩ {o | p.g k γ 0 o ≤ C0}) := setLIntegral_const _ _
    _ ≤ C0 * (volume.prod Measure.count) (nativeCrossing p k γ κ c u₀ Q) := by
        gcongr; exact Set.inter_subset_left
    _ ≤ C0 * ENNReal.ofReal (256 * κ ^ 4 * (1 - 0) * |Q.det|) := by
        gcongr
        exact Submission.Obl.k4_coarsened_outer_horizon_composition.reference_crossing hκ
          zero_le_one (by have := hp.B_pos k γ; positivity) (hp.B_pos k γ) c u₀ Q hQ (p.P k γ)
          (by
            obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
            exact ((hfmt k).2.2.2.1 γ).2.2.2.2.1)

end

end Submission.Obl.k4_raw_localized_native_systems.C
