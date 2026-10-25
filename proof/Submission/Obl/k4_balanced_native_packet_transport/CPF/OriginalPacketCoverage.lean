/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/OriginalPacketCoverage.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedPacketSystems
import Submission.Obl.k4_native_finite_terminal_atlas_lift.ProductTransport
import Submission.Obl.k4_native_finite_terminal_atlas_lift.MassCalibration

/-! Restore actual child incidence events and their original weighted coverage.
Conditioning is undone with the full parent prior and its actual time length. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace OriginalPacketCoverage

open MeasureTheory Set Filter
open BalancedPacketSystems

noncomputable def incidenceEquiv {p : SourceData} (q : Certificate p) (k : ℕ)
    (b : Fin (q.sequence.atlas k).C) : Incidence ≃ᵐ Incidence :=
  Submission.Obl.k4_native_finite_terminal_atlas_lift.normalizedIncidenceEquiv
    (NormalizedAssignments.trajectoryEquiv (q.sequence.atlas k) b (parent_det_ne_zero q k b))
    (((q.sequence.atlas k).j b : ℝ) / (2 : ℝ) ^ (q.sequence.atlas k).T)
    (1 / (2 : ℝ) ^ (q.sequence.atlas k).T) (by positivity)

def originalEvent {p : SourceData} (q : Certificate p) (k : ℕ)
    (a : Atlas (normalizedData q) k) (c : Fin a.C) : Set Incidence :=
  (incidenceEquiv q k (a.γ c)).symm '' a.F c

noncomputable def originalCoveredMass {p : SourceData} (q : Certificate p) (k : ℕ)
    (a : Atlas (normalizedData q) k) : ENNReal :=
  ∑ c, ENNReal.ofReal (p.ω (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))) *
    ((p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))).prod volume)
      (originalEvent q k a c)

noncomputable def normalizer {p : SourceData} (q : Certificate p) (k : ℕ) : ℝ :=
  (q.sequence.atlas k).system.normZ (p.ω (q.sequence.index k)) (p.ν (q.sequence.index k))

theorem normalizer_pos {p : SourceData} (hp : p.Valid) (q : Certificate p) (k : ℕ) :
    0 < normalizer q k := by
  obtain ⟨_, _, hs⟩ := hp.sampleProblem
  have hκ : 0 < (q.sequence.atlas k).κ := by linarith [q.sequence.slack_one k]
  exact (inv_pos.mpr hκ).trans_le ((q.sequence.valid k).normalizer_lower
    (hs (q.sequence.index k)).prob (hs (q.sequence.index k)).weight_nonneg hκ)

theorem measurableSet_originalEvent {p : SourceData} (q : Certificate p)
    {k M D : ℕ} {r : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) (c : Fin a.C) :
    MeasurableSet (originalEvent q k a c) := by
  obtain ⟨_, _, _, _, _, _, _, hF, _, _, _, _⟩ := ha.2.2.1 c
  exact (incidenceEquiv q k (a.γ c)).symm.measurableSet_image.mpr hF

/-- The recovered incidence event is a subset of the original parent event. -/
theorem originalEvent_subset_parent {p : SourceData} (q : Certificate p)
    {k M D : ℕ} {r : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) (c : Fin a.C) :
    originalEvent q k a c ⊆ (q.sequence.atlas k).F (a.γ c) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := ha.2.2.1 c
  rintro _ ⟨z, hz, rfl⟩
  exact (q.remainder.event_subset k (a.γ c) (hsel z hz).1).2.2

theorem originalEvent_subset_original {p : SourceData} (q : Certificate p)
    {k M D : ℕ} {r : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) (c : Fin a.C) :
    originalEvent q k a c ⊆ p.E (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c)) := by
  obtain ⟨_, _, _, _, hcharts, _⟩ := q.sequence.valid k
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := hcharts (a.γ c)
  intro z hz
  exact (hsel z (originalEvent_subset_parent q ha c hz)).1

theorem originalEvent_subset_assignment {p : SourceData} (q : Certificate p)
    {k M D : ℕ} {r : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) (c : Fin a.C) :
    originalEvent q k a c ⊆ originalAssignment q k a c ×ˢ (univ : Set ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := ha.2.2.1 c
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨⟨(q.remainder.event_subset k (a.γ c) (hsel z hz).1).1, ?_⟩, mem_univ _⟩
  change (NormalizedAssignments.trajectoryEquiv _ _ (parent_det_ne_zero q k (a.γ c)))
    ((NormalizedAssignments.trajectoryEquiv _ _ (parent_det_ne_zero q k (a.γ c))).symm
      z.1) ∈ a.A c
  simpa only [MeasurableEquiv.apply_symm_apply] using (hsel z hz).2.1

theorem originalEvent_eq_pullback {p : SourceData} (q : Certificate p)
    {k M D : ℕ} {r : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) (c : Fin a.C) :
    originalEvent q k a c =
      ((q.sequence.atlas k).A (a.γ c) ×ˢ (univ : Set ℝ)) ∩
        incidenceEquiv q k (a.γ c) ⁻¹' a.F c := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsel, _⟩ := ha.2.2.1 c
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨(q.remainder.event_subset k (a.γ c) (hsel z hz).1).1, mem_univ _⟩, ?_⟩
    simpa only [Set.mem_preimage, MeasurableEquiv.apply_symm_apply] using hz
  · rintro ⟨_, hx⟩
    exact ⟨_, hx, (incidenceEquiv q k (a.γ c)).symm_apply_apply x⟩

theorem original_event_mass {p : SourceData} (hp : p.Valid) (q : Certificate p)
    {k M D : ℕ} {r : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) (c : Fin a.C) :
    ((p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))).prod volume)
        (originalEvent q k a c) =
      ENNReal.ofReal ((1 / (2 : ℝ) ^ (q.sequence.atlas k).T) *
        (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))
          ((q.sequence.atlas k).A (a.γ c))).toReal) *
        (((normalizedData q).ν k (a.γ c)).prod volume) (a.F c) := by
  obtain ⟨_, _, hs⟩ := hp.sampleProblem
  letI : IsProbabilityMeasure
      (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))) :=
    (hs (q.sequence.index k)).prob _
  obtain ⟨_, _, _, _, hcharts, _⟩ := q.sequence.valid k
  obtain ⟨_, _, _, _, _, _, hA, _, _, _, _, _⟩ := hcharts (a.γ c)
  obtain ⟨_, _, _, _, _, _, _, hF, _, _, _, _⟩ := ha.2.2.1 c
  have hpos : p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))
      ((q.sequence.atlas k).A (a.γ c)) ≠ 0 := by
    intro hz
    have h := q.remainder.prior_positive k (a.γ c)
    simp only [hz, ENNReal.toReal_zero, lt_self_iff_false] at h
  rw [originalEvent_eq_pullback q ha c,
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ (q.sequence.atlas k).T),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact Submission.Obl.k4_native_finite_terminal_atlas_lift.assigned_product_pullback
    _ _ hA hpos (measure_ne_top _ _)
    (NormalizedAssignments.trajectoryEquiv _ _ (parent_det_ne_zero q k (a.γ c)))
    _ _ (by positivity) _ hF

/-- Original world weights restore the full prior-and-time budgets exactly,
even when many children have the same parent world. -/
theorem original_covered_mass {p : SourceData} (hp : p.Valid) (q : Certificate p)
    {k M D : ℕ} {r : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) :
    originalCoveredMass q k a = ENNReal.ofReal (normalizer q k) * a.mass := by
  obtain ⟨_, _, hs⟩ := hp.sampleProblem
  rw [Atlas.mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [original_event_mass hp q ha c]
  apply Submission.Obl.k4_native_finite_terminal_atlas_lift.weighted_conditional_mass
    ((hs (q.sequence.index k)).weight_nonneg _) (normalizer_pos hp q k)
  change _ / normalizer q k = _
  dsimp only [Submission.Obl.k4_remainder_pure_profile_normalization.Atlas.system]
  ring

/-- The recovered actual events retain an inverse product of the actual parent
and child slacks on the original weighted law. -/
theorem original_coverage_lower {p : SourceData} (hp : p.Valid) (q : Certificate p)
    {k M D : ℕ} {r : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) (hκ : 0 < a.κ) :
    ENNReal.ofReal (((q.sequence.atlas k).κ * a.κ)⁻¹) ≤ originalCoveredMass q k a := by
  obtain ⟨_, _, hs⟩ := hp.sampleProblem
  have hparent : 0 < (q.sequence.atlas k).κ := by linarith [q.sequence.slack_one k]
  rw [original_covered_mass hp q ha]
  exact Submission.Obl.k4_native_finite_terminal_atlas_lift.retained_mass_lift hparent hκ
    ((q.sequence.valid k).normalizer_lower (hs (q.sequence.index k)).prob
      (hs (q.sequence.index k)).weight_nonneg hparent) ha.2.2.2

theorem original_coverage_power_lower {p : SourceData} (hp : p.Valid) (q : Certificate p)
    {k M D : ℕ} {r ε : ℝ} {a : Atlas (normalizedData q) k}
    (ha : a.TrueAt M D r) (hκ : 1 ≤ a.κ)
    (hparent : (q.sequence.atlas k).κ ≤ p.N (q.sequence.index k) ^ (ε / 2))
    (hchild : a.κ ≤ p.N (q.sequence.index k) ^ (ε / 2)) :
    ENNReal.ofReal (p.N (q.sequence.index k) ^ (-ε)) ≤ originalCoveredMass q k a := by
  have hN : 0 < p.N (q.sequence.index k) := by linarith [hp.1 (q.sequence.index k)]
  have hproduct : (q.sequence.atlas k).κ * a.κ ≤ p.N (q.sequence.index k) ^ ε := by
    calc
      _ ≤ p.N (q.sequence.index k) ^ (ε / 2) *
          p.N (q.sequence.index k) ^ (ε / 2) :=
        mul_le_mul hparent hchild (by linarith) (Real.rpow_nonneg hN.le _)
      _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
  have hinv : p.N (q.sequence.index k) ^ (-ε) ≤
      ((q.sequence.atlas k).κ * a.κ)⁻¹ := by
    rw [Real.rpow_neg hN.le]
    exact inv_anti₀ (mul_pos (by linarith [q.sequence.slack_one k]) (by linarith)) hproduct
  exact (ENNReal.ofReal_le_ofReal hinv).trans
    (original_coverage_lower hp q ha (by linarith))

/-- Genuine small saturated packets have measurable events inside the original
problem, balanced original prior masses, and inverse-subpower original coverage.
All format bounds are fixed before the arbitrary inner loss. -/
theorem exists_balanced_covered_systems (hi : InitialHorizon) {p : SourceData}
    (hp : p.Valid) (hL : p.L = 1) (q : Certificate p)
    {b d D err : ℝ} (hb : 0 < b) (hb₁ : 2 * b ≤ 1)
    (hD : 0 < D) (hD₁ : D < 1) (hdD : d < D)
    (hold : |p.f 1 - d| ≤ err)
    (hprofile : ∀ s ∈ Icc (0 : ℝ) 1,
      |q.remainder.f s - q.remainder.f 0 - d * s| ≤ err)
    (hsmall : 2 * err ≤ (D - d) * b) :
    ∃ r ∈ Icc b (2 * b), ∀ h : ℝ, 2 * b < h →
      ∃ M₁ D₁ : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
        ∃ a : Atlas (normalizedData q) k,
          1 ≤ a.κ ∧ (normalizedData q).K k ≤ a.κ ∧
          a.κ ≤ (normalizedData q).N k ^ ε ∧
          (2 : ℝ) ^ a.T ≤ (normalizedData q).N k ^ h ∧ a.SaturatedAt M₁ D₁ r ∧
          ENNReal.ofReal (p.N (q.sequence.index k) ^ (-ε)) ≤ originalCoveredMass q k a ∧
          ∀ c, MeasurableSet (originalAssignment q k a c) ∧
            MeasurableSet (originalEvent q k a c) ∧
            originalEvent q k a c ⊆
              p.E (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c)) ∧
            originalEvent q k a c ⊆ originalAssignment q k a c ×ˢ (univ : Set ℝ) ∧
            p.N (q.sequence.index k) ^ (-d * r - (3 * err + ε)) ≤
              originalMass q k a c / |(composedFrame q k a c).det| ∧
            originalMass q k a c / |(composedFrame q k a c).det| ≤
              p.N (q.sequence.index k) ^ (-d * r + (3 * err + ε)) := by
  obtain ⟨r, hr, hs⟩ := exists_balanced_systems hi hp hL q hb hb₁ hD hD₁ hdD
    hold hprofile hsmall
  refine ⟨r, hr, fun h hh => ?_⟩
  obtain ⟨M₁, D₁, hs⟩ := hs h hh
  refine ⟨M₁, D₁, fun ε hε => ?_⟩
  apply ((hs (ε / 2) (half_pos hε)).and_eventually
    (q.sequence.slack_subpower (ε / 2) (half_pos hε))).mono
  rintro k ⟨⟨a, hκ, hK, hκN, hT, ha, hband⟩, hparent⟩
  have hN : 1 ≤ (normalizedData q).N k := by
    change 1 ≤ p.N (q.sequence.index k)
    linarith [hp.1 (q.sequence.index k)]
  refine ⟨a, hκ, hK, hκN.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hT, ha,
    original_coverage_power_lower hp q ha.1 hκ hparent hκN, fun c => ?_⟩
  obtain ⟨hA, hlo, hhi⟩ := hband c
  refine ⟨hA, measurableSet_originalEvent q ha.1 c,
    originalEvent_subset_original q ha.1 c, originalEvent_subset_assignment q ha.1 c, ?_⟩
  simpa only [show 2 * (ε / 2) = ε by ring] using And.intro hlo hhi

end OriginalPacketCoverage
end Submission.Obl.k4_balanced_native_packet_transport.CPF
