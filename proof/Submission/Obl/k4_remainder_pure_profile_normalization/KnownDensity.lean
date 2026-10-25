/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/KnownDensity.lean.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.KnownSystem
import Submission.Obl.k4_remainder_pure_profile_normalization.ListDensity
import Submission.Obl.k4_remainder_pure_profile_normalization.ObservationImages

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory Set
open scoped ENNReal

noncomputable def Atlas.selectedMeasure {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) :
    Measure Incidence := ((p.ν k (a.γ b)).prod volume).restrict (a.F b)

noncomputable def Atlas.terminalObservation {p : Data} {k : ℕ} (a : Atlas p k)
    (b : Fin a.C) : Incidence → Observation := obs (p.B k (a.γ b)) (δ (p.N k) p.L)

theorem KnownSystem.Valid.chart {p : Data} {k M D : ℕ} {r : ℝ}
    {s : KnownSystem p k} (hs : s.Valid M D r) (b : Fin s.atlas.C) :
    Chart (p.N k) M D s.atlas.κ s.atlas.T (s.atlas.j b : ℝ) r
      (p.B k (s.atlas.γ b)) (p.E k (s.atlas.γ b)) (s.atlas.c b) (s.atlas.u b)
      (s.atlas.Q b) (s.atlas.R b) (s.atlas.A b) (s.atlas.F b)
      (∀ x ∈ s.atlas.F b, b ∈ s.lists (s.atlas.γ b) (s.atlas.terminalObservation b x)) :=
  hs.2.2.2.1 b

/-- Any measurable versions of the label densities vanish outside the original
known lists.  No measurability is required of those lists. -/
theorem KnownSystem.Valid.density_support {p : Data} {k M D : ℕ} {r : ℝ}
    {s : KnownSystem p k} (hs : s.Valid M D r)
    (g : Fin s.atlas.C → Observation → ENNReal) (hg : ∀ b, Measurable (g b))
    (hlaw : ∀ b, (s.atlas.selectedMeasure b).map (s.atlas.terminalObservation b) =
      (volume.prod Measure.count).withDensity (g b)) :
    ∀ᵐ o ∂(volume.prod Measure.count), ∀ b,
      b ∉ s.lists (s.atlas.γ b) o → g b o = 0 := by
  classical
  let L (o : Observation) : Finset (Fin s.atlas.C) :=
    Finset.univ.filter (fun b => b ∈ s.lists (s.atlas.γ b) o)
  have hobs (b : Fin s.atlas.C) : Measurable (s.atlas.terminalObservation b) :=
    Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _
  have hF (b : Fin s.atlas.C) : MeasurableSet (s.atlas.F b) := by
    rcases hs.chart b with ⟨_, _, _, _, _, _, _, hF, _⟩
    exact hF
  have hz (b : Fin s.atlas.C) : s.atlas.selectedMeasure b (s.atlas.F b)ᶜ = 0 := by
    rw [Atlas.selectedMeasure, Measure.restrict_apply' (hF b)]
    simp
  have him (b : Fin s.atlas.C) :
      MeasurableSet (s.atlas.terminalObservation b '' s.atlas.F b) :=
    (hs.chart b).obs_image_measurable _ _
  have hlabel (b : Fin s.atlas.C) (a : Incidence) (ha : a ∈ s.atlas.F b) :
      b ∈ L (s.atlas.terminalObservation b a) := by
    rcases hs.chart b with ⟨_, _, _, _, _, _, _, _, _, _, _, hex⟩
    simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and] using hex a ha
  have h := refined_density_support_of_images s.atlas.selectedMeasure
    (volume.prod Measure.count) s.atlas.terminalObservation hobs g hg hlaw s.atlas.F hz him L hlabel
  filter_upwards [h] with o ho
  intro b hb
  apply ho b
  simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and] using hb

/-- The low-ratio exceptional mass in any one original world is charged to
its original density with only the known-list cardinality loss. -/
theorem KnownSystem.Valid.world_lowDensity_mass {p : Data} {k M D : ℕ} {r : ℝ}
    {s : KnownSystem p k} (hs : s.Valid M D r)
    (g : Fin s.atlas.C → Observation → ENNReal) (hg : ∀ b, Measurable (g b))
    (hlaw : ∀ b, (s.atlas.selectedMeasure b).map (s.atlas.terminalObservation b) =
      (volume.prod Measure.count).withDensity (g b))
    (f : Observation → ENNReal) (hf : Measurable f) (γ : Fin (p.W k)) (ε : ENNReal) :
    (∑ b : {b : Fin s.atlas.C // s.atlas.γ b = γ},
      s.atlas.selectedMeasure b.1 {a |
        g b.1 (s.atlas.terminalObservation b.1 a) < ε * f (s.atlas.terminalObservation b.1 a)}) ≤
      ε * ENNReal.ofReal s.atlas.κ * ∫⁻ o, f o ∂(volume.prod Measure.count) := by
  classical
  let L (o : Observation) : Finset {b : Fin s.atlas.C // s.atlas.γ b = γ} :=
    (s.lists γ o).subtype (fun b => s.atlas.γ b = γ)
  have hcard (o : Observation) : ((L o).card : ENNReal) ≤ ENNReal.ofReal s.atlas.κ := by
    calc
      ((L o).card : ENNReal) ≤ ((s.lists γ o).card : ENNReal) := by
        dsimp [L]
        rw [Finset.card_subtype]
        exact_mod_cast Finset.card_filter_le (s.lists γ o) (fun b => s.atlas.γ b = γ)
      _ ≤ ENNReal.ofReal s.atlas.κ := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (hs.2.2.1 γ o)
  have hsupport : ∀ᵐ o ∂(volume.prod Measure.count),
      ∀ b : {b : Fin s.atlas.C // s.atlas.γ b = γ}, b ∉ L o → g b.1 o = 0 := by
    filter_upwards [hs.density_support g hg hlaw] with o ho
    intro b hb
    apply ho b.1
    simpa only [L, Finset.mem_subtype, b.2] using hb
  exact observation_list_refinement_lowDensity_mass
    (fun b : {b : Fin s.atlas.C // s.atlas.γ b = γ} => s.atlas.selectedMeasure b.1)
    (volume.prod Measure.count) (fun b => s.atlas.terminalObservation b.1)
    (fun _ => Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _)
    ε (ENNReal.ofReal s.atlas.κ) f (fun b => g b.1) hf (fun b => hg b.1)
    (fun b => hlaw b.1) L hcard hsupport

/-- Sum the same estimate with the original world weights.  The source laws,
observations and lists remain those of the actual selected chart events. -/
theorem KnownSystem.Valid.weighted_lowDensity_mass {p : Data} {k M D : ℕ} {r : ℝ}
    {s : KnownSystem p k} (hs : s.Valid M D r)
    (g : Fin s.atlas.C → Observation → ENNReal) (hg : ∀ b, Measurable (g b))
    (hlaw : ∀ b, (s.atlas.selectedMeasure b).map (s.atlas.terminalObservation b) =
      (volume.prod Measure.count).withDensity (g b))
    (f : Fin (p.W k) → Observation → ENNReal) (hf : ∀ γ, Measurable (f γ))
    (ω : Fin (p.W k) → ENNReal) (ε : ENNReal) :
    (∑ b, ω (s.atlas.γ b) * s.atlas.selectedMeasure b {a |
      g b (s.atlas.terminalObservation b a) < ε * f (s.atlas.γ b) (s.atlas.terminalObservation b a)}) ≤
      ε * ENNReal.ofReal s.atlas.κ *
        ∑ γ, ω γ * ∫⁻ o, f γ o ∂(volume.prod Measure.count) := by
  classical
  let m (b : Fin s.atlas.C) := s.atlas.selectedMeasure b {a |
    g b (s.atlas.terminalObservation b a) < ε * f (s.atlas.γ b) (s.atlas.terminalObservation b a)}
  calc
    (∑ b, ω (s.atlas.γ b) * m b) =
        ∑ γ, ∑ b : {b : Fin s.atlas.C // s.atlas.γ b = γ}, ω (s.atlas.γ b.1) * m b.1 :=
      (Fintype.sum_fiberwise s.atlas.γ (fun b => ω (s.atlas.γ b) * m b)).symm
    _ = ∑ γ, ω γ * ∑ b : {b : Fin s.atlas.C // s.atlas.γ b = γ},
        s.atlas.selectedMeasure b.1 {a |
          g b.1 (s.atlas.terminalObservation b.1 a) < ε * f γ (s.atlas.terminalObservation b.1 a)} := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [m, b.2]
    _ ≤ ∑ γ, ω γ * (ε * ENNReal.ofReal s.atlas.κ *
        ∫⁻ o, f γ o ∂(volume.prod Measure.count)) := by
      apply Finset.sum_le_sum
      intro γ _
      exact mul_le_mul' le_rfl (hs.world_lowDensity_mass g hg hlaw (f γ) (hf γ) γ ε)
    _ = ε * ENNReal.ofReal s.atlas.κ *
        ∑ γ, ω γ * ∫⁻ o, f γ o ∂(volume.prod Measure.count) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      ring

end Submission.Obl.k4_remainder_pure_profile_normalization
