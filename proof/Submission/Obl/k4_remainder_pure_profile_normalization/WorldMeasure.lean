/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/WorldMeasure.lean.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.NativeDepth
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Set MeasureTheory Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open scoped ENNReal Topology

abbrev Data.SampleState (p : Data) (k : ℕ) := Fin (p.W k) × Incidence

/-- The exact original weighted law, retaining the world as a visible tag. -/
noncomputable def Data.sampleMeasure (p : Data) (k : ℕ) : Measure (p.SampleState k) :=
  Measure.sum (fun γ => ENNReal.ofReal (p.ω k γ) •
    (p.incidenceMeasure k γ).map (fun a : Incidence => (γ, a)))

noncomputable def Data.sampledDensity (p : Data) (r : ℝ) (k : ℕ)
    (a : p.SampleState k) : ENNReal :=
  p.g k a.1 r (obs (p.B k a.1) (δ (p.N k) r) a.2)

theorem Data.sampleMeasure_apply (p : Data) (k : ℕ) {A : Set (p.SampleState k)}
    (hA : MeasurableSet A) :
    p.sampleMeasure k A = ∑ γ, ENNReal.ofReal (p.ω k γ) *
      p.incidenceMeasure k γ ((fun a : Incidence => (γ, a)) ⁻¹' A) := by
  rw [Data.sampleMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  apply Finset.sum_congr rfl
  intro γ _
  have hι : Measurable (fun a : Incidence => (γ, a)) :=
    measurable_const.prodMk measurable_id
  rw [Measure.smul_apply, Measure.map_apply hι hA]
  rfl

theorem Data.Valid.measurable_sampledDensity {p : Data} (hp : p.Valid)
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L) (k : ℕ) : Measurable (p.sampledDensity r k) := by
  apply measurable_from_prod_countable_right
  intro γ
  change Measurable (fun a : Incidence =>
    p.g k γ r (obs (p.B k γ) (δ (p.N k) r) a))
  exact (hp.2.2.2.2.2.2.2.2.2.1 k γ r hr hrL).1.comp
    (Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation
      (p.B k γ) (δ (p.N k) r))

theorem Data.Valid.sampledDensity_antitone {p : Data} (hp : p.Valid)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hsL : s ≤ p.L) (k : ℕ) :
    ∀ᵐ a ∂p.sampleMeasure k, p.sampledDensity s k a ≤ p.sampledDensity r k a := by
  apply Measure.ae_sum_iff.mpr
  intro γ
  apply Measure.smul_absolutelyContinuous
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
    (measurableSet_le (hp.measurable_sampledDensity (hr.trans hrs) hsL k)
      (hp.measurable_sampledDensity hr (hrs.trans hsL) k))).mpr
  exact hp.density_antitone k γ hr hrs hsL

/-- The frozen weighted exceptional-mass clause is precisely typicality on the
world-tagged original probability space. -/
theorem Data.Valid.sampledDensity_typical {p : Data} (hp : p.Valid)
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L) :
    HasTypicalDensity p.N p.sampleMeasure (p.sampledDensity r) (p.f r) := by
  intro τ hτ
  have hvalid := hp
  obtain ⟨_, _, _, _, _, _, _, _, hrest⟩ := hvalid
  obtain ⟨c, hc, hb⟩ := hrest.2.2.2.2.1 r τ hr hrL hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb] with k hk
  have hA : MeasurableSet {a : p.SampleState k |
      p.sampledDensity r k a < ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ∨
      ENNReal.ofReal (p.N k ^ (-p.f r + τ)) < p.sampledDensity r k a} :=
    (measurableSet_lt (hp.measurable_sampledDensity hr hrL k) measurable_const).union
      (measurableSet_lt measurable_const (hp.measurable_sampledDensity hr hrL k))
  rw [Data.sampleMeasure_apply _ _ hA]
  exact hk

end Submission.Obl.k4_remainder_pure_profile_normalization
