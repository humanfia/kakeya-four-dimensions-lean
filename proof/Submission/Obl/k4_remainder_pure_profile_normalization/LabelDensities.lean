/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/LabelDensities.lean.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.KnownDensity
import Submission.Obl.k4_remainder_pure_profile_normalization.NativeDepth
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.IncidenceTransport

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory Set
open scoped ENNReal

/-- Canonical densities of the actual selected chart events at every depth. -/
noncomputable def Atlas.labelDensity {p : Data} {k : ℕ} (a : Atlas p k) (t : ℝ)
    (b : Fin a.C) : Observation → ENNReal :=
  ((a.selectedMeasure b).map (obs (p.B k (a.γ b)) (δ (p.N k) t))).rnDeriv
    (volume.prod Measure.count)

theorem Atlas.measurable_labelDensity {p : Data} {k : ℕ} (a : Atlas p k) (t : ℝ)
    (b : Fin a.C) : Measurable (a.labelDensity t b) := Measure.measurable_rnDeriv _ _

/-- The canonical label densities have the exact observation map law throughout
the original depth interval. -/
theorem KnownSystem.Valid.labelDensity_law {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r)
    {t : ℝ} (ht : 0 ≤ t) (htL : t ≤ p.L) (b : Fin s.atlas.C) :
    (s.atlas.selectedMeasure b).map (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t)) =
      (volume.prod Measure.count).withDensity (s.atlas.labelDensity t b) := by
  let μ : Measure Observation := volume.prod Measure.count
  obtain ⟨hN, hlim, hK, hL, hd, hd1, hS, hη, hrest⟩ := hp
  obtain ⟨M₀, D₀, hfinite⟩ := hrest.1
  obtain ⟨hW, hω, hsum, hworld, hmass⟩ := hfinite k
  obtain ⟨hprob, hB, hBm, hBinv, hdeg, hcoeff, hprior, hE, hEsupp,
    hbounds, hfmt, hgood, hderiv⟩ := hworld (s.atlas.γ b)
  haveI := hprob
  have hFE : s.atlas.F b ⊆ p.E k (s.atlas.γ b) := by
    rcases hs.chart b with ⟨_, _, _, _, _, _, _, _, _, _, hF, _⟩
    exact fun a ha => (hF a ha).1
  haveI : IsFiniteMeasure (s.atlas.selectedMeasure b) :=
    Submission.Obl.k4_dyadic_crop_affine_laws.Framework.finite_selected_incidence
      (p.ν k (s.atlas.γ b)) (s.atlas.F b) (hFE.trans hEsupp)
  have hobs : Measurable (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t)) :=
    Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _
  have hdom : (s.atlas.selectedMeasure b).map
      (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t)) ≤
      μ.withDensity (p.g k (s.atlas.γ b) t) := by
    have hle : s.atlas.selectedMeasure b ≤
        ((p.ν k (s.atlas.γ b)).prod volume).restrict (p.E k (s.atlas.γ b)) :=
      Measure.restrict_mono hFE le_rfl
    have hlaw := (hrest.2.1 k (s.atlas.γ b) t ht htL).2
    exact (Measure.map_mono hle hobs).trans_eq hlaw
  have hac : (s.atlas.selectedMeasure b).map
      (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t)) ≪ μ :=
    (Measure.absolutelyContinuous_of_le hdom).trans (withDensity_absolutelyContinuous _ _)
  exact (Measure.withDensity_rnDeriv_eq _ μ hac).symm

/-- Restricting each chart event gives actual measurable RN label densities at
the original terminal observation. -/
theorem KnownSystem.Valid.exists_terminal_label_densities {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r) :
    ∃ g : Fin s.atlas.C → Observation → ENNReal,
      (∀ b, Measurable (g b)) ∧
      ∀ b, (s.atlas.selectedMeasure b).map (s.atlas.terminalObservation b) =
        (volume.prod Measure.count).withDensity (g b) :=
  ⟨s.atlas.labelDensity p.L, s.atlas.measurable_labelDensity p.L,
    fun b => hs.labelDensity_law hp hp.L_pos.le le_rfl b⟩

/-- Selected label densities are bounded by the original world density at every
intermediate depth. -/
theorem KnownSystem.Valid.labelDensity_le {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r)
    {t : ℝ} (ht : 0 ≤ t) (htL : t ≤ p.L) (b : Fin s.atlas.C) :
    s.atlas.labelDensity t b ≤ᵐ[volume.prod Measure.count] p.g k (s.atlas.γ b) t := by
  rcases hs.chart b with ⟨_, _, _, _, _, _, _, hF, _, _, hsubset, _⟩
  have hFE : s.atlas.F b ⊆ p.E k (s.atlas.γ b) := fun a ha => (hsubset a ha).1
  have hres : (p.incidenceMeasure k (s.atlas.γ b)).restrict (s.atlas.F b) =
      s.atlas.selectedMeasure b := by
    rw [Data.incidenceMeasure, Measure.restrict_restrict hF, inter_eq_left.mpr hFE]
    rfl
  apply Submission.Lib.K4Homogenization.observation_restriction_density_le
    (p.incidenceMeasure k (s.atlas.γ b)) (volume.prod Measure.count) (s.atlas.F b)
    (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t))
    (Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _)
    (s.atlas.measurable_labelDensity t b)
    (hp.2.2.2.2.2.2.2.2.2.1 k (s.atlas.γ b) t ht htL).2
  rw [hres]
  exact hs.labelDensity_law hp ht htL b

theorem KnownSystem.Valid.sampled_labelDensity_le {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r)
    {t : ℝ} (ht : 0 ≤ t) (htL : t ≤ p.L) (b : Fin s.atlas.C) :
    ∀ᵐ a ∂s.atlas.selectedMeasure b,
      s.atlas.labelDensity t b (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t) a) ≤
        p.g k (s.atlas.γ b) t (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t) a) := by
  have hac : (s.atlas.selectedMeasure b).map
      (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t)) ≪ volume.prod Measure.count := by
    rw [hs.labelDensity_law hp ht htL b]
    exact withDensity_absolutelyContinuous _ _
  exact ae_of_ae_map
    (Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _).aemeasurable
    (hac.ae_le (hs.labelDensity_le hp ht htL b))

theorem KnownSystem.Valid.labelDensity_antitone {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r)
    {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (huL : u ≤ p.L) (b : Fin s.atlas.C) :
    ∀ᵐ a ∂s.atlas.selectedMeasure b,
      s.atlas.labelDensity u b (obs (p.B k (s.atlas.γ b)) (δ (p.N k) u) a) ≤
        s.atlas.labelDensity t b (obs (p.B k (s.atlas.γ b)) (δ (p.N k) t) a) :=
  obs_refinement_density_le (s.atlas.selectedMeasure b) (by linarith [hp.N_ge k])
    ht htu (p.B k (s.atlas.γ b)) _ _
    (s.atlas.measurable_labelDensity t b) (s.atlas.measurable_labelDensity u b)
    (hs.labelDensity_law hp ht (htu.trans huL) b)
    (hs.labelDensity_law hp (ht.trans htu) huL b)

/-- The original weighted terminal density has mass at most one. -/
theorem Data.Valid.weighted_terminal_density_mass_le_one {p : Data} (hp : p.Valid) (k : ℕ) :
    (∑ γ, ENNReal.ofReal (p.ω k γ) *
      ∫⁻ o, p.g k γ p.L o ∂(volume.prod Measure.count)) ≤ 1 := by
  obtain ⟨hN, hlim, hK, hL, hd, hd1, hS, hη, hrest⟩ := hp
  obtain ⟨M, D, hfinite⟩ := hrest.1
  obtain ⟨hW, hω, hsum, hworld, hmass⟩ := hfinite k
  have hmass_one (γ : Fin (p.W k)) :
      (∫⁻ o, p.g k γ p.L o ∂(volume.prod Measure.count)) ≤ 1 := by
    obtain ⟨hprob, hB, hBm, hBinv, hdeg, hcoeff, hprior, hE, hEsupp,
      hbounds, hfmt, hgood, hderiv⟩ := hworld γ
    haveI := hprob
    have hlaw := (hrest.2.1 k γ p.L hL.le le_rfl).2
    have hobs : Measurable (obs (p.B k γ) (δ (p.N k) p.L)) :=
      Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _
    calc
      (∫⁻ o, p.g k γ p.L o ∂(volume.prod Measure.count)) =
          ((p.ν k γ).prod volume) (p.E k γ) := by
        have h := congrArg (fun m : Measure Observation => m univ) hlaw
        simpa only [Measure.map_apply hobs MeasurableSet.univ, preimage_univ,
          Measure.restrict_apply_univ, withDensity_apply _ MeasurableSet.univ,
          Measure.restrict_univ] using h.symm
      _ ≤ ((p.ν k γ).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hEsupp
      _ = 1 := by simp
  calc
    (∑ γ, ENNReal.ofReal (p.ω k γ) *
      ∫⁻ o, p.g k γ p.L o ∂(volume.prod Measure.count)) ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) := by
      apply Finset.sum_le_sum
      intro γ _
      simpa only [mul_one] using (mul_le_mul' le_rfl (hmass_one γ))
    _ = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => hω γ), hsum]
      norm_num

/-- The exact terminal refinement estimate, including existence of all label
densities, follows from the frozen Problem and Known predicates. -/
theorem KnownSystem.Valid.terminal_refinement {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r) :
    ∃ g : Fin s.atlas.C → Observation → ENNReal,
      (∀ b, Measurable (g b)) ∧
      (∀ b, (s.atlas.selectedMeasure b).map (s.atlas.terminalObservation b) =
        (volume.prod Measure.count).withDensity (g b)) ∧
      ∀ ε : ENNReal, (∑ b, ENNReal.ofReal (p.ω k (s.atlas.γ b)) *
        s.atlas.selectedMeasure b {a | g b (s.atlas.terminalObservation b a) <
          ε * p.g k (s.atlas.γ b) p.L (s.atlas.terminalObservation b a)}) ≤
        ε * ENNReal.ofReal s.atlas.κ := by
  obtain ⟨g, hg, hlaw⟩ := hs.exists_terminal_label_densities hp
  refine ⟨g, hg, hlaw, fun ε => ?_⟩
  have hL := hp.L_pos
  have hf := fun γ => (hp.2.2.2.2.2.2.2.2.2.1 k γ p.L hL.le le_rfl).1
  have h := hs.weighted_lowDensity_mass g hg hlaw (fun γ => p.g k γ p.L) hf
    (fun γ => ENNReal.ofReal (p.ω k γ)) ε
  exact h.trans (by simpa only [mul_one] using
    (mul_le_mul' le_rfl (hp.weighted_terminal_density_mass_le_one k)))

/-- The terminal lower comparison holds for the same canonical family as the
intermediate upper comparison. -/
theorem KnownSystem.Valid.canonical_terminal_refinement {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {s : KnownSystem p k} (hs : s.Valid M D r) (ε : ENNReal) :
    (∑ b, ENNReal.ofReal (p.ω k (s.atlas.γ b)) *
      s.atlas.selectedMeasure b {a |
        s.atlas.labelDensity p.L b (s.atlas.terminalObservation b a) <
          ε * p.g k (s.atlas.γ b) p.L (s.atlas.terminalObservation b a)}) ≤
      ε * ENNReal.ofReal s.atlas.κ := by
  have hL := hp.L_pos
  have hf := fun γ => (hp.2.2.2.2.2.2.2.2.2.1 k γ p.L hL.le le_rfl).1
  have h := hs.weighted_lowDensity_mass (s.atlas.labelDensity p.L)
    (s.atlas.measurable_labelDensity p.L) (fun b => hs.labelDensity_law hp hL.le le_rfl b)
    (fun γ => p.g k γ p.L) hf (fun γ => ENNReal.ofReal (p.ω k γ)) ε
  exact h.trans (by simpa only [mul_one] using
    (mul_le_mul' le_rfl (hp.weighted_terminal_density_mass_le_one k)))

end Submission.Obl.k4_remainder_pure_profile_normalization
