import Submission.Obl.k4_scalar_grid_cartesian_field.PreparationChoices
import Submission.Obl.k4_scalar_grid_cartesian_field.SourceReady
import Submission.Obl.k4_scalar_grid_cartesian_field.SourceGeometry
import Submission.Obl.k4_scalar_grid_cartesian_field.OriginalBaseCeiling
import Submission.Obl.k4_scalar_grid_cartesian_field.OriginalCaps
import Submission.Obl.k4_scalar_grid_cartesian_field.PrepSupport
import Submission.Obl.k4_scalar_grid_cartesian_field.DensityRestriction

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- The frozen preparation and the global choices provide ready packets at every compact range. -/
theorem PreparationChoices.ready_eventually (data : Data) (hs : scaleHyp data) (hb : baseHyp data)
    (hcap : capHyp data) (H₀ : ℕ → ℝ)
    (θ : (k : ℕ) → Fin (data.W k) → Measure Trajectory)
    (E₀ : (k : ℕ) → Fin (data.W k) → Set Incidence)
    (hp : prepData data H₀ θ E₀) (c : PreparationChoices data H₀ E₀)
    (R : ℝ) (hR : 1 < R) :
    ∀ᶠ k in atTop, Nonempty (ReadyPacket data k c.M (c.Λ k) c.B R) := by
  obtain ⟨grid, hgrid, hsupport⟩ := prep_registered_support data H₀ θ E₀ hp
  have hH₀ := hp.1
  obtain ⟨_, _, _, hprep⟩ := hp
  have hκ : 0 < data.κ := hs.2.2.2.2.2.1
  have hκone : data.κ ≤ 1 := hs.2.2.2.2.2.2.1
  have hd : 0 ≤ data.d := hs.2.2.2.1
  have hdone : data.d ≤ 1 := hs.2.2.2.2.1.le
  have hN : ∀ k, 1 ≤ data.N k := fun k => by linarith [hs.1 k]
  have hsmall := eventually_polynomial_subpower_le hN hs.2.1 hs.2.2.1
    (by norm_num : (1 : ℝ) ≤ 2880) 3 (by norm_num : (0 : ℝ) < 9)
  let R' := max R 21
  have hR' : 1 < R' := hR.trans_le (le_max_left _ _)
  have hinv : R'⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < R) (le_max_left R 21)
  have h20lo : R'⁻¹ ≤ (20 : ℝ) := (inv_le_one_of_one_le₀ hR'.le).trans (by norm_num)
  have h20hi : (20 : ℝ) ≤ R' := (by norm_num : (20 : ℝ) ≤ 21).trans (le_max_right _ _)
  filter_upwards [c.sources, c.separation, c.separation_cap,
    hsupport (c.B + 2) (by linarith [c.hB]), hprep 2 (by norm_num),
    c.graph.2.2 8 (by norm_num), original_base_rectangle_cap data hs hcap,
    original_angular_cap_compact data hcap R hR,
    original_physical_palette_compact data hs hcap (B := c.B) (by linarith [c.hB]) R' hR',
    core_precision_eventually data hs c.subpower_Λ c.hκM c.hB,
    hs.2.2.1.2 (1 / 6) (by norm_num), hs.2.2.1.2 (data.κ / 2) (by positivity), hsmall]
    with k hsources hseparation hsepcap hregistered hpdata hgdata hbasecap hangular hphysical hprecision hK₁ hKκ hsm
  obtain ⟨s⟩ := hsources
  let g := data.γ k 1 s.i
  have hNk := hs.1 k
  have hNp : 0 < data.N k := by linarith
  have hK := s.original.budget_one
  have hKp : 0 < data.K k := by linarith
  have hHp : 0 < c.H k := by linarith [c.graph.1.1 k]
  have hH₀p : 0 < H₀ k := by linarith [hH₀.1 k]
  obtain ⟨hEm, hEE₀, hgraph, hcoarse, _⟩ := hgdata.2 g
  have hsource : s.S ⊆ E₀ k g := fun x hx => hEE₀ (s.subset_E hx)
  let Band : Set ℝ := Icc R'⁻¹ R' ∪ {c.β k}
  have hraw : ∀ r ∈ Band, ∀ (q : Fin 3 → ℤ) (v : ℤ), data.ρ k g
      {x | physCube (data.N k) c.B x = q ∧ x.1.2 1 ∈ vel data k r v} ≤
      ENNReal.ofReal (data.K k * (data.N k ^ (-c.B)) ^ (2 + data.d)) * data.π k g (vel data k r v) := by
    intro r hr q v
    rcases hr with hr | hr
    · exact hphysical g r hr.1 hr.2 q v
    · have heq : r = c.β k := hr
      subst r
      exact hsepcap g q v
  obtain ⟨r⟩ := refine_source_packet s hNk hκone hd hdone (hH₀.1 k) (c.graph.1.1 k)
    (c.geometry k).1 c.hB (grid k) (hgrid k).1 (hgrid k).2 (E₀ k g) hsource
    (hregistered g) Band hraw
  have hh := s.original.positive_horizon
  have hμ : (data.ρ k g).restrict r.S₀ ≤ data.ρ k g := Measure.restrict_le_self
  have hμsource : (data.ρ k g).restrict r.S₀ ≤ (data.ρ k g).restrict s.S :=
    Measure.restrict_mono_set _ r.subset_source
  have hmem : ∀ᵐ x ∂(data.ρ k g).restrict r.S₀,
      x ∈ {x | x.1 ∈ data.A k 1 s.i ∧ x.2 ∈ I data (data.T k 1) (data.j k 1 s.i)} := by
    filter_upwards [ae_restrict_mem r.measurable_S₀] with x hx
    exact s.subset_packet (r.subset_source hx)
  have hnormalized := s.original.normalized_base_cap hNp ((data.ρ k g).restrict r.S₀) hμ
    (ae_iff.mp hmem) (hbasecap g) hsm
  obtain ⟨hθle, hθmass, _, _, _, hdensitylo, hdensityhi, _⟩ := hpdata.2 g
  have hθfinite : IsFiniteMeasure (θ k g) := ⟨lt_of_le_of_lt hθmass (by simp)⟩
  obtain ⟨hdlo, hdhi⟩ := original_two_sided_density (data.ρ k g) ((θ k g).prod volume)
    hH₀p hEE₀ hdensitylo hdensityhi
  obtain ⟨hhorlo, _⟩ := horizon_power_bounds hNk hKp hκone hK₁ hKκ
    s.original.horizon_lower s.original.horizon_upper
  obtain ⟨rT, hrTlo, hrThi, herror⟩ := field_error_exponent hNk hh s.original.bounded_horizon hhorlo
  have hcore : SourceCoreInput s r (c.Λ k) (c.β k) rT (θ k g) := {
    hN := hNk, hΛ := c.subpower_Λ.1 k, hH := c.graph.1.1 k, hH₀ := hH₀.1 k
    budget := c.budget k, geometry_base := (c.geometry k).1, geometry_layer := (c.geometry k).2
    precision := hprecision _ hh s.original.bounded_horizon s.original.horizon_lower s.original.horizon_upper
    error_eq := herror, qualification_budget := c.qualification_budget k, hβ := c.positive_β k
    separation_budget := c.separation_budget k, band_velocity := Or.inl ⟨h20lo, h20hi⟩
    band_separation := Or.inr rfl, finite_ρ := original_finite_of_base data hb k g
    finite_θ := hθfinite, measurable_E := hEm, lower_graph_density := hdlo, upper_graph_density := hdhi
    graph_bound := by simpa only [phys_eq_physCube] using hgraph
    coarse_lists := by
      intro q
      simpa only [phys_eq_physCube, rowbin_eq_rowBin] using
        hcoarse rT (by norm_num; linarith) (by linarith) (by linarith) q
    separation := hseparation g, base_ceiling := hnormalized }
  refine ⟨sourceReady s r (θ k g) hcore hrTlo ?_ (hangular g) ?_⟩
  · intro v hv₀ hv₁
    exact hphysical g v (hinv.trans hv₀) (hv₁.trans (le_max_left _ _))
  · intro w hw₀ hw₁
    have hhor : data.N k ^ (-2 : ℝ) ≤ packetLength data k :=
      (Real.rpow_le_rpow_of_exponent_le (hN k) (by norm_num : (-2 : ℝ) ≤ -7 / 6)).trans hhorlo
    exact s.joint_support hNk hκone hd hdone (hH₀.1 k) (c.geometry k).1 (grid k) (hgrid k).1
      (hgrid k).2 (E₀ k g) hsource (by linarith [c.hB] : 3 ≤ c.B + 2) (hregistered g)
      ((data.ρ k g).restrict r.S₀) hμsource hhor w hw₀ hw₁

/-- Complete preparation contract used by the outer field theorem. -/
theorem exists_ready_packets (data : Data) (hs : scaleHyp data) (hb : baseHyp data)
    (hcap : capHyp data) (hpacket : packetHyp data)
    (H₀ : ℕ → ℝ) (θ : (k : ℕ) → Fin (data.W k) → Measure Trajectory)
    (E₀ : (k : ℕ) → Fin (data.W k) → Set Incidence)
    (hp : prepData data H₀ θ E₀) (hq : qualOracle data E₀) :
    ∃ (M : ℕ) (Λ : ℕ → ℝ) (B : ℝ), 2 ≤ M ∧ subpower data Λ ∧ 20 ≤ B ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, Nonempty (ReadyPacket data k M (Λ k) B R) := by
  obtain ⟨c⟩ := exists_preparation_choices data hs hb hcap hpacket H₀ hp.1 E₀ hq
  exact ⟨c.M, c.Λ, c.B, c.hM, c.subpower_Λ, by linarith [c.hB],
    c.ready_eventually data hs hb hcap H₀ θ E₀ hp⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
