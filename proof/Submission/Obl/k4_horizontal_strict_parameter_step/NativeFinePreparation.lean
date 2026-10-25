import Submission.Obl.k4_horizontal_strict_parameter_step.NativeDepthGrid
import Submission.Obl.k4_horizontal_strict_parameter_step.FiniteNativeEvent
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.Table
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeMesh
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.UniformBudgets

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

/-- Pointwise certificates for every native level needed by one scalar
preparation. All measures, assignments and affine fits are original. -/
structure NativeFinePreparation {α : Type} [MeasurableSpace α] (cfg : NativeModel α)
    (k : ℕ) (s E D : ℝ) where
  parent : cfg.AssignmentLevel k s
  grid : NativeDepthGrid (cfg.N k) s E
  child : ∀ j, cfg.AssignmentLevel k (grid.depth j)
  affine : ∀ j, NativeAffineTable cfg k (grid.depth j)
  event : Set (α × ℝ)
  measurable_event : MeasurableSet event
  conull : ∀ᵐ p ∂cfg.μ k, p ∈ event
  event_prop : ∀ p ∈ event, ∀ j,
    (∃ i, p.1 ∈ cfg.B k (grid.depth j) i ∧
      p.2 ∈ Data.I (cfg.T k (grid.depth j)) (cfg.j k (grid.depth j) i)) ∧
    ∀ block block' : Fin (2 ^ cfg.T k (grid.depth j)),
      p.2 ∈ Data.I (cfg.T k (grid.depth j)) block →
      p.2 ∈ Data.I (cfg.T k (grid.depth j)) block' → block = block'
  nested : ∀ j (i : Fin (cfg.n k (grid.depth j))), ∃ a : Fin (cfg.n k s),
    cfg.A k (grid.depth j) i ⊆ cfg.A k s a ∧
    Data.I (cfg.T k (grid.depth j)) (cfg.j k (grid.depth j) i) ⊆
      Data.I (cfg.T k s) (cfg.j k s a)
  large : 69120 * cfg.K k ^ 8 ≤ cfg.N k
  parameter_small : ∀ j, D ≤ cfg.timeLength k (grid.depth j) ^ 2
  caps : ∀ j, ∀ u ∈ ({s, grid.depth j} : Set ℝ), ∀ (Q : Fin 3 → ℤ) (a : ℤ),
    cfg.μ k {ω | cfg.z k (cfg.N k) (grid.depth j + 2) ω = Q ∧
      ⌊(cfg.x k ω.1 ω.2) 3 / cfg.N k ^ (-u)⌋ = a} ≤
        ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * (grid.depth j + 2) - cfg.d * u))
  contact_budget : ∀ j, 16 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) ≤ cfg.N k ^ (-grid.depth j)
  spatial_budget : ∀ j, 14155776 * cfg.K k ^ 10 * D ≤
    (cfg.N k ^ (-grid.depth j) / cfg.N k ^ (-s)) * cfg.timeLength k (grid.depth j) ^ 2

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Compact-range original hypotheses and the strict transverse gap prepare
the entire finite native grid at once, even though it depends on the sample. -/
theorem eventually_fine_preparation
    (hN : ∀ k, 2 ≤ cfg.N k) (hNt : Tendsto cfg.N atTop atTop)
    (hK : ∀ k, 1 ≤ cfg.K k)
    (hsub : ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ a)
    (hbasic : cfg.Basic) (hcaps : cfg.Caps) (hatlas : cfg.Atlas) (hnested : cfg.Nested)
    (hℓ : cfg.ℓ = cfg.κ) (hκ : 0 ≤ cfg.κ) (hκ1 : 2 * cfg.κ ≤ 1)
    {s E u : ℝ} (hs : 0 < s) (hE : 0 < E) (hU : s + E ≤ cfg.U)
    (he : s + E < cfg.e₀)
    (hroom : -u * s + 2 * cfg.κ * (s + E) ≤ -8 * E) :
    ∀ᶠ k in atTop, Nonempty (NativeFinePreparation cfg k s E (cfg.N k ^ (-u * s))) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [hN k]
  let R := 2 + cfg.U + s⁻¹
  have hRp : 0 < R := by dsimp [R]; have := inv_pos.mpr hs; linarith
  have hR : 1 < R := by dsimp [R]; have := inv_pos.mpr hs; linarith
  have hRs : R⁻¹ ≤ s := (inv_le_comm₀ hRp hs).mpr (by dsimp [R]; linarith)
  have hR1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR.le
  have hRU : cfg.U + 2 ≤ R := by dsimp [R]; have := inv_pos.mpr hs; linarith
  have hlarge := cfg.eventually_original_affine_mesh_large hN1 hNt hK hsub
  have hspatial := eventually_all_child_spatial_budget hN1 hNt hK hsub hE hroom
  have hcontact := eventually_original_velocity_budget hN1 hNt hK hsub he
  filter_upwards [cfg.assignment_levels_on_range hatlas R hR, hnested R hR,
    hcaps R hR, hlarge, hspatial, hcontact] with k hlev hnest hcap hlarge hspatial hcontact
  have hNp : 0 < cfg.N k := by linarith [hN k]
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le (hK k)
  obtain ⟨g⟩ := exists_native_depth_grid (N := cfg.N k) (s := s) (by linarith [hN k]) hE.le
  have hdepth (j : Fin (g.J + 1)) : 0 ≤ g.depth j ∧ g.depth j ≤ cfg.U :=
    ⟨hs.le.trans (g.depth_mem j).1, (g.depth_mem j).2.trans hU⟩
  let parent := hlev s hRs (by linarith)
  let child := fun j => hlev (g.depth j) (hRs.trans (g.depth_mem j).1) (hdepth j).2
  let L := fun j => Classical.choice
    (cfg.exists_affine_table (child j) (hN1 k) (hK k) hκ hκ1 (hdepth j).1)
  obtain ⟨G, hG, hGae, hGprop⟩ := cfg.finite_assignment_regular_event
    (hbasic k).2.1 (hbasic k).2.2.2.1 g.depth child
  have hn (r : ℝ) (hsr : s ≤ r) (hrU : r ≤ cfg.U) :
      ∀ i : Fin (cfg.n k r), ∃ a : Fin (cfg.n k s), cfg.A k r i ⊆ cfg.A k s a ∧
        Data.I (cfg.T k r) (cfg.j k r i) ⊆ Data.I (cfg.T k s) (cfg.j k s a) := by
    rcases eq_or_lt_of_le hsr with heq | hlt
    · subst r
      intro i
      exact ⟨i, Subset.rfl, Subset.rfl⟩
    · exact hnest s r hRs hlt hrU
  have hw (j : Fin (g.J + 1)) : cfg.N k ^ (-E) ≤
      cfg.N k ^ (-g.depth j) / cfg.N k ^ (-s) ∧
      cfg.N k ^ (-g.depth j) / cfg.N k ^ (-s) ≤ 1 := by
    rw [← Real.rpow_sub hNp]
    exact ⟨Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith [(g.depth_mem j).2]),
      Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith [(g.depth_mem j).1])⟩
  have hb (j : Fin (g.J + 1)) : 14155776 * cfg.K k ^ 10 * cfg.N k ^ (-u * s) ≤
      (cfg.N k ^ (-g.depth j) / cfg.N k ^ (-s)) * cfg.timeLength k (g.depth j) ^ 2 := by
    apply hspatial _ _ (by unfold Data.timeLength; positivity) (hw j).1
    apply (div_le_iff₀ hKp).mpr
    rw [mul_comm (cfg.timeLength k (g.depth j)) (cfg.K k)]
    have hcmp := (time_length_comparison hNp hKp (child j).time_lower (child j).time_upper).2
    apply le_trans _ hcmp
    exact Real.rpow_le_rpow_of_exponent_le (hN1 k) (by
      nlinarith [mul_nonneg hκ (sub_nonneg.mpr (g.depth_mem j).2)])
  refine ⟨{
    parent := parent
    grid := g
    child := child
    affine := L
    event := G
    measurable_event := hG
    conull := hGae
    event_prop := hGprop
    nested := fun j => hn _ (g.depth_mem j).1 (hdepth j).2
    large := hlarge
    parameter_small := ?_
    caps := ?_
    contact_budget := ?_
    spatial_budget := hb }⟩
  · intro j
    have hcoef : 1 ≤ 14155776 * cfg.K k ^ 10 := by
      have hh : 1 ≤ cfg.K k ^ 10 := one_le_pow₀ (hK k)
      linarith
    calc
      cfg.N k ^ (-u * s) ≤ 14155776 * cfg.K k ^ 10 * cfg.N k ^ (-u * s) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hNp.le _)
      _ ≤ _ := hb j
      _ ≤ cfg.timeLength k (g.depth j) ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw j).2 (sq_nonneg _)
  · intro j v hv Q a
    have hv0 : 0 ≤ v := by rcases hv with (rfl | rfl); exact hs.le; exact (hdepth j).1
    have hvR : v ≤ R := by rcases hv with (rfl | rfl) <;> linarith [(hdepth j).2]
    have hh := (hcap (g.depth j + 2) v 1 (by linarith [(hdepth j).1])
      (by linarith [(hdepth j).2]) hv0 hvR hR1 hR.le).2.1 false Q a
    simpa only [Bool.false_eq_true, if_false] using hh
  · intro j
    calc
      _ ≤ cfg.N k ^ (-E) * cfg.N k ^ (-s) := hcontact
      _ = cfg.N k ^ (-E + -s) := (Real.rpow_add hNp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith [(g.depth_mem j).2])

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
