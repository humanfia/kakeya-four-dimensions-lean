import Submission.Obl.k4_scalar_guarded_entropic_path.CandidateAssembly
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCoreBudgets

/-!
# The reference hypotheses of the candidate stages of a stage path

`referenceTests s pe` are the base density tests of every view of a stage path: the
tangent mesh depths `scale · j / m` (`j ≤ m²`), the terminal depth `L`, and the angular
grid of `[scale / R, scale · R]` with gaps `ε = scale · δ / 100`, at the common tolerance
`pe.τ` (each menu restricted to its valid range, which removes nothing).

`eventually_reference_inputs`: on one tail of inner samples, every candidate stage
`s.candidateStage al pe (s.referenceTests pe) j a node layers α` (for ANY nodes, layers and
`α`; the reference hypotheses only see its unchanged geometric fields) satisfies
`Reference.CandidateInput` with `d = dstar`, `S = min S₀ 1`, the graph box
`Kb = graphK j = N_final(j)^{scale/1000}`, the mesh `m`, slack `ε`, tolerance `pe.τ`,
floor exponent `pe.γ` and the angular menu of the view.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

/-- The reference slack `ε = scale · δ / 100`. -/
def referenceSlack (s : StagePath ctx source k R δ) : ℝ := s.layout.scale * δ / 100

theorem referenceSlack_pos (s : StagePath ctx source k R δ) : 0 < s.referenceSlack := by
  have hscale := s.layout.scale_pos
  have hδ : 0 < δ := hscale.trans_le s.layout.scale_error
  unfold referenceSlack
  positivity

/-- The base density tests of every view (see the module docstring). -/
def referenceTests (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η) (a : s.ViewIndex) :
    DensityTests (s.views a).parent where
  pure := (insert (L (s.views a).parent) (Reference.pureGrid s.layout.scale s.layout.m)).filter
    fun r => 0 ≤ r ∧ r ≤ L (s.views a).parent
  angular := (Reference.angularGrid s.layout.scale R s.referenceSlack).filter
    fun u => 0 < u ∧ u ≤ U (s.views a).parent
  tolerance := pe.τ
  tolerance_pos := pe.τ_pos
  pure_valid := fun _ hr => (Finset.mem_filter.mp hr).2
  angular_valid := fun _ hu => (Finset.mem_filter.mp hu).2

theorem referenceTests_tolerance (s : StagePath ctx source k R δ) {v : ℝ}
    (pe : PreparationExponents s.layout.scale δ v ctx.S₀ ctx.η) (a : s.ViewIndex) :
    (s.referenceTests pe a).tolerance = pe.τ := rfl

/-- The mesh depths lie well inside every view. -/
theorem mesh_lt_length (s : StagePath ctx source k R δ) (hR : 0 < R) (n : ℕ) :
    s.layout.scale * s.layout.m < L (s.view n).parent := by
  have hL := s.view_length n
  have hrange := s.layout.range_small
  have hscale := s.layout.scale_pos
  have : s.layout.scale * s.layout.m ≤ s.layout.scale * ((s.layout.m : ℝ) + R + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hscale.le
  linarith

/-- The angular grid lies inside the angular range of every view. -/
theorem angular_lt_range (s : StagePath ctx source k R δ) (hR : 0 < R) (hη : 0 < ctx.η)
    (n : ℕ) : s.layout.scale * R < U (s.view n).parent := by
  have hL := s.view_length n
  have hU : U (s.view n).parent = ctx.η * L (s.view n).parent := (s.view n).range
  have hang := s.layout.angular_small
  have hscale := s.layout.scale_pos
  have hm : (0 : ℝ) ≤ s.layout.m := Nat.cast_nonneg _
  have h1 : s.layout.scale * R < s.layout.scale * ((s.layout.m : ℝ) + R + 1) :=
    mul_lt_mul_of_pos_left (by linarith) hscale
  have h2 : ctx.η / 4 < ctx.η * L (s.view n).parent := by nlinarith
  rw [hU]
  linarith

/-- **The reference hypotheses** of every candidate stage on one tail of inner samples. -/
theorem eventually_reference_inputs (s : StagePath ctx source k R δ) (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η)
    (hR : 1 < R) (hη : 0 < ctx.η) :
    ∀ᶠ j in atTop, ∀ (a : Fin s.layout.L)
      (node : ℝ → Fin (s.views (s.candidateIndex a)).count)
      (layers : Fin (s.views (s.candidateIndex a)).count →
        Layer (W (s.views (s.candidateIndex a)).parent
          ((s.views (s.candidateIndex a)).suffixChain.sample j))) (α : ℝ),
      ∃ (ε : ℝ) (us : Finset ℝ),
        Reference.CandidateInput (s.candidateStage al pe (s.referenceTests pe) j a node layers α)
          ctx.dstar (min ctx.S₀ 1) R (s.graphK j) s.layout.m ε pe.τ pe.γ us := by
  have hscale := s.layout.scale_pos
  have hδ : 0 < δ := hscale.trans_le s.layout.scale_error
  have hε := s.referenceSlack_pos
  have hR0 : 0 < R := by linarith
  have hK : ∀ᶠ j in atTop, ∀ a : s.ViewIndex,
      K (s.views a).parent ((s.views a).suffixChain.sample j) ≤
        N s.final j ^ (s.layout.scale / 1000) :=
    Filter.eventually_all.2 fun a => s.view_K_subpower a _ (by positivity)
  have htwo : ∀ᶠ j in atTop, 2 ≤ N s.final j ^ s.referenceSlack :=
    ((tendsto_rpow_atTop hε).comp s.final_exact.1.2.1).eventually_ge_atTop 2
  have hcore := s.eventually_core_properties hη pe (s.referenceTests pe)
  filter_upwards [hK, htwo, hcore] with j hKj htwoj hcorej
  intro a node layers α
  refine ⟨s.referenceSlack, (s.referenceTests pe (s.candidateIndex a)).angular, ?_⟩
  have hp : Exact (s.views (s.candidateIndex a)).parent :=
    (s.views (s.candidateIndex a)).parent_exact
  have hN : Code.N (s.views (s.candidateIndex a)).parent
      ((s.views (s.candidateIndex a)).suffixChain.sample j) = N s.final j :=
    s.views_resolution_code (s.candidateIndex a) j
  have hN₀1 : 1 ≤ N s.final j := by linarith [s.final_exact.1.1 j]
  have hS : 0 < ctx.S₀ := pe.S_pos
  have hmL : s.layout.scale * s.layout.m < L (s.views (s.candidateIndex a)).parent :=
    s.mesh_lt_length hR0 (a.val + 1)
  have hRU : s.layout.scale * R < U (s.views (s.candidateIndex a)).parent :=
    s.angular_lt_range hR0 hη (a.val + 1)
  have hL0 : 0 < L (s.views (s.candidateIndex a)).parent := by
    have := s.view_length (a.val + 1)
    change (1 / 2 : ℝ) < L (s.views (s.candidateIndex a)).parent at this
    linarith
  have hmem_pure : ∀ r, r ∈ insert (L (s.views (s.candidateIndex a)).parent)
      (Reference.pureGrid s.layout.scale s.layout.m) → 0 ≤ r →
        r ≤ L (s.views (s.candidateIndex a)).parent →
      r ∈ (s.densityTests (s.referenceTests pe) (s.candidateIndex a)).pure := by
    intro r hr h0 hL
    exact (s.views (s.candidateIndex a)).pure_mem_withLayerTests _
      (Finset.mem_filter.mpr ⟨hr, h0, hL⟩)
  exact
    { exact := hp
      scale_pos := hscale
      S_pos := lt_min hS one_pos
      S_le_one := min_le_right _ _
      S_le := (min_le_left _ _).trans (le_of_eq (s.views (s.candidateIndex a)).angular.symm)
      R_pos := hR0
      m_pos := s.layout.m_one
      K_le := hKj (s.candidateIndex a)
      mesh_le := hmL.le
      tol_pos := pe.τ_pos
      tol_le := by
        have h := pe.τ_budget
        have : 0 ≤ s.layout.scale * δ := by positivity
        unfold referenceSlack
        linarith
      floor_le := by
        have h := pe.γ_budget
        have : 0 ≤ s.layout.scale * δ := by positivity
        unfold referenceSlack
        linarith
      two_le := by
        show 2 ≤ Code.N (s.views (s.candidateIndex a)).parent
          ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ s.referenceSlack
        rw [hN]
        exact htwoj
      B_ge := by
        show Code.N (s.views (s.candidateIndex a)).parent
            ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ (5 * s.referenceSlack) ≤
          Code.N (s.views (s.candidateIndex a)).parent
            ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ (s.layout.scale * δ)
        rw [hN]
        apply Real.rpow_le_rpow_of_exponent_le hN₀1
        have : 0 ≤ s.layout.scale * δ := by positivity
        unfold referenceSlack
        linarith
      profile := by
        intro r hr0 hr
        have h := s.view_absolute_profile (Nat.succ_pos a.val) r hr0 (hr.trans hmL.le)
        have h' := (abs_le.mp h).1
        have : 0 ≤ s.layout.scale * δ := by positivity
        show ctx.dstar * r - s.referenceSlack ≤ f (s.views (s.candidateIndex a)).parent r
        unfold referenceSlack
        change -(s.layout.scale * δ / 10000) ≤
          f (s.views (s.candidateIndex a)).parent r - ctx.dstar * r at h'
        linarith
      sigma_le := fun g => s.worldLaw_le pe (s.referenceTests pe) j (s.candidateIndex a) g
      floor := by
        intro g
        have h := hcorej.2.2.2.2 (s.candidateIndex a) g
        show (s.views (s.candidateIndex a)).suffixChain.selectedWorldLaw j
            (s.coreSet pe (s.referenceTests pe) j) g = 0 ∨
          ENNReal.ofReal ((Code.N (s.views (s.candidateIndex a)).parent
            ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ pe.γ)⁻¹) ≤
            (s.views (s.candidateIndex a)).suffixChain.selectedWorldLaw j
              (s.coreSet pe (s.referenceTests pe) j) g univ
        rw [hN]
        exact h
      grid_valid := fun u hu => (Finset.mem_filter.mp hu).2
      grid_cover := by
        intro b hb1 hb2
        obtain ⟨u, hu, hub, hgap⟩ := Reference.angularGrid_cover hscale hR0 hε hb1 hb2
        have hv := Reference.angularGrid_valid hscale hR.le hε u hu
        exact ⟨u, Finset.mem_filter.mpr ⟨hu, hv.1, hv.2.trans hRU.le⟩, hub, hgap⟩
      pure_null := by
        intro g i
        have hr := Reference.pureGrid_valid hscale.le s.layout.m_one _
          (Reference.mem_pureGrid s.layout.scale s.layout.m i)
        exact s.core_pure_null pe (s.referenceTests pe) j (s.candidateIndex a) _
          (hmem_pure _ (Finset.mem_insert_of_mem (Reference.mem_pureGrid _ _ i)) hr.1
            (hr.2.trans hmL.le)) g
      terminal_null := by
        intro g
        exact s.core_pure_null pe (s.referenceTests pe) j (s.candidateIndex a) _
          (hmem_pure _ (Finset.mem_insert_self _ _) hL0.le le_rfl) g
      angular_null := by
        intro g u hu
        exact s.core_angular_null pe (s.referenceTests pe) j (s.candidateIndex a) u hu g }

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
