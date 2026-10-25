/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameCellCaps.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameSlopeStep

/-!
# Cell caps of a residual label's incidences

A residual label's incidences have hidden residual within `H` (the parent fit),
and within `H` times the parent width of the parent label's affine part. In a
base cell where that affine part varies by at most one parent width, the
incidences occupy at most `4 H + 10` hidden bins, so the residual caps at the
corresponding hidden width bound the label's cell masses.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4MovingMeshBoxes
open Frame

noncomputable section

/-- Hidden values confined near a center in every base cell occupy few bins. -/
theorem cell_cap_of_confined {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Set Ω) (hS : MeasurableSet S) (base : Ω → Fin 3 → ℝ) (w : Ω → ℝ) {δ a ρ X : ℝ} (ha : 0 < a)
    (hρ : 0 ≤ ρ) (c : Fin 3 → ℤ) (y : ℝ)
    (hconf : ∀ p ∈ S, baseMesh δ (base p) = c → |w p - y| ≤ ρ)
    (hcap : ∀ j : ℤ, μ {p | baseMesh δ (base p) = c ∧ ⌊w p / a⌋ = j} ≤ ENNReal.ofReal X) :
    (μ.restrict S) {p | baseMesh δ (base p) = c} ≤ ENNReal.ofReal ((4 * ρ / a + 2) * X) := by
  classical
  obtain ⟨F, hF, hcov⟩ := interval_mesh_cover ha hρ y
  have hX : 0 ≤ X ∨ X < 0 := le_or_gt 0 X
  calc (μ.restrict S) {p | baseMesh δ (base p) = c}
      = μ ({p | baseMesh δ (base p) = c} ∩ S) := Measure.restrict_apply' hS
    _ ≤ μ (⋃ j ∈ F, {p | baseMesh δ (base p) = c ∧ ⌊w p / a⌋ = j}) := by
      apply measure_mono
      intro p hp
      exact mem_iUnion₂.2 ⟨_, hcov _ (hconf p hp.2 hp.1), hp.1, rfl⟩
    _ ≤ ∑ j ∈ F, μ {p | baseMesh δ (base p) = c ∧ ⌊w p / a⌋ = j} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ F, ENNReal.ofReal X := Finset.sum_le_sum fun j _ => hcap j
    _ = ENNReal.ofReal ((F.card : ℝ) * X) := by
      rcases hX with hX | hX
      · rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
      · rw [ENNReal.ofReal_of_nonpos hX.le, ENNReal.ofReal_of_nonpos]
        · simp
        · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hX.le
    _ ≤ ENNReal.ofReal ((4 * ρ / a + 2) * X) := by
      rcases hX with hX | hX
      · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hF hX)
      · rw [ENNReal.ofReal_of_nonpos]
        · exact bot_le
        · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hX.le

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- The residual hidden coordinate of an incidence. -/
def Frame.resW (f : Frame D k s₀ U') (p : α × ℝ) : ℝ := point (f.coeff p.1) p.2 3

/-- An affine function of the residual base point. -/
def affineAt (L : Fin 4 → ℝ) (z : Fin 3 → ℝ) : ℝ := L 0 + L 1 * z 0 + L 2 * z 1 + L 3 * z 2

theorem lastEntry_zero {M : ℕ} (u : EntryHistory M 0) : lastEntry 0 u = u := rfl

/-- The parent fit bounds the residual hidden coordinate of a label's incidences. -/
theorem FrameGood.resW_le (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) {p : α × ℝ} (hp : p ∈ f.labelSet h i) :
    |f.resW p| ≤ f.H := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  obtain ⟨hsub, hhist⟩ := hg.inside hh i
  have hl : p.1 ∈ f.parentSet := hhist hp.1
  have hent : p.1 ∈ f.entry 0 f.i₀ f.u₀ := f.hist_subset_entry 0 f.i₀ f.u₀ hl
  have hfit := (assignedAffineEntry_subset _ _ _ _ _ _ _ hent).2
  have ht := (hg.mem_resBlock hh i p.2).mp hp.2
  have hw := hfit (f.t₀ + f.q₀ * p.2) (hsub ht)
  have ha₀ := f.a₀_pos hN
  rw [Frame.resW, f.point_coeff_three, abs_div, abs_of_pos ha₀, div_le_iff₀ ha₀, abs_sub_comm]
  refine hw.trans (le_of_eq ?_)
  rw [Frame.a₀, hg.depth_zero]

/-- The parent label of a label contains its incidences. -/
theorem FrameGood.labelSet_sub_up (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h < f.m)
    (i : Fin (f.retained (h + 1)).card) :
    f.labelSet (h + 1) i ⊆ f.labelSet h (f.upLabel hg hh i) := by
  intro p hp
  refine ⟨?_, ?_⟩
  · change p.1 ∈ f.hist h (f.node h (f.upLabel hg hh i)).1 (f.node h (f.upLabel hg hh i)).2
    rw [hg.node_upLabel hh i]
    exact hg.hist_subset_parentNode h _ hp.1
  · have h1 := (hg.mem_resBlock (show h + 1 ≤ f.m from hh) i p.2).mp hp.2
    refine (hg.mem_resBlock hh.le (f.upLabel hg hh i) p.2).mpr ?_
    rw [hg.node_upLabel hh i]
    exact (hg.anc_sub h hh _).2 h1

/-- The parent label's fit confines the hidden coordinate of a label's incidences. -/
theorem FrameGood.resW_sub_up (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h < f.m)
    (i : Fin (f.retained (h + 1)).card) {p : α × ℝ} (hp : p ∈ f.labelSet (h + 1) i) :
    |f.resW p - affineAt (f.labelL h (f.upLabel hg hh i)) (f.resBase p)| ≤
      f.H * D.N k ^ (-((h : ℝ) * (U' / f.m))) := by
  have hp' := hg.labelSet_sub_up hh i hp
  have hfit := (hg.res_fit hh.le (f.upLabel hg hh i) p.1 hp'.1 p.2 hp'.2).1
  refine le_of_eq_of_le ?_ hfit
  congr 1
  simp only [Frame.level, Frame.labelL, affineAt, Frame.resW, Frame.resBase, affineBase,
    eval_sub, eval_X, eval_add, eval_mul, eval_C, point]
  simp

/-- The mass floor of a label's incidence law. -/
theorem FrameGood.nodeLaw_mass (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) :
    ENNReal.ofReal (θ ^ 2 / D.K k ^ 3 * f.resq h *
      ((D.N k ^ (-((h : ℝ) * (U' / f.m)))) ^ D.d * f.resq h ^ 2 *
        D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))))) ≤ f.nodeLaw h i univ := by
  have hθ := hg.θ_pos
  have hK : 0 < D.K k := by linarith [hg.K_ge]
  have hq := f.resq_pos h
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  rw [Frame.nodeLaw, Measure.restrict_apply_univ]
  refine le_trans ?_ (hg.res_mass hh i)
  set X := (D.N k ^ (-((h : ℝ) * (U' / f.m)))) ^ D.d * f.resq h ^ 2 *
    D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m)))
  have hX : 0 ≤ X := mul_nonneg (mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hN.le _) _)
    (sq_nonneg _)) (Real.rpow_nonneg hN.le _)
  calc ENNReal.ofReal (θ ^ 2 / D.K k ^ 3 * f.resq h * X)
      = ENNReal.ofReal (f.resq h / θ⁻¹) * ENNReal.ofReal (X / (D.K k ^ 3 / θ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ _ := mul_le_mul_right (hg.res_floor hh i) _

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
