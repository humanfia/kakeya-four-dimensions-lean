-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.UnitGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.GrainRefinement
import Submission.WZ.Obl.wz_broad_grains_initialization.GrainState
import Submission.WZ.Obl.wz_broad_grains_initialization.CommonMultiplicity
import Submission.WZ.Obl.wz_broad_grains_initialization.PolynomialCount
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.PowerBudget
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Multiplicity

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (A bodyCount)
open wz_measurable_angular_selection (pd)
open wz_ad_dichotomy_from_separated (exists_monomial_bound exists_power_bound)

/-- Broad shading at unit scale has an elementary initial grain state.
The allowed local convex coefficient is arbitrary, so tiny separated cubes
suffice; their endpoint and sparsity losses fit into the prescribed error. -/
theorem unit_scale_grains_of_broad {h : ℝ} (hh : 0 < h) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ ω ζ η τ θ : ℝ,
        ω ≤ 1 → η ≤ min (h / 8) (1 / 16) → τ ≤ min (h / 8) (1 / 16) → θ ≤ h / 2 →
        ∀ (n : ℕ) (x v : Fin n → Space) (Y Z : Fin n → Set Space),
          A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
          (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) →
          ENNReal.ofReal (δ ^ τ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) →
          (∀ (p u : Space) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 1 →
            ({i | p ∈ Z i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
              δ ^ (-θ) * r ^ (ω * ζ / 100) * bodyCount Z p) →
          ∃ c : ℝ, State ω ζ δ h 1 c n x v Y false := by
  have hν : 0 < h / 8 := by positivity
  have hC := grainMassConstant_pos
  obtain ⟨dl, hdl, hlog⟩ := common_multiplicity_cut_power (by norm_num : (0 : ℝ) < 4) hν
  obtain ⟨dt, hdt, _, htrim⟩ := exists_monomial_bound 64000000000000
    (by norm_num : (1 / 4 : ℝ) < 1)
  obtain ⟨ds, hds, _, hsparse⟩ := exists_monomial_bound (4 * grainMassConstant * 2073600000)
    (by linarith : h / 2 < h)
  obtain ⟨dm, hdm, _, hmass⟩ := exists_monomial_bound (4 * grainMassConstant)
    (by linarith : h / 2 < h)
  obtain ⟨db, hdb, _, hbroad⟩ := exists_power_bound (2 * (2002 : ℝ) ^ 3)
    (by linarith : 0 < h / 2)
  let d₀ : ℝ := min (1 / 100000) (min dl (min dt (min ds (min dm db))))
  refine ⟨d₀, by dsimp [d₀]; positivity, (min_le_left _ _).trans (by norm_num), ?_⟩
  intro δ hδ hδd ω ζ η τ θ hω hη hτ hθ n x v Y Z hA hZ hZmass hZbroad
  have hd := hδd
  dsimp only [d₀] at hd
  simp only [le_min_iff] at hd
  obtain ⟨hδsmall, hδl, hδt, hδs, hδm, hδb⟩ := hd
  have hδ1 : δ ≤ 1 := by linarith
  have hηh := hη.trans (min_le_left _ _)
  have hτh := hτ.trans (min_le_left _ _)
  have hηsmall := hη.trans (min_le_right _ _)
  have hτsmall := hτ.trans (min_le_right _ _)
  have hlam : 0 < δ ^ (η + τ) := Real.rpow_pos_of_pos hδ _
  have hq : 0 < δ ^ (h / 8) := Real.rpow_pos_of_pos hδ _
  have hT : 64000000000000 * δ ≤ δ ^ (η + τ) := by
    calc
      _ = 64000000000000 * δ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ δ ^ (1 / 4 : ℝ) := htrim δ hδ hδt
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hS : 4 * grainMassConstant * 2073600000 * δ ^ h ≤
      δ ^ (h / 8) * δ ^ (η + τ) := by
    rw [← Real.rpow_add hδ]
    exact (hsparse δ hδ hδs).trans
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hZd : ENNReal.ofReal (δ ^ (η + τ) * n * δ ^ 2) ≤ ∑ i, volume (Z i) :=
    wz_clustered_cover_volume_gain.Parent.density_of_retained_mass hδ hA.2.2.2.1 hZmass
  have hnpoly := normalized_polynomial_count hδ (by linarith) (by linarith) hA
  obtain ⟨W, hW, hWmass, hWcount, ⟨G⟩⟩ := grain_refinement_of_budgets hA.1 hδ hδsmall
    hlam hq hT hS x v Z (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.1)
    (fun i => (hZ i).1) (fun i => (hZ i).2.trans (hA.2.1 i).2.2.2) hZd
    (hlog δ hδ hδl n hnpoly)
  have hret : δ ^ h ≤ δ ^ (h / 8) / (4 * grainMassConstant) * δ ^ τ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (show 0 < 4 * grainMassConstant by positivity)).mpr
    calc
      _ ≤ δ ^ (h / 2) := by simpa only [mul_comm] using hmass δ hδ hδm
      _ ≤ δ ^ (h / 8 + τ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = _ := by rw [Real.rpow_add hδ]
  have hWYmass : ENNReal.ofReal (δ ^ h) * (∑ i, volume (Y i)) ≤ ∑ i, volume (W i) := by
    calc
      _ ≤ ENNReal.ofReal (δ ^ (h / 8) / (4 * grainMassConstant) * δ ^ τ) *
          (∑ i, volume (Y i)) := mul_le_mul' (ENNReal.ofReal_le_ofReal hret) le_rfl
      _ = ENNReal.ofReal (δ ^ (h / 8) / (4 * grainMassConstant)) *
          (ENNReal.ofReal (δ ^ τ) * ∑ i, volume (Y i)) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal (δ ^ (h / 8) / (4 * grainMassConstant)) * ∑ i, volume (Z i) :=
        mul_le_mul' le_rfl hZmass
      _ ≤ _ := hWmass
  have hconst : (2 * (2002 : ℝ) ^ 3) * δ ^ (-θ) ≤ δ ^ (-h) := by
    calc
      _ ≤ δ ^ (-(h / 2)) * δ ^ (-θ) :=
        mul_le_mul_of_nonneg_right (hbroad δ hδ hδb) (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-(h / 2) + -θ) := (Real.rpow_add hδ _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  refine ⟨100 * δ, G.to_state hδ hδ1 hh.le hω (fun i => (hA.2.1 i).2.2.1)
    (fun i => (hA.2.1 i).2.1) (fun i => ⟨(hW i).1, (hW i).2.trans (hZ i).2⟩) hWYmass ?_⟩
  intro p u r hu hr hr1
  have hr0 : 0 ≤ r := hδ.le.trans hr
  calc
    _ ≤ ((2 * (2002 : ℝ) ^ 3) * δ ^ (-θ)) * r ^ (ω * ζ / 100) * bodyCount W p :=
      broadness_of_pointwise_fraction_at (by positivity) (Real.rpow_nonneg hδ.le _) hr0
        (fun i => (hW i).2) hWcount p u (hZbroad p u r hu hr hr1)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _)

end WangZahlLot.Obl.wz_broad_grains_initialization
