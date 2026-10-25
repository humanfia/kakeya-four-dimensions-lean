-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/UniformAnchors.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/UniformAnchors.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/UniformAnchors.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Lib.K4PolynomialNorming.AnchorSeparation
import Mathlib
import Submission.Obl.k4_oss_bad_direction_extraction.Energy

/-!
Adapted from the same LOT tree, obligation root, session x0001,
commit 50fd00fa: Submission/Obl/Root/AnchorSeparation.lean and
Submission/Obl/Root/UniformAnchorSampling.lean. Offered in the o116
API post of 2026-10-21 05:24 UTC. These original-measure sampling
kernels are adapted under this obligation's namespace because the
root's own helper modules are not accepted imports.
-/

/-! Reuse the accepted anchor-separation kernel, then specialize to finite grids. -/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

export Submission.Lib.K4PolynomialNorming
  (pi_pair_measure_preimage close_pair_measure_le pi_bad_pairs_measure_le
    cartesian_bad_pairs_measure_le cartesian_close_pairs_measure_le)

end Submission.Obl.k4_physical_row_packet_potential.Cartesian


open Set MeasureTheory ProbabilityTheory

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

/-- The uniform law on a separated real finite set has an explicit small-ball cap. -/
theorem uniform_finset_ball_measure_le (S : Finset ℝ) [Nonempty S]
    (δ r : ℝ) (hδ : 0 < δ) (hr : 0 ≤ r)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ dist a b) (c : ℝ) :
    (PMF.uniformOfFintype S).toMeasure {x : S | |(x : ℝ) - c| < r} ≤
      ENNReal.ofReal ((2 * r / δ + 1) / (S.card : ℝ)) := by
  classical
  let F := S.filter (fun x => |x - c| < r)
  have hcount : (F.card : ℝ) ≤ 2 * r / δ + 1 :=
    Submission.Obl.k4_oss_bad_direction_extraction.card_le_of_separated_of_subset_ball F hδ
      (fun a ha b hb hab => hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab)
      hr (fun x hx => (Finset.mem_filter.mp hx).2.le)
  have heq : Fintype.card {x : S | |(x : ℝ) - c| < r} = F.card := by
    let e : {x : S | |(x : ℝ) - c| < r} ≃ F :=
      { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
        invFun := fun x => ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, (Finset.mem_filter.mp x.2).2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_coe F)
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast (show 0 < S.card by simpa using Fintype.card_pos (α := S))
  rw [PMF.toMeasure_uniformOfFintype_apply _ (by measurability), heq, Fintype.card_coe,
    ENNReal.ofReal_div_of_pos hcard, ENNReal.ofReal_natCast]
  simpa only [ENNReal.ofReal_natCast] using
    ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hcount) (S.card : ENNReal)

/-- Uniform finite grids give a concrete Cartesian anchor-collision budget,
including the atom-size term. -/
theorem uniform_finset_cartesian_close_pairs_measure_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] (S : Finset ℝ) [Nonempty S]
    (δ r : ℝ) (hδ : 0 < δ) (hr : 0 ≤ r)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ dist a b) :
    Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => (PMF.uniformOfFintype S).toMeasure))
      {a | ∃ i j k, j ≠ k ∧ |(a i j : ℝ) - (a i k : ℝ)| < r} ≤
        (Fintype.card ι : ENNReal) * (Fintype.card κ : ENNReal) ^ 2 *
          ENNReal.ofReal ((2 * r / δ + 1) / (S.card : ℝ)) := by
  let μ := (PMF.uniformOfFintype S).toMeasure
  let τ := ENNReal.ofReal ((2 * r / δ + 1) / (S.card : ℝ))
  have hcap (x : S) : μ (Metric.ball x r) ≤ τ := by
    simpa only [μ, τ, Metric.ball, Subtype.dist_eq, Real.dist_eq] using
      uniform_finset_ball_measure_le S δ r hδ hr hsep (x : ℝ)
  have h := cartesian_bad_pairs_measure_le (κ := κ) (fun _ : ι => μ)
    (fun _ => {p : S × S | dist p.1 p.2 < r})
    (fun _ => measurableSet_lt (measurable_fst.dist measurable_snd) measurable_const)
    τ (fun _ => close_pair_measure_le μ r τ hcap)
  simpa only [μ, τ, Subtype.dist_eq, Real.dist_eq, Set.mem_ofPred_eq] using h

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
