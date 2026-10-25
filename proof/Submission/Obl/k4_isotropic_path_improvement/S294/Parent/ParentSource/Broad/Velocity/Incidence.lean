-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.Incidence, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/Incidence.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/Incidence.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 5bf2ec7212f0;
-- source Submission/Obl/k4_isotropic_path_improvement/IncidenceCapture.lean.
-- The finite capture keeps original directions for breadth, and compresses only
-- the hidden coordinate in the tube directions. This preserves one determinant factor.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling.MeasureCapture
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.HeightScale

set_option autoImplicit false

/-!
Cell incidence laws can be different submeasures of a common line prior.
Their breadth is transferred without asserting breadth for the full prior
conditioned merely on hitting a cell. This is the duration-sensitive form
needed in the physical velocity-graph argument.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set
open scoped BigOperators
open Submission.Obl.k4_mk_grid_transfer
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

theorem anisotropic_incidence_line_law_support_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω],
      ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (ν : Measure Ω) [IsFiniteMeasure ν] (laws : Fin m → Measure Ω)
        [∀ q, IsFiniteMeasure (laws q)] (a e : Ω → EuclideanSpace ℝ (Fin 4)) (compression : ℝ),
      0 < compression → compression ≤ 1 →
      Measurable e → (∀ x, ‖e x‖ = 1) →
      (∀ q : Fin m, MeasurableSet {x | latticePoint (z q) ∈ lineTube 3 (a x) (heightUnit compression (e x))}) →
      ∀ ρ c b : ℝ, 0 < ρ → 0 ≤ c → 0 < b →
      (∀ q E, (laws q).real E ≤ b * ν.real E) →
      (∀ q : Fin m, laws q {x | latticePoint (z q) ∉ lineTube 3 (a x) (heightUnit compression (e x))} = 0) →
      (∀ q : Fin m, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
        c * (laws q).real univ ≤ (laws q).real {x | ρ ≤ Metric.infDist (e x) (V : Set _)}) →
      (compression / 256) * (c * ρ / 2) ^ 4 * ((∑ q : Fin m, (laws q).real univ) / b) ^ 4 ≤
        (m : ℝ) * C ^ 3 * (ν.real univ) ^ 4 := by
  classical
  obtain ⟨C, hC, hbudget⟩ := four_dimensional_broad_lattice_budget
  refine ⟨C, hC, ?_⟩
  intro Ω instΩ m z hz ν hν laws hlaws a e compression hcompression hcompression1 he hunit hsets ρ c b hρ hc hb hdom hsupp hbroad
  let S : Fin m → Set Ω := fun q => {x | latticePoint (z q) ∈ lineTube 3 (a x) (heightUnit compression (e x))}
  obtain ⟨n, code, rep, hcode, hrep, herr, hmem⟩ :=
    exists_direction_event_capture e he hunit m S hsets (ρ / 2) (by positivity)
  let w := codeWeight ν code
  let wq (q : Fin m) := codeWeight (laws q) code
  let localW (q : Fin m) (i : Fin n) :=
    w i * (lineTube 3 (a (rep i)) (heightUnit compression (e (rep i)))).indicator (fun _ => (1 : ℝ)) (latticePoint (z q))
  have hlocal (q : Fin m) (i : Fin n) : 0 ≤ localW q i :=
    mul_nonneg measureReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hweight (q : Fin m) (i : Fin n) : wq q i ≤ b * localW q i := by
    by_cases hi : rep i ∈ S q
    · have hi' : latticePoint (z q) ∈ lineTube 3 (a (rep i)) (heightUnit compression (e (rep i))) := hi
      simpa only [wq, w, localW, codeWeight, Set.indicator_of_mem hi', mul_one] using
        hdom q (code ⁻¹' {i})
    · have hsubset : code ⁻¹' {i} ⊆ (S q)ᶜ := by
        intro x hx
        have hcx : code x = i := hx
        intro hxs
        have hri := (hmem q x).mpr hxs
        rw [hcx] at hri
        exact hi hri
      have hzero : laws q (code ⁻¹' {i}) = 0 := measure_mono_null hsubset (hsupp q)
      have hi' : latticePoint (z q) ∉ lineTube 3 (a (rep i)) (heightUnit compression (e (rep i))) := hi
      simp only [wq, codeWeight, measureReal_def, hzero, ENNReal.toReal_zero, localW,
        Set.indicator_of_notMem hi', mul_zero, le_refl]
  have hbq (q : Fin m) : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)),
      Module.finrank ℝ V < 4 → c * ∑ i, wq q i ≤
        ∑ i, if ρ / 2 ≤ Metric.infDist (e (rep i)) (V : Set _) then wq q i else 0 := by
    have h := capture_breadth (laws q) code hcode rep e univ (fun _ => by simp)
      ρ (ρ / 2) c herr (by simpa only [mem_univ, true_and] using hbroad q)
    simpa only [wq, Set.indicator_univ, mul_one, show ρ - ρ / 2 = ρ / 2 by ring] using h
  let F (q : Fin m) := tubeSum 3 (fun _ : Fin 4 => fun i => a (rep i))
    (fun _ : Fin 4 => fun i => heightUnit compression (e (rep i))) (fun _ : Fin 4 => w) (latticePoint (z q))
  have hraw (q : Fin m) : (compression / 256) * (c * (ρ / 2)) ^ 4 * (∑ i, wq q i) ^ 4 ≤ b ^ 4 * F q := by
    have hdet := Breadth.det_weight_of_breadth (fun i => e (rep i)) (wq q)
      (fun _ => measureReal_nonneg) (ρ / 2) c (by positivity) hc (hbq q)
    calc
      _ = (compression / 256) * ((c * (ρ / 2)) ^ 4 * (∑ i, wq q i) ^ 4) := by ring
      _ ≤ (compression / 256) *
          (∑ T : Fin 4 → Fin n, |(Matrix.of fun i j => e (rep (T i)) j).det| * ∏ i, wq q (T i)) :=
        mul_le_mul_of_nonneg_left hdet (by positivity)
      _ ≤ ∑ T : Fin 4 → Fin n,
          |(Matrix.of fun i j => heightUnit compression (e (rep (T i))) j).det| * ∏ i, wq q (T i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro T _
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (det_heightUnit_ge hcompression hcompression1 (fun i => e (rep (T i)))
            (fun i => hunit (rep (T i))))
          (Finset.prod_nonneg (fun _ _ => measureReal_nonneg))
      _ ≤
          ∑ T : Fin 4 → Fin n, |(Matrix.of fun i j => heightUnit compression (e (rep (T i))) j).det| *
            ∏ i, b * localW q (T i) := by
        apply Finset.sum_le_sum
        intro T _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) (fun i _ => hweight q (T i))
      _ = b ^ 4 * F q := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        change _ = b ^ 4 * (∑ T : Fin 4 → Fin n,
          |(Matrix.of fun i j => heightUnit compression (e (rep (T i))) j).det| * ∏ i, localW q (T i))
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        ring
  have hcell (q : Fin m) : (compression / 256) * (c * (ρ / 2)) ^ 4 * ((laws q).real univ / b) ^ 4 ≤ F q := by
    have h := hraw q
    rw [show (∑ i, wq q i) = (laws q).real univ from sum_codeWeight (laws q) code hcode] at h
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos hb 4)]
    simpa only [mul_comm] using h
  have h := hbudget m z hz (fun _ => n) (fun _ i => a (rep i)) (fun _ i => heightUnit compression (e (rep i)))
    (fun _ => w) (fun _ i => norm_heightUnit hcompression.ne'
      (norm_ne_zero_iff.mp (by rw [hunit (rep i)]; norm_num))) (fun _ _ => measureReal_nonneg)
    (fun q => (laws q).real univ / b) ((compression / 256) * (c * (ρ / 2)) ^ 4)
    (fun q => div_nonneg measureReal_nonneg hb.le) (by positivity) hcell
  simpa only [w, sum_codeWeight ν code hcode, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.sum_div, show c * (ρ / 2) = c * ρ / 2 by ring] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
