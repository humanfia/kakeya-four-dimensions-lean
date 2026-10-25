import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Source
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.FiniteAveraging

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction

theorem raw_scalar_source {p : Problem} (hp : RawScalar p) (k : ℕ) (a : Fin (p.1 k)) :
    ∃ f : (Fin 6 → ℝ) → ℝ,
      ScalarMixtureFormat (resolution p k) (sizeBudget p) (degreeBudget p) f ∧
      Measurable f ∧ (∀ z, 0 ≤ f z ∧ f z ≤ resolution p k ^ (2 * sizeBudget p)) ∧
      supportedInCube f (3 * resolution p k ^ sizeBudget p) ∧
      (law p k a).map chartPoint = volume.withDensity (fun z => ENNReal.ofReal (f z)) := by
  classical
  have ha := (hp.2 k).2.2.2.1 a
  obtain ⟨m, hm, c, i, A, hdata, hprior⟩ := ha.2.1
  let N := resolution p k
  let T := N ^ sizeBudget p
  let B (j : Fin m) := eventFiber (event p k a) (i j)
  have hT : 1 ≤ T := one_le_pow₀ (by linarith [hp.1.1 k])
  have hm' : (m : ℝ) ≤ T := by simpa only [Real.rpow_natCast] using hm
  have hc (j : Fin m) : 0 ≤ c j ∧ c j ≤ T := by
    refine ⟨(hdata j).1, ?_⟩
    simpa only [Real.rpow_natCast, T, N] using (hdata j).2.1
  have hA (j : Fin m) : Format 5 T (degreeBudget p) (A j) := by
    simpa only [Real.rpow_natCast] using (hdata j).2.2.2.1
  have hB (j : Fin m) : Format 6 T (degreeBudget p) (B j) := by
    simpa only [Real.rpow_natCast, B, eventFiber, T, N] using ha.2.2.2.2.2.2 (i j)
  have hsA (j : Fin m) : ∀ b ∈ A j, ∀ e, |b e| ≤ T := by
    simpa only [Real.rpow_natCast] using (hdata j).2.2.2.2
  have hsB (j : Fin m) : ∀ b ∈ B j, b 5 ∈ Icc (0 : ℝ) 1 := by
    intro b hb
    exact (ha.2.2.2.2.1 hb).2
  let f (z : Fin 6 → ℝ) : ℝ := ∑ j, scalarComponentDensity (c j) (A j) (B j) z
  have hf : Measurable f := Finset.measurable_sum _ fun j _ =>
    measurable_scalarComponentDensity _
      (Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.measurable (hA j))
      (Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.measurable (hB j))
  have hb (z : Fin 6 → ℝ) : 0 ≤ f z ∧ f z ≤ N ^ (2 * sizeBudget p) := by
    refine ⟨Finset.sum_nonneg (fun j _ => (scalarComponentDensity_bound (hc j).1 _ _ z).1), ?_⟩
    calc
      f z ≤ ∑ _j : Fin m, T := by
        apply Finset.sum_le_sum
        intro j _
        exact (le_abs_self _).trans
          ((scalarComponentDensity_bound (hc j).1 _ _ z).2.trans (hc j).2)
      _ = (m : ℝ) * T := by simp
      _ ≤ T ^ 2 := by nlinarith
      _ = N ^ (2 * sizeBudget p) := by
        rw [← pow_mul]
        congr 1
        omega
  refine ⟨f, ⟨m, c, A, B, hm', hc, hA, hB, hsA, hsB, rfl⟩, hf, hb, ?_, ?_⟩
  · intro z e he
    apply Finset.sum_eq_zero
    intro j _
    exact scalarComponentDensity_support (c j) T hT (A j) (B j) (hsA j) (hsB j) z e he
  · change Measure.map chartPoint (((prior p k a).prod volume).restrict (event p k a)) = _
    rw [hprior, map_chart_restrict c i
      (fun j => Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format.measurable (hA j))
      ha.2.2.2.1]
    congr 1
    funext z
    exact sourceDensity_ofReal c (fun j => (hc j).1) i A (event p k a) z

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
