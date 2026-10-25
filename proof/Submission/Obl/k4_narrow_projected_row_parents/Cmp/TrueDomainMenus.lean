/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/TrueDomainMenus.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.TrueDomainGeometry
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.TrueDomainCounting
import Submission.Obl.k4_general_parent_projected_layers.Support.CompatibleWorlds

/-! Literal common-domain menus for a true tilted packet. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open Set
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- True packet assignments meet a finite common-domain menu. Its complete weighted
reference sum uses the unchanged original velocity probabilities. -/
theorem true_domain_menu {K Q q χ g m t₀ : ℝ} (hK : 1 ≤ K) (hQ : 0 < Q)
    (hQ1 : Q ≤ 1) (hq : 0 < q) (hqQ : q ≤ Q) (hχ : 0 < χ) (hg : 0 < g)
    (hχQ : χ ≤ Q) (hχQg : χ ≤ Q * g) (hm : 0 < m) (hmQg : m ≤ Q * g)
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (c : Fin 5 → ℝ) (hc₄ : |c 4| ≤ K) :
    ∃ (V : Finset ℤ) (S : Finset Code),
      (∀ w : ℤ → ℝ, (∀ v, 0 ≤ w v) → (∑ v ∈ V, w v) ≤ 1 →
        (∑ d ∈ S, q * χ * m * w (d 1)) ≤ 237600 * K ^ 4 * Q ^ 3 * g) ∧
      ∀ (b : Fin 6 → ℝ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → |t - t₀| ≤ Q →
        |b 0| + |b 1| + |b 3| + |b 4| ≤ K →
        |b 0 + t₀ * b 3 - (c 0 + t₀ * c 1)| ≤ K * Q →
        |rowError c b t₀| ≤ K * Q * g → |b 4 - c 3 - c 4 * b 3| ≤ K * g →
        code q χ g m b t ∈ S := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  obtain ⟨V, I, G, hI, hG, hworld⟩ := compatible_parent_world_lists c hK hQ.le hQ1 hg hχ
    hχQ hχQg ht₀ hc₄
  obtain ⟨P, hP, hPcover⟩ := true_position_menus (t₀ := t₀) hK hq hqQ hχ hχQg hm hmQg c hc₄
  obtain ⟨J, hJ, hJcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hq hQ.le t₀
  have hJ' : (J.card : ℝ) * q ≤ 6 * Q := by
    have h := mul_le_mul_of_nonneg_right hJ hq.le
    have heq : (4 * Q / q + 2) * q = 4 * Q + 2 * q := by field_simp <;> ring
    rw [heq] at h
    linarith
  obtain ⟨S, hbudget, hcover⟩ := true_domain_reference_menu J V I G P hK0 hQ hq hχ hg hm hJ' hI hG hP
  refine ⟨V, S, hbudget, ?_⟩
  intro b t ht htt₀ hb hmajor hposition hslope
  let u := projectedWorldTag χ g b
  have hu : u 0 ∈ V ∧ u 1 ∈ I (u 0) ∧ (u 2, u 3) ∈ G (u 0) (u 1) :=
    hworld b hb hmajor hposition hslope
  have hj : ⌊t / q⌋ ∈ J := hJcover t htt₀
  have hp := hPcover b t ht htt₀ hposition hslope
  have hmem := hcover ⌊t / q⌋ hj (u 0) hu.1 (u 1) hu.2.1 (u 2, u 3) hu.2.2
    (code q χ g m b t 4) hp
  convert hmem using 1
  ext i
  fin_cases i <;> simp [code, u, projectedWorldTag]

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
