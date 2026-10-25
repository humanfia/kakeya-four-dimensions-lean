import Submission.Obl.k4_scalar_grid_polynomial_qualification.AssignedSupport
import Submission.Obl.k4_scalar_grid_polynomial_qualification.OriginalRows

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory Filter
open Submission.Lib.K4CommonLocalChoice

namespace ScalarData

/-- The frozen hereditary physical counts also control assignments through
fine-state centers. Positive original joint cells are the only pointwise
support requirement; a countable positive-record core supplies it. -/
theorem prepData.original_assigned_physical_support {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k) :
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ D.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
      M = D.prepMesh hprep ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ r r₀ : ℝ,
        R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ r₀ → r₀ ≤ r →
        (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) →
        (∃ m : ℕ, r₀ = (m : ℝ) / (M k : ℝ)) →
        ∀ b : ℝ, 0 < b → b ≤ D.N k ^ (-r) → ∀ E' : Set ScalarIncidence,
        (∀ z ∈ E', (D.ρ k g).restrict (E₀ k g)
          {p | D.phys k r p = D.phys k r z ∧ D.phys k r₀ p = D.phys k r₀ z} ≠ 0) →
        ∀ q : Fin 3 → ℤ, ∃ L : Finset (Fin 3 → ℤ),
          (L.card : ℝ) ≤ 64 * (H k * D.N k ^ ((2 + D.d) * (r - r₀))) ∧
          ∀ z ∈ E', cell (D.N k ^ (-r₀)) (leftCorner b (cell b (scalarPosition z))) = q →
            cell (D.N k ^ (-r)) (leftCorner b (cell b (scalarPosition z))) ∈ L := by
  let M := D.prepMesh hprep
  obtain ⟨hM, hdata⟩ := Classical.choose_spec hprep.2
  refine ⟨M, hM, rfl, ?_⟩
  intro R hR
  filter_upwards [hdata R hR] with k hk
  intro g r r₀ hrlo hrhi hr₀lo hr₀r hrgrid hr₀grid b hb hbp E' hpositive q
  classical
  obtain ⟨_, _, _, _, _, _, _, hgrid, _⟩ := hk.2 g
  obtain ⟨hfinite, _, hhered, _, _⟩ := hgrid r hrlo hrhi hrgrid
  let μ := (D.ρ k g).restrict (E₀ k g)
  let S : (Fin 3 → ℤ) → Set (Fin 3 → ℤ) :=
    fun q₀ => {a | μ {p | D.phys k r p = a ∧ D.phys k r₀ p = q₀} ≠ 0}
  have hS (q₀ : Fin 3 → ℤ) : (S q₀).Finite := by
    apply hfinite.subset
    intro a ha hz
    exact ha (measure_mono_null (fun _ hp => hp.1) hz)
  let F : (Fin 3 → ℤ) → Finset (Fin 3 → ℤ) := fun q₀ => (hS q₀).toFinset
  have hcard (q₀ : Fin 3 → ℤ) : ((F q₀).card : ℝ) ≤ H k * D.N k ^ ((2 + D.d) * (r - r₀)) := by
    rw [← Set.ncard_eq_toFinset_card _ (hS q₀)]
    exact hhered r₀ hr₀lo hr₀r hr₀grid q₀
  have hphys (s : ℝ) (z : ScalarIncidence) :
      D.phys k s z = cell (D.N k ^ (-s)) (scalarPosition z) := by
    funext e
    rfl
  have hmem (z : ScalarIncidence) (hz : z ∈ E') :
      cell (D.N k ^ (-r)) (scalarPosition z) ∈
        F (cell (D.N k ^ (-r₀)) (scalarPosition z)) := by
    apply (hS _).mem_toFinset.mpr
    simpa only [S, μ, hphys, mem_ofPred_eq] using hpositive z hz
  have hρ : b ≤ D.N k ^ (-r₀) := hbp.trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith [hN k]) (by linarith))
  simpa only [show (4 : ℝ) ^ 3 = 64 by norm_num] using
    assigned_hereditary_cell_list scalarPosition E' hb hbp hρ F hcard hmem q

end ScalarData

end Submission.Obl.k4_scalar_grid_polynomial_qualification
