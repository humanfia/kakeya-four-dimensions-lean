-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/OriginalFiberSelection.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/OriginalFiberSelection.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/OriginalFiberSelection.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.ArbitraryFiberLists
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.CommonFiberTables

/-!
Original fitting durations produce the local coefficient lists required
for the four common table choices. All polynomial and field families may
be infinite; only the grid keys are finite. The resulting original mass
loss is a fixed power of the original conditioning parameter.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- A common field and three common polynomial coefficient tables with a
fixed-power ORIGINAL mass cost, derived from actual old fitting witnesses. -/
theorem original_common_fiber_selection (D q : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ {X S : Type} [MeasurableSpace X]
      [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
      (μ : Measure X) [IsFiniteMeasure μ]
      (grid : X → S × S × S), Measurable grid →
      ∀ (G : X → Fin q → ℝ), Measurable G →
      ∀ (P : Fin 3 → X → Fin q → Polynomial ℝ),
      (∀ axis, Measurable (fun x => polynomialFitCoefficients D (P axis x))) →
      ∀ (Ω : Set X), MeasurableSet Ω →
      ∀ p K : ℝ, 0 < p → 1 ≤ K →
      (∀ axis x, x ∈ Ω → ∀ j, (P axis x j).natDegree ≤ D) →
      ∀ E : Fin 3 → X → Set ℝ,
      (∀ axis x, x ∈ Ω → MeasurableSet (E axis x)) →
      (∀ axis x, x ∈ Ω → E axis x ⊆ Icc (0 : ℝ) 1) →
      (∀ axis x, x ∈ Ω → ENNReal.ofReal (1 / K) ≤ volume (E axis x)) →
      ∀ H : Fin 3 → X → ℝ → Fin q → ℝ,
      (∀ axis x, x ∈ Ω → ∀ t ∈ E axis x, ∀ j,
        |(P axis x j).eval t - H axis x t j| ≤ p) →
      (∀ g, ∃ F : Finset (Fin q → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Ω, grid x = g → cell p (G x) ∈ F) →
      (∀ axis key t, ∃ F : Finset (Fin q → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Ω, gridFiberKey axis (grid x) = key → t ∈ E axis x →
          cell p (H axis x t) ∈ F) →
      ∃ (value : S × S × S → Fin q → ℤ)
        (fiber : Fin 3 → S × S → Fin (q * (D + 1)) → ℤ) (T : Set X),
        MeasurableSet T ∧ T ⊆ Ω ∧
        (∀ x, x ∈ T ↔ x ∈ Ω ∧ cell p (G x) = value (grid x) ∧
          ∀ axis, polynomialFitCoefficientCode D p (P axis x) =
            fiber axis (gridFiberKey axis (grid x))) ∧
        μ.real Ω ≤ B * K ^ (1 + 3 * (3 + 3 * D * (q * (D + 1)))) * μ.real T := by
  classical
  obtain ⟨A, hA, hpacking⟩ := approximate_original_field_fiber_lists D q
  refine ⟨2 * (A + 1) ^ 3, by positivity, ?_⟩
  intro X S _ _ _ _ μ _ grid hgrid G hG P hPmeas Ω hΩ p K hp hK
    hdegree E hE hunit hduration H hfit hfield hlocal
  let b := 3 + 3 * D * (q * (D + 1))
  let K₀ := ⌈K⌉₊
  let Kf := ⌈A * K ^ b⌉₊
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  have hfield' : ∀ g, ∃ F : Finset (Fin q → ℤ), F.card ≤ K₀ ∧
      ∀ x ∈ Ω, grid x = g → cell p (G x) ∈ F := by
    intro g
    obtain ⟨F, hF, hFm⟩ := hfield g
    exact ⟨F, by exact_mod_cast hF.trans (Nat.le_ceil K), hFm⟩
  have hfiber' : ∀ axis key, ∃ F : Finset (Fin (q * (D + 1)) → ℤ), F.card ≤ Kf ∧
      ∀ x ∈ Ω, gridFiberKey axis (grid x) = key →
        cell p (polynomialFitCoefficients D (P axis x)) ∈ F := by
    intro axis key
    let I := {x : X // x ∈ Ω ∧ gridFiberKey axis (grid x) = key}
    obtain ⟨F, hF, hFm⟩ := hpacking I (fun x => P axis x.1)
      (fun x => hdegree axis x.1 x.2.1) (fun x => E axis x.1)
      (fun x => hE axis x.1 x.2.1) (fun x => hunit axis x.1 x.2.1)
      p K hp hK (fun x => hduration axis x.1 x.2.1) (fun x => H axis x.1)
      (fun x => hfit axis x.1 x.2.1) (fun t => by
        obtain ⟨V, hV, hVm⟩ := hlocal axis key t
        exact ⟨V, hV, fun x hx => hVm x.1 x.2.1 x.2.2 hx⟩)
    refine ⟨F, by exact_mod_cast hF.trans (Nat.le_ceil (A * K ^ b)), ?_⟩
    intro x hx hkey
    exact hFm ⟨x, hx, hkey⟩
  obtain ⟨value, fiber, T, hT, hTΩ, hmem, hmass⟩ := select_common_grid_fiber_codes μ
    grid hgrid G hG (fun axis x => polynomialFitCoefficients D (P axis x)) hPmeas
    Ω hΩ p K₀ Kf hfield' hfiber'
  refine ⟨value, fiber, T, hT, hTΩ, hmem, hmass.trans ?_⟩
  have hceil₀ : (K₀ : ℝ) ≤ 2 * K := by
    have hc := Nat.ceil_lt_add_one hKnonneg
    dsimp only [K₀]
    linarith
  have hKb : 1 ≤ K ^ b := one_le_pow₀ hK
  have hceilf : (Kf : ℝ) ≤ (A + 1) * K ^ b := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ A * K ^ b by positivity)
    dsimp only [Kf]
    nlinarith
  have hproduct : (K₀ : ℝ) * (Kf : ℝ) ^ 3 ≤
      (2 * (A + 1) ^ 3) * K ^ (1 + 3 * b) := by
    calc
      _ ≤ (2 * K) * ((A + 1) * K ^ b) ^ 3 :=
        mul_le_mul hceil₀ (pow_le_pow_left₀ (by positivity) hceilf 3)
          (by positivity) (by positivity)
      _ = (2 * (A + 1) ^ 3) * K ^ (1 + 3 * b) := by
        rw [mul_pow, ← pow_mul, pow_add, pow_one]
        simp only [Nat.mul_comm b 3]
        ring
  exact mul_le_mul_of_nonneg_right hproduct measureReal_nonneg

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
