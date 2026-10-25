-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.FiberLevels.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.UniformFibers
import Submission.WZ.Obl.wz_separated_projection_dichotomy.DyadicDepth

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

/-- The total mass in cells below a prescribed relative size is controlled
by the number of cells, even when the original set is arbitrarily large. -/
theorem small_fiber_card_le {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (f : X → Y) (hf : ∀ x ∈ S, f x ∈ T)
    {a : ℝ} (ha : 0 ≤ a) :
    ((S.filter (fun x => ((S.filter (fun z => f z = f x)).card : ℝ) < a * (S.card : ℝ))).card : ℝ)
      ≤ a * (S.card : ℝ) * (T.card : ℝ) := by
  classical
  let U := T.filter (fun y => ((S.filter (fun z => f z = y)).card : ℝ) < a * (S.card : ℝ))
  have hu : ∀ y ∈ U, ((S.filter (fun z => f z = y)).card : ℝ) ≤ a * (S.card : ℝ) :=
    fun y hy => (Finset.mem_filter.mp hy).2.le
  have h := upper_fiber_count S U f hu
  have heq : S.filter (fun x => f x ∈ U) =
      S.filter (fun x => ((S.filter (fun z => f z = f x)).card : ℝ) < a * (S.card : ℝ)) := by
    ext x
    simp only [Finset.mem_filter, U]
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hf x hx.1, hx.2⟩⟩
  rw [heq] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- Every cell above the cutoff lies in one of finitely many dyadic mass
classes; each class has a factor-two fiber bound. -/
theorem fiber_mass_level {X Y : Type*} [DecidableEq Y]
    (S : Finset X) (f : X → Y) {a : ℝ} {n : ℕ}
    (hS : S.Nonempty) (ha : 0 < a) (hlast : dyadicRadius (n + 1) < a)
    {y : Y} (hy : a * (S.card : ℝ) ≤ ((S.filter (fun x => f x = y)).card : ℝ)) :
    ∃ k ∈ Finset.range (n + 1),
      dyadicRadius k * (S.card : ℝ) / 2 < ((S.filter (fun x => f x = y)).card : ℝ) ∧
      ((S.filter (fun x => f x = y)).card : ℝ) ≤ dyadicRadius k * (S.card : ℝ) := by
  have hN : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hlow : a ≤ ((S.filter (fun x => f x = y)).card : ℝ) / (S.card : ℝ) :=
    (le_div_iff₀ hN).mpr hy
  have hu : ((S.filter (fun x => f x = y)).card : ℝ) / (S.card : ℝ) ≤ 32 := by
    apply (div_le_iff₀ hN).mpr
    have hc : ((S.filter (fun x => f x = y)).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le S _
    linarith
  obtain ⟨k, hk, hkU, hkL⟩ := dyadicRadius_cover ha hlast hlow hu
  refine ⟨k, hk, ?_, (div_le_iff₀ hN).mp hkU⟩
  have hh := (lt_div_iff₀ hN).mp (show dyadicRadius k <
    (2 * ((S.filter (fun x => f x = y)).card : ℝ)) / (S.card : ℝ) by simpa [mul_div_assoc] using hkL)
  linarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
