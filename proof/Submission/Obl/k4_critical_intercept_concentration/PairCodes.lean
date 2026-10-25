/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/PairCodes.lean.
   Original source attributions below are preserved. -/
import Submission.Lib.K4ModelReduction.FiniteTable

namespace Submission.Obl.k4_critical_intercept_concentration

open Set MeasureTheory

noncomputable section

/-- Exact midpoint-intercept bin paired with the ORIGINAL normalized base code. -/
def pairCode {Ω : Type*} (a δ : ℝ) (value : Ω → ℝ) (point : Ω → Fin 3 → ℝ)
    (p : Ω) : ℤ × (Fin 3 → ℤ) :=
  (⌊value p / a⌋, fun i => ⌊point p i / δ⌋)

theorem measurable_pairCode {Ω : Type*} [MeasurableSpace Ω]
    (a δ : ℝ) {value : Ω → ℝ} {point : Ω → Fin 3 → ℝ}
    (hvalue : Measurable value) (hpoint : Measurable point) :
    Measurable (pairCode a δ value point) := by
  unfold pairCode
  fun_prop

/-- Bounded original signals give a finite set of ACTUAL occupied pairs.
The enclosing rectangular grid is used only for finiteness, not for the
quantitative pair budget. -/
theorem finite_actual_pair_codes {Ω : Type*} (E : Set Ω)
    (value : Ω → ℝ) (point : Ω → Fin 3 → ℝ)
    (a δ V B : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hvalue : ∀ p ∈ E, |value p| ≤ V) (hpoint : ∀ p ∈ E, ∀ i, |point p i| ≤ B) :
    ((pairCode a δ value point) '' E).Finite := by
  classical
  let bins := (Submission.Lib.K4ModelReduction.meshCodes Unit a V).image (fun q => q ())
  let cells := Submission.Lib.K4ModelReduction.meshCodes (Fin 3) δ B
  refine (bins.product cells).finite_toSet.subset ?_
  rintro u ⟨p, hp, rfl⟩
  apply Finset.mem_product.mpr
  constructor
  · have hb := Submission.Lib.K4ModelReduction.meshTag_mem_codes (ι := Unit) ha
      (fun _ => value p) (fun _ => hvalue p hp)
    exact Finset.mem_image.mpr ⟨_, hb, rfl⟩
  · exact Submission.Lib.K4ModelReduction.meshTag_mem_codes hδ (point p) (hpoint p hp)

/-- Finite pair membership retains an actual original-source witness. -/
theorem exists_actual_pair_table {Ω : Type*} (E : Set Ω)
    (value : Ω → ℝ) (point : Ω → Fin 3 → ℝ)
    (a δ V B : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hvalue : ∀ p ∈ E, |value p| ≤ V) (hpoint : ∀ p ∈ E, ∀ i, |point p i| ≤ B) :
    ∃ F : Finset (ℤ × (Fin 3 → ℤ)),
      ∀ u, u ∈ F ↔ ∃ p ∈ E, pairCode a δ value point p = u := by
  classical
  let hf := finite_actual_pair_codes E value point a δ V B ha hδ hvalue hpoint
  exact ⟨hf.toFinset, fun u => by simp only [Set.Finite.mem_toFinset, Set.mem_image]⟩

end

end Submission.Obl.k4_critical_intercept_concentration
