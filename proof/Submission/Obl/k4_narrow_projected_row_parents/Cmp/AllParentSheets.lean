/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/AllParentSheets.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonNativeSheets
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentSupportBudget

/-!
# Native sheets of all true parents at one depth

`all_parents_native_sheets` runs `parent_native_sheets` for every true parent at depth `s` with
one common radius `ρ = (2K · 442368 K⁶)^(-n)` and one measurable deleted event
`E = ⋃ i, (B_i × block_i) ∩ E_i`. Its original mass is at most `K ζ` with
`ζ = (2K · parentFilling)^(-A) + (2K · 442368 K⁶)^(-A)`, because the parent sets at one depth
have total original mass at most `K` (accepted o253 `sum_original_parent_mass_le`). The mesh
resolution is one uniform inequality for all parents (`parent_resolve`), from `|c| ≤ K`.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

noncomputable section

theorem SheetOn.mono_radius {R : MvPolynomial (Fin 4) ℂ} {g : EuclideanSpace ℂ (Fin 3) → ℂ}
    {c : EuclideanSpace ℝ (Fin 3)} {r r' V : ℝ} (h : SheetOn R g c r V) (hr : r' ≤ r) :
    SheetOn R g c r' V :=
  ⟨h.1.mono (ball_subset_ball hr), fun z hz => h.2.1 z (ball_subset_ball hr hz),
    fun z hz => h.2.2.1 z (ball_subset_ball hr hz), fun x hx => h.2.2.2 x (lt_of_lt_of_le hx hr)⟩

theorem parentMatrix_row0 (K Q g : ℝ) (c : Fin 5 → ℝ) (δ : ℝ) :
    (∑ j, |parentMatrix K Q g c 0 j| * δ) = |1 / (32 * K * Q)| * δ := by
  simp [parentMatrix, Fin.sum_univ_three]

theorem parentMatrix_row1 (K Q g : ℝ) (c : Fin 5 → ℝ) (δ : ℝ) :
    (∑ j, |parentMatrix K Q g c 1 j| * δ) = |1 / (32 * K * Q)| * δ := by
  simp [parentMatrix, Fin.sum_univ_three]

theorem parentMatrix_row2 (K Q g : ℝ) (c : Fin 5 → ℝ) (δ : ℝ) :
    (∑ j, |parentMatrix K Q g c 2 j| * δ) =
      (|c 3 / (16 * K * Q * g)| + |c 4 / (16 * K * Q * g)| + |1 / (16 * K * Q * g)|) * δ := by
  simp [parentMatrix, Fin.sum_univ_three, abs_div]
  ring

/-- One inequality resolves the support zoom of every parent at one depth. -/
theorem parent_resolve {α : Type} [MeasurableSpace α] (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) {R : ℝ} {k : ℕ} {s : ℝ} (hs : 0 ≤ s) (hatlas : a.AtlasAt p R k s)
    (i : Fin (a.n k s)) {δ σ : ℝ} (hδ : 0 ≤ δ)
    (h : δ * (2 * p.K k + 2) ≤ σ * (16 * p.K k * a.q k s * narrow p k s)) :
    ∀ e, (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * δ) ≤ σ := by
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hK0 : 0 < p.K k := by linarith
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hq : 0 < a.q k s := by unfold PreparedModel.q; positivity
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have hg1 : narrow p k s ≤ 1 := by
    unfold narrow
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k])
    have := hp.2.2.2.2.2.2.2.1
    nlinarith
  have hc : ∀ e, |a.c k s i e| ≤ p.K k := (hatlas.2.2.2.2.1 i).2.2.2.1
  set D := 16 * p.K k * a.q k s * narrow p k s with hD
  have hDpos : 0 < D := by positivity
  have hσ : δ * (2 * p.K k + 2) / D ≤ σ := by rw [div_le_iff₀ hDpos]; exact h
  have h01 : |1 / (32 * p.K k * a.q k s)| * δ ≤ σ := by
    refine le_trans ?_ hσ
    rw [abs_of_pos (by positivity), div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hDpos,
      hD]
    have hδK : δ * (16 * p.K k * a.q k s * narrow p k s) ≤ δ * (16 * p.K k * a.q k s) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      nlinarith [mul_pos hK0 hq]
    have h2 : δ * (16 * p.K k * a.q k s) ≤ δ * (2 * p.K k + 2) * (32 * p.K k * a.q k s) := by
      have : 16 * p.K k * a.q k s ≤ (2 * p.K k + 2) * (32 * p.K k * a.q k s) := by
        nlinarith [mul_pos hK0 hq]
      nlinarith
    linarith
  intro e
  rw [parentSupportZoom_baseMatrix]
  fin_cases e
  · exact (parentMatrix_row0 _ _ _ _ δ).trans_le h01
  · exact (parentMatrix_row1 _ _ _ _ δ).trans_le h01
  · refine (parentMatrix_row2 _ _ _ _ δ).trans_le (le_trans ?_ hσ)
    rw [abs_div, abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 16 * p.K k * a.q k s * narrow p k s),
      abs_one, ← hD]
    rw [show (|a.c k s i 3| / D + |a.c k s i 4| / D + 1 / D) * δ =
      δ * (|a.c k s i 3| + |a.c k s i 4| + 1) / D by ring]
    apply div_le_div_of_nonneg_right _ hDpos.le
    apply mul_le_mul_of_nonneg_left _ hδ
    linarith [hc 3, hc 4]

set_option maxHeartbeats 4000000 in
/-- **Native sheets of all true parents at one depth.** -/
theorem all_parents_native_sheets :
    ∃ αc βc : ℕ, 1 ≤ βc ∧ ∀ (A : ℕ) {α : Type} [MeasurableSpace α] (p : Parameters), p.Valid →
      ∀ a : PreparedModel α, a.Common p → ∀ (R : ℝ) (k : ℕ) (s : ℝ), 0 ≤ s →
      a.AtlasAt p R k s → ∀ δ₀ σ₀ δ₁ σ₁ : ℝ,
      0 < δ₀ → 0 < σ₀ → 0 < δ₁ → 0 < σ₁ →
      δ₀ * (2 * p.K k + 2) ≤ σ₀ * (16 * p.K k * a.q k s * narrow p k s) →
      δ₁ * (2 * p.K k + 2) ≤ σ₁ * (16 * p.K k * a.q k s * narrow p k s) →
      (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ (αc * A + βc) * σ₀ ≤ 1 →
      (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ (αc * A + βc) * σ₁ ≤ width p k s →
      (2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc) * σ₁ ≤ 1 →
      (∀ q : Fin 3 → ℤ, a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₀
          (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q} ≤
        ENNReal.ofReal ((4 * p.K k + 2) * p.K k * δ₀ ^ 3)) →
      (∀ (q : Fin 3 → ℤ) (x₀ : ℤ), a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₁
          (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q ∧
          ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋ = x₀} ≤
        ENNReal.ofReal (p.K k * width p k s ^ p.d * δ₁ ^ 3)) →
      ∃ (Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ)
        (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ) (E : Set (α × ℝ)),
        (∀ i, Rel i ≠ 0 ∧ (Rel i).totalDegree ≤ 4) ∧ MeasurableSet E ∧
        a.mu k E ≤ ENNReal.ofReal (p.K k *
          (((2 * p.K k * parentFilling (p.K k) (width p k s)) ^ A)⁻¹ +
            ((2 * p.K k * parentBinCap (p.K k)) ^ A)⁻¹)) ∧
        ∀ i, ∀ᵐ z ∂a.mu k, z ∈ a.parentSet k s i → z ∉ E →
          SheetOn (Rel i) (g i (branch ((a.parentSupportZoom p k s i).push (a.F k s i))
              (rootBaseCoordinates (parentZoomPoint p a k s i z))
              (parentZoomPoint p a k s i z 3)))
            (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z)))
            (4 * ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))⁻¹)
            ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc)) ∧
          |eval (a.x k z.1 z.2) (a.P k) -
            (g i (branch ((a.parentSupportZoom p k s i).push (a.F k s i))
              (rootBaseCoordinates (parentZoomPoint p a k s i z))
              (parentZoomPoint p a k s i z 3))
              (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))))).re| ≤
            32 * (2 * p.K k) ^ 9 * width p k s := by
  obtain ⟨αc, βc, hβc, hpar⟩ := parent_native_sheets
  refine ⟨αc, βc, hβc, ?_⟩
  intro A α _ p hp a hcommon R k s hs hatlas δ₀ σ₀ δ₁ σ₁ hδ₀ hσ₀ hδ₁ hσ₁ hr₀ hr₁ hm₀ hm₁ hm₂
    hcap₀ hcapS
  have hone := fun i => hpar A p hp a hcommon R k s hs hatlas i δ₀ σ₀ δ₁ σ₁ hδ₀ hσ₀ hδ₁ hσ₁
    (parent_resolve p hp a hs hatlas i hδ₀.le hr₀) (parent_resolve p hp a hs hatlas i hδ₁.le hr₁)
    hm₀ hm₁ hm₂ hcap₀ hcapS
  choose ρf Relf gf Ef hρf hρf1 hRelf hRelfd hEfm hEf haef using hone
  set ζ := ((2 * p.K k * parentFilling (p.K k) (width p k s)) ^ A)⁻¹ +
    ((2 * p.K k * parentBinCap (p.K k)) ^ A)⁻¹ with hζ
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hζ0 : 0 ≤ ζ := by
    have h1 : 0 ≤ parentFilling (p.K k) (width p k s) := by
      unfold parentFilling
      have hN : 0 < p.N k := by linarith [hp.1 k]
      have : 0 < width p k s := Real.rpow_pos_of_pos hN _
      positivity
    have h2 : 0 ≤ parentBinCap (p.K k) := by unfold parentBinCap; positivity
    positivity
  refine ⟨Relf, gf, ⋃ i, (a.parentSet k s i ∩ Ef i), fun i => ⟨hRelf i, hRelfd i⟩,
    MeasurableSet.iUnion fun i => (a.measurableSet_parentSet p hatlas i).inter (hEfm i), ?_, ?_⟩
  · calc a.mu k (⋃ i, (a.parentSet k s i ∩ Ef i))
        ≤ ∑ i, a.mu k (a.parentSet k s i ∩ Ef i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ i, a.mu k (a.parentSet k s i) * ENNReal.ofReal ζ :=
          Finset.sum_le_sum fun i _ => hEf i
      _ = (∑ i, a.mu k (a.parentSet k s i)) * ENNReal.ofReal ζ := by rw [Finset.sum_mul]
      _ ≤ ENNReal.ofReal (p.K k) * ENNReal.ofReal ζ := by
          gcongr
          exact a.sum_original_parent_mass_le p hp hcommon hatlas
      _ = ENNReal.ofReal (p.K k * ζ) := (ENNReal.ofReal_mul (by linarith)).symm
  · intro i
    filter_upwards [haef i] with z hz hzP hzE
    have hzEi : z ∉ Ef i := fun h => hzE (mem_iUnion.mpr ⟨i, hzP, h⟩)
    obtain ⟨h1, h2⟩ := hz hzP hzEi
    exact ⟨h1.mono_radius (by linarith [hρf i]), h2⟩

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
