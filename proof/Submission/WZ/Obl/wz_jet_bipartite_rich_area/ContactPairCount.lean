-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactPairCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGraph
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGridPairs
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.MonotoneSublevel

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open scoped Classical
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- Uniform pair multiplicity in a transverse dyadic slope band. -/
theorem cell_pair_count_transverse {α β : Type*}
    (S : Finset (ℤ × ℤ × ℤ)) (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β)
    (tag : ℤ × ℤ × ℤ → ℝ) (gA : α → ℝ → ℝ) (gB : β → ℝ → ℝ) (f₀ : ℝ → ℝ)
    (hgA : ∀ a, ContDiff ℝ 2 (gA a)) (hgB : ∀ b, ContDiff ℝ 2 (gB b))
    {δ s ℓ w l u c : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (hc : 0 < c)
    (hmesh : δ ≤ 2 * s * ℓ)
    (hcurv : ∀ a b, ∀ z ∈ Icc l u, c ≤ |deriv (deriv (gA a - gB b)) z|)
    (hcell : ∀ t ∈ S, JetCell (gA (red t)) f₀ δ s ℓ w 42 t)
    (hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ)
    (htag : ∀ t ∈ S, tag t ∈ Icc l u ∧
      NearContact (2 * δ) s (gA (red t)) (gB (blue t)) (tag t) ∧
      s / 2 ≤ |deriv (gA (red t)) (tag t) - deriv (gB (blue t)) (tag t)|)
    (a : α) (b : β) :
    (S.filter (fun t => red t = a ∧ blue t = b)).card ≤ 30000000 := by
  classical
  have hF : ContDiff ℝ 2 (gA a - gB b) := (hgA a).sub (hgB b)
  have hmono' : MonotoneOn (deriv (gA a - gB b)) (Icc l u) ∨
      AntitoneOn (deriv (gA a - gB b)) (Icc l u) := by
    apply WangZahlLot.Obl.wz_jet_transverse_pair_moment.monotone_deriv_of_deriv2_ne_zero hF
    intro z hz heq
    have hh := hcurv a b z hz
    rw [heq, abs_zero] at hh
    linarith
  have hscale : 2 * (2 * δ) / (s / 2) + 2 * ℓ ≤ (18 : ℕ) * ℓ := by
    have hds : δ / s ≤ 2 * ℓ := (div_le_iff₀ hs).mpr (by nlinarith)
    have heq : 2 * (2 * δ) / (s / 2) = 8 * (δ / s) := by field_simp <;> norm_num
    rw [heq]
    norm_num
    nlinarith
  have hh := card_jetCell_transverse_pair
    (S.filter (fun t => red t = a ∧ blue t = b)) tag hδ hs hℓ (by linarith : 0 < s / 2)
    42 18 (hF.differentiable (by norm_num)) hmono'
    (f := gA a) (f₀ := f₀) (w := w) (A := 2 * δ)
    (fun t ht => by
      have ht' := Finset.mem_filter.mp ht
      simpa only [ht'.2.1] using hcell t ht'.1)
    (fun t ht => hnear t (Finset.mem_filter.mp ht).1)
    (fun t ht => by
      have ht' := Finset.mem_filter.mp ht
      have hv := htag t ht'.1
      rw [ht'.2.1, ht'.2.2] at hv
      refine ⟨hv.1, ?_, ?_⟩
      · exact hv.2.1.1
      · rw [deriv_sub_of_contDiff_two (hgA a) (hgB b)]
        exact hv.2.2) hscale
  exact hh.trans (by norm_num)

/-- The same uniform constant covers the natural small-slope band. -/
theorem cell_pair_count_natural {α β : Type*}
    (S : Finset (ℤ × ℤ × ℤ)) (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β)
    (tag : ℤ × ℤ × ℤ → ℝ) (gA : α → ℝ → ℝ) (gB : β → ℝ → ℝ) (f₀ : ℝ → ℝ)
    (hgA : ∀ a, ContDiff ℝ 2 (gA a)) (hgB : ∀ b, ContDiff ℝ 2 (gB b))
    {δ s ℓ w l u D : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (hD : 0 < D)
    (hmesh : δ ≤ 2 * s * ℓ) (hnat : s ^ 2 ≤ δ * D)
    (hcurv : ∀ a b, ∀ z ∈ Icc l u, D / 120 ≤ |deriv (deriv (gA a - gB b)) z|)
    (hcell : ∀ t ∈ S, JetCell (gA (red t)) f₀ δ s ℓ w 42 t)
    (hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ)
    (htag : ∀ t ∈ S, tag t ∈ Icc l u ∧
      NearContact (2 * δ) s (gA (red t)) (gB (blue t)) (tag t))
    (a : α) (b : β) :
    (S.filter (fun t => red t = a ∧ blue t = b)).card ≤ 30000000 := by
  classical
  have hF : ContDiff ℝ 2 (gA a - gB b) := (hgA a).sub (hgB b)
  have hscale : 2 * s / (D / 120) + 2 * ℓ ≤ (482 : ℕ) * ℓ := by
    have hds : δ / s ≤ 2 * ℓ := (div_le_iff₀ hs).mpr (by nlinarith)
    have hsd : s / D ≤ δ / s := (div_le_div_iff₀ hD hs).mpr (by nlinarith [hnat])
    have heq : 2 * s / (D / 120) = 240 * (s / D) := by field_simp <;> norm_num
    rw [heq]
    norm_num
    nlinarith
  have hh := card_jetCell_small_slope_pair
    (S.filter (fun t => red t = a ∧ blue t = b)) tag hδ hs hℓ (by positivity : 0 < D / 120)
    42 482 hF (hcurv a b) (f := gA a) (f₀ := f₀) (w := w) (η := s)
    (fun t ht => by
      have ht' := Finset.mem_filter.mp ht
      simpa only [ht'.2.1] using hcell t ht'.1)
    (fun t ht => hnear t (Finset.mem_filter.mp ht).1)
    (fun t ht => by
      have ht' := Finset.mem_filter.mp ht
      have hv := htag t ht'.1
      rw [ht'.2.1, ht'.2.2] at hv
      refine ⟨hv.1, ?_⟩
      rw [deriv_sub_of_contDiff_two (hgA a) (hgB b)]
      exact hv.2.2) hscale
  exact hh.trans (by norm_num)

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
