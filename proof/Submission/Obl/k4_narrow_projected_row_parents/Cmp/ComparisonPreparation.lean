/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ComparisonPreparation.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ComparisonTables
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.OriginalGraphTube
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.StoredSheetLists

/-!
# A comparison table from original finite caps and stored witness floors

Both colors retain their own stored witnesses. The current source law may be a further
submeasure. Its density ceilings follow from the native-bin caps, while the list counts
follow from the original witness floors and graph tube caps at coarser widths.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal Classical

noncomputable section

/-- Construct every field of a comparison table from original finite native caps,
stored original witnesses, stable sheets, and a later current source law. -/
def tableOfOriginalFamilies {Ω : Type*} [MeasurableSpace Ω]
    (μ τ : Measure Ω) [IsFiniteMeasure μ] (hτ : τ ≤ μ) (M : ComparisonMesh μ)
    {D n₁ n₂ : ℕ} (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂)
    (hi₁ : Measurable i₁) (hi₂ : Measurable i₂)
    (signal : Ω → ℝ) (hs : Measurable signal)
    (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (hf₁ : ∀ i, IsSheet D (f₁ i)) (hf₂ : ∀ j, IsSheet D (f₂ j))
    (K : NNReal)
    (hlip₁ : ∀ i, LipschitzOnWith K (fun x => f₁ i (emb x)) (closedBall 0 (1 / 2)))
    (hlip₂ : ∀ j, LipschitzOnWith K (fun x => f₂ j (emb x)) (closedBall 0 (1 / 2)))
    {a B F T d L : ℝ} (ha : 0 < a) (hB : 0 < B) (hF : 0 < F) (hT : 0 < T)
    (hL : 14 * B * F ≤ L) (palette : ℝ≥0∞) (hp : palette ≠ 0) (hpt : palette ≠ ⊤)
    (hresolve : 2 * (K : ℝ) * M.diameter ≤ a / 2)
    (hvolume : (∑ _q : Fin M.n, M.vol) ≤ 1)
    (W₁ : Fin n₁ → Set Ω) (W₂ : Fin n₂ → Set Ω)
    (hW₁ : ∀ i, MeasurableSet (W₁ i)) (hW₂ : ∀ j, MeasurableSet (W₂ j))
    (hdisj₁ : Pairwise (fun i j => Disjoint (W₁ i) (W₁ j)))
    (hdisj₂ : Pairwise (fun i j => Disjoint (W₂ i) (W₂ j)))
    (hfloor₁ : ∀ i, ENNReal.ofReal (T / F) * palette ≤ μ (W₁ i))
    (hfloor₂ : ∀ j, ENNReal.ofReal (T / F) * palette ≤ μ (W₂ j))
    (hfit₁ : ∀ i p, p ∈ W₁ i → ‖M.base p‖ ≤ 1 / 2 ∧
      ‖(signal p : ℂ) - f₁ i (emb (M.base p))‖ ≤ a / 4)
    (hfit₂ : ∀ j p, p ∈ W₂ j → ‖M.base p‖ ≤ 1 / 2 ∧
      ‖(signal p : ℂ) - f₂ j (emb (M.base p))‖ ≤ a / 4)
    (hcurrent : ∀ᵐ p ∂τ, p ∈ W₁ (i₁ p) ∧ p ∈ W₂ (i₂ p))
    (hnative : ∀ R : ℝ, a ≤ R → ∀ q j,
      μ {p | M.code p = q ∧ ⌊signal p / R⌋ = j} ≤
        (ENNReal.ofReal (B * T * (R / a) ^ d) * palette) * M.vol) :
    ComparisonTable Ω D d a L (6 * B) := by
  let M' : ComparisonMesh τ := M.mono hτ
  let R₀ : ℝ := T * palette.toReal
  have hR₀ : 0 ≤ R₀ := mul_nonneg hT.le ENNReal.toReal_nonneg
  have hcur₁ : ∀ᵐ p ∂τ, ‖(signal p : ℂ) - f₁ (i₁ p) (emb (M'.base p))‖ ≤ a / 4 := by
    filter_upwards [hcurrent] with p hpw
    exact (hfit₁ _ p hpw.1).2
  have hcur₂ : ∀ᵐ p ∂τ, ‖(signal p : ℂ) - f₂ (i₂ p) (emb (M'.base p))‖ ≤ a / 4 := by
    filter_upwards [hcurrent] with p hpw
    exact (hfit₂ _ p hpw.2).2
  have hnat (q : Fin M.n) (j : ℤ) :
      τ {p | M'.code p = q ∧ ⌊signal p / a⌋ = j} ≤
        (ENNReal.ofReal (B * T) * palette) * M'.vol := by
    change τ {p | M.code p = q ∧ ⌊signal p / a⌋ = j} ≤
      (ENNReal.ofReal (B * T) * palette) * M.vol
    have h := (hτ _).trans (hnative a le_rfl q j)
    simpa only [div_self ha.ne', Real.one_rpow, mul_one] using h
  have hceiling : (6 : ℝ≥0∞) * (ENNReal.ofReal (B * T) * palette) =
      ENNReal.ofReal ((6 * B) * R₀) := by
    calc
      _ = ENNReal.ofReal (6 * (B * T)) * palette := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat, mul_assoc]
      _ = ENNReal.ofReal ((6 * B) * R₀) := by
        rw [show (6 * B) * R₀ = (6 * (B * T)) * palette.toReal by dsimp [R₀]; ring,
          ENNReal.ofReal_mul (show 0 ≤ 6 * (B * T) by positivity),
          ENNReal.ofReal_toReal hpt]
  have hsmall : a / 4 + (K : ℝ) * M'.diameter ≤ a := by
    change a / 4 + (K : ℝ) * M.diameter ≤ a
    linarith
  have hcap₁ (q : Fin M'.n) (i : Fin n₁) :
      τ {p | M'.code p = q ∧ i₁ p = i} ≤ ENNReal.ofReal ((6 * B) * R₀) * M'.vol := by
    have h := index_cell_cap_of_native_bins τ M' i₁ signal (fun i x => f₁ i (emb x)) K ha hsmall
      hlip₁ hcur₁ (ENNReal.ofReal (B * T) * palette) hnat q i
    rwa [hceiling] at h
  have hcap₂ (q : Fin M'.n) (j : Fin n₂) :
      τ {p | M'.code p = q ∧ i₂ p = j} ≤ ENNReal.ofReal ((6 * B) * R₀) * M'.vol := by
    have h := index_cell_cap_of_native_bins τ M' i₂ signal (fun j x => f₂ j (emb x)) K ha hsmall
      hlip₂ hcur₂ (ENNReal.ofReal (B * T) * palette) hnat q j
    rwa [hceiling] at h
  have hagreement : ∀ᵐ p ∂τ,
      ‖f₁ (i₁ p) (emb (M'.base p)) - f₂ (i₂ p) (emb (M'.base p))‖ ≤ a / 2 := by
    filter_upwards [hcur₁, hcur₂] with p h₁ h₂
    have h := dist_triangle (f₁ (i₁ p) (emb (M'.base p))) (signal p : ℂ)
      (f₂ (i₂ p) (emb (M'.base p)))
    simp only [dist_eq_norm] at h
    rw [norm_sub_rev (f₁ (i₁ p) (emb (M'.base p))) (signal p : ℂ)] at h
    linarith
  have hlists : NearbyListBound a L d f₁ f₂ := by
    intro i₀ R hR
    have hRpos : 0 < R := ha.trans_le hR
    have hsmallR : (K : ℝ) * M.diameter ≤ R := by linarith
    have htube := original_graph_tube_cap μ M signal hs (fun x => f₁ i₀ (emb x)) K
      (hlip₁ i₀) hRpos hsmallR hvolume
      (ENNReal.ofReal (B * T * (R / a) ^ d) * palette) (hnative R hR)
    have htube' : μ {p | ‖M.base p‖ ≤ 1 / 2 ∧
        ‖(signal p : ℂ) - f₁ i₀ (emb (M.base p))‖ ≤ 2 * R} ≤
        ENNReal.ofReal ((14 * B) * T * (R / a) ^ d) * palette := by
      refine htube.trans_eq ?_
      rw [← ENNReal.ofReal_ofNat 14, ← mul_assoc,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 14)]
      congr 2
      ring
    have hcount {n : ℕ} (W : Fin n → Set Ω) (hW : ∀ i, MeasurableSet (W i))
        (hdisj : Pairwise (fun i j => Disjoint (W i) (W j)))
        (f : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ)
        (hfloor : ∀ i, ENNReal.ofReal (T / F) * palette ≤ μ (W i))
        (hfit : ∀ i p, p ∈ W i → ‖M.base p‖ ≤ 1 / 2 ∧
          ‖(signal p : ℂ) - f i (emb (M.base p))‖ ≤ a / 4) :
        ((Finset.univ.filter fun i : Fin n => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
          ‖f i (emb x) - f₁ i₀ (emb x)‖ ≤ R).card : ℝ) ≤ L * (R / a) ^ d := by
      have h := stored_sheet_list_count μ W hdisj hW M.base (fun p => (signal p : ℂ))
        (fun i x => f i (emb x)) (fun x => f₁ i₀ (emb x)) ha hR hF (by positivity) hT
        palette hp hpt hfloor (fun i p hpw => ⟨(hfit i p hpw).1, (hfit i p hpw).2.trans (by linarith)⟩)
        htube'
      exact h.trans (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (by positivity) _))
    exact ⟨hcount W₁ hW₁ hdisj₁ f₁ hfloor₁ hfit₁, hcount W₂ hW₂ hdisj₂ f₂ hfloor₂ hfit₂⟩
  exact
    { law := τ
      finite := isFiniteMeasure_of_le μ hτ
      mesh := M'
      n₁ := n₁
      n₂ := n₂
      i₁ := i₁
      i₂ := i₂
      measurable_i₁ := hi₁
      measurable_i₂ := hi₂
      f₁ := f₁
      f₂ := f₂
      sheet₁ := hf₁
      sheet₂ := hf₂
      T₁ := fun _ => R₀
      T₂ := fun _ => R₀
      nonneg₁ := fun _ => hR₀
      nonneg₂ := fun _ => hR₀
      cap₁ := hcap₁
      cap₂ := hcap₂
      lip := K
      lip₁ := hlip₁
      lip₂ := hlip₂
      resolved := hresolve
      agreement := hagreement
      lists := hlists }

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
