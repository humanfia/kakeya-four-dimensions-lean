-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CellProfile
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X305Helpers
-- Copied from session x0338 (o070 branch, commit ec01e52, file StickyPieces.lean), namespace renamed.

/-!
# Pieces of the sticky branch

The sticky branch of the derived trichotomy ends with x0305's `allScales_of_prepared`
(`X305/StickyBranch.lean`), whose hypotheses are: common classes, populations within `δ^(-ξ)` at
every level (`hbal`), cells `δ^(-ξ)`-Frostman at their radius (`hFF`), and global Frostman
(`hFG`).  This file turns the outputs of the per-level refinement into these hypotheses:

* `fibre_frostman_of_katzTao`: a cell inside a Katz–Tao set with constant `c`, holding at least
  `t` tubes with `c ρ² ≤ δ^(-ξ) t δ²`, is `δ^(-ξ)`-Frostman at radius `ρ` (the form of `hFF`);
* `pop_ratio_of_bounds`: populations in `[t, P]` with `P ≤ δ^(-ξ) t` (the form of `hbal`);
* `frostman_of_subset`: global Frostman passes to a subset with the size loss (the form of `hFG`).

It also identifies the grid cells of this namespace with x0305's: `lineGridCell = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric MeasureTheory

/-- The grid cells of `RoundBox.lean` are x0305's `lineCell`. -/
lemma lineGridCell_eq_lineCell (s : ℝ) (x v : Space) :
    lineGridCell s x v = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell s x v := rfl

/-- The populations of `CellProfile.lean` are x0305's `pop`. -/
lemma cellPop_eq_pop {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n)) (s : ℝ) (i : Fin n) :
    cellPop x v S s i = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.pop S (fun j => WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.lineCell s (x j) (v j)) i := rfl

open Classical in
/-- **Fibre Frostman from Katz–Tao.**  If the cell of `i₀` in `S` lies in a set `F'` that is
Katz–Tao with constant `c` (`#{F' in W} δ² ≤ c |W|`), the cell holds at least `t` tubes, and
`c ρ² ≤ δ^(-ξ) t δ²`, then the cell is `δ^(-ξ)`-Frostman at radius `ρ`. -/
theorem fibre_frostman_of_katzTao {n : ℕ} (x v : Fin n → Space) (S F' : Finset (Fin n))
    {α : Type*} [DecidableEq α] (κ : Fin n → α) (i₀ : Fin n) {δ ρ c ξ t : ℝ} (hδ : 0 < δ)
    (hc : 0 ≤ c)
    (hsub : ∀ i ∈ S, κ i = κ i₀ → i ∈ F')
    (hKT : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (((F'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal c * volume W)
    (hpop : t ≤ ((S.filter (fun i => κ i = κ i₀)).card : ℝ))
    (hcρ : c * ρ ^ 2 ≤ δ ^ (-ξ) * t * δ ^ 2) :
    ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (((S.filter (fun i => κ i = κ i₀ ∧ Tube δ (x i) (v i) ⊆ W)).card : ℝ) *
          ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ξ) * ((S.filter (fun i => κ i = κ i₀)).card : ℝ)) * volume W := by
  intro W hW
  have hle : (S.filter (fun i => κ i = κ i₀ ∧ Tube δ (x i) (v i) ⊆ W)).card ≤
      (F'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card :=
    Finset.card_le_card (fun i hi => by
      obtain ⟨hiS, hκ, hW'⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hsub i hiS hκ, hW'⟩)
  set A := ((S.filter (fun i => κ i = κ i₀ ∧ Tube δ (x i) (v i) ⊆ W)).card : ℝ) with hA
  set B := ((F'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) with hB
  set P := ((S.filter (fun i => κ i = κ i₀)).card : ℝ) with hP
  have hAB : A ≤ B := Nat.cast_le.mpr hle
  have hδ2 : 0 < δ ^ 2 := by positivity
  -- `A ρ² = (A δ²) (ρ²/δ²) ≤ (c |W|) (ρ²/δ²) ≤ δ^(-ξ) t |W| ≤ δ^(-ξ) P |W|`
  have hscale : ENNReal.ofReal (A * ρ ^ 2) =
      ENNReal.ofReal (A * δ ^ 2) * ENNReal.ofReal (ρ ^ 2 / δ ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hcoef : ENNReal.ofReal c * ENNReal.ofReal (ρ ^ 2 / δ ^ 2) ≤
      ENNReal.ofReal (δ ^ (-ξ) * P) := by
    rw [← ENNReal.ofReal_mul hc]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_div_assoc', div_le_iff₀ hδ2]
    calc c * ρ ^ 2 ≤ δ ^ (-ξ) * t * δ ^ 2 := hcρ
      _ ≤ δ ^ (-ξ) * P * δ ^ 2 := by gcongr
  calc ENNReal.ofReal (A * ρ ^ 2)
      = ENNReal.ofReal (A * δ ^ 2) * ENNReal.ofReal (ρ ^ 2 / δ ^ 2) := hscale
    _ ≤ ENNReal.ofReal (B * δ ^ 2) * ENNReal.ofReal (ρ ^ 2 / δ ^ 2) := by
        gcongr
    _ ≤ (ENNReal.ofReal c * volume W) * ENNReal.ofReal (ρ ^ 2 / δ ^ 2) := by
        gcongr
        exact hKT W hW
    _ = (ENNReal.ofReal c * ENNReal.ofReal (ρ ^ 2 / δ ^ 2)) * volume W := by ring
    _ ≤ ENNReal.ofReal (δ ^ (-ξ) * P) * volume W := by gcongr

/-- **Balance from thresholds.**  Populations between `t` and `P` with `P ≤ δ^(-ξ) t` are within
the ratio `δ^(-ξ)`. -/
lemma pop_ratio_of_bounds {δ ξ t P p p' : ℝ} (hp : p ≤ P) (hp' : t ≤ p')
    (hPt : P ≤ δ ^ (-ξ) * t) (hδ : 0 < δ) : p ≤ δ ^ (-ξ) * p' := by
  have h0 : 0 ≤ δ ^ (-ξ) := Real.rpow_nonneg hδ.le _
  calc p ≤ P := hp
    _ ≤ δ ^ (-ξ) * t := hPt
    _ ≤ δ ^ (-ξ) * p' := mul_le_mul_of_nonneg_left hp' h0

open Classical in
/-- **Global Frostman on a subset.**  If `S` is `K`-Frostman and `|S| ≤ M |S'|` for `S' ⊆ S`, then
`S'` is `K M`-Frostman. -/
theorem frostman_of_subset {n : ℕ} (x v : Fin n → Space) (S S' : Finset (Fin n)) (hS' : S' ⊆ S)
    {δ K M : ℝ} (hK : 0 ≤ K) (hcard : (S.card : ℝ) ≤ M * S'.card)
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal (K * S.card) * volume W) :
    ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((S'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal ((K * M) * S'.card) * volume W := by
  intro W hW
  have hle : (S'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card ≤
      (S.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hS')
  calc ENNReal.ofReal ((S'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ)
      ≤ ENNReal.ofReal ((S.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) := by
        apply ENNReal.ofReal_le_ofReal; exact_mod_cast hle
    _ ≤ ENNReal.ofReal (K * S.card) * volume W := hF W hW
    _ ≤ ENNReal.ofReal ((K * M) * S'.card) * volume W := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        calc K * S.card ≤ K * (M * S'.card) := mul_le_mul_of_nonneg_left hcard hK
          _ = (K * M) * S'.card := by ring

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
