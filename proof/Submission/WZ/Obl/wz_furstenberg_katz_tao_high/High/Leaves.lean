-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.Leaves.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/Leaves.lean (95ffa93).
-- Composed-tube balance fields updated from that workspace branch, commit 521e40b.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Profiles
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FromHalf

/-!
# The leaves of the high range

The high range `1/2 < s < 1` is reduced (`High/TopLevel.lean`, `high_range_of_leaves`) to four
statements about one regularized failed configuration on the palette of scales
`palScale r n i = r ^ (i / n)`, `i ≤ n`:

* `ConfigLeaf`: a failed configuration (`FailData`) contains a `HighConfig`: a regularized
  subfamily `S`, the classes (fine lines `J₀`), tubes at every palette scale, the
  `(1 - s)`-Frostman bound of the pins along each line, and the balance of every map used
  at the palette scales;
* `PremiseLeaf`: the energy premise at every resolution `a` and cell scale `h ≤ a`, for the
  point profile `G = ptProfile` and the bush profile `F = bushProfile` of any pin;
* `UniformityLeaf`: the profile analysis (x0651's `small_frontloading_of_all_scale_energy`
  with additive slack): the premise forces near-uniform bushes, `F t ≤ s t + d n`;
* `CaseALeaf`: case A at a right-min window of `G - s·id` with near-uniform bushes is
  impossible.

All constants are chosen before `n` and before `r`, as the top level needs them.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high
open WangZahlLot.Obl.wz_tower_balanced_refinement

noncomputable section

/-- The palette base `r ^ (-1/n)`: `palScale r n i = palBase r n ^ (-i) = r ^ (i / n)`. -/
def palBase (r : ℝ) (n : ℕ) : ℝ := r ^ (-(1 / (n : ℝ)))

/-- The palette scale `i ≤ n`: `r ^ (i / n)`; scale `0` is `1` and scale `n` is `r`. -/
def palScale (r : ℝ) (n i : ℕ) : ℝ := palBase r n ^ (-(i : ℝ))

/-- The point profile `G i = log_B #(occupied palScale i - cells of the pins of S)`. -/
def ptProfile (r : ℝ) (n : ℕ) (S : Finset (E2 × E2)) (i : ℕ) : ℝ :=
  cellProfile (S.image Prod.fst) (palBase r n) i

/-- The bush profile of the pin `p₀`: `F i = log_B #(occupied palScale i - arcs of its
bush)` (`arcOf` and `cellOf` are the same square cells). -/
def bushProfile (r : ℝ) (n : ℕ) (S : Finset (E2 × E2)) (p₀ : E2) (i : ℕ) : ℝ :=
  cellProfile (bushOf S p₀) (palBase r n) i

/-- One regularized failed configuration: `S ⊆ D` with `|S| ≥ r ^ ε |D|`, both failed
(`FailData` with `η = ε`); the lines `J₀ ⊆ D` (a maximal `StripSep r` family, so
`|J₀| < r ^ (-2 s - ε₀)`) with the class map `cls` (9r/r geometry); the pins of every line
are `(1 - s)`-Frostman along it (constant `r ^ (-κ)`); tubes `J₁ j ⊆ J₀` at every palette
scale `j ≤ n` with the map `tb j` (9ρ/ρ geometry, `StripSep ρ`); and every map used at the
palette scales is balanced with ratio `r ^ (-ε)`. -/
structure HighConfig (r s ε₀ ε κ : ℝ) (n : ℕ) (P : Finset E2) (D S J₀ : Finset (E2 × E2))
    (cls : E2 × E2 → E2 × E2) (J₁ : ℕ → Finset (E2 × E2))
    (tb : ℕ → E2 × E2 → E2 × E2) : Prop where
  fail : FailData r s ε₀ ε P D
  sub : S ⊆ D
  mass : r ^ ε * (D.card : ℝ) ≤ S.card
  failS : FailData r s ε₀ ε (S.image Prod.fst) S
  lines_sub : J₀ ⊆ D
  lines_sep : ∀ x ∈ J₀, ∀ y ∈ J₀, x ≠ y → StripSep r x y
  cls_mem : ∀ q ∈ D, cls q ∈ J₀
  cls_geo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
    (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)
  line_frostman : ∀ q ∈ S, ∀ c : ℝ, r ≤ c →
    (((S.filter (fun q' => cls q' = cls q)).filter (fun q' => dist q'.1 q.1 < c)).card : ℝ) ≤
      r ^ (-κ) * c ^ (1 - s) * (S.filter (fun q' => cls q' = cls q)).card
  tubes_sub : ∀ j, J₁ j ⊆ J₀
  tubes_sep : ∀ j ≤ n, ∀ x ∈ J₁ j, ∀ y ∈ J₁ j, x ≠ y → StripSep (palScale r n j) x y
  tube_mem : ∀ j ≤ n, ∀ ℓ ∈ J₀, tb j ℓ ∈ J₁ j
  tube_geo : ∀ j ≤ n, ∀ ℓ ∈ J₀,
    |inner ℝ (ℓ.1 - (tb j ℓ).1) (tb j ℓ).2| < 9 * palScale r n j ∧
      (dist ℓ.2 (tb j ℓ).2 < palScale r n j ∨ dist ℓ.2 (-(tb j ℓ).2) < palScale r n j)
  bal_pin : Balanced S Prod.fst (r ^ (-ε))
  bal_cls : Balanced S cls (r ^ (-ε))
  bal_cell : ∀ i ≤ n, Balanced S (fun q => cellOf (palScale r n i) q.1) (r ^ (-ε))
  bal_arc : ∀ j ≤ n, Balanced S (fun q => arcOf (palScale r n j) q.2) (r ^ (-ε))
  bal_tube : ∀ j ≤ n, Balanced S (fun q => tb j (cls q)) (r ^ (-ε))
  bal_pin_arc : ∀ j ≤ n, Balanced S (fun q => (q.1, arcOf (palScale r n j) q.2)) (r ^ (-ε))
  bal_pin_tube : ∀ j ≤ n, Balanced S (fun q => (q.1, tb j (cls q))) (r ^ (-ε))
  bal_cell_cls : ∀ i ≤ n,
    Balanced S (fun q => (cellOf (palScale r n i) q.1, cls q)) (r ^ (-ε))
  bal_cell_arc : ∀ i ≤ n, ∀ j ≤ n,
    Balanced S (fun q => (cellOf (palScale r n i) q.1, arcOf (palScale r n j) q.2)) (r ^ (-ε))
  bal_cell_tube : ∀ i ≤ n, ∀ j ≤ n,
    Balanced S (fun q => (cellOf (palScale r n i) q.1, tb j (cls q))) (r ^ (-ε))
  bal_tube2 : ∀ h ≤ n, ∀ a ≤ n,
    Balanced S (fun q => tb h (tb a (cls q))) (r ^ (-ε))
  bal_pin_tube2 : ∀ h ≤ n, ∀ a ≤ n,
    Balanced S (fun q => (q.1, tb h (tb a (cls q)))) (r ^ (-ε))
  bal_cell_tube2 : ∀ i ≤ n, ∀ h ≤ n, ∀ a ≤ n,
    Balanced S (fun q => (cellOf (palScale r n i) q.1, tb h (tb a (cls q)))) (r ^ (-ε))

/-- Leaf (C): every failed configuration contains a `HighConfig`. Given the line-Frostman
exponent `κ`, the leaf chooses the regularization exponent `ε ≤ κ` and the admissible
`η, ε₀ ≤ η₀`, then (for each palette size `n`) the admissible scales `r ≤ r₁`. -/
def ConfigLeaf (s : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ ε : ℝ, 0 < ε ∧ ε ≤ κ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ n : ℕ, 0 < n →
    ∃ r₁ : ℝ, 0 < r₁ ∧
      ∀ (r ε₀ η : ℝ) (P : Finset E2) (D : Finset (E2 × E2)), 0 < r → r ≤ r₁ →
        0 < ε₀ → ε₀ ≤ η₀ → 0 < η → η ≤ η₀ → FailData r s ε₀ η P D →
        ∃ (S J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (J₁ : ℕ → Finset (E2 × E2))
          (tb : ℕ → E2 × E2 → E2 × E2), HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb

/-- Leaf (E), the energy premise: at every resolution `a ≤ n` and cell scale `0 < h ≤ a`
some `y ∈ [h, a]` has `G y + F (a - y) ≤ F a + G h - F h + e n`. -/
def PremiseLeaf (s : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ ε' : ℝ, 0 < ε' ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ r₁ : ℝ, 0 < r₁ ∧
    ∀ (r ε₀ ε κ : ℝ) (P : Finset E2) (D S J₀ : Finset (E2 × E2))
      (cls : E2 × E2 → E2 × E2) (J₁ : ℕ → Finset (E2 × E2)) (tb : ℕ → E2 × E2 → E2 × E2),
      0 < r → r ≤ r₁ → 0 < ε₀ → ε₀ ≤ ε' → 0 < ε → ε ≤ ε' → 0 < κ → κ ≤ ε' →
      HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb →
      ∀ p₀ ∈ S.image Prod.fst, ∀ h a : ℕ, 0 < h → h ≤ a → a ≤ n →
        ∃ y : ℕ, h ≤ y ∧ y ≤ a ∧
          ptProfile r n S y + bushProfile r n S p₀ (a - y) ≤
            bushProfile r n S p₀ a + ptProfile r n S h - bushProfile r n S p₀ h + e * n

/-- Leaf (U), the profile analysis: approximate monotonicity, slope `≤ 1`, endpoint `s n`,
the lower bounds and the premise, all with additive slack `e n`, force
`F t ≤ s t + d n`. (x0651's `small_frontloading_of_all_scale_energy` is the exact form.) -/
def UniformityLeaf (s : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → ∃ e : ℝ, 0 < e ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ F G : ℕ → ℝ,
    |F n - s * n| ≤ e * n →
    (∀ i j : ℕ, i ≤ j → j ≤ n → F i ≤ F j + e * n) →
    (∀ i j : ℕ, i ≤ j → j ≤ n → F j - F i ≤ ((j : ℝ) - i) + e * n) →
    (∀ t : ℕ, t ≤ n → s * t - e * n ≤ F t) →
    (∀ t : ℕ, t ≤ n → (t : ℝ) - e * n ≤ G t ∧ G t ≤ 2 * t + e * n) →
    (∀ h a : ℕ, 0 < h → h ≤ a → a ≤ n → ∃ y : ℕ, h ≤ y ∧ y ≤ a ∧
      G y + F (a - y) ≤ F a + G h - F h + e * n) →
    ∀ t : ℕ, t ≤ n → F t ≤ s * t + d * n

/-- Leaf (A), case A: a window `[h, a]` with `a / 2 ≤ h ≤ (1 - c) a`, `n ≤ L a`, on which
`h` is a right-min of `G - s·id`, with near-uniform bushes `|F t - s t| ≤ d n`, is
impossible. The leaf chooses `d` and the admissible exponents `ε'` from the window
fraction `c` and the ratio `L`. -/
def CaseALeaf (s : ℝ) : Prop :=
  ∀ c L : ℝ, 0 < c → 1 ≤ L → ∃ d ε' : ℝ, 0 < d ∧ 0 < ε' ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ r₁ : ℝ, 0 < r₁ ∧
    ∀ (r ε₀ ε κ : ℝ) (P : Finset E2) (D S J₀ : Finset (E2 × E2))
      (cls : E2 × E2 → E2 × E2) (J₁ : ℕ → Finset (E2 × E2)) (tb : ℕ → E2 × E2 → E2 × E2),
      0 < r → r ≤ r₁ → 0 < ε₀ → ε₀ ≤ ε' → 0 < ε → ε ≤ ε' → 0 < κ → κ ≤ ε' →
      HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb →
      ∀ p₀ ∈ S.image Prod.fst, ∀ h a : ℕ, a ≤ n → (n : ℝ) ≤ L * a → (a : ℝ) ≤ 2 * h →
        (h : ℝ) + c * a ≤ a →
        (∀ i : ℕ, h ≤ i → i ≤ a → ptProfile r n S h - s * h ≤ ptProfile r n S i - s * i) →
        (∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ d * n) →
        False

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
