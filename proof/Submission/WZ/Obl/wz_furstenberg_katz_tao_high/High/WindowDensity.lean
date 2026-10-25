-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.EnergyGeometry
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.AbstractCaseA
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.TubeLineFrostman

/-!
# A dense window tube

In a `HighConfig` at the window `(a, h)`: the lines are the `a`-tubes `tb a (cls q)` of the labels,
their pins the points of the labels (`pinsOf S (tb a ∘ cls)`, within `26 palScale a` of the line),
the tubes the `h`-tubes `tb h`, with axis `-perp t.2` (x0672's `tubeAxis`), and the pins of a tube
the points of its labels. `HighConfig.window_dense_tube` is `exists_dense_column_tubeA` for these
objects: from an incidence count `I`, a close-pair energy `E` (pairs within `6 w + 4 ι`,
`ι = 26 palScale a`) and a column budget `X`, some tube has (column, line) density at least
`I² / (E X)`, with columns `tubeCol (-perp t.2) w`. (x0720's `window_pair_energy` bounds `E` over
pairs within `10 palScale h`, which contains these pairs when `6 w + 104 palScale a ≤ 10 palScale h`;
x0720's `window_column_size` bounds `X`.)
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open scoped BigOperators

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)} {tb : ℕ → E2 × E2 → E2 × E2}

/-- Lines of `J₀` have unit normals and base points of norm at most `4`. -/
theorem HighConfig.line_norms (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {j : E2 × E2}
    (hj : j ∈ J₀) : ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 := by
  have hjD := H.lines_sub hj
  exact ⟨(H.fail.D_mem j hjD).2, H.fail.P_norm j.1 (H.fail.D_mem j hjD).1⟩

/-- The window lines are lines of `J₀`. -/
theorem HighConfig.window_line_mem (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a : ℕ}
    (ha : a ≤ n) {j : E2 × E2} (hj : j ∈ S.image (fun q => tb a (cls q))) : j ∈ J₀ := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
  exact H.coarse_class_mem ha hq

/-- Pins of a window line lie within `26 palScale a` of it. -/
theorem HighConfig.window_pin_width (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {a : ℕ} (ha : a ≤ n) {j : E2 × E2} {x : E2}
    (hx : x ∈ pinsOf S (fun q => tb a (cls q)) j) :
    |inner ℝ (x - j.1) j.2| ≤ 26 * palScale r n a := by
  obtain ⟨e, hxe, hj⟩ := mem_pinsOf.mp hx
  have := H.coarse_class_incidence hr1 hn ha hxe
  rw [hj] at this
  exact this.le

/-- Window lines are transverse to the axis `-perp t.2` of their `h`-tube. -/
theorem HighConfig.window_transverse (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {h : ℕ} (hh : h ≤ n) (hρ : palScale r n h ≤ 1 / 2) {j : E2 × E2} (hj : j ∈ J₀) :
    1 / 2 ≤ |inner ℝ j.2 (perp (-perp (tb h j).2))| := by
  have hgeo := H.tube_geo h hh j hj
  have htm := H.tubes_sub h (H.tube_mem h hh j hj)
  have ht2 : ‖(tb h j).2‖ = 1 := (H.line_norms htm).1
  have hj2 : ‖j.2‖ = 1 := (H.line_norms hj).1
  have hperp : perp (-perp (tb h j).2) = -(perp (perp (tb h j).2)) := by
    ext i; fin_cases i <;> simp [perp]
  have h1 := transverse_of_near (θ := palScale r n h) hρ ht2 hj2 hgeo.2
  rw [hperp, inner_neg_right, abs_neg]
  exact h1

/-- **A dense window tube** (`exists_dense_column_tubeA` for the window objects). -/
theorem HighConfig.window_dense_tube (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {h a : ℕ} (hhn : h ≤ n) (han : a ≤ n)
    (hρ : palScale r n h ≤ 1 / 2) {w I E X : ℝ} (hw : 0 < w) (hI : 0 < I) (hE : 0 < E)
    (hX : 0 < X)
    (hIsum : I ≤ ∑ j ∈ S.image (fun q => tb a (cls q)),
      ((pinsOf S (fun q => tb a (cls q)) j).card : ℝ))
    (hEsum : ∑ p ∈ S.image Prod.fst, ∑ p' ∈ (S.image Prod.fst).filter
        (fun p' => dist p p' ≤ 6 * w + 4 * (26 * palScale r n a)),
      (((S.image (fun q => tb a (cls q))).filter (fun j =>
        p ∈ pinsOf S (fun q => tb a (cls q)) j ∧
        p' ∈ pinsOf S (fun q => tb a (cls q)) j)).card : ℝ) ≤ E)
    (hXsum : ∑ t ∈ (S.image (fun q => tb a (cls q))).image (tb h),
      ((((S.filter (fun q => tb h (tb a (cls q)) = t)).image Prod.fst).image
        (tubeCol (-perp t.2) w)).card : ℝ) *
        (((S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t)).card : ℝ) ≤ X) :
    ∃ t ∈ (S.image (fun q => tb a (cls q))).image (tb h),
      ((S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t)).Nonempty ∧
      ((S.filter (fun q => tb h (tb a (cls q)) = t)).image Prod.fst).Nonempty ∧
      I ^ 2 / (E * X) *
          ((((S.filter (fun q => tb h (tb a (cls q)) = t)).image Prod.fst).image
            (tubeCol (-perp t.2) w)).card : ℝ) *
          (((S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t)).card : ℝ) ≤
        (((((S.filter (fun q => tb h (tb a (cls q)) = t)).image Prod.fst).image
            (tubeCol (-perp t.2) w)) ×ˢ
            ((S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t))).filter
          (fun p : ℝ × (E2 × E2) => ∃ x ∈ (S.filter (fun q => tb h (tb a (cls q)) = t)).image
            Prod.fst, x ∈ pinsOf S (fun q => tb a (cls q)) p.2 ∧
              tubeCol (-perp t.2) w x = p.1)).card := by
  classical
  set JA := S.image (fun q => tb a (cls q)) with hJA
  set pinsF := pinsOf S (fun q => tb a (cls q)) with hpinsF
  set Ut : E2 × E2 → Finset E2 := fun t => (S.filter (fun q => tb h (tb a (cls q)) = t)).image
    Prod.fst with hUt
  have hJAJ₀ : ∀ j ∈ JA, j ∈ J₀ := fun j hj => H.window_line_mem han hj
  -- the pins of a line of the tube `t` are pins of `t`
  have hpinsUt : ∀ j ∈ JA, pinsF j ⊆ Ut (tb h j) := by
    intro j _ x hx
    obtain ⟨e, hxe, hjx⟩ := mem_pinsOf.mp hx
    refine Finset.mem_image.mpr ⟨(x, e), Finset.mem_filter.mpr ⟨hxe, ?_⟩, rfl⟩
    simp only [hjx]
  have hIsum' : I ≤ ∑ t ∈ JA.image (tb h), ∑ j ∈ JA.filter (fun j => tb h j = t),
      ((pinsF j ∩ Ut t).card : ℝ) := by
    refine hIsum.trans (le_of_eq ?_)
    rw [Columns.sum_classes_eq_sum_tubes JA (tb h)]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hjJA, hjt⟩ := Finset.mem_filter.mp hj
    rw [Finset.inter_eq_left.mpr (hjt ▸ hpinsUt j hjJA)]
  have hUtU : ∀ t ∈ JA.image (tb h), Ut t ⊆ S.image Prod.fst := by
    intro t _ x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hq).1
  obtain ⟨t, ht, hJne, hUne, hdens⟩ := exists_dense_column_tubeA (ι := 26 * palScale r n a)
    hw hI hE hX pinsF JA (fun j hj => (H.line_norms (hJAJ₀ j hj)).1)
    (fun j _ x hx => H.window_pin_width hr1 hn han hx) (S.image Prod.fst)
    (fun p p' => (((JA.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j))).card : ℝ))
    (fun _ _ _ _ => le_rfl) (JA.image (tb h)) (tb h) (fun t => -perp t.2) Ut
    (fun t _ => by rw [norm_neg, perp_norm]; exact (H.line_norms (H.tubes_sub h
      (by obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ‹t ∈ JA.image (tb h)›
          exact H.tube_mem h hhn j (hJAJ₀ j hj)))).1)
    (fun t _ j hj => by
      have hjt := (Finset.mem_filter.mp hj).2
      have := H.window_transverse hhn hρ (hJAJ₀ j (Finset.mem_filter.mp hj).1)
      rw [hjt] at this
      exact this)
    hUtU hIsum' hEsum hXsum
  exact ⟨t, ht, hJne, hUne, hdens⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/High/WindowDensity.lean
