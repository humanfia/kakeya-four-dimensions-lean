-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.Quantization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/TubeCoordinates/Quantization.lean (82de8bd).
-- Ported from workspace o157, branch x0572 (commit 9dec67f), TubeCoordinates/Quantization.lean;
-- SP references re-pointed to the accepted o223 (SP), o142 (covers) and o143 (cover counting) modules.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GridQuantization

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open WangZahlLot.Obl.wz_square_frostman_graph_projection

/-- Rounding a height down to a fixed real grid. -/
noncomputable def rounded (h z : ℝ) : ℝ := h * (SP.realGridIndex h z : ℝ)

lemma rounded_error {h : ℝ} (hh : 0 < h) (z : ℝ) :
    0 ≤ z - rounded h z ∧ z - rounded h z < h :=
  SP.realGridIndex_error hh z

lemma rounded_eq_close {h z w : ℝ} (hh : 0 < h) (heq : rounded h z = rounded h w) :
    |z - w| < h := by
  have hz := rounded_error hh z
  have hw := rounded_error hh w
  rw [heq] at hz
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Distinct grid heights are separated by the grid mesh. -/
lemma rounded_separated {h z w : ℝ} (hh : 0 < h) (hne : rounded h z ≠ rounded h w) :
    h ≤ dist (rounded h z) (rounded h w) := by
  have hi : SP.realGridIndex h z ≠ SP.realGridIndex h w := fun heq => hne (by simp [rounded, heq])
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · have he : (SP.realGridIndex h z : ℝ) + 1 ≤ (SP.realGridIndex h w : ℝ) := by
      exact_mod_cast Int.add_one_le_iff.mpr hlt
    rw [Real.dist_eq, abs_sub_comm]
    apply le_trans _ (le_abs_self _)
    dsimp [rounded]
    nlinarith
  · have he : (SP.realGridIndex h w : ℝ) + 1 ≤ (SP.realGridIndex h z : ℝ) := by
      exact_mod_cast Int.add_one_le_iff.mpr hlt
    rw [Real.dist_eq]
    apply le_trans _ (le_abs_self _)
    dsimp [rounded]
    nlinarith

/-- A line is encoded by its rounded heights at two columns. -/
noncomputable def code (h x₀ x₁ : ℝ) (l : ℝ × ℝ) : ℝ × ℝ :=
  (rounded h (height l x₀), rounded h (height l x₁))

/-- Two rounded heights retain a separated line family if the rounding is
finer than the line separation times the column gap. -/
lemma code_injOn {L : Set (ℝ × ℝ)} {h δ q B x₀ x₁ : ℝ}
    (hh : 0 < h) (hq : 0 < q) (hgap : q ≤ |x₁ - x₀|) (hx : |x₀| ≤ B)
    (hs : 2 * h / q ≤ δ) (hb : h + B * (2 * h / q) ≤ δ)
    (hsep : L.Pairwise (fun l l' => δ ≤ dist l l')) :
    Set.InjOn (code h x₀ x₁) L := by
  intro l hl l' hl' hcode
  by_contra hne
  have hc₀ := congrArg Prod.fst hcode
  have hc₁ := congrArg Prod.snd hcode
  have hclose := parameters_close_of_heights hq hgap hx
    (rounded_eq_close hh hc₀) (rounded_eq_close hh hc₁)
  have hdist : dist l l' < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨hclose.1.trans_le hs, hclose.2.trans_le hb⟩
  exact (not_lt_of_ge (hsep hl hl' hne)) hdist

/-- Every height between the anchors agrees with the scalar projection of the
rounded code up to one mesh width. The error is one-sided as well. -/
lemma code_interpolation_error {h t : ℝ} (hh : 0 < h) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (l : ℝ × ℝ) (x₀ x₁ : ℝ) :
    0 ≤ height l ((1 - t) * x₀ + t * x₁) -
      ((1 - t) * (code h x₀ x₁ l).1 + t * (code h x₀ x₁ l).2) ∧
    height l ((1 - t) * x₀ + t * x₁) -
      ((1 - t) * (code h x₀ x₁ l).1 + t * (code h x₀ x₁ l).2) < h := by
  have he₀ := rounded_error hh (height l x₀)
  have he₁ := rounded_error hh (height l x₁)
  rw [height_interpolate]
  dsimp [code]
  have hlo₀ := mul_nonneg (sub_nonneg.mpr ht.2) he₀.1
  have hlo₁ := mul_nonneg ht.1 he₁.1
  constructor
  · nlinarith
  · by_cases htz : t = 0
    · simpa [htz] using he₀.2
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htz)
      have hhi₀ := mul_le_mul_of_nonneg_left he₀.2.le (sub_nonneg.mpr ht.2)
      have hhi₁ := mul_lt_mul_of_pos_left he₁.2 htp
      nlinarith

/-- Rounded codes remain close to the actual heights throughout the anchor interval. -/
lemma code_interpolation_dist {h t : ℝ} (hh : 0 < h) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (l : ℝ × ℝ) (x₀ x₁ : ℝ) :
    dist ((1 - t) * (code h x₀ x₁ l).1 + t * (code h x₀ x₁ l).2)
      (height l ((1 - t) * x₀ + t * x₁)) < h := by
  have he := code_interpolation_error hh ht l x₀ x₁
  rw [dist_comm, Real.dist_eq, abs_of_nonneg he.1]
  exact he.2

/-- Encoding yields a graph in the product of the two grid-height sets,
with exactly as many edges as lines. -/
lemma code_graph {h δ q B x₀ x₁ : ℝ} (L : Finset (ℝ × ℝ))
    (hh : 0 < h) (hq : 0 < q) (hgap : q ≤ |x₁ - x₀|) (hx : |x₀| ≤ B)
    (hs : 2 * h / q ≤ δ) (hb : h + B * (2 * h / q) ≤ δ)
    (hsep : (L : Set (ℝ × ℝ)).Pairwise (fun l l' => δ ≤ dist l l')) :
    ∃ A B' : Finset ℝ, ∃ G : Finset (ℝ × ℝ),
      A = L.image (fun l => rounded h (height l x₀)) ∧
      B' = L.image (fun l => rounded h (height l x₁)) ∧
      G = L.image (code h x₀ x₁) ∧ G ⊆ A ×ˢ B' ∧ G.card = L.card ∧
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → h ≤ dist a b) ∧
      (∀ a ∈ B', ∀ b ∈ B', a ≠ b → h ≤ dist a b) := by
  classical
  refine ⟨L.image (fun l => rounded h (height l x₀)),
    L.image (fun l => rounded h (height l x₁)), L.image (code h x₀ x₁),
    rfl, rfl, rfl, ?_, Finset.card_image_of_injOn (code_injOn hh hq hgap hx hs hb hsep), ?_, ?_⟩
  · intro z hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨l, hl, rfl⟩, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
  · intro a ha b hb hab
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hb
    exact rounded_separated hh hab
  · intro a ha b hb hab
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hb
    exact rounded_separated hh hab

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
