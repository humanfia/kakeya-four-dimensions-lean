-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CoarseTripleModel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.UniformCellTriples
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseCellCounts
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FiniteCells

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Separated representatives of a counting configuration, preserving its
regularity and hypergraph density and recording the approximation error. -/
structure CoarseTripleData (δ C D ζ d : ℝ) (F G U : Finset Plane) (H : Finset Triple) where
  first : Finset Plane
  second : Finset Plane
  third : Finset Plane
  edges : Finset Triple
  first_subset : first ⊆ F
  second_subset : second ⊆ G
  third_subset : third ⊆ U
  first_separated : ∀ x ∈ first, ∀ y ∈ first, x ≠ y → δ < dist x y
  second_separated : ∀ x ∈ second, ∀ y ∈ second, x ≠ y → δ < dist x y
  third_separated : ∀ x ∈ third, ∀ y ∈ third, x ≠ y → δ < dist x y
  first_frostman : ClosedFiniteFrostman δ C first
  second_frostman : ClosedFiniteFrostman δ C second
  third_frostman : ClosedFiniteFrostman δ C third
  second_line : IndexedLineFrostman δ D ζ (fun x : second => (x : Plane))
  third_line : IndexedLineFrostman δ D ζ (fun x : third => (x : Plane))
  contained : edges ⊆ first ×ˢ (second ×ˢ third)
  nonempty : edges.Nonempty
  density : d * (first.card : ℝ) * (second.card : ℝ) * (third.card : ℝ) ≤ (edges.card : ℝ)
  approximates : ∀ q ∈ edges, ∃ p ∈ H, dist p q ≤ δ

/-- Uniformize cell masses and choose separated internal representatives in
all three coordinates. Only a dyadic-depth budget remains numerical. -/
theorem exists_coarse_triple_data {δ R C D ζ d a B : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hζ : 0 ≤ ζ) (hd : 0 < d) (ha : 0 < a)
    (hB : (2 * R + 1) ^ 2 / δ ^ 2 ≤ B)
    (hsmall : 3 * a * B ≤ d / 2) (hlast : dyadicRadius (n + 1) < a)
    (hbudget : (4 * ((n + 1 : ℕ) : ℝ) ^ 3 / d) * (2 * C) ^ ζ ≤ D ^ ζ)
    (F G U : Finset Plane) (H : Finset Triple)
    (hFn : ∀ x ∈ F, ‖x‖ ≤ R) (hGn : ∀ x ∈ G, ‖x‖ ≤ R) (hUn : ∀ x ∈ U, ‖x‖ ≤ R)
    (hF : ClosedFiniteFrostman δ C F) (hG : ClosedFiniteFrostman δ C G)
    (hU : ClosedFiniteFrostman δ C U)
    (hGl : IndexedLineFrostman δ C ζ (fun x : G => (x : Plane)))
    (hUl : IndexedLineFrostman δ C ζ (fun x : U => (x : Plane)))
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (hHne : H.Nonempty)
    (hden : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ)) :
    Nonempty (CoarseTripleData δ (2 * C * (4 * ((n + 1 : ℕ) : ℝ) ^ 3 / d)) D ζ
      (d / (16 * ((n + 1 : ℕ) : ℝ) ^ 3)) F G U H) := by
  classical
  obtain ⟨T₁, f, hT₁F, hsep₁, hf, hT₁⟩ := exists_bounded_finite_cells F hδ hδ1 hR hFn
  obtain ⟨T₂, g, hT₂G, hsep₂, hg, hT₂⟩ := exists_bounded_finite_cells G hδ hδ1 hR hGn
  obtain ⟨T₃, h, hT₃U, hsep₃, hh, hT₃⟩ := exists_bounded_finite_cells U hδ hδ1 hR hUn
  have hBn : 0 ≤ B := (by positivity : 0 ≤ (2 * R + 1) ^ 2 / δ ^ 2).trans hB
  obtain ⟨V₁, V₂, V₃, M₁, M₂, M₃, J, hV₁, hV₂, hV₃, hM₁, hM₂, hM₃,
      hb₁, hb₂, hb₃, hJH, hJV, hJden⟩ :=
    exists_uniform_cell_triples hHne hH f g h T₁ T₂ T₃
      (fun x hx => (hf x hx).1) (fun x hx => (hg x hx).1) (fun x hx => (hh x hx).1)
      ha hBn hd (hT₁.trans hB) (hT₂.trans hB) (hT₃.trans hB) hsmall hlast hden
  let K := 2 * ((n + 1 : ℕ) : ℝ) ^ 3
  let L := 4 * ((n + 1 : ℕ) : ℝ) ^ 3 / d
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨p₀, hp₀⟩ := hHne
  have hp₀' := Finset.mem_product.mp (hH hp₀)
  have hp₀'' := Finset.mem_product.mp hp₀'.2
  have hFc : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr ⟨p₀.1, hp₀'.1⟩
  have hGc : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr ⟨p₀.2.1, hp₀''.1⟩
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr ⟨p₀.2.2, hp₀''.2⟩
  have hJpos : (0 : ℝ) < J.card := by
    have hprod : 0 < d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) := by positivity
    have hkJ : 0 < K * (J.card : ℝ) := hprod.trans_le hJden
    exact (mul_pos_iff.mp hkJ).resolve_right (fun hn => (not_lt_of_ge hK.le) hn.1) |>.2
  have hJne : J.Nonempty := Finset.card_pos.mp (by exact_mod_cast hJpos)
  have hJsub : J ⊆ F ×ˢ (G ×ˢ U) := hJH.trans hH
  obtain ⟨hc₁, hc₂, hc₃, hcd⟩ := coarse_cell_counts hJne hJsub f g h
    hM₁ hM₂ hM₃ hd hK.le hb₁ hb₂ hb₃ hJV hJden
  have hLK : 2 * K / d = L := by dsimp [K, L]; ring
  rw [hLK] at hc₁ hc₂ hc₃
  let E := J.image (coarseTriple f g h)
  refine ⟨{
    first := V₁
    second := V₂
    third := V₃
    edges := E
    first_subset := hV₁.trans hT₁F
    second_subset := hV₂.trans hT₂G
    third_subset := hV₃.trans hT₃U
    first_separated := fun x hx y hy hxy => hsep₁ x (hV₁ hx) y (hV₁ hy) hxy
    second_separated := fun x hx y hy hxy => hsep₂ x (hV₂ hx) y (hV₂ hy) hxy
    third_separated := fun x hx y hy hxy => hsep₃ x (hV₃ hx) y (hV₃ hy) hxy
    first_frostman := hF.coarse_cells hδ hC hM₁ hL.le f (fun x hx => (hf x hx).2)
      (fun y hy => (hb₁ y hy).1) hc₁
    second_frostman := hG.coarse_cells hδ hC hM₂ hL.le g (fun x hx => (hg x hx).2)
      (fun y hy => (hb₂ y hy).1) hc₂
    third_frostman := hU.coarse_cells hδ hC hM₃ hL.le h (fun x hx => (hh x hx).2)
      (fun y hy => (hb₃ y hy).1) hc₃
    second_line := hGl.coarse_cells hδ hC hD hM₂ hζ g (fun x hx => (hg x hx).2)
      (fun y hy => (hb₂ y hy).1) hc₂ hbudget
    third_line := hUl.coarse_cells hδ hC hD hM₃ hζ h (fun x hx => (hh x hx).2)
      (fun y hy => (hb₃ y hy).1) hc₃ hbudget
    contained := ?_
    nonempty := hJne.image _
    density := ?_
    approximates := ?_ }⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨(hJV p hp).1, Finset.mem_product.mpr (hJV p hp).2⟩
  · have hP : 0 < 16 * ((n + 1 : ℕ) : ℝ) ^ 3 := by positivity
    rw [show d / (16 * ((n + 1 : ℕ) : ℝ) ^ 3) * (V₁.card : ℝ) * (V₂.card : ℝ) * (V₃.card : ℝ) =
      (d * (V₁.card : ℝ) * (V₂.card : ℝ) * (V₃.card : ℝ)) / (16 * ((n + 1 : ℕ) : ℝ) ^ 3) by ring]
    apply (div_le_iff₀ hP).mpr
    convert hcd using 1 <;> dsimp [E, K] <;> ring
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hpF := Finset.mem_product.mp (hJsub hp)
    have hpG := Finset.mem_product.mp hpF.2
    refine ⟨p, hJH hp, ?_⟩
    simp only [coarseTriple, Prod.dist_eq, max_le_iff]
    exact ⟨(hf p.1 hpF.1).2, (hg p.2.1 hpG.1).2, (hh p.2.2 hpG.2).2⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
