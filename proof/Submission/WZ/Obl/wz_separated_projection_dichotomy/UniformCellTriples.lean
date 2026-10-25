-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.UniformCellTriples.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FiberLevels
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseTriples
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Localization

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

attribute [local instance] Classical.propDecidable

noncomputable def fiberLevelCells (S : Finset Plane) (f : Plane → Plane) (k : ℕ) : Finset Plane :=
  (S.image f).filter (fun y =>
    dyadicRadius k * (S.card : ℝ) / 2 < ((S.filter (fun x => f x = y)).card : ℝ) ∧
    ((S.filter (fun x => f x = y)).card : ℝ) ≤ dyadicRadius k * (S.card : ℝ))

/-- Uniformize cell masses in three coordinates while retaining a quantified
fraction of a dense hypergraph. The cutoff depends on the number of cells,
not on the cardinality of the original point families. -/
theorem exists_uniform_cell_triples
    {F G U : Finset Plane} {H : Finset Triple} (hHne : H.Nonempty)
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (f g h : Plane → Plane)
    (T₁ T₂ T₃ : Finset Plane)
    (hf : ∀ x ∈ F, f x ∈ T₁) (hg : ∀ x ∈ G, g x ∈ T₂) (hh : ∀ x ∈ U, h x ∈ T₃)
    {a B d : ℝ} {n : ℕ} (ha : 0 < a) (hB : 0 ≤ B) (hd : 0 < d)
    (hT₁ : (T₁.card : ℝ) ≤ B) (hT₂ : (T₂.card : ℝ) ≤ B) (hT₃ : (T₃.card : ℝ) ≤ B)
    (hsmall : 3 * a * B ≤ d / 2) (hlast : dyadicRadius (n + 1) < a)
    (hden : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ)) :
    ∃ (V₁ V₂ V₃ : Finset Plane) (M₁ M₂ M₃ : ℝ) (J : Finset Triple),
      V₁ ⊆ T₁ ∧ V₂ ⊆ T₂ ∧ V₃ ⊆ T₃ ∧ 0 < M₁ ∧ 0 < M₂ ∧ 0 < M₃ ∧
      (∀ y ∈ V₁, M₁ ≤ ((F.filter (fun x => f x = y)).card : ℝ) ∧
        ((F.filter (fun x => f x = y)).card : ℝ) ≤ 2 * M₁) ∧
      (∀ y ∈ V₂, M₂ ≤ ((G.filter (fun x => g x = y)).card : ℝ) ∧
        ((G.filter (fun x => g x = y)).card : ℝ) ≤ 2 * M₂) ∧
      (∀ y ∈ V₃, M₃ ≤ ((U.filter (fun x => h x = y)).card : ℝ) ∧
        ((U.filter (fun x => h x = y)).card : ℝ) ≤ 2 * M₃) ∧
      J ⊆ H ∧ (∀ p ∈ J, f p.1 ∈ V₁ ∧ g p.2.1 ∈ V₂ ∧ h p.2.2 ∈ V₃) ∧
      d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤
        2 * ((n + 1 : ℕ) : ℝ) ^ 3 * (J.card : ℝ) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hHne
  have hp₀' := Finset.mem_product.mp (hH hp₀)
  have hp₀'' := Finset.mem_product.mp hp₀'.2
  have hF : F.Nonempty := ⟨p₀.1, hp₀'.1⟩
  have hG : G.Nonempty := ⟨p₀.2.1, hp₀''.1⟩
  have hU : U.Nonempty := ⟨p₀.2.2, hp₀''.2⟩
  have hFc : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hF
  have hGc : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr hG
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hU
  let B₁ := F.filter (fun x => ((F.filter (fun z => f z = f x)).card : ℝ) < a * (F.card : ℝ))
  let B₂ := G.filter (fun x => ((G.filter (fun z => g z = g x)).card : ℝ) < a * (G.card : ℝ))
  let B₃ := U.filter (fun x => ((U.filter (fun z => h z = h x)).card : ℝ) < a * (U.card : ℝ))
  have hB₁ : (B₁.card : ℝ) ≤ a * (F.card : ℝ) * B :=
    (small_fiber_card_le F T₁ f hf ha.le).trans (by gcongr)
  have hB₂ : (B₂.card : ℝ) ≤ a * (G.card : ℝ) * B :=
    (small_fiber_card_le G T₂ g hg ha.le).trans (by gcongr)
  have hB₃ : (B₃.card : ℝ) ≤ a * (U.card : ℝ) * B :=
    (small_fiber_card_le U T₃ h hh ha.le).trans (by gcongr)
  let H₀ := H.filter (fun p => p.1 ∉ B₁ ∧ p.2.1 ∉ B₂ ∧ p.2.2 ∉ B₃)
  have hdelete : (H.card : ℝ) ≤ (H₀.card : ℝ) +
      (B₁.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) +
      (F.card : ℝ) * (B₂.card : ℝ) * (U.card : ℝ) +
      (F.card : ℝ) * (G.card : ℝ) * (B₃.card : ℝ) := by
    exact_mod_cast triple_delete_card hH B₁ B₂ B₃
  have hterm₁ : (B₁.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤
      a * B * ((F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ)) := by
    calc _ ≤ (a * (F.card : ℝ) * B) * (G.card : ℝ) * (U.card : ℝ) := by gcongr
      _ = _ := by ring
  have hterm₂ : (F.card : ℝ) * (B₂.card : ℝ) * (U.card : ℝ) ≤
      a * B * ((F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ)) := by
    calc _ ≤ (F.card : ℝ) * (a * (G.card : ℝ) * B) * (U.card : ℝ) := by gcongr
      _ = _ := by ring
  have hterm₃ : (F.card : ℝ) * (G.card : ℝ) * (B₃.card : ℝ) ≤
      a * B * ((F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ)) := by
    calc _ ≤ (F.card : ℝ) * (G.card : ℝ) * (a * (U.card : ℝ) * B) := by gcongr
      _ = _ := by ring
  have hhalf : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ 2 * (H₀.card : ℝ) := by
    have hs := mul_le_mul_of_nonneg_right hsmall
      (by positivity : 0 ≤ (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ))
    nlinarith
  let I := Fin (n + 1) × Fin (n + 1) × Fin (n + 1)
  let P (i : I) : Set Triple := {p | f p.1 ∈ fiberLevelCells F f i.1 ∧
    g p.2.1 ∈ fiberLevelCells G g i.2.1 ∧ h p.2.2 ∈ fiberLevelCells U h i.2.2}
  have hcover : ∀ p ∈ H₀, ∃ i : I, p ∈ P i := by
    intro p hp
    have hpH := (Finset.mem_filter.mp hp).1
    have hpB := (Finset.mem_filter.mp hp).2
    have hpF := Finset.mem_product.mp (hH hpH)
    have hpG := Finset.mem_product.mp hpF.2
    have hl₁ : a * (F.card : ℝ) ≤ ((F.filter (fun z => f z = f p.1)).card : ℝ) := by
      by_contra hn
      exact hpB.1 (Finset.mem_filter.mpr ⟨hpF.1, lt_of_not_ge hn⟩)
    have hl₂ : a * (G.card : ℝ) ≤ ((G.filter (fun z => g z = g p.2.1)).card : ℝ) := by
      by_contra hn
      exact hpB.2.1 (Finset.mem_filter.mpr ⟨hpG.1, lt_of_not_ge hn⟩)
    have hl₃ : a * (U.card : ℝ) ≤ ((U.filter (fun z => h z = h p.2.2)).card : ℝ) := by
      by_contra hn
      exact hpB.2.2 (Finset.mem_filter.mpr ⟨hpG.2, lt_of_not_ge hn⟩)
    obtain ⟨i, hi, hiL, hiU⟩ := fiber_mass_level F f hF ha hlast hl₁
    obtain ⟨j, hj, hjL, hjU⟩ := fiber_mass_level G g hG ha hlast hl₂
    obtain ⟨k, hk, hkL, hkU⟩ := fiber_mass_level U h hU ha hlast hl₃
    refine ⟨(⟨i, Finset.mem_range.mp hi⟩, ⟨j, Finset.mem_range.mp hj⟩,
      ⟨k, Finset.mem_range.mp hk⟩), ?_⟩
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f hpF.1, hiL, hiU⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem g hpG.1, hjL, hjU⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem h hpG.2, hkL, hkU⟩⟩
  obtain ⟨i, hlarge⟩ := exists_large_cover_piece H₀ P hcover
  let J := H₀.filter (fun p => p ∈ P i)
  have hJi : ∀ p ∈ J, p ∈ P i := fun p hp => (Finset.mem_filter.mp hp).2
  have hJH : J ⊆ H := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hJcard : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤
      2 * ((n + 1 : ℕ) : ℝ) ^ 3 * (J.card : ℝ) := by
    have hlarge' : (H₀.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * (J.card : ℝ) := by
      convert hlarge using 1
      simp only [I, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      ring_nf
      congr 2
      apply congrArg Finset.card
      ext p
      simp only [J, Finset.mem_filter]
    nlinarith
  refine ⟨fiberLevelCells F f i.1, fiberLevelCells G g i.2.1, fiberLevelCells U h i.2.2,
    dyadicRadius i.1 * (F.card : ℝ) / 2,
    dyadicRadius i.2.1 * (G.card : ℝ) / 2,
    dyadicRadius i.2.2 * (U.card : ℝ) / 2, J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hJH, hJi, hJcard⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
    exact hf x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
    exact hg x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
    exact hh x hx
  · exact div_pos (mul_pos (dyadicRadius_pos _) hFc) (by norm_num)
  · exact div_pos (mul_pos (dyadicRadius_pos _) hGc) (by norm_num)
  · exact div_pos (mul_pos (dyadicRadius_pos _) hUc) (by norm_num)
  · intro y hy
    have hyy := (Finset.mem_filter.mp hy).2
    exact ⟨hyy.1.le, by linarith [hyy.2]⟩
  · intro y hy
    have hyy := (Finset.mem_filter.mp hy).2
    exact ⟨hyy.1.le, by linarith [hyy.2]⟩
  · intro y hy
    have hyy := (Finset.mem_filter.mp hy).2
    exact ⟨hyy.1.le, by linarith [hyy.2]⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
