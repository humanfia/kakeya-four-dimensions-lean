-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CoarseCellCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseTriples

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

private theorem cancel_product_mass {A B C N K d M : ℝ}
    (hB : 0 < B) (hC : 0 < C) (hd : 0 < d) (hK : 0 ≤ K)
    (hden : d * A * B * C ≤ K * N) (hcount : N ≤ M * B * C) :
    A ≤ K * M / d := by
  have hh : (d * A) * (B * C) ≤ (K * M) * (B * C) := by
    calc _ ≤ K * N := by simpa only [mul_assoc] using hden
      _ ≤ K * (M * B * C) := mul_le_mul_of_nonneg_left hcount hK
      _ = _ := by ring
  have hc := (mul_le_mul_iff_left₀ (mul_pos hB hC)).mp (by
    simpa only [mul_comm (B * C)] using hh)
  apply (le_div_iff₀ hd).mpr
  nlinarith

private theorem selected_fiber_upper (S V : Finset Plane) (f : Plane → Plane) {M : ℝ}
    (hM : ∀ y ∈ V, ((S.filter (fun x => f x = y)).card : ℝ) ≤ M) :
    ∀ y ∈ (S.filter (fun x => f x ∈ V)).image f,
      (((S.filter (fun x => f x ∈ V)).filter (fun x => f x = y)).card : ℝ) ≤ M := by
  classical
  intro y hy
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
  have hyV : y ∈ V := hxy ▸ (Finset.mem_filter.mp hx).2
  have hc : (((S.filter (fun x => f x ∈ V)).filter (fun x => f x = y)).card : ℝ) ≤
      ((S.filter (fun x => f x = y)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (show
      (S.filter (fun x => f x ∈ V)).filter (fun x => f x = y) ⊆ S.filter (fun x => f x = y) by
      intro z hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1,
        (Finset.mem_filter.mp hz).2⟩)
  exact hc.trans (hM y hyV)

/-- Quantitative cardinal bookkeeping after uniform cell selection. -/
theorem coarse_cell_counts {F G U V₁ V₂ V₃ : Finset Plane} {J : Finset Triple}
    (hJne : J.Nonempty) (hJ : J ⊆ F ×ˢ (G ×ˢ U)) (f g h : Plane → Plane)
    {M₁ M₂ M₃ d K : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hd : 0 < d) (hK : 0 ≤ K)
    (h₁ : ∀ y ∈ V₁, M₁ ≤ ((F.filter (fun x => f x = y)).card : ℝ) ∧
      ((F.filter (fun x => f x = y)).card : ℝ) ≤ 2 * M₁)
    (h₂ : ∀ y ∈ V₂, M₂ ≤ ((G.filter (fun x => g x = y)).card : ℝ) ∧
      ((G.filter (fun x => g x = y)).card : ℝ) ≤ 2 * M₂)
    (h₃ : ∀ y ∈ V₃, M₃ ≤ ((U.filter (fun x => h x = y)).card : ℝ) ∧
      ((U.filter (fun x => h x = y)).card : ℝ) ≤ 2 * M₃)
    (hJV : ∀ p ∈ J, f p.1 ∈ V₁ ∧ g p.2.1 ∈ V₂ ∧ h p.2.2 ∈ V₃)
    (hden : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ K * (J.card : ℝ)) :
    (F.card : ℝ) ≤ (2 * K / d) * M₁ * (V₁.card : ℝ) ∧
    (G.card : ℝ) ≤ (2 * K / d) * M₂ * (V₂.card : ℝ) ∧
    (U.card : ℝ) ≤ (2 * K / d) * M₃ * (V₃.card : ℝ) ∧
    d * (V₁.card : ℝ) * (V₂.card : ℝ) * (V₃.card : ℝ) ≤
      8 * K * ((J.image (coarseTriple f g h)).card : ℝ) := by
  classical
  obtain ⟨p, hp⟩ := hJne
  have hpF := Finset.mem_product.mp (hJ hp)
  have hpG := Finset.mem_product.mp hpF.2
  have hFc : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr ⟨p.1, hpF.1⟩
  have hGc : (0 : ℝ) < G.card := by exact_mod_cast Finset.card_pos.mpr ⟨p.2.1, hpG.1⟩
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr ⟨p.2.2, hpG.2⟩
  let F₁ := F.filter (fun x => f x ∈ V₁)
  let G₁ := G.filter (fun x => g x ∈ V₂)
  let U₁ := U.filter (fun x => h x ∈ V₃)
  have hJ' : J ⊆ F₁ ×ˢ (G₁ ×ˢ U₁) := by
    intro q hq
    have hqF := Finset.mem_product.mp (hJ hq)
    have hqG := Finset.mem_product.mp hqF.2
    have hqV := hJV q hq
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hqF.1, hqV.1⟩,
      Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hqG.1, hqV.2.1⟩,
        Finset.mem_filter.mpr ⟨hqG.2, hqV.2.2⟩⟩⟩
  have hJcard : (J.card : ℝ) ≤ (F₁.card : ℝ) * (G₁.card : ℝ) * (U₁.card : ℝ) := by
    have hh := Finset.card_le_card hJ'
    simp only [Finset.card_product] at hh
    exact_mod_cast (by simpa only [mul_assoc] using hh)
  have hF₁ : (F₁.card : ℝ) ≤ 2 * M₁ * (V₁.card : ℝ) :=
    upper_fiber_count F V₁ f (fun y hy => (h₁ y hy).2)
  have hG₁ : (G₁.card : ℝ) ≤ 2 * M₂ * (V₂.card : ℝ) :=
    upper_fiber_count G V₂ g (fun y hy => (h₂ y hy).2)
  have hU₁ : (U₁.card : ℝ) ≤ 2 * M₃ * (V₃.card : ℝ) :=
    upper_fiber_count U V₃ h (fun y hy => (h₃ y hy).2)
  have hFsub : (F₁.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_filter_le F _
  have hGsub : (G₁.card : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast Finset.card_filter_le G _
  have hUsub : (U₁.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_filter_le U _
  have hc₁ := cancel_product_mass hGc hUc hd hK hden
    (hJcard.trans (show (F₁.card : ℝ) * (G₁.card : ℝ) * (U₁.card : ℝ) ≤
      (2 * M₁ * (V₁.card : ℝ)) * (G.card : ℝ) * (U.card : ℝ) by gcongr))
  have hc₂ := cancel_product_mass hFc hUc hd hK
    (show d * (G.card : ℝ) * (F.card : ℝ) * (U.card : ℝ) ≤ K * (J.card : ℝ) by nlinarith [hden])
    (hJcard.trans (show (F₁.card : ℝ) * (G₁.card : ℝ) * (U₁.card : ℝ) ≤
      (2 * M₂ * (V₂.card : ℝ)) * (F.card : ℝ) * (U.card : ℝ) by
        calc _ ≤ (F.card : ℝ) * (2 * M₂ * (V₂.card : ℝ)) * (U.card : ℝ) := by gcongr
          _ = _ := by ring))
  have hc₃ := cancel_product_mass hFc hGc hd hK
    (show d * (U.card : ℝ) * (F.card : ℝ) * (G.card : ℝ) ≤ K * (J.card : ℝ) by nlinarith [hden])
    (hJcard.trans (show (F₁.card : ℝ) * (G₁.card : ℝ) * (U₁.card : ℝ) ≤
      (2 * M₃ * (V₃.card : ℝ)) * (F.card : ℝ) * (G.card : ℝ) by
        calc _ ≤ (F.card : ℝ) * (G.card : ℝ) * (2 * M₃ * (V₃.card : ℝ)) := by gcongr
          _ = _ := by ring))
  refine ⟨by convert hc₁ using 1 <;> ring, by convert hc₂ using 1 <;> ring,
    by convert hc₃ using 1 <;> ring, ?_⟩
  have himage := coarse_triple_card_bound hJ' f g h (by positivity) (by positivity) (by positivity)
    (selected_fiber_upper F V₁ f (fun y hy => (h₁ y hy).2))
    (selected_fiber_upper G V₂ g (fun y hy => (h₂ y hy).2))
    (selected_fiber_upper U V₃ h (fun y hy => (h₃ y hy).2))
  have hl₁ : M₁ * (V₁.card : ℝ) ≤ (F.card : ℝ) :=
    (lower_fiber_count F V₁ f (fun y hy => (h₁ y hy).1)).trans hFsub
  have hl₂ : M₂ * (V₂.card : ℝ) ≤ (G.card : ℝ) :=
    (lower_fiber_count G V₂ g (fun y hy => (h₂ y hy).1)).trans hGsub
  have hl₃ : M₃ * (V₃.card : ℝ) ≤ (U.card : ℝ) :=
    (lower_fiber_count U V₃ h (fun y hy => (h₃ y hy).1)).trans hUsub
  have hproduct : (M₁ * M₂ * M₃) * (d * (V₁.card : ℝ) * (V₂.card : ℝ) * (V₃.card : ℝ)) ≤
      (M₁ * M₂ * M₃) * (8 * K * ((J.image (coarseTriple f g h)).card : ℝ)) := by
    calc _ = d * (M₁ * (V₁.card : ℝ)) * (M₂ * (V₂.card : ℝ)) * (M₃ * (V₃.card : ℝ)) := by ring
      _ ≤ d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) := by gcongr
      _ ≤ K * (J.card : ℝ) := hden
      _ ≤ K * ((2 * M₁) * (2 * M₂) * (2 * M₃) * ((J.image (coarseTriple f g h)).card : ℝ)) :=
        mul_le_mul_of_nonneg_left himage hK
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (mul_pos (mul_pos hM₁ hM₂) hM₃)).mp hproduct

end WangZahlLot.Obl.wz_separated_projection_dichotomy
