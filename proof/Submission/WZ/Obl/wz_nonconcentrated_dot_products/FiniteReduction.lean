-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.FiniteReduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.FiniteWitness
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Parameters

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

theorem InUnitSquare.isBounded {F : Set Plane} (h : InUnitSquare F) :
    Bornology.IsBounded F := by
  apply (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 2)).subset
  intro x hx
  rw [EuclideanSpace.closedBall_zero_eq 2 (by norm_num)]
  have h0 := h x hx 0
  have h1 := h x hx 1
  have hs0 : (x 0) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg h0.1 (sub_nonneg.mpr h0.2)]
  have hs1 : (x 1) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg h1.1 (sub_nonneg.mpr h1.2)]
  simp only [Set.mem_ofPred_eq, Fin.sum_univ_two]
  linarith

theorem AD.mono_set {δ C : ℝ} {F F' : Set Plane} (h : AD δ C F) (hF : F' ⊆ F) :
    AD δ C F' := by
  intro x ρ r hδρ hρr
  obtain ⟨m, c, hc, hm⟩ := h x ρ r hδρ hρr
  exact ⟨m, c, hc.mono_set (Set.inter_subset_inter_left _ hF), hm⟩

theorem LineConclusion.mono_set {δ ε : ℝ} {F F' G G' : Set Plane}
    (h : LineConclusion δ ε F G) (hF : F ⊆ F') (hG : G ⊆ G') :
    LineConclusion δ ε F' G' := by
  obtain ⟨e, b, c, he, hf, hg⟩ := h
  exact ⟨e, b, c, he, hf.mono_set (Set.inter_subset_inter_right _ hF),
    hg.mono_set (Set.inter_subset_inter_right _ hG)⟩

theorem DotSet.mono {Q Q' : Set Triple} (h : Q ⊆ Q') : DotSet Q ⊆ DotSet Q' := by
  rintro t ⟨x, hx, ht⟩
  exact ⟨x, h hx, ht⟩

theorem ProjectionGain.mono_set {δ η ε : ℝ} {Q Q' : Set Triple}
    (h : ProjectionGain δ η ε Q) (hQ : Q ⊆ Q') : ProjectionGain δ η ε Q' := by
  obtain ⟨ρ, a, L, hρ, hL, hcov⟩ := h
  exact ⟨ρ, a, L, hρ, hL, hcov.mono_set (Set.inter_subset_inter_right _ (DotSet.mono hQ))⟩

/-- The finite-set case of the frozen theorem at fixed parameters. -/
def FiniteDichotomyAt (δ η ε : ℝ) : Prop :=
  ∀ F G : Set Plane, F.Finite → G.Finite → InUnitSquare F → InUnitSquare G →
    AD δ (δ ^ (-η)) F → AD δ (δ ^ (-η)) G →
    LineConclusion δ ε F G ∨ ProjectionConclusion δ η ε F G

/-- Passing from finite sets to arbitrary bounded sets costs no radius or exponent. -/
theorem dichotomy_of_finite {δ η ε : ℝ} (hδ : 0 < δ)
    (hfinite : FiniteDichotomyAt δ η ε) (F G : Set Plane)
    (hF : InUnitSquare F) (hG : InUnitSquare G)
    (hAF : AD δ (δ ^ (-η)) F) (hAG : AD δ (δ ^ (-η)) G) :
    LineConclusion δ ε F G ∨ ProjectionConclusion δ η ε F G := by
  classical
  by_cases hline : LineConclusion δ ε F G
  · exact Or.inl hline
  right
  intro Q hQ hcover
  have hQB : Bornology.IsBounded Q :=
    (hF.isBounded.prod (hG.isBounded.prod hG.isBounded)).subset hQ
  obtain ⟨T, hTQ, hTcover⟩ := hcover.exists_finite_subset hδ.le hQB
  let F' : Set Plane := Prod.fst '' (↑T : Set Triple)
  let G' : Set Plane := (fun p : Triple => p.2.1) '' (↑T : Set Triple) ∪
    (fun p : Triple => p.2.2) '' (↑T : Set Triple)
  have hF' : F' ⊆ F := by
    rintro x ⟨p, hp, rfl⟩
    exact (hQ (hTQ hp)).1
  have hG' : G' ⊆ G := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (hQ (hTQ hp)).2.1
    · exact (hQ (hTQ hp)).2.2
  have hF'fin : F'.Finite := T.finite_toSet.image _
  have hG'fin : G'.Finite := (T.finite_toSet.image _).union (T.finite_toSet.image _)
  have hTprod : (↑T : Set Triple) ⊆ F' ×ˢ (G' ×ˢ G') := by
    intro p hp
    exact ⟨⟨p, hp, rfl⟩, Or.inl ⟨p, hp, rfl⟩, Or.inr ⟨p, hp, rfl⟩⟩
  have hfin := hfinite F' G' hF'fin hG'fin
    (fun a ha => hF a (hF' ha)) (fun b hb => hG b (hG' hb))
    (hAF.mono_set hF') (hAG.mono_set hG')
  rcases hfin with hline' | hproj
  · exact (hline (hline'.mono_set hF' hG')).elim
  · exact (hproj (↑T : Set Triple) hTprod hTcover).mono_set hTQ

/-- Only finite plane sets and exponents strictly between zero and one are needed. -/
theorem reduce_to_finite_small_epsilon
    (H : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → FiniteDichotomyAt δ η ε) :
    ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ F G : Set Plane,
        InUnitSquare F → InUnitSquare G → AD δ (δ ^ (-η)) F → AD δ (δ ^ (-η)) G →
        LineConclusion δ ε F G ∨ ProjectionConclusion δ η ε F G := by
  intro ε hε
  by_cases hε1 : ε < 1
  · obtain ⟨η, δ₀, hη, hδ₀, hfin⟩ := H ε hε hε1
    refine ⟨η, δ₀, hη, hδ₀, ?_⟩
    intro δ hδ hδ₀' F G hF hG hAF hAG
    exact dichotomy_of_finite hδ (hfin δ hδ hδ₀') F G hF hG hAF hAG
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro δ hδ hδ1 F G hF hG hAF hAG
    exact Or.inr (projectionConclusion_of_one_le_epsilon hδ hδ1 (by norm_num)
      (le_of_not_gt hε1))

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
