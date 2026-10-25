-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.ModelReduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Stability

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

def CenterSet {S T : Finset Plane} (H : Finset (S × T × T)) : Set Triple :=
  tripleCenter '' (H : Set (S × T × T))

/-- The remaining finite projection statement, with all constants from the
cover-to-counting reduction exposed. This definition makes no assertion that
the finite statement has been proved. -/
def CenterDichotomyAt (δ η ε : ℝ) : Prop :=
  ∀ S T : Finset Plane,
    InUnitSquare (↑S : Set Plane) → InUnitSquare (↑T : Set Plane) →
    δ ^ (3 * η - 1) / 9 ≤ (S.card : ℝ) →
    δ ^ (3 * η - 1) / 9 ≤ (T.card : ℝ) →
    (S.card : ℝ) ≤ 75 * δ ^ (-η) / δ →
    (T.card : ℝ) ≤ 75 * δ ^ (-η) / δ →
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ < dist a b) →
    (∀ a ∈ T, ∀ b ∈ T, a ≠ b → δ < dist a b) →
    FiniteFrostman δ (225 * δ ^ (-4 * η)) S →
    FiniteFrostman δ (225 * δ ^ (-4 * η)) T →
    ∀ H : Finset (S × T × T), δ ^ (η - 3) ≤ (H.card : ℝ) →
      LineConclusion δ ε (↑S : Set Plane) (↑T : Set Plane) ∨
        ProjectionGain δ η (ε / 2) (CenterSet H)

/-- An explicit finite Frostman hypergraph theorem suffices for the original
AD dichotomy. The projection conclusion survives the quantization error. -/
theorem dichotomy_of_center_model {δ η ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : 153 ≤ δ ^ (-(η * ε / 2))) (hcore : CenterDichotomyAt δ η ε)
    {F G : Set Plane} (hF : InUnitSquare F) (hG : InUnitSquare G)
    (hAF : AD δ (δ ^ (-η)) F) (hAG : AD δ (δ ^ (-η)) G) :
    LineConclusion δ ε F G ∨ ProjectionConclusion δ η ε F G := by
  classical
  by_cases hline : LineConclusion δ ε F G
  · exact Or.inl hline
  right
  intro Q hQ hN
  obtain ⟨S, T, hS, hT⟩ :=
    exists_frostman_nets_of_large_triples hδ hδ1 hF hG hAF hAG hQ hN
  obtain ⟨hSF, hSN, hSsep, hScov, hSFr⟩ := hS
  obtain ⟨hTG, hTN, hTsep, hTcov, hTFr⟩ := hT
  obtain ⟨H, hHN, hHcov, p, hp⟩ := exists_tripartite_model hQ hN S T hScov hTcov
  have hSsq : InUnitSquare (↑S : Set Plane) := fun x hx => hF x (hSF hx)
  have hTsq : InUnitSquare (↑T : Set Plane) := fun x hx => hG x (hTG hx)
  have hSup := hAF.separated_card_bound hδ hδ1 hF S hSF
    (fun a ha b hb hab => (hSsep a ha b hb hab).le)
  have hTup := hAG.separated_card_bound hδ hδ1 hG T hTG
    (fun a ha b hb hab => (hTsep a ha b hb hab).le)
  rcases hcore S T hSsq hTsq hSN hTN hSup hTup hSsep hTsep hSFr hTFr H hHN with hl | hg
  · exact (hline (hl.mono_set hSF hTG)).elim
  apply hg.of_approximation hδ hδ1 hη hε hε1 hsmall
  rintro q ⟨i, hi, rfl⟩
  refine ⟨p ⟨i, hi⟩, (hp ⟨i, hi⟩).1, ?_⟩
  have hic : tripleCenter i ∈ F ×ˢ (G ×ˢ G) :=
    ⟨hSF i.1.property, hTG i.2.1.property, hTG i.2.2.property⟩
  have hd := dotValue_sub_le_of_square hF hG (hQ (hp ⟨i, hi⟩).1) hic
    (hp ⟨i, hi⟩).2
  simpa only [Real.dist_eq, abs_sub_comm] using hd

/-- The parameter-level bridge to the frozen theorem. -/
theorem reduce_to_center_dichotomy
    (hcore : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η δ₀ : ℝ,
      0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → CenterDichotomyAt δ η ε) :
    ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ F G : Set Plane,
        InUnitSquare F → InUnitSquare G → AD δ (δ ^ (-η)) F → AD δ (δ ^ (-η)) G →
          LineConclusion δ ε F G ∨ ProjectionConclusion δ η ε F G := by
  apply reduce_to_finite_small_epsilon
  intro ε hε hε1
  obtain ⟨η, d, hη, hd, hcore'⟩ := hcore ε hε hε1
  obtain ⟨s, hs, hs1, hstab⟩ := exists_stability_cutoff hε hη
  refine ⟨η, min d s, hη, lt_min hd hs, ?_⟩
  intro δ hδ hδ₀ F G hFfin hGfin hF hG hAF hAG
  have hδd : δ ≤ d := hδ₀.trans (min_le_left _ _)
  have hδs : δ ≤ s := hδ₀.trans (min_le_right _ _)
  exact dichotomy_of_center_model hδ (hδs.trans hs1) hη.le hε hε1.le
    (hstab δ hδ hδs) (hcore' δ hδ hδd) hF hG hAF hAG

end WangZahlLot.Obl.wz_separated_projection_dichotomy
