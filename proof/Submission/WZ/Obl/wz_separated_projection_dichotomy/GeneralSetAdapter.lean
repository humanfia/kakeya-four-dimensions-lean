-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.GeneralSetAdapter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.GeneralSeparated
import Submission.WZ.Obl.wz_separated_projection_dichotomy.SetInterface

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem StripCountConclusion.mono_epsilon {δ ε ε' : ℝ} {F G : Set Plane}
    (h : StripCountConclusion δ ε F G) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : ε ≤ ε') :
    StripCountConclusion δ ε' F G := by
  obtain ⟨e, e', he, he', hee', c, c', hFc, hGc⟩ := h
  have hp : δ ^ (ε' - 1) ≤ δ ^ (ε - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  exact ⟨e, e', he, he', hee', c, c', hp.trans hFc, hp.trans hGc⟩

/-- Proposition 8.9 in the literal set interface of the split, from the
bounded separated nonconcentrated projection principle. -/
theorem separated_set_statement_of_bounded_nonconcentrated
    (hnc : BoundedNonconcentratedPrinciple true) : SeparatedSetStatement := by
  classical
  intro Fr hFr ε hε
  subst Fr
  let ε' := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  obtain ⟨θ, d₀, hθ, hd₀, hcore⟩ := general_separated_dichotomy_of_bounded_nonconcentrated
    hnc hε' (min_le_right _ _)
  refine ⟨θ, min d₀ 1, hθ, by positivity, ?_⟩
  intro δ hδ hs F G U H hF hG hU hFgeom hGdiam hUdiam hcross hH hHne hden
  have hδ1 := hs.trans (min_le_right _ _)
  have hHfin : H.Finite := (hF.1.prod (hG.1.prod hU.1)).subset hH
  let S := hF.1.toFinset
  let T := hG.1.toFinset
  let V := hU.1.toFinset
  let J := hHfin.toFinset
  have hS : (↑S : Set Plane) = F := hF.1.coe_toFinset
  have hT : (↑T : Set Plane) = G := hG.1.coe_toFinset
  have hV : (↑V : Set Plane) = U := hU.1.coe_toFinset
  have hJ : (↑J : Set Triple) = H := hHfin.coe_toFinset
  have hSc : (S.card : ℝ) = (F.ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card F hF.1]
  have hTc : (T.card : ℝ) = (G.ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card G hG.1]
  have hVc : (V.card : ℝ) = (U.ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card U hU.1]
  have hJc : (J.card : ℝ) = (H.ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card H hHfin]
  have hSF : ClosedFiniteFrostman δ (δ ^ (-θ)) S := by
    intro x r hr
    simpa only [hS, hSc] using hF.2.2 x r hr
  have hTF : ClosedFiniteFrostman δ (δ ^ (-θ)) T := by
    intro x r hr
    simpa only [hT, hTc] using hG.2.2 x r hr
  have hVF : ClosedFiniteFrostman δ (δ ^ (-θ)) V := by
    intro x r hr
    simpa only [hV, hVc] using hU.2.2 x r hr
  have hJsub : J ⊆ S ×ˢ (T ×ˢ V) := by
    intro p hp
    have hh := hH (hHfin.mem_toFinset.mp hp)
    exact Finset.mem_product.mpr ⟨hF.1.mem_toFinset.mpr hh.1,
      Finset.mem_product.mpr ⟨hG.1.mem_toFinset.mpr hh.2.1, hU.1.mem_toFinset.mpr hh.2.2⟩⟩
  have hJne : J.Nonempty := by
    obtain ⟨p, hp⟩ := hHne
    exact ⟨p, hHfin.mem_toFinset.mpr hp⟩
  have hdense : δ ^ θ * (S.card : ℝ) * (T.card : ℝ) * (V.card : ℝ) ≤ (J.card : ℝ) := by
    simpa only [hSc, hTc, hVc, hJc] using hden
  have hresult := hcore δ hδ (hs.trans (min_le_left _ _)) S T V
    (fun x hx => (hF.2.1 x (hF.1.mem_toFinset.mp hx)).1)
    (fun x hx => (hG.2.1 x (hG.1.mem_toFinset.mp hx)).1)
    (fun x hx => (hU.2.1 x (hU.1.mem_toFinset.mp hx)).1) hSF hTF hVF
    (fun x hx y hy => (hGdiam x (hG.1.mem_toFinset.mp hx) y (hG.1.mem_toFinset.mp hy)).trans (by norm_num))
    (fun x hx y hy => (hUdiam x (hU.1.mem_toFinset.mp hx) y (hU.1.mem_toFinset.mp hy)).trans (by norm_num))
    (fun x hx y hy => by simpa only [dist_eq_norm] using hcross x (hG.1.mem_toFinset.mp hx) y (hU.1.mem_toFinset.mp hy))
    J hJne hJsub hdense
  change StripCountConclusion δ ε F G ∨ ProjectionGain δ θ ε H
  rcases hresult with hl | hp
  · left
    rw [hS, hT] at hl
    exact hl.mono_epsilon hδ hδ1 (min_le_left _ _)
  · right
    rw [hJ] at hp
    exact hp.mono_epsilon hδ hδ1 hθ.le (min_le_left _ _)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
