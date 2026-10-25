-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.GlobalUnion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.NarrowWindowBridge

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set MeasureTheory
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The local estimate consumed by coefficient and time localization. -/
def OrientedWindowEstimate (ε θ C : ℝ) : Prop :=
  ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
    (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
  ∀ δ : ℝ, 0 < δ → δ ≤ (1/100:ℝ) →
    (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
  ∀ (A B : Finset (Fin n)) (D κ l u : ℝ), δ ≤ D → D ≤ 20 →
    0 < κ → Real.sqrt (δ/D) ≤ κ → κ < 1/100000 →
    -1 ≤ l → u ≤ 1 → l ≤ u → u-l ≤ 1/10000 →
    (∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ θ*D) →
    (∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ θ*D) →
    (∀ i ∈ A, ∀ j ∈ B, dist (q i) (q j) ≤ 2*D) →
    ((∀ i ∈ A, ∀ j ∈ B, ∀ t ∈ Icc l u,
        D/120 ≤ deriv (deriv (g i)) t-deriv (deriv (g j)) t) ∨
      (∀ i ∈ A, ∀ j ∈ B, ∀ t ∈ Icc l u,
        D/120 ≤ deriv (deriv (g j)) t-deriv (deriv (g i)) t)) →
    volume (narrowWindowUnion A B g δ l u (2*κ*D)) ≤
      ENNReal.ofReal (C*δ^(-ε)*δ*Real.sqrt (δ/D)*
        ((A.card:ℝ)+(B.card:ℝ))*Real.sqrt ((A.card:ℝ)+(B.card:ℝ)))

/-- The hereditary one-rich estimate needed by the sampling reduction. -/
def NarrowUnionEstimate (ε C : ℝ) : Prop :=
  ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
    (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
  ∀ δ : ℝ, 0 < δ → δ ≤ (1/100:ℝ) →
    (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
  ∀ (A B : Finset (Fin n)) (D κ : ℝ), δ ≤ D → D ≤ 20 →
    0 < κ → Real.sqrt (δ/D) ≤ κ →
    (∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D/100) →
    (∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D/100) →
    (∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2*D) →
    volume (⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ≤
      ENNReal.ofReal (C*δ^(-ε)*δ*
        (Real.sqrt (δ/D)*((A.card:ℝ)+(B.card:ℝ))*Real.sqrt ((A.card:ℝ)+(B.card:ℝ))+
          κ*((A.card:ℝ)+(B.card:ℝ))))

/-- Summing the refined short-window estimate gives the full hereditary
union estimate, including the elementary large-threshold range. -/
theorem narrowUnionEstimate_of_orientedWindowEstimate {ε θ C : ℝ}
    (hε : 0 ≤ ε) (hθ : 0 < θ) (hθsmall : θ ≤ 1/10000) (hC : 0 ≤ C)
    (hlocal : OrientedWindowEstimate ε θ C) :
    NarrowUnionEstimate ε (400000+20000*(27648/θ^3)^2*C) := by
  intro n q g hq hg hjet δ hδ hδ100 hsep A B D κ hδD hD20 hκ hnatural hA hB hcross
  have hD : 0 < D := hδ.trans_le hδD
  have hδ1 : δ ≤ 1 := by linarith
  let N : ℝ := (A.card:ℝ)+(B.card:ℝ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let J : ℝ := 20000*(27648/θ^3)^2
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hfactor : 0 ≤ δ^(-ε)*δ := by positivity
  have hmass : 0 ≤ Real.sqrt (δ/D)*N*Real.sqrt N+κ*N := by positivity
  by_cases hsmall : κ < 1/100000
  · let T : ℝ := C*δ^(-ε)*δ*Real.sqrt (δ/D)
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hwin : ∀ F ⊆ A, ∀ G ⊆ B,
        (∀ i ∈ F, ∀ j ∈ F, dist (q i) (q j) ≤ θ*D) →
        (∀ i ∈ G, ∀ j ∈ G, dist (q i) (q j) ≤ θ*D) →
        ∀ w : Fin 20000,
        volume ((⋃ i ∈ F, ⋃ j ∈ G, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ∩
          {p : ℝ × ℝ | p.2 ∈ Icc (timeWindowLeft w) (timeWindowRight w)}) ≤
          ENNReal.ofReal (T*((F.card:ℝ)+(G.card:ℝ))*Real.sqrt ((F.card:ℝ)+(G.card:ℝ))) := by
      intro F hFA G hGB hFd hGd w
      have hw := timeWindow_bounds w
      have hthetaD : θ*D ≤ D/10000 := by nlinarith [mul_le_mul_of_nonneg_right hθsmall hD.le]
      apply volume_localized_narrow_union_le_of_oriented_window hg hjet F G hδ.le hD
        hnatural hsmall hw.1 hw.2.2.1 hw.2.2.2.le
        (fun i hi j hj => (hFd i hi j hj).trans hthetaD)
        (fun i hi j hj => (hGd i hi j hj).trans hthetaD)
        (fun i hi j hj => hcross i (hFA hi) j (hGB hj))
      intro hord
      exact hlocal hq hg hjet δ hδ hδ100 hsep F G D κ
        (timeWindowLeft w) (timeWindowRight w) hδD hD20 hκ hnatural hsmall
        hw.1 hw.2.2.1 hw.2.1.le hw.2.2.2.le hFd hGd
        (fun i hi j hj => (hcross i (hFA hi) j (hGB hj)).2) hord
    have hb := volume_narrow_union_le_of_refined_windows A B q g hD hθ
      (by linarith : θ ≤ 1) hT
      (fun i hi j hj => (hA i hi j hj).trans (by linarith))
      (fun i hi j hj => (hB i hi j hj).trans (by linarith)) hwin
    apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
    change J*T*N*Real.sqrt N ≤ (400000+J*C)*δ^(-ε)*δ*(Real.sqrt (δ/D)*N*Real.sqrt N+κ*N)
    have hle : J*C*(Real.sqrt (δ/D)*N*Real.sqrt N) ≤
        (400000+J*C)*(Real.sqrt (δ/D)*N*Real.sqrt N+κ*N) := by
      have hr : 0 ≤ Real.sqrt (δ/D)*N*Real.sqrt N := by positivity
      have hkN : 0 ≤ κ*N := by positivity
      nlinarith [mul_nonneg (mul_nonneg hJ hC) hkN]
    have hh := mul_le_mul_of_nonneg_left hle hfactor
    dsimp [T]
    nlinarith only [hh]
  · apply (volume_narrow_union_le_of_large_threshold A B q g hδ hδ1 hε
      (le_of_not_gt hsmall) (fun i _ => (hg i).continuous)).trans
    apply ENNReal.ofReal_le_ofReal
    change 400000*δ^(-ε)*δ*(Real.sqrt (δ/D)*N*Real.sqrt N+κ*N) ≤
      (400000+J*C)*δ^(-ε)*δ*(Real.sqrt (δ/D)*N*Real.sqrt N+κ*N)
    have hh := mul_nonneg (mul_nonneg (mul_nonneg hJ hC) hfactor) hmass
    nlinarith only [hh]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
