-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.LocalizationParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.RankPowerLoss
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.WindowClusterOrder
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.NearPairs

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The coefficient refinement can be fixed in terms of the chosen rank
loss, with a curvature contraction ratio uniform in the coefficient scale. -/
theorem exists_rank_refinement (ε : ℝ) (hε : 0 < ε) :
    ∃ B θ : ℝ, 1 < B ∧ 4 ≤ B^ε ∧ 0 < θ ∧ θ ≤ 1/10000 ∧
      ∀ D : ℝ, 0 ≤ D → 2*(19*(θ*D))*B ≤ D/120 := by
  obtain ⟨B, hB, hpower⟩ := exists_rank_base ε hε
  have hB0 : 0 < B := by linarith
  refine ⟨B, 1/(10000*B), hB, hpower, by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 10000*B)).mpr
    linarith
  · intro D hD
    have heq : 2*(19*(1/(10000*B)*D))*B = 38*D/10000 := by field_simp; ring
    rw [heq]
    linarith

/-- At a small slope threshold above the natural scale, narrow contacts
satisfy the value and slope margins for uniform curvature orientation. -/
theorem narrow_errors_lt_curvature_scale {δ D κ : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 < D)
    (hnatural : Real.sqrt (δ/D) ≤ κ) (hκ : κ < 1/100000) :
    2*δ < D/480 ∧ 2*κ*D < D/480 := by
  have hκ0 : 0 ≤ κ := (Real.sqrt_nonneg _).trans hnatural
  have hsq : δ/D ≤ κ^2 := by
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg (δ/D)) hκ0).mpr hnatural
    rwa [Real.sq_sqrt (div_nonneg hδ hD.le)] at hh
  have hδD : δ ≤ κ^2*D := (div_le_iff₀ hD).mp hsq
  have hκsq : κ^2 < 1/960 := by
    have hh := mul_self_lt_mul_self hκ0 hκ
    nlinarith only [hh]
  have hscale := mul_lt_mul_of_pos_right hκsq hD
  have hslope := mul_lt_mul_of_pos_right hκ hD
  constructor <;> nlinarith

/-- A nonempty narrow union supplies the one contact required to orient
the two refined clusters on a whole short window. -/
theorem curvature_order_of_narrow_union_nonempty {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (A B : Finset (Fin n)) {δ D κ l u : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 < D) (hnatural : Real.sqrt (δ/D) ≤ κ)
    (hκ : κ < 1/100000) (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u-l ≤ 1/10000)
    (hA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D/10000)
    (hB : ∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D/10000)
    (hcross : ∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2*D)
    (hne : ((⋃ i ∈ A, ⋃ j ∈ B,
      narrowIntersection δ κ (q i) (q j) (g i) (g j)) ∩
      {p : ℝ × ℝ | p.2 ∈ Icc l u}).Nonempty) :
    (∀ i ∈ A, ∀ j ∈ B, ∀ t ∈ Icc l u,
      D/120 ≤ deriv (deriv (g i)) t-deriv (deriv (g j)) t) ∨
    (∀ i ∈ A, ∀ j ∈ B, ∀ t ∈ Icc l u,
      D/120 ≤ deriv (deriv (g j)) t-deriv (deriv (g i)) t) := by
  have herr := narrow_errors_lt_curvature_scale hδ hD hnatural hκ
  apply window_cluster_curvature_order hg hjet A B hD herr.1 herr.2 hl hu hshort hA hB
    (fun i hi j hj => (hcross i hi j hj).1)
  obtain ⟨p, hp, hw⟩ := hne
  obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
  obtain ⟨j, hj, hp⟩ := mem_iUnion₂.mp hp
  refine ⟨i,hi,j,hj,p.2,hw,?_,?_⟩
  · have hh := abs_sub_le (g i p.2) p.1 (g j p.2)
    rw [abs_sub_comm (g i p.2) p.1] at hh
    linarith [hp.1.1.2, hp.1.2.2]
  · have hκ0 : 0 ≤ κ := (Real.sqrt_nonneg _).trans hnatural
    exact hp.2.le.trans (by nlinarith [mul_le_mul_of_nonneg_left (hcross i hi j hj).2 hκ0])

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
