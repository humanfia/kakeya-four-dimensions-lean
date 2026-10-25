-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.Contradiction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/Contradiction.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_square_frostman_graph_projection
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.Endgame

/-!
# Graph data contradict the accepted projection theorem (o223)

`graph_data_false`: for positive `e, b, β`, the accepted theorem
`WangZahlLot.wz_square_frostman_graph_projection` supplies `ζ, δ₀`; then no scale `δ ≤ δ₀`
carries graph data with that `ζ` (the data of o222's conclusion): the projection theorem gives a
direction `t ∈ S` in which every `δ^ζ`-dense subset needs `δ^(-α-ζ)` intervals, while the data
cover the projection of such a subset by `δ^(-α-ζ/2)` of them.

`tube_false`: combined with x0658's `graph_data_of_tube` (copied in `GraphData/Endgame.lean`), a
tube model at such a scale is contradictory.  This is the Case A contradiction.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

/-- Graph data at a small scale contradict the accepted projection theorem. -/
theorem graph_data_false {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ¬ ∃ α C : ℝ, 0 ≤ α ∧ α ≤ 1 - e ∧ 1 ≤ C ∧ C ≤ δ ^ (-ζ) ∧
        ∃ (G : Set (ℝ × ℝ)) (S : Set ℝ), G.Finite ∧ G.Nonempty ∧ S.Finite ∧ S.Nonempty ∧
          (∀ p ∈ G, |p.1| ≤ 4 ∧ |p.2| ≤ 4) ∧
          (∀ x y ρ : ℝ, δ ≤ ρ →
            ({p ∈ G | dist p.1 x ≤ ρ ∧ dist p.2 y ≤ ρ}.ncard : ℝ) ≤ C * ρ ^ (1 + b) * G.ncard) ∧
          (∀ x ρ : ℝ, δ ≤ ρ → ((S ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ ^ β * S.ncard) ∧
          (∀ t ∈ S, t ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ a ∈ Prod.fst '' G, ∀ a' ∈ Prod.fst '' G, a ≠ a' → δ ≤ dist a a') ∧
          (∀ a ∈ Prod.snd '' G, ∀ a' ∈ Prod.snd '' G, a ≠ a' → δ ≤ dist a a') ∧
          ((Prod.fst '' G).ncard : ℝ) ≤ δ ^ (-α - ζ) ∧
          ((Prod.snd '' G).ncard : ℝ) ≤ δ ^ (-α - ζ) ∧
          δ ^ (ζ - 2 * α) ≤ (G.ncard : ℝ) ∧
          (∀ t ∈ S, ∃ H : Set (ℝ × ℝ), H ⊆ G ∧ δ ^ ζ * G.ncard ≤ (H.ncard : ℝ) ∧
            ∃ (m : ℕ) (cc : Fin m → ℝ),
              (fun p : ℝ × ℝ => p.1 + t * p.2) '' H ⊆ (⋃ j, Metric.closedBall (cc j) δ) ∧
              (m : ℝ) ≤ δ ^ (-α - ζ / 2)) := by
  obtain ⟨ζ, δ₀, hζ, hδ₀, hδ₀1, hproject⟩ :=
    WangZahlLot.wz_square_frostman_graph_projection e b β he hb hβ
  refine ⟨ζ, min δ₀ (1 / 2), hζ, lt_min hδ₀ (by norm_num), (min_le_right _ _).trans (by norm_num),
    ?_⟩
  intro δ hδ hδδ₀
  rintro ⟨α, C, hα, hαmax, hC, hCmax, G, S, hGfin, hGne, hSfin, hSne, hGbound, hGsquare,
    hScount, hSunit, hAsep, hBsep, hAsize, hBsize, hGsize, hsmallproj⟩
  obtain ⟨t, ht, hlarge⟩ :=
    hproject δ α C hδ (hδδ₀.trans (min_le_left _ _)) hα hαmax hC hCmax G S hGfin hGne hSfin hSne
      hGbound hGsquare hScount hSunit hAsep hBsep hAsize hBsize hGsize
  obtain ⟨H, hHG, hHdense, m, cc, hcover, hm⟩ := hsmallproj t ht
  have hlower := hlarge H hHG hHdense m cc hcover
  have hδ1 : δ < 1 := lt_of_le_of_lt (hδδ₀.trans (min_le_right _ _)) (by norm_num)
  have hstrict : δ ^ (-α - ζ / 2) < δ ^ (-α - ζ) :=
    Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith)
  exact (not_lt_of_ge hlower) (hm.trans_lt hstrict)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

/-- **Case A contradiction.**  For positive `e, b, β` there are `ζ, δ₀` such that no tube model in
the sense of x0658's `graph_data_of_tube` exists at a scale `δ ≤ δ₀`. -/
theorem tube_model_false {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∀ (δ F K B : ℝ), 0 < δ → δ ≤ δ₀ →
      1 ≤ B → 1 ≤ K → 1 ≤ F → F ≤ δ ^ (-(1 - e)) →
      (4 * K * (2 * (1 + B) ^ 2) ^ β) * 2 ^ (1 + b) ≤ δ ^ (-ζ) →
      4 ≤ δ ^ (-(ζ / 2)) →
      ∀ (W : Finset (ℝ × ℝ)), W.Nonempty →
      (∀ w ∈ W, |w.1| ≤ 7 / 2 ∧ |w.2| ≤ 7 / 2) →
      (∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → δ ≤ dist w w') →
      ∀ (Y0 Y1 : Finset ℝ), (Y0.card : ℝ) ≤ F → (Y1.card : ℝ) ≤ F →
      (∀ w ∈ W, ∃ y ∈ Y0, |w.1 - y| ≤ δ) → (∀ w ∈ W, ∃ y ∈ Y1, |w.2 - y| ≤ δ) →
      (∀ x y ρ : ℝ, δ ≤ ρ →
        ((W.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ)).card : ℝ) ≤
          K * ρ ^ (1 + b) * W.card) →
      F ^ 2 ≤ K * W.card →
      ∀ (X : Finset ℝ), X.Nonempty → (∀ τ ∈ X, |τ| ≤ B) →
      (∀ x ρ : ℝ, δ ≤ ρ →
        ((X.filter (fun τ => dist τ x ≤ ρ)).card : ℝ) ≤ K * ρ ^ β * X.card) →
      ∀ (Wx : ℝ → Finset (ℝ × ℝ)), (∀ τ ∈ X, Wx τ ⊆ W) →
      (∀ τ ∈ X, (W.card : ℝ) ≤ K * (Wx τ).card) →
      ∀ (Yx : ℝ → Finset ℝ), (∀ τ ∈ X, ((Yx τ).card : ℝ) ≤ F) →
      (∀ τ ∈ X, ∀ w ∈ Wx τ, ∃ y ∈ Yx τ, |hgt w τ - y| ≤ δ) → False := by
  obtain ⟨ζ, δ₀, hζ, hδ₀, hδ₀1, hnot⟩ := graph_data_false he hb hβ
  refine ⟨ζ, min δ₀ (1 / 2), hζ, lt_min hδ₀ (by norm_num), min_le_right _ _, ?_⟩
  intro δ F K B hδ hδδ₀ hB hK hF hFe hloss h4 W hWne hWb hWsep Y0 Y1 hY0 hY1 hW0 hW1 hsq hWbig
    X hXne hXB hXfr Wx hWx hWxbig Yx hYx hcovx
  have hδ2 : δ ≤ 1 / 2 := hδδ₀.trans (min_le_right _ _)
  exact hnot δ hδ (hδδ₀.trans (min_le_left _ _))
    (graph_data_of_tube hδ hδ2 hζ hb hβ.le hB hK hF hFe hloss h4 W hWne hWb hWsep Y0 Y1 hY0 hY1
      hW0 hW1 hsq hWbig X hXne hXB hXfr Wx hWx hWxbig Yx hYx hcovx)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
