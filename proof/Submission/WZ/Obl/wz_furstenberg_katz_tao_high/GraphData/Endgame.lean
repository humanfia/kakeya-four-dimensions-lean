-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.Endgame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/Endgame.lean (82de8bd).
-- Copied from workspace o222, branch x0658 (commit 1206391), Endgame.lean; namespace renamed.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.Charts

/-!
# Endgame of o222 in its exponent form

`graph_data_of_tube` turns a tube model (codes of tube lines at the normalized
anchors `0, 1`, anchor fibers of size `≤ F`, columns at positions `τ ∈ [-B, B]`
each with a dense subfamily whose heights lie near a fiber of size `≤ F`,
square-Frostman codes and Frostman positions, all with one loss `K`) into the
graph data of the conclusion of o222, with `δ ^ (-α) = F`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open Set Metric

lemma rpow_neg_logratio {δ F : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hF : 0 < F) :
    δ ^ (-(Real.log F / Real.log δ⁻¹)) = F := by
  have hl : 0 < Real.log δ⁻¹ := Real.log_pos (one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  rw [Real.rpow_def_of_pos hδ, Real.log_inv] at *
  have hl' : Real.log δ ≠ 0 := by linarith
  rw [show Real.log δ * -(Real.log F / -Real.log δ) = Real.log F by field_simp]
  exact Real.exp_log hF

theorem graph_data_of_tube {δ ζ e b β F K B : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (_hζ : 0 < ζ) (hb : 0 < b) (hβ : 0 ≤ β) (hB : 1 ≤ B) (hK : 1 ≤ K) (hF : 1 ≤ F)
    (hFe : F ≤ δ ^ (-(1 - e)))
    (hloss : (4 * K * (2 * (1 + B) ^ 2) ^ β) * 2 ^ (1 + b) ≤ δ ^ (-ζ))
    (h4 : 4 ≤ δ ^ (-(ζ / 2)))
    (W : Finset (ℝ × ℝ)) (hWne : W.Nonempty)
    (hWb : ∀ w ∈ W, |w.1| ≤ 7 / 2 ∧ |w.2| ≤ 7 / 2)
    (hWsep : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → δ ≤ dist w w')
    (Y0 Y1 : Finset ℝ) (hY0 : (Y0.card : ℝ) ≤ F) (hY1 : (Y1.card : ℝ) ≤ F)
    (hW0 : ∀ w ∈ W, ∃ y ∈ Y0, |w.1 - y| ≤ δ) (hW1 : ∀ w ∈ W, ∃ y ∈ Y1, |w.2 - y| ≤ δ)
    (hsq : ∀ x y ρ : ℝ, δ ≤ ρ →
      ((W.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ)).card : ℝ) ≤
        K * ρ ^ (1 + b) * W.card)
    (hWbig : F ^ 2 ≤ K * W.card)
    (X : Finset ℝ) (hXne : X.Nonempty) (hXB : ∀ τ ∈ X, |τ| ≤ B)
    (hXfr : ∀ x ρ : ℝ, δ ≤ ρ →
      ((X.filter (fun τ => dist τ x ≤ ρ)).card : ℝ) ≤ K * ρ ^ β * X.card)
    (Wx : ℝ → Finset (ℝ × ℝ)) (hWx : ∀ τ ∈ X, Wx τ ⊆ W)
    (hWxbig : ∀ τ ∈ X, (W.card : ℝ) ≤ K * (Wx τ).card)
    (Yx : ℝ → Finset ℝ) (hYx : ∀ τ ∈ X, ((Yx τ).card : ℝ) ≤ F)
    (hcovx : ∀ τ ∈ X, ∀ w ∈ Wx τ, ∃ y ∈ Yx τ, |hgt w τ - y| ≤ δ) :
    ∃ α C : ℝ, 0 ≤ α ∧ α ≤ 1 - e ∧ 1 ≤ C ∧ C ≤ δ ^ (-ζ) ∧
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
  have hδ1 : δ < 1 := by linarith
  have hγ : (0 : ℝ) ≤ 1 + b := by linarith
  obtain ⟨G, S, hGf, hGne, hSf, hSne, hG4, hGsq, hSfr, hS01, hfsep, hssep, hfc, hsc, hGbig,
    hH⟩ := positions_endgame (γ := 1 + b) hδ hδ2 hK hγ hβ hB W hWne hWb hWsep Y0 Y1 hY0 hY1
      hW0 hW1 hsq hWbig X hXne hXB hXfr Wx hWx hWxbig Yx hYx hcovx
  set K₁ : ℝ := 4 * K * (2 * (1 + B) ^ 2) ^ β with hK₁
  have hBB : (1 : ℝ) ≤ 2 * (1 + B) ^ 2 := by nlinarith
  have hpow : (1 : ℝ) ≤ (2 * (1 + B) ^ 2) ^ β := Real.one_le_rpow hBB hβ
  have hK₁1 : 1 ≤ K₁ := by rw [hK₁]; nlinarith
  have h2b : (1 : ℝ) ≤ 2 ^ (1 + b) := Real.one_le_rpow (by norm_num) hγ
  have hK₁le : K₁ ≤ K₁ * 2 ^ (1 + b) := by nlinarith
  have hK₁z : K₁ ≤ δ ^ (-ζ) := hK₁le.trans hloss
  have hFpos : 0 < F := by linarith
  set α : ℝ := Real.log F / Real.log δ⁻¹ with hα
  have hlogpos : 0 < Real.log δ⁻¹ := Real.log_pos (one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  have hFα : δ ^ (-α) = F := rpow_neg_logratio hδ hδ1 hFpos
  have hα0 : 0 ≤ α := div_nonneg (Real.log_nonneg hF) hlogpos.le
  have hαe : α ≤ 1 - e := by
    rw [hα, div_le_iff₀ hlogpos]
    have := Real.log_le_log hFpos hFe
    rw [Real.log_rpow hδ] at this
    rw [Real.log_inv]
    have h' : (1 - e) * (-Real.log δ) = -(1 - e) * Real.log δ := by ring
    linarith
  have hz : δ ^ ζ * δ ^ (-ζ) = 1 := by
    rw [← Real.rpow_add hδ]; simp
  have hzpos : 0 < δ ^ ζ := Real.rpow_pos_of_pos hδ ζ
  have hK₁dz : δ ^ ζ * K₁ ≤ 1 := by
    calc δ ^ ζ * K₁ ≤ δ ^ ζ * δ ^ (-ζ) := mul_le_mul_of_nonneg_left hK₁z hzpos.le
      _ = 1 := hz
  have hK₁4 : 4 ≤ K₁ := by rw [hK₁]; nlinarith
  have h3 : 3 ≤ δ ^ (-ζ) := by linarith
  have hF0 : 0 ≤ F := hFpos.le
  have h3F : 3 * F ≤ F * δ ^ (-ζ) := by nlinarith [mul_le_mul_of_nonneg_left h3 hF0]
  have h4F : 4 * F ≤ F * δ ^ (-(ζ / 2)) := by nlinarith [mul_le_mul_of_nonneg_left h4 hF0]
  have hαζ : δ ^ (-α - ζ) = F * δ ^ (-ζ) := by
    rw [sub_eq_add_neg, Real.rpow_add hδ, hFα]
  have hαζ2 : δ ^ (-α - ζ / 2) = F * δ ^ (-(ζ / 2)) := by
    rw [sub_eq_add_neg, Real.rpow_add hδ, hFα]
  have hζ2α : δ ^ (ζ - 2 * α) = δ ^ ζ * F ^ 2 := by
    rw [sub_eq_add_neg, Real.rpow_add hδ, show -(2 * α) = (-α) * 2 by ring,
      Real.rpow_mul hδ.le, hFα]
    norm_cast
  refine ⟨α, K₁ * 2 ^ (1 + b), hα0, hαe, hK₁1.trans hK₁le, hloss, G, S, hGf, hGne, hSf,
    hSne, hG4, hGsq, ?_, hS01, hfsep, hssep, ?_, ?_, ?_, ?_⟩
  · intro x ρ hρ
    have h := hSfr x ρ hρ
    have hρ0 : 0 ≤ ρ ^ β := Real.rpow_nonneg (hδ.le.trans hρ) _
    have hS0 : (0 : ℝ) ≤ S.ncard := Nat.cast_nonneg _
    calc _ ≤ K₁ * ρ ^ β * S.ncard := h
      _ ≤ K₁ * 2 ^ (1 + b) * ρ ^ β * S.ncard := by
        apply mul_le_mul_of_nonneg_right _ hS0
        exact mul_le_mul_of_nonneg_right hK₁le hρ0
  · rw [hαζ]; linarith
  · rw [hαζ]; linarith
  · rw [hζ2α]
    have hG0 : (0 : ℝ) ≤ G.ncard := Nat.cast_nonneg _
    calc δ ^ ζ * F ^ 2 ≤ δ ^ ζ * (K₁ * G.ncard) := mul_le_mul_of_nonneg_left hGbig hzpos.le
      _ = (δ ^ ζ * K₁) * G.ncard := by ring
      _ ≤ 1 * G.ncard := mul_le_mul_of_nonneg_right hK₁dz hG0
      _ = G.ncard := one_mul _
  · intro t ht
    obtain ⟨H, hHG, hHd, m, cc, hcc, hm⟩ := hH t ht
    refine ⟨H, hHG, ?_, m, cc, hcc, ?_⟩
    · have hH0 : (0 : ℝ) ≤ H.ncard := Nat.cast_nonneg _
      calc δ ^ ζ * G.ncard ≤ δ ^ ζ * (K₁ * H.ncard) := mul_le_mul_of_nonneg_left hHd hzpos.le
        _ = (δ ^ ζ * K₁) * H.ncard := by ring
        _ ≤ 1 * H.ncard := mul_le_mul_of_nonneg_right hK₁dz hH0
        _ = H.ncard := one_mul _
    · rw [hαζ2]; linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
