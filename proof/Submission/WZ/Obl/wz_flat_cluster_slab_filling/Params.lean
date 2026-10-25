-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.Params.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Basic

/-!
The scalar bookkeeping of the proof of `WangZahlLot.wz_flat_cluster_slab_filling`: with the
parameters `lam = δ^a/768`, `τ = (δ^a'/6144)^(1/β)`, `θ = ρ τ`, `b = δ^(1 - min c 1 / 2)`,
`L = b/(32ρ)`, all the inequalities needed by `per_tube` and `crossing_exists` follow from
the smallness conditions of `numerics`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

/-- Pure numerical step of `params` (the inequality `hnum`), with the rpow quantities
abstracted. -/
lemma par_num {X Y Lg τ : ℝ} (hτ : 0 < τ)
    (N6 : Y * ((10 ^ 13 * 768 ^ 2 * 16 * 16000 ^ 2 : ℝ) * Lg) ≤ X ^ 3 * τ) :
    Y * (10 ^ 13 * (1 / τ) * Lg) ≤ (X / 768 / 16000) ^ 2 * (48 * (X / 768)) := by
  have hτne : τ ≠ 0 := hτ.ne'
  have key : Y * (10 ^ 13 * (1 / τ) * Lg) =
      (Y * ((10 ^ 13 * 768 ^ 2 * 16 * 16000 ^ 2 : ℝ) * Lg)) /
        (τ * (768 ^ 2 * 16 * 16000 ^ 2)) := by
    field_simp
  have key2 : (X / 768 / 16000) ^ 2 * (48 * (X / 768)) =
      X ^ 3 * τ / (τ * (768 ^ 2 * 16 * 16000 ^ 2)) := by
    field_simp
    ring
  rw [key, key2]
  exact div_le_div_of_nonneg_right N6 (by positivity)

/-- The polynomial part of `params`, with the rpow quantities abstracted:
`P = δ^c`, `R = δ^(1-c)`, `Q = δ^(c - c')`, `D = δ^c'`, `b = δ^(1-c')`. -/
lemma par_poly {δ r ρ P R Q D b τ θ L : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hδr : δ ≤ r) (hrρ : r ≤ P * ρ) (hρ1 : ρ ≤ 1)
    (hP : 0 < P) (hP16 : P ≤ 1 / 16) (hRP : R * P = δ) (hQ1 : Q ≤ 1)
    (hb0 : 0 < b) (hbRQ : b = R * Q) (hbD : b * D = δ) (hD96 : D ≤ 1 / 96)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hPτ : P ≤ τ) (hτ32 : 32 * P ≤ τ)
    (hθ : θ = ρ * τ) (hL : L = b / (32 * ρ)) :
    0 < ρ ∧ 0 < θ ∧ θ ≤ 1 ∧ δ ≤ θ ∧ θ ≤ ρ ∧ 0 < L ∧ 3 * δ ≤ L ∧ 1 / 2 + δ + L ≤ 1 ∧
      2 * δ ≤ b ∧ b = 32 * ρ * L ∧ 32 * r ≤ θ ∧
      3 * δ + 8 * r * (L + 2 * δ) ≤ 5 * δ ∧ 3 * δ + 8 * ρ * (L + 2 * δ) ≤ b / 2 := by
  have hPρ : 0 < P * ρ := by linarith
  have hρpos : 0 < ρ := pos_of_mul_pos_right hPρ hP.le
  have hρne : ρ ≠ 0 := hρpos.ne'
  have hR : 0 < R := by
    have : 0 < R * P := by rw [hRP]; exact hδ
    exact pos_of_mul_pos_left this hP.le
  have hRρ : R ≤ ρ := by
    have h1 : R * P ≤ ρ * P := by rw [hRP, mul_comm ρ P]; linarith
    exact le_of_mul_le_mul_right h1 hP
  have hbρ : b ≤ ρ := by
    rw [hbRQ]
    calc R * Q ≤ R * 1 := mul_le_mul_of_nonneg_left hQ1 hR.le
      _ = R := mul_one R
      _ ≤ ρ := hRρ
  have h96 : 96 * δ ≤ b := by
    have : b * D ≤ b * (1 / 96) := mul_le_mul_of_nonneg_left hD96 hb0.le
    linarith
  have hθpos : 0 < θ := by rw [hθ]; exact mul_pos hρpos hτ0
  have hθρ : θ ≤ ρ := by
    rw [hθ]
    calc ρ * τ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hτ1 hρpos.le
      _ = ρ := mul_one ρ
  have hθ1 : θ ≤ 1 := le_trans hθρ hρ1
  have hδθ : δ ≤ θ := by
    rw [hθ, ← hRP]
    exact mul_le_mul hRρ hPτ hP.le hρpos.le
  have h32rθ : 32 * r ≤ θ := by
    rw [hθ]
    have h1 : 32 * P * ρ ≤ τ * ρ := mul_le_mul_of_nonneg_right hτ32 hρpos.le
    linarith
  have h32L : 32 * ρ * L = b := by rw [hL]; field_simp
  have hLpos : 0 < L := by rw [hL]; positivity
  have h3δL : 3 * δ ≤ L := by
    have h1 : ρ * L ≤ 1 * L := mul_le_mul_of_nonneg_right hρ1 hLpos.le
    linarith
  have hL32 : L ≤ 1 / 32 := by
    have h1 : ρ * L ≤ ρ * (1 / 32) := by linarith
    exact le_of_mul_le_mul_left h1 hρpos
  have hrL : 8 * r * L ≤ δ / 4 := by
    have h1 : r * L ≤ (P * ρ) * L := mul_le_mul_of_nonneg_right hrρ hLpos.le
    have h2 : (P * ρ) * L = δ * Q / 32 := by
      linear_combination (P / 32) * h32L + (P / 32) * hbRQ + (Q / 32) * hRP
    have h3 : δ * Q ≤ δ * 1 := mul_le_mul_of_nonneg_left hQ1 hδ.le
    linarith
  refine ⟨hρpos, hθpos, hθ1, hδθ, hθρ, hLpos, h3δL, ?_, ?_, h32L.symm, h32rθ, ?_, ?_⟩
  · linarith
  · linarith
  · -- `3δ + 8 r (L + 2δ) ≤ 5δ`
    have h1 : P * ρ ≤ P * 1 := mul_le_mul_of_nonneg_left hρ1 hP.le
    have hr16 : r ≤ 1 / 16 :=
      calc r ≤ P * ρ := hrρ
        _ ≤ P * 1 := h1
        _ = P := mul_one P
        _ ≤ 1 / 16 := hP16
    have h2 : r * δ ≤ (1 / 16) * δ := mul_le_mul_of_nonneg_right hr16 hδ.le
    linarith
  · -- `3δ + 8ρ(L+2δ) ≤ b/2`
    have h1 : ρ * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hρ1 hδ.le
    linarith

lemma params {β c e δ η ρ r a a' lam τ θ b L : ℝ} (hβ : 0 < β) (hc : 0 < c) (he : 0 < e)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hη : 0 < η)
    (hδr : δ ≤ r) (hrρ : r ≤ δ ^ c * ρ) (hρ1 : ρ ≤ 1)
    (ha : a = min e c * min β 1 / 20 + η) (ha' : a' = min e c * min β 1 / 20 + 2 * η)
    (hlam : lam = δ ^ a / 768) (hτ : τ = (δ ^ a' / 6144) ^ (1 / β)) (hθ : θ = ρ * τ)
    (hb : b = δ ^ (1 - min c 1 / 2)) (hL : L = b / (32 * ρ))
    (N2 : δ ^ (c * β) ≤ δ ^ a' / 6144)
    (N3 : (32 * δ ^ c) ^ β ≤ δ ^ a' / 6144)
    (N4 : δ ^ c ≤ 1 / 16)
    (N5 : δ ^ (min c 1 / 2) ≤ 1 / 96)
    (N6 : δ ^ e * ((10 ^ 13 * 768 ^ 2 * 16 * 16000 ^ 2 : ℝ) * (1 + Real.log (1 / δ))) ≤
          δ ^ (3 * a) * (δ ^ a' / 6144) ^ (1 / β)) :
    0 < ρ ∧ 0 < θ ∧ θ ≤ 1 ∧ δ ≤ θ ∧ θ ≤ ρ ∧ 0 < L ∧ 3 * δ ≤ L ∧ 1 / 2 + δ + L ≤ 1 ∧
      2 * δ ≤ b ∧ b ≤ 1 ∧ b = 32 * ρ * L ∧ 32 * r ≤ θ ∧
      3 * δ + 8 * r * (L + 2 * δ) ≤ 5 * δ ∧ 3 * δ + 8 * ρ * (L + 2 * δ) ≤ b / 2 ∧
      δ ^ (-η) * (θ / ρ) ^ β ≤ lam / 4 / 2 ∧
      δ ^ e * (10 ^ 13 * (ρ / θ) * (1 + Real.log (1 / δ))) ≤
        (lam / 16000) ^ 2 * (48 * lam) := by
  -- basic facts on `δ`
  have hδ0 : (0 : ℝ) ≤ δ := hδ.le
  have hδle1 : δ ≤ 1 := by linarith
  -- exponents
  have hmc_le_c : min c 1 ≤ c := min_le_left _ _
  have hmc_le_1 : min c 1 ≤ 1 := min_le_right _ _
  have hmc_pos : 0 < min c 1 := lt_min hc one_pos
  have hε : 0 < min e c * min β 1 / 20 := by
    have h1 : 0 < min e c := lt_min he hc
    have h2 : 0 < min β 1 := lt_min hβ one_pos
    positivity
  have ha'pos : 0 < a' := by rw [ha']; linarith
  have ha'η : -η + a' = a := by rw [ha, ha']; ring
  -- rpow quantities
  have hP : 0 < δ ^ c := Real.rpow_pos_of_pos hδ c
  have hRP : δ ^ (1 - c) * δ ^ c = δ := by
    rw [← Real.rpow_add hδ, sub_add_cancel, Real.rpow_one]
  have hbD : b * δ ^ (min c 1 / 2) = δ := by
    rw [hb, ← Real.rpow_add hδ, sub_add_cancel, Real.rpow_one]
  have hQ1 : δ ^ (c - min c 1 / 2) ≤ 1 := Real.rpow_le_one hδ0 hδle1 (by linarith)
  have hbRQ : b = δ ^ (1 - c) * δ ^ (c - min c 1 / 2) := by
    rw [hb, ← Real.rpow_add hδ]
    congr 1
    ring
  have hbpos : 0 < b := by rw [hb]; exact Real.rpow_pos_of_pos hδ _
  have hb1 : b ≤ 1 := by rw [hb]; exact Real.rpow_le_one hδ0 hδle1 (by linarith)
  -- `τ`
  have hBpos : 0 < δ ^ a' / 6144 := by
    have : 0 < δ ^ a' := Real.rpow_pos_of_pos hδ a'
    positivity
  have hB1 : δ ^ a' / 6144 ≤ 1 := by
    have : δ ^ a' ≤ 1 := Real.rpow_le_one hδ0 hδle1 ha'pos.le
    linarith
  have hβne : β ≠ 0 := hβ.ne'
  have hβinv : 0 ≤ 1 / β := by positivity
  have hτpos : 0 < τ := by rw [hτ]; exact Real.rpow_pos_of_pos hBpos _
  have hτ1 : τ ≤ 1 := by
    rw [hτ]; exact Real.rpow_le_one hBpos.le hB1 hβinv
  have hτc : δ ^ c ≤ τ := by
    have h1 : (δ ^ (c * β)) ^ (1 / β) ≤ τ := by
      rw [hτ]; exact Real.rpow_le_rpow (Real.rpow_pos_of_pos hδ _).le N2 hβinv
    have h2 : (δ ^ (c * β)) ^ (1 / β) = δ ^ c := by
      rw [← Real.rpow_mul hδ0]
      congr 1
      field_simp
    rw [h2] at h1
    exact h1
  have hτ32 : 32 * δ ^ c ≤ τ := by
    have h0 : (0 : ℝ) ≤ 32 * δ ^ c := by positivity
    have h1 : ((32 * δ ^ c) ^ β) ^ (1 / β) ≤ τ := by
      rw [hτ]; exact Real.rpow_le_rpow (Real.rpow_nonneg h0 β) N3 hβinv
    have h2 : ((32 * δ ^ c) ^ β) ^ (1 / β) = 32 * δ ^ c := by
      rw [one_div]; exact Real.rpow_rpow_inv h0 hβne
    rw [h2] at h1
    exact h1
  have hτβ : τ ^ β = δ ^ a' / 6144 := by
    rw [hτ, one_div]; exact Real.rpow_inv_rpow hBpos.le hβne
  obtain ⟨hρpos, hθpos, hθ1, hδθ, hθρ, hLpos, h3δL, h8, h9, h11, h12, h13, h14⟩ :=
    par_poly hδ hδ1 hδr hrρ hρ1 hP N4 hRP hQ1 hbpos hbRQ hbD N5 hτpos hτ1 hτc hτ32 hθ hL
  refine ⟨hρpos, hθpos, hθ1, hδθ, hθρ, hLpos, h3δL, h8, h9, hb1, h11, h12, h13, h14, ?_, ?_⟩
  · -- the smallness condition
    have hθρτ : θ / ρ = τ := by
      rw [hθ]; exact mul_div_cancel_left₀ τ hρpos.ne'
    rw [hθρτ, hτβ, hlam, ← ha'η, Real.rpow_add hδ]
    apply le_of_eq
    ring
  · -- the numerical condition
    have hρθ : ρ / θ = 1 / τ := by
      rw [hθ, div_mul_eq_div_div, div_self hρpos.ne']
    have h3a : (δ ^ a) ^ 3 = δ ^ (3 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0]
      congr 1
      push_cast
      ring
    rw [← hτ, ← h3a] at N6
    rw [hρθ, hlam]
    exact par_num hτpos N6

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
