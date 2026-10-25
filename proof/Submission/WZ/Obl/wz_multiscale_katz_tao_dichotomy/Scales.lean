-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy.Scales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_katz_tao_dichotomy.Basic

namespace WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya

/-- A balanced cover at a specified radius, with the error used in the conclusion. -/
def HasKatzTaoCover (δ ε : ℝ) {n : ℕ} (x v : Fin n → Space) (ρ : ℝ) : Prop :=
  ∃ (N : ℕ) (y w : Fin N → Space) (f : Fin n → Fin N),
    (∀ k, ‖w k‖ = 1) ∧
    (∀ j, Tube δ (x j) (v j) ⊆ Tube ρ (y (f j)) (w (f j))) ∧
    (∀ k k', ({j | f j = k}.ncard : ℝ) ≤ δ ^ (-ε) * {j | f j = k'}.ncard) ∧
    KatzTao ρ (δ ^ (-ε)) y w

def KatzTaoEveryScale (δ ε : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 →
    ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ < δ ^ (-ε) * ρ₀ ∧ HasKatzTaoCover δ ε x v ρ

theorem HasKatzTaoCover.mono {δ ε ε' ρ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : HasKatzTaoCover δ ε x v ρ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : ε ≤ ε') : HasKatzTaoCover δ ε' x v ρ := by
  obtain ⟨N, y, w, f, hw, hf, hb, hK⟩ := h
  have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hε)
  refine ⟨N, y, w, f, hw, hf, ?_, hK.mono hp⟩
  intro k k'
  exact (hb k k').trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))

theorem KatzTaoEveryScale.mono {δ ε ε' : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : KatzTaoEveryScale δ ε x v) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : ε ≤ ε') : KatzTaoEveryScale δ ε' x v := by
  intro ρ₀ hρ₀ hρ₁
  obtain ⟨ρ, hρ, hρ', hc⟩ := h ρ₀ hρ₀ hρ₁
  refine ⟨ρ, hρ, hρ'.trans_le ?_, hc.mono hδ hδ1 hε⟩
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hε)) (hδ.le.trans hρ₀)

/-- A finite chain with small adjacent gaps meets every required scale interval.
No monotonicity of the list is needed: use the last index above the target scale. -/
theorem exists_scale_of_adjacent_gaps {δ ε θ ρ₀ : ℝ} {J : ℕ} (r : ℕ → ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hθε : θ < ε)
    (hr0 : r 0 = 1) (hrJ : r J = δ)
    (hgap : ∀ i < J, r i ≤ δ ^ (-θ) * r (i + 1))
    (hρ₀ : δ ≤ ρ₀) (hρ₁ : ρ₀ ≤ 1) :
    ∃ i ≤ J, ρ₀ ≤ r i ∧ r i < δ ^ (-ε) * ρ₀ := by
  classical
  let S := (Finset.range (J + 1)).filter (fun i => ρ₀ ≤ r i)
  have hS : S.Nonempty := ⟨0, by simp [S, hr0, hρ₁]⟩
  let k := S.max' hS
  have hk : k ∈ S := Finset.max'_mem S hS
  have hkJ : k ≤ J := by
    have := (Finset.mem_filter.mp hk).1
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using this
  have hkρ : ρ₀ ≤ r k := (Finset.mem_filter.mp hk).2
  refine ⟨k, hkJ, hkρ, ?_⟩
  by_cases hkJ' : k = J
  · have heq : r k = ρ₀ := le_antisymm (by simpa [hkJ', hrJ] using hρ₀) hkρ
    rw [heq]
    exact lt_mul_of_one_lt_left (hδ.trans_le hρ₀)
      (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hδ hδ1 (neg_neg_of_pos hε))
  · have hklt : k < J := lt_of_le_of_ne hkJ hkJ'
    have hnext : r (k + 1) < ρ₀ := by
      by_contra hn
      have hn' : k + 1 ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, le_of_not_gt hn⟩
      have := Finset.le_max' S (k + 1) hn'
      change k + 1 ≤ k at this
      omega
    calc
      r k ≤ δ ^ (-θ) * r (k + 1) := hgap k hklt
      _ < δ ^ (-θ) * ρ₀ :=
        mul_lt_mul_of_pos_left hnext (Real.rpow_pos_of_pos hδ _)
      _ ≤ δ ^ (-ε) * ρ₀ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)) (hδ.le.trans hρ₀)

/-- The final scale-selection step in Lemma 11.2. -/
theorem KatzTaoEveryScale.of_chain {δ ε θ : ℝ} {n J : ℕ}
    {x v : Fin n → Space} (r : ℕ → ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hθε : θ < ε)
    (hr0 : r 0 = 1) (hrJ : r J = δ)
    (hgap : ∀ i < J, r i ≤ δ ^ (-θ) * r (i + 1))
    (hc : ∀ i ≤ J, HasKatzTaoCover δ ε x v (r i)) :
    KatzTaoEveryScale δ ε x v := by
  intro ρ₀ hρ₀ hρ₁
  obtain ⟨i, hi, hri, hri'⟩ :=
    exists_scale_of_adjacent_gaps r hδ hδ1 hε hθε hr0 hrJ hgap hρ₀ hρ₁
  exact ⟨r i, hri, hri', hc i hi⟩

/-- Scale-halving eventually makes the exponent of every gap smaller than the budget. -/
theorem exists_depth {ω ε : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) (hε : 0 < ε) :
    ∃ N : ℕ, (1 - ω / 100) ^ N < ε := by
  exact exists_pow_lt_of_lt_one hε (by linarith : (1 - ω / 100 : ℝ) < 1)

end WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy
