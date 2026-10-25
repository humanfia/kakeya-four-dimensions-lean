-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.Numeric.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Parameter choice for the fibre dichotomy

For `0 < c < τ` and `h > 0` we choose `η₀` and `d₀` so that, for `0 < δ ≤ d₀` and
`0 ≤ η ≤ η₀`, the losses of the greedy extraction (`θ = δ^(2η)/6144`, slab threshold `δ^c ρ`,
logarithmic factor `1 + 320 K`) are absorbed by `δ^(-τ)` and by `δ^(5η) - δ^h`.
-/

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

/-- If `0 < δ ≤ A^(-1/p)` with `A, p > 0`, then `A ≤ δ^(-p)`. -/
lemma le_rpow_neg_of_le {δ A p : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hp : 0 < p)
    (h : δ ≤ A ^ (-(1 / p))) : A ≤ δ ^ (-p) := by
  have h1 : δ ^ p ≤ (A ^ (-(1 / p))) ^ p := Real.rpow_le_rpow hδ.le h hp.le
  rw [← Real.rpow_mul hA.le, show -(1 / p) * p = -1 by field_simp, Real.rpow_neg_one] at h1
  rw [Real.rpow_neg hδ.le]
  have hδp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ p
  rw [le_inv_comm₀ hA hδp]
  exact h1

lemma log_one_div_le {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    Real.log (1 / δ) ≤ δ ^ (-ε) / ε := by
  have h := Real.log_le_rpow_div (x := 1 / δ) (by positivity) hε
  rw [one_div] at h ⊢
  rwa [Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le] at h

theorem fd_numeric {τ c h : ℝ} (hτ : 0 < τ) (hc : 0 < c) (hcτ : c < τ) (hh : 0 < h) :
    ∃ η₀ d₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ η : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ η → η ≤ η₀ →
        384 ≤ δ ^ (-τ) ∧
        589824 * 6144 * δ ^ (-(c + 2 * η)) ≤ δ ^ (-τ) ∧
        4 * 6144 ^ 2 * (321 + 320 * (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2) *
          (δ ^ h + 2 * δ ^ τ) ≤ δ ^ (5 * η) := by
  set m₀ := min h τ with hm₀
  have hm₀pos : 0 < m₀ := lt_min hh hτ
  set ε := m₀ / 4 with hε
  have hεpos : 0 < ε := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog12 : 0 < Real.log 12288 := Real.log_pos (by norm_num)
  set Cε := 321 + 320 * Real.log 12288 / Real.log 2 + 960 / (ε * Real.log 2) with hCε
  have hCεpos : 0 < Cε := by positivity
  set A1 := 12 * 6144 ^ 2 * Cε with hA1
  have hA1pos : 0 < A1 := by positivity
  set A2 : ℝ := 589824 * 6144 with hA2
  have hA2pos : 0 < A2 := by positivity
  set η₀ := min (1 / 2) (min ((τ - c) / 4) (m₀ / 20)) with hη₀
  have hη₀pos : 0 < η₀ := lt_min (by norm_num) (lt_min (by linarith) (by positivity))
  set d₀ := min (1 / 100) (min (A1 ^ (-(1 / (m₀ / 2)))) (min (A2 ^ (-(1 / ((τ - c) / 2))))
    ((384 : ℝ) ^ (-(1 / τ))))) with hd₀
  have hd₀pos : 0 < d₀ := by
    apply lt_min (by norm_num)
    apply lt_min (Real.rpow_pos_of_pos hA1pos _)
    exact lt_min (Real.rpow_pos_of_pos hA2pos _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨η₀, d₀, hη₀pos, min_le_left _ _, hd₀pos, min_le_left _ _, ?_⟩
  intro δ η hδ hδd hη hηη₀
  have hδ1 : δ ≤ 1 := hδd.trans ((min_le_left _ _).trans (by norm_num))
  have hδA1 : δ ≤ A1 ^ (-(1 / (m₀ / 2))) :=
    hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδA2 : δ ≤ A2 ^ (-(1 / ((τ - c) / 2))) :=
    hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ384 : δ ≤ (384 : ℝ) ^ (-(1 / τ)) :=
    hδd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hη2 : η ≤ (τ - c) / 4 := hηη₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : η ≤ m₀ / 20 := hηη₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨le_rpow_neg_of_le hδ (by norm_num) hτ hδ384, ?_, ?_⟩
  · -- the below-slab constant
    have hA2le : A2 ≤ δ ^ (-((τ - c) / 2)) := le_rpow_neg_of_le hδ hA2pos (by linarith) hδA2
    have hexp : δ ^ (-((τ - c) / 2)) ≤ δ ^ (c + 2 * η - τ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hsplit : δ ^ (-τ) = δ ^ (c + 2 * η - τ) * δ ^ (-(c + 2 * η)) := by
      rw [← Real.rpow_add hδ]; ring_nf
    rw [hsplit]
    have hpos : 0 < δ ^ (-(c + 2 * η)) := Real.rpow_pos_of_pos hδ _
    exact mul_le_mul_of_nonneg_right (hA2le.trans hexp) hpos.le
  · -- the logarithmic loss
    have hlog : Real.log (1 / δ) ≤ δ ^ (-ε) / ε := log_one_div_le hδ hεpos
    have hδε : 1 ≤ δ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    have hL : 321 + 320 * (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2 ≤
        Cε * δ ^ (-ε) := by
      have e1 : 320 * (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2 ≤
          320 * Real.log 12288 / Real.log 2 + 960 / (ε * Real.log 2) * δ ^ (-ε) := by
        have : 320 * (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2 =
            320 * Real.log 12288 / Real.log 2 + 960 / Real.log 2 * Real.log (1 / δ) := by ring
        rw [this]
        have e2 : 960 / Real.log 2 * Real.log (1 / δ) ≤ 960 / Real.log 2 * (δ ^ (-ε) / ε) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        have e3 : 960 / Real.log 2 * (δ ^ (-ε) / ε) = 960 / (ε * Real.log 2) * δ ^ (-ε) := by
          field_simp
        linarith
      have e4 : (321 + 320 * Real.log 12288 / Real.log 2) * 1 ≤
          (321 + 320 * Real.log 12288 / Real.log 2) * δ ^ (-ε) :=
        mul_le_mul_of_nonneg_left hδε (by positivity)
      rw [hCε]
      nlinarith
    have hpow : δ ^ h + 2 * δ ^ τ ≤ 3 * δ ^ m₀ := by
      have e1 : δ ^ h ≤ δ ^ m₀ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)
      have e2 : δ ^ τ ≤ δ ^ m₀ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_right _ _)
      linarith
    have hA1le : A1 ≤ δ ^ (-(m₀ / 2)) := le_rpow_neg_of_le hδ hA1pos (by positivity) hδA1
    -- A1 * δ^(m₀/2) ≤ 1
    have hA1' : A1 * δ ^ (m₀ / 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hA1le (Real.rpow_pos_of_pos hδ (m₀ / 2)).le
      rwa [← Real.rpow_add hδ, show -(m₀ / 2) + m₀ / 2 = 0 by ring, Real.rpow_zero] at this
    have hfive : δ ^ (m₀ / 4) ≤ δ ^ (5 * η) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hsplit : δ ^ m₀ = δ ^ (m₀ / 2) * δ ^ ε * δ ^ (m₀ / 4) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, hε]; ring_nf
    have hεcancel : δ ^ (-ε) * δ ^ ε = 1 := by
      rw [← Real.rpow_add hδ]; simp
    have hpos1 : 0 ≤ δ ^ (m₀ / 2) := (Real.rpow_pos_of_pos hδ _).le
    have hpos2 : 0 ≤ δ ^ (m₀ / 4) := (Real.rpow_pos_of_pos hδ _).le
    have hpos3 : 0 ≤ δ ^ ε := (Real.rpow_pos_of_pos hδ _).le
    have hpos4 : 0 ≤ δ ^ (-ε) := (Real.rpow_pos_of_pos hδ _).le
    calc 4 * 6144 ^ 2 * (321 + 320 * (Real.log 12288 + 3 * Real.log (1 / δ)) / Real.log 2) *
          (δ ^ h + 2 * δ ^ τ)
        ≤ 4 * 6144 ^ 2 * (Cε * δ ^ (-ε)) * (3 * δ ^ m₀) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hL (by norm_num)) hpow
            (by positivity) (by positivity)
      _ = (A1 * δ ^ (m₀ / 2)) * (δ ^ (-ε) * δ ^ ε) * δ ^ (m₀ / 4) := by
          rw [hsplit, hA1]; ring
      _ ≤ 1 * 1 * δ ^ (m₀ / 4) := by
          rw [hεcancel]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA1' (by norm_num)) hpos2
      _ = δ ^ (m₀ / 4) := by ring
      _ ≤ δ ^ (5 * η) := hfive

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
