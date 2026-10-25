-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.Endpoints.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_estimate_equivalence.Starting
import Submission.WZ.Obl.wz_estimate_equivalence.Slab
import Submission.WZ.Obl.wz_endpoint_bootstrap

namespace WangZahlLot.Obl.wz_estimate_equivalence

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Moving away from zero cardinality exponent costs the same amount in scale exponent. -/
theorem d_pos_of_d_zero {s ω : ℝ} (hs : 0 ≤ s) (hD : D 0 ω) : D s (ω + s) := by
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := hD ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδmax n x v Y hn hv hT hsep hY hYT hdens hK hF
  have hold := h δ hδ hδmax n x v Y hn hv hT hsep hY hYT hdens hK hF
  simp only [neg_zero, Real.rpow_zero, mul_one] at hold
  refine (ENNReal.ofReal_le_ofReal ?_).trans hold
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : ((n : ℝ) * δ) ^ (-s) ≤ δ ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hδ (by nlinarith) (neg_nonpos.mpr hs)
  calc
    a * δ ^ ((ω + s) + ε) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-s) ≤
        a * δ ^ ((ω + s) + ε) * ((n : ℝ) * δ ^ 2) * δ ^ (-s) := by gcongr
    _ = a * (δ ^ ((ω + s) + ε) * δ ^ (-s)) * ((n : ℝ) * δ ^ 2) := by ring
    _ = a * δ ^ (ω + ε) * ((n : ℝ) * δ ^ 2) := by
      rw [← Real.rpow_add hδ, show (ω + s) + ε + -s = ω + ε by ring]

/-- Bounding the bracket after clamping the slab constant. -/
theorem clamped_bracket_le {δ m l C : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hm : 1 ≤ m) (hl : 0 ≤ l) (hlδ : l ≤ δ ^ (-3 : ℝ))
    (hpack : (n : ℝ) * δ ^ 6 ≤ C) :
    m ^ (-(3 / 2 : ℝ)) * l * ((n : ℝ) * δ) ≤ C * δ ^ (-8 : ℝ) := by
  have hmfac : m ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm (by norm_num)
  have hn : (n : ℝ) * δ ≤ C * δ ^ (-5 : ℝ) := by
    rw [Real.rpow_neg hδ.le, Real.rpow_ofNat, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hδ 5)).2
    convert hpack using 1
    ring
  calc
    m ^ (-(3 / 2 : ℝ)) * l * ((n : ℝ) * δ) ≤ 1 * (δ ^ (-3 : ℝ)) * ((n : ℝ) * δ) := by
      gcongr
    _ ≤ δ ^ (-3 : ℝ) * (C * δ ^ (-5 : ℝ)) := by rw [one_mul]; gcongr
    _ = C * δ ^ (-8 : ℝ) := by
      rw [mul_left_comm, ← Real.rpow_add hδ]
      norm_num

/-- A small positive cardinality exponent can be removed at a controlled scale cost. -/
theorem zero_sigma_coefficient_le {a C δ ω ε ε' s m N B : ℝ}
    (ha : 0 ≤ a) (hC : 1 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hm : 0 ≤ m) (hN : 0 ≤ N) (hB : 0 < B)
    (hbound : B ≤ C * δ ^ (-8 : ℝ)) (hε : 9 * s + ε' ≤ ε) :
    (a / C) * δ ^ (ω + ε) * m⁻¹ * N ≤
      a * δ ^ ((ω + s) + ε') * m⁻¹ * N * B ^ (-s) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCpow : C⁻¹ ≤ C ^ (-s) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  have hBpow : C⁻¹ * δ ^ (8 * s) ≤ B ^ (-s) := by
    calc
      C⁻¹ * δ ^ (8 * s) ≤ C ^ (-s) * δ ^ (8 * s) := by gcongr
      _ = (C * δ ^ (-8 : ℝ)) ^ (-s) := by
        rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
        congr 1
        congr 1
        ring
      _ ≤ B ^ (-s) := Real.rpow_le_rpow_of_nonpos hB hbound (neg_nonpos.mpr hs)
  have hscale : δ ^ (ω + ε) ≤ δ ^ ((ω + s) + ε') * δ ^ (8 * s) := by
    rw [← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  calc
    (a / C) * δ ^ (ω + ε) * m⁻¹ * N ≤
        (a / C) * (δ ^ ((ω + s) + ε') * δ ^ (8 * s)) * m⁻¹ * N := by gcongr
    _ = a * δ ^ ((ω + s) + ε') * m⁻¹ * N * (C⁻¹ * δ ^ (8 * s)) := by ring
    _ ≤ _ := by gcongr

/-- The positive-parameter implication suffices at `σ = 0`. -/
theorem e_zero_of_positive_implication
    (hpos : ∀ σ ω : ℝ, 0 < σ → σ ≤ 1 / 2 → 0 < ω → D σ ω → E σ ω)
    {ω : ℝ} (hω : 0 ≤ ω) (hD : D 0 ω) : E 0 ω := by
  intro ε hε
  let s : ℝ := min (1 / 2) (ε / 18)
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have hsmax : s ≤ 1 / 2 := min_le_left _ _
  have hsε : 9 * s + ε / 2 ≤ ε := by
    have : s ≤ ε / 18 := min_le_right _ _
    linarith
  have hE := hpos s (ω + s) hs hsmax (by linarith) (d_pos_of_d_zero hs.le hD)
  obtain ⟨a, ha, η, hη, h⟩ := hE (ε / 2) (by positivity)
  let C : ℝ := 160 ^ 6
  have hC : 1 ≤ C := by norm_num [C]
  refine ⟨a / C, div_pos ha (lt_of_lt_of_le zero_lt_one hC), η, hη, ?_⟩
  intro δ hδ hδmax m l hm hl n x v Y hn hv hT hsep hY hYT hdens hK hF
  let l' := min l (δ ^ (-3 : ℝ))
  have hδ1 : δ ≤ 1 := le_trans hδmax (by norm_num)
  have hl' : 1 ≤ l' := le_min hl
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by norm_num))
  have hF' : ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal ({i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        (Metric.ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r})}.ncard : ℝ) ≤
      ENNReal.ofReal (l' * (n : ℝ)) *
        volume (Metric.ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r}) := by
    intro u t r hu hr
    dsimp [l']
    rcases le_total l (δ ^ (-3 : ℝ)) with hle | hle
    · rw [min_eq_left hle]
      exact hF u t r hu hr
    · rw [min_eq_right hle]
      exact universal_volume_count hδ x v _
  have hbound := h δ hδ hδmax m l' hm hl' n x v Y hn hv hT hsep hY hYT hdens hK hF'
  simp only [neg_zero, Real.rpow_zero, mul_one]
  refine (ENNReal.ofReal_le_ofReal ?_).trans hbound
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl'0 : 0 < l' := lt_of_lt_of_le zero_lt_one hl'
  exact zero_sigma_coefficient_le ha.le hC hδ hδ1 hs.le (by linarith) hm0.le
    (by positivity) (by positivity)
    (clamped_bracket_le hδ hm hl'0.le (min_le_right _ _)
      (tube_card_bound hδ hδmax hv hT hsep)) hsε

/-- Extending the equivalence implication from positive parameters to both boundary faces. -/
theorem e_of_d_of_positive_implication
    (hpos : ∀ σ ω : ℝ, 0 < σ → σ ≤ 1 / 2 → 0 < ω → D σ ω → E σ ω)
    (σ ω : ℝ) (hσ : 0 ≤ σ) (hσmax : σ ≤ 1 / 2) (hω : 0 ≤ ω)
    (hD : D σ ω) : E σ ω := by
  rcases eq_or_lt_of_le hσ with hσzero | hσpos
  · subst σ
    exact e_zero_of_positive_implication hpos hω hD
  · apply e_of_forall_pos_add
    intro t ht
    exact hpos σ (ω + t) hσpos hσmax (by linarith)
      (WangZahlLot.Obl.wz_endpoint_bootstrap.Estimate.mono_omega (by linarith) hD)

end WangZahlLot.Obl.wz_estimate_equivalence
