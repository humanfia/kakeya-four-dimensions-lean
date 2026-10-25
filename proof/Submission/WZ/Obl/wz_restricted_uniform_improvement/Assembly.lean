-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_restricted_uniform_improvement.Glue

/-!
# Assembly of `WangZahlLot.wz_restricted_uniform_improvement`

For a fixed current exponent `u > ω` the three cases (a sticky subfamily, a
large dense Frostman subfamily, neither) are exhaustive; the first is the
premise `A` with the packing count, the others are the two deep children.
The pointwise improvement is then made uniform by `Uniform.lean`.
-/

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement.Glue

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_endpoint_bootstrap WangZahlLot.Obl.wz_restricted_uniform_improvement

/-- A smaller constant and a larger scale exponent give a smaller target. -/
theorem target_le_target {a a' w w' δ m N σ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ha0 : 0 ≤ a) (ha : a ≤ a') (hw : w' ≤ w) (hm : 0 ≤ m) (hN : 0 ≤ N) :
    ENNReal.ofReal (a * δ ^ w * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ)) ≤
      ENNReal.ofReal (a' * δ ^ w' * m⁻¹ * (N * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ)) := by
  apply ENNReal.ofReal_le_ofReal
  have h1 : δ ^ w ≤ δ ^ w' := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hw
  have h2 : a * δ ^ w ≤ a' * δ ^ w' := mul_le_mul ha h1 (by positivity) (ha0.trans ha)
  have h3 : 0 ≤ m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ) := by positivity
  calc a * δ ^ w * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ)
      = (a * δ ^ w) * (m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ)) := by ring
    _ ≤ (a' * δ ^ w') * (m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ)) :=
      mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by ring

/-- `x ^ p ≤ max 1 x` for `0 ≤ x` and `0 ≤ p ≤ 1`. -/
theorem rpow_le_max_one {x p : ℝ} (hx : 0 ≤ x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    x ^ p ≤ max 1 x := by
  calc x ^ p ≤ (max 1 x) ^ p := Real.rpow_le_rpow hx (le_max_right _ _) hp0
    _ ≤ (max 1 x) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hp1
    _ = max 1 x := Real.rpow_one _

/-- The coefficient of the restricted target is bounded by an absolute constant
once the convex count on the unit ball and the packing count are known. -/
theorem sticky_coeff_le {σ δ m N V C : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hδ : 0 < δ)
    (hm : 1 ≤ m) (hN : 0 < N) (hV : 0 < V) (hC : 0 < C)
    (hK : N * δ ^ 2 ≤ m * V) (hP : N * δ ^ 4 ≤ C) :
    m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ) ≤ max 1 V * max 1 C := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have hA0 : 0 < N * δ ^ 2 := by positivity
  have hB0 : 0 < N * δ := by positivity
  set p : ℝ := 1 - 3 * σ / 2 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p ≤ 1 := by rw [hp]; linarith
  have e1 : (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ) = m ^ (3 * σ / 2) * (N * δ) ^ (-σ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hm0.le _) hB0.le, ← Real.rpow_mul hm0.le]
    congr 2
    ring
  have e2 : m⁻¹ * m ^ (3 * σ / 2) = m ^ (-p) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hm0]
    congr 1
    rw [hp]
    ring
  have eL : m⁻¹ * (N * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * (N * δ)) ^ (-σ) =
      m ^ (-p) * (N * δ ^ 2) * (N * δ) ^ (-σ) := by
    rw [e1, ← e2]
    ring
  have hAp : (N * δ ^ 2) ^ p ≤ m ^ p * V ^ p := by
    rw [← Real.mul_rpow hm0.le hV.le]
    exact Real.rpow_le_rpow hA0.le hK hp0.le
  have hsplit : N * δ ^ 2 = (N * δ ^ 2) ^ p * (N * δ ^ 2) ^ (1 - p) := by
    rw [← Real.rpow_add hA0]
    simp
  have h3 : m ^ (-p) * (N * δ ^ 2) ≤ V ^ p * (N * δ ^ 2) ^ (1 - p) := by
    have hmp : 0 < m ^ p := Real.rpow_pos_of_pos hm0 p
    calc m ^ (-p) * (N * δ ^ 2)
        = m ^ (-p) * ((N * δ ^ 2) ^ p * (N * δ ^ 2) ^ (1 - p)) := by rw [← hsplit]
      _ ≤ m ^ (-p) * ((m ^ p * V ^ p) * (N * δ ^ 2) ^ (1 - p)) := by gcongr
      _ = (m ^ (-p) * m ^ p) * V ^ p * (N * δ ^ 2) ^ (1 - p) := by ring
      _ = V ^ p * (N * δ ^ 2) ^ (1 - p) := by
        rw [Real.rpow_neg hm0.le, inv_mul_cancel₀ hmp.ne', one_mul]
  have h4 : (N * δ ^ 2) ^ (1 - p) * (N * δ) ^ (-σ) = (N * δ ^ 4) ^ (σ / 2) := by
    rw [Real.rpow_def_of_pos hA0, Real.rpow_def_of_pos hB0,
      Real.rpow_def_of_pos (by positivity : 0 < N * δ ^ 4), ← Real.exp_add]
    congr 1
    rw [Real.log_mul hN.ne' (by positivity), Real.log_mul hN.ne' hδ.ne',
      Real.log_mul hN.ne' (by positivity), Real.log_pow, Real.log_pow, hp]
    push_cast
    ring
  have h5 : (N * δ ^ 4) ^ (σ / 2) ≤ max 1 C :=
    (Real.rpow_le_rpow (by positivity) hP (by linarith)).trans
      (rpow_le_max_one hC.le (by linarith) (by linarith))
  have h6 : V ^ p ≤ max 1 V := rpow_le_max_one hV.le hp0.le hp1
  rw [eL]
  calc m ^ (-p) * (N * δ ^ 2) * (N * δ) ^ (-σ)
      ≤ V ^ p * (N * δ ^ 2) ^ (1 - p) * (N * δ) ^ (-σ) := by gcongr
    _ = V ^ p * (N * δ ^ 4) ^ (σ / 2) := by rw [mul_assoc, h4]
    _ ≤ max 1 V * max 1 C := mul_le_mul h6 h5 (by positivity) (by positivity)

/-- The convex count on the unit ball bounds the number of tubes. -/
theorem katz_ball {δ m : ℝ} {n : ℕ} {x v : Fin n → Space} (hδ : 0 < δ) (hm : 0 ≤ m)
    (hb : ∀ i, tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) (hK : Katz δ m x v) :
    (n : ℝ) * δ ^ 2 ≤ m * (volume (Metric.ball (0 : Space) 1)).toReal := by
  have hcount := hK (Metric.ball (0 : Space) 1) (convex_ball _ _)
  have hset : {i : Fin n | tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1} = Set.univ :=
    Set.eq_univ_of_forall hb
  rw [hset] at hcount
  simp only [Set.ncard_univ, Nat.card_fin] at hcount
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne) hcount
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (n : ℝ) * δ ^ 2),
    ENNReal.toReal_ofReal hm] using ht

/-- For a fixed current exponent `u > ω`, the three exhaustive cases give the
individually dense restricted estimate at `u - α`. -/
theorem individually_of_cases {σ ω u : ℝ} (hA : AllScalesVolume) (hσ : 0 < σ)
    (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hu : ω < u) (hD : Estimate σ ω) (hE : Full σ u) :
    ∃ α : ℝ, 0 < α ∧ α ≤ u / 2 ∧ IndividuallyRestricted σ (u - α) := by
  have hu0 : 0 < u := hω.trans hu
  obtain ⟨aA, haA, ηA, hηA, hAδ⟩ := hA (u / 2) (by positivity)
  obtain ⟨α₂, hα₂, ζ, hζ, h₂⟩ := frostman_case hA hσ hσ2 hω hu hD hE ηA hηA
  obtain ⟨α₃, hα₃, h₃⟩ := concentrated_case hσ hσ2 hω hu hD hE ζ hζ
  obtain ⟨C, hC, hpack⟩ := packing
  have hV : 0 < (volume (Metric.ball (0 : Space) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  set V : ℝ := (volume (Metric.ball (0 : Space) 1)).toReal with hVdef
  have hKc : 0 < max 1 V * max 1 C := by positivity
  have hα : 0 < min α₂ (min α₃ (u / 2)) := lt_min hα₂ (lt_min hα₃ (by positivity))
  refine ⟨min α₂ (min α₃ (u / 2)), hα, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro ε hε
  obtain ⟨a₂, ha₂, η₂, hη₂, h₂δ⟩ := h₂ ε hε
  obtain ⟨a₃, ha₃, η₃, hη₃, h₃δ⟩ := h₃ η₂ hη₂ ε hε
  refine ⟨min a₂ (min a₃ (aA / (max 1 V * max 1 C))),
    lt_min ha₂ (lt_min ha₃ (div_pos haA hKc)), min η₂ (min η₃ ηA),
    lt_min hη₂ (lt_min hη₃ hηA), ?_⟩
  intro δ hδ hδ1 m hm n x v Y hAd hind hK hF
  have hδ1' : δ ≤ 1 := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have hN : (0 : ℝ) < n := Nat.cast_pos.2 hAd.1
  have ha0 : 0 ≤ min a₂ (min a₃ (aA / (max 1 V * max 1 C))) :=
    (lt_min ha₂ (lt_min ha₃ (div_pos haA hKc))).le
  have hη₂le : min η₂ (min η₃ ηA) ≤ η₂ := min_le_left _ _
  have hη₃le : min η₂ (min η₃ ηA) ≤ η₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hηAle : min η₂ (min η₃ ηA) ≤ ηA := (min_le_right _ _).trans (min_le_right _ _)
  -- weakening the density and slab hypotheses to a larger exponent
  have hind' : ∀ η', min η₂ (min η₃ ηA) ≤ η' →
      ∀ i, ENNReal.ofReal (δ ^ η' * δ ^ 2) ≤ volume (Y i) := fun η' hη' i =>
    le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1' hη') (sq_nonneg δ))) (hind i)
  have hAd' : ∀ η', min η₂ (min η₃ ηA) ≤ η' → Admissible δ η' x v Y := fun η' hη' =>
    hAd.mono hδ hδ1' hη'
  have hF' : ∀ η', min η₂ (min η₃ ηA) ≤ η' → Frostman δ (δ ^ (-η')) x v := fun η' hη' =>
    hF.mono (Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (neg_le_neg hη'))
  by_cases hS : Sticky ηA δ n x v
  · -- Case 1: the premise `A` applies to a sticky subfamily.
    obtain ⟨k, g, hg, hk, hAS⟩ := hS
    let f : Fin k ↪ Fin n := ⟨g, hg⟩
    have hsubA : Admissible δ ηA (x ∘ f) (v ∘ f) (Y ∘ f) :=
      admissible_subfamily f hk hAd (dense_of_individual hδ.le fun j => hind' ηA hηAle (f j))
    have hvol := hAδ δ hδ hδ1 k (x ∘ f) (v ∘ f) (Y ∘ f) hsubA hAS
    refine le_trans ?_ (hvol.trans (measure_mono (subfamily_union_subset f Y)))
    apply ENNReal.ofReal_le_ofReal
    have hcoef := sticky_coeff_le hσ hσ2 hδ hm hN hV hC (katz_ball hδ hm0.le hAd.2.2.1 hK)
      (hpack δ hδ hδ1 n x v hAd.2.1 hAd.2.2.1 hAd.2.2.2.1)
    have hexp : δ ^ ((u - min α₂ (min α₃ (u / 2))) + ε) ≤ δ ^ (u / 2) := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1'
      have : min α₂ (min α₃ (u / 2)) ≤ u / 2 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have hacoef : min a₂ (min a₃ (aA / (max 1 V * max 1 C))) ≤ aA / (max 1 V * max 1 C) :=
      (min_le_right _ _).trans (min_le_right _ _)
    calc min a₂ (min a₃ (aA / (max 1 V * max 1 C))) * δ ^ ((u - min α₂ (min α₃ (u / 2))) + ε) *
          m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)
        = (min a₂ (min a₃ (aA / (max 1 V * max 1 C))) *
            δ ^ ((u - min α₂ (min α₃ (u / 2))) + ε)) *
          (m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * ((n : ℝ) * δ)) ^ (-σ)) := by ring
      _ ≤ (aA / (max 1 V * max 1 C) * δ ^ (u / 2)) * (max 1 V * max 1 C) :=
          mul_le_mul (mul_le_mul hacoef hexp (by positivity) (by positivity)) hcoef
            (by positivity) (by positivity)
      _ = aA * δ ^ (u / 2) := by field_simp
  · by_cases hFS : FrostSub η₂ ζ δ n x v
    · -- Case 2: a large Frostman subfamily, no sticky subfamily.
      have h := h₂δ δ hδ hδ1 m hm n x v Y (hAd' η₂ hη₂le) (hind' η₂ hη₂le) hK (hF' η₂ hη₂le)
        hS hFS
      refine le_trans (target_le_target hδ hδ1' ha0 (min_le_left _ _) ?_ hm0.le hN.le) h
      have : min α₂ (min α₃ (u / 2)) ≤ α₂ := min_le_left _ _
      linarith
    · -- Case 3: no large Frostman subfamily.
      have h := h₃δ δ hδ hδ1 m hm n x v Y (hAd' η₃ hη₃le) (hind' η₃ hη₃le) hK (hF' η₃ hη₃le)
        hFS
      refine le_trans (target_le_target hδ hδ1' ha0
        ((min_le_right _ _).trans (min_le_left _ _)) ?_ hm0.le hN.le) h
      have : min α₂ (min α₃ (u / 2)) ≤ α₃ := (min_le_right _ _).trans (min_le_left _ _)
      linarith

/-- The pointwise improvement, in the form consumed by `Bridge.lean`. -/
theorem pointwise_improvement : PointwiseImprovement := by
  intro σ ω u hA hσ hσ2 hω hu hD hE
  obtain ⟨α, hα, hαu, h⟩ := individually_of_cases hA hσ hσ2 hω hu hD hE
  refine ⟨α, hα, restricted_of_individually hσ.le (by linarith) ?_ h⟩
  have hu0 : 0 < u := hω.trans hu
  linarith

end WangZahlLot.Obl.wz_restricted_uniform_improvement.Glue
