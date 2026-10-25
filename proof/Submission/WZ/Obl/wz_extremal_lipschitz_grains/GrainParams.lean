-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainParams.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainStructure

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **Lower bound for the balanced density**: the contracted fine set fills the coarse union with
density at most `δ^(-ε) θ`, so `θ` is at least the fine volume over the coarse volume. -/
theorem balance_density_lower {n k : ℕ} {Y1 : Fin n → Set Space} {M : Fin k → Finset (Fin 3 → ℤ)}
    {a : Fin n → Fin k} {s lam ε δ θb ρc σ μhi mass : ℝ} (hs : 0 < s) (hlam : 0 < lam)
    (hδ : 0 < δ) (hρc : 0 < ρc)
    (hY1m : ∀ i, MeasurableSet (Y1 i))
    (hcontr : ∀ i, lam • Y1 i ⊆ cubeSet s (M (a i)))
    (hbal : ∀ j, ∀ m ∈ M j, volume ((⋃ i, lam • Y1 i) ∩ gridCube s m) ≤
      ENNReal.ofReal (δ ^ (-ε) * θb) * volume (gridCube s m))
    (hvol : volume (⋃ j, cubeSet s (M j)) ≤ ENNReal.ofReal (ρc ^ (σ - ε)))
    (hμhi : ∀ p, (fineMult Y1 p : ℝ) ≤ μhi) (hμ : 0 < μhi)
    (hmass : ENNReal.ofReal mass ≤ ∑ i, volume (Y1 i)) (hθb : 0 ≤ θb) :
    lam ^ 3 * (mass / μhi) ≤ δ ^ (-ε) * θb * ρc ^ (σ - ε) := by
  classical
  have hE1m : MeasurableSet (⋃ i, Y1 i) := MeasurableSet.iUnion hY1m
  -- the fine volume
  have h1 : ENNReal.ofReal mass ≤ ENNReal.ofReal μhi * volume (⋃ i, Y1 i) := by
    have := massMeasure_le_mul hY1m hμhi hE1m
    rw [massMeasure_apply hY1m hE1m] at this
    have e : ∀ i, Y1 i ∩ ⋃ j, Y1 j = Y1 i := fun i => inter_eq_left.2 (subset_iUnion Y1 i)
    simp only [e, inter_self] at this
    exact hmass.trans this
  -- the contracted fine set lies in the coarse cubes
  set U := Finset.univ.biUnion M with hU
  have hsub : (⋃ i, lam • Y1 i) ⊆ ⋃ m ∈ U, gridCube s m := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy
    obtain ⟨m, hm, hym⟩ := mem_iUnion₂.1 (hcontr i hi)
    exact mem_iUnion₂.2 ⟨m, Finset.mem_biUnion.2 ⟨a i, Finset.mem_univ _, hm⟩, hym⟩
  have hcoarse : volume (⋃ m ∈ U, gridCube s m) = (U.card : ℝ≥0∞) * ENNReal.ofReal s ^ 3 := by
    rw [measure_biUnion_finset (fun m _ m' _ hmm => gridCube_disjoint hs hmm)
      (fun m _ => measurableSet_gridCube s m)]
    simp only [volume_gridCube hs, Finset.sum_const, nsmul_eq_mul]
  have hUsub : (⋃ m ∈ U, gridCube s m) ⊆ ⋃ j, cubeSet s (M j) := by
    intro y hy
    obtain ⟨m, hm, hym⟩ := mem_iUnion₂.1 hy
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hm
    exact mem_iUnion.2 ⟨j, mem_iUnion₂.2 ⟨m, hj, hym⟩⟩
  have h2 : volume (⋃ i, lam • Y1 i) ≤
      ENNReal.ofReal (δ ^ (-ε) * θb) * volume (⋃ j, cubeSet s (M j)) := by
    calc volume (⋃ i, lam • Y1 i) ≤ volume (⋃ m ∈ U, (⋃ i, lam • Y1 i) ∩ gridCube s m) := by
          apply measure_mono
          intro y hy
          obtain ⟨m, hm, hym⟩ := mem_iUnion₂.1 (hsub hy)
          exact mem_iUnion₂.2 ⟨m, hm, hy, hym⟩
      _ ≤ ∑ m ∈ U, volume ((⋃ i, lam • Y1 i) ∩ gridCube s m) := measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ U, ENNReal.ofReal (δ ^ (-ε) * θb) * volume (gridCube s m) := by
          apply Finset.sum_le_sum
          intro m hm
          obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hm
          exact hbal j m hj
      _ = ENNReal.ofReal (δ ^ (-ε) * θb) * volume (⋃ m ∈ U, gridCube s m) := by
          rw [← Finset.mul_sum, measure_biUnion_finset (fun m _ m' _ hmm =>
            gridCube_disjoint hs hmm) (fun m _ => measurableSet_gridCube s m)]
      _ ≤ _ := by gcongr
  -- scaling
  have h3 : volume (⋃ i, lam • Y1 i) = ENNReal.ofReal (lam ^ 3) * volume (⋃ i, Y1 i) := by
    rw [← Set.smul_set_iUnion, Measure.addHaar_smul, finrank_euclideanSpace, Fintype.card_fin,
      abs_of_pos (by positivity)]
  -- combine
  have hfinE : volume (⋃ i, Y1 i) ≠ ∞ := by
    intro htop
    have h := h3 ▸ h2
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne'] at h
    exact (lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt hvol ENNReal.ofReal_lt_top))).ne rfl
  set X := (volume (⋃ i, Y1 i)).toReal with hX
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hEX : volume (⋃ i, Y1 i) = ENNReal.ofReal X := (ENNReal.ofReal_toReal hfinE).symm
  rw [hEX] at h1 h3
  rw [h3] at h2
  have h4 : ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal X ≤
      ENNReal.ofReal (δ ^ (-ε) * θb) * ENNReal.ofReal (ρc ^ (σ - ε)) := h2.trans (by gcongr)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at h4
  have h5 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4
  rw [← ENNReal.ofReal_mul hμ.le] at h1
  have h6 : mass ≤ μhi * X := by
    rcases le_or_gt mass 0 with hm0 | hm0
    · nlinarith
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have h7 : mass / μhi ≤ X := by rw [div_le_iff₀ hμ]; linarith
  calc lam ^ 3 * (mass / μhi) ≤ lam ^ 3 * X := mul_le_mul_of_nonneg_left h7 (by positivity)
    _ ≤ _ := h5

/-- **Arithmetic of the grain window bound.** -/
theorem grain_arith {δ ρ ρc r R g H0 A W U mf σ εc e1 e2 C2 : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : δ ≤ ρ) (hρc : ρ ≤ ρc) (hρc1 : ρc ≤ 1) (hr : δ ≤ r)
    (hR : ρ ≤ R) (hg : 1 ≤ g) (hσ : 0 < σ) (hσ1 : σ < 1) (he1 : 0 ≤ e1)
    (he2 : 0 ≤ e2) (hεc : 0 ≤ εc) (hεc1 : εc ≤ 1) (hC2 : 0 < C2)
    (hA : 0 ≤ A) (hA8 : A ≤ 8 * g * Real.sqrt ρ) (hW : 0 ≤ W) (hW3 : W ≤ 3 * r)
    (hU : 0 ≤ U) (hUb : U ≤ 54880000 * g ^ 4 * r ^ (3 - σ - εc) * δ ^ (σ - 2 * εc))
    (hmf : δ ^ (σ + e1) * ρ * ρc ^ (1 - σ + e2) / C2 ≤ mf)
    (hrR : r ≤ g * H0 * R) (hH01 : 1 ≤ H0) :
    (8 * (2 * A) ^ 2 * W / r ^ 3 * U) / mf * H0 ≤
      (6144 * 54880000 * C2) * g ^ 7 * H0 ^ 2 * δ ^ (-(3 * εc + e1 + e2)) * (R / ρ) ^ (1 - σ) := by
  have hρ0 : 0 < ρ := hδ.trans_le hρ
  have hρc0 : 0 < ρc := hρ0.trans_le hρc
  have hr0 : 0 < r := hδ.trans_le hr
  have hR0 : 0 < R := hρ0.trans_le hR
  have hg0 : 0 < g := by linarith
  -- the geometric factor
  have hA2 : A ^ 2 ≤ 64 * g ^ 2 * ρ := by
    have h1 : A ^ 2 ≤ (8 * g * Real.sqrt ρ) ^ 2 := pow_le_pow_left₀ hA hA8 2
    rw [mul_pow, Real.sq_sqrt hρ0.le] at h1
    nlinarith
  have hgeo : 8 * (2 * A) ^ 2 * W / r ^ 3 ≤ 6144 * g ^ 2 * ρ / r ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 8 * (2 * A) ^ 2 * W ≤ 8 * (4 * (64 * g ^ 2 * ρ)) * (3 * r) := by
      have : (2 * A) ^ 2 = 4 * A ^ 2 := by ring
      rw [this]
      apply mul_le_mul (by nlinarith) hW3 hW (by positivity)
    calc 8 * (2 * A) ^ 2 * W * r ^ 2 ≤ 8 * (4 * (64 * g ^ 2 * ρ)) * (3 * r) * r ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 6144 * g ^ 2 * ρ * r ^ 3 := by ring
  -- powers of `r`, `ρc` and `δ`
  have hrpow : r ^ (3 - σ - εc) / r ^ 2 ≤ r ^ (1 - σ) * δ ^ (-εc) := by
    have e : r ^ (3 - σ - εc) / r ^ 2 = r ^ (1 - σ) * r ^ (-εc) := by
      rw [show r ^ 2 = r ^ (2 : ℝ) by norm_cast, ← Real.rpow_sub hr0, ← Real.rpow_add hr0]
      ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hδ hr (by linarith))
      (by positivity)
  have hρcpow : ρc ^ (1 - σ + e2) ≥ ρ ^ (1 - σ) * δ ^ e2 := by
    rw [Real.rpow_add hρc0]
    apply mul_le_mul (Real.rpow_le_rpow hρ0.le hρc (by linarith))
      (Real.rpow_le_rpow hδ.le (hρ.trans hρc) he2) (by positivity) (by positivity)
  -- the main quotient
  set num := 8 * (2 * A) ^ 2 * W / r ^ 3 * U with hnum
  have hnum0 : 0 ≤ num := by positivity
  have hnumb : num ≤ 6144 * 54880000 * g ^ 6 * ρ * (r ^ (1 - σ) * δ ^ (-εc)) *
      δ ^ (σ - 2 * εc) := by
    calc num ≤ 6144 * g ^ 2 * ρ / r ^ 2 * (54880000 * g ^ 4 * r ^ (3 - σ - εc) *
          δ ^ (σ - 2 * εc)) := mul_le_mul hgeo hUb hU (by positivity)
      _ = 6144 * 54880000 * g ^ 6 * ρ * (r ^ (3 - σ - εc) / r ^ 2) * δ ^ (σ - 2 * εc) := by
          ring
      _ ≤ _ := by gcongr
  have hm0 : 0 < δ ^ (σ + e1) * ρ * ρc ^ (1 - σ + e2) / C2 := by positivity
  have hmf0 : 0 < mf := hm0.trans_le hmf
  have hq : num / mf ≤ num / (δ ^ (σ + e1) * ρ * ρc ^ (1 - σ + e2) / C2) :=
    div_le_div_of_nonneg_left hnum0 hm0 hmf
  have hq2 : num / (δ ^ (σ + e1) * ρ * ρc ^ (1 - σ + e2) / C2) ≤
      6144 * 54880000 * C2 * g ^ 6 * (r / ρ) ^ (1 - σ) * δ ^ (-(3 * εc + e1 + e2)) := by
    rw [div_le_iff₀ hm0]
    refine hnumb.trans (le_of_eq_of_le rfl ?_)
    -- rearrange powers
    have e1' : δ ^ (σ - 2 * εc) = δ ^ (-(3 * εc + e1 + e2)) * δ ^ (σ + e1) * δ ^ e2 *
        δ ^ εc := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
    have e2' : (r / ρ) ^ (1 - σ) * ρ ^ (1 - σ) = r ^ (1 - σ) := by
      rw [Real.div_rpow hr0.le hρ0.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hρ0 _).ne']
    have e3' : δ ^ (-εc) * δ ^ εc = 1 := by
      rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
    have hpos : 0 ≤ 6144 * 54880000 * C2 * g ^ 6 * (r / ρ) ^ (1 - σ) *
        δ ^ (-(3 * εc + e1 + e2)) * δ ^ (σ + e1) * ρ := by positivity
    calc 6144 * 54880000 * g ^ 6 * ρ * (r ^ (1 - σ) * δ ^ (-εc)) * δ ^ (σ - 2 * εc)
        = 6144 * 54880000 * C2 * g ^ 6 * (r / ρ) ^ (1 - σ) * δ ^ (-(3 * εc + e1 + e2)) *
            δ ^ (σ + e1) * ρ * (ρ ^ (1 - σ) * δ ^ e2) / C2 := by
          rw [e1', ← e2']
          field_simp
          rw [show δ ^ (-εc) * δ ^ εc = 1 from e3'] at *
      _ ≤ 6144 * 54880000 * C2 * g ^ 6 * (r / ρ) ^ (1 - σ) * δ ^ (-(3 * εc + e1 + e2)) *
            (δ ^ (σ + e1) * ρ * ρc ^ (1 - σ + e2) / C2) := by
          set Y0 := 6144 * 54880000 * C2 * g ^ 6 * (r / ρ) ^ (1 - σ) *
            δ ^ (-(3 * εc + e1 + e2)) * δ ^ (σ + e1) * ρ / C2 with hY0
          have hY00 : 0 ≤ Y0 := by positivity
          have eL : 6144 * 54880000 * C2 * g ^ 6 * (r / ρ) ^ (1 - σ) * δ ^ (-(3 * εc + e1 + e2)) *
              δ ^ (σ + e1) * ρ * (ρ ^ (1 - σ) * δ ^ e2) / C2 = Y0 * (ρ ^ (1 - σ) * δ ^ e2) := by
            rw [hY0]; ring
          have eR : 6144 * 54880000 * C2 * g ^ 6 * (r / ρ) ^ (1 - σ) * δ ^ (-(3 * εc + e1 + e2)) *
              (δ ^ (σ + e1) * ρ * ρc ^ (1 - σ + e2) / C2) = Y0 * ρc ^ (1 - σ + e2) := by
            rw [hY0]; ring
          rw [eL, eR]
          exact mul_le_mul_of_nonneg_left hρcpow hY00
  -- the final factor
  have hrρ : (r / ρ) ^ (1 - σ) ≤ g * H0 * (R / ρ) ^ (1 - σ) := by
    have h1 : r / ρ ≤ g * H0 * (R / ρ) := by
      rw [div_le_iff₀ hρ0]
      calc r ≤ g * H0 * R := hrR
        _ = g * H0 * (R / ρ) * ρ := by field_simp
    have hgH : 1 ≤ g * H0 := by nlinarith
    calc (r / ρ) ^ (1 - σ) ≤ (g * H0 * (R / ρ)) ^ (1 - σ) :=
          Real.rpow_le_rpow (by positivity) h1 (by linarith)
      _ = (g * H0) ^ (1 - σ) * (R / ρ) ^ (1 - σ) := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (g * H0) * (R / ρ) ^ (1 - σ) := by
          gcongr
          calc (g * H0) ^ (1 - σ) ≤ (g * H0) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hgH (by linarith)
            _ = g * H0 := Real.rpow_one _
  have hH00 : 0 ≤ H0 := by linarith
  calc num / mf * H0 ≤ (6144 * 54880000 * C2 * g ^ 6 * (r / ρ) ^ (1 - σ) *
        δ ^ (-(3 * εc + e1 + e2))) * H0 := mul_le_mul_of_nonneg_right (hq.trans hq2) hH00
    _ ≤ (6144 * 54880000 * C2 * g ^ 6 * (g * H0 * (R / ρ) ^ (1 - σ)) *
        δ ^ (-(3 * εc + e1 + e2))) * H0 := by gcongr
    _ = _ := by ring


/-- Cube counts of shadings inside `ρc`-tubes. -/
theorem sum_card_cubes_le {k : ℕ} {s ρc : ℝ} (hs : 0 < s) (hρc0 : 0 < ρc) (hρc1 : ρc ≤ 1)
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {M : Fin k → Finset (Fin 3 → ℤ)}
    (hMT : ∀ j, cubeSet s (M j) ⊆ tube ρc (z j) (w j)) :
    (∑ j, ((M j).card : ℝ)) * s ^ 3 ≤ (k : ℝ) * (384 * ρc ^ 2) := by
  have hMcard : ∀ j, ((M j).card : ℝ) * s ^ 3 ≤ 384 * ρc ^ 2 := by
    intro j
    have h1 : volume (cubeSet s (M j)) ≤ ENNReal.ofReal (384 * ρc ^ 2) :=
      (measure_mono (hMT j)).trans
        (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hρc0 hρc1 (z j) (w j) (hw j))
    rw [volume_cubeSet hs, ← ENNReal.ofReal_pow hs.le, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  rw [Finset.sum_mul]
  calc ∑ j, ((M j).card : ℝ) * s ^ 3 ≤ ∑ _j : Fin k, 384 * ρc ^ 2 :=
        Finset.sum_le_sum fun j _ => hMcard j
    _ = (k : ℝ) * (384 * ρc ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The union of the cube sets has at most `384 k ρc² / μlo` volume when the multiplicity is at
least `μlo` on it. -/
theorem card_union_cubes_le {k : ℕ} {s ρc μlo : ℝ} (hs : 0 < s) (hρc0 : 0 < ρc) (hρc1 : ρc ≤ 1)
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {M : Fin k → Finset (Fin 3 → ℤ)}
    (hMT : ∀ j, cubeSet s (M j) ⊆ tube ρc (z j) (w j)) (hμlo : 0 < μlo)
    (hclo : ∀ q ∈ ⋃ j, cubeSet s (M j), μlo ≤ (fineMult (fun j => cubeSet s (M j)) q : ℝ)) :
    ((Finset.univ.biUnion M).card : ℝ) * s ^ 3 ≤ 384 * (k : ℝ) * ρc ^ 2 / μlo := by
  classical
  set Yt : Fin k → Set Space := fun j => cubeSet s (M j) with hYt
  have hU : cubeSet s (Finset.univ.biUnion M) = ⋃ j, Yt j := by
    ext y
    simp only [hYt, cubeSet, mem_iUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨m, ⟨j, hm⟩, hy⟩; exact ⟨j, m, hm, hy⟩
    · rintro ⟨j, m, hm, hy⟩; exact ⟨m, ⟨j, hm⟩, hy⟩
  have hYtm : ∀ j, MeasurableSet (Yt j) := fun j => measurableSet_cubeSet s _
  have h1 := massMeasure_ge_mul hYtm hclo (MeasurableSet.iUnion hYtm)
  rw [massMeasure_apply hYtm (MeasurableSet.iUnion hYtm), inter_self] at h1
  have e : ∀ j, Yt j ∩ ⋃ j', Yt j' = Yt j := fun j => inter_eq_left.2 (subset_iUnion Yt j)
  simp only [e] at h1
  have h2 : ∑ j, volume (Yt j) ≤ ENNReal.ofReal ((k : ℝ) * (384 * ρc ^ 2)) := by
    calc ∑ j, volume (Yt j) ≤ ∑ _j : Fin k, ENNReal.ofReal (384 * ρc ^ 2) :=
          Finset.sum_le_sum fun j _ => (measure_mono (hMT j)).trans
            (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hρc0 hρc1 (z j) (w j)
              (hw j))
      _ = ENNReal.ofReal ((k : ℝ) * (384 * ρc ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have h3 := h1.trans h2
  rw [← hU, volume_cubeSet hs, ← ENNReal.ofReal_pow hs.le, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hμlo.le] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  rw [le_div_iff₀ hμlo]
  linarith


theorem fine_density_ratio {δ σ ερ n : ℝ} (hδ : 0 < δ) (hn : 0 < n) :
    δ ^ ερ * n * δ ^ 2 / (δ ^ (2 - σ - ερ) * n) = δ ^ (σ + 2 * ερ) := by
  have h : δ ^ (σ + 2 * ερ) * δ ^ (2 - σ - ερ) = δ ^ ερ * δ ^ (2 : ℝ) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
  have hp : 0 < δ ^ (2 - σ - ερ) := Real.rpow_pos_of_pos hδ _
  rw [div_eq_iff (by positivity)]
  rw [show δ ^ 2 = δ ^ (2 : ℝ) by norm_cast]
  calc δ ^ ερ * n * δ ^ (2 : ℝ) = (δ ^ ερ * δ ^ (2 : ℝ)) * n := by ring
    _ = δ ^ (σ + 2 * ερ) * δ ^ (2 - σ - ερ) * n := by rw [h]
    _ = δ ^ (σ + 2 * ερ) * (δ ^ (2 - σ - ερ) * n) := by ring

theorem theta_from_balance {δ ρc σ ερ lam θb : ℝ} (hδ : 0 < δ) (hρc : 0 < ρc)
    (hlam : 1 / 2 ≤ lam) (h : lam ^ 3 * δ ^ (σ + 2 * ερ) ≤ δ ^ (-ερ) * θb * ρc ^ (σ - ερ)) :
    δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8 ≤ θb := by
  have hl3 : (1 / 2 : ℝ) ^ 3 ≤ lam ^ 3 := pow_le_pow_left₀ (by norm_num) hlam 3
  have hp : 0 ≤ δ ^ (σ + 2 * ερ) := Real.rpow_nonneg hδ.le _
  have key : δ ^ (σ + 2 * ερ) / 8 ≤ δ ^ (-ερ) * θb * ρc ^ (σ - ερ) := by
    have : δ ^ (σ + 2 * ερ) / 8 ≤ lam ^ 3 * δ ^ (σ + 2 * ερ) := by nlinarith
    linarith
  have e2 : δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8 =
      (δ ^ (σ + 2 * ερ) / 8) * (δ ^ ερ * ρc ^ (ερ - σ)) := by
    rw [show σ + 3 * ερ = (σ + 2 * ερ) + ερ by ring, Real.rpow_add hδ]; ring
  have h1 : δ ^ (-ερ) * δ ^ ερ = 1 := by
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
  have h2 : ρc ^ (σ - ερ) * ρc ^ (ερ - σ) = 1 := by
    rw [← Real.rpow_add hρc, show σ - ερ + (ερ - σ) = 0 by ring, Real.rpow_zero]
  have e3 : δ ^ (-ερ) * θb * ρc ^ (σ - ερ) * (δ ^ ερ * ρc ^ (ερ - σ)) = θb := by
    calc δ ^ (-ερ) * θb * ρc ^ (σ - ερ) * (δ ^ ερ * ρc ^ (ερ - σ))
        = θb * (δ ^ (-ερ) * δ ^ ερ) * (ρc ^ (σ - ερ) * ρc ^ (ερ - σ)) := by ring
      _ = θb := by rw [h1, h2]; ring
  rw [e2]
  calc δ ^ (σ + 2 * ερ) / 8 * (δ ^ ερ * ρc ^ (ερ - σ))
      ≤ δ ^ (-ερ) * θb * ρc ^ (σ - ερ) * (δ ^ ερ * ρc ^ (ερ - σ)) :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = θb := e3

/-- The mass of the grain refinement is at least `δ^ε n δ²`. -/
theorem grain_mass_arith {δ σ ερ εG ε ρc θb n k E : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρc : δ ≤ ρc) (hn : 0 < n) (hk : 0 < k)
    (hθb : δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8 ≤ θb)
    (hE : ρc ^ εG * k * ρc ^ 2 / 4 ≤ E) (hερ : 0 ≤ ερ) (hεG : 0 ≤ εG)
    (hexp : 6 * ερ + εG ≤ ε / 2) (hcut : δ ^ (ε / 2) ≤ 1 / 32) :
    δ ^ ε * n * δ ^ 2 ≤ δ ^ (2 - σ + ερ) * n * θb * E / (ρc ^ (2 - σ - ερ) * k) := by
  have hρc0 : 0 < ρc := hδ.trans_le hρc
  have hθb0 : 0 ≤ θb := le_trans (by positivity) hθb
  have hden : 0 < ρc ^ (2 - σ - ερ) * k := by positivity
  rw [le_div_iff₀ hden]
  -- lower bound for the right side
  have h1 : δ ^ (2 - σ + ερ) * n * (δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8) *
      (ρc ^ εG * k * ρc ^ 2 / 4) ≤ δ ^ (2 - σ + ερ) * n * θb * E := by
    have hA : 0 ≤ δ ^ (2 - σ + ερ) * n := by positivity
    have hB : 0 ≤ ρc ^ εG * k * ρc ^ 2 / 4 := by positivity
    calc δ ^ (2 - σ + ερ) * n * (δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8) *
          (ρc ^ εG * k * ρc ^ 2 / 4)
        ≤ δ ^ (2 - σ + ερ) * n * θb * (ρc ^ εG * k * ρc ^ 2 / 4) := by gcongr
      _ ≤ δ ^ (2 - σ + ερ) * n * θb * E := by gcongr
  refine le_trans ?_ h1
  -- simplify the powers
  have e : δ ^ (2 - σ + ερ) * n * (δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8) *
      (ρc ^ εG * k * ρc ^ 2 / 4) =
      δ ^ (2 + 4 * ερ) * ρc ^ (2 * ερ + εG) * (ρc ^ (2 - σ - ερ) * k) * n / 32 := by
    have e1 : δ ^ (2 - σ + ερ) * δ ^ (σ + 3 * ερ) = δ ^ (2 + 4 * ερ) := by
      rw [← Real.rpow_add hδ]; ring_nf
    have e2 : ρc ^ (ερ - σ) * ρc ^ εG * ρc ^ (2 : ℝ) = ρc ^ (2 * ερ + εG) * ρc ^ (2 - σ - ερ) := by
      rw [← Real.rpow_add hρc0, ← Real.rpow_add hρc0, ← Real.rpow_add hρc0]; ring_nf
    rw [show ρc ^ 2 = ρc ^ (2 : ℝ) by norm_cast]
    calc δ ^ (2 - σ + ερ) * n * (δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8) *
          (ρc ^ εG * k * ρc ^ (2 : ℝ) / 4)
        = (δ ^ (2 - σ + ερ) * δ ^ (σ + 3 * ερ)) * (ρc ^ (ερ - σ) * ρc ^ εG * ρc ^ (2 : ℝ)) *
            k * n / 32 := by ring
      _ = _ := by rw [e1, e2]; ring
  rw [e]
  have hρcpow : δ ^ (2 * ερ + εG) ≤ ρc ^ (2 * ερ + εG) :=
    Real.rpow_le_rpow hδ.le hρc (by positivity)
  have hδpow : δ ^ ε ≤ δ ^ (2 * ερ + εG) * δ ^ (4 * ερ) / 32 := by
    have h1 : δ ^ ε = δ ^ (ε - 6 * ερ - εG) * (δ ^ (2 * ερ + εG) * δ ^ (4 * ερ)) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
    have h2 : δ ^ (ε - 6 * ερ - εG) ≤ 1 / 32 :=
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans hcut
    rw [h1]
    have hp : 0 ≤ δ ^ (2 * ερ + εG) * δ ^ (4 * ερ) := by positivity
    nlinarith
  have hsplit : δ ^ (2 + 4 * ερ) = δ ^ (2 : ℝ) * δ ^ (4 * ερ) := by
    rw [← Real.rpow_add hδ]
  rw [hsplit, show δ ^ 2 = δ ^ (2 : ℝ) by norm_cast]
  have hpos : 0 ≤ (ρc ^ (2 - σ - ερ) * k) * n * δ ^ (2 : ℝ) := by positivity
  calc δ ^ ε * n * δ ^ (2 : ℝ) * (ρc ^ (2 - σ - ερ) * k)
      ≤ (δ ^ (2 * ερ + εG) * δ ^ (4 * ερ) / 32) * ((ρc ^ (2 - σ - ερ) * k) * n * δ ^ (2 : ℝ)) := by
        nlinarith
    _ ≤ (ρc ^ (2 * ερ + εG) * δ ^ (4 * ερ) / 32) * ((ρc ^ (2 - σ - ερ) * k) * n * δ ^ (2 : ℝ)) := by
        gcongr
    _ = δ ^ (2 : ℝ) * δ ^ (4 * ερ) * ρc ^ (2 * ερ + εG) * (ρc ^ (2 - σ - ερ) * k) * n / 32 := by
        ring



/-- Lower bound for the grain volume `mf`. -/
theorem mf_lower {δ ρ ρc σ ερ εG κ θb ω s k ρ0G : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρc : 0 < ρc)
    (hρc1 : ρc ≤ 1) (hs : 0 < s) (hk : 0 < k) (hω : Real.sqrt ρ / 2 ≤ ω)
    (hρ0G : ρc ^ κ / 16 ≤ ρ0G) (hρ0G1 : ρ0G ≤ 1) (hκ : 0 ≤ κ)
    (hθb : δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8 ≤ θb) :
    δ ^ (σ + 3 * ερ) * ρ * ρc ^ (1 - σ + (κ + 3 * εG + 3 * ερ)) /
        (32 * 55296 ^ 2 * 3072 * 256 * 4608) ≤
      θb * ((ρc ^ εG * ρc ^ 2 * ω / (55296 * s ^ 3) * s ^ 3) ^ 2 *
        (ρc ^ (2 - σ + ερ) * k * ρc ^ εG / 3072) /
        (256 * (4 * (32 * ρc / ρ0G + ρc) + ρc) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k))) := by
  have hρ0G0 : 0 < ρ0G := lt_of_lt_of_le (by positivity) hρ0G
  have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hω0 : 0 < ω := lt_of_lt_of_le (by positivity) hω
  set D := 32 * ρc / ρ0G with hD
  have hDlo : 32 * ρc ≤ D := by rw [hD, le_div_iff₀ hρ0G0]; nlinarith
  have hDhi : D ≤ 512 * ρc ^ (1 - κ) := by
    rw [hD, div_le_iff₀ hρ0G0]
    have e : ρc = ρc ^ (1 - κ) * ρc ^ κ := by
      rw [← Real.rpow_add hρc]; simp
    calc 32 * ρc = 32 * (ρc ^ (1 - κ) * ρc ^ κ) := by rw [← e]
      _ = 512 * ρc ^ (1 - κ) * (ρc ^ κ / 16) := by ring
      _ ≤ 512 * ρc ^ (1 - κ) * ρ0G := by gcongr
  have hden : 256 * (4 * (D + ρc) + ρc) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k) ≤
      256 * (9 * (512 * ρc ^ (1 - κ))) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k) := by
    have : 4 * (D + ρc) + ρc ≤ 9 * (512 * ρc ^ (1 - κ)) := by nlinarith
    gcongr
  have hθs : ρc ^ εG * ρc ^ 2 * ω / (55296 * s ^ 3) * s ^ 3 = ρc ^ εG * ρc ^ 2 * ω / 55296 := by
    field_simp
  rw [hθs]
  have hθb0 : 0 ≤ θb := le_trans (by positivity) hθb
  have hω2 : ρ / 4 ≤ ω ^ 2 := by
    have h1 : (Real.sqrt ρ / 2) ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (by positivity) hω 2
    rw [div_pow, Real.sq_sqrt hρ.le] at h1
    linarith
  -- main computation
  set Q := (ρc ^ εG * ρc ^ 2 * ω / 55296) ^ 2 * (ρc ^ (2 - σ + ερ) * k * ρc ^ εG / 3072) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hdenpos : 0 < 256 * (4 * (D + ρc) + ρc) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k) := by
    have : 0 < D := lt_of_lt_of_le (by positivity) hDlo
    positivity
  have hstep1 : Q / (256 * (9 * (512 * ρc ^ (1 - κ))) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k)) ≤
      Q / (256 * (4 * (D + ρc) + ρc) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k)) :=
    div_le_div_of_nonneg_left hQ0 hdenpos hden
  have hk0 : 0 < k := hk
  set C'' : ℝ := 55296 ^ 2 * 3072 * 256 * 4608 with hC''
  have hnum : (ρc ^ εG * ρc ^ 2 * ω / 55296) ^ 2 * (ρc ^ (2 - σ + ερ) * k * ρc ^ εG / 3072) =
      ω ^ 2 * k * ρc ^ (3 * εG + 6 - σ + ερ) / (55296 ^ 2 * 3072) := by
    have e : (ρc ^ εG) ^ 2 * (ρc ^ 2) ^ 2 * ρc ^ (2 - σ + ερ) * ρc ^ εG =
        ρc ^ (3 * εG + 6 - σ + ερ) := by
      rw [← Real.rpow_natCast (ρc ^ εG), ← Real.rpow_mul hρc.le, show (ρc ^ 2) ^ 2 = ρc ^ (4 : ℝ) by
        rw [← pow_mul]; norm_cast, ← Real.rpow_add hρc, ← Real.rpow_add hρc,
        ← Real.rpow_add hρc]
      congr 1; push_cast; ring
    rw [← e]; ring
  have hden' : 256 * (9 * (512 * ρc ^ (1 - κ))) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k) =
      256 * 4608 * k * ρc ^ (5 - κ - σ - ερ) := by
    have e : ρc ^ (1 - κ) * ρc ^ 2 * ρc ^ (2 - σ - ερ) = ρc ^ (5 - κ - σ - ερ) := by
      rw [show ρc ^ 2 = ρc ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hρc, ← Real.rpow_add hρc]
      congr 1; ring
    rw [← e]; ring
  have hratio : ρc ^ (3 * εG + 6 - σ + ερ) / ρc ^ (5 - κ - σ - ερ) =
      ρc ^ (2 * ερ + 3 * εG + 1 + κ) := by
    rw [← Real.rpow_sub hρc]; congr 1; ring
  have hval : Q / (256 * (9 * (512 * ρc ^ (1 - κ))) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k)) =
      ω ^ 2 * ρc ^ (2 * ερ + 3 * εG + 1 + κ) / C'' := by
    rw [hQ, hnum, hden', ← hratio, hC'']
    field_simp
  have hθbρ : δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8 * (ω ^ 2 * ρc ^ (2 * ερ + 3 * εG + 1 + κ) / C'')
      ≥ δ ^ (σ + 3 * ερ) * ρ * ρc ^ (1 - σ + (κ + 3 * εG + 3 * ερ)) / (32 * C'') := by
    have e : ρc ^ (ερ - σ) * ρc ^ (2 * ερ + 3 * εG + 1 + κ) = ρc ^ (1 - σ + (κ + 3 * εG + 3 * ερ)) := by
      rw [← Real.rpow_add hρc]; congr 1; ring
    have hC0 : 0 < C'' := by positivity
    have hP : 0 ≤ δ ^ (σ + 3 * ερ) * ρc ^ (1 - σ + (κ + 3 * εG + 3 * ερ)) := by positivity
    calc δ ^ (σ + 3 * ερ) * ρ * ρc ^ (1 - σ + (κ + 3 * εG + 3 * ερ)) / (32 * C'')
        = (δ ^ (σ + 3 * ερ) * ρc ^ (1 - σ + (κ + 3 * εG + 3 * ερ))) * (ρ / 4) / (8 * C'') := by
          ring
      _ ≤ (δ ^ (σ + 3 * ερ) * ρc ^ (1 - σ + (κ + 3 * εG + 3 * ερ))) * ω ^ 2 / (8 * C'') := by
          gcongr
      _ = δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8 * (ω ^ 2 * ρc ^ (2 * ερ + 3 * εG + 1 + κ) / C'') := by
          rw [← e]; ring
  have hfin : δ ^ (σ + 3 * ερ) * ρc ^ (ερ - σ) / 8 * (ω ^ 2 * ρc ^ (2 * ερ + 3 * εG + 1 + κ) / C'')
      ≤ θb * (Q / (256 * (4 * (D + ρc) + ρc) * ρc ^ 2 * (ρc ^ (2 - σ - ερ) * k))) := by
    rw [← hval]
    apply mul_le_mul hθb hstep1 (by positivity) hθb0
  have e32 : (32 : ℝ) * 55296 ^ 2 * 3072 * 256 * 4608 = 32 * C'' := by rw [hC'']; ring
  rw [e32]
  exact hθbρ.trans hfin



/-- Bound for the slab half-width of the grains. -/
theorem slab_width_le {δ ρ ρc s ω L lam ερ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδρc : δ ≤ ρc)
    (hρc : ρc ≤ δ ^ (-ερ) * ρ) (hρcsq : ρc ≤ Real.sqrt ρ / 4096) (hs : 0 < s) (hsρc : s ≤ ρc)
    (hω0 : 0 ≤ ω) (hω : ω ≤ Real.sqrt ρ) (hsq1 : Real.sqrt ρ ≤ 1) (hρ : 0 < ρ)
    (hL : L = δ ^ (-η)) (hlam : 1 / 2 ≤ lam) (hερ : 0 ≤ ερ) (hη : 0 ≤ η) :
    (2 * ((2 * ω + 2 * ρc) * (ρc / 2 + δ + L * (Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s +
      4 * ρc)) + 2 * ρc) + 2 * s) / lam ≤ 78 * δ ^ (-(ερ + η)) * ρ := by
  have hρc0 : 0 < ρc := hδ.trans_le hδρc
  have hsq0 : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hsq2 : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ.le
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hΛ1 : δ ^ (-ερ) ≤ δ ^ (-(ερ + η)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hΛ2 : δ ^ (-η) ≤ δ ^ (-(ερ + η)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  set Λ := δ ^ (-(ερ + η)) with hΛ
  have hπ : ρc / 2 + δ + L * (Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s + 4 * ρc) ≤
      3 / 2 * ρc + 4 * L * Real.sqrt ρ := by
    have h1 : Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s + 4 * ρc ≤ 4 * Real.sqrt ρ := by
      nlinarith
    have h2 : L * (Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s + 4 * ρc) ≤ L * (4 * Real.sqrt ρ) :=
      mul_le_mul_of_nonneg_left h1 hL0
    linarith
  have hfac : 2 * ω + 2 * ρc ≤ 3 * Real.sqrt ρ := by linarith
  have hprod : (2 * ω + 2 * ρc) * (ρc / 2 + δ + L * (Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s +
      4 * ρc)) ≤ 9 / 2 * ρc + 12 * L * ρ := by
    have hπ0 : 0 ≤ ρc / 2 + δ + L * (Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s + 4 * ρc) := by
      positivity
    calc (2 * ω + 2 * ρc) * (ρc / 2 + δ + L * (Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s + 4 * ρc))
        ≤ (3 * Real.sqrt ρ) * (3 / 2 * ρc + 4 * L * Real.sqrt ρ) :=
          mul_le_mul hfac hπ hπ0 (by positivity)
      _ = 9 / 2 * Real.sqrt ρ * ρc + 12 * L * (Real.sqrt ρ * Real.sqrt ρ) := by ring
      _ ≤ 9 / 2 * ρc + 12 * L * ρ := by
          rw [hsq2]
          have : Real.sqrt ρ * ρc ≤ ρc := by nlinarith
          linarith
  have hnum : 2 * ((2 * ω + 2 * ρc) * (ρc / 2 + δ + L * (Real.sqrt ρ + 4 * ρc + 2 * ω + 2 * s +
      4 * ρc)) + 2 * ρc) + 2 * s ≤ 15 * ρc + 24 * L * ρ := by linarith
  have hnum0 : 0 ≤ 2 * ((2 * ω + 2 * ρc) * (ρc / 2 + δ + L * (Real.sqrt ρ + 4 * ρc + 2 * ω +
      2 * s + 4 * ρc)) + 2 * ρc) + 2 * s := by positivity
  have hlam0 : 0 < lam := by linarith
  rw [div_le_iff₀ hlam0]
  have hρcΛ : ρc ≤ Λ * ρ := hρc.trans (mul_le_mul_of_nonneg_right hΛ1 hρ.le)
  have hLΛ : L * ρ ≤ Λ * ρ := by rw [hL]; exact mul_le_mul_of_nonneg_right hΛ2 hρ.le
  have hΛρ : 0 ≤ Λ * ρ := by positivity
  nlinarith

/-- Combination of the final exponents. -/
theorem final_exponent_le {δ g H0 C E a b ε Rt : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hg : 1 ≤ g)
    (hga : g ≤ δ ^ (-a)) (hH : 1 ≤ H0) (hHb : H0 ≤ 158 * δ ^ (-b))
    (hE : 7 * a + 2 * b + E ≤ ε / 2) (hC : 0 ≤ C) (hcut : C * 158 ^ 2 * δ ^ (ε / 2) ≤ 1)
    (hRt : 0 ≤ Rt) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    C * g ^ 7 * H0 ^ 2 * δ ^ (-E) * Rt ≤ δ ^ (-ε) * Rt := by
  apply mul_le_mul_of_nonneg_right _ hRt
  have hg7 : g ^ 7 ≤ δ ^ (-(7 * a)) := by
    calc g ^ 7 ≤ (δ ^ (-a)) ^ 7 := pow_le_pow_left₀ (by linarith) hga 7
      _ = δ ^ (-(7 * a)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; ring_nf
  have hH2 : H0 ^ 2 ≤ 158 ^ 2 * δ ^ (-(2 * b)) := by
    calc H0 ^ 2 ≤ (158 * δ ^ (-b)) ^ 2 := pow_le_pow_left₀ (by linarith) hHb 2
      _ = 158 ^ 2 * δ ^ (-(2 * b)) := by
          rw [mul_pow, ← Real.rpow_natCast (δ ^ (-b)), ← Real.rpow_mul hδ.le]; ring_nf
  have hcomb : δ ^ (-(7 * a)) * δ ^ (-(2 * b)) * δ ^ (-E) ≤ δ ^ (-(ε / 2)) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hsplit : δ ^ (-ε) = δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) := by
    rw [← Real.rpow_add hδ]; ring_nf
  have hcut' : C * 158 ^ 2 ≤ δ ^ (-(ε / 2)) := by
    have e : C * 158 ^ 2 = C * 158 ^ 2 * δ ^ (ε / 2) * δ ^ (-(ε / 2)) := by
      rw [mul_assoc (C * 158 ^ 2), ← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero, mul_one]
    rw [e]
    calc C * 158 ^ 2 * δ ^ (ε / 2) * δ ^ (-(ε / 2)) ≤ 1 * δ ^ (-(ε / 2)) :=
          mul_le_mul_of_nonneg_right hcut (by positivity)
      _ = δ ^ (-(ε / 2)) := one_mul _
  have hg0 : 0 ≤ g ^ 7 := by positivity
  have hH0 : 0 ≤ H0 ^ 2 := by positivity
  calc C * g ^ 7 * H0 ^ 2 * δ ^ (-E) ≤ C * δ ^ (-(7 * a)) * (158 ^ 2 * δ ^ (-(2 * b))) *
        δ ^ (-E) := by gcongr
    _ = C * 158 ^ 2 * (δ ^ (-(7 * a)) * δ ^ (-(2 * b)) * δ ^ (-E)) := by ring
    _ ≤ δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) := mul_le_mul hcut' hcomb (by positivity) (by positivity)
    _ = δ ^ (-ε) := hsplit.symm


end WangZahlLot.Obl.wz_extremal_lipschitz_grains
