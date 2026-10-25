-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.LargeComparison.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-! The B-to-CF implication from this obligation's x0150 branch. -/

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open MeasureTheory

/-- A normalized slope is bounded by `3` on `[-1, 1]` (mean value theorem). -/
theorem abs_le_three {f : ℝ → ℝ} (hN : ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) (hf0 : |f 0| ≤ 1) {z : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) : |f z| ≤ 3 := by
  have hd : Differentiable ℝ f := hN.1.differentiable (by norm_num)
  have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (C := 2)
    (fun x _ => hd x) (fun x hx => by simpa [Real.norm_eq_abs] using (hN.2 x hx).2.1)
    (convex_Icc (-1 : ℝ) 1) h0 hz
  simp only [Real.norm_eq_abs, sub_zero] at hmv
  have hz1 : |z| ≤ 1 := abs_le.mpr ⟨hz.1, hz.2⟩
  calc |f z| = |(f z - f 0) + f 0| := by rw [sub_add_cancel]
    _ ≤ |f z - f 0| + |f 0| := abs_add_le _ _
    _ ≤ 3 := by linarith

/-- The twisted projection of a subset of the unit ball lies in `[-4,4] × [-1,1]`. -/
theorem proj_subset_box {f : ℝ → ℝ} (hN : ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) (hf0 : |f 0| ≤ 1)
    {E : Set LeanEval.Analysis.WangZahlKakeya.Space} (hE : E ⊆ Metric.ball 0 1) :
    (fun p : LeanEval.Analysis.WangZahlKakeya.Space => (p 0 + f (p 2) * p 1, p 2)) '' E ⊆
      Set.Icc (-4 : ℝ) 4 ×ˢ Set.Icc (-1 : ℝ) 1 := by
  rintro _ ⟨p, hp, rfl⟩
  have hpn : ‖p‖ < 1 := by simpa using hE hp
  have hc : ∀ k : Fin 3, |p k| ≤ 1 := fun k => by
    have := PiLp.norm_apply_le p k
    rw [Real.norm_eq_abs] at this
    linarith
  have h2 : p 2 ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp (hc 2)
  have hf := abs_le_three hN hf0 h2
  refine ⟨?_, abs_le.mp (hc 2)⟩
  have h4 : |p 0 + f (p 2) * p 1| ≤ 4 := by
    calc |p 0 + f (p 2) * p 1| ≤ |p 0| + |f (p 2) * p 1| := abs_add_le _ _
      _ = |p 0| + |f (p 2)| * |p 1| := by rw [abs_mul]
      _ ≤ 1 + 3 * 1 := add_le_add (hc 0) (mul_le_mul hf (hc 1) (abs_nonneg _) (by norm_num))
      _ = 4 := by norm_num
  exact abs_le.mp h4

/-- The `1/2`-thickening of a subset of `[-4,4] × [-1,1]` has area at most `27`. -/
theorem volume_thickening_half_le {A : Set (ℝ × ℝ)}
    (hA : A ⊆ Set.Icc (-4 : ℝ) 4 ×ˢ Set.Icc (-1 : ℝ) 1) :
    volume (Metric.thickening (1/2 : ℝ) A) ≤ 27 := by
  have hsub : Metric.thickening (1/2 : ℝ) A ⊆
      Set.Ioo (-9/2 : ℝ) (9/2) ×ˢ Set.Ioo (-3/2 : ℝ) (3/2) := by
    intro q hq
    rcases Metric.mem_thickening_iff.mp hq with ⟨a, ha, hqa⟩
    have ha' := hA ha
    rw [Prod.dist_eq] at hqa
    have h1 : dist q.1 a.1 < 1/2 := lt_of_le_of_lt (le_max_left _ _) hqa
    have h2 : dist q.2 a.2 < 1/2 := lt_of_le_of_lt (le_max_right _ _) hqa
    rw [Real.dist_eq] at h1 h2
    rcases ha' with ⟨⟨ha1, ha2⟩, ⟨ha3, ha4⟩⟩
    rcases abs_lt.mp h1 with ⟨h1a, h1b⟩
    rcases abs_lt.mp h2 with ⟨h2a, h2b⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  calc volume (Metric.thickening (1/2 : ℝ) A)
      ≤ volume (Set.Ioo (-9/2 : ℝ) (9/2) ×ˢ Set.Ioo (-3/2 : ℝ) (3/2)) := measure_mono hsub
    _ = 27 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
        ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- `δ ^ (1 - ε ^ 2) < 1/2` for `δ ≤ (1/4) ^ (1 / (1 - ε ^ 2))`. -/
theorem scale_lt {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ4 : δ ≤ (1/4 : ℝ) ^ (1 / (1 - ε ^ 2))) : δ ^ (1 - ε ^ 2) < 1/2 := by
  have hpos : 0 < 1 - ε ^ 2 := by nlinarith
  calc δ ^ (1 - ε ^ 2) ≤ ((1/4 : ℝ) ^ (1 / (1 - ε ^ 2))) ^ (1 - ε ^ 2) :=
        Real.rpow_le_rpow hδ.le hδ4 hpos.le
    _ = 1/4 := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hpos.ne', Real.rpow_one]
    _ < 1/2 := by norm_num

/-- `27 (2δ)^ε ≤ δ^(ε/2)` for `δ ≤ (1/54) ^ (2/ε)`. -/
theorem key_real {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ54 : δ ≤ (1/54 : ℝ) ^ (2 / ε)) : (δ / (1/2)) ^ ε * 27 ≤ δ ^ (ε / 2) := by
  have h2 : δ / (1/2) = 2 * δ := by ring
  rw [h2, Real.mul_rpow (by norm_num) hδ.le]
  have hsplit : δ ^ ε = δ ^ (ε / 2) * δ ^ (ε / 2) := by
    rw [← Real.rpow_add hδ]; ring_nf
  have hsmall : δ ^ (ε / 2) ≤ 1/54 := by
    calc δ ^ (ε / 2) ≤ ((1/54 : ℝ) ^ (2 / ε)) ^ (ε / 2) :=
          Real.rpow_le_rpow hδ.le hδ54 (by positivity)
      _ = 1/54 := by
          rw [← Real.rpow_mul (by norm_num)]
          have : 2 / ε * (ε / 2) = 1 := by field_simp
          rw [this, Real.rpow_one]
  have h2e : (2 : ℝ) ^ ε ≤ 2 := by
    calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1.le
      _ = 2 := Real.rpow_one 2
  have hpos : 0 ≤ δ ^ (ε / 2) := Real.rpow_nonneg hδ.le _
  have h2pos : 0 ≤ (2 : ℝ) ^ ε := Real.rpow_nonneg (by norm_num) _
  have hab : (2 : ℝ) ^ ε * δ ^ (ε / 2) ≤ 1/27 := by
    nlinarith [mul_le_mul h2e hsmall hpos (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hab hpos]

/-- The normalized projection estimate implies the coarse/fine comparison, with `ρ = 1/2`
and `Z = Y`. -/
theorem cf_of_b : ((fun T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (F : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (N : (ℝ → ℝ) → Prop) (P : (ℝ → ℝ) → Set LeanEval.Analysis.WangZahlKakeya.Space → Set (ℝ × ℝ)) => ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) → F η δ n x v → ∀ f : ℝ → ℝ, N f → |f 0| ≤ 1 → ENNReal.ofReal (δ ^ ε) ≤ MeasureTheory.volume (P f (⋃ i, Y i))) (fun η δ n x v Y => 0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ Metric.ball 0 1) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))) (fun η δ n x v => ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * MeasureTheory.volume W) (fun f : ℝ → ℝ => ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) (fun (f : ℝ → ℝ) (E : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun p : LeanEval.Analysis.WangZahlKakeya.Space => (p 0 + f (p 2) * p 1, p 2)) '' E)) (fun (δ : ℝ) (x v : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening δ (segment ℝ x (x + v)))) → ((fun T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (F : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (N : (ℝ → ℝ) → Prop) (P : (ℝ → ℝ) → Set LeanEval.Analysis.WangZahlKakeya.Space → Set (ℝ × ℝ)) => ∀ ε κ : ℝ, 0 < ε → ε < 1 → 0 < κ → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) → F η δ n x v → ∀ f : ℝ → ℝ, N f → |f 0| ≤ 1 → ∃ ρ : ℝ, δ ^ (1 - ε ^ 2) < ρ ∧ ρ < 1 ∧ ∃ Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space, (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧ ENNReal.ofReal (δ ^ κ * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Z i)) ∧ ENNReal.ofReal ((δ / ρ) ^ ε) * MeasureTheory.volume (Metric.thickening ρ (P f (⋃ i, Z i))) ≤ MeasureTheory.volume (P f (⋃ i, Z i))) (fun η δ n x v Y => 0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ Metric.ball 0 1) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))) (fun η δ n x v => ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * MeasureTheory.volume W) (fun f : ℝ → ℝ => ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) (fun (f : ℝ → ℝ) (E : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun p : LeanEval.Analysis.WangZahlKakeya.Space => (p 0 + f (p 2) * p 1, p 2)) '' E)) (fun (δ : ℝ) (x v : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening δ (segment ℝ x (x + v)))) := by
  intro hB
  beta_reduce at hB ⊢
  intro ε κ hε hε1 hκ
  obtain ⟨ηB, hηB, dB, hdB, hBδ⟩ := hB (ε / 2) (by positivity)
  refine ⟨min ηB κ, lt_min hηB hκ,
    min dB (min ((1/4 : ℝ) ^ (1 / (1 - ε ^ 2))) ((1/54 : ℝ) ^ (2 / ε))),
    lt_min hdB (lt_min (by positivity) (by positivity)), ?_⟩
  intro δ hδ hδd hδ100 n x v Y hH htr hF f hN hf0
  obtain ⟨hn, hv, hTB, hsep, hYm, hYT, hmass⟩ := hH
  have hδ1 : δ ≤ 1 := by linarith
  have hδdB : δ ≤ dB := le_trans hδd (min_le_left _ _)
  have hδ4 : δ ≤ (1/4 : ℝ) ^ (1 / (1 - ε ^ 2)) :=
    le_trans hδd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ54 : δ ≤ (1/54 : ℝ) ^ (2 / ε) :=
    le_trans hδd (le_trans (min_le_right _ _) (min_le_right _ _))
  have hpowη : δ ^ ηB ≤ δ ^ (min ηB κ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)
  have hpowκ : δ ^ κ ≤ δ ^ (min ηB κ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_right _ _)
  have hpowneg : δ ^ (-(min ηB κ)) ≤ δ ^ (-ηB) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg (min_le_left _ _))
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hδ2 : (0 : ℝ) ≤ δ ^ 2 := by positivity
  have hmassB := le_trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpowη hnn) hδ2)) hmass
  have hvol := hBδ δ hδ hδdB hδ100 n x v Y ⟨hn, hv, hTB, hsep, hYm, hYT, hmassB⟩ htr
    (fun W hW => le_trans (hF W hW)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpowneg hnn)) le_rfl))
    f hN hf0
  refine ⟨1/2, scale_lt hε hε1 hδ hδ4, by norm_num, Y, hYm, fun i => le_rfl,
    le_trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpowκ hnn) hδ2)) hmass, ?_⟩
  have hsubball : (⋃ i, Y i) ⊆ Metric.ball 0 1 :=
    Set.iUnion_subset (fun i => (hYT i).trans (hTB i))
  have h27 := volume_thickening_half_le (proj_subset_box hN hf0 hsubball)
  calc ENNReal.ofReal ((δ / (1/2)) ^ ε) * volume (Metric.thickening (1/2 : ℝ)
          ((fun p : LeanEval.Analysis.WangZahlKakeya.Space => (p 0 + f (p 2) * p 1, p 2)) ''
            ⋃ i, Y i))
        ≤ ENNReal.ofReal ((δ / (1/2)) ^ ε) * 27 := mul_le_mul' le_rfl h27
    _ = ENNReal.ofReal ((δ / (1/2)) ^ ε * 27) := by
        rw [ENNReal.ofReal_mul (by positivity)]; norm_num
    _ ≤ ENNReal.ofReal (δ ^ (ε / 2)) := ENNReal.ofReal_le_ofReal (key_real hε hε1 hδ hδ54)
    _ ≤ _ := hvol

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
