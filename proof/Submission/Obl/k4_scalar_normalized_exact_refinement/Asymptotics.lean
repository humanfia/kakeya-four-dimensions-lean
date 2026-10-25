import Submission.Obl.k4_scalar_normalized_exact_refinement.WeightedTails

/-!
# Asymptotic bookkeeping for a Refinement

* `RefData.Z_inv_le`: `Z⁻¹ ≤ N^ε` with the certificate's tolerances `ε → 0`;
* `powerSmall_of_factor`: a power-small bound multiplied by `N^(o(1))` and a constant stays
  power-small;
* `RefData.along`: power-small estimates of `p` hold along the certificate's subsequence;
* `exists_good_point`: finitely many power-small weighted exceptional families of `q` leave,
  eventually, a world and a point outside all of them.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

variable {p q : Code} {r b h : ℝ}

/-- A power-small bound times `N^(ε k)`, with `ε → 0`, times a constant is power-small. -/
lemma powerSmall_of_factor {N : ℕ → ℝ} (hNt : Tendsto N atTop atTop) (hN1 : ∀ k, 1 ≤ N k)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0)) (C : ℝ≥0∞) (hC : C ≠ ∞)
    {a : ℕ → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (ha : ∀ᶠ k in atTop, a k ≤ ENNReal.ofReal (N k ^ ε k) * (C * ENNReal.ofReal (N k ^ (-c)))) :
    ∀ᶠ k in atTop, a k ≤ ENNReal.ofReal (N k ^ (-(c / 2))) := by
  have hε' : ∀ᶠ k in atTop, ε k ≤ c / 4 :=
    hε.eventually (ge_mem_nhds (by linarith))
  have hC' : ∀ᶠ k in atTop, C ≤ ENNReal.ofReal (N k ^ (c / 4)) := by
    have h1 : Tendsto (fun k => N k ^ (c / 4)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hNt
    have h2 := h1.eventually (eventually_ge_atTop (C.toReal))
    filter_upwards [h2] with k hk
    calc C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hk
  filter_upwards [ha, hε', hC'] with k hk hεk hCk
  have hNk : 0 < N k := by linarith [hN1 k]
  calc a k ≤ ENNReal.ofReal (N k ^ ε k) * (C * ENNReal.ofReal (N k ^ (-c))) := hk
    _ ≤ ENNReal.ofReal (N k ^ (c / 4)) *
        (ENNReal.ofReal (N k ^ (c / 4)) * ENNReal.ofReal (N k ^ (-c))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN1 k) hεk))
          (mul_le_mul' hCk le_rfl)
    _ = ENNReal.ofReal (N k ^ (c / 4) * (N k ^ (c / 4) * N k ^ (-c))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (N k ^ (-(c / 2))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.rpow_add hNk, ← Real.rpow_add hNk]
        apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
        linarith

namespace RefData

variable (R : RefData p q r b h)

lemma φ_tendsto : Tendsto R.φ atTop atTop := R.mono.tendsto_atTop

lemma Z_inv_le (hp : Spec.RawScalar p) (k : ℕ) :
    ENNReal.ofReal (R.Z k)⁻¹ ≤ ENNReal.ofReal (q.N k ^ R.ε k) := by
  apply ENNReal.ofReal_le_ofReal
  have hN : 0 < p.N (R.φ k) := by linarith [RawScalar.N_ge hp (R.φ k)]
  have hZ := R.Z_ge hp k
  rw [R.qN_eq k]
  calc (R.Z k)⁻¹ ≤ (p.N (R.φ k) ^ (-R.ε k))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hN _) hZ
    _ = p.N (R.φ k) ^ R.ε k := by rw [Real.rpow_neg hN.le, inv_inv]

/-- Eventual bounds of `p` hold along the subsequence, in the resolution of `q`. -/
lemma along {F : ℕ → ℝ≥0∞} {c : ℝ}
    (hF : ∀ᶠ k in atTop, F k ≤ ENNReal.ofReal (p.N k ^ (-c))) :
    ∀ᶠ k in atTop, F (R.φ k) ≤ ENNReal.ofReal (q.N k ^ (-c)) := by
  filter_upwards [R.φ_tendsto.eventually hF] with k hk
  rw [R.qN_eq k]
  exact hk

end RefData

/-- Finitely many power-small weighted exceptional families leave a good point. -/
theorem exists_good_point (hq : Spec.RawScalar q) {m : ℕ}
    (X : Fin m → (k : ℕ) → Fin (q.1 k) → Set Inc)
    (hsmall : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (X j k i) ≤ ENNReal.ofReal (q.N k ^ (-c))) :
    ∀ᶠ k in atTop, ∃ i : Fin (q.1 k), ∃ z : Inc, ∀ j, z ∉ X j k i := by
  classical
  choose c hc hbound using hsmall
  set c₀ : ℝ := if hm : m = 0 then 1 else Finset.univ.inf' (Finset.univ_nonempty_iff.mpr
    ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩) c with hc₀def
  have hc₀ : 0 < c₀ := by
    rw [hc₀def]
    split_ifs with hm
    · norm_num
    · exact (Finset.lt_inf'_iff _).mpr fun j _ => hc j
  have hc₀le : ∀ j, c₀ ≤ c j := by
    intro j
    rw [hc₀def]
    split_ifs with hm
    · exact absurd j.2 (by omega)
    · exact Finset.inf'_le _ (Finset.mem_univ j)
  have hN1 : ∀ k, 1 ≤ q.N k := fun k => by linarith [RawScalar.N_ge hq k]
  have hNt := RawScalar.N_tendsto hq
  have hall : ∀ᶠ k in atTop, ∀ j, ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (X j k i) ≤
      ENNReal.ofReal (q.N k ^ (-c₀)) := by
    rw [eventually_all]
    intro j
    filter_upwards [hbound j] with k hk
    exact hk.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith [hc₀le j])))
  have hK := RawScalar.K_sub hq (c₀ / 2) (by linarith)
  have hlarge : ∀ᶠ k in atTop, (m : ℝ) + 1 ≤ q.N k ^ (c₀ / 2) :=
    ((tendsto_rpow_atTop (by linarith)).comp hNt).eventually (eventually_ge_atTop _)
  filter_upwards [hall, hK, hlarge] with k hk hKk hlk
  have hNk : 0 < q.N k := by linarith [hN1 k]
  by_contra hcon
  push_neg at hcon
  have hcover : ∀ i, q.mu k i univ ≤ ∑ j, q.mu k i (X j k i) := by
    intro i
    calc q.mu k i univ ≤ q.mu k i (⋃ j, X j k i) := by
          apply measure_mono
          intro z _
          obtain ⟨j, hj⟩ := hcon i z
          exact mem_iUnion.mpr ⟨j, hj⟩
      _ ≤ ∑ j, q.mu k i (X j k i) := measure_iUnion_fintype_le _ _
  have htotal : ENNReal.ofReal ((q.K k)⁻¹) ≤ (m : ℝ≥0∞) * ENNReal.ofReal (q.N k ^ (-c₀)) := by
    calc ENNReal.ofReal ((q.K k)⁻¹) ≤ ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i univ :=
          RawScalar.mass_lower hq k
      _ ≤ ∑ i, ENNReal.ofReal (q.ω k i) * ∑ j, q.mu k i (X j k i) := by
          gcongr with i
          exact hcover i
      _ = ∑ j, ∑ i, ENNReal.ofReal (q.ω k i) * q.mu k i (X j k i) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
      _ ≤ ∑ _j : Fin m, ENNReal.ofReal (q.N k ^ (-c₀)) := Finset.sum_le_sum fun j _ => hk j
      _ = (m : ℝ≥0∞) * ENNReal.ofReal (q.N k ^ (-c₀)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hKpos : 0 < q.K k := by linarith [RawScalar.K_ge hq k]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at htotal
  have h1 : q.N k ^ (-(c₀ / 2)) ≤ (q.K k)⁻¹ := by
    rw [Real.rpow_neg hNk.le]
    exact inv_anti₀ hKpos hKk
  have h2 : (m : ℝ) * q.N k ^ (-c₀) < q.N k ^ (-(c₀ / 2)) := by
    have e : q.N k ^ (-c₀) = q.N k ^ (-(c₀ / 2)) * (q.N k ^ (c₀ / 2))⁻¹ := by
      rw [← Real.rpow_neg hNk.le, ← Real.rpow_add hNk]
      ring_nf
    rw [e]
    have hpos : 0 < q.N k ^ (-(c₀ / 2)) := Real.rpow_pos_of_pos hNk _
    have hpos' : 0 < q.N k ^ (c₀ / 2) := Real.rpow_pos_of_pos hNk _
    calc (m : ℝ) * (q.N k ^ (-(c₀ / 2)) * (q.N k ^ (c₀ / 2))⁻¹)
        = q.N k ^ (-(c₀ / 2)) * ((m : ℝ) / q.N k ^ (c₀ / 2)) := by ring
      _ < q.N k ^ (-(c₀ / 2)) * 1 := by
          gcongr
          rw [div_lt_one hpos']
          linarith
      _ = _ := mul_one _
  linarith

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
