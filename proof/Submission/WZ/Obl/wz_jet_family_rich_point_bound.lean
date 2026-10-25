-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_family_rich_point_bound.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_jet_close_pair_moment
import Submission.WZ.Obl.wz_jet_transverse_pair_moment
import Submission.WZ.Obl.wz_jet_broad_tangent_rich_bound
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_jet_family_rich_point_bound`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_jet_family_rich_point_bound`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_jet_family_rich_point_bound/`
belong to this obligation.

## Glue of the split (x0240)

Every point of the `lam`-rich set has many coefficient-close pairs, or many
transverse pairs, or lies in the broad near-tangent remainder. Markov's
inequality and the two pair-moment children bound the first two parts. The
broad child, applied at `ε / 2`, bounds the third. The three bounds add up to
`δ ^ (-ε) * lam ^ (-(3/2))` once the cutoff is small. `PROOF.md` of the split
has the prose.
-/

namespace WangZahlLot.Obl.wz_jet_family_rich_point_bound

open MeasureTheory

noncomputable def mult {n : ℕ} (δ : ℝ) (g : Fin n → ℝ → ℝ) (p : ℝ × ℝ) : ENNReal :=
  Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p)

noncomputable def closeCount {n : ℕ} (δ R : ℝ) (q : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : Fin n → ℝ → ℝ) (p : ℝ × ℝ) : ENNReal :=
  Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if dist (q i) (q j) < R then Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ}) (fun _ => (1 : ENNReal)) p else 0))

noncomputable def transCount {n : ℕ} (δ κ : ℝ) (q : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : Fin n → ℝ → ℝ) (p : ℝ × ℝ) : ENNReal :=
  Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if i = j then 0 else Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | κ * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p))

theorem measurableSet_strip {δ : ℝ} {h : ℝ → ℝ} (hh : Continuous h) :
    MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - h p.2| ≤ δ} :=
  (measurableSet_Icc.preimage measurable_snd).inter
    (measurableSet_le ((continuous_fst.sub (hh.comp continuous_snd)).abs).measurable
      measurable_const)

theorem measurable_closeCount {n : ℕ} {δ R : ℝ} {q : Fin n → EuclideanSpace ℝ (Fin 3)}
    {g : Fin n → ℝ → ℝ} (hg : ∀ i, Continuous (g i)) :
    Measurable (closeCount δ R q g) := by
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  by_cases hd : dist (q i) (q j) < R
  · simp only [ite_eq_left hd]
    exact measurable_const.indicator ((measurableSet_strip (hg i)).inter (measurableSet_strip (hg j)))
  · simp only [ite_eq_right hd]
    exact measurable_const

theorem measurable_transCount {n : ℕ} {δ κ : ℝ} {q : Fin n → EuclideanSpace ℝ (Fin 3)}
    {g : Fin n → ℝ → ℝ} (hg : ∀ i, Continuous (g i)) :
    Measurable (transCount δ κ q g) := by
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    exact measurable_const
  · simp only [ite_eq_right hij]
    refine measurable_const.indicator
      (((measurableSet_strip (hg i)).inter (measurableSet_strip (hg j))).inter ?_)
    exact measurableSet_le measurable_const (continuous_abs.measurable.comp
      (((measurable_deriv (g i)).comp measurable_snd).sub
        ((measurable_deriv (g j)).comp measurable_snd)))

theorem exists_absorb (A s : ℝ) (hA : 0 < A) (hs : 0 < s) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → A * δ ^ s ≤ 1 := by
  refine ⟨(A⁻¹) ^ (1 / s), by positivity, ?_⟩
  intro δ hδ hδd
  have h1 : δ ^ s ≤ ((A⁻¹) ^ (1 / s)) ^ s := Real.rpow_le_rpow hδ.le hδd hs.le
  have h2 : ((A⁻¹) ^ (1 / s)) ^ s = A⁻¹ := by
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
  rw [h2] at h1
  calc A * δ ^ s ≤ A * A⁻¹ := mul_le_mul_of_nonneg_left h1 hA.le
    _ = 1 := mul_inv_cancel₀ hA.ne'

theorem close_arith (C δ η ε lam : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hηε : η ≤ ε / 32) (hlam : 1 ≤ lam) :
    C * δ ^ (-2 * η) * Real.sqrt (δ * lam * δ ^ (-(ε / 2)) / δ) / (δ ^ (ε / 2 / 4) * lam ^ 2) ≤
      C * δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have e1 : δ * lam * δ ^ (-(ε / 2)) / δ = lam * δ ^ (-(ε / 2)) := by
    field_simp
  have e2 : Real.sqrt (lam * δ ^ (-(ε / 2))) = lam ^ (1 / 2 : ℝ) * δ ^ (-(ε / 4)) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hlam0.le (Real.rpow_nonneg hδ.le _),
      ← Real.rpow_mul hδ.le]
    congr 2
    ring
  have e3 : lam ^ (1 / 2 : ℝ) / lam ^ 2 = lam ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast lam 2, ← Real.rpow_sub hlam0]
    norm_num
  have e4 : δ ^ (-2 * η) * δ ^ (-(ε / 4)) / δ ^ (ε / 2 / 4) =
      δ ^ (-2 * η + -(ε / 4) - ε / 2 / 4) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_sub hδ]
  have e5 : δ ^ (-2 * η + -(ε / 4) - ε / 2 / 4) ≤ δ ^ (-(ε / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  rw [e1, e2]
  calc C * δ ^ (-2 * η) * (lam ^ (1 / 2 : ℝ) * δ ^ (-(ε / 4))) / (δ ^ (ε / 2 / 4) * lam ^ 2)
      = C * (δ ^ (-2 * η) * δ ^ (-(ε / 4)) / δ ^ (ε / 2 / 4)) *
          (lam ^ (1 / 2 : ℝ) / lam ^ 2) := by ring
    _ = C * δ ^ (-2 * η + -(ε / 4) - ε / 2 / 4) * lam ^ (-(3 / 2 : ℝ)) := by rw [e4, e3]
    _ ≤ C * δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)) := by gcongr

theorem trans_arith (C δ η ε lam : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hηε : η ≤ ε / 32) (hlam : 1 ≤ lam) :
    C * δ ^ (-2 * η - ε / 16) / (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) /
        (δ ^ (ε / 2 / 4) * lam ^ 2) ≤
      C * δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have e3 : 1 / (lam ^ (-(1 / 2 : ℝ)) * lam ^ 2) = lam ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast lam 2, ← Real.rpow_add hlam0, one_div, ← Real.rpow_neg hlam0.le]
    norm_num
  have e4 : δ ^ (-2 * η - ε / 16) / δ ^ (ε / 2 / 2) / δ ^ (ε / 2 / 4) =
      δ ^ (-2 * η - ε / 16 - ε / 2 / 2 - ε / 2 / 4) := by
    rw [← Real.rpow_sub hδ, ← Real.rpow_sub hδ]
  have e5 : δ ^ (-2 * η - ε / 16 - ε / 2 / 2 - ε / 2 / 4) ≤ δ ^ (-(ε / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  calc C * δ ^ (-2 * η - ε / 16) / (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) /
        (δ ^ (ε / 2 / 4) * lam ^ 2)
      = C * (δ ^ (-2 * η - ε / 16) / δ ^ (ε / 2 / 2) / δ ^ (ε / 2 / 4)) *
          (1 / (lam ^ (-(1 / 2 : ℝ)) * lam ^ 2)) := by ring
    _ = C * δ ^ (-2 * η - ε / 16 - ε / 2 / 2 - ε / 2 / 4) * lam ^ (-(3 / 2 : ℝ)) := by
      rw [e4, e3]
    _ ≤ C * δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)) := by gcongr

theorem final_arith (A δ ε lam : ℝ) (hδ : 0 < δ) (hlam : 1 ≤ lam)
    (habs : A * δ ^ (ε / 2) ≤ 1) :
    A * (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ))) ≤ δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ)) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have e : δ ^ (-(ε / 2)) = δ ^ (ε / 2) * δ ^ (-ε) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [e]
  calc A * (δ ^ (ε / 2) * δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ)))
      = (A * δ ^ (ε / 2)) * (δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ))) := by ring
    _ ≤ 1 * (δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right habs (by positivity)
    _ = δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ)) := one_mul _

/-- The frozen statement, proved from the three children of the split. -/
theorem main : (fun P : (n : ℕ) → (Fin n → EuclideanSpace ℝ (Fin 3)) → (Fin n → ℝ → ℝ) → Prop => ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ), (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → P n q g → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → ∀ lam : ℝ, 1 ≤ lam → MeasureTheory.volume {p : ℝ × ℝ | ENNReal.ofReal lam ≤ (Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p))} ≤ ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3/2 : ℝ)))) (fun n q g => ∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) := by
  intro ε hε
  obtain ⟨ηB, hηB, dB, hdB, hBb⟩ :=
    WangZahlLot.wz_jet_broad_tangent_rich_bound (ε / 2) (by positivity)
  obtain ⟨CC, hCC, hCm⟩ := WangZahlLot.wz_jet_close_pair_moment
  obtain ⟨CT, hCT, hTm⟩ :=
    WangZahlLot.wz_jet_transverse_pair_moment (ε / 16) (by positivity)
  obtain ⟨d1, hd1, habs⟩ := exists_absorb (CC + CT + 1) (ε / 2) (by positivity) (by positivity)
  refine ⟨min ηB (ε / 32), lt_min hηB (by positivity), min dB d1, lt_min hdB hd1, ?_⟩
  intro δ hδ hδ0 hδ1 n q g hq hg hjet hsep hcount lam hlam
  have hδ1' : δ ≤ 1 := hδ1.trans (by norm_num)
  have hlam0 : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hη0 : 0 ≤ min ηB (ε / 32) := le_min hηB.le (by positivity)
  have hηε : min ηB (ε / 32) ≤ ε / 32 := min_le_right _ _
  have hcountB : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
      (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-ηB) * (r / δ) := by
    intro q0 r hr hr1
    refine (hcount q0 r hr hr1).trans (mul_le_mul_of_nonneg_right ?_
      (div_nonneg (hδ.le.trans hr) hδ.le))
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (neg_le_neg (min_le_left _ _))
  have hBδ := hBb δ hδ (hδ0.trans (min_le_left _ _)) hδ1 n q g hq hg hjet hsep hcountB lam hlam
  have hBδ' : volume {p : ℝ × ℝ | ENNReal.ofReal lam ≤ mult δ g p ∧
      closeCount δ (δ * lam * δ ^ (-(ε / 2))) q g p < ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) ∧
      transCount δ (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) q g p <
        ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2)} ≤
      ENNReal.ofReal (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ))) := hBδ
  have hgc : ∀ i, Continuous (g i) := fun i => (hg i).continuous
  have hθ : 0 < δ ^ (ε / 2 / 4) * lam ^ 2 := by positivity
  have hδR : δ ≤ δ * lam * δ ^ (-(ε / 2)) := by
    have h1 : 1 ≤ δ ^ (-(ε / 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1' (by linarith)
    have h2 : 1 ≤ lam * δ ^ (-(ε / 2)) := by nlinarith
    calc δ = δ * 1 := (mul_one δ).symm
      _ ≤ δ * (lam * δ ^ (-(ε / 2))) := mul_le_mul_of_nonneg_left h2 hδ.le
      _ = δ * lam * δ ^ (-(ε / 2)) := (mul_assoc _ _ _).symm
  have hκ : 0 < δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ)) := by positivity
  have hκ1 : δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have h1 : δ ^ (ε / 2 / 2) ≤ 1 := Real.rpow_le_one hδ.le hδ1' (by positivity)
    have h2 : lam ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlam (by norm_num)
    calc δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ)) ≤ 1 * 1 :=
          mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hclose : volume {p : ℝ × ℝ | ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) ≤
      closeCount δ (δ * lam * δ ^ (-(ε / 2))) q g p} ≤
      ENNReal.ofReal (CC * (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)))) := by
    have hM := meas_ge_le_lintegral_div (μ := volume)
      (measurable_closeCount (δ := δ) (R := δ * lam * δ ^ (-(ε / 2))) (q := q) hgc).aemeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hθ) ENNReal.ofReal_ne_top
    have hI : ∫⁻ p, closeCount δ (δ * lam * δ ^ (-(ε / 2))) q g p ∂volume ≤
        ENNReal.ofReal (CC * δ ^ (-2 * min ηB (ε / 32)) *
          Real.sqrt (δ * lam * δ ^ (-(ε / 2)) / δ)) :=
      hCm n q g δ (min ηB (ε / 32)) (δ * lam * δ ^ (-(ε / 2))) hδ hδ1' hη0 hδR hq hg hjet
        hsep hcount
    calc _ ≤ (∫⁻ p, closeCount δ (δ * lam * δ ^ (-(ε / 2))) q g p ∂volume) /
          ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) := hM
      _ ≤ ENNReal.ofReal (CC * δ ^ (-2 * min ηB (ε / 32)) *
            Real.sqrt (δ * lam * δ ^ (-(ε / 2)) / δ)) /
          ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) := by gcongr
      _ = ENNReal.ofReal (CC * δ ^ (-2 * min ηB (ε / 32)) *
            Real.sqrt (δ * lam * δ ^ (-(ε / 2)) / δ) / (δ ^ (ε / 2 / 4) * lam ^ 2)) :=
        (ENNReal.ofReal_div_of_pos hθ).symm
      _ ≤ ENNReal.ofReal (CC * (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_assoc]
        exact close_arith CC δ _ ε lam hCC.le hδ hδ1' hε.le hηε hlam
  have htrans : volume {p : ℝ × ℝ | ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) ≤
      transCount δ (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) q g p} ≤
      ENNReal.ofReal (CT * (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)))) := by
    have hM := meas_ge_le_lintegral_div (μ := volume)
      (measurable_transCount (δ := δ) (κ := δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ)))
        (q := q) hgc).aemeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hθ) ENNReal.ofReal_ne_top
    have hI : ∫⁻ p, transCount δ (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) q g p ∂volume ≤
        ENNReal.ofReal (CT * δ ^ (-2 * min ηB (ε / 32) - ε / 16) /
          (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ)))) :=
      hTm n q g δ (min ηB (ε / 32)) (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) hδ hδ1' hη0 hκ
        hκ1 hq hg hjet hsep hcount
    calc _ ≤ (∫⁻ p, transCount δ (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) q g p ∂volume) /
          ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) := hM
      _ ≤ ENNReal.ofReal (CT * δ ^ (-2 * min ηB (ε / 32) - ε / 16) /
            (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ)))) /
          ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) := by gcongr
      _ = ENNReal.ofReal (CT * δ ^ (-2 * min ηB (ε / 32) - ε / 16) /
            (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) / (δ ^ (ε / 2 / 4) * lam ^ 2)) :=
        (ENNReal.ofReal_div_of_pos hθ).symm
      _ ≤ ENNReal.ofReal (CT * (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_assoc]
        exact trans_arith CT δ _ ε lam hCT.le hδ hδ1' hηε hlam
  have hsub : {p : ℝ × ℝ | ENNReal.ofReal lam ≤ mult δ g p} ⊆
      ({p : ℝ × ℝ | ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) ≤
          closeCount δ (δ * lam * δ ^ (-(ε / 2))) q g p} ∪
        {p : ℝ × ℝ | ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) ≤
          transCount δ (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) q g p}) ∪
      {p : ℝ × ℝ | ENNReal.ofReal lam ≤ mult δ g p ∧
        closeCount δ (δ * lam * δ ^ (-(ε / 2))) q g p <
          ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) ∧
        transCount δ (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) q g p <
          ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2)} := by
    intro p hp
    by_cases h1 : ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) ≤
        closeCount δ (δ * lam * δ ^ (-(ε / 2))) q g p
    · exact Or.inl (Or.inl h1)
    by_cases h2 : ENNReal.ofReal (δ ^ (ε / 2 / 4) * lam ^ 2) ≤
        transCount δ (δ ^ (ε / 2 / 2) * lam ^ (-(1 / 2 : ℝ))) q g p
    · exact Or.inl (Or.inr h2)
    exact Or.inr ⟨hp, lt_of_not_ge h1, lt_of_not_ge h2⟩
  have hX : 0 ≤ δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)) := by positivity
  show volume {p : ℝ × ℝ | ENNReal.ofReal lam ≤ mult δ g p} ≤
    ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ)))
  calc volume {p : ℝ × ℝ | ENNReal.ofReal lam ≤ mult δ g p}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (CC * (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)))) +
        ENNReal.ofReal (CT * (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)))) +
        ENNReal.ofReal (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ))) :=
      add_le_add (add_le_add hclose htrans) hBδ'
    _ = ENNReal.ofReal ((CC + CT + 1) * (δ ^ (-(ε / 2)) * lam ^ (-(3 / 2 : ℝ)))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) hX]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3 / 2 : ℝ))) :=
      ENNReal.ofReal_le_ofReal (final_arith (CC + CT + 1) δ ε lam hδ hlam
        (habs δ hδ (hδ0.trans (min_le_right _ _))))

end WangZahlLot.Obl.wz_jet_family_rich_point_bound

theorem WangZahlLot.wz_jet_family_rich_point_bound : (fun P : (n : ℕ) → (Fin n → EuclideanSpace ℝ (Fin 3)) → (Fin n → ℝ → ℝ) → Prop => ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ), (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → P n q g → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → ∀ lam : ℝ, 1 ≤ lam → MeasureTheory.volume {p : ℝ × ℝ | ENNReal.ofReal lam ≤ (Finset.sum Finset.univ (fun i => Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} (fun _ => (1 : ENNReal)) p))} ≤ ENNReal.ofReal (δ ^ (-ε) * lam ^ (-(3/2 : ℝ)))) (fun n q g => ∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) :=
  WangZahlLot.Obl.wz_jet_family_rich_point_bound.main
