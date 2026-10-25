-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorDyadic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorBox

/-!
# Volume of boxes, and dyadic rounding of box dimensions

`box a b c z e` has volume `a b c`. A dimension `a ∈ [ρ, 4]` is rounded up to `4 / 2^α` with
`α = ⌊log₂ (4/a)⌋₊ ≤ ⌊log₂ (4/ρ)⌋₊`, at most doubling it (WZ Proposition 4.6, Step 3).
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

noncomputable section

/-- The volume of a box. -/
theorem box_volume {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) (z : Space)
    (e : Space ≃ₗᵢ[ℝ] Space) :
    volume (box a b c z e) = ENNReal.ofReal (a * b * c) := by
  let s : Fin 3 → ℝ := ![a, b, c]
  let Q : Set (Fin 3 → ℝ) := Icc (fun i => -(s i / 2)) (fun i => s i / 2)
  have hbox : box a b c z e = (fun p => WithLp.ofLp (e (p - z))) ⁻¹' Q := by
    ext p
    show (|e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧ |e (p - z) 2| ≤ c / 2) ↔
      ((fun i => -(s i / 2)) ≤ WithLp.ofLp (e (p - z)) ∧ WithLp.ofLp (e (p - z)) ≤ fun i => s i / 2)
    rw [Pi.le_def, Pi.le_def]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
      · exact (abs_le.mp h0).1
      · exact (abs_le.mp h1).1
      · exact (abs_le.mp h2).1
      · exact (abs_le.mp h0).2
      · exact (abs_le.mp h1).2
      · exact (abs_le.mp h2).2
    · rintro ⟨hlo, hhi⟩
      exact ⟨abs_le.mpr ⟨hlo 0, hhi 0⟩, abs_le.mpr ⟨hlo 1, hhi 1⟩, abs_le.mpr ⟨hlo 2, hhi 2⟩⟩
  have hmp : MeasurePreserving (fun p : Space => WithLp.ofLp (e (p - z))) volume volume :=
    (PiLp.volume_preserving_ofLp (Fin 3)).comp
      ((LinearIsometryEquiv.measurePreserving e).comp (measurePreserving_sub_right volume z))
  rw [hbox, hmp.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_three, s, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have e1 : a / 2 - -(a / 2) = a := by ring
  have e2 : b / 2 - -(b / 2) = b := by ring
  have e3 : c / 2 - -(c / 2) = c := by ring
  rw [e1, e2, e3, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]

theorem box_mono {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (z : Space)
    (e : Space ≃ₗᵢ[ℝ] Space) : box a b c z e ⊆ box a' b' c' z e := by
  rintro p ⟨h0, h1, h2⟩
  exact ⟨h0.trans (by linarith), h1.trans (by linarith), h2.trans (by linarith)⟩

theorem box_convex (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    Convex ℝ (box a b c z e) := by
  intro x hx y hy s t hs ht hst
  have hlin : ∀ i : Fin 3, e (s • x + t • y - z) i = s * e (x - z) i + t * e (y - z) i := by
    intro i
    have h1 : s • x + t • y - z = s • (x - z) + t • (y - z) := by
      calc s • x + t • y - z = s • x + t • y - (s + t) • z := by rw [hst, one_smul]
        _ = s • (x - z) + t • (y - z) := by rw [smul_sub, smul_sub, add_smul]; abel
    rw [h1, map_add, map_smul, map_smul]
    rfl
  have hbound : ∀ (i : Fin 3) (r : ℝ), |e (x - z) i| ≤ r → |e (y - z) i| ≤ r →
      |e (s • x + t • y - z) i| ≤ r := by
    intro i r hx' hy'
    rw [hlin]
    calc |s * e (x - z) i + t * e (y - z) i| ≤ |s * e (x - z) i| + |t * e (y - z) i| :=
          abs_add_le _ _
      _ = s * |e (x - z) i| + t * |e (y - z) i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * r + t * r := by gcongr
      _ = r := by rw [← add_mul, hst, one_mul]
  exact ⟨hbound 0 _ hx.1 hy.1, hbound 1 _ hx.2.1 hy.2.1, hbound 2 _ hx.2.2 hy.2.2⟩

/-- The dyadic exponent of a dimension `a ∈ (0, M]`. -/
def dyExp (M a : ℝ) : ℕ := ⌊Real.logb 2 (M / a)⌋₊

/-- The dyadic round-up `M / 2 ^ dyExp M a` of `a`. -/
def dyUp (M a : ℝ) : ℝ := M / 2 ^ dyExp M a

theorem le_dyUp {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) : a ≤ dyUp M a := by
  have hM : 0 < M := ha.trans_le haM
  have h1 : (1 : ℝ) ≤ M / a := by rw [le_div_iff₀ ha]; linarith
  have hlog : 0 ≤ Real.logb 2 (M / a) := Real.logb_nonneg (by norm_num) h1
  have h2 : (2 : ℝ) ^ dyExp M a ≤ M / a := by
    have := Nat.floor_le hlog
    calc (2 : ℝ) ^ dyExp M a = (2 : ℝ) ^ ((dyExp M a : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ Real.logb 2 (M / a) := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = M / a := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  unfold dyUp
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ ha] at h2
  linarith

theorem dyUp_lt {M a : ℝ} (ha : 0 < a) (hM : 0 < M) : dyUp M a < 2 * a := by
  have h2 : M / a < (2 : ℝ) ^ (dyExp M a + 1) := by
    have := Nat.lt_floor_add_one (Real.logb 2 (M / a))
    calc M / a = (2 : ℝ) ^ Real.logb 2 (M / a) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ < (2 : ℝ) ^ ((dyExp M a : ℝ) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by simpa [dyExp] using this)
      _ = (2 : ℝ) ^ (dyExp M a + 1) := by rw [← Real.rpow_natCast]; push_cast; rfl
  unfold dyUp
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ ha, pow_succ] at h2
  linarith

theorem dyExp_le {M a ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) (hρa : ρ ≤ a) :
    dyExp M a ≤ dyExp M ρ := by
  unfold dyExp
  apply Nat.floor_le_floor
  apply Real.logb_le_logb_of_le (by norm_num) (div_pos hM (hρ.trans_le hρa))
  exact div_le_div_of_nonneg_left hM.le hρ hρa

theorem dyUp_le {M a : ℝ} (hM : 0 ≤ M) : dyUp M a ≤ M := by
  unfold dyUp
  exact div_le_self hM (one_le_pow₀ (by norm_num))

theorem dyUp_le_dyUp {M a b : ℝ} (hM : 0 ≤ M) (h : dyExp M b ≤ dyExp M a) :
    dyUp M a ≤ dyUp M b := by
  unfold dyUp
  exact div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_right₀ (by norm_num) h)

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
