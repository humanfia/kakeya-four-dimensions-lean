-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.PhysicalEstimates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Physical
import Submission.WZ.Obl.wz_multiscale_finite_tower.Scales

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (ConvexCount convexCount_mono slabBound_mono)

lemma PhysicalFrame.mono {d r s θ θ' : ℝ} {y w : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : PhysicalFrame d r s θ y w n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ θ') :
    PhysicalFrame d r s θ' y w n x v Y := by
  have hp : d ^ θ' ≤ d ^ θ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hθ
  have hn : d ^ (-θ) ≤ d ^ (-θ') :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ)
  exact ⟨hF.1, hF.2.1, (ENNReal.ofReal_le_ofReal (by gcongr)).trans hF.2.2.1,
    convexCount_mono hn hF.2.2.2.1, slabBound_mono hn hF.2.2.2.2⟩

/-- Averaging is valid without any separation condition on the child tubes. -/
lemma PhysicalFrame.union_lower {d r s θ : ℝ} {y w : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : PhysicalFrame d r s θ y w n x v Y) (hd : 0 < d) :
    ENNReal.ofReal (d ^ θ * s ^ 2) ≤ volume (⋃ i, Y i) := by
  have hs : (∑ i, volume (Y i)) ≤ (n : ℝ≥0∞) * volume (⋃ i, Y i) := by
    calc
      _ ≤ ∑ _i : Fin n, volume (⋃ i, Y i) := Finset.sum_le_sum fun i _ =>
        measure_mono (Set.subset_iUnion Y i)
      _ = _ := by simp [nsmul_eq_mul]
  have hv := hF.2.2.1.trans hs
  rw [show d ^ θ * n * s ^ 2 = (n : ℝ) * (d ^ θ * s ^ 2) by ring,
    ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast] at hv
  exact (ENNReal.mul_le_mul_iff_left
    (show (n : ℝ≥0∞) ≠ 0 by exact_mod_cast hF.1.ne') (by simp)).mp
      (by simpa only [mul_comm] using hv)

/-- A fibre's convex count controls its normalized cardinality. -/
lemma PhysicalFrame.card_bound {d r s θ : ℝ} {y w : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : PhysicalFrame d r s θ y w n x v Y)
    (hd : 0 < d) (hr : 0 < r) (hr1 : r ≤ 1) (hw : ‖w‖ = 1) :
    (n : ℝ) * (s / r) ^ 2 ≤ 56 * d ^ (-θ) := by
  have hcount := hF.2.2.2.1 (Tube r y w) ((convex_segment y (y + w)).thickening r)
  have hset : {i : Fin n | True ∧ Tube s (x i) (v i) ⊆ Tube r y w} = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun i => ⟨trivial, (hF.2.1 i).2.1⟩
  rw [hset, Set.ncard_univ, Nat.card_fin] at hcount
  have hvol := WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hr.le hr1 y w hw
  have hbound := hcount.trans (mul_le_mul' le_rfl hvol)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hr)]
  nlinarith

/-- The elementary estimate for gaps too short to use affine normalization. -/
lemma PhysicalFrame.small_gap {σ ω d r s θ h loss : ℝ} {y w : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : PhysicalFrame d r s θ y w n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) (hsr : s ≤ r) (hw : ‖w‖ = 1)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω)
    (hgap : d ^ h ≤ s / r) (hbudget : 2 * θ + (5 / 2 : ℝ) * h ≤ loss) :
    ENNReal.ofReal ((1 / 56 : ℝ) * d ^ loss * r ^ 2 * volumeFactor σ ω (s / r) n) ≤
      volume (⋃ i, Y i) := by
  have ht : 0 < s / r := div_pos hs hr
  have ht1 : s / r ≤ 1 := (div_le_one hr).mpr hsr
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hF.1
  have hnt : s / r ≤ n * (s / r) := by nlinarith
  have hcard := hF.card_bound hd hr hr1 hw
  have hpow : (n * (s / r)) ^ (-σ) ≤ d ^ (-h / 2) := by
    calc
      _ ≤ (s / r) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos ht hnt (neg_nonpos.mpr hσ)
      _ ≤ (s / r) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
      _ ≤ (d ^ h) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hd _) hgap (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hd.le]; congr 1; ring
  have hfac : volumeFactor σ ω (s / r) n ≤ 56 * d ^ (-θ - h / 2) := by
    calc
      _ ≤ 1 * (56 * d ^ (-θ)) * d ^ (-h / 2) := by
        dsimp [volumeFactor]
        apply mul_le_mul
        · exact mul_le_mul (Real.rpow_le_one ht.le ht1 hω) hcard (by positivity) zero_le_one
        · exact hpow
        · positivity
        · positivity
      _ = _ := by rw [one_mul, mul_assoc, ← Real.rpow_add hd]; congr 2; ring
  have ht2 : d ^ (2 * h) ≤ (s / r) ^ 2 := by
    rw [show (2 : ℝ) * h = h * (2 : ℝ) by ring, Real.rpow_mul hd.le, Real.rpow_two]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hd.le _) hgap 2
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hF.union_lower hd)
  calc
    _ ≤ (1 / 56 : ℝ) * d ^ loss * r ^ 2 * (56 * d ^ (-θ - h / 2)) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = r ^ 2 * d ^ (loss - θ - h / 2) := by
      rw [show loss - θ - h / 2 = loss + (-θ - h / 2) by ring, Real.rpow_add hd]
      ring
    _ ≤ r ^ 2 * d ^ (θ + 2 * h) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)) (sq_nonneg r)
    _ = d ^ θ * (r ^ 2 * d ^ (2 * h)) := by rw [Real.rpow_add hd]; ring
    _ ≤ d ^ θ * (r ^ 2 * (s / r) ^ 2) := by gcongr
    _ = d ^ θ * s ^ 2 := by field_simp

/-- Uniform physical estimates on every edge, with a common bottom-scale error. -/
theorem Endpoint.all_physical_scales {σ ω : ℝ} (hE : Endpoint σ ω)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω)
    {loss D : ℝ} (hloss : 0 < loss) (hD : 0 < D) :
    ∃ a θ d₀ : ℝ, 0 < a ∧ 0 < θ ∧ θ ≤ 1 ∧ 0 < d₀ ∧ d₀ ≤ D ∧
      ∀ d r s : ℝ, 0 < d → d ≤ 1 → d ≤ d₀ → 0 < r → r ≤ 1 →
      0 < s → d * r ≤ s → s ≤ r → ∀ y w : Space, ‖w‖ = 1 → ∀ n x v Y,
      PhysicalFrame d r s θ y w n x v Y →
      ENNReal.ofReal (a * d ^ loss * r ^ 2 * volumeFactor σ ω (s / r) n) ≤
        volume (⋃ i, Y i) := by
  let h : ℝ := loss / 10
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨a, η, c, ha, hη, hη1, hc, hc1, HE⟩ := hE.physical_on_large_gap hσ hloss hh
  obtain ⟨d₀, hd₀, hd₀D, hcut⟩ := exists_scale_cutoff c h D hc hh hD
  let θ : ℝ := min η (loss / 8)
  have hθ : 0 < θ := lt_min hη (by positivity)
  have hθη : θ ≤ η := min_le_left _ _
  have hθloss : θ ≤ loss / 8 := min_le_right _ _
  refine ⟨min a (1 / 56), θ, d₀, lt_min ha (by norm_num), hθ,
    hθη.trans hη1, hd₀, hd₀D, ?_⟩
  intro d r s hd hd1 hdd hr hr1 hs hdr hsr y w hw n x v Y hF
  have hfac : 0 ≤ d ^ loss * r ^ 2 * volumeFactor σ ω (s / r) n := by
    dsimp [volumeFactor]; positivity
  rcases le_total (d ^ h) (s / r) with hgap | hgap
  · have hv := hF.small_gap hd hd1 hr hr1 hs hsr hw hσ hσ1 hω hgap
      (show 2 * θ + (5 / 2 : ℝ) * h ≤ loss by dsimp [h]; linarith)
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hv
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (min_le_right a (1 / 56)) hfac
  · have hsc : s ≤ c * r := (div_le_iff₀ hr).mp (hgap.trans (hcut d hd hdd))
    have hv := HE d r s hd hd1 hr hs hdr hsc hr1 hgap y w hw n x v Y
      (hF.mono hd hd1 hθη)
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hv
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (min_le_left a (1 / 56)) hfac

end WangZahlLot.Obl.wz_multiscale_finite_tower
