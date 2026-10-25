-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.ParameterPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.OverlapLower

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- A totally bounded set has a uniform bound on the cardinality of families
separated by a fixed positive distance. -/
theorem separated_family_card_bound {P : Type*} [PseudoMetricSpace P]
    {K : Set P} (hK : TotallyBounded K) {r : ℝ} (hr : 0 < r) :
    ∃ M : ℕ, ∀ {n : ℕ} (p : Fin n → P), (∀ i, p i ∈ K) →
      (∀ i j, i ≠ j → r ≤ dist (p i) (p j)) → n ≤ M := by
  classical
  obtain ⟨F, hF, hcover⟩ := Metric.totallyBounded_iff.mp hK (r / 2) (half_pos hr)
  let := hF.fintype
  refine ⟨Fintype.card F, ?_⟩
  intro n p hp hsep
  have hex (i : Fin n) : ∃ c : F, dist (p i) c < r / 2 := by
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp (hcover (hp i))
    exact ⟨⟨c, hc⟩, hpc⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have htri := dist_triangle (p i) (f i) (p j)
    rw [hij, dist_comm (f j : P) (p j)] at htri
    have hfi := hf i
    rw [hij] at hfi
    linarith [hsep i j hne, hfi, hf j]
  simpa using Fintype.card_le_of_injective f hinj

/-- An essentially distinct unit-tube family whose axes and directions all lie
within fixed multiples of the radius of a common line has bounded cardinality.
The bound depends only on the two multiples and the longitudinal interval. -/
theorem near_axis_family_card_bound (A B L : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B) (_hL : 0 ≤ L) :
    ∃ M : ℕ, ∀ {δ : ℝ}, 0 < δ → ∀ {n : ℕ} (x v : Fin n → Space)
      (t : Fin n → ℝ) (x₀ v₀ : Space), (∀ i, ‖v i‖ = 1) →
      (∀ i, |t i| ≤ L) → (∀ i, ‖x i - x₀ - t i • v₀‖ ≤ B * δ) →
      (∀ i, ‖v i - v₀‖ ≤ A * δ) →
      (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) → n ≤ M := by
  let r : ℝ := 1 / (100 * (A + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hr100 : r ≤ 1 / 100 := by
    dsimp [r]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100)
    linarith
  have hrA : r * (A + 1) = 1 / 100 := by
    dsimp [r]
    have hA1 : A + 1 ≠ 0 := by positivity
    field_simp
  let R₀ : ℝ := max L (max B A)
  obtain ⟨M, hM⟩ := separated_family_card_bound
    (isCompact_closedBall (0 : ℝ × Space × Space) R₀).totallyBounded hr
  refine ⟨M, ?_⟩
  intro δ hδ n x v t x₀ v₀ hv ht hx hdir hhalf
  let b : Fin n → Space := fun i => δ⁻¹ • (x i - x₀ - t i • v₀)
  let a : Fin n → Space := fun i => δ⁻¹ • (v i - v₀)
  let p : Fin n → ℝ × Space × Space := fun i => (t i, b i, a i)
  have hb (i : Fin n) : ‖b i‖ ≤ B := by
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    calc
      δ⁻¹ * ‖x i - x₀ - t i • v₀‖ ≤ δ⁻¹ * (B * δ) :=
        mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr hδ.le)
      _ = B := by field_simp
  have ha (i : Fin n) : ‖a i‖ ≤ A := by
    dsimp [a]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    calc
      δ⁻¹ * ‖v i - v₀‖ ≤ δ⁻¹ * (A * δ) :=
        mul_le_mul_of_nonneg_left (hdir i) (inv_nonneg.mpr hδ.le)
      _ = A := by field_simp
  apply hM p
  · intro i
    rw [mem_closedBall, dist_zero_right]
    change max |t i| (max ‖b i‖ ‖a i‖) ≤ R₀
    exact max_le ((ht i).trans (le_max_left _ _))
      (max_le_max (hb i) (ha i) |>.trans (le_max_right _ _))
  · intro i j hij
    by_contra hfar
    have hclose : dist (p i) (p j) < r := lt_of_not_ge hfar
    change max |t i - t j| (max ‖b i - b j‖ ‖a i - a j‖) < r at hclose
    obtain ⟨htij, hbij, haij⟩ := (max_lt_iff.mp hclose).imp_right max_lt_iff.mp
    have hbs (k : Fin n) : δ • b k = x k - x₀ - t k • v₀ := by
      dsimp [b]
      rw [smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
    have has (k : Fin n) : δ • a k = v k - v₀ := by
      dsimp [a]
      rw [smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
    have hdij : ‖v i - v j‖ ≤ δ / 100 := by
      have heq : v i - v j = δ • (a i - a j) := by
        rw [smul_sub, has, has]
        abel
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      exact (mul_le_mul_of_nonneg_left haij.le hδ.le).trans
        (by nlinarith [mul_le_mul_of_nonneg_left hr100 hδ.le])
    have htji : |t j - t i| ≤ r := by rw [abs_sub_comm]; exact htij.le
    have hposij : ‖x j - (x i + (t j - t i) • v i)‖ ≤ δ / 100 := by
      have heq : x j - (x i + (t j - t i) • v i) =
          δ • (b j - b i) + (t j - t i) • (v₀ - v i) := by
        rw [smul_sub, hbs, hbs]
        module
      rw [heq]
      calc
        _ ≤ ‖δ • (b j - b i)‖ + ‖(t j - t i) • (v₀ - v i)‖ := norm_add_le _ _
        _ = δ * ‖b i - b j‖ + |t j - t i| * ‖v i - v₀‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos hδ, norm_sub_rev (b j), norm_sub_rev v₀]
        _ ≤ δ * r + r * (A * δ) := add_le_add
          (mul_le_mul_of_nonneg_left hbij.le hδ.le)
          (mul_le_mul htji (hdir i) (norm_nonneg _) hr.le)
        _ = δ * (r * (A + 1)) := by ring
        _ = δ / 100 := by rw [hrA]; ring
    exact (intersection_gt_half_of_near_parameters hδ (hv i)
      (htji.trans hr100) hposij hdij).not_ge (hhalf i j hij)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
