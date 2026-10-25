-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_cell_weighted_cover.Classes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Basic
import Submission.WZ.Obl.wz_tube_packing_bound

/-!
# Normal classes

`sgnNormal n` flips a unit vector so that its chart coordinate is nonnegative.
`normal_class_pigeonhole`: a set covered by finitely many sets `A i` indexed by unit vectors is,
up to a factor `θ³ / 100000`, covered by the `A i` of one class of sign-normalised directions of
diameter `≤ θ / 4` (grid of spacing `θ / 8` on each coordinate, plus the chart: at most
`3 (16/θ + 3)³ ≤ 100000 / θ³` classes).
`exists_good_direction`: a unit vector at projective distance `≥ θ` from `e₀` has a component
`≥ θ / 2` along some unit vector `v ⊥ e₀`.
-/

namespace WangZahlLot.Obl.wz_transverse_cell_weighted_cover

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Sign normalisation of a direction: its chart coordinate becomes nonnegative. -/
def sgnNormal (n : Space) : Space :=
  if 0 ≤ n (WangZahlLot.Obl.wz_tube_packing_bound.chart n) then n else -n

theorem sgnNormal_eq_or (n : Space) : sgnNormal n = n ∨ sgnNormal n = -n := by
  unfold sgnNormal; split_ifs <;> simp

theorem norm_sgnNormal (n : Space) : ‖sgnNormal n‖ = ‖n‖ := by
  rcases sgnNormal_eq_or n with h | h <;> rw [h]; simp

theorem pd_sgnNormal_left (n e : Space) : pd (sgnNormal n) e = pd n e := by
  rcases sgnNormal_eq_or n with h | h <;> rw [h]
  exact pd_neg_left n e

theorem abs_inner_sgnNormal (n q : Space) : |inner ℝ (sgnNormal n) q| = |inner ℝ n q| := by
  rcases sgnNormal_eq_or n with h | h <;> rw [h]; simp [inner_neg_left]

/-- Pigeonholing sign-normalised directions into classes of diameter `θ / 4`. -/
theorem normal_class_pigeonhole {n : ℕ} (K : Finset (Fin n)) (nrm : Fin n → Space)
    (hnrm : ∀ i ∈ K, ‖nrm i‖ = 1) (A : Fin n → Set Space) (Y : Set Space)
    (hY : Y ⊆ ⋃ i ∈ K, A i) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ K' ⊆ K, (∀ i ∈ K', ∀ i' ∈ K', ‖sgnNormal (nrm i) - sgnNormal (nrm i')‖ ≤ θ / 4) ∧
      volume Y * ENNReal.ofReal (θ ^ 3 / 100000) ≤ volume (Y ∩ ⋃ i ∈ K', A i) := by
  classical
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = θ / 8 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; positivity
  -- coordinates of the normalised normals lie in `[-1, 1]`
  have hcoord1 : ∀ i ∈ K, ∀ m : Fin 3, |sgnNormal (nrm i) m| ≤ 1 := by
    intro i hi m
    have h := WangZahlLot.Obl.wz_tube_packing_bound.abs_apply_le_norm (sgnNormal (nrm i)) m
    rwa [norm_sgnNormal, hnrm i hi] at h
  -- the class of an index: the grid cell (spacing `η`) of its normalised normal
  obtain ⟨cls, hcls⟩ : ∃ cls : Fin n → Fin 3 → ℕ,
      cls = fun i m => ⌊(sgnNormal (nrm i) m + 1) / η⌋₊ := ⟨_, rfl⟩
  obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = ⌊16 / θ⌋₊ + 1 := ⟨_, rfl⟩
  obtain ⟨T, hT_def⟩ : ∃ T : Finset (Fin 3 → ℕ),
      T = Fintype.piFinset fun _ => Finset.range M := ⟨_, rfl⟩
  have hclsT : ∀ i ∈ K, cls i ∈ T := by
    intro i hi
    rw [hT_def, Fintype.mem_piFinset]
    intro m
    rw [Finset.mem_range, hM_def]
    simp only [hcls]
    have h1 := abs_le.mp (hcoord1 i hi m)
    have h2 : (sgnNormal (nrm i) m + 1) / η ≤ 16 / θ := by
      rw [div_le_iff₀ hη, hη_def]
      field_simp
      linarith
    have h3 := Nat.floor_le_floor h2
    omega
  -- indices in the same class have close normalised normals
  have hclose : ∀ i ∈ K, ∀ i' ∈ K, cls i = cls i' →
      ‖sgnNormal (nrm i) - sgnNormal (nrm i')‖ ≤ θ / 4 := by
    intro i hi i' hi' heq
    have hc : ∀ m : Fin 3, |sgnNormal (nrm i) m - sgnNormal (nrm i') m| ≤ η := by
      intro m
      have hfl : ⌊(sgnNormal (nrm i) m + 1) / η⌋₊ = ⌊(sgnNormal (nrm i') m + 1) / η⌋₊ := by
        have h := congrFun heq m
        rw [hcls] at h
        exact h
      have ha := abs_le.mp (hcoord1 i hi m)
      have hb := abs_le.mp (hcoord1 i' hi' m)
      have hx0 : 0 ≤ (sgnNormal (nrm i) m + 1) / η := div_nonneg (by linarith) hη.le
      have hy0 : 0 ≤ (sgnNormal (nrm i') m + 1) / η := div_nonneg (by linarith) hη.le
      have e1 := Nat.floor_le hx0
      have e2 := Nat.lt_floor_add_one ((sgnNormal (nrm i) m + 1) / η)
      have e3 := Nat.floor_le hy0
      have e4 := Nat.lt_floor_add_one ((sgnNormal (nrm i') m + 1) / η)
      rw [hfl] at e1 e2
      have h5 : |(sgnNormal (nrm i) m + 1) / η - (sgnNormal (nrm i') m + 1) / η| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      rw [← sub_div, abs_div, abs_of_pos hη, div_le_one hη] at h5
      simpa using h5
    have hsq : ‖sgnNormal (nrm i) - sgnNormal (nrm i')‖ ^ 2 ≤ (θ / 4) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      simp only [PiLp.sub_apply]
      have s : ∀ m : Fin 3, (sgnNormal (nrm i) m - sgnNormal (nrm i') m) ^ 2 ≤ η ^ 2 := by
        intro m
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc m) 2
      have s0 := s 0
      have s1 := s 1
      have s2 := s 2
      rw [hη_def] at s0 s1 s2
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) (by norm_num)).mp hsq
  -- the classes cover `Y`
  obtain ⟨B, hB⟩ : ∃ B : (Fin 3 → ℕ) → Set Space,
      B = fun γ => Y ∩ ⋃ i ∈ K.filter (fun i => cls i = γ), A i := ⟨_, rfl⟩
  have hcover : Y ⊆ ⋃ γ ∈ T, B γ := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ : ∃ i ∈ K, y ∈ A i := by simpa using hY hy
    simp only [Set.mem_iUnion]
    refine ⟨cls i, hclsT i hi, ?_⟩
    rw [hB]
    refine ⟨hy, ?_⟩
    simp only [Set.mem_iUnion]
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hyi⟩
  have hTne : T.Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    rw [hT_def, Fintype.mem_piFinset]
    intro m
    rw [Finset.mem_range, hM_def]
    omega
  -- the heaviest class
  obtain ⟨γ₀, hγ₀T, hγ₀max⟩ := Finset.exists_max_image T (fun γ => volume (B γ)) hTne
  refine ⟨K.filter (fun i => cls i = γ₀), Finset.filter_subset _ _, ?_, ?_⟩
  · intro i hi i' hi'
    rw [Finset.mem_filter] at hi hi'
    exact hclose i hi.1 i' hi'.1 (hi.2.trans hi'.2.symm)
  · have hBγ₀ : B γ₀ = Y ∩ ⋃ i ∈ K.filter (fun i => cls i = γ₀), A i := by rw [hB]
    rw [← hBγ₀]
    have hvol : volume Y ≤ T.card * volume (B γ₀) := by
      calc volume Y ≤ volume (⋃ γ ∈ T, B γ) := measure_mono hcover
        _ ≤ ∑ γ ∈ T, volume (B γ) := measure_biUnion_finset_le T B
        _ ≤ T.card • volume (B γ₀) := Finset.sum_le_card_nsmul _ _ _ hγ₀max
        _ = T.card * volume (B γ₀) := nsmul_eq_mul _ _
    have hcard : (T.card : ℝ) ≤ (17 / θ) ^ 3 := by
      rw [hT_def, Fintype.card_piFinset_const, Finset.card_range]
      push_cast
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      rw [hM_def]
      push_cast
      have h1 := Nat.floor_le (show 0 ≤ 16 / θ by positivity)
      have h2 : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ]; linarith
      calc (⌊16 / θ⌋₊ : ℝ) + 1 ≤ 16 / θ + 1 / θ := by linarith
        _ = 17 / θ := by ring
    have hfac : (T.card : ℝ≥0∞) * ENNReal.ofReal (θ ^ 3 / 100000) ≤ 1 := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_le_one]
      calc (T.card : ℝ) * (θ ^ 3 / 100000) ≤ (17 / θ) ^ 3 * (θ ^ 3 / 100000) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 4913 / 100000 := by field_simp; ring
        _ ≤ 1 := by norm_num
    calc volume Y * ENNReal.ofReal (θ ^ 3 / 100000)
        ≤ T.card * volume (B γ₀) * ENNReal.ofReal (θ ^ 3 / 100000) := by gcongr
      _ = volume (B γ₀) * (T.card * ENNReal.ofReal (θ ^ 3 / 100000)) := by ring
      _ ≤ volume (B γ₀) * 1 := by gcongr
      _ = volume (B γ₀) := mul_one _

/-- A unit vector at projective distance `≥ θ` from the unit vector `e₀` has a component
`≥ θ / 2` along a unit vector orthogonal to `e₀`. -/
theorem exists_good_direction {e₀ n : Space} (he : ‖e₀‖ = 1) (hn : ‖n‖ = 1) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ pd n e₀) :
    ∃ v : Space, ‖v‖ = 1 ∧ inner ℝ e₀ v = 0 ∧ θ / 2 ≤ inner ℝ n v := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, inner ℝ n e₀ = c := ⟨_, rfl⟩
  have hc' : inner ℝ e₀ n = c := by rw [real_inner_comm]; exact hc
  have h1 : θ ≤ ‖n - e₀‖ := hθ.trans (min_le_left _ _)
  have h2 : θ ≤ ‖n + e₀‖ := hθ.trans (min_le_right _ _)
  have h1' : θ ^ 2 ≤ 2 - 2 * c := by
    have h := pow_le_pow_left₀ hθ0 h1 2
    rw [norm_sub_sq_real, hn, he, hc] at h
    linarith
  have h2' : θ ^ 2 ≤ 2 + 2 * c := by
    have h := pow_le_pow_left₀ hθ0 h2 2
    rw [norm_add_sq_real, hn, he, hc] at h
    linarith
  have hc1 : |c| ≤ 1 := by
    have h := abs_real_inner_le_norm n e₀
    rwa [hn, he, hc, one_mul] at h
  -- `1 - c² = (1 - c) (1 + c) ≥ θ² / 2`
  have hkey : θ ^ 2 / 2 ≤ 1 - c ^ 2 := by
    have h := abs_le.mp hc1
    nlinarith [mul_nonneg (sub_nonneg.2 h1') (by linarith : (0 : ℝ) ≤ 1 + c),
      mul_nonneg (sub_nonneg.2 h2') (by linarith : (0 : ℝ) ≤ 1 - c)]
  -- the component of `n` orthogonal to `e₀`
  obtain ⟨β, hβ_def⟩ : ∃ β : Space, β = n - c • e₀ := ⟨_, rfl⟩
  have hβe : inner ℝ e₀ β = 0 := by
    rw [hβ_def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he, hc']
    ring
  have hβ2 : ‖β‖ ^ 2 = 1 - c ^ 2 := by
    rw [hβ_def, norm_sub_sq_real, norm_smul, real_inner_smul_right, hn, he, hc,
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hnβ : inner ℝ n β = 1 - c ^ 2 := by
    rw [hβ_def, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hn, hc]
    ring
  by_cases hβ0 : ‖β‖ = 0
  · -- then `θ = 0` and any unit vector orthogonal to `e₀` will do
    have hθz : θ = 0 := by
      have h : θ ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h (sq_nonneg θ))
    obtain ⟨v, hv, hve⟩ :=
      WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_unit_perp he
    have hβz : β = 0 := norm_eq_zero.mp hβ0
    have hn_eq : n = c • e₀ := by
      rw [hβ_def] at hβz
      exact sub_eq_zero.mp hβz
    refine ⟨v, hv, by rw [real_inner_comm]; exact hve, ?_⟩
    rw [hn_eq, real_inner_smul_left, real_inner_comm, hve, mul_zero, hθz]
    norm_num
  · refine ⟨‖β‖⁻¹ • β, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hβ0]
    · rw [real_inner_smul_right, hβe, mul_zero]
    · rw [real_inner_smul_right, hnβ, ← hβ2, pow_two, ← mul_assoc, inv_mul_cancel₀ hβ0,
        one_mul]
      have h3 : (θ / 2) ^ 2 ≤ ‖β‖ ^ 2 := by rw [hβ2]; nlinarith
      exact (pow_le_pow_iff_left₀ (by linarith) (norm_nonneg _) (by norm_num)).mp h3

end

end WangZahlLot.Obl.wz_transverse_cell_weighted_cover
