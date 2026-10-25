-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_strict_improvement.Slab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_strict_improvement.Estimates

namespace WangZahlLot.Obl.wz_strict_improvement

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

/-- A unit direction can be used as the first vector of an orthonormal frame. -/
theorem exists_basis_with_first {v : Space} (hv : ‖v‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space, b 0 = v := by
  have horth : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => v)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hv
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by simp [LeanEval.Analysis.WangZahlKakeya.Space])
  exact ⟨b, hb 0 (by simp)⟩

/-- A unit-ball slab has volume at most that of its containing rectangular box. -/
theorem volume_slab_le (b : OrthonormalBasis (Fin 3) ℝ Space) (t r : ℝ) (hr : 0 ≤ r) :
    volume (Slab (b 1) t r) ≤ ENNReal.ofReal (8 * r) := by
  let lo : Fin 3 → ℝ := ![-1, t - r, -1]
  let hi : Fin 3 → ℝ := ![1, t + r, 1]
  let f : Space → Fin 3 → ℝ := fun p => WithLp.ofLp (b.repr p)
  have hf : MeasurePreserving f volume volume :=
    (PiLp.volume_preserving_ofLp (Fin 3)).comp b.measurePreserving_repr
  have hbox : volume (f ⁻¹' Set.Icc lo hi) = ENNReal.ofReal (8 * r) := by
    rw [hf.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    calc
      (∏ i : Fin 3, ENNReal.ofReal (hi i - lo i)) =
          ENNReal.ofReal 2 * ENNReal.ofReal (2 * r) * ENNReal.ofReal 2 := by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
        change ENNReal.ofReal (1 - -1) *
          (ENNReal.ofReal (t + r - (t - r)) * ENNReal.ofReal (1 - -1)) = _
        rw [show (1 : ℝ) - -1 = 2 by norm_num, show t + r - (t - r) = 2 * r by ring]
        exact (mul_assoc _ _ _).symm
      _ = ENNReal.ofReal (8 * r) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  rw [← hbox]
  apply measure_mono
  intro p hp
  have hpball : ‖p‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hp.1
  have habs (i : Fin 3) : |b.repr p i| ≤ 1 := by
    have := (PiLp.norm_apply_le (b.repr p) i).trans_lt
      (show ‖b.repr p‖ < 1 by simpa using hpball)
    exact le_of_lt (by simpa only [Real.norm_eq_abs] using this)
  have h0 := abs_le.mp (habs 0)
  have h2 := abs_le.mp (habs 2)
  have h1 : |b.repr p 1 - t| ≤ r := by
    rw [b.repr_apply_apply]
    exact hp.2
  rcases abs_le.mp h1 with ⟨h1lo, h1hi⟩
  change (∀ i, lo i ≤ f p i) ∧ (∀ i, f p i ≤ hi i)
  constructor <;> intro i <;> fin_cases i
  · change -1 ≤ b.repr p 0
    exact h0.1
  · change t - r ≤ b.repr p 1
    linarith
  · change -1 ≤ b.repr p 2
    exact h2.1
  · change b.repr p 0 ≤ 1
    exact h0.2
  · change b.repr p 1 ≤ t + r
    linarith
  · change b.repr p 2 ≤ 1
    exact h2.2

/-- The neighborhood of a segment lies in every perpendicular slab of its radius. -/
theorem tube_subset_perpendicular_slab {δ : ℝ} {x v u : Space}
    (hu : ‖u‖ = 1) (huv : inner ℝ u v = 0)
    (hball : Tube δ x v ⊆ Metric.ball (0 : Space) 1) :
    Tube δ x v ⊆ Slab u (inner ℝ u x) δ := by
  intro p hp
  refine ⟨hball hp, ?_⟩
  change |inner ℝ u p - inner ℝ u x| ≤ δ
  obtain ⟨z, hz, hpz⟩ := Metric.mem_thickening_iff.mp hp
  have hzinner : inner ℝ u z = inner ℝ u x := by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    simp only [inner_add_right, inner_smul_right, huv, add_zero]
    rw [← add_mul, hab, one_mul]
  rw [← hzinner, ← inner_sub_right]
  have hinner := abs_real_inner_le_norm u (p - z)
  rw [hu, one_mul] at hinner
  exact hinner.trans (le_of_lt (by simpa only [dist_eq_norm] using hpz))

/-- Testing the slab bound on a slab containing one tube controls `n * δ` from below. -/
theorem frostman_cardinality_lower {n : ℕ} {δ η : ℝ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1)
    (hF : FrostmanSlab δ (δ ^ (-η)) x v) :
    δ ^ η ≤ 8 * ((n : ℝ) * δ) := by
  let i : Fin n := ⟨0, hn⟩
  obtain ⟨b, hb⟩ := exists_basis_with_first (hv i)
  have huv : inner ℝ (b 1) (v i) = 0 := by
    rw [← hb]
    exact b.orthonormal.2 (by decide : (1 : Fin 3) ≠ 0)
  have hcontains := tube_subset_perpendicular_slab (b.orthonormal.1 1) huv (hball i)
  let t := inner ℝ (b 1) (x i)
  have hcard : (1 : ℝ) ≤ ({j : Fin n | Tube δ (x j) (v j) ⊆ Slab (b 1) t δ}.ncard : ℝ) := by
    have hnonempty : Set.Nonempty {j : Fin n | Tube δ (x j) (v j) ⊆ Slab (b 1) t δ} :=
      ⟨i, hcontains⟩
    exact_mod_cast Nat.succ_le_of_lt hnonempty.ncard_pos
  have hcount := hF (b 1) t δ (b.orthonormal.1 1) hδ
  have hreal : 1 ≤ (δ ^ (-η) * (n : ℝ)) * (8 * δ) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    calc
      ENNReal.ofReal 1 ≤ _ := ENNReal.ofReal_le_ofReal hcard
      _ ≤ _ := hcount
      _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * ENNReal.ofReal (8 * δ) :=
        mul_le_mul_right (volume_slab_le b t δ hδ.le) _
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hcancel : δ ^ η * δ ^ (-η) = 1 := by
    rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
  calc
    δ ^ η = δ ^ η * 1 := (mul_one _).symm
    _ ≤ δ ^ η * ((δ ^ (-η) * (n : ℝ)) * (8 * δ)) :=
      mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg hδ.le _)
    _ = (δ ^ η * δ ^ (-η)) * (8 * ((n : ℝ) * δ)) := by ring
    _ = 8 * ((n : ℝ) * δ) := by rw [hcancel, one_mul]

end WangZahlLot.Obl.wz_strict_improvement
