-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_strict_improvement.TubeVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_strict_improvement.Slab

namespace WangZahlLot.Obl.wz_strict_improvement

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

/-- A unit tube fits in a box of dimensions `1+2δ`, `2δ`, `2δ`. -/
theorem volume_tube_le_box {δ : ℝ} {x v : Space} (hδ : 0 ≤ δ) (hv : ‖v‖ = 1) :
    volume (Tube δ x v) ≤ ENNReal.ofReal ((1 + 2 * δ) * (2 * δ) * (2 * δ)) := by
  obtain ⟨b, hb⟩ := exists_basis_with_first hv
  let c : Fin 3 → ℝ := fun i => inner ℝ (b i) x
  let lo : Fin 3 → ℝ := ![c 0 - δ, c 1 - δ, c 2 - δ]
  let hi : Fin 3 → ℝ := ![c 0 + 1 + δ, c 1 + δ, c 2 + δ]
  let f : Space → Fin 3 → ℝ := fun p => WithLp.ofLp (b.repr p)
  have hf : MeasurePreserving f volume volume :=
    (PiLp.volume_preserving_ofLp (Fin 3)).comp b.measurePreserving_repr
  have hbox : volume (f ⁻¹' Set.Icc lo hi) =
      ENNReal.ofReal ((1 + 2 * δ) * (2 * δ) * (2 * δ)) := by
    rw [hf.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change ENNReal.ofReal (c 0 + 1 + δ - (c 0 - δ)) *
      (ENNReal.ofReal (c 1 + δ - (c 1 - δ)) * ENNReal.ofReal (c 2 + δ - (c 2 - δ))) = _
    rw [show c 0 + 1 + δ - (c 0 - δ) = 1 + 2 * δ by ring,
      show c 1 + δ - (c 1 - δ) = 2 * δ by ring,
      show c 2 + δ - (c 2 - δ) = 2 * δ by ring,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [← hbox]
  apply measure_mono
  intro p hp
  obtain ⟨z, hz, hpz⟩ := Metric.mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hpz
  have hcoord (i : Fin 3) :
      |inner ℝ (b i) p - (c i + t * inner ℝ (b i) v)| ≤ δ := by
    have hinner := abs_real_inner_le_norm (b i) (p - (x + t • v))
    rw [b.norm_eq_one, one_mul] at hinner
    have hd : ‖p - (x + t • v)‖ ≤ δ := by
      exact le_of_lt (by simpa only [dist_eq_norm] using hpz)
    simpa only [inner_sub_right, inner_add_right, inner_smul_right, c] using hinner.trans hd
  have h00 : inner ℝ (b 0) v = 1 := by
    rw [← hb]
    simp
  have h10 : inner ℝ (b 1) v = 0 := by
    rw [← hb]
    exact b.orthonormal.2 (by decide : (1 : Fin 3) ≠ 0)
  have h20 : inner ℝ (b 2) v = 0 := by
    rw [← hb]
    exact b.orthonormal.2 (by decide : (2 : Fin 3) ≠ 0)
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  simp only [h00, mul_one] at h0
  simp only [h10, mul_zero, add_zero] at h1
  simp only [h20, mul_zero, add_zero] at h2
  rcases abs_le.mp h0 with ⟨h0lo, h0hi⟩
  rcases abs_le.mp h1 with ⟨h1lo, h1hi⟩
  rcases abs_le.mp h2 with ⟨h2lo, h2hi⟩
  change (∀ i, lo i ≤ f p i) ∧ (∀ i, f p i ≤ hi i)
  constructor <;> intro i <;> fin_cases i
  · change c 0 - δ ≤ b.repr p 0
    rw [b.repr_apply_apply]
    linarith [ht.1]
  · change c 1 - δ ≤ b.repr p 1
    rw [b.repr_apply_apply]
    linarith
  · change c 2 - δ ≤ b.repr p 2
    rw [b.repr_apply_apply]
    linarith
  · change b.repr p 0 ≤ c 0 + 1 + δ
    rw [b.repr_apply_apply]
    linarith [ht.2]
  · change b.repr p 1 ≤ c 1 + δ
    rw [b.repr_apply_apply]
    linarith
  · change b.repr p 2 ≤ c 2 + δ
    rw [b.repr_apply_apply]
    linarith

theorem volume_tube_le {δ : ℝ} {x v : Space}
    (hδ : 0 ≤ δ) (hδmax : δ ≤ (1 / 2 : ℝ)) (hv : ‖v‖ = 1) :
    volume (Tube δ x v) ≤ ENNReal.ofReal (8 * δ ^ 2) := by
  apply (volume_tube_le_box hδ hv).trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [mul_nonneg (sq_nonneg δ) (show 0 ≤ 1 - 2 * δ by linarith)]

/-- A mass bound for shadings, independent of their overlap. -/
theorem shading_mass_le {n : ℕ} {δ : ℝ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 ≤ δ) (hδmax : δ ≤ (1 / 2 : ℝ))
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i)) :
    ∑ i, volume (Y i) ≤ ENNReal.ofReal (8 * (n : ℝ) * δ ^ 2) := by
  calc
    ∑ i, volume (Y i) ≤ ∑ _i : Fin n, ENNReal.ofReal (8 * δ ^ 2) := by
      exact Finset.sum_le_sum (fun i _ =>
        (measure_mono (hY i)).trans (volume_tube_le hδ hδmax (hv i)))
    _ = ENNReal.ofReal (8 * (n : ℝ) * δ ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring

/-- Retaining a fraction of the shading mass retains a controlled number of tubes. -/
theorem cardinality_of_retained_mass {n m : ℕ} {δ η θ : ℝ}
    {Y : Fin n → Set Space} {Z : Fin m → Set Space} {x v : Fin m → Space}
    (hδ : 0 < δ) (hδmax : δ ≤ (1 / 2 : ℝ))
    (hv : ∀ i, ‖v i‖ = 1) (hZ : ∀ i, Z i ⊆ Tube δ (x i) (v i))
    (hdense : Dense δ η Y)
    (hretain : ENNReal.ofReal (δ ^ θ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    δ ^ (η + θ) * (n : ℝ) ≤ 8 * (m : ℝ) := by
  have hreal : δ ^ θ * (δ ^ η * (n : ℝ) * δ ^ 2) ≤ 8 * (m : ℝ) * δ ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    exact (mul_le_mul_right hdense _).trans
      (hretain.trans (shading_mass_le hδ.le hδmax hv hZ))
  have hpow : δ ^ θ * δ ^ η = δ ^ (η + θ) := by
    rw [← Real.rpow_add hδ, add_comm]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp
  calc
    δ ^ (η + θ) * (n : ℝ) * δ ^ 2 = δ ^ θ * (δ ^ η * (n : ℝ) * δ ^ 2) := by
      rw [← hpow]
      ring
    _ ≤ 8 * (m : ℝ) * δ ^ 2 := hreal

end WangZahlLot.Obl.wz_strict_improvement
