-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.MultipleGrids.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GridRegularization

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridCell gridUnion)

lemma shading_density_of_mass_retention {d θ ζ : ℝ} (hd : 0 < d) {n : ℕ}
    {Y Z : Fin n → Set Space}
    (hmass : ENNReal.ofReal (d ^ θ * n * d ^ 2) ≤ ∑ i, volume (Y i))
    (hret : ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    ENNReal.ofReal (d ^ (θ + ζ) * n * d ^ 2) ≤ ∑ i, volume (Z i) := by
  have he : d ^ (θ + ζ) * n * d ^ 2 = d ^ ζ * (d ^ θ * n * d ^ 2) := by
    rw [Real.rpow_add hd]
    ring
  rw [he, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
  exact (mul_le_mul' le_rfl hmass).trans hret

/-- Simultaneous density classes at a fixed finite list of meshes. All classes
refer to the original union, while the final shadings lie in every selected grid.
Thus later restriction does not change the reference densities in the product. -/
theorem regularize_multiple_grids (B : ℕ) {ζ D : ℝ} (hζ : 0 < ζ) (hD : 0 < D) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧
      ∀ d θ : ℝ, 0 < d → d ≤ d₀ → θ ≤ 1 / 2 →
      ∀ a : ℕ → ℝ, (∀ j, j < B → 0 < a j ∧ a j ≤ 1) →
      ∀ (n : ℕ) (Y : Fin n → Set Space),
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ ball 0 1) →
      ENNReal.ofReal (d ^ θ * n * d ^ 2) ≤ ∑ i, volume (Y i) →
      ∃ (Z : Fin n → Set Space) (S : ℕ → Finset (Fin 3 → ℤ)) (t : ℕ → ℝ),
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
        ∀ j, j < B → 0 < t j ∧ (∀ i, Z i ⊆ gridUnion (a j) (S j)) ∧
          ∀ z ∈ S j, t j * (a j) ^ 3 ≤ volume.real ((⋃ i, Y i) ∩ gridCell (a j) z) ∧
            d ^ ζ * volume.real ((⋃ i, Y i) ∩ gridCell (a j) z) ≤ t j * (a j) ^ 3 := by
  classical
  let τ : ℝ := min ζ (1 / 2) / (B + 1)
  have hmin : 0 < min ζ (1 / 2) := lt_min hζ (by norm_num)
  have hden : 0 < (B : ℝ) + 1 := by positivity
  have hτ : 0 < τ := div_pos hmin hden
  have hτζ : τ ≤ ζ := (div_le_self hmin.le (by have := Nat.cast_nonneg (α := ℝ) B; linarith)).trans
    (min_le_left _ _)
  have hBτ : (B : ℝ) * τ ≤ min ζ (1 / 2) := by
    dsimp [τ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  obtain ⟨d₀, hd₀, hd₀D, H⟩ := regularize_grid_relative hτ (lt_min hD zero_lt_one)
  refine ⟨d₀, hd₀, hd₀D.trans (min_le_left D 1), ?_⟩
  intro d θ hd hdd hθ a ha n Y hYm hYB hmass
  have hd1 : d ≤ 1 := hdd.trans (hd₀D.trans (min_le_right D 1))
  let E : Set Space := ⋃ i, Y i
  have hE : MeasurableSet E := MeasurableSet.iUnion hYm
  have hbuild : ∀ J : ℕ, J ≤ B →
      ∃ (Z : Fin n → Set Space) (S : ℕ → Finset (Fin 3 → ℤ)) (t : ℕ → ℝ),
        (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
        ENNReal.ofReal (d ^ ((J : ℝ) * τ)) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
        ∀ j, j < J → 0 < t j ∧ (∀ i, Z i ⊆ gridUnion (a j) (S j)) ∧
          ∀ z ∈ S j, t j * (a j) ^ 3 ≤ volume.real (E ∩ gridCell (a j) z) ∧
            d ^ τ * volume.real (E ∩ gridCell (a j) z) ≤ t j * (a j) ^ 3 := by
    intro J
    induction J with
    | zero =>
        intro _
        exact ⟨Y, fun _ => ∅, fun _ => 1, fun i => ⟨hYm i, Subset.rfl⟩,
          by simp, fun j hj => by omega⟩
    | succ J ih =>
        intro hJB
        obtain ⟨Z, S, t, hZ, hret, hclasses⟩ := ih (by omega)
        have hJτ : (J : ℝ) * τ ≤ 1 / 2 :=
          ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show J ≤ B by omega)) hτ.le).trans
            hBτ).trans (min_le_right _ _)
        have hZmass := shading_density_of_mass_retention hd hmass hret
        obtain ⟨Snew, tnew, htnew, hZnew, hretain, hclass, _⟩ :=
          H d (θ + J * τ) (a J) hd hdd (by linarith) (ha J (by omega)).1 (ha J (by omega)).2
            n Z (fun i => (hZ i).1) (fun i => (hZ i).2.trans (hYB i)) E hE
            (fun i => (hZ i).2.trans (subset_iUnion Y i)) hZmass
        refine ⟨fun i => Z i ∩ gridUnion (a J) Snew, Function.update S J Snew,
          Function.update t J tnew, fun i => ⟨hZnew i, inter_subset_left.trans (hZ i).2⟩, ?_, ?_⟩
        · have he : ((J + 1 : ℕ) : ℝ) * τ = τ + J * τ := by push_cast; ring
          rw [he, Real.rpow_add hd, ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _), mul_assoc]
          exact (mul_le_mul' le_rfl hret).trans hretain
        · intro j hj
          by_cases he : j = J
          · subst j
            simpa only [Function.update_self] using
              (show 0 < tnew ∧
                (∀ i, Z i ∩ gridUnion (a J) Snew ⊆ gridUnion (a J) Snew) ∧
                ∀ z ∈ Snew, tnew * (a J) ^ 3 ≤ volume.real (E ∩ gridCell (a J) z) ∧
                  d ^ τ * volume.real (E ∩ gridCell (a J) z) ≤ tnew * (a J) ^ 3 from
                ⟨htnew, fun _ => inter_subset_right, hclass⟩)
          · obtain ⟨htj, hZj, hclassj⟩ := hclasses j (by omega)
            simpa only [Function.update_of_ne he] using
              (show 0 < t j ∧
                (∀ i, Z i ∩ gridUnion (a J) Snew ⊆ gridUnion (a j) (S j)) ∧
                ∀ z ∈ S j, t j * (a j) ^ 3 ≤ volume.real (E ∩ gridCell (a j) z) ∧
                  d ^ τ * volume.real (E ∩ gridCell (a j) z) ≤ t j * (a j) ^ 3 from
                ⟨htj, fun i => inter_subset_left.trans (hZj i), hclassj⟩)
  obtain ⟨Z, S, t, hZ, hret, hclasses⟩ := hbuild B le_rfl
  refine ⟨Z, S, t, hZ, ?_, ?_⟩
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (hBτ.trans (min_le_left _ _)))) le_rfl).trans hret
  · intro j hj
    obtain ⟨htj, hZj, hclassj⟩ := hclasses j hj
    refine ⟨htj, hZj, fun z hz => ⟨(hclassj z hz).1, ?_⟩⟩
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hd hd1 hτζ)
      measureReal_nonneg).trans (hclassj z hz).2

end WangZahlLot.Obl.wz_multiscale_finite_tower
