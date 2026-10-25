-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Mesh.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Budgets

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

/-- A bounded logarithmic mesh has room for fixed enlargement factors and for
the small errors in the supplied scale selection. -/
theorem choose_mesh_depth {a : ℝ} (ha : 0 < a) :
    ∃ J : ℕ, 0 < J ∧ ∃ t : ℝ, 0 < t ∧ t * J = 1 ∧ 4 * t ≤ a := by
  obtain ⟨J, hJ, hgap⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_net_size (by positivity : 0 < a / 4)
  refine ⟨J, hJ, (J : ℝ)⁻¹, by positivity, ?_, by linarith⟩
  exact inv_mul_cancel₀ (by exact_mod_cast hJ.ne')

/-- Scalar budgets for the raw geometric mesh, uniform over every smaller
choice of the cover error. -/
theorem mesh_cutoff {a t : ℝ} (ht : 0 < t) (hta : 4 * t ≤ a) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ η : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d →
      0 < η → η ≤ t / 2 →
      δ ^ (-η) * δ ^ t ≤ (1 / 51200 : ℝ) ∧
      32 * δ ^ (a / 2) * δ ^ (-η) ≤ δ ^ t ∧
      δ ^ (a / 2) ≤ (1 / 100 : ℝ) := by
  obtain ⟨d, hd, hsmall⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (show 0 < t / 2 by positivity) (show (0 : ℝ) < 1 / 51200 by norm_num)
  refine ⟨d, hd, ?_⟩
  intro δ η hδ hδ1 hδd hη hηt
  have hs := hsmall δ hδ hδd
  have hq : δ ^ (-η) * δ ^ t ≤ δ ^ (t / 2) := by
    rw [← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hgap : δ ^ (a / 2 - η - t) ≤ δ ^ (t / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have he : 32 * δ ^ (a / 2) * δ ^ (-η) =
      (32 * δ ^ (a / 2 - η - t)) * δ ^ t := by
    rw [mul_assoc, ← Real.rpow_add hδ, mul_assoc, ← Real.rpow_add hδ]
    congr 2
    ring
  refine ⟨hq.trans hs, ?_, ?_⟩
  · rw [he]
    have hcoef : 32 * δ ^ (a / 2 - η - t) ≤ 1 := by linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hδ.le t)
  · have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show t / 2 ≤ a / 2 by linarith)
    exact hh.trans (hs.trans (by norm_num))

/-- Insert a fixed small root and the exact bottom radius into the raw cover
scales. The enlarged interior scales retain separation and the desired mesh gap. -/
theorem buffered_mesh {δ a b q : ℝ} {J : ℕ}
    (hδ : 0 < δ) (hJ : 0 < J) (hb : 0 < b) (hb1 : b ≤ 1)
    (hbJ : b ^ J = δ) (hq : 1 ≤ q)
    (hsmall : q * b ≤ (1 / 51200 : ℝ))
    (hgap : 32 * δ ^ (a / 2) * q ≤ b)
    (s : ℕ → ℝ) (hs0 : s 0 = (1 / 3200 : ℝ)) (hsJ : s J = δ)
    (hs : ∀ j, 0 < j → j ≤ J → b ^ j ≤ s j ∧ s j ≤ q * b ^ j) :
    let r := fun j => if j < J then 32 * s j else δ
    r 0 = (1 / 100 : ℝ) ∧ r J = δ ∧
    (∀ j, j ≤ J → 0 < s j ∧ r j ≤ 32 * s j ∧ δ ≤ r j ∧ r j ≤ 1 / 100) ∧
    (∀ j, 0 < j → j ≤ J → s j ≤ 1 / 51200) ∧
    (∀ j, j < J → r j = 32 * s j ∧ 16 * s (j + 1) ≤ s j ∧
      16 * r (j + 1) ≤ r j ∧ δ ^ (a / 2) * r j ≤ r (j + 1)) := by
  intro r
  have hspos (j) (hj : j ≤ J) : 0 < s j := by
    by_cases hj0 : j = 0
    · rw [hj0, hs0]; norm_num
    · exact (pow_pos hb j).trans_le (hs j (by omega) hj).1
  have hbound (j) (hj0 : 0 < j) (hj : j ≤ J) : s j ≤ 1 / 51200 := by
    calc
      s j ≤ q * b ^ j := (hs j hj0 hj).2
      _ ≤ q * b := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ j by omega)
      _ ≤ _ := hsmall
  have hbsmall : b ≤ 1 / 51200 := (le_mul_of_one_le_left hb.le hq).trans hsmall
  have hδb : δ ≤ b := by
    rw [← hbJ]
    simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ J by omega)
  have hrupper (j) (hj : j ≤ J) : r j ≤ 32 * s j := by
    dsimp [r]
    split_ifs with hjlt
    · rfl
    · have he : j = J := by omega
      rw [he, hsJ]
      linarith
  have hrlower (j) (hj : j ≤ J) : s j ≤ r j := by
    dsimp [r]
    split_ifs with hjlt
    · linarith [hspos j hj]
    · have he : j = J := by omega
      rw [he, hsJ]
  have hr0 : r 0 = 1 / 100 := by simp only [r, ite_eq_left hJ, hs0]; norm_num
  refine ⟨hr0, by simp [r], ?_, hbound, ?_⟩
  · intro j hj
    refine ⟨hspos j hj, hrupper j hj, ?_, ?_⟩
    · by_cases hj0 : j = 0
      · rw [hj0, hr0]
        linarith
      · apply le_trans _ (hrlower j hj)
        calc
          δ = b ^ J := hbJ.symm
          _ ≤ b ^ j := pow_le_pow_of_le_one hb.le hb1 hj
          _ ≤ s j := (hs j (by omega) hj).1
    · by_cases hj0 : j = 0
      · rw [hj0, hr0]
      · have hbnd := hbound j (by omega) hj
        linarith [hrupper j hj]
  · intro j hj
    have hreq : r j = 32 * s j := by simp only [r, ite_eq_left hj]
    have hsep : 16 * s (j + 1) ≤ s j := by
      by_cases hj0 : j = 0
      · rw [hj0, hs0]
        have hh := hbound (j + 1) (by omega) (by omega)
        subst j
        linarith
      · calc
          16 * s (j + 1) ≤ 16 * (q * b ^ (j + 1)) :=
            mul_le_mul_of_nonneg_left (hs (j + 1) (by omega) (by omega)).2 (by norm_num)
          _ = (16 * (q * b)) * b ^ j := by rw [pow_succ]; ring
          _ ≤ 1 * b ^ j := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb.le j)
            linarith
          _ ≤ s j := by simpa only [one_mul] using (hs j (by omega) (by omega)).1
    refine ⟨hreq, hsep, ?_, ?_⟩
    · rw [hreq]
      linarith [hrupper (j + 1) (by omega)]
    · have hg0 : 0 ≤ δ ^ (a / 2) := Real.rpow_nonneg hδ.le _
      have hq0 : 0 ≤ q := by linarith
      have hgsmall : 32 * δ ^ (a / 2) ≤ b :=
        (le_mul_of_one_le_right (by positivity) hq).trans hgap
      by_cases hj0 : j = 0
      · rw [hj0, hr0]
        have hh := (hs 1 (by omega) (by omega)).1
        simp only [pow_one] at hh
        have hh' := hrlower 1 (by omega)
        norm_num only at *
        linarith
      · rw [hreq]
        calc
          δ ^ (a / 2) * (32 * s j) ≤ δ ^ (a / 2) * (32 * (q * b ^ j)) := by
            gcongr
            exact (hs j (by omega) (by omega)).2
          _ = (32 * δ ^ (a / 2) * q) * b ^ j := by ring
          _ ≤ b * b ^ j := mul_le_mul_of_nonneg_right hgap (pow_nonneg hb.le j)
          _ = b ^ (j + 1) := by rw [pow_succ]; ring
          _ ≤ s (j + 1) := (hs (j + 1) (by omega) (by omega)).1
          _ ≤ r (j + 1) := hrlower (j + 1) (by omega)

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
