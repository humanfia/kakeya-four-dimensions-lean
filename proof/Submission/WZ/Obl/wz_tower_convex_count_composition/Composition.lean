-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_convex_count_composition.Composition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_convex_count_composition.Geometry
import Submission.WZ.Obl.wz_tower_convex_count_composition.Containment

namespace WangZahlLot.Obl.wz_tower_convex_count_composition

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Counts (r L : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W, Convex ℝ W → ENNReal.ofReal ((Set.ncard {i | Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2) ≤
    ENNReal.ofReal L * volume W

theorem counts_mono {r L M : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Counts r L n x v) (hLM : L ≤ M) : Counts r M n x v := by
  intro W hW
  exact (h W hW).trans (by gcongr)

/-- A single unit-radius tube obeys the normalized convex count with constant one. -/
theorem counts_root {n : ℕ} (hn : n = 1) (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1) :
    Counts 1 1 n x v := by
  intro W _
  let S : Set (Fin n) := {i | Tube 1 (x i) (v i) ⊆ W}
  change ENNReal.ofReal ((S.ncard : ℝ) * 1 ^ 2) ≤ ENNReal.ofReal 1 * volume W
  rcases S.eq_empty_or_nonempty with he | ⟨i, hi⟩
  · simp [he]
  · have hc : S.ncard ≤ 1 := by
      simpa [hn] using Set.ncard_le_card S
    have hl := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower
      (show (0 : ℝ) < 1 by norm_num) (x i) (v i) (hv i)
    have hvol : ENNReal.ofReal (1 : ℝ) ≤ volume W := by
      simpa using hl.trans (measure_mono hi)
    simpa using (ENNReal.ofReal_le_ofReal (show (S.ncard : ℝ) ≤ 1 by exact_mod_cast hc)).trans hvol

/-- Testing on bounded open convex sets suffices for a finite family of tubes. -/
theorem counts_of_bounded_open {r L : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : ∀ W : Set Space, Convex ℝ W → IsOpen W → Bornology.IsBounded W →
      ENNReal.ofReal ((Set.ncard {i | Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2) ≤
        ENNReal.ofReal L * volume W) : Counts r L n x v := by
  have hb : Bornology.IsBounded (⋃ i, Tube r (x i) (v i)) := by
    apply Bornology.isBounded_iUnion.mpr
    intro i
    have hc : IsCompact (segment ℝ (x i) (x i + v i)) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    exact hc.isBounded.thickening
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : Space)
  intro W hW
  let U := interior W ∩ ball (0 : Space) R
  have hU : Convex ℝ U := hW.interior.inter (convex_ball _ _)
  have hUo : IsOpen U := isOpen_interior.inter isOpen_ball
  have hUb : Bornology.IsBounded U := isBounded_ball.subset inter_subset_right
  have he : {i | Tube r (x i) (v i) ⊆ W} = {i | Tube r (x i) (v i) ⊆ U} := by
    ext i
    constructor
    · intro hi
      exact subset_inter ((isOpen_thickening.subset_interior_iff).mpr hi)
        (fun p hp => hR (mem_iUnion.mpr ⟨i, hp⟩))
    · intro hi
      exact hi.trans (inter_subset_left.trans interior_subset)
  rw [he]
  exact (h U hU hUo hUb).trans (by
    gcongr
    exact inter_subset_left.trans interior_subset)

/-- One edge of a tube tower multiplies the two convex-count constants by a
universal factor. Indexed families and arbitrary assignments are allowed. -/
theorem counts_compose {r s M L : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hr1 : r ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L)
    {m n : ℕ} (x v : Fin n → Space) (y w : Fin m → Space) (f : Fin n → Fin m)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ k, ‖w k‖ = 1)
    (hsub : ∀ i, Tube s (x i) (v i) ⊆ Tube r (y (f i)) (w (f i)))
    (hP : Counts r M m y w)
    (hF : ∀ k W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | f i = k ∧ Tube s (x i) (v i) ⊆ W} : ℝ) * s ^ 2) ≤
        ENNReal.ofReal L * volume W) :
    Counts s (131072 * M * L) n x v := by
  classical
  apply counts_of_bounded_open
  intro W hW hWo hWb
  let S : Finset (Fin n) := Finset.univ.filter (fun i => Tube s (x i) (v i) ⊆ W)
  let I : Finset (Fin m) := S.image f
  have hcS : Set.ncard {i | Tube s (x i) (v i) ⊆ W} = S.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [S]
  rw [hcS]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  obtain ⟨i₀, hi₀⟩ := hSne
  let A := thickening (4 * r) W
  have hAb : Bornology.IsBounded A := hWb.thickening
  have hAfin : volume A ≠ ⊤ := hAb.measure_lt_top.ne
  have hWfin : volume W ≠ ⊤ := hWb.measure_lt_top.ne
  have hApos : 0 < (volume A).toReal := by
    have hball : ball (x i₀) s ⊆ A := by
      apply Subset.trans (ball_subset_thickening (left_mem_segment ℝ (x i₀) (x i₀ + v i₀)) s)
      exact ((Finset.mem_filter.mp hi₀).2).trans (self_subset_thickening (by positivity) W)
    exact ENNReal.toReal_pos ((measure_ball_pos volume _ hs).trans_le (measure_mono hball)).ne' hAfin
  have hI : (I : Set (Fin m)) ⊆ {k | Tube r (y k) (w k) ⊆ A} := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact parent_subset_thickening hr hs (hv i) (hw (f i)) hW
      (Finset.mem_filter.mp hi).2 (hsub i)
  have hparent : (I.card : ℝ) * r ^ 2 ≤ M * (volume A).toReal := by
    have hc : I.card ≤ Set.ncard {k | Tube r (y k) (w k) ⊆ A} := by
      simpa using Set.ncard_mono hI
    have he : ENNReal.ofReal ((I.card : ℝ) * r ^ 2) ≤ ENNReal.ofReal M * volume A :=
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg r))).trans
        (hP A (hW.thickening _))
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin) he
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (I.card : ℝ) * r ^ 2),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using ht
  have hfiber : ∀ k ∈ I,
      ((S.filter (fun i => f i = k)).card : ℝ) * s ^ 2 * (volume A).toReal ≤
        L * (131072 * r ^ 2 * (volume W).toReal) := by
    intro k hk
    let U := W ∩ Tube r (y k) (w k)
    have hUfin : volume U ≠ ⊤ := (hWb.subset inter_subset_left).measure_lt_top.ne
    have hUc : Convex ℝ U := hW.inter ((convex_segment (y k) (y k + w k)).thickening r)
    have he : {i | f i = k ∧ Tube s (x i) (v i) ⊆ U} =
        (↑(S.filter (fun i => f i = k)) : Set (Fin n)) := by
      ext i
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S]
      constructor
      · intro hi
        exact ⟨hi.2.trans inter_subset_left, hi.1⟩
      · intro hi
        refine ⟨hi.2, subset_inter hi.1 ?_⟩
        simpa only [hi.2] using hsub i
    have hl := hF k U hUc
    rw [he, Set.ncard_coe_finset] at hl
    have hl' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUfin) hl
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ ((S.filter (fun i => f i = k)).card : ℝ) * s ^ 2)] at hl'
    have hg := thickening_mul_inter_tube hW hWo hr hr1 (y k) (w k) (hw k)
    have hg' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWfin) hg
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 131072 * r ^ 2)] at hg'
    calc
      ((S.filter (fun i => f i = k)).card : ℝ) * s ^ 2 * (volume A).toReal ≤
        (L * (volume U).toReal) * (volume A).toReal := by
          gcongr 1
      _ = L * ((volume A).toReal * (volume U).toReal) := by ring
      _ ≤ L * (131072 * r ^ 2 * (volume W).toReal) := by
          gcongr 1
  have hsum := Finset.sum_le_sum hfiber
  have hcard : (S.card : ℝ) = ∑ k ∈ I, ((S.filter (fun i => f i = k)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f S
  have htotal : (S.card : ℝ) * s ^ 2 * (volume A).toReal ≤
      (I.card : ℝ) * (L * (131072 * r ^ 2 * (volume W).toReal)) := by
    simpa only [← Finset.sum_mul, ← hcard, Finset.sum_const,
      nsmul_eq_mul, mul_assoc] using hsum
  have hfinal : (S.card : ℝ) * s ^ 2 ≤ (131072 * M * L) * (volume W).toReal := by
    apply (mul_le_mul_iff_right₀ hApos).mp
    calc
      (volume A).toReal * ((S.card : ℝ) * s ^ 2) ≤
        (I.card : ℝ) * (L * (131072 * r ^ 2 * (volume W).toReal)) := by nlinarith only [htotal]
      _ = ((I.card : ℝ) * r ^ 2) * (131072 * L * (volume W).toReal) := by ring
      _ ≤ (M * (volume A).toReal) * (131072 * L * (volume W).toReal) := by
          gcongr 1
      _ = _ := by ring
  calc
    ENNReal.ofReal ((S.card : ℝ) * s ^ 2) ≤
      ENNReal.ofReal ((131072 * M * L) * (volume W).toReal) := ENNReal.ofReal_le_ofReal hfinal
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hWfin]

end WangZahlLot.Obl.wz_tower_convex_count_composition
