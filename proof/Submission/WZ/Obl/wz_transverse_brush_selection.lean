-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_brush_selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_brush_selection.Geometry
import Submission.WZ.Obl.wz_transverse_brush_selection.Energy
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_transverse_brush_selection`

Retain the tubes with shading volume at least `lam * δ² / 2`. Broadness of
the original family gives a transverse pair count controlling the second
moment of the retained multiplicity. Cauchy--Schwarz and the overlap bound
`4096 * δ³ / b` then give the required brush about a stem maximizing its
cardinality. The absolute selection constant is `1 / 32768`.
-/

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_transverse_brush_selection
open scoped ENNReal

theorem WangZahlLot.wz_transverse_brush_selection : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ b δ lam : ℝ, 0 < b → b ≤ 1 → 0 < δ → δ ≤ (1 / 100 : ℝ) → 0 < lam → lam ≤ 1 → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ (p w : LeanEval.Analysis.WangZahlKakeya.Space), ‖w‖ = 1 → (((Set.ncard {i : Fin n | p ∈ Y i ∧ min ‖v i - w‖ ‖v i + w‖ ≤ b} : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) * (((Set.ncard {i : Fin n | p ∈ Y i} : ℕ) : ℝ))) → ∃ (i₀ : Fin n) (F : Finset (Fin n)), (∀ i : Fin n, i ∈ F → (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x i₀) (x i₀ + v i₀))).Nonempty) ∧ (∀ i : Fin n, i ∈ F → b ≤ min ‖v i - v i₀‖ ‖v i + v i₀‖) ∧ (∀ i : Fin n, i ∈ F → ENNReal.ofReal (a * lam * δ ^ 2) ≤ MeasureTheory.volume (Y i)) ∧ a * b * lam ^ 2 * (n : ℝ) * δ ≤ (F.card : ℝ) * (MeasureTheory.volume (⋃ i : Fin n, Y i)).toReal := by
  classical
  refine ⟨1 / 32768, by norm_num, by norm_num, ?_⟩
  intro b δ lam hb hb1 hδ hδ1 hlam hlam1 n x v Y hn hv hT hY hshade havg hbroad
  let E : Set Space := ⋃ i, Y i
  let q : ℝ := (volume E).toReal
  let V : Fin n → ℝ := fun i => (volume (Y i)).toReal
  have hE : MeasurableSet E := MeasurableSet.iUnion hY
  have hsubE : ∀ i, Y i ⊆ E := fun i => subset_iUnion Y i
  have hEball : E ⊆ ball (0 : Space) 1 := iUnion_subset (fun i => (hshade i).trans (hT i))
  have hEfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hEball)
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hEfin (measure_mono (hsubE i))
  have htotal : lam * (n : ℝ) * δ ^ 2 ≤ ∑ i, V i := by
    rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i)),
      ENNReal.toReal_sum (fun i _ => hYfin i)] at havg
    exact havg
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htotal_q : ∑ i, V i ≤ (n : ℝ) * q := by
    calc
      ∑ i, V i ≤ ∑ _i : Fin n, q := Finset.sum_le_sum (fun i _ =>
        ENNReal.toReal_mono hEfin (measure_mono (hsubE i)))
      _ = _ := by simp
  have hq : 0 < q := by
    have hmasspos : 0 < lam * (n : ℝ) * δ ^ 2 := by positivity
    by_contra! hq
    have : (n : ℝ) * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnR.le hq
    linarith
  let t : ℝ := lam * δ ^ 2 / 2
  let D : Finset (Fin n) := Finset.univ.filter (fun i => t ≤ V i)
  have hsmall : ∑ i ∈ Finset.univ.filter (fun i => ¬t ≤ V i), V i ≤ (n : ℝ) * t := by
    calc
      _ = ∑ i : Fin n, if ¬t ≤ V i then V i else 0 := Finset.sum_filter _ _
      _ ≤ ∑ _i : Fin n, t := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with h
        · dsimp [t]
          positivity
        · exact (lt_of_not_ge h).le
      _ = _ := by simp
  have hmassD : lam * (n : ℝ) * δ ^ 2 / 2 ≤ ∑ i ∈ D, V i := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => t ≤ V i) V
    change (∑ i ∈ D, V i) + _ = _ at hsplit
    dsimp [t] at hsmall
    nlinarith
  let R : Fin n → Fin n → Prop := fun j i => b < min ‖v i - v j‖ ‖v i + v j‖
  have hcount : ∀ j p, multiplicity Y Finset.univ p ≤
      2 * multiplicity Y (Finset.univ.filter (R j)) p := by
    intro j p
    have hnear := hbroad p (v j) (hv j)
    have hfull : ({i | p ∈ Y i}.ncard : ℝ) = multiplicity Y Finset.univ p := by
      simpa using incidence_ncard Y (fun _ => True) p
    rw [incidence_ncard Y (fun i => min ‖v i - v j‖ ‖v i + v j‖ ≤ b) p,
      hfull] at hnear
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => min ‖v i - v j‖ ‖v i + v j‖ ≤ b) (fun i => oneOn (Y i) p)
    simp only [not_le] at hsplit
    change multiplicity Y (Finset.univ.filter (fun i => min ‖v i - v j‖ ‖v i + v j‖ ≤ b)) p +
      multiplicity Y (Finset.univ.filter (R j)) p = multiplicity Y Finset.univ p at hsplit
    linarith
  have henergy := broad_energy Y D R hY hYfin hcount
  have hcs := integral_sq_bound hE hEfin hq
    (integrable_multiplicity Y D (fun i _ => hY i) (fun i _ => hYfin i))
    (integrable_multiplicity_sq Y D (fun i _ => hY i) (fun i _ => hYfin i))
    (fun p hp => by
      apply Finset.sum_eq_zero
      intro i hi
      exact oneOn_of_notMem (fun h => hp (hsubE i h)))
  rw [integral_multiplicity Y D (fun i _ => hY i) (fun i _ => hYfin i)] at hcs
  let F : Fin n → Finset (Fin n) := fun i =>
    D.filter (fun j => R j i ∧ (Y j ∩ Y i).Nonempty)
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => (F i).card)
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, by simp⟩)
  let B : ℝ := 4096 * δ ^ 3 / b
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrows : ∀ i, (∑ j ∈ D.filter (fun j => R j i), (volume (Y j ∩ Y i)).toReal) ≤
      ((F i₀).card : ℝ) * B := by
    intro i
    have hroweq : (∑ j ∈ D.filter (fun j => R j i), (volume (Y j ∩ Y i)).toReal) =
        ∑ j ∈ F i, (volume (Y j ∩ Y i)).toReal := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [F, Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, hj.2.1⟩
      · intro j hj hjF
        have hne : ¬(Y j ∩ Y i).Nonempty := by
          intro h
          apply hjF
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
            (Finset.mem_filter.mp hj).2, h⟩
        rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty, ENNReal.toReal_zero]
    rw [hroweq]
    calc
      _ ≤ ∑ _j ∈ F i, B := by
        apply Finset.sum_le_sum
        intro j hj
        have hR := (Finset.mem_filter.mp hj).2.1
        have hsep : b ≤ min ‖v j - v i‖ ‖v j + v i‖ := by
          rw [norm_sub_rev, add_comm]
          exact le_of_lt hR
        have hbound := (measure_mono (inter_subset_inter (hshade j) (hshade i))).trans
          (transverse_intersection_volume hδ hb hb1 (hv j) (hv i) hsep)
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
          (ENNReal.toReal_ofReal hB)
      _ = ((F i).card : ℝ) * B := by simp
      _ ≤ ((F i₀).card : ℝ) * B := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hmax i (Finset.mem_univ i)) hB
  have hsum : (∑ i, ∑ j ∈ D.filter (fun j => R j i), (volume (Y j ∩ Y i)).toReal) ≤
      (n : ℝ) * (((F i₀).card : ℝ) * B) := by
    calc
      _ ≤ ∑ _i : Fin n, ((F i₀).card : ℝ) * B := Finset.sum_le_sum (fun i _ => hrows i)
      _ = _ := by simp
  have hsq : (lam * (n : ℝ) * δ ^ 2 / 2) ^ 2 ≤
      q * (2 * ((n : ℝ) * (((F i₀).card : ℝ) * B))) := by
    calc
      _ ≤ (∑ i ∈ D, V i) ^ 2 := pow_le_pow_left₀ (by positivity) hmassD 2
      _ ≤ q * ∫ p, multiplicity Y D p ^ 2 := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (henergy.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))) hq.le
  refine ⟨i₀, F i₀, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨p, hp, hp₀⟩ := (Finset.mem_filter.mp hi).2.2
    exact ⟨p, hshade i hp, hshade i₀ hp₀⟩
  · intro i hi
    have hR := (Finset.mem_filter.mp hi).2.1
    rw [norm_sub_rev, add_comm]
    exact le_of_lt hR
  · intro i hi
    apply (ENNReal.ofReal_le_iff_le_toReal (hYfin i)).2
    have hd := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    change t ≤ V i at hd
    change 1 / 32768 * lam * δ ^ 2 ≤ V i
    dsimp [t] at hd
    nlinarith [mul_nonneg hlam.le (sq_nonneg δ)]
  · change 1 / 32768 * b * lam ^ 2 * (n : ℝ) * δ ≤ ((F i₀).card : ℝ) * q
    apply (mul_le_mul_iff_right₀ (show 0 < 32768 * (n : ℝ) * δ ^ 3 by positivity)).mp
    have hh := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 4 * b by positivity)
    convert hh using 1
    · ring
    · dsimp [B]
      field_simp
      ring
