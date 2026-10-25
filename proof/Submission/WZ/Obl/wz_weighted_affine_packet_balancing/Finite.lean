-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_weighted_affine_packet_balancing.Finite.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_weighted_affine_packet_balancing

open scoped BigOperators

/-- A cell with at most the average cost per incidence. -/
theorem good_cell {m : ℕ} (hm : 0 < m) (a c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) {H : ℝ} (_hH : 0 ≤ H)
    (hcover : H ≤ ∑ j, a j) :
    ∃ j, H * c j ≤ (∑ i, c i) * a j ∧ c j ≤ ∑ i, c i := by
  classical
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hsum : 0 ≤ ∑ j, c j := Finset.sum_nonneg (fun j _ => hc j)
  have hex : ∃ j, H * c j ≤ (∑ i, c i) * a j := by
    by_contra hn
    push Not at hn
    have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun j (_ : j ∈ Finset.univ) => hn j)
    simp only [← Finset.mul_sum] at hlt
    nlinarith [mul_le_mul_of_nonneg_left hcover hsum]
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, hj, Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ j)⟩

/-- One size class carries a definite fraction of the total weight. -/
theorem uniform_selection {α : Type*} [Fintype α] [Nonempty α]
    (w : α → ℕ) (hw : ∀ a, 0 < w a) {n b : ℕ} (hb : 0 < b)
    (hwn : ∀ a, w a ≤ n) {R : ℝ} (hR : 1 < R) (hn : (n : ℝ) < R ^ b) :
    ∃ (N q : ℕ) (u : Fin N → α), 0 < N ∧ 0 < q ∧ Function.Injective u ∧
      (∀ i, q ≤ w (u i)) ∧ (∑ a, (w a : ℝ)) ≤ (b : ℝ) * R * N * q := by
  classical
  obtain ⟨color, hcolor⟩ :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.exists_size_color n b R hb hR hn
  have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  let S : Fin b → Finset α := fun t => Finset.univ.filter fun a => color (w a) = t
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image Finset.univ
    (fun t => ∑ a ∈ S t, (w a : ℝ)) Finset.univ_nonempty
  have hmass : (∑ a, (w a : ℝ)) ≤ (b : ℝ) * ∑ a ∈ S t, (w a : ℝ) := by
    calc
      (∑ a, (w a : ℝ)) = ∑ t : Fin b, ∑ a ∈ S t, (w a : ℝ) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
      _ ≤ ∑ _t : Fin b, ∑ a ∈ S t, (w a : ℝ) :=
        Finset.sum_le_sum fun t' ht' => ht t' ht'
      _ = _ := by simp
  have hpos : 0 < ∑ a, (w a : ℝ) :=
    Finset.sum_pos (fun a _ => by exact_mod_cast hw a) Finset.univ_nonempty
  have hS : (S t).Nonempty := by
    by_contra h
    have he : S t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he] at hmass
    simp only [Finset.sum_empty, mul_zero] at hmass
    linarith
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image (S t) w hS
  let u := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate (S t)
  have hu (i) : u i ∈ S t :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_mem (S t) i
  refine ⟨(S t).card, w a, u, Finset.card_pos.mpr hS, hw a,
    WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_injective (S t),
    fun i => hmin _ (hu i), ?_⟩
  have hclass : (∑ a' ∈ S t, (w a' : ℝ)) ≤ (S t).card * (R * w a) := by
    calc
      _ ≤ ∑ _a' ∈ S t, R * (w a : ℝ) := by
        apply Finset.sum_le_sum
        intro a' ha'
        apply hcolor _ _ (hw a') (hwn a') (hw a) (hwn a)
        exact (Finset.mem_filter.mp ha').2.trans (Finset.mem_filter.mp ha).2.symm
      _ = _ := by simp
  calc
    (∑ a', (w a' : ℝ)) ≤ (b : ℝ) * ∑ a' ∈ S t, (w a' : ℝ) := hmass
    _ ≤ (b : ℝ) * ((S t).card * (R * w a)) := by gcongr
    _ = _ := by ring

/-- A rounded number of repetitions attains the target with less than one packet overhead. -/
theorem repetitions {H P : ℝ} (hH : 0 < H) (hP : 0 < P) :
    ∃ k : ℕ, 0 < k ∧ H ≤ (k : ℝ) * P ∧ (k : ℝ) * P ≤ H + P := by
  refine ⟨⌈H / P⌉₊, Nat.ceil_pos.mpr (by positivity), ?_, ?_⟩
  · exact (div_le_iff₀ hP).mp (Nat.le_ceil _)
  · have h := (Nat.ceil_lt_add_one (show 0 ≤ H / P by positivity)).le
    have h' := mul_le_mul_of_nonneg_right h hP.le
    simpa only [add_mul, div_mul_cancel₀ _ hP.ne', one_mul] using h'

end WangZahlLot.Obl.wz_weighted_affine_packet_balancing
