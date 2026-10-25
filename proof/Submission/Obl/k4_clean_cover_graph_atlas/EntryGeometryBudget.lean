import Submission.Obl.k4_clean_cover_graph_atlas.SampleScales
import Submission.Obl.k4_clean_cover_graph_atlas.EntryPartition

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- The entry table size times its normalized comparison volume is independent
of the sheet scale. Only a fixed constant and five powers of the chart loss remain. -/
theorem entry_geometry_volume_budget {A κ : ℝ} {Cs s₀ K : ℕ}
    (hA : 0 < A) (hκ : 1 ≤ κ)
    (hs : (2 : ℝ) ^ s₀ ≤ 2 * (256 * (κ + 2) * A ^ (Cs : ℝ)))
    (hK : (K : ℝ) ≤ κ * (2 : ℝ) ^ s₀ + 1) :
    ((2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4) * sheetRadius A Cs ^ 3 ≤
      (2 : ℝ) ^ (18 : ℕ) * κ ^ 5 := by
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have hZ : (1 : ℝ) ≤ 2 ^ s₀ := one_le_pow₀ (by norm_num)
  have hAC : 0 < A ^ (Cs : ℝ) := Real.rpow_pos_of_pos hA _
  have hradius : 0 < sheetRadius A Cs := by unfold sheetRadius; positivity
  have hside : (2 : ℝ) ^ s₀ ≤ 1536 * κ * A ^ (Cs : ℝ) := by
    have : κ + 2 ≤ 3 * κ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hAC.le]
  have hK6 : 2 * (K : ℝ) + 2 ≤ 6 * κ * (2 : ℝ) ^ s₀ := by
    have : (1 : ℝ) ≤ κ * (2 : ℝ) ^ s₀ := one_le_mul_of_one_le_of_one_le hκ hZ
    linarith
  have hgeom : (2 : ℝ) ^ s₀ * (2 * (K : ℝ) + 2) ^ 2 * 4 ≤
      144 * κ ^ 2 * ((2 : ℝ) ^ s₀) ^ 3 := by
    calc
      _ ≤ (2 : ℝ) ^ s₀ * (6 * κ * (2 : ℝ) ^ s₀) ^ 2 * 4 := by gcongr
      _ = _ := by ring
  have hcancel : (A ^ (Cs : ℝ)) ^ 3 * sheetRadius A Cs ^ 3 = (128 : ℝ)⁻¹ ^ 3 := by
    unfold sheetRadius
    rw [Real.rpow_neg hA.le]
    field_simp [hAC.ne']
  calc
    _ ≤ (144 * κ ^ 2 * ((2 : ℝ) ^ s₀) ^ 3) * sheetRadius A Cs ^ 3 :=
      mul_le_mul_of_nonneg_right hgeom (by unfold sheetRadius; positivity)
    _ ≤ (144 * κ ^ 2 * (1536 * κ * A ^ (Cs : ℝ)) ^ 3) * sheetRadius A Cs ^ 3 := by
      gcongr
    _ = 248832 * κ ^ 5 := by
      calc
        _ = (144 * 1536 ^ (3 : ℕ) * κ ^ 5) *
            ((A ^ (Cs : ℝ)) ^ 3 * sheetRadius A Cs ^ 3) := by ring
        _ = _ := by rw [hcancel]; norm_num; ring
    _ ≤ _ := by norm_num; nlinarith [pow_nonneg hκ0 5]

open Classical in
/-- Fixing an entry group leaves only the candidate and its fine derivative
sign free. In particular, the geometric subdivision costs nothing in this count. -/
theorem card_entryGroup_le {n C s₀ K : ℕ} (old : Fin n → Fin C)
    (G : Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) :
    (Finset.univ.filter (fun e : Entry n s₀ K => entryGroup old e = G)).card ≤
      2 * (Finset.univ.filter (fun a => old a = G.1)).card := by
  classical
  let f := fun e : Entry n s₀ K => (e.1, e.2.2.2.1)
  have hcard : (Finset.univ.filter (fun e : Entry n s₀ K => entryGroup old e = G)).card ≤
      ((Finset.univ.filter (fun a => old a = G.1)) ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro e he
      have heG := (Finset.mem_filter.mp he).2
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.fst heG⟩,
        Finset.mem_univ _⟩
    · intro e he e' he' hpair
      change (e.1, e.2.2.2.1) = (e'.1, e'.2.2.2.1) at hpair
      have ha : e.1 = e'.1 := congrArg (fun p : Fin n × Bool => p.1) hpair
      have hb : e.2.2.2.1 = e'.2.2.2.1 := congrArg (fun p : Fin n × Bool => p.2) hpair
      have heG := (Finset.mem_filter.mp he).2
      have heG' := (Finset.mem_filter.mp he').2
      have hg := heG.trans heG'.symm
      exact Prod.ext ha (Prod.ext (congrArg (fun g => g.2.1) hg)
        (Prod.ext (congrArg (fun g => g.2.2.1) hg) (Prod.ext hb
          (congrArg (fun g => g.2.2.2) hg))))
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm] using hcard

end Submission.Obl.k4_clean_cover_graph_atlas
