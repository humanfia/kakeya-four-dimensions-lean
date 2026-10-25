-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.ChartedEndgame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/ChartedEndgame.lean (82de8bd).
-- Copied from workspace o222, branch x0658 (commit 1206391), ChartedEndgame.lean; namespace renamed.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.Rounding

/-!
# Charted endgame

A finite `δ`-separated family `W` of code pairs (heights of tube lines at two
anchor columns), whose coordinates lie near fibers of size at most `F`, together
with a set `T ⊆ [0,1]` of slopes, each seeing a dense subfamily `Wt t` whose
projection `u + t v` lies near a fiber of size at most `F`, yields the graph data
of o222 after rounding the codes to the grid `δ ℤ × δ ℤ`. All constants are
explicit; the conversion to the exponents `α, ζ` is done elsewhere.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open Set Metric

lemma rd2_injOn {δ : ℝ} (hδ : 0 < δ) {W : Finset (ℝ × ℝ)}
    (hsep : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → δ ≤ dist w w') :
    Set.InjOn (rd2 δ) (W : Set (ℝ × ℝ)) := by
  intro w hw w' hw' he
  by_contra hne
  have h := hsep w hw w' hw' hne
  have h1 : rd δ w.1 = rd δ w'.1 := congrArg Prod.fst he
  have h2 : rd δ w.2 = rd δ w'.2 := congrArg Prod.snd he
  have a1 := rd_le hδ w.1
  have a2 := lt_rd_add hδ w.1
  have a3 := rd_le hδ w'.1
  have a4 := lt_rd_add hδ w'.1
  have b1 := rd_le hδ w.2
  have b2 := lt_rd_add hδ w.2
  have b3 := rd_le hδ w'.2
  have b4 := lt_rd_add hδ w'.2
  have d1 : dist w.1 w'.1 < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have d2 : dist w.2 w'.2 < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have : dist w w' < δ := by rw [Prod.dist_eq]; exact max_lt d1 d2
  linarith

/-- The rounded first coordinates of points near a fiber of size `F` number at most `3F`. -/
lemma card_rd_image_le {δ : ℝ} (hδ : 0 < δ) {W : Finset (ℝ × ℝ)} (f : ℝ × ℝ → ℝ)
    (Y : Finset ℝ) (hY : ∀ w ∈ W, ∃ y ∈ Y, |f w - y| ≤ δ) :
    (W.image (fun w => rd δ (f w))).card ≤ 3 * Y.card := by
  classical
  have hsub : W.image (fun w => rd δ (f w)) ⊆
      Y.biUnion (fun y => ({rd δ (y - δ), rd δ (y - δ) + δ, rd δ (y - δ) + 2 * δ} :
        Finset ℝ)) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y, hy, hwy⟩ := hY w hw
    exact Finset.mem_biUnion.mpr ⟨y, hy, rd_mem_three hδ hwy⟩
  calc (W.image (fun w => rd δ (f w))).card
      ≤ (Y.biUnion (fun y => ({rd δ (y - δ), rd δ (y - δ) + δ, rd δ (y - δ) + 2 * δ} :
          Finset ℝ))).card := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ Y, ({rd δ (y - δ), rd δ (y - δ) + δ, rd δ (y - δ) + 2 * δ} :
          Finset ℝ).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ Y, 3 := by
        apply Finset.sum_le_sum
        intro y _
        exact (Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    _ = 3 * Y.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- A point within `4δ` of `y` is within `δ` of one of four fixed points. -/
lemma near_four {δ y z : ℝ} (_hδ : 0 < δ) (h : |z - y| ≤ 4 * δ) :
    ∃ c ∈ ({y - 3 * δ, y - δ, y + δ, y + 3 * δ} : Finset ℝ), |z - c| ≤ δ := by
  rw [abs_le] at h
  by_cases h1 : z - y ≤ -2 * δ
  · refine ⟨y - 3 * δ, by simp, ?_⟩
    rw [abs_le]; constructor <;> linarith
  by_cases h2 : z - y ≤ 0
  · refine ⟨y - δ, by simp, ?_⟩
    rw [abs_le]; constructor <;> linarith
  by_cases h3 : z - y ≤ 2 * δ
  · refine ⟨y + δ, by simp, ?_⟩
    rw [abs_le]; constructor <;> linarith
  · refine ⟨y + 3 * δ, by simp, ?_⟩
    rw [abs_le]; constructor <;> linarith

/-- A finite set of centres, enumerated, covers what its balls cover. -/
lemma exists_fin_cover {δ : ℝ} (Z : Finset ℝ) (A : Set ℝ)
    (hA : ∀ a ∈ A, ∃ c ∈ Z, |a - c| ≤ δ) :
    ∃ (m : ℕ) (cc : Fin m → ℝ), A ⊆ (⋃ j, closedBall (cc j) δ) ∧ m = Z.card := by
  refine ⟨Z.card, fun j => Z.orderEmbOfFin rfl j, ?_, rfl⟩
  intro a ha
  obtain ⟨c, hc, hac⟩ := hA a ha
  have hcr : c ∈ Set.range (Z.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hc
  obtain ⟨j, hj⟩ := hcr
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  rw [mem_closedBall, Real.dist_eq]
  simpa [hj] using hac

theorem charted_endgame {δ F K γ β : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hK : 1 ≤ K)
    (hγ : 0 ≤ γ)
    (W : Finset (ℝ × ℝ)) (hWne : W.Nonempty)
    (hWb : ∀ w ∈ W, |w.1| ≤ 7 / 2 ∧ |w.2| ≤ 7 / 2)
    (hWsep : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → δ ≤ dist w w')
    (Y0 Y1 : Finset ℝ) (hY0 : (Y0.card : ℝ) ≤ F) (hY1 : (Y1.card : ℝ) ≤ F)
    (hW0 : ∀ w ∈ W, ∃ y ∈ Y0, |w.1 - y| ≤ δ) (hW1 : ∀ w ∈ W, ∃ y ∈ Y1, |w.2 - y| ≤ δ)
    (hsq : ∀ x y ρ : ℝ, δ ≤ ρ →
      ((W.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ)).card : ℝ) ≤
        K * ρ ^ γ * W.card)
    (hWbig : F ^ 2 ≤ K * W.card)
    (T : Finset ℝ) (hTne : T.Nonempty) (hT01 : ∀ t ∈ T, t ∈ Icc (0 : ℝ) 1)
    (hTfr : ∀ x ρ : ℝ, δ ≤ ρ →
      ((T.filter (fun t => dist t x ≤ ρ)).card : ℝ) ≤ K * ρ ^ β * T.card)
    (Wt : ℝ → Finset (ℝ × ℝ)) (hWt : ∀ t ∈ T, Wt t ⊆ W)
    (hWtbig : ∀ t ∈ T, (W.card : ℝ) ≤ K * (Wt t).card)
    (Yt : ℝ → Finset ℝ) (hYt : ∀ t ∈ T, ((Yt t).card : ℝ) ≤ F)
    (hcov : ∀ t ∈ T, ∀ w ∈ Wt t, ∃ y ∈ Yt t, |w.1 + t * w.2 - y| ≤ 2 * δ) :
    ∃ (G : Set (ℝ × ℝ)) (S : Set ℝ), G.Finite ∧ G.Nonempty ∧ S.Finite ∧ S.Nonempty ∧
      (∀ p ∈ G, |p.1| ≤ 4 ∧ |p.2| ≤ 4) ∧
      (∀ x y ρ : ℝ, δ ≤ ρ →
        ({p ∈ G | dist p.1 x ≤ ρ ∧ dist p.2 y ≤ ρ}.ncard : ℝ) ≤
          (K * 2 ^ γ) * ρ ^ γ * G.ncard) ∧
      (∀ x ρ : ℝ, δ ≤ ρ → ((S ∩ closedBall x ρ).ncard : ℝ) ≤ K * ρ ^ β * S.ncard) ∧
      (∀ t ∈ S, t ∈ Icc (0 : ℝ) 1) ∧
      (∀ a ∈ Prod.fst '' G, ∀ a' ∈ Prod.fst '' G, a ≠ a' → δ ≤ dist a a') ∧
      (∀ a ∈ Prod.snd '' G, ∀ a' ∈ Prod.snd '' G, a ≠ a' → δ ≤ dist a a') ∧
      ((Prod.fst '' G).ncard : ℝ) ≤ 3 * F ∧ ((Prod.snd '' G).ncard : ℝ) ≤ 3 * F ∧
      F ^ 2 ≤ K * G.ncard ∧
      (∀ t ∈ S, ∃ H : Set (ℝ × ℝ), H ⊆ G ∧ (G.ncard : ℝ) ≤ K * H.ncard ∧
        ∃ (m : ℕ) (cc : Fin m → ℝ),
          (fun p : ℝ × ℝ => p.1 + t * p.2) '' H ⊆ (⋃ j, closedBall (cc j) δ) ∧
          (m : ℝ) ≤ 4 * F) := by
  classical
  have hinj := rd2_injOn hδ hWsep
  set GF : Finset (ℝ × ℝ) := W.image (rd2 δ) with hGF
  have hGcard : GF.card = W.card := Finset.card_image_of_injOn hinj
  have hGn : ((GF : Set (ℝ × ℝ)).ncard : ℝ) = W.card := by
    rw [Set.ncard_coe_finset, hGcard]
  have hfst : Prod.fst '' (GF : Set (ℝ × ℝ)) =
      ((W.image (fun w => rd δ w.1) : Finset ℝ) : Set ℝ) := by
    ext a
    simp only [GF, Finset.coe_image, Set.mem_image, Finset.mem_coe, rd2]
    constructor
    · rintro ⟨p, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  have hsnd : Prod.snd '' (GF : Set (ℝ × ℝ)) =
      ((W.image (fun w => rd δ w.2) : Finset ℝ) : Set ℝ) := by
    ext a
    simp only [GF, Finset.coe_image, Set.mem_image, Finset.mem_coe, rd2]
    constructor
    · rintro ⟨p, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨(GF : Set (ℝ × ℝ)), (T : Set ℝ), Finset.finite_toSet _, ?_,
    Finset.finite_toSet _, Finset.coe_nonempty.mpr hTne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact Finset.coe_nonempty.mpr (hWne.image _)
  · -- coordinates bounded by 4
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    obtain ⟨h1, h2⟩ := hWb w hw
    have e1 := abs_rd_le hδ w.1
    have e2 := abs_rd_le hδ w.2
    exact ⟨by simp only [rd2]; linarith, by simp only [rd2]; linarith⟩
  · -- square Frostman
    intro x y ρ hρ
    have hρ0 : 0 < ρ := hδ.trans_le hρ
    have hsub : {p ∈ (GF : Set (ℝ × ℝ)) | dist p.1 x ≤ ρ ∧ dist p.2 y ≤ ρ} ⊆
        (((W.filter (fun w => |w.1 - x| ≤ ρ + δ ∧ |w.2 - y| ≤ ρ + δ)).image (rd2 δ) :
          Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      rintro p ⟨hp, hpx, hpy⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, ?_, ?_⟩, rfl⟩)
      · have := abs_sub_rd_lt hδ w.1
        rw [Real.dist_eq] at hpx
        simp only [rd2] at hpx
        calc |w.1 - x| = |(w.1 - rd δ w.1) + (rd δ w.1 - x)| := by ring_nf
          _ ≤ |w.1 - rd δ w.1| + |rd δ w.1 - x| := abs_add_le _ _
          _ ≤ ρ + δ := by linarith
      · have := abs_sub_rd_lt hδ w.2
        rw [Real.dist_eq] at hpy
        simp only [rd2] at hpy
        calc |w.2 - y| = |(w.2 - rd δ w.2) + (rd δ w.2 - y)| := by ring_nf
          _ ≤ |w.2 - rd δ w.2| + |rd δ w.2 - y| := abs_add_le _ _
          _ ≤ ρ + δ := by linarith
    have h1 : ({p ∈ (GF : Set (ℝ × ℝ)) | dist p.1 x ≤ ρ ∧ dist p.2 y ≤ ρ}.ncard : ℝ) ≤
        ((W.filter (fun w => |w.1 - x| ≤ ρ + δ ∧ |w.2 - y| ≤ ρ + δ)).card : ℝ) := by
      have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this.trans Finset.card_image_le
    have h2 := hsq x y (ρ + δ) (by linarith)
    have h3 : (ρ + δ) ^ γ ≤ 2 ^ γ * ρ ^ γ := by
      rw [← Real.mul_rpow (by norm_num) hρ0.le]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hγ
    rw [hGn]
    have hK0 : 0 ≤ K := by linarith
    have hW0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    calc _ ≤ _ := h1
      _ ≤ K * (ρ + δ) ^ γ * W.card := h2
      _ ≤ K * (2 ^ γ * ρ ^ γ) * W.card := by gcongr
      _ = K * 2 ^ γ * ρ ^ γ * W.card := by ring
  · -- Frostman of the slopes
    intro x ρ hρ
    have hset : (T : Set ℝ) ∩ closedBall x ρ =
        ((T.filter (fun t => dist t x ≤ ρ) : Finset ℝ) : Set ℝ) := by
      ext t; simp [mem_closedBall]
    rw [hset, Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hTfr x ρ hρ
  · intro t ht; exact hT01 t (Finset.mem_coe.mp ht)
  · rw [hfst]
    intro a ha a' ha' hne
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨w', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha')
    exact rd_sep hδ hne
  · rw [hsnd]
    intro a ha a' ha' hne
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨w', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha')
    exact rd_sep hδ hne
  · rw [hfst, Set.ncard_coe_finset]
    have := card_rd_image_le hδ (W := W) (fun w => w.1) Y0 hW0
    have : ((W.image (fun w => rd δ w.1)).card : ℝ) ≤ 3 * (Y0.card : ℝ) := by
      exact_mod_cast this
    linarith
  · rw [hsnd, Set.ncard_coe_finset]
    have := card_rd_image_le hδ (W := W) (fun w => w.2) Y1 hW1
    have : ((W.image (fun w => rd δ w.2)).card : ℝ) ≤ 3 * (Y1.card : ℝ) := by
      exact_mod_cast this
    linarith
  · rw [hGn]; exact hWbig
  · intro t ht
    have ht' : t ∈ T := Finset.mem_coe.mp ht
    obtain ⟨ht0, ht1⟩ := hT01 t ht'
    have hinjt : Set.InjOn (rd2 δ) ((Wt t : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) :=
      hinj.mono (by exact_mod_cast hWt t ht')
    refine ⟨(((Wt t).image (rd2 δ) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)), ?_, ?_, ?_⟩
    · exact Finset.coe_subset.mpr (Finset.image_subset_image (hWt t ht'))
    · rw [Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_image_of_injOn hinjt,
        hGcard]
      exact hWtbig t ht'
    · set Z : Finset ℝ := (Yt t).biUnion
        (fun y => ({y - 3 * δ, y - δ, y + δ, y + 3 * δ} : Finset ℝ)) with hZ
      obtain ⟨m, cc, hcc, hm⟩ := exists_fin_cover (δ := δ) Z
        ((fun p : ℝ × ℝ => p.1 + t * p.2) ''
          (((Wt t).image (rd2 δ) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) (by
          rintro a ⟨p, hp, rfl⟩
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
          obtain ⟨y, hy, hwy⟩ := hcov t ht' w hw
          have e1 := abs_sub_rd_lt hδ w.1
          have e2 := abs_sub_rd_lt hδ w.2
          have hnear : |(rd2 δ w).1 + t * (rd2 δ w).2 - y| ≤ 4 * δ := by
            simp only [rd2]
            have ht2 : |t * (rd δ w.2 - w.2)| ≤ δ := by
              rw [abs_mul, abs_of_nonneg ht0]
              have : |rd δ w.2 - w.2| ≤ δ := by
                rw [abs_sub_comm]; exact e2.le
              nlinarith [abs_nonneg (rd δ w.2 - w.2)]
            have e1' : |rd δ w.1 - w.1| ≤ δ := by rw [abs_sub_comm]; exact e1.le
            calc |rd δ w.1 + t * rd δ w.2 - y|
                = |(rd δ w.1 - w.1) + t * (rd δ w.2 - w.2) + (w.1 + t * w.2 - y)| := by
                  ring_nf
              _ ≤ |(rd δ w.1 - w.1) + t * (rd δ w.2 - w.2)| + |w.1 + t * w.2 - y| :=
                  abs_add_le _ _
              _ ≤ |rd δ w.1 - w.1| + |t * (rd δ w.2 - w.2)| + |w.1 + t * w.2 - y| := by
                  gcongr; exact abs_add_le _ _
              _ ≤ 4 * δ := by linarith
          obtain ⟨c, hc, hzc⟩ := near_four hδ hnear
          exact ⟨c, Finset.mem_biUnion.mpr ⟨y, hy, hc⟩, hzc⟩)
      refine ⟨m, cc, hcc, ?_⟩
      have hZc : Z.card ≤ 4 * (Yt t).card := by
        calc Z.card ≤ ∑ y ∈ Yt t, ({y - 3 * δ, y - δ, y + δ, y + 3 * δ} : Finset ℝ).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _y ∈ Yt t, 4 := by
              apply Finset.sum_le_sum
              intro y _
              exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
                ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
                  ((Finset.card_insert_le _ _).trans (by simp)))))
          _ = 4 * (Yt t).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      rw [hm]
      have : (Z.card : ℝ) ≤ 4 * ((Yt t).card : ℝ) := by exact_mod_cast hZc
      linarith [hYt t ht']

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
