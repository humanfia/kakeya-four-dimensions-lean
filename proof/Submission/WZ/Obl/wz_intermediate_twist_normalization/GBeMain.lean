-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.GBeMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.GBeUnion
import Submission.WZ.Obl.wz_intermediate_twist_normalization.MiddleMain
import Submission.WZ.Obl.wz_essentially_distinct_tube_count

/-!
# Graceful B from B

`GBe_of_B : Estimate (|c| ≤ 1) → GBe`. For a family in `safeCyl r e` with enlarged convex
count coefficient `Kt`:

1. superpose `N ≈ r² Kt / m` grid translates selected with `o055`/`o057` (`translates_count`);
2. keep the dense translated tubes and regularize them to an essentially distinct subfamily
   with a dyadic class of cluster sizes (`regularize`); its convex count is the count of the
   union divided by the cluster size;
3. apply `B` to it; the projection of the union of translates has area at most `N` times the
   projection of the family.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN proj
  nat_succ_le_rpow)
open WangZahlLot.Obl.wz_compact_offset_normalization (Estimate Family Frostman Slope Projection)

/-- The number of dyadic classes. -/
theorem dyadic_classes_le {ρ σ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ((Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (2 / σ) * ρ ^ (-(10 * σ)) := by
  have h1 := nat_succ_le_rpow hσ hσ1 (Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊)
  have hge : (1 : ℝ) ≤ ρ ^ (-10 : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  have hn : ⌊ρ ^ (-10 : ℝ)⌋₊ ≠ 0 := by
    have := Nat.floor_pos.mpr hge; omega
  have h2 : ((2 : ℝ) ^ Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊) ≤ ρ ^ (-10 : ℝ) := by
    have := Nat.pow_log_le_self 2 hn
    calc ((2 : ℝ) ^ Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊) = ((2 ^ Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊ : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ (⌊ρ ^ (-10 : ℝ)⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ ρ ^ (-10 : ℝ) := Nat.floor_le (by positivity)
  have h3 : ((2 : ℝ) ^ Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊) ^ σ ≤ (ρ ^ (-10 : ℝ)) ^ σ :=
    Real.rpow_le_rpow (by positivity) h2 hσ.le
  rw [← Real.rpow_mul hρ.le] at h3
  calc ((Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊ : ℕ) : ℝ) + 1
      ≤ (2 / σ) * ((2 : ℝ) ^ Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊) ^ σ := h1
    _ ≤ (2 / σ) * ρ ^ (-10 * σ) := by gcongr
    _ = (2 / σ) * ρ ^ (-(10 * σ)) := by ring_nf

/-- The dense part of a family. -/
theorem dense_part {ι : Type*} [Fintype ι] {ρ η : ℝ} (hρ : 0 < ρ) (Y : ι → Set Space)
    (hmass : ENNReal.ofReal (ρ ^ η * (Fintype.card ι : ℝ) * ρ ^ 2) ≤ ∑ q, volume (Y q))
    (hmax : ∀ q, volume (Y q) ≤ ENNReal.ofReal (144 * ρ ^ 2)) :
    ρ ^ η * (Fintype.card ι : ℝ) / 288 ≤
      ((Finset.univ.filter (fun q => ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) ≤ volume (Y q))).card : ℝ) := by
  classical
  set U := Finset.univ.filter (fun q => ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) ≤ volume (Y q))
  have hρη : 0 < ρ ^ η := Real.rpow_pos_of_pos hρ _
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q => ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) ≤ volume (Y q)) (fun q => volume (Y q))
  have hlow : ∑ q ∈ Finset.univ.filter (fun q => ¬ ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) ≤ volume (Y q)),
      volume (Y q) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (ρ ^ η * ρ ^ 2 / 2)) := by
    calc _ ≤ ∑ _q ∈ Finset.univ.filter (fun q => ¬ ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) ≤
          volume (Y q)), ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) :=
          Finset.sum_le_sum fun q hq => (not_le.mp (Finset.mem_filter.mp hq).2).le
      _ ≤ ∑ _q : ι, ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (ρ ^ η * ρ ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have hhigh : ∑ q ∈ U, volume (Y q) ≤ ENNReal.ofReal (U.card * (144 * ρ ^ 2)) := by
    calc ∑ q ∈ U, volume (Y q) ≤ ∑ _q ∈ U, ENNReal.ofReal (144 * ρ ^ 2) :=
          Finset.sum_le_sum fun q _ => hmax q
      _ = ENNReal.ofReal (U.card * (144 * ρ ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have htot : ENNReal.ofReal (ρ ^ η * (Fintype.card ι : ℝ) * ρ ^ 2) ≤
      ENNReal.ofReal (U.card * (144 * ρ ^ 2)) +
        ENNReal.ofReal ((Fintype.card ι : ℝ) * (ρ ^ η * ρ ^ 2 / 2)) := by
    rw [← hsplit] at hmass
    exact hmass.trans (add_le_add hhigh hlow)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at htot
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have : ρ ^ η * (Fintype.card ι : ℝ) * ρ ^ 2 / 2 ≤ U.card * (144 * ρ ^ 2) := by nlinarith
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

open Classical in
/-- The convex count of the selected representatives. -/
theorem selected_frostman {ι : Type*} [Fintype ι] {ρ : ℝ} (xU vU : ι → Space)
    (hT : ∀ q, tube ρ (xU q) (vU q) ⊆ ball 0 1) (U S : Finset ι) {μb CU : ℝ} (hμb : 0 < μb)
    (hCU : 0 ≤ CU)
    (htrans : ∀ W : Set Space, Convex ℝ W →
      ((S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W)).card : ℝ) * μb ≤
        ((U.filter (fun q => tube ρ (xU q) (vU q) ⊆ W + (5003 : ℝ) • (W - W))).card : ℝ))
    (hcountU : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {q | tube ρ (xU q) (vU q) ⊆ W} : ℕ) : ℝ) ≤
        ENNReal.ofReal CU * volume W) (W : Set Space) (hW : Convex ℝ W) :
    ENNReal.ofReal ((S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W)).card : ℝ) ≤
      ENNReal.ofReal (CU * (1 + 4 * 5003) ^ 3 / μb) * volume W := by
  set W' := W ∩ ball 0 1 with hW'
  have hW'c : Convex ℝ W' := hW.inter (convex_ball _ _)
  have hW'b : Bornology.IsBounded W' := isBounded_ball.subset inter_subset_right
  have hS : S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W) =
      S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W') := by
    ext r
    simp only [Finset.mem_filter, hW', subset_inter_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, hT r⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
  rw [hS]
  have hplus : Convex ℝ (W' + (5003 : ℝ) • (W' - W')) := hW'c.add ((hW'c.sub hW'c).smul _)
  have h1 := htrans W' hW'c
  have h2 : ((U.filter (fun q => tube ρ (xU q) (vU q) ⊆ W' + (5003 : ℝ) • (W' - W'))).card : ℝ) ≤
      ((Set.ncard {q | tube ρ (xU q) (vU q) ⊆ W' + (5003 : ℝ) • (W' - W')} : ℕ) : ℝ) := by
    rw [← Set.ncard_coe_finset]
    exact_mod_cast Set.ncard_le_ncard (fun q hq => (Finset.mem_filter.mp hq).2) (Set.toFinite _)
  have h3 := hcountU _ hplus
  have h4 := volume_add_smul_sub_le hW'c hW'b (t := 5003) (by norm_num)
  have h5 : volume W' ≤ volume W := measure_mono inter_subset_left
  have hchain : ENNReal.ofReal (((S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W')).card : ℝ) * μb) ≤
      ENNReal.ofReal (CU * (1 + 4 * 5003) ^ 3) * volume W := by
    calc ENNReal.ofReal (((S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W')).card : ℝ) * μb)
        ≤ ENNReal.ofReal ((Set.ncard {q | tube ρ (xU q) (vU q) ⊆
            W' + (5003 : ℝ) • (W' - W')} : ℕ) : ℝ) := ENNReal.ofReal_le_ofReal (h1.trans h2)
      _ ≤ ENNReal.ofReal CU * volume (W' + (5003 : ℝ) • (W' - W')) := h3
      _ ≤ ENNReal.ofReal CU * (ENNReal.ofReal ((1 + 4 * 5003) ^ 3) * volume W) := by
          gcongr; exact h4.trans (by gcongr)
      _ = ENNReal.ofReal (CU * (1 + 4 * 5003) ^ 3) * volume W := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCU]
  have hsplit : ENNReal.ofReal ((S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W')).card : ℝ) =
      ENNReal.ofReal (((S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W')).card : ℝ) * μb) *
        ENNReal.ofReal (1 / μb) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hsplit]
  calc ENNReal.ofReal (((S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W')).card : ℝ) * μb) *
        ENNReal.ofReal (1 / μb)
      ≤ ENNReal.ofReal (CU * (1 + 4 * 5003) ^ 3) * volume W * ENNReal.ofReal (1 / μb) := by
        gcongr
    _ = ENNReal.ofReal (CU * (1 + 4 * 5003) ^ 3 / μb) * volume W := by
        rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- The exponent arithmetic for the Frostman condition of the selected representatives. -/
theorem frostman_arith {ρ η ηB ε' σ g A Cpp Kt J Uplus : ℝ} (hρ : 0 < ρ) (hKt : 0 < Kt)
    (hA : 0 ≤ A) (hCpp : 0 ≤ Cpp) (hσ : 0 < σ) (hJ0 : 0 ≤ J)
    (hJ : J ≤ (2 / σ) * ρ ^ (-(10 * σ))) (hU : ρ ^ (3 * η) * Kt / 288 ≤ Uplus)
    (hg : g = ηB - 3 * η - ε' - 10 * σ) (hT5 : ρ ^ g * (A * Cpp * 2304 / σ) ≤ 1) :
    A * ρ ^ (-ε') * Kt * Cpp * (4 * J) ≤ ρ ^ (-ηB) * Uplus := by
  have hρε : 0 < ρ ^ (-ε') := Real.rpow_pos_of_pos hρ _
  have hpow : ρ ^ (-ε') * ρ ^ (-(10 * σ)) = ρ ^ (-ηB) * ρ ^ (3 * η) * ρ ^ g := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_add hρ, hg]
    congr 1; ring
  have hB : 0 ≤ ρ ^ (-ηB) * (ρ ^ (3 * η) * Kt / 288) := by
    have := Real.rpow_pos_of_pos hρ (-ηB); have := Real.rpow_pos_of_pos hρ (3 * η); positivity
  calc A * ρ ^ (-ε') * Kt * Cpp * (4 * J)
      ≤ A * ρ ^ (-ε') * Kt * Cpp * (4 * ((2 / σ) * ρ ^ (-(10 * σ)))) := by gcongr
    _ = (ρ ^ g * (A * Cpp * 2304 / σ)) * (ρ ^ (-ηB) * (ρ ^ (3 * η) * Kt / 288)) := by
        rw [show A * ρ ^ (-ε') * Kt * Cpp * (4 * ((2 / σ) * ρ ^ (-(10 * σ)))) =
          A * Kt * Cpp * (8 / σ) * (ρ ^ (-ε') * ρ ^ (-(10 * σ))) by ring, hpow]
        field_simp
        ring
    _ ≤ 1 * (ρ ^ (-ηB) * (ρ ^ (3 * η) * Kt / 288)) := mul_le_mul_of_nonneg_right hT5 hB
    _ ≤ ρ ^ (-ηB) * Uplus := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hU (Real.rpow_pos_of_pos hρ _).le

/-- Projections of the union of translates. -/
theorem volume_proj_union_translates_le {f : ℝ → ℝ} (hf : Continuous f) {N m : ℕ}
    (s : Fin N → Space) (hs : ∀ j, s j 2 = 0) (Y : Fin m → Set Space) :
    volume (proj f (⋃ q : Fin N × Fin m, (fun p => p - s q.1) ⁻¹' Y q.2)) ≤
      N * volume (proj f (⋃ i, Y i)) := by
  have he : (⋃ q : Fin N × Fin m, (fun p => p - s q.1) ⁻¹' Y q.2) =
      ⋃ j, (fun p => p - s j) ⁻¹' (⋃ i, Y i) := by
    ext p; simp [Prod.exists]
  rw [he, proj, Set.image_iUnion]
  calc volume (⋃ j, (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) ''
        ((fun p => p - s j) ⁻¹' ⋃ i, Y i))
      ≤ ∑ j, volume ((fun p : Space => (p 0 + f (p 2) * p 1, p 2)) ''
          ((fun p => p - s j) ⁻¹' ⋃ i, Y i)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin N, volume (proj f (⋃ i, Y i)) :=
        Finset.sum_le_sum fun j _ => volume_proj_translate_le hf (hs j) _
    _ = N * volume (proj f (⋃ i, Y i)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

set_option maxHeartbeats 1600000 in
/-- **Graceful B from B.** -/
theorem GBe_of_B (hB : Estimate (fun c => |c| ≤ 1)) : GBe := by
  classical
  intro ε hε
  obtain ⟨ηB0, hηB0, dB, hdB, hBε⟩ := hB (ε / 2) (by positivity)
  obtain ⟨ηB, hηBdef⟩ : ∃ ηB : ℝ, ηB = min ηB0 1 := ⟨_, rfl⟩
  have hηB : 0 < ηB := by rw [hηBdef]; exact lt_min hηB0 one_pos
  have hηB1 : ηB ≤ 1 := by rw [hηBdef]; exact min_le_right _ _
  have hηBB0 : ηB ≤ ηB0 := by rw [hηBdef]; exact min_le_left _ _
  obtain ⟨D55, hD55, h55⟩ := WangZahlLot.wz_nsp_convex_test_family _ rfl
  obtain ⟨C43, hC43, h43⟩ := WangZahlLot.wz_essentially_distinct_tube_count
  obtain ⟨C57, hC57, h57⟩ := WangZahlLot.wz_nsp_finite_load_selection 4000 D55 (by norm_num) hD55
    (ηB / 4) (by positivity)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = D55 * (27 * C57 * Real.log 3) := ⟨_, rfl⟩
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hA0 : 0 ≤ A := by rw [hA]; have := hD55; positivity
  obtain ⟨Cpp, hCpp⟩ : ∃ Cpp : ℝ, Cpp = (1 + 4 * 5003) ^ 3 := ⟨_, rfl⟩
  have hCpp0 : 0 ≤ Cpp := by rw [hCpp]; positivity
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ηB / 100 := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ηB / 40 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ηB - 3 * η - ηB / 4 - 10 * σ := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hg0 : 0 < g := by rw [hg, hη, hσ]; linarith
  -- the thresholds
  obtain ⟨X5, hX5⟩ : ∃ X5 : ℝ, X5 = A * Cpp * 2304 / σ := ⟨_, rfl⟩
  have hX50 : 0 ≤ X5 := by rw [hX5]; positivity
  have hd43 : 0 < 1 / (2 * C43) := by positivity
  set d0 := min (1 / 10000) (min dB (min ((1 / (2 * C43)) ^ (1 / (4 : ℝ)))
    (min ((1 / 2 : ℝ) ^ (1 / (ηB - η))) ((1 / (X5 + 1)) ^ (1 / g))))) with hd0
  have hηBη : 0 < ηB - η := by rw [hη]; linarith
  refine ⟨η, hη0, d0, ?_, 217, by norm_num, ?_⟩
  · refine lt_min (by norm_num) (lt_min hdB (lt_min (Real.rpow_pos_of_pos hd43 _)
      (lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by positivity) _))))
  intro ρ r e hρ hρd hρr he16 he4 m x v Y Kt hm hv hv2 hcyl hYm hYT hcount hmass f hf hf0
  have hρ1' : ρ ≤ 1 / 10000 := hρd.trans (min_le_left _ _)
  have hρdB : ρ ≤ dB := hρd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ1 : ρ ≤ 1 := by linarith
  have hρ100 : ρ ≤ 1 / 100 := by linarith
  have hT3 : ρ ^ (4 : ℝ) ≤ 1 / (2 * C43) := rpow_le_of_le_rpow_inv hρ (by norm_num) hd43
    (hρd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hT4 : ρ ^ (ηB - η) ≤ 1 / 2 := rpow_le_of_le_rpow_inv hρ hηBη (by norm_num)
    (hρd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))))
  have hT5' : ρ ^ g ≤ 1 / (X5 + 1) := rpow_le_of_le_rpow_inv hρ hg0 (by positivity)
    (hρd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))))
  have hT5 : ρ ^ g * X5 ≤ 1 := by
    have h1 : ρ ^ g * X5 ≤ 1 / (X5 + 1) * X5 := mul_le_mul_of_nonneg_right hT5' hX50
    have h2 : 1 / (X5 + 1) * X5 ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
    linarith
  have hsmall : C43 * ρ ^ 4 ≤ 1 / 2 := by
    rw [← Real.rpow_natCast] at *
    have : ρ ^ ((4 : ℕ) : ℝ) ≤ 1 / (2 * C43) := by simpa using hT3
    calc C43 * ρ ^ ((4 : ℕ) : ℝ) ≤ C43 * (1 / (2 * C43)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hρη : ρ ^ η ≤ 1 := Real.rpow_le_one hρ.le hρ1 hη0.le
  have hρr' : ρ ≤ r := by
    have : ρ ^ (1 : ℝ) ≤ ρ ^ η := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by rw [hη]; linarith)
    rw [Real.rpow_one] at this
    exact this.trans hρr
  have he0 : 0 ≤ e := by nlinarith [sq_nonneg r]
  have hr1 : r ≤ 1 := by nlinarith [sq_nonneg r]
  -- Step A: the selected translates
  obtain ⟨hKt, N, s, hN1, hN2, hs, hUcount⟩ := translates_count (ε' := ηB / 4) hD55 hC57 h55
    h57 hρ hρ1 hρr' he16 he4 hm hv hv2 hcyl hcount
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set xU : Fin N × Fin m → Space := fun q => x q.2 + s q.1 with hxU
  set vU : Fin N × Fin m → Space := fun q => v q.2 with hvU
  set YU : Fin N × Fin m → Set Space := fun q => (fun p => p - s q.1) ⁻¹' Y q.2 with hYU
  have hTU : ∀ q, tube ρ (xU q) (vU q) ⊆ ball 0 1 := fun q =>
    translate_subset_ball he16 he4 (hcyl q.2) (hs q.1).1 (hs q.1).2
  have hYUm : ∀ q, MeasurableSet (YU q) := fun q =>
    (hYm q.2).preimage (continuous_id.sub continuous_const).measurable
  have hYUT : ∀ q, YU q ⊆ tube ρ (xU q) (vU q) := by
    intro q
    rw [hxU, hvU]
    simp only
    rw [tube_translate]
    exact preimage_mono (hYT q.2)
  have hvolYU : ∀ q, volume (YU q) = volume (Y q.2) := by
    intro q
    simp only [hYU, sub_eq_add_neg]
    exact measure_preimage_add_right _ _ _
  have hmassU : ENNReal.ofReal (ρ ^ η * (Fintype.card (Fin N × Fin m) : ℝ) * ρ ^ 2) ≤
      ∑ q, volume (YU q) := by
    rw [Fintype.sum_prod_type]
    simp only [hvolYU]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
    calc ENNReal.ofReal (ρ ^ η * ((N * m : ℕ) : ℝ) * ρ ^ 2)
        = (N : ℝ≥0∞) * ENNReal.ofReal (ρ ^ η * (m : ℝ) * ρ ^ 2) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1; push_cast; ring
      _ ≤ (N : ℝ≥0∞) * ∑ i, volume (Y i) := by gcongr
  have hmaxU : ∀ q, volume (YU q) ≤ ENNReal.ofReal (144 * ρ ^ 2) := fun q =>
    (measure_mono (hYUT q)).trans (volume_tube_le hρ (hv q.2) (hv2 q.2) (hTU q))
  have hUp := dense_part hρ YU hmassU hmaxU
  set Up := Finset.univ.filter (fun q => ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) ≤ volume (YU q))
    with hUpdef
  have hcardU : r ^ 2 * Kt ≤ (Fintype.card (Fin N × Fin m) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    have := mul_le_mul_of_nonneg_right hN1 hm0.le
    rw [div_mul_cancel₀ _ hm0.ne'] at this
    linarith
  have hUpos : (0 : ℝ) < Up.card := by
    refine lt_of_lt_of_le ?_ hUp
    have : 0 < r ^ 2 * Kt := by have := lt_of_lt_of_le hρ hρr'; positivity
    have : 0 < (Fintype.card (Fin N × Fin m) : ℝ) := lt_of_lt_of_le this hcardU
    have := Real.rpow_pos_of_pos hρ η
    positivity
  have hUne : Up.Nonempty := Finset.card_pos.mp (by exact_mod_cast hUpos)
  -- Step B: regularization
  have h43' : ∀ (k : ℕ) (x' v' : Fin k → Space), (∀ i, ‖v' i‖ = 1) →
      (∀ i, tube ρ (x' i) (v' i) ⊆ ball 0 1) →
      (∀ i j, i ≠ j → volume (tube ρ (x' i) (v' i) ∩ tube ρ (x' j) (v' j)) ≤
        (1 / 2 : ℝ≥0∞) * volume (tube ρ (x' i) (v' i))) → (k : ℝ) * ρ ^ 6 ≤ C43 :=
    fun k x' v' h1 h2 h3 => h43 ρ hρ hρ100 k x' v' h1 h2 h3
  obtain ⟨S, hSU, hSne, hSnc, μb, hμb, htrans, hR4⟩ := regularize hρ hρ1' xU vU
    (fun q => hv q.2) hTU Up hUne h43' hsmall
  -- the convex count of the representatives
  set CU := A * ρ ^ (-(ηB / 4)) * Kt with hCUdef
  have hCU0 : 0 ≤ CU := by
    rw [hCUdef]; have := Real.rpow_pos_of_pos hρ (-(ηB / 4)); positivity
  have hUcount' : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {q | tube ρ (xU q) (vU q) ⊆ W} : ℕ) : ℝ) ≤
        ENNReal.ofReal CU * volume W := by
    intro W hW
    have := hUcount W hW
    have he : D55 * (27 * C57 * ρ ^ (-(ηB / 4)) * Real.log 3 * Kt) = CU := by
      rw [hCUdef, hA]; ring
    rwa [he] at this
  have hSfr := selected_frostman xU vU hTU Up S hμb hCU0 htrans hUcount'
  -- the coefficient
  set J : ℝ := ((Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊ : ℕ) : ℝ) + 1 with hJdef
  have hJ0 : 0 < J := by rw [hJdef]; positivity
  have hJle := dyadic_classes_le hρ hρ1 hσ0 hσ1
  have hUp3 : ρ ^ (3 * η) * Kt / 288 ≤ Up.card := by
    refine le_trans ?_ hUp
    have hr2 : ρ ^ (2 * η) ≤ r ^ 2 := by
      rw [show ρ ^ (2 * η) = (ρ ^ η) ^ 2 by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; ring_nf]
      exact pow_le_pow_left₀ (Real.rpow_pos_of_pos hρ _).le hρr 2
    have h3 : ρ ^ (3 * η) = ρ ^ η * ρ ^ (2 * η) := by rw [← Real.rpow_add hρ]; ring_nf
    rw [h3]
    have := Real.rpow_pos_of_pos hρ η
    have h4 : ρ ^ (2 * η) * Kt ≤ (Fintype.card (Fin N × Fin m) : ℝ) :=
      (mul_le_mul_of_nonneg_right hr2 hKt.le).trans hcardU
    calc ρ ^ η * ρ ^ (2 * η) * Kt / 288 = ρ ^ η * (ρ ^ (2 * η) * Kt) / 288 := by ring
      _ ≤ ρ ^ η * (Fintype.card (Fin N × Fin m) : ℝ) / 288 := by gcongr
  have harith := frostman_arith (ηB := ηB) (ε' := ηB / 4) hρ hKt hA0 hCpp0 hσ0 hJ0.le hJle hUp3
    hg (by rw [← hX5]; exact hT5)
  have hcoef : CU * Cpp / μb ≤ ρ ^ (-ηB) * S.card := by
    have h1 : (Up.card : ℝ) ≤ 4 * J * (S.card * μb) := by rw [hJdef]; exact hR4
    have h2 : CU * Cpp * (4 * J) ≤ ρ ^ (-ηB) * (4 * J * (S.card * μb)) :=
      harith.trans (mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hρ _).le)
    rw [div_le_iff₀ hμb]
    have h4J : 0 < 4 * J := by positivity
    have h3 : CU * Cpp * (4 * J) ≤ (ρ ^ (-ηB) * S.card * μb) * (4 * J) := by
      calc CU * Cpp * (4 * J) ≤ ρ ^ (-ηB) * (4 * J * (S.card * μb)) := h2
        _ = (ρ ^ (-ηB) * S.card * μb) * (4 * J) := by ring
    exact le_of_mul_le_mul_right h3 h4J
  -- Step C: the bounded offset estimate on the representatives
  set k := S.card with hk
  let eS : Fin k ≃ { q // q ∈ S } := S.equivFin.symm
  have hk0 : 0 < k := Finset.card_pos.mpr hSne
  have hfam : Family ηB0 ρ k (fun i => xU (eS i)) (fun i => vU (eS i)) (fun i => YU (eS i)) := by
    refine WangZahlLot.Obl.wz_normalized_projection_iteration.family_mono hρ hρ1 hηBB0 ?_
    refine ⟨hk0, fun i => hv _, fun i => hTU _, ?_, fun i => hYUm _, fun i => hYUT _, ?_⟩
    · intro i j hij
      have hne : (eS i : Fin N × Fin m) ≠ eS j := fun h => hij (eS.injective (Subtype.ext h))
      have hnc := hSnc _ (eS i).2 _ (eS j).2 hne
      unfold conflict at hnc
      push Not at hnc
      refine hnc.trans ?_
      calc ENNReal.ofReal (ρ ^ 2 / 2) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (ρ ^ 2) := by
            rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_inv_of_pos (by norm_num)]
            norm_num
        _ ≤ (1 / 2 : ℝ≥0∞) * volume (tube ρ (xU (eS i)) (vU (eS i))) := by
            gcongr
            exact WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hρ _ _ (hv _)
    · have hdense : ∀ i, ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) ≤ volume (YU (eS i)) := fun i =>
        (Finset.mem_filter.mp (hSU (eS i).2)).2
      calc ENNReal.ofReal (ρ ^ ηB * (k : ℝ) * ρ ^ 2)
          ≤ ∑ _i : Fin k, ENNReal.ofReal (ρ ^ η * ρ ^ 2 / 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            have h1 : ρ ^ ηB = ρ ^ η * ρ ^ (ηB - η) := by rw [← Real.rpow_add hρ]; ring_nf
            have h2 : 0 < ρ ^ η := Real.rpow_pos_of_pos hρ _
            rw [h1]
            have h3 : ρ ^ η * ρ ^ (ηB - η) ≤ ρ ^ η * (1 / 2) := mul_le_mul_of_nonneg_left hT4 h2.le
            have h4 : 0 ≤ (k : ℝ) * ρ ^ 2 := by positivity
            nlinarith
        _ ≤ ∑ i : Fin k, volume (YU (eS i)) := Finset.sum_le_sum fun i _ => hdense i
  have hfrost : Frostman ηB0 ρ k (fun i => xU (eS i)) (fun i => vU (eS i)) := by
    refine WangZahlLot.Obl.wz_normalized_projection_iteration.frostman_mono hρ hρ1 hηBB0 ?_
    intro W hW
    have hcard : (Set.ncard {i : Fin k | tube ρ (xU (eS i)) (vU (eS i)) ⊆ W} : ℝ) =
        ((S.filter (fun r => tube ρ (xU r) (vU r) ⊆ W)).card : ℝ) := by
      congr 1
      rw [← Set.ncard_coe_finset]
      apply Set.ncard_congr (fun i _ => (eS i : Fin N × Fin m))
      · intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi ⊢
        exact ⟨(eS i).2, hi⟩
      · intro i j _ _ hij
        exact eS.injective (Subtype.ext hij)
      · intro q hq
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
        refine ⟨eS.symm ⟨q, hq.1⟩, ?_, ?_⟩
        · simp only [Set.mem_setOf_eq, Equiv.apply_symm_apply]; exact hq.2
        · simp
    rw [hcard]
    refine (hSfr W hW).trans ?_
    rw [← hCpp]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoef) _
  have hBapp := hBε ρ hρ (hρdB) hρ100 k (fun i => xU (eS i)) (fun i => vU (eS i))
    (fun i => YU (eS i)) hfam (fun i => hv2 _) hfrost f hf (by show |f 0| ≤ 1; rw [hf0, abs_zero]; norm_num)
  -- the projection of the union of translates
  have hproj : volume (Projection f (⋃ i, YU (eS i))) ≤ N * volume (proj f (⋃ i, Y i)) := by
    refine le_trans (measure_mono (image_mono ?_))
      (volume_proj_union_translates_le hf.continuous s (fun j => (hs j).1) Y)
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨(eS i : Fin N × Fin m), hi⟩
  -- conclusion
  by_cases htop : volume (proj f (⋃ i, Y i)) = ⊤
  · rw [htop, ENNReal.mul_top (by simp [hKt])]; exact le_top
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (volume (proj f (⋃ i, Y i))).toReal := ⟨_, rfl⟩
  have haeq : volume (proj f (⋃ i, Y i)) = ENNReal.ofReal a := by
    rw [ha, ENNReal.ofReal_toReal htop]
  have ha0 : 0 ≤ a := by rw [ha]; exact ENNReal.toReal_nonneg
  rw [haeq] at hproj ⊢
  have h1 : ENNReal.ofReal (ρ ^ (ε / 2)) ≤ ENNReal.ofReal (N * a) := by
    refine hBapp.trans (hproj.trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : (N : ℝ) * a ≤ 217 * (r ^ 2 * Kt / m) * a := mul_le_mul_of_nonneg_right hN2 ha0
  have h3 : r ^ 2 ≤ 1 := by nlinarith
  have h4 : ρ ^ ε ≤ ρ ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have h5 : ρ ^ (ε / 2) * m ≤ 217 * (r ^ 2 * Kt) * a := by
    have := mul_le_mul_of_nonneg_right (h1.trans h2) hm0.le
    calc ρ ^ (ε / 2) * m ≤ 217 * (r ^ 2 * Kt / m) * a * m := this
      _ = 217 * (r ^ 2 * Kt) * a := by field_simp
  have h6 : 217 * (r ^ 2 * Kt) * a ≤ 217 * Kt * a := by
    have : r ^ 2 * Kt ≤ Kt := by nlinarith
    nlinarith
  calc ρ ^ ε * m ≤ ρ ^ (ε / 2) * m := mul_le_mul_of_nonneg_right h4 hm0.le
    _ ≤ 217 * Kt * a := h5.trans h6

end WangZahlLot.Obl.wz_intermediate_twist_normalization
