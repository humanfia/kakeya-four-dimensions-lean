-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowDecay.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/WindowDecay.lean (bf60247).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.PaletteArithmetic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- Angular profile errors become a single small power in the squared ratio
of occupied arc counts. -/
theorem profile_ratio_sq_le {r s d : ℝ} {n h i : ℕ} {F : ℕ → ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n)
    (hh : |F h - s * h| ≤ d * n) (hi : |F i - s * i| ≤ d * n) :
    (palBase r n ^ (F h - F i)) ^ (2 : ℕ) ≤
      r ^ (-4 * d) * (palScale r n i / palScale r n h) ^ (2 * s) := by
  have hB := palBase_gt_one hr hr1 hn
  have hB0 := palBase_pos (n := n) hr
  rw [← Real.rpow_mul_natCast hB0.le, rpow_eq_palBase hr hn]
  unfold palScale
  rw [← Real.rpow_sub hB0, ← Real.rpow_mul hB0.le, ← Real.rpow_add hB0]
  apply Real.rpow_le_rpow_of_exponent_le hB.le
  obtain ⟨hhl, hhu⟩ := abs_le.mp hh
  obtain ⟨hil, hiu⟩ := abs_le.mp hi
  norm_num
  linarith

/-- The ratio of average bush masses per arc has the decay predicted by a
near-linear measured angular profile. -/
theorem bush_average_ratio_sq_le {r s d : ℝ} {n h i : ℕ}
    {S : Finset (E2 × E2)} {p : E2}
    (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) (hne : (bushOf S p).Nonempty)
    (hh : |bushProfile r n S p h - s * h| ≤ d * n)
    (hi : |bushProfile r n S p i - s * i| ≤ d * n) :
    ((((bushOf S p).card : ℝ) / ((bushOf S p).image (arcOf (palScale r n i))).card) /
      (((bushOf S p).card : ℝ) / ((bushOf S p).image (arcOf (palScale r n h))).card)) ^
        (2 : ℕ) ≤ r ^ (-4 * d) * (palScale r n i / palScale r n h) ^ (2 * s) := by
  have hB := palBase_gt_one hr hr1 hn
  have hB0 := palBase_pos (n := n) hr
  have hb : (0 : ℝ) < (bushOf S p).card := by exact_mod_cast Finset.card_pos.mpr hne
  have hm (j : ℕ) : (0 : ℝ) < ((bushOf S p).image (arcOf (palScale r n j))).card := by
    exact_mod_cast Finset.card_pos.mpr (hne.image _)
  have hprof (j : ℕ) : palBase r n ^ bushProfile r n S p j =
      (((bushOf S p).image (arcOf (palScale r n j))).card : ℝ) := by
    unfold bushProfile cellProfile cellCount
    exact Real.rpow_logb hB0 hB.ne' (hm j)
  have heq :
      (((bushOf S p).card : ℝ) / ((bushOf S p).image (arcOf (palScale r n i))).card) /
        (((bushOf S p).card : ℝ) / ((bushOf S p).image (arcOf (palScale r n h))).card) =
          palBase r n ^ (bushProfile r n S p h - bushProfile r n S p i) := by
    rw [Real.rpow_sub hB0, hprof, hprof]
    field_simp
  rw [heq]
  exact profile_ratio_sq_le hr hr1 hn hh hi

/-- Every intermediate radius has a coarser palette representative with at
most one factor of the palette base. Both endpoints are retained. -/
theorem palette_bracket {r x : ℝ} {n h a : ℕ}
    (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) (hha : h ≤ a)
    (hlo : palScale r n a ≤ x) (hhi : x ≤ palScale r n h) :
    ∃ i : ℕ, h ≤ i ∧ i ≤ a ∧ x ≤ palScale r n i ∧
      palScale r n i ≤ palBase r n * x := by
  classical
  let A := (Finset.Icc h a).filter (fun i => x ≤ palScale r n i)
  have hmem : h ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hha⟩, hhi⟩
  have hne : A.Nonempty := ⟨h, hmem⟩
  let i := A.max' hne
  have hiA : i ∈ A := Finset.max'_mem A hne
  obtain ⟨⟨hhi', hia⟩, hxi⟩ := (Finset.mem_filter.mp hiA).imp_left Finset.mem_Icc.mp
  refine ⟨i, hhi', hia, hxi, ?_⟩
  have hB := palBase_gt_one hr hr1 hn
  have hB0 := palBase_pos (n := n) hr
  have hx : 0 < x := (Real.rpow_pos_of_pos hB0 _).trans_le hlo
  by_cases hia' : i = a
  · rw [hia']
    exact hlo.trans (le_mul_of_one_le_left hx.le hB.le)
  · have his : i + 1 ≤ a := by omega
    have hnext : palScale r n (i + 1) < x := by
      by_contra hh
      have hmem' : i + 1 ∈ A := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, his⟩, not_lt.mp hh⟩
      have := Finset.le_max' A (i + 1) hmem'
      change i + 1 ≤ i at this
      omega
    have hid : palScale r n i = palBase r n * palScale r n (i + 1) := by
      unfold palScale
      calc
        palBase r n ^ (-(i : ℝ)) = palBase r n ^ (1 + -((i + 1 : ℕ) : ℝ)) := by
          congr 1
          push_cast
          ring
        _ = palBase r n ^ (1 : ℝ) * palBase r n ^ (-((i + 1 : ℕ) : ℝ)) :=
          Real.rpow_add hB0 _ _
        _ = _ := by rw [Real.rpow_one]
    rw [hid]
    exact mul_le_mul_of_nonneg_left hnext.le hB0.le

/-- A square count on the discrete palette implies a Frostman count at every
radius. The only loss from bracketing is one power of the palette base. -/
theorem palette_square_decay {r s d q K L δ N : ℝ} {n h a : ℕ}
    {F : ℕ → ℝ} {A : ℝ → ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) (hha : h ≤ a)
    (hK : 0 ≤ K) (hL : 1 ≤ L) (hN : 0 ≤ N) (hq : 0 ≤ q) (hqs : q ≤ 2 * s)
    (hδ : 0 < δ) (hsmall : palScale r n a ≤ L * palScale r n h * δ)
    (hF : ∀ i, h ≤ i → i ≤ a → |F i - s * i| ≤ d * n)
    (hcount : ∀ ρ, δ ≤ ρ → A ρ ≤ N)
    (hpal : ∀ ρ, δ ≤ ρ → ρ ≤ 1 / L → ∀ i, h ≤ i → i ≤ a →
      L * palScale r n h * ρ ≤ palScale r n i →
      A ρ ≤ K * (palBase r n ^ (F h - F i)) ^ (2 : ℕ) * N) :
    ∀ ρ, δ ≤ ρ → A ρ ≤
      (L ^ (2 * s) + K * r ^ (-4 * d) * (palBase r n * L) ^ (2 * s)) * ρ ^ q * N := by
  intro ρ hρ
  have hρ0 := hδ.trans_le hρ
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hB := palBase_gt_one hr hr1 hn
  have hB0 := palBase_pos (n := n) hr
  have hsh : 0 < palScale r n h := Real.rpow_pos_of_pos hB0 _
  have hs : 0 ≤ 2 * s := hq.trans hqs
  have hC0 : 0 ≤ K * r ^ (-4 * d) * (palBase r n * L) ^ (2 * s) := by positivity
  by_cases hρL : ρ ≤ 1 / L
  · have hlo : palScale r n a ≤ L * palScale r n h * ρ :=
      hsmall.trans (mul_le_mul_of_nonneg_left hρ (by positivity))
    have hhi : L * palScale r n h * ρ ≤ palScale r n h := by
      have hmul := (le_div_iff₀ hL0).mp hρL
      nlinarith
    obtain ⟨i, hhi', hia, hxi, hix⟩ := palette_bracket hr hr1 hn hha hlo hhi
    have hsi : 0 < palScale r n i := Real.rpow_pos_of_pos hB0 _
    have hratio : palScale r n i / palScale r n h ≤ (palBase r n * L) * ρ := by
      rw [div_le_iff₀ hsh]
      nlinarith [hix]
    have hρ1 : ρ ≤ 1 := by
      have hinv : 1 / L ≤ 1 := (div_le_one hL0).mpr hL
      exact hρL.trans hinv
    have hdecay := profile_ratio_sq_le hr hr1 hn (hF h le_rfl hha) (hF i hhi' hia)
    calc
      A ρ ≤ K * (palBase r n ^ (F h - F i)) ^ (2 : ℕ) * N :=
        hpal ρ hρ hρL i hhi' hia hxi
      _ ≤ K * (r ^ (-4 * d) * (palScale r n i / palScale r n h) ^ (2 * s)) * N := by
        gcongr
      _ ≤ K * (r ^ (-4 * d) * ((palBase r n * L) * ρ) ^ (2 * s)) * N := by
        gcongr
      _ = K * r ^ (-4 * d) * (palBase r n * L) ^ (2 * s) * ρ ^ (2 * s) * N := by
        rw [Real.mul_rpow (by positivity) hρ0.le]
        ring
      _ ≤ K * r ^ (-4 * d) * (palBase r n * L) ^ (2 * s) * ρ ^ q * N := by
        apply mul_le_mul_of_nonneg_right _ hN
        apply mul_le_mul_of_nonneg_left _ hC0
        exact Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 hqs
      _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_left (Real.rpow_nonneg hL0.le _)
  · have hLρ : 1 ≤ L * ρ := by
      have := (div_lt_iff₀ hL0).mp (lt_of_not_ge hρL)
      linarith
    have h1 : 1 ≤ L ^ q * ρ ^ q := by
      rw [← Real.mul_rpow hL0.le hρ0.le]
      exact Real.one_le_rpow hLρ hq
    have hLpow : L ^ q ≤ L ^ (2 * s) := Real.rpow_le_rpow_of_exponent_le hL hqs
    calc A ρ ≤ N := hcount ρ hρ
      _ ≤ (L ^ q * ρ ^ q) * N := le_mul_of_one_le_left hN h1
      _ ≤ L ^ (2 * s) * ρ ^ q * N := by gcongr
      _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_right hC0

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
