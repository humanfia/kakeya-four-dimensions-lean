-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowLineFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/WindowLineFrostman.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowCounts
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeLineFrostman
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAObjects
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TopLevel
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeChart

/-!
# Tube-line Frostman for the lines of a window tube

In a `HighConfig` at the window `(a, h)` (`δ = palScale a`, `ρ = palScale h`), the `δ`-lines
`windowLines S cls tb a h T` of a coarse tube `T` (composed map `tb h ∘ tb a ∘ cls`) satisfy, at
every third palette index `i` with `w = palScale i ≥ 5 λ ρ'`,

`#{j ∈ windowLines : tubeLine j ∈ ρ'-square} ≤ Kwin · (avg_i / avg_h)² · #windowLines`

(`HighConfig.window_square_le`), where `avg_j` is the average number of normals of a reference
pin per occupied `palScale j`-arc: `coarse_square_count` with the label counts of
`fiber_le_of_balanced` (`bal_tube i`), `fiber_ge_of_balanced` (the composed balance),
`composed_tubes_le`, `HighConfig.tubes_upper` at `h` and `HighConfig.tubes_lower` at `i`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

attribute [local instance] Classical.propDecidable

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)} {tb : ℕ → E2 × E2 → E2 × E2}

/-- The algebra of `HighConfig.window_square_le`. -/
theorem window_algebra {A LT La nS tI tH tC Jc avgI avgH L K Cn Cq Cp aTC R : ℝ}
    (hLa : 0 < La) (hLT : 0 < LT) (htI : 0 < tI) (havgH : 0 < avgH) (havgI : 0 < avgI)
    (hK : 0 < K) (hCn : 0 ≤ Cn) (hR : 0 < R) (haTC : 0 < aTC) (hCp : 0 ≤ Cp)
    (hJc : 0 ≤ Jc) (hA : 0 ≤ A)
    (h1 : A * (La / K * LT) ≤ Cn ^ 2 * (K * nS / tI) * (K * La) * Jc)
    (h2 : nS ≤ K * tC * LT) (h3 : tC ≤ Cn * tH)
    (h4 : tH * (avgH / (K ^ 2 * aTC)) ^ 2 ≤ Cq * L)
    (h5 : (R / (2 * (49 * (K * avgI)))) ^ 2 ≤ Cp * tI) :
    A ≤ (Cn ^ 3 * K ^ 4 * Cq * Cp * (K ^ 2 * aTC) ^ 2 * (2 * (49 * K)) ^ 2 * L / R ^ 2) *
      (avgI / avgH) ^ 2 * Jc := by
  -- step 1: clear `La / K` and `tI`
  have e1 : A * LT * tI ≤ Cn ^ 2 * K ^ 3 * nS * Jc := by
    have hpos : 0 < K * tI / La := by positivity
    have := mul_le_mul_of_nonneg_right h1 hpos.le
    have l : A * (La / K * LT) * (K * tI / La) = A * LT * tI := by
      field_simp
    have rr : Cn ^ 2 * (K * nS / tI) * (K * La) * Jc * (K * tI / La) =
        Cn ^ 2 * K ^ 3 * nS * Jc := by
      field_simp
    linarith
  -- step 2: `nS ≤ K Cn tH LT`, cancel `LT`
  have e2 : A * tI ≤ Cn ^ 3 * K ^ 4 * tH * Jc := by
    have hnS : nS ≤ K * Cn * tH * LT := by
      calc nS ≤ K * tC * LT := h2
        _ ≤ K * (Cn * tH) * LT := by
            apply mul_le_mul_of_nonneg_right _ hLT.le
            exact mul_le_mul_of_nonneg_left h3 hK.le
        _ = K * Cn * tH * LT := by ring
    have h' : A * LT * tI ≤ Cn ^ 2 * K ^ 3 * (K * Cn * tH * LT) * Jc := by
      calc A * LT * tI ≤ Cn ^ 2 * K ^ 3 * nS * Jc := e1
        _ ≤ Cn ^ 2 * K ^ 3 * (K * Cn * tH * LT) * Jc := by
            apply mul_le_mul_of_nonneg_right _ hJc
            exact mul_le_mul_of_nonneg_left hnS (by positivity)
    have h'' : LT * (A * tI) ≤ LT * (Cn ^ 3 * K ^ 4 * tH * Jc) := by
      have : Cn ^ 2 * K ^ 3 * (K * Cn * tH * LT) * Jc = LT * (Cn ^ 3 * K ^ 4 * tH * Jc) := by ring
      nlinarith
    exact le_of_mul_le_mul_left h'' hLT
  -- step 3: bound `tH` above and `tI` below
  have htH' : tH ≤ Cq * L * (K ^ 2 * aTC) ^ 2 / avgH ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : tH * (avgH / (K ^ 2 * aTC)) ^ 2 * (K ^ 2 * aTC) ^ 2 = tH * avgH ^ 2 := by
      field_simp
    nlinarith [h4, sq_nonneg (K ^ 2 * aTC)]
  have htI' : R ^ 2 ≤ Cp * tI * (2 * (49 * (K * avgI))) ^ 2 := by
    have : (R / (2 * (49 * (K * avgI)))) ^ 2 * (2 * (49 * (K * avgI))) ^ 2 = R ^ 2 := by
      field_simp
    nlinarith [h5, sq_nonneg (2 * (49 * (K * avgI)))]
  -- combine
  have hfin : A * R ^ 2 ≤ Cn ^ 3 * K ^ 4 * tH * Jc * (Cp * (2 * (49 * (K * avgI))) ^ 2) := by
    calc A * R ^ 2 ≤ A * (Cp * tI * (2 * (49 * (K * avgI))) ^ 2) :=
          mul_le_mul_of_nonneg_left htI' hA
      _ = (A * tI) * (Cp * (2 * (49 * (K * avgI))) ^ 2) := by ring
      _ ≤ Cn ^ 3 * K ^ 4 * tH * Jc * (Cp * (2 * (49 * (K * avgI))) ^ 2) :=
          mul_le_mul_of_nonneg_right e2 (by positivity)
  have hfin2 : A * R ^ 2 ≤ Cn ^ 3 * K ^ 4 * (Cq * L * (K ^ 2 * aTC) ^ 2 / avgH ^ 2) * Jc *
      (Cp * (2 * (49 * (K * avgI))) ^ 2) := by
    refine hfin.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hJc
    exact mul_le_mul_of_nonneg_left htH' (by positivity)
  have hfin3 := (le_div_iff₀ (by positivity : (0:ℝ) < R ^ 2)).mpr hfin2
  calc A ≤ Cn ^ 3 * K ^ 4 * (Cq * L * (K ^ 2 * aTC) ^ 2 / avgH ^ 2) * Jc *
        (Cp * (2 * (49 * (K * avgI))) ^ 2) / R ^ 2 := hfin3
    _ = (Cn ^ 3 * K ^ 4 * Cq * Cp * (K ^ 2 * aTC) ^ 2 * (2 * (49 * K)) ^ 2 * L / R ^ 2) *
        (avgI / avgH) ^ 2 * Jc := by
        field_simp

/-- The window constant: everything but the arc-average ratio. -/
noncomputable def winConst (r s ε K c w CY : ℝ) (KY : ℕ) (L : ℝ) : ℝ :=
  nearTubeConst ^ 3 * K ^ 4 * quadConst r s ε K c * pinConst w CY KY *
    (K ^ 2 * arcTubeConst) ^ 2 * (2 * (49 * K)) ^ 2 * L / (r ^ (ε - s)) ^ 2

/-- **Chart squares of a window tube at a third palette index `i`.** -/
theorem HighConfig.window_square_le (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {a h i : ℕ} (ha : a ≤ n) (hh : h ≤ n) (hi : i ≤ n)
    (hδw : palScale r n a ≤ palScale r n i) (hw67 : 67 * palScale r n i ≤ 1 / 2)
    (hrw : 2 * r ≤ palScale r n i)
    (hδρ : 2 * palScale r n a ≤ palScale r n h) (hrρ : 10 * r ≤ palScale r n h)
    (hρ142 : 142 * palScale r n h ≤ 1 / 2)
    (hbal2 : Balanced S (fun q => tb h (tb a (cls q))) (r ^ (-ε)))
    {T : E2 × E2} (hT : T ∈ S.image (fun q => tb h (tb a (cls q))))
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) {c : ℝ} (hrc : r ≤ c)
    (hcfar : r ^ (-κ) * c ^ (1 - s) ≤ 1 / 2) (KY : ℕ)
    (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY)
    {v : Plane} (hv : ‖v‖ = 1) {cT aT lam ρ' : ℝ} (hlam : 0 < lam) (hρ' : 0 < ρ')
    (hWw : 5 * lam * ρ' ≤ palScale r n i)
    (hJt : ∀ j ∈ windowLines S cls tb a h T,
      ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)|) (x y : ℝ) :
    (((windowLines S cls tb a h T).filter (fun j => |(tubeLine v cT aT lam j).1 - x| ≤ ρ' ∧
        |(tubeLine v cT aT lam j).2 - y| ≤ ρ')).card : ℝ) ≤
      winConst r s ε (r ^ (-ε)) c (palScale r n i)
          (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card *
        (arcAvg (palScale r n i) S p₀ / arcAvg (palScale r n h) S p₀) ^ 2 *
          (windowLines S cls tb a h T).card := by
  classical
  have hr := hC.fail.r_pos
  set K := r ^ (-ε) with hKdef
  have hK : 0 < K := Real.rpow_pos_of_pos hr _
  have hpal : ∀ j : ℕ, 0 < palScale r n j := fun j =>
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hr _) _
  set δ := palScale r n a with hδdef
  set ρ := palScale r n h with hρdef
  set w := palScale r n i with hwdef
  have hδ : 0 < δ := hpal a
  obtain ⟨htbJ₁a, htbJ₀a, hJ₀4, hJ₁na, hJ₁sepa, htbgeoa⟩ := hC.tube_facts ha
  obtain ⟨htbJ₁h, htbJ₀h, -, hJ₁nh, hJ₁seph, htbgeoh⟩ := hC.tube_facts hh
  obtain ⟨htbJ₁i, htbJ₀i, -, hJ₁ni, hJ₁sepi, htbgeoi⟩ := hC.tube_facts hi
  have hcls : ∀ q ∈ S, cls q ∈ J₀ := fun q hq => (hC.label_facts hq).2.2.2.1
  obtain ⟨qT, hqTS, hqTT⟩ := Finset.mem_image.mp hT
  -- label counts of the `δ`-tubes
  set La : ℝ := ((S.filter (fun q' => tb a (cls q') = tb a (cls qT))).card : ℝ) with hLa
  have hLapos : 0 < La := by
    have hmem : qT ∈ S.filter (fun q' => tb a (cls q') = tb a (cls qT)) :=
      Finset.mem_filter.mpr ⟨hqTS, rfl⟩
    rw [hLa]; exact_mod_cast Finset.card_pos.mpr ⟨qT, hmem⟩
  have hbalA := hC.bal_tube a ha
  have hfibA : ∀ q ∈ S, leafFiber S (fun q => tb a (cls q)) q =
      S.filter (fun q' => tb a (cls q') = tb a (cls q)) := by
    intro q _; ext x; simp [leafFiber]
  have hLminA' : ∀ q ∈ S, La / K ≤ ((S.filter (fun q' => tb a (cls q') = tb a (cls q))).card : ℝ) := by
    intro q hq
    have := hbalA qT hqTS q hq
    rw [hfibA qT hqTS, hfibA q hq] at this
    rw [div_le_iff₀ hK]; linarith
  have hLmaxA' : ∀ q ∈ S, ((S.filter (fun q' => tb a (cls q') = tb a (cls q))).card : ℝ) ≤ K * La := by
    intro q hq
    have := hbalA q hq qT hqTS
    rw [hfibA qT hqTS, hfibA q hq] at this
    exact this
  -- label counts of the `w`-tubes
  set nS : ℝ := (S.card : ℝ) with hnS
  set tI : ℝ := ((S.image (fun q => tb i (cls q))).card : ℝ) with htI
  have htIpos : 0 < tI := by
    rw [htI]; exact_mod_cast Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ hqTS⟩
  have hLmaxI' : ∀ k' ∈ J₁ i, ((S.filter (fun q => tb i (cls q) = k')).card : ℝ) ≤ K * nS / tI := by
    intro k' _
    by_cases hk : ∃ q ∈ S, tb i (cls q) = k'
    · obtain ⟨q, hq, rfl⟩ := hk
      have hf := fiber_le_of_balanced (hC.bal_tube i hi) hq
      rw [le_div_iff₀ htIpos]
      exact hf
    · push Not at hk
      have : S.filter (fun q => tb i (cls q) = k') = ∅ := by
        ext q; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        exact hk q
      rw [this, Finset.card_empty, Nat.cast_zero]
      positivity
  -- the square count (`coarse_square_count` with the composed outer map)
  have hJt' : ∀ j ∈ (S.filter (fun q => tb h (tb a (cls q)) = T)).image (fun q => tb a (cls q)),
      ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)| := hJt
  have hsq := coarse_square_count (S := S) (J₀ := J₀) (J₁ := J₁ i) (cls := cls) (tbA := tb a)
    (tbI := tb i) (tbH := fun ℓ => tb h (tb a ℓ)) (T := T) (c := x) (a := y) (cT := cT) (aT := aT)
    hv hlam hρ' hδ hδw hw67 hWw (by positivity) (by positivity)
    hcls hJ₀4 htbJ₀a htbgeoa htbJ₁i htbgeoi hJ₁ni hJ₁sepi hLminA' hLmaxA' hLmaxI' hJt'
  -- `L_T`: the labels of `T`, against all labels (composed balance)
  set LT : ℝ := ((S.filter (fun q => tb h (tb a (cls q)) = T)).card : ℝ) with hLT
  have hLTpos : 0 < LT := by
    rw [hLT]; exact_mod_cast Finset.card_pos.mpr ⟨qT, Finset.mem_filter.mpr ⟨hqTS, hqTT⟩⟩
  set tC : ℝ := ((S.image (fun q => tb h (tb a (cls q)))).card : ℝ) with htC
  have h2 : nS ≤ K * tC * LT := by
    have := fiber_ge_of_balanced hbal2 hqTS
    rw [hqTT] at this
    exact this
  set tH : ℝ := ((S.image (fun q => tb h (cls q))).card : ℝ) with htH
  have h3 : tC ≤ nearTubeConst * tH :=
    composed_tubes_le hδ hδρ (by linarith) hcls hJ₀4 htbJ₀a htbgeoa htbJ₁h htbgeoh hJ₁nh hJ₁seph
  have h4 := hC.tubes_upper hs0 hs1 hh hrρ hρ142 hp₀ hrc hcfar
  have h5 := hC.tubes_lower hi hrw (by linarith) hp₀ KY hKY
  -- arc averages are positive
  have havg : ∀ j : ℕ, 0 < arcAvg (palScale r n j) S p₀ := by
    intro j
    obtain ⟨q₀, hq₀S, hq₀p⟩ := Finset.mem_image.mp hp₀
    have hne : (bushOf S p₀).Nonempty := ⟨q₀.2, by rw [mem_bushOf, ← hq₀p]; exact hq₀S⟩
    unfold arcAvg
    have h1 : (0 : ℝ) < (bushOf S p₀).card := by exact_mod_cast Finset.card_pos.mpr hne
    have h2 : (0 : ℝ) < ((bushOf S p₀).image (arcOf (palScale r n j))).card := by
      exact_mod_cast Finset.card_pos.mpr (hne.image _)
    positivity
  have hR : 0 < r ^ (ε - s) := Real.rpow_pos_of_pos hr _
  have haTC : 0 < arcTubeConst := by rw [arcTubeConst]; norm_num
  have hCp : 0 ≤ pinConst w (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY := by
    unfold pinConst
    have hQ : (0 : ℝ) < ((S.image Prod.fst).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ hqTS⟩
    have hw0 : 0 < w := hpal i
    have h26 : 0 ≤ Real.log (1 / (26 * w)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (mul_pos (by norm_num) hw0)]; linarith
    have e1 : 0 ≤ 64 * (26 * w) / w + 2 := by positivity
    have e2 : 0 ≤ 36 * (26 * w) / w + 2 := by positivity
    have e3 : 0 ≤ r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ) := by
      have := Real.rpow_nonneg hr.le (-ε); positivity
    positivity
  have hfinal := window_algebra (A := (((windowLines S cls tb a h T).filter (fun j =>
      |(tubeLine v cT aT lam j).1 - x| ≤ ρ' ∧ |(tubeLine v cT aT lam j).2 - y| ≤ ρ')).card : ℝ))
    (LT := LT) (La := La) (nS := nS) (tI := tI) (tH := tH) (tC := tC)
    (Jc := ((windowLines S cls tb a h T).card : ℝ))
    (avgI := arcAvg w S p₀) (avgH := arcAvg ρ S p₀) (L := ((S.image cls).card : ℝ)) (K := K)
    (Cn := nearTubeConst) (Cq := quadConst r s ε K c)
    (Cp := pinConst w (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY) (aTC := arcTubeConst)
    (R := r ^ (ε - s)) hLapos hLTpos htIpos (havg h) (havg i) hK nearTubeConst_pos.le hR haTC hCp
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsq h2 h3 h4 h5
  unfold winConst
  exact hfinal

/-! ### From arc averages to the bush profile, and the palette index -/

/-- `arcOf` and `cellOf` are the same square cells. -/
theorem image_arcOf_eq_cellOf (Q : Finset E2) (ρ : ℝ) :
    Q.image (arcOf ρ) = Q.image (cellOf ρ) := rfl

/-- The ratio of two arc averages of a reference pin is a power of the palette base: the arcs
are counted by the bush profile. -/
theorem arcAvg_ratio_eq {r : ℝ} {n : ℕ} (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n)
    {S : Finset (E2 × E2)} {p₀ : E2} (hne : (bushOf S p₀).Nonempty) (i h : ℕ) :
    arcAvg (palScale r n i) S p₀ / arcAvg (palScale r n h) S p₀ =
      palBase r n ^ (bushProfile r n S p₀ h - bushProfile r n S p₀ i) := by
  have hB := palBase_gt_one hr hr1 hn
  have hcount : ∀ j : ℕ, (((bushOf S p₀).image (arcOf (palScale r n j))).card : ℝ) =
      palBase r n ^ (bushProfile r n S p₀ j) := by
    intro j
    rw [image_arcOf_eq_cellOf]
    unfold bushProfile cellProfile
    rw [Real.rpow_logb (by linarith) (by linarith : palBase r n ≠ 1)
      (by exact_mod_cast cellCount_pos hne _)]
    rfl
  unfold arcAvg
  rw [hcount i, hcount h]
  have hbush : (0 : ℝ) < (bushOf S p₀).card := by exact_mod_cast Finset.card_pos.mpr hne
  have hBpos : 0 < palBase r n := by linarith
  rw [Real.rpow_sub hBpos]
  have h1 : 0 < palBase r n ^ (bushProfile r n S p₀ i) := Real.rpow_pos_of_pos hBpos _
  have h2 : 0 < palBase r n ^ (bushProfile r n S p₀ h) := Real.rpow_pos_of_pos hBpos _
  field_simp

/-- With near-uniform bushes `|F t - s t| ≤ d n`, the squared arc-average ratio is at most
`(palScale i / palScale h) ^ (2 s) · r ^ (-4 d)`. -/
theorem arcAvg_ratio_sq_le {r s d : ℝ} {n : ℕ} (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n)
    {S : Finset (E2 × E2)} {p₀ : E2} (hne : (bushOf S p₀).Nonempty) {i h : ℕ} (hi : i ≤ n)
    (hh : h ≤ n) (hunif : ∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ d * n) :
    (arcAvg (palScale r n i) S p₀ / arcAvg (palScale r n h) S p₀) ^ 2 ≤
      (palScale r n i / palScale r n h) ^ (2 * s) * r ^ (-(4 * d)) := by
  have hB := palBase_gt_one hr hr1 hn
  have hBpos : 0 < palBase r n := by linarith
  rw [arcAvg_ratio_eq hr hr1 hn hne i h]
  have hFi := abs_le.mp (hunif i hi)
  have hFh := abs_le.mp (hunif h hh)
  have hexp : bushProfile r n S p₀ h - bushProfile r n S p₀ i ≤ s * ((h : ℝ) - i) + 2 * d * n := by
    linarith [hFi.1, hFh.2]
  have hratio : palScale r n i / palScale r n h = palBase r n ^ ((h : ℝ) - i) := by
    unfold palScale
    rw [← Real.rpow_sub hBpos]
    congr 1; ring
  have hr4 : r ^ (-(4 * d)) = palBase r n ^ ((n : ℝ) * (4 * d)) := by
    rw [rpow_eq_palBase hr hn]; congr 1; ring
  rw [hratio, hr4, ← Real.rpow_mul hBpos.le, ← Real.rpow_add hBpos, ← Real.rpow_natCast,
    ← Real.rpow_mul hBpos.le]
  apply Real.rpow_le_rpow_of_exponent_le hB.le
  push_cast
  nlinarith

/-- **A palette index at every scale.** For `palScale a ≤ W ≤ 1` some `i ≤ a` has
`W ≤ palScale i ≤ palBase · W`. -/
theorem exists_palette_index {r : ℝ} {n : ℕ} (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n)
    {a : ℕ} {W : ℝ} (hW : palScale r n a ≤ W) (hW1 : W ≤ 1) :
    ∃ i : ℕ, i ≤ a ∧ W ≤ palScale r n i ∧ palScale r n i ≤ palBase r n * W := by
  have hB := palBase_gt_one hr hr1 hn
  have hBpos : 0 < palBase r n := by linarith
  have hWpos : 0 < W := lt_of_lt_of_le (Real.rpow_pos_of_pos hBpos _) hW
  set x := Real.logb (palBase r n) (1 / W) with hx
  have hx0 : 0 ≤ x := by
    apply Real.logb_nonneg hB
    rw [le_div_iff₀ hWpos]; linarith
  have hxa : x ≤ a := by
    rw [hx, Real.logb_le_iff_le_rpow hB (by positivity)]
    have : palScale r n a = palBase r n ^ (-(a : ℝ)) := rfl
    rw [this] at hW
    rw [div_le_iff₀ hWpos]
    calc (1 : ℝ) = palBase r n ^ (a : ℝ) * palBase r n ^ (-(a : ℝ)) := by
          rw [← Real.rpow_add hBpos]; simp
      _ ≤ palBase r n ^ (a : ℝ) * W := by
          apply mul_le_mul_of_nonneg_left hW (Real.rpow_nonneg hBpos.le _)
  refine ⟨⌊x⌋₊, ?_, ?_, ?_⟩
  · have := Nat.floor_le_floor (R := ℝ) hxa
    rwa [Nat.floor_natCast] at this
  · -- `palScale ⌊x⌋ = B^(-⌊x⌋) ≥ B^(-x) = W`
    unfold palScale
    have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    calc W = palBase r n ^ (-x) := by
          rw [hx, Real.rpow_neg hBpos.le, Real.rpow_logb hBpos (by linarith) (by positivity)]
          field_simp
      _ ≤ palBase r n ^ (-(⌊x⌋₊ : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hB.le (by linarith)
  · unfold palScale
    have hfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hW' : W = palBase r n ^ (-x) := by
      rw [hx, Real.rpow_neg hBpos.le, Real.rpow_logb hBpos (by linarith) (by positivity)]
      field_simp
    calc palBase r n ^ (-(⌊x⌋₊ : ℝ)) = palBase r n ^ ((1 : ℝ) + -(⌊x⌋₊ + 1 : ℝ)) := by
          congr 1; ring
      _ = palBase r n * palBase r n ^ (-(⌊x⌋₊ + 1 : ℝ)) := by
          rw [Real.rpow_add hBpos, Real.rpow_one]
      _ ≤ palBase r n * palBase r n ^ (-x) := by
          apply mul_le_mul_of_nonneg_left _ hBpos.le
          exact Real.rpow_le_rpow_of_exponent_le hB.le (by linarith)
      _ = palBase r n * W := by rw [hW']

/-- `pinConst` decreases in the width. -/
theorem pinConst_anti {r w CY : ℝ} {KY : ℕ} (hr : 0 < r) (hrw : r ≤ w) (hw2 : 26 * w ≤ 1)
    (hCY : 0 ≤ CY) : pinConst w CY KY ≤ pinConst r CY KY := by
  unfold pinConst
  have hw : 0 < w := lt_of_lt_of_le hr hrw
  have e1 : 64 * (26 * w) / w = 64 * 26 := by field_simp
  have e2 : 36 * (26 * w) / w = 36 * 26 := by field_simp
  have e3 : 64 * (26 * r) / r = 64 * 26 := by field_simp
  have e4 : 36 * (26 * r) / r = 36 * 26 := by field_simp
  rw [e1, e2, e3, e4]
  have hlog : Real.log (1 / (26 * w)) ≤ Real.log (1 / (26 * r)) := by
    apply Real.log_le_log (by positivity)
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hlog0 : 0 ≤ Real.log (1 / (26 * w)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have hK : (0 : ℝ) ≤ ((KY : ℝ) + 1) ^ 2 := by positivity
  have hC : (0 : ℝ) ≤ 128000 * (64 * 26 + 2) * (36 * 26 + 2) * CY := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add_left hlog 1) hC
  nlinarith

theorem pinConst_nonneg' {w CY : ℝ} {KY : ℕ} (hw : 0 < w) (hw26 : 26 * w ≤ 1) (hCY : 0 ≤ CY) :
    0 ≤ pinConst w CY KY := by
  unfold pinConst
  have h26 : 0 ≤ Real.log (1 / (26 * w)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have e1 : 0 ≤ 64 * (26 * w) / w + 2 := by positivity
  have e2 : 0 ≤ 36 * (26 * w) / w + 2 := by positivity
  positivity

theorem winConst_nonneg {r s ε K c w CY L : ℝ} {KY : ℕ} (hr : 0 < r) (hK : 0 ≤ K) (hc : 0 < c)
    (hw : 0 < w) (hw26 : 26 * w ≤ 1) (hCY : 0 ≤ CY) (hL : 0 ≤ L) :
    0 ≤ winConst r s ε K c w CY KY L := by
  unfold winConst
  have hq := quadConst_nonneg (s := s) (ε := ε) hr hK hc
  have hp := pinConst_nonneg' (KY := KY) hw hw26 hCY
  have hR : 0 < (r ^ (ε - s)) ^ 2 := by have := Real.rpow_pos_of_pos hr (ε - s); positivity
  have haTC : 0 < arcTubeConst := by rw [arcTubeConst]; norm_num
  have hn := nearTubeConst_pos
  positivity

/-- The constant of the tube-line Frostman bound of a window tube. -/
noncomputable def lineFrConst (r s ε c CY : ℝ) (KY : ℕ) (L d B : ℝ) : ℝ :=
  max 1 (winConst r s ε (r ^ (-ε)) c r CY KY L * r ^ (-(4 * d)) * (320 * B) ^ (2 * s))

theorem winConst_mono_pin {r s ε K c w w' CY L : ℝ} {KY : ℕ} (hr : 0 < r) (hK : 0 ≤ K)
    (hc : 0 < c) (hL : 0 ≤ L) (hpin : pinConst w CY KY ≤ pinConst w' CY KY) :
    winConst r s ε K c w CY KY L ≤ winConst r s ε K c w' CY KY L := by
  unfold winConst
  have hq := quadConst_nonneg (s := s) (ε := ε) hr hK hc
  have hR : 0 < (r ^ (ε - s)) ^ 2 := by have := Real.rpow_pos_of_pos hr (ε - s); positivity
  have haTC : 0 < arcTubeConst := by rw [arcTubeConst]; norm_num
  have hn := nearTubeConst_pos
  apply div_le_div_of_nonneg_right _ hR.le
  apply mul_le_mul_of_nonneg_right _ hL
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left hpin (by positivity)

/-- **Tube-line Frostman of a window tube**, in the frame of `caseA_window_false` /
`caseA_window_two_ends_false` (x0672): axis `tubeAxis T`, central line `lineChart (tubeAxis T) T`,
vertical scale `4 · 16 ρ`, every `ρ' ≥ δ / (100 ρ)` (below both tolerances `243 δ / (128 ρ)` and
`tubeTol (27 δ) (16 ρ) (ρ / 2) ≥ 108 δ / (64 ρ)`). With near-uniform bushes
`|F t - s t| ≤ d n`:
`#{j ∈ windowLines : tubeLine j ∈ ρ'-square} ≤ lineFrConst · ρ' ^ (2 s) · #windowLines`. -/
theorem HighConfig.window_line_frostman (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hn : 0 < n) (hr1 : r < 1)
    {a h : ℕ} (ha : a ≤ n) (hh : h ≤ n)
    (hδρ : 2 * palScale r n a ≤ palScale r n h) (hrρ : 10 * r ≤ palScale r n h)
    (hρsmall : 21440 * palBase r n * palScale r n h ≤ 1 / 2)
    {T : E2 × E2} (hT : T ∈ S.image (fun q => tb h (tb a (cls q))))
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) {c : ℝ} (hrc : r ≤ c)
    (hcfar : r ^ (-κ) * c ^ (1 - s) ≤ 1 / 2) (KY : ℕ)
    (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY) {d : ℝ}
    (hunif : ∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ d * n) :
    ∀ x y ρ' : ℝ, palScale r n a / (100 * palScale r n h) ≤ ρ' →
      (((windowLines S cls tb a h T).filter (fun j =>
        |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
          (4 * (16 * palScale r n h)) j).1 - x| ≤ ρ' ∧
        |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
          (4 * (16 * palScale r n h)) j).2 - y| ≤ ρ')).card : ℝ) ≤
      lineFrConst r s ε c (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card d
        (palBase r n) * ρ' ^ (2 * s) * (windowLines S cls tb a h T).card := by
  classical
  intro x y ρ' hρ'
  have hr := hC.fail.r_pos
  have hB := palBase_gt_one hr hr1 hn
  have hpal : ∀ j : ℕ, 0 < palScale r n j := fun j =>
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hr _) _
  set δ := palScale r n a with hδdef
  set ρ := palScale r n h with hρdef
  set B := palBase r n with hBdef
  have hδ : 0 < δ := hpal a
  have hρ : 0 < ρ := hpal h
  have hrδ : r ≤ δ := r_le_palScale hr hr1 hn ha
  have hρ'pos : 0 < ρ' := lt_of_lt_of_le (by positivity) hρ'
  set J := windowLines S cls tb a h T with hJdef
  set Sq := J.filter (fun j =>
    |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
      (4 * (16 * ρ)) j).1 - x| ≤ ρ' ∧
    |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
      (4 * (16 * ρ)) j).2 - y| ≤ ρ') with hSqdef
  have hSqJ : (Sq.card : ℝ) ≤ J.card := by exact_mod_cast Finset.card_filter_le _ _
  have hK1 : 1 ≤ lineFrConst r s ε c (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
      (S.image cls).card d B := le_max_left _ _
  by_cases hbig : 1 ≤ ρ'
  · -- trivial range
    have : 1 ≤ ρ' ^ (2 * s) := Real.one_le_rpow hbig (by linarith)
    calc (Sq.card : ℝ) ≤ J.card := hSqJ
      _ = 1 * 1 * J.card := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul hK1 this zero_le_one (by linarith)
  · push Not at hbig
    -- the facts of `T`
    obtain ⟨qT, hqTS, hqTT⟩ := Finset.mem_image.mp hT
    obtain ⟨htbJ₁a, htbJ₀a, hJ₀4, -, -, -⟩ := hC.tube_facts ha
    obtain ⟨htbJ₁h, htbJ₀h, -, hJ₁nh, -, -⟩ := hC.tube_facts hh
    have hTJ₁ : T ∈ J₁ h := by
      rw [← hqTT]; exact htbJ₁h _ (htbJ₀a _ (hC.label_facts hqTS).2.2.2.1)
    obtain ⟨hT4, hT2⟩ := hJ₁nh T hTJ₁
    have hρ12 : ρ ≤ 1 / 2 := by nlinarith
    -- the transversality of the window lines
    have hgeo := (window_geometry hC ha hh hrδ T).1
    have hJt : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp (tubeAxis T))| := by
      intro j hj
      obtain ⟨h1, h2, h3, h4⟩ := hgeo j hj
      exact ⟨h1, h2, (near_tube_chart (lam := 4 * (16 * ρ)) hT2 hT4 h1 hρ12 (by positivity)
        h3 h4).1⟩
    -- the palette index at the scale `W = 5 λ ρ' = 320 ρ ρ'`
    set W := 5 * (4 * (16 * ρ)) * ρ' with hW
    have hWδ2 : 2 * δ ≤ W := by
      have h1 : δ / (100 * ρ) * ρ ≤ ρ' * ρ := mul_le_mul_of_nonneg_right hρ' hρ.le
      have h2 : δ / (100 * ρ) * ρ = δ / 100 := by field_simp
      rw [hW]; nlinarith
    have hWδ : δ ≤ W := by linarith
    have hW1 : W ≤ 1 := by
      rw [hW]; nlinarith
    obtain ⟨i, hia, hWi, hiBW⟩ := exists_palette_index hr hr1 hn hWδ hW1
    have hi : i ≤ n := le_trans hia ha
    have hw67 : 67 * palScale r n i ≤ 1 / 2 := by
      have : palScale r n i ≤ B * (320 * ρ) := by
        calc palScale r n i ≤ B * W := hiBW
          _ ≤ B * (320 * ρ) := by
              apply mul_le_mul_of_nonneg_left _ (by linarith)
              rw [hW]; nlinarith
      nlinarith
    have hrw : 2 * r ≤ palScale r n i := by linarith
    have hsq := hC.window_square_le (cT := (lineChart (tubeAxis T) T).1)
      (aT := (lineChart (tubeAxis T) T).2) hs0 hs1 ha hh hi (le_trans hWδ hWi) hw67 hrw hδρ hrρ
      (by nlinarith) (hC.bal_tube2 h hh a ha) hT hp₀ hrc hcfar KY hKY
      (tubeAxis_norm hT2) (by positivity : (0 : ℝ) < 4 * (16 * ρ)) hρ'pos hWi hJt x y
    -- the arc-average ratio
    obtain ⟨q₀, hq₀S, hq₀p⟩ := Finset.mem_image.mp hp₀
    have hne : (bushOf S p₀).Nonempty := ⟨q₀.2, by rw [mem_bushOf, ← hq₀p]; exact hq₀S⟩
    have hratio := arcAvg_ratio_sq_le hr hr1 hn hne hi hh hunif
    have hscale : palScale r n i / ρ ≤ 320 * B * ρ' := by
      rw [div_le_iff₀ hρ]
      calc palScale r n i ≤ B * W := hiBW
        _ = 320 * B * ρ' * ρ := by rw [hW]; ring
    have hpow : (palScale r n i / ρ) ^ (2 * s) ≤ (320 * B) ^ (2 * s) * ρ' ^ (2 * s) := by
      have h320 : (0 : ℝ) ≤ 320 * B := by linarith
      rw [← Real.mul_rpow h320 hρ'pos.le]
      exact Real.rpow_le_rpow (div_nonneg (hpal i).le hρ.le) hscale (by linarith)
    -- the constants
    have hK : 0 ≤ r ^ (-ε) := Real.rpow_nonneg hr.le _
    have hc : 0 < c := lt_of_lt_of_le hr hrc
    have hCY : 0 ≤ r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ) := by
      have := Real.rpow_nonneg hr.le (-ε); positivity
    have hwin := winConst_mono_pin (s := s) (ε := ε) (K := r ^ (-ε)) (c := c) (KY := KY)
      (CY := r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) (L := (S.image cls).card) hr hK hc
      (Nat.cast_nonneg _)
      (pinConst_anti (w := palScale r n i) hr (by linarith) (by linarith) hCY)
    have hwin0 : 0 ≤ winConst r s ε (r ^ (-ε)) c (palScale r n i)
        (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card :=
      winConst_nonneg hr hK hc (hpal i) (by linarith) hCY (Nat.cast_nonneg _)
    have hr4 : 0 ≤ r ^ (-(4 * d)) := Real.rpow_nonneg hr.le _
    have hsq0 : (0 : ℝ) ≤ (arcAvg (palScale r n i) S p₀ / arcAvg (palScale r n h) S p₀) ^ 2 :=
      sq_nonneg _
    calc (Sq.card : ℝ)
        ≤ winConst r s ε (r ^ (-ε)) c (palScale r n i)
            (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY (S.image cls).card *
          (arcAvg (palScale r n i) S p₀ / arcAvg (palScale r n h) S p₀) ^ 2 * J.card := hsq
      _ ≤ winConst r s ε (r ^ (-ε)) c r (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
            (S.image cls).card * ((palScale r n i / ρ) ^ (2 * s) * r ^ (-(4 * d))) * J.card := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul hwin hratio hsq0 (le_trans hwin0 hwin)
      _ ≤ winConst r s ε (r ^ (-ε)) c r (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
            (S.image cls).card * (((320 * B) ^ (2 * s) * ρ' ^ (2 * s)) * r ^ (-(4 * d))) *
              J.card := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (le_trans hwin0 hwin)
          exact mul_le_mul_of_nonneg_right hpow hr4
      _ = (winConst r s ε (r ^ (-ε)) c r (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
            (S.image cls).card * r ^ (-(4 * d)) * (320 * B) ^ (2 * s)) * ρ' ^ (2 * s) *
              J.card := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_right (le_max_right _ _)
          exact Real.rpow_nonneg hρ'pos.le _

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
