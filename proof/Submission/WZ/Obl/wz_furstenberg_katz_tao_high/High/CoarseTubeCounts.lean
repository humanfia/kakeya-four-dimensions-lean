-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CoarseTubeCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/CoarseTubeCounts.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeUpper

/-!
# Counting fine-resolution tubes inside coarser tubes

Tube families at two palette scales `δ ≤ w` (maps `tbA`, `tbI` on the lines `J₀`, geometry
`9δ/δ` and `9w/w`) need not nest. The counts below go through the labels instead:

* `near_tubes_le`: in a `StripSep w` family, at most `nearTubeConst` tubes are not
  `StripSep W`-separated from a given one (`W ≤ 67 w`; `strip_neighbor_count`).
* `delta_tubes_in_tube_le`: the `δ`-tubes `ℓ_a` (of labels of `S`) with `tbI ℓ_a = k`, each
  holding at least `L_min` labels, number at most `nearTubeConst · L_max / L_min`, where `L_max`
  bounds the labels of every `w`-tube: the fine lines of those `δ`-tubes have their own `w`-tubes
  among the `nearTubeConst` tubes near `k` (`tubes_close_of_lines_close`).
* `card_image_ge_of_fibers`: a set of labels with at most `L` labels per `δ`-tube meets at
  least `#labels / L` of them.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

attribute [local instance] Classical.propDecidable

/-- `StripSep` is monotone in the scale. -/
theorem stripSep_mono {a b : ℝ} (hab : b ≤ a) {x y : E2 × E2} (h : StripSep a x y) :
    StripSep b x y := by
  rcases h with ⟨h1, h2⟩ | h3
  · exact Or.inl ⟨le_trans hab h1, le_trans hab h2⟩
  · exact Or.inr (le_trans hab h3)

/-- The packing constant of `strip_neighbor_count` at the ratio `67`. -/
noncomputable def nearTubeConst : ℝ := 2 * (64 * 67 + 2) * (36 * 67 + 2)

theorem nearTubeConst_pos : 0 < nearTubeConst := by
  rw [nearTubeConst]; norm_num

/-- In a `StripSep w` family, at most `nearTubeConst` tubes are within `¬ StripSep W` of a given
one, for `W ≤ 67 w`. -/
theorem near_tubes_le {w W : ℝ} (hw : 0 < w) (hw2 : 67 * w ≤ 1 / 2) (hW : W ≤ 67 * w)
    {J₁ : Finset (E2 × E2)} (hJ₁ : ∀ j ∈ J₁, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep w x y) {k : E2 × E2} (hk : k ∈ J₁) :
    ((J₁.filter (fun j => ¬ StripSep W j k ∨ ¬ StripSep W k j)).card : ℝ) ≤ nearTubeConst := by
  classical
  have hsep' : (J₁ : Set (E2 × E2)).Pairwise (WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep w) := by
    intro x hx y hy hxy
    exact hsep x (by simpa using hx) y (by simpa using hy) hxy
  have hcount := strip_neighbor_count hw (by linarith : 0 < 67 * w) hw2 J₁ hJ₁ hsep' hk
  have hr64 : 64 * (67 * w) / w = 64 * 67 := by field_simp
  have hr36 : 36 * (67 * w) / w = 36 * 67 := by field_simp
  rw [hr64, hr36] at hcount
  have hsub : J₁.filter (fun j => ¬ StripSep W j k ∨ ¬ StripSep W k j) ⊆
      J₁.filter (fun j =>
        ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep (67 * w) j k ∨
        ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep (67 * w) k j) := by
    intro j hj
    obtain ⟨hjJ, hjn⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨hjJ, ?_⟩
    rcases hjn with h | h
    · left; intro h'; exact h (stripSep_mono hW h')
    · right; intro h'; exact h (stripSep_mono hW h')
  calc ((J₁.filter (fun j => ¬ StripSep W j k ∨ ¬ StripSep W k j)).card : ℝ)
      ≤ (J₁.filter (fun j =>
          ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep (67 * w) j k ∨
          ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep (67 * w) k j)).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ nearTubeConst := by rw [nearTubeConst]; linarith

/-- **`δ`-tubes inside a `w`-tube, counted through labels.** -/
theorem delta_tubes_in_tube_le {δ w Lmin Lmax : ℝ} (hδ : 0 < δ) (hδw : δ ≤ w)
    (hw2 : 67 * w ≤ 1 / 2) (hLmax : 0 ≤ Lmax)
    {S J₀ J₁ : Finset (E2 × E2)} {cls tbA tbI : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ S, cls q ∈ J₀) (hJ₀4 : ∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4)
    (htbA : ∀ ℓ ∈ J₀, tbA ℓ ∈ J₀)
    (htbAgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tbA ℓ).1) (tbA ℓ).2| < 9 * δ ∧
      (dist ℓ.2 (tbA ℓ).2 < δ ∨ dist ℓ.2 (-(tbA ℓ).2) < δ))
    (htbI : ∀ ℓ ∈ J₀, tbI ℓ ∈ J₁)
    (htbIgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tbI ℓ).1) (tbI ℓ).2| < 9 * w ∧
      (dist ℓ.2 (tbI ℓ).2 < w ∨ dist ℓ.2 (-(tbI ℓ).2) < w))
    (hJ₁ : ∀ j ∈ J₁, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep w x y)
    (X : Finset (E2 × E2))
    (hLmin : ∀ ℓa ∈ X, Lmin ≤ ((S.filter (fun q => tbA (cls q) = ℓa)).card : ℝ))
    (hLmaxk : ∀ k' ∈ J₁, ((S.filter (fun q => tbI (cls q) = k')).card : ℝ) ≤ Lmax)
    {k : E2 × E2} (hk : k ∈ J₁) :
    ((X.filter (fun ℓa => tbI ℓa = k)).card : ℝ) * Lmin ≤ nearTubeConst * Lmax := by
  classical
  have hw : 0 < w := lt_of_lt_of_le hδ hδw
  set Y := X.filter (fun ℓa => tbI ℓa = k) with hY
  set U := S.filter (fun q => tbA (cls q) ∈ Y) with hU
  set Near := J₁.filter (fun j => ¬ StripSep (25 * δ + 42 * w) j k ∨
    ¬ StripSep (25 * δ + 42 * w) k j) with hNear
  -- lower: the labels of the tubes of `Y`
  have hUsum : (U.card : ℝ) = ∑ ℓa ∈ Y, ((S.filter (fun q => tbA (cls q) = ℓa)).card : ℝ) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := fun q => tbA (cls q)) (s := U) (t := Y)
      (fun q hq => (Finset.mem_filter.mp hq).2)
    have h2 : ∀ ℓa ∈ Y, U.filter (fun q => tbA (cls q) = ℓa) =
        S.filter (fun q => tbA (cls q) = ℓa) := by
      intro ℓa hℓa
      ext q
      simp only [hU, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hqS, _⟩, hq⟩; exact ⟨hqS, hq⟩
      · rintro ⟨hqS, hq⟩; exact ⟨⟨hqS, hq ▸ hℓa⟩, hq⟩
    rw [h1]
    push_cast
    exact Finset.sum_congr rfl (fun ℓa hℓa => by rw [h2 ℓa hℓa])
  have hlow : (Y.card : ℝ) * Lmin ≤ U.card := by
    rw [hUsum]
    calc (Y.card : ℝ) * Lmin = ∑ _ℓa ∈ Y, Lmin := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ℓa ∈ Y, ((S.filter (fun q => tbA (cls q) = ℓa)).card : ℝ) :=
          Finset.sum_le_sum (fun ℓa hℓa => hLmin ℓa (Finset.mem_filter.mp hℓa).1)
  -- upper: the labels of `U` lie in tubes near `k`
  have hsubU : U ⊆ Near.biUnion (fun k' => S.filter (fun q => tbI (cls q) = k')) := by
    intro q hq
    obtain ⟨hqS, hqY⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqX, hqk⟩ := Finset.mem_filter.mp hqY
    have hℓ := hcls q hqS
    have hℓa : tbA (cls q) ∈ J₀ := htbA _ hℓ
    have hnot := tubes_close_of_lines_close (hJ₀4 _ hℓ) (hJ₀4 _ hℓa)
      (hJ₁ _ (htbI _ hℓ)).1 (hJ₁ _ (htbI _ hℓa)).1 (htbAgeo _ hℓ) (htbIgeo _ hℓ)
      (htbIgeo _ hℓa)
    rw [hqk] at hnot
    refine Finset.mem_biUnion.mpr ⟨tbI (cls q), ?_, Finset.mem_filter.mpr ⟨hqS, rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨htbI _ hℓ, Or.inl hnot⟩
  have hNear : (Near.card : ℝ) ≤ nearTubeConst :=
    near_tubes_le (W := 25 * δ + 42 * w) hw hw2 (by linarith) hJ₁ hJ₁sep hk
  have hup : (U.card : ℝ) ≤ nearTubeConst * Lmax := by
    calc (U.card : ℝ) ≤ (Near.biUnion (fun k' => S.filter (fun q => tbI (cls q) = k'))).card := by
          exact_mod_cast Finset.card_le_card hsubU
      _ ≤ ∑ k' ∈ Near, ((S.filter (fun q => tbI (cls q) = k')).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _k' ∈ Near, Lmax := Finset.sum_le_sum (fun k' hk' =>
          hLmaxk k' (Finset.mem_filter.mp hk').1)
      _ = Near.card * Lmax := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ nearTubeConst * Lmax := mul_le_mul_of_nonneg_right hNear hLmax
  linarith

/-- A set of labels with at most `L` labels per `δ`-tube meets at least `#labels / L` tubes. -/
theorem card_image_ge_of_fibers {L : ℝ} {A S : Finset (E2 × E2)} (hAS : A ⊆ S)
    {f : E2 × E2 → E2 × E2} (hL : ∀ q ∈ A, ((S.filter (fun q' => f q' = f q)).card : ℝ) ≤ L) :
    (A.card : ℝ) ≤ (A.image f).card * L := by
  classical
  have h1 := Finset.card_eq_sum_card_fiberwise (f := f) (s := A) (t := A.image f)
    (fun q hq => Finset.mem_image_of_mem f hq)
  have h2 : ∀ b ∈ A.image f, ((A.filter (fun q => f q = b)).card : ℝ) ≤ L := by
    intro b hb
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    have hsub : A.filter (fun q' => f q' = f q) ⊆ S.filter (fun q' => f q' = f q) :=
      Finset.filter_subset_filter _ hAS
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hL q hq)
  calc (A.card : ℝ) = ∑ b ∈ A.image f, ((A.filter (fun q => f q = b)).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ _b ∈ A.image f, L := Finset.sum_le_sum h2
    _ = (A.image f).card * L := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Closeness counts for the `δ`-lines of a tube.** `J = J(T)`: the `δ`-tubes (map `tbA`) of
the labels whose `ρ`-tube (map `tbH`) is `T`. For `W ≤ w` (the scale of a third family `tbI`),
the members of `J` within `(9 W, W)` of a member `j₀` satisfy
`#close · (L_min,a · L_T) ≤ nearTubeConst² · L_max,w · L_max,a · #J`,
with `L_min,a ≤` labels of every `δ`-tube of `J`, `L_max,a`, `L_max,w` upper bounds for the
labels of `δ`- and `w`-tubes, and `L_T` the labels of `T`. -/
theorem coarse_close_count {δ w W LminA LmaxA LmaxI : ℝ} (hδ : 0 < δ) (hδw : δ ≤ w)
    (hw2 : 67 * w ≤ 1 / 2) (hW0 : 0 ≤ W) (hWw : W ≤ w) (hLmaxI : 0 ≤ LmaxI)
    (hLminA : 0 ≤ LminA)
    {S J₀ J₁ : Finset (E2 × E2)} {cls tbA tbI tbH : E2 × E2 → E2 × E2} {T : E2 × E2}
    (hcls : ∀ q ∈ S, cls q ∈ J₀) (hJ₀4 : ∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4)
    (htbA : ∀ ℓ ∈ J₀, tbA ℓ ∈ J₀)
    (htbAgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tbA ℓ).1) (tbA ℓ).2| < 9 * δ ∧
      (dist ℓ.2 (tbA ℓ).2 < δ ∨ dist ℓ.2 (-(tbA ℓ).2) < δ))
    (htbI : ∀ ℓ ∈ J₀, tbI ℓ ∈ J₁)
    (htbIgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tbI ℓ).1) (tbI ℓ).2| < 9 * w ∧
      (dist ℓ.2 (tbI ℓ).2 < w ∨ dist ℓ.2 (-(tbI ℓ).2) < w))
    (hJ₁ : ∀ j ∈ J₁, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep w x y)
    (hLminA' : ∀ q ∈ S, LminA ≤ ((S.filter (fun q' => tbA (cls q') = tbA (cls q))).card : ℝ))
    (hLmaxA' : ∀ q ∈ S, ((S.filter (fun q' => tbA (cls q') = tbA (cls q))).card : ℝ) ≤ LmaxA)
    (hLmaxI' : ∀ k' ∈ J₁, ((S.filter (fun q => tbI (cls q) = k')).card : ℝ) ≤ LmaxI)
    {j₀ : E2 × E2}
    (hj₀ : j₀ ∈ (S.filter (fun q => tbH (cls q) = T)).image (fun q => tbA (cls q))) :
    ((((S.filter (fun q => tbH (cls q) = T)).image (fun q => tbA (cls q))).filter
        (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * W ∧
          (dist j.2 j₀.2 < W ∨ dist j.2 (-j₀.2) < W))).card : ℝ) *
        (LminA * ((S.filter (fun q => tbH (cls q) = T)).card : ℝ)) ≤
      nearTubeConst ^ 2 * LmaxI * LmaxA *
        (((S.filter (fun q => tbH (cls q) = T)).image (fun q => tbA (cls q))).card : ℝ) := by
  classical
  have hw : 0 < w := lt_of_lt_of_le hδ hδw
  set A := S.filter (fun q => tbH (cls q) = T) with hA
  set J := A.image (fun q => tbA (cls q)) with hJ
  have hJJ₀ : ∀ j ∈ J, j ∈ J₀ := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact htbA _ (hcls q (Finset.mem_filter.mp hq).1)
  -- every `δ`-tube of `J` holds at least `L_min,a` labels
  have hJmin : ∀ ℓa ∈ J, LminA ≤ ((S.filter (fun q => tbA (cls q) = ℓa)).card : ℝ) := by
    intro ℓa hℓa
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓa
    exact hLminA' q (Finset.mem_filter.mp hq).1
  -- the `δ`-tubes of `J` inside one `w`-tube
  have hNi : ∀ k ∈ J₁, ((J.filter (fun ℓa => tbI ℓa = k)).card : ℝ) * LminA ≤
      nearTubeConst * LmaxI := fun k hk =>
    delta_tubes_in_tube_le hδ hδw hw2 hLmaxI hcls hJ₀4 htbA htbAgeo htbI htbIgeo hJ₁ hJ₁sep
      J hJmin hLmaxI' hk
  -- the closeness count, through the `w`-tubes (`lines_near_le` with `cls = id`)
  by_cases hLpos : 0 < LminA
  · set Nmax : ℝ := nearTubeConst * LmaxI / LminA with hNmax
    have hN : ∀ q ∈ J, (((J.filter (fun a => tbI (id a) = tbI (id q))).image id).card : ℝ) ≤
        Nmax := by
      intro q hq
      rw [Finset.image_id, hNmax, le_div_iff₀ hLpos]
      exact hNi (tbI q) (htbI q (hJJ₀ q hq))
    have hW' : 25 * W + 42 * w ≤ 1 / 2 := by linarith
    have hnear := lines_near_le (S := J) (cls := id) (tb := tbI) (W := W) (w := w) (Nmax := Nmax)
      hw hW0 hW'
      (fun q hq => hJ₁ _ (htbI q (hJJ₀ q hq))) (fun q hq => hJ₀4 q (hJJ₀ q hq))
      (fun x hx y hy hxy => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hy
        exact hJ₁sep _ (htbI q (hJJ₀ q hq)) _ (htbI q' (hJJ₀ q' hq')) hxy)
      (fun q hq => htbIgeo q (hJJ₀ q hq)) hN hj₀
    rw [Finset.image_id] at hnear
    have hconst : 2 * (64 * (25 * W + 42 * w) / w + 2) * (36 * (25 * W + 42 * w) / w + 2) ≤
        nearTubeConst := by
      have h1 : 64 * (25 * W + 42 * w) / w ≤ 64 * 67 := by
        rw [div_le_iff₀ hw]; nlinarith
      have h2 : 36 * (25 * W + 42 * w) / w ≤ 36 * 67 := by
        rw [div_le_iff₀ hw]; nlinarith
      have h1' : 0 ≤ 64 * (25 * W + 42 * w) / w := by positivity
      have h2' : 0 ≤ 36 * (25 * W + 42 * w) / w := by positivity
      rw [nearTubeConst]
      nlinarith
    have hNmax0 : 0 ≤ Nmax := by
      rw [hNmax]; exact div_nonneg (mul_nonneg nearTubeConst_pos.le hLmaxI) hLpos.le
    have hclose : ((J.filter (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * W ∧
        (dist j.2 j₀.2 < W ∨ dist j.2 (-j₀.2) < W))).card : ℝ) ≤ nearTubeConst * Nmax := by
      calc _ ≤ 2 * (64 * (25 * W + 42 * w) / w + 2) * (36 * (25 * W + 42 * w) / w + 2) * Nmax := by
            simpa using hnear
        _ ≤ nearTubeConst * Nmax := mul_le_mul_of_nonneg_right hconst hNmax0
    -- `#J ≥ L_T / L_max,a`
    have hJcard : (A.card : ℝ) ≤ J.card * LmaxA := by
      apply card_image_ge_of_fibers (Finset.filter_subset _ _)
      intro q hq
      exact hLmaxA' q (Finset.mem_filter.mp hq).1
    have hc0 : (0 : ℝ) ≤ (J.filter (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * W ∧
        (dist j.2 j₀.2 < W ∨ dist j.2 (-j₀.2) < W))).card := by positivity
    calc ((J.filter (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * W ∧
          (dist j.2 j₀.2 < W ∨ dist j.2 (-j₀.2) < W))).card : ℝ) * (LminA * A.card)
        ≤ (nearTubeConst * Nmax) * (LminA * (J.card * LmaxA)) := by
          apply mul_le_mul hclose _ (mul_nonneg hLminA (Nat.cast_nonneg _))
            (mul_nonneg nearTubeConst_pos.le hNmax0)
          exact mul_le_mul_of_nonneg_left hJcard hLminA
      _ = nearTubeConst ^ 2 * LmaxI * LmaxA * J.card := by
          rw [hNmax]; field_simp
  · have h0 : LminA = 0 := le_antisymm (not_lt.mp hLpos) hLminA
    rw [h0, zero_mul, mul_zero]
    have hLmaxA0 : 0 ≤ LmaxA := by
      obtain ⟨q, hq, -⟩ := Finset.mem_image.mp hj₀
      exact le_trans (Nat.cast_nonneg _) (hLmaxA' q (Finset.mem_filter.mp hq).1)
    have := nearTubeConst_pos
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg this.le 2) hLmaxI) hLmaxA0)
      (Nat.cast_nonneg _)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
