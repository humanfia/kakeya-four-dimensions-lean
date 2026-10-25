-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.GoodPoints.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Defs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CircleGeometry

/-!
# Far same-class pairs at a point

`HalfData.good_degree`: given a classification `cls` of the labels of `D` into strips of
half-width `9 r` (with normals `r`-close to the label directions up to sign), the number of
pairs of same-class labels `((p, e), (p', e'))` with `dist p p' ≥ d₀` and first point `p` is
at most `12 · 52 ^ (1/2) · r ^ (-2η) · d₀ ^ (-1/2)` times the number of points `p' ∈ P` with
`dist p' p ≥ d₀` lying in the `26 r`-strip through `p` with normal some `e ∈ bushOf D p`.

Proof: for a counted pair, `|⟪p' - p, e⟫| < 26 r` and `e'` is `2 r`-close to `±e`
(`good_close`). Group the pairs by `p'` and then by `e`: for fixed `p'` there are at most
`2 r ^ (-η) (52 / d₀) ^ (1/2)` such `e` (`good_strip_count`, via
`SP.unit_circle_strip_two_balls` and the Katz–Tao bound of the bush of `p`), and for fixed
`(p', e)` at most `2 · 2 ^ (1/2) r ^ (-η)` such `e'` (`good_pair_count`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- Number of same-class far label pairs whose first label sits at `p`. -/
noncomputable def farCount (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (d₀ : ℝ)
    (p : E2) : ℕ :=
  ((D ×ˢ D).filter (fun qq => cls qq.1 = cls qq.2 ∧ d₀ ≤ dist qq.1.1 qq.2.1 ∧
    qq.1.1 = p)).card

/-- Two labels of the same class: the second base point lies in the `26 r`-strip through the
first with normal the first direction, and the two directions are `2 r`-close up to sign. -/
theorem good_close {r : ℝ} {D : Finset (E2 × E2)} (cls : E2 × E2 → E2 × E2)
    (hcls : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    {q q' : E2 × E2} (hq : q ∈ D) (hq' : q' ∈ D) (hc : cls q = cls q')
    (h8 : ‖q'.1 - q.1‖ ≤ 8) :
    |inner ℝ (q'.1 - q.1) q.2| < 26 * r ∧
      (dist q'.2 q.2 < 2 * r ∨ dist q'.2 (-q.2) < 2 * r) := by
  obtain ⟨h1, h2⟩ := hcls q hq
  obtain ⟨h1', h2'⟩ := hcls q' hq'
  rw [← hc] at h1' h2'
  set j := cls q with hj
  have hin : |inner ℝ (q'.1 - q.1) j.2| < 18 * r := by
    have e1 : inner ℝ (q'.1 - q.1) j.2 =
        inner ℝ (q'.1 - j.1) j.2 - inner ℝ (q.1 - j.1) j.2 := by
      rw [← inner_sub_left]; congr 1; abel
    rw [e1]
    calc |inner ℝ (q'.1 - j.1) j.2 - inner ℝ (q.1 - j.1) j.2|
        ≤ |inner ℝ (q'.1 - j.1) j.2| + |inner ℝ (q.1 - j.1) j.2| := abs_sub _ _
      _ < 9 * r + 9 * r := add_lt_add h1' h1
      _ = 18 * r := by ring
  constructor
  · rcases h2 with h2 | h2
    · have := inner_lt_of_close (v := q'.1 - q.1) (e := j.2) (e' := q.2) (w := 18 * r)
        (ρ := r) h8 hin (by rw [← dist_eq_norm, dist_comm]; exact h2.le)
      linarith
    · have hin' : |inner ℝ (q'.1 - q.1) (-j.2)| < 18 * r := by
        rw [inner_neg_right, abs_neg]; exact hin
      have := inner_lt_of_close (v := q'.1 - q.1) (e := -j.2) (e' := q.2) (w := 18 * r)
        (ρ := r) h8 hin' (by rw [← dist_eq_norm, dist_comm]; exact h2.le)
      linarith
  · rcases h2 with h2 | h2 <;> rcases h2' with h2' | h2'
    · left
      calc dist q'.2 q.2 ≤ dist q'.2 j.2 + dist j.2 q.2 := dist_triangle _ _ _
        _ < r + r := by rw [dist_comm j.2]; exact add_lt_add h2' h2
        _ = 2 * r := by ring
    · right
      calc dist q'.2 (-q.2) ≤ dist q'.2 (-j.2) + dist (-j.2) (-q.2) := dist_triangle _ _ _
        _ < r + r := by rw [dist_neg_neg, dist_comm j.2]; exact add_lt_add h2' h2
        _ = 2 * r := by ring
    · right
      have e2 : dist j.2 (-q.2) = dist q.2 (-j.2) := by
        rw [dist_eq_norm, dist_eq_norm, sub_neg_eq_add, sub_neg_eq_add, add_comm]
      calc dist q'.2 (-q.2) ≤ dist q'.2 j.2 + dist j.2 (-q.2) := dist_triangle _ _ _
        _ < r + r := by rw [e2]; exact add_lt_add h2' h2
        _ = 2 * r := by ring
    · left
      calc dist q'.2 q.2 ≤ dist q'.2 (-j.2) + dist (-j.2) q.2 := dist_triangle _ _ _
        _ < r + r := by rw [dist_comm (-j.2)]; exact add_lt_add h2' h2
        _ = 2 * r := by ring

/-- Directions of the bush of `p'` that are `2 r`-close to `±e` are few. -/
theorem good_pair_count {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p' : E2} (hp' : p' ∈ P) {e : E2} (he : ‖e‖ = 1) :
    (((bushOf D p').filter (fun e' => dist e' e < 2 * r ∨ dist e' (-e) < 2 * r)).card : ℝ) ≤
      2 * 2 ^ (1 / 2 : ℝ) * r ^ (-η) := by
  have hr0 := h.r_pos
  have hsub : (bushOf D p').filter (fun e' => dist e' e < 2 * r ∨ dist e' (-e) < 2 * r) ⊆
      (bushOf D p').filter (fun e' => dist e' e ≤ 2 * r) ∪
        (bushOf D p').filter (fun e' => dist e' (-e) ≤ 2 * r) := by
    intro e' he'
    rw [Finset.mem_filter] at he'
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases he'.2 with h1 | h1
    · exact Or.inl ⟨he'.1, h1.le⟩
    · exact Or.inr ⟨he'.1, h1.le⟩
  have h1 := h.D_kt p' hp' e he (2 * r) (by linarith)
  have h2 := h.D_kt p' hp' (-e) (by rw [norm_neg, he]) (2 * r) (by linarith)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc' :
      (((bushOf D p').filter (fun e' => dist e' e < 2 * r ∨ dist e' (-e) < 2 * r)).card : ℝ) ≤
        (((bushOf D p').filter (fun e' => dist e' e ≤ 2 * r)).card : ℝ) +
          (((bushOf D p').filter (fun e' => dist e' (-e) ≤ 2 * r)).card : ℝ) := by
    exact_mod_cast hc
  have h2r : 2 * r / r = 2 := by field_simp
  rw [h2r] at h1 h2
  linarith

/-- Directions of the bush of `p` in the `26 r`-strip normal to `v`, `d₀ ≤ ‖v‖ ≤ 8`,
are few. -/
theorem good_strip_count {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p : E2} (hp : p ∈ P) {v : E2} {d₀ : ℝ} (hd₀ : 0 < d₀)
    (hv : d₀ ≤ ‖v‖) (hv8 : ‖v‖ ≤ 8) :
    (((bushOf D p).filter (fun e => |inner ℝ v e| < 26 * r)).card : ℝ) ≤
      2 * r ^ (-η) * (52 ^ (1 / 2 : ℝ) * d₀ ^ (-(1 / 2) : ℝ)) := by
  have hr0 := h.r_pos
  have hvpos : 0 < ‖v‖ := lt_of_lt_of_le hd₀ hv
  have hv0 : v ≠ 0 := norm_pos_iff.mp hvpos
  obtain ⟨e₀, he₀, hball⟩ := SP.unit_circle_strip_two_balls hv0 (s := 26 * r)
  set ρ : ℝ := 2 * (26 * r) / ‖v‖ with hρ
  have hρr : r ≤ ρ := by
    rw [hρ, le_div_iff₀ hvpos]
    nlinarith
  have hsub : (bushOf D p).filter (fun e => |inner ℝ v e| < 26 * r) ⊆
      (bushOf D p).filter (fun e => dist e e₀ ≤ ρ) ∪
        (bushOf D p).filter (fun e => dist e (-e₀) ≤ ρ) := by
    intro e he
    rw [Finset.mem_filter] at he
    have he1 : ‖e‖ = 1 := (h.D_mem _ (mem_bushOf.mp he.1)).2
    have hle : |inner ℝ e v| ≤ 26 * r := by rw [real_inner_comm]; exact he.2.le
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hball e he1 hle with h1 | h1
    · exact Or.inl ⟨he.1, h1⟩
    · exact Or.inr ⟨he.1, h1⟩
  have h1 := h.D_kt p hp e₀ he₀ ρ hρr
  have h2 := h.D_kt p hp (-e₀) (by rw [norm_neg, he₀]) ρ hρr
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc' : (((bushOf D p).filter (fun e => |inner ℝ v e| < 26 * r)).card : ℝ) ≤
      (((bushOf D p).filter (fun e => dist e e₀ ≤ ρ)).card : ℝ) +
        (((bushOf D p).filter (fun e => dist e (-e₀) ≤ ρ)).card : ℝ) := by
    exact_mod_cast hc
  have hρr' : ρ / r = 52 / ‖v‖ := by rw [hρ]; field_simp; ring
  have hpow : (ρ / r) ^ (1 / 2 : ℝ) ≤ 52 ^ (1 / 2 : ℝ) * d₀ ^ (-(1 / 2) : ℝ) := by
    rw [hρr']
    calc (52 / ‖v‖) ^ (1 / 2 : ℝ) ≤ (52 / d₀) ^ (1 / 2 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          exact div_le_div_of_nonneg_left (by norm_num) hd₀ hv
      _ = 52 ^ (1 / 2 : ℝ) * d₀ ^ (-(1 / 2) : ℝ) := by
          rw [Real.div_rpow (by norm_num) hd₀.le, Real.rpow_neg hd₀.le, div_eq_mul_inv]
  have hrη : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr0.le _
  have := mul_le_mul_of_nonneg_left hpow hrη
  linarith

theorem HalfData.good_degree {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hr : r ≤ 1 / 100) (hη : 0 < η)
    (cls : E2 × E2 → E2 × E2)
    (hcls : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (hcls4 : ∀ q ∈ D, ‖(cls q).1‖ ≤ 4 ∧ ‖(cls q).2‖ = 1)
    {d₀ : ℝ} (hd₀ : 52 * r ≤ d₀) (p : E2) (hp : p ∈ P) :
    (farCount D cls d₀ p : ℝ) ≤
      12 * 52 ^ (1 / 2 : ℝ) * r ^ (-2 * η) * d₀ ^ (-(1 / 2) : ℝ) *
        ((P.filter (fun q => d₀ ≤ dist q p ∧
          ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r)).card : ℝ) := by
  -- (`hη` and `hcls4` are not needed for this bound.)
  have hr0 : 0 < r := h.r_pos
  have hd0 : 0 < d₀ := by linarith
  set K : ℝ := 12 * 52 ^ (1 / 2 : ℝ) * r ^ (-2 * η) * d₀ ^ (-(1 / 2) : ℝ) with hK
  set T := P.filter (fun q => d₀ ≤ dist q p ∧
    ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 26 * r) with hT
  unfold farCount
  set S := (D ×ˢ D).filter (fun qq => cls qq.1 = cls qq.2 ∧ d₀ ≤ dist qq.1.1 qq.2.1 ∧
    qq.1.1 = p) with hS
  have hmemS : ∀ qq ∈ S, qq.1 ∈ D ∧ qq.2 ∈ D ∧ cls qq.1 = cls qq.2 ∧
      d₀ ≤ dist qq.1.1 qq.2.1 ∧ qq.1.1 = p := by
    intro qq hqq
    rw [hS, Finset.mem_filter, Finset.mem_product] at hqq
    exact ⟨hqq.1.1, hqq.1.2, hqq.2⟩
  have hgeom : ∀ qq ∈ S, |inner ℝ (qq.2.1 - p) qq.1.2| < 26 * r ∧
      (dist qq.2.2 qq.1.2 < 2 * r ∨ dist qq.2.2 (-qq.1.2) < 2 * r) := by
    intro qq hqq
    obtain ⟨h1, h2, hc, -, hp1⟩ := hmemS qq hqq
    have h8 : ‖qq.2.1 - qq.1.1‖ ≤ 8 :=
      norm_le_eight_of_norm_le_four (h.P_norm _ (h.D_mem _ h2).1) (h.P_norm _ (h.D_mem _ h1).1)
    have := good_close cls hcls h1 h2 hc h8
    rw [hp1] at this
    exact this
  have hmaps : Set.MapsTo (fun qq : (E2 × E2) × (E2 × E2) => qq.2.1) S T := by
    intro qq hqq
    obtain ⟨h1, h2, -, hd, hp1⟩ := hmemS qq hqq
    rw [Finset.mem_coe, hT, Finset.mem_filter]
    refine ⟨(h.D_mem _ h2).1, ?_, qq.1.2, ?_, (hgeom qq hqq).1⟩
    · rw [dist_comm, ← hp1]; exact hd
    · rw [mem_bushOf, ← hp1]; exact h1
  have hfib : ∀ p' ∈ T, ((S.filter (fun qq => qq.2.1 = p')).card : ℝ) ≤ K := by
    intro p' hp'T
    rw [hT, Finset.mem_filter] at hp'T
    obtain ⟨hp'P, hdp', -⟩ := hp'T
    set A := (bushOf D p).filter (fun e => |inner ℝ (p' - p) e| < 26 * r) with hA
    set Sp := S.filter (fun qq => qq.2.1 = p') with hSp
    have hmapsA : Set.MapsTo (fun qq : (E2 × E2) × (E2 × E2) => qq.1.2) Sp A := by
      intro qq hqq
      rw [Finset.mem_coe, hSp, Finset.mem_filter] at hqq
      obtain ⟨hqqS, hq2⟩ := hqq
      obtain ⟨h1, -, -, -, hp1⟩ := hmemS qq hqqS
      rw [Finset.mem_coe, hA, Finset.mem_filter, mem_bushOf]
      refine ⟨?_, ?_⟩
      · rw [← hp1]; exact h1
      · rw [← hq2]; exact (hgeom qq hqqS).1
    have hfibA : ∀ e ∈ A, ((Sp.filter (fun qq => qq.1.2 = e)).card : ℝ) ≤
        2 * 2 ^ (1 / 2 : ℝ) * r ^ (-η) := by
      intro e heA
      have he1 : ‖e‖ = 1 := by
        rw [hA, Finset.mem_filter, mem_bushOf] at heA
        exact (h.D_mem _ heA.1).2
      refine le_trans ?_ (good_pair_count h hp'P he1)
      have hinj := Finset.card_le_card_of_injOn (s := Sp.filter (fun qq => qq.1.2 = e))
        (t := (bushOf D p').filter (fun e' => dist e' e < 2 * r ∨ dist e' (-e) < 2 * r))
        (fun qq => qq.2.2) ?_ ?_
      · exact_mod_cast hinj
      · intro qq hqq
        rw [Finset.mem_coe, Finset.mem_filter, hSp, Finset.mem_filter] at hqq
        obtain ⟨⟨hqqS, hq2⟩, hq12⟩ := hqq
        obtain ⟨-, h2, -, -, -⟩ := hmemS qq hqqS
        rw [Finset.mem_coe, Finset.mem_filter, mem_bushOf]
        refine ⟨?_, ?_⟩
        · rw [← hq2]; exact h2
        · rw [← hq12]; exact (hgeom qq hqqS).2
      · intro qq hqq qq' hqq' heq
        rw [Finset.mem_coe, Finset.mem_filter, hSp, Finset.mem_filter] at hqq hqq'
        obtain ⟨⟨hqqS, hq2⟩, hq12⟩ := hqq
        obtain ⟨⟨hqqS', hq2'⟩, hq12'⟩ := hqq'
        obtain ⟨-, -, -, -, hp1⟩ := hmemS qq hqqS
        obtain ⟨-, -, -, -, hp1'⟩ := hmemS qq' hqqS'
        exact Prod.ext (Prod.ext (hp1.trans hp1'.symm) (hq12.trans hq12'.symm))
          (Prod.ext (hq2.trans hq2'.symm) heq)
    have hv8 : ‖p' - p‖ ≤ 8 := norm_le_eight_of_norm_le_four (h.P_norm p' hp'P) (h.P_norm p hp)
    have hvd : d₀ ≤ ‖p' - p‖ := by rw [← dist_eq_norm]; exact hdp'
    have hcardA := good_strip_count h hp hd0 hvd hv8
    have hs2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hs0 : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
    have ha0 : 0 ≤ r ^ (-η) := Real.rpow_nonneg hr0.le _
    have hb0 : 0 ≤ (52 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
    have hc0 : 0 ≤ d₀ ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hd0.le _
    have hr2 : r ^ (-2 * η) = r ^ (-η) * r ^ (-η) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    rw [Finset.card_eq_sum_card_fiberwise hmapsA]
    push_cast
    calc ∑ e ∈ A, ((Sp.filter (fun qq => qq.1.2 = e)).card : ℝ)
        ≤ ∑ e ∈ A, (2 * 2 ^ (1 / 2 : ℝ) * r ^ (-η)) := Finset.sum_le_sum hfibA
      _ = (A.card : ℝ) * (2 * 2 ^ (1 / 2 : ℝ) * r ^ (-η)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * r ^ (-η) * (52 ^ (1 / 2 : ℝ) * d₀ ^ (-(1 / 2) : ℝ))) *
            (2 * 2 ^ (1 / 2 : ℝ) * r ^ (-η)) :=
          mul_le_mul_of_nonneg_right hcardA (by positivity)
      _ = (4 * 2 ^ (1 / 2 : ℝ)) *
            (52 ^ (1 / 2 : ℝ) * (r ^ (-η) * r ^ (-η)) * d₀ ^ (-(1 / 2) : ℝ)) := by ring
      _ ≤ 12 * (52 ^ (1 / 2 : ℝ) * (r ^ (-η) * r ^ (-η)) * d₀ ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = K := by rw [hK, hr2]; ring
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  calc ∑ p' ∈ T, ((S.filter (fun qq => qq.2.1 = p')).card : ℝ)
      ≤ ∑ p' ∈ T, K := Finset.sum_le_sum hfib
    _ = K * (T.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
