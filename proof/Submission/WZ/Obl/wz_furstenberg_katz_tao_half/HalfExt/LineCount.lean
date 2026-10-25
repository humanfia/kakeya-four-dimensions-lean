-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.LineCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Defs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CircleGeometry

/-!
# Few points of `HalfData` near a line

`HalfData.line_count`: the points of a `HalfData` configuration in a strip of width `128 r`
are at most `10 ^ 7 * r ^ (-1/2 - ε₀ - 7 η)`.  Proof: through a maximal `λ`-separated subset
of these points, the bush normals that are far from the direction of the strip, made
`r`-separated up to sign, give a `StripSep`-separated family of labels; `few_lines` bounds its
size.

`HalfData.near_line_degree`: the points `q` at distance `≥ d₀` from a point `p` of the
configuration, near a line through `p` with normal `n`, and on a strip of the bush of `p`,
are few: the normals of these strips are close to `± n`, and each strip holds few points.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-! ### Real powers -/

lemma lc_rpow_half_eq {y z : ℝ} (hz : 0 ≤ z) (h : z ^ 2 = y) : y ^ (1 / 2 : ℝ) = z := by
  rw [← h, ← Real.rpow_natCast, ← Real.rpow_mul hz]; norm_num

lemma lc_sq_rpow_half {y : ℝ} (hy : 0 ≤ y) : (y ^ (1 / 2 : ℝ)) ^ 2 = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

lemma lc_rho_ge {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 100) (hη1 : η ≤ 1 / 100) :
    r ≤ r ^ (4 * η) / 16 := by
  have h1 : r ^ ((1 : ℝ) / 3) ≤ r ^ (4 * η) :=
    Real.rpow_le_rpow_of_exponent_ge hr (by linarith) (by linarith)
  have hy0 : 0 ≤ r ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hr.le _
  have hy3 : (r ^ ((1 : ℝ) / 3)) ^ 3 = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  generalize r ^ ((1 : ℝ) / 3) = y at h1 hy0 hy3
  have hy4 : y ≤ 1 / 4 := by
    by_contra hc
    have hc' : 1 / 4 < y := not_le.mp hc
    have : (1 / 4 : ℝ) ^ 3 < y ^ 3 := pow_lt_pow_left₀ hc' (by norm_num) (by norm_num)
    norm_num at this
    linarith
  have hy2 : y ^ 2 ≤ 1 / 16 := by nlinarith
  have h16 : 16 * r ≤ y := by
    rw [← hy3]; nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy2)]
  linarith

lemma lc_far_bound {r η ρ₀ : ℝ} (hr : 0 < r) (hρ₀ : ρ₀ = r ^ (4 * η) / 16) :
    r ^ (-η) * (ρ₀ / r) ^ (1 / 2 : ℝ) = r ^ (η - 1 / 2) / 4 := by
  have hz : 0 ≤ r ^ (2 * η - 1 / 2) / 4 := by positivity
  have hsq : (r ^ (2 * η - 1 / 2) / 4) ^ 2 = ρ₀ / r := by
    have e1 : (r ^ (2 * η - 1 / 2)) ^ 2 = r ^ (4 * η - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
    have e2 : r ^ (4 * η - 1) = r ^ (4 * η) / r := by
      rw [Real.rpow_sub hr, Real.rpow_one]
    rw [div_pow, e1, e2, hρ₀]; ring
  rw [lc_rpow_half_eq hz hsq]
  have e3 : r ^ (-η) * r ^ (2 * η - 1 / 2) = r ^ (η - 1 / 2) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  calc r ^ (-η) * (r ^ (2 * η - 1 / 2) / 4) = (r ^ (-η) * r ^ (2 * η - 1 / 2)) / 4 := by ring
    _ = r ^ (η - 1 / 2) / 4 := by rw [e3]

lemma lc_final_arith {N X A R C S : ℝ} (hX : 0 ≤ X) (hA : 0 < A)
    (h1 : S ≤ N * X) (h2 : N * A < R) (h3 : X * R ≤ C * A) : S ≤ C := by
  have k1 : N * A * X ≤ R * X := mul_le_mul_of_nonneg_right h2.le hX
  have k2 : N * X * A ≤ C * A := by linarith
  have k3 : N * X ≤ C := le_of_mul_le_mul_right k2 hA
  linarith

/-! ### Plane geometry -/

lemma lc_inner_frame {u : E2} (hu : ‖u‖ = 1) (w e : E2) :
    inner ℝ w e = inner ℝ w u * inner ℝ e u + inner ℝ w (rot u) * inner ℝ e (rot u) := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
  simp only [inner_coords, rot_zero, rot_one]
  linear_combination (-(w 0 * e 0 + w 1 * e 1)) * hu2

/-- A unit vector far from `± u` has a large component along `rot u`. -/
lemma lc_far_inner {u e : E2} {ρ : ℝ} (hu : ‖u‖ = 1) (he : ‖e‖ = 1) (hρ : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (h1 : ρ ≤ dist e u) (h2 : ρ ≤ dist e (-u)) :
    ρ / 2 ≤ |inner ℝ e (rot u)| := by
  have hf := norm_sq_frame hu e
  rw [he] at hf
  have hd1 : ‖e - u‖ ^ 2 = 2 - 2 * inner ℝ e u := by
    rw [norm_sub_sq_real, he, hu]; ring
  have hd2 : ‖e - -u‖ ^ 2 = 2 + 2 * inner ℝ e u := by
    rw [sub_neg_eq_add, norm_add_sq_real, he, hu]; ring
  rw [dist_eq_norm] at h1 h2
  have k1 : ρ ^ 2 ≤ ‖e - u‖ ^ 2 := pow_le_pow_left₀ hρ h1 2
  have k2 : ρ ^ 2 ≤ ‖e - -u‖ ^ 2 := pow_le_pow_left₀ hρ h2 2
  rw [hd1] at k1
  rw [hd2] at k2
  have hb : ρ ^ 2 / 4 ≤ (inner ℝ e (rot u)) ^ 2 := by
    have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
    have hm : 0 ≤ (1 - inner ℝ e u - ρ ^ 2 / 2) * (1 + inner ℝ e u - ρ ^ 2 / 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg (sq_nonneg ρ) (sub_nonneg.mpr hρ2), sq_nonneg ρ]
  have hb' : (ρ / 2) ^ 2 ≤ |inner ℝ e (rot u)| ^ 2 := by
    rw [sq_abs, show (ρ / 2) ^ 2 = ρ ^ 2 / 4 by ring]; exact hb
  exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp hb'

/-- Two points near the line `⟪x, u⟫ = t`, far apart, are separated along a normal with a
large component along the line. -/
lemma lc_offset_sep {u e a a' : E2} {r t lam θ : ℝ} (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (hr : 0 < r) (hθ : 0 ≤ θ)
    (ha : |inner ℝ a u - t| ≤ 64 * r) (ha' : |inner ℝ a' u - t| ≤ 64 * r)
    (hlam : 256 * r ≤ lam) (hdist : lam ≤ dist a a')
    (hθe : θ ≤ |inner ℝ e (rot u)|) (hlθ : 258 * r ≤ lam * θ) :
    r ≤ |inner ℝ (a - a') e| := by
  have hα : |inner ℝ (a - a') u| ≤ 128 * r := by
    have : inner ℝ (a - a') u = (inner ℝ a u - t) - (inner ℝ a' u - t) := by
      rw [inner_sub_left]; ring
    rw [this]
    calc _ ≤ |inner ℝ a u - t| + |inner ℝ a' u - t| := abs_sub _ _
      _ ≤ 64 * r + 64 * r := add_le_add ha ha'
      _ = 128 * r := by ring
  have hwn : lam ≤ ‖a - a'‖ := by rw [← dist_eq_norm]; exact hdist
  have hf := norm_sq_frame hu (a - a')
  have hβ : lam / 2 ≤ |inner ℝ (a - a') (rot u)| := by
    have hlam0 : 0 ≤ lam := by linarith
    have h1 : lam ^ 2 ≤ ‖a - a'‖ ^ 2 := pow_le_pow_left₀ hlam0 hwn 2
    have h2 : (inner ℝ (a - a') u) ^ 2 ≤ (128 * r) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hα 2
    have h4 : (128 * r) ^ 2 ≤ lam ^ 2 / 4 := by
      have : (128 * r) ^ 2 ≤ (lam / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      rw [show (lam / 2) ^ 2 = lam ^ 2 / 4 by ring] at this; exact this
    have h3 : (lam / 2) ^ 2 ≤ |inner ℝ (a - a') (rot u)| ^ 2 := by
      rw [sq_abs, show (lam / 2) ^ 2 = lam ^ 2 / 4 by ring]; linarith [sq_nonneg lam]
    exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp h3
  have heu : |inner ℝ e u| ≤ 1 := by
    have := abs_real_inner_le_norm e u
    rw [he, hu] at this; linarith
  have k1 : lam / 2 * θ ≤ |inner ℝ (a - a') (rot u) * inner ℝ e (rot u)| := by
    rw [abs_mul]
    exact mul_le_mul hβ hθe hθ (abs_nonneg _)
  have k2 : |inner ℝ (a - a') u * inner ℝ e u| ≤ 128 * r := by
    rw [abs_mul]
    calc |inner ℝ (a - a') u| * |inner ℝ e u| ≤ 128 * r * 1 :=
          mul_le_mul hα heu (abs_nonneg _) (by positivity)
      _ = 128 * r := by ring
  have k3 : |inner ℝ (a - a') (rot u) * inner ℝ e (rot u)| -
      |inner ℝ (a - a') u * inner ℝ e u| ≤
      |inner ℝ (a - a') u * inner ℝ e u + inner ℝ (a - a') (rot u) * inner ℝ e (rot u)| := by
    have := abs_sub_abs_le_abs_sub (inner ℝ (a - a') (rot u) * inner ℝ e (rot u))
      (-(inner ℝ (a - a') u * inner ℝ e u))
    rwa [abs_neg, sub_neg_eq_add, add_comm] at this
  have k0 : lam / 2 * θ = (lam * θ) / 2 := by ring
  rw [lc_inner_frame hu (a - a') e]
  linarith

/-- If two unit vectors are both nearly orthogonal to a long vector `w`, they are close up
to sign. -/
lemma lc_normal_close {w e n : E2} {c d₀ : ℝ} (hd₀ : 0 < d₀) (hw : d₀ ≤ ‖w‖)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hwe : |inner ℝ w e| ≤ 2 * c)
    (hwn : |inner ℝ w n| ≤ 2 * c) :
    dist e n ≤ 8 * c / d₀ ∨ dist e (-n) ≤ 8 * c / d₀ := by
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw; linarith
  have hc0 : 0 ≤ c := by have := abs_nonneg (inner ℝ w e); linarith
  obtain ⟨e₀, -, hball⟩ := SP.unit_circle_strip_two_balls (v := w) hw0 (s := 2 * c)
  have hbound : 2 * (2 * c) / ‖w‖ ≤ 4 * c / d₀ := by
    rw [show 2 * (2 * c) = 4 * c by ring]
    exact div_le_div_of_nonneg_left (by positivity) hd₀ hw
  have h1 := hball e he (by rw [real_inner_comm]; exact hwe)
  have h2 := hball n hn (by rw [real_inner_comm]; exact hwn)
  have key : 8 * c / d₀ = 4 * c / d₀ + 4 * c / d₀ := by ring
  rw [key]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left
    calc dist e n ≤ dist e e₀ + dist e₀ n := dist_triangle _ _ _
      _ = dist e e₀ + dist n e₀ := by rw [dist_comm e₀ n]
      _ ≤ _ := by linarith
  · right
    calc dist e (-n) ≤ dist e e₀ + dist e₀ (-n) := dist_triangle _ _ _
      _ = dist e e₀ + dist n (-e₀) := by
          rw [← dist_neg_neg e₀ (-n), neg_neg, dist_comm (-e₀) n]
      _ ≤ _ := by linarith
  · right
    calc dist e (-n) ≤ dist e (-e₀) + dist (-e₀) (-n) := dist_triangle _ _ _
      _ = dist e (-e₀) + dist n e₀ := by rw [dist_neg_neg, dist_comm e₀ n]
      _ ≤ _ := by linarith
  · left
    calc dist e n ≤ dist e (-e₀) + dist (-e₀) n := dist_triangle _ _ _
      _ = dist e (-e₀) + dist n (-e₀) := by rw [dist_comm (-e₀) n]
      _ ≤ _ := by linarith

/-! ### Far normals of a bush -/

/-- The normals of the bush of `p` that are `ρ₀`-far from `± u`. -/
noncomputable def lc_far (D : Finset (E2 × E2)) (u : E2) (ρ₀ : ℝ) (p : E2) : Finset E2 :=
  (bushOf D p).filter (fun e => ρ₀ ≤ dist e u ∧ ρ₀ ≤ dist e (-u))

lemma lc_mem_far {D : Finset (E2 × E2)} {u : E2} {ρ₀ : ℝ} {p e : E2} :
    e ∈ lc_far D u ρ₀ p ↔ e ∈ bushOf D p ∧ ρ₀ ≤ dist e u ∧ ρ₀ ≤ dist e (-u) := by
  unfold lc_far; exact Finset.mem_filter

lemma lc_far_sub_bush {D : Finset (E2 × E2)} {u : E2} {ρ₀ : ℝ} {p : E2} :
    lc_far D u ρ₀ p ⊆ bushOf D p :=
  fun _ he => (lc_mem_far.mp he).1

lemma lc_far_unit {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {u : E2} {ρ₀ : ℝ} {p e : E2} (he : e ∈ lc_far D u ρ₀ p) :
    ‖e‖ = 1 :=
  (h.D_mem _ (mem_bushOf.mp (lc_mem_far.mp he).1)).2

lemma lc_kt_r {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p : E2} (hp : p ∈ P) {u : E2} (hu : ‖u‖ = 1) :
    (((bushOf D p).filter (fun e => dist e u ≤ r)).card : ℝ) ≤ r ^ (-η) := by
  have := h.D_kt p hp u hu r le_rfl
  rwa [div_self h.r_pos.ne', Real.one_rpow, mul_one] at this

/-- Few normals of a bush are near `± u`. -/
lemma lc_far_card {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p : E2} (hp : p ∈ P) {u : E2} (hu : ‖u‖ = 1) {ρ₀ : ℝ}
    (hρ₀ : r ≤ ρ₀) :
    ((bushOf D p).card : ℝ) ≤
      ((lc_far D u ρ₀ p).card : ℝ) + 2 * (r ^ (-η) * (ρ₀ / r) ^ (1 / 2 : ℝ)) := by
  classical
  have hsub : bushOf D p ⊆ lc_far D u ρ₀ p ∪
      ((bushOf D p).filter (fun e => dist e u ≤ ρ₀) ∪
        (bushOf D p).filter (fun e => dist e (-u) ≤ ρ₀)) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_filter, lc_mem_far]
    by_cases h1 : ρ₀ ≤ dist e u
    · by_cases h2 : ρ₀ ≤ dist e (-u)
      · exact Or.inl ⟨he, h1, h2⟩
      · exact Or.inr (Or.inr ⟨he, (not_le.mp h2).le⟩)
    · exact Or.inr (Or.inl ⟨he, (not_le.mp h1).le⟩)
  have hc := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have hc' : ((bushOf D p).card : ℝ) ≤ ((lc_far D u ρ₀ p).card : ℝ) +
      ((((bushOf D p).filter (fun e => dist e u ≤ ρ₀)).card : ℝ) +
        (((bushOf D p).filter (fun e => dist e (-u) ≤ ρ₀)).card : ℝ)) := by
    exact_mod_cast hc
  have h1 := h.D_kt p hp u hu ρ₀ hρ₀
  have h2 := h.D_kt p hp (-u) (by rw [norm_neg, hu]) ρ₀ hρ₀
  linarith

/-- A subset of a bush covered by the `r`-neighbourhoods of `± e'`, `e' ∈ B`, has at most
`2 r ^ (-η) #B` elements. -/
lemma lc_sep_card {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p : E2} (hp : p ∈ P) (F B : Finset E2)
    (hF : F ⊆ bushOf D p) (hB : ∀ e' ∈ B, ‖e'‖ = 1)
    (hcov : ∀ e ∈ F, ∃ e' ∈ B, dist e e' < r ∨ dist e (-e') < r) :
    (F.card : ℝ) ≤ B.card * (2 * r ^ (-η)) := by
  classical
  have hsub : F ⊆ B.biUnion (fun e' => (bushOf D p).filter (fun e => dist e e' ≤ r) ∪
      (bushOf D p).filter (fun e => dist e (-e') ≤ r)) := by
    intro e he
    obtain ⟨e', he', hcl⟩ := hcov e he
    rw [Finset.mem_biUnion]
    refine ⟨e', he', ?_⟩
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hcl with hc | hc
    · exact Or.inl ⟨hF he, hc.le⟩
    · exact Or.inr ⟨hF he, hc.le⟩
  have hc1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hc2 : ∀ e' ∈ B, ((((bushOf D p).filter (fun e => dist e e' ≤ r) ∪
      (bushOf D p).filter (fun e => dist e (-e') ≤ r)).card : ℕ) : ℝ) ≤ 2 * r ^ (-η) := by
    intro e' he'
    have h1 := lc_kt_r h hp (hB e' he')
    have h2 := lc_kt_r h hp (u := -e') (by rw [norm_neg]; exact hB e' he')
    have h3 : ((((bushOf D p).filter (fun e => dist e e' ≤ r) ∪
        (bushOf D p).filter (fun e => dist e (-e') ≤ r)).card : ℕ) : ℝ) ≤
        (((bushOf D p).filter (fun e => dist e e' ≤ r)).card : ℝ) +
        (((bushOf D p).filter (fun e => dist e (-e') ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_union_le _ _
    linarith
  have hc3 := Finset.sum_le_sum hc2
  rw [Finset.sum_const, nsmul_eq_mul] at hc3
  have hc4 : (F.card : ℝ) ≤ ∑ e' ∈ B, ((((bushOf D p).filter (fun e => dist e e' ≤ r) ∪
      (bushOf D p).filter (fun e => dist e (-e') ≤ r)).card : ℕ) : ℝ) := by
    exact_mod_cast hc1
  linarith

/-- A maximal `r`-separated (up to sign) set of far normals is large. -/
lemma lc_bush_lower {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {p : E2} (hp : p ∈ P) {u : E2} (hu : ‖u‖ = 1) {ρ₀ : ℝ}
    (hρ₀ : ρ₀ = r ^ (4 * η) / 16) (hρ₀r : r ≤ ρ₀) (B : Finset E2)
    (hBF : B ⊆ lc_far D u ρ₀ p)
    (hBcov : ∀ e ∈ lc_far D u ρ₀ p, ∃ e' ∈ B, dist e e' < r ∨ dist e (-e') < r) :
    r ^ (2 * η - 1 / 2) / 4 ≤ (B.card : ℝ) := by
  have hr0 := h.r_pos
  have h1 := lc_far_card h hp hu hρ₀r
  have h2 := h.D_card p hp
  have h3 := lc_far_bound (η := η) hr0 hρ₀
  have h4 := lc_sep_card h hp (lc_far D u ρ₀ p) B lc_far_sub_bush
    (fun e' he' => lc_far_unit h (hBF he')) hBcov
  have h5 : r ^ (η - 1 / 2) = r ^ (2 * η - 1 / 2) * r ^ (-η) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have hK : 0 < r ^ (-η) := by positivity
  have h6 : r ^ (2 * η - 1 / 2) / 4 * (2 * r ^ (-η)) ≤ (B.card : ℝ) * (2 * r ^ (-η)) := by
    have : r ^ (2 * η - 1 / 2) / 4 * (2 * r ^ (-η)) = r ^ (η - 1 / 2) / 2 := by
      rw [h5]; ring
    rw [this]
    linarith
  exact le_of_mul_le_mul_right h6 (by positivity)

/-! ### The separated family through separated points -/

lemma lc_family {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) {u : E2} (hu : ‖u‖ = 1) {t ρ₀ lam : ℝ}
    (hρ₀ : 0 ≤ ρ₀) (hρ₀1 : ρ₀ ≤ 1)
    (hlam : 256 * r ≤ lam) (hlamθ : 258 * r ≤ lam * (ρ₀ / 2))
    (S' : Finset E2)
    (hS'line : ∀ a ∈ S', |inner ℝ a u - t| ≤ 64 * r)
    (hS'pair : ∀ a ∈ S', ∀ a' ∈ S', a ≠ a' → lam ≤ dist a a')
    (B : E2 → Finset E2) (hBF : ∀ a, B a ⊆ lc_far D u ρ₀ a)
    (hBsep : ∀ a, (B a : Set E2).Pairwise (NormSep r)) :
    ∑ a ∈ S', ((B a).card : ℝ) < r ^ (-1 - ε₀) := by
  classical
  have hr0 := h.r_pos
  set J : Finset (E2 × E2) := S'.biUnion (fun a => (B a).image (Prod.mk a)) with hJ
  have hJmem : ∀ q ∈ J, q.1 ∈ S' ∧ q.2 ∈ B q.1 := by
    intro q hq
    rw [hJ, Finset.mem_biUnion] at hq
    obtain ⟨a, ha, hq⟩ := hq
    rw [Finset.mem_image] at hq
    obtain ⟨e, he, rfl⟩ := hq
    exact ⟨ha, he⟩
  have hJD : J ⊆ D := by
    intro q hq
    obtain ⟨_, he⟩ := hJmem q hq
    have hb : q.2 ∈ bushOf D q.1 := (lc_mem_far.mp (hBF q.1 he)).1
    have := mem_bushOf.mp hb
    simpa using this
  have hJsep : ∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → StripSep r q q' := by
    intro q hq q' hq' hne
    obtain ⟨ha, he⟩ := hJmem q hq
    obtain ⟨ha', he'⟩ := hJmem q' hq'
    unfold StripSep
    by_cases haa : q.1 = q'.1
    · have hee : q.2 ≠ q'.2 := fun h2 => hne (Prod.ext haa h2)
      rw [haa] at he
      left
      exact hBsep q'.1 (Finset.mem_coe.mpr he) (Finset.mem_coe.mpr he') hee
    · right
      have hF := lc_mem_far.mp (hBF q.1 he)
      have heu : ‖q.2‖ = 1 := lc_far_unit h (hBF q.1 he)
      have hθe : ρ₀ / 2 ≤ |inner ℝ q.2 (rot u)| :=
        lc_far_inner hu heu hρ₀ hρ₀1 hF.2.1 hF.2.2
      exact lc_offset_sep hu heu hr0 (by linarith) (hS'line _ ha) (hS'line _ ha') hlam
        (hS'pair _ ha _ ha' haa) hθe hlamθ
  have hJcard : (J.card : ℝ) = ∑ a ∈ S', ((B a).card : ℝ) := by
    have hdisj : (S' : Set E2).PairwiseDisjoint (fun a => (B a).image (Prod.mk a)) := by
      intro a _ a' _ haa
      show Disjoint ((B a).image (Prod.mk a)) ((B a').image (Prod.mk a'))
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_image] at hx hx'
      obtain ⟨e, _, rfl⟩ := hx
      obtain ⟨e', _, he'⟩ := hx'
      exact haa (congrArg Prod.fst he').symm
    rw [hJ, Finset.card_biUnion hdisj]
    push_cast
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.card_image_of_injective _ (Prod.mk_right_injective a)]
  rw [← hJcard]
  exact h.few_lines J hJD hJsep

/-- Covering a set of points by the `lam`-balls about a subset. -/
lemma lc_cover_card {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (S S' : Finset E2) (hSP : S ⊆ P) {lam : ℝ} (hlam : r ≤ lam)
    (hcov : ∀ q ∈ S, ∃ a ∈ S', dist q a ≤ lam) :
    (S.card : ℝ) ≤ S'.card * (r ^ (-η) * (lam / r)) := by
  classical
  have hsub : S ⊆ S'.biUnion (fun a => P.filter (fun p => dist p a ≤ lam)) := by
    intro q hq
    obtain ⟨a, ha, hd⟩ := hcov q hq
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, Finset.mem_filter.mpr ⟨hSP hq, hd⟩⟩
  have hc1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hc2 : ∀ a ∈ S', (((P.filter (fun p => dist p a ≤ lam)).card : ℕ) : ℝ) ≤
      r ^ (-η) * (lam / r) := fun a _ => h.P_kt a lam hlam
  have hc3 := Finset.sum_le_sum hc2
  rw [Finset.sum_const, nsmul_eq_mul] at hc3
  have hc4 : (S.card : ℝ) ≤ ∑ a ∈ S', (((P.filter (fun p => dist p a ≤ lam)).card : ℕ) : ℝ) := by
    exact_mod_cast hc1
  linarith

/-! ### The line count -/

theorem HalfData.line_count {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hr : r ≤ 1 / 100) (hη : 0 < η) (hη1 : η ≤ 1 / 100)
    (u : E2) (hu : ‖u‖ = 1) (t : ℝ) :
    ((P.filter (fun p => |inner ℝ p u - t| ≤ 64 * r)).card : ℝ) ≤
      10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η) := by
  have hr0 := h.r_pos
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = r ^ (4 * η) / 16 := ⟨_, rfl⟩
  have hρ₀r : r ≤ ρ₀ := by rw [hρ₀]; exact lc_rho_ge hr0 hr hη1
  have hρ₀1 : ρ₀ ≤ 1 / 16 := by
    have : r ^ (4 * η) ≤ 1 := Real.rpow_le_one hr0.le (by linarith) (by linarith)
    rw [hρ₀]; linarith
  have hρ₀0 : 0 < ρ₀ := lt_of_lt_of_le hr0 hρ₀r
  have hθ0 : 0 < ρ₀ / 2 := by linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 258 * r / (ρ₀ / 2) := ⟨_, rfl⟩
  have hlamθ : lam * (ρ₀ / 2) = 258 * r := by
    rw [hlam, div_mul_cancel₀ _ hθ0.ne']
  have hlam256 : 256 * r ≤ lam := by
    rw [hlam, le_div_iff₀ hθ0]
    nlinarith [mul_nonneg hr0.le (by linarith : (0 : ℝ) ≤ 1 / 16 - ρ₀)]
  have hlamr : lam / r = 8256 * r ^ (-(4 * η)) := by
    have hp : 0 < r ^ (4 * η) := by positivity
    rw [Real.rpow_neg hr0.le, hlam, hρ₀]
    field_simp
    ring
  -- the separated far normals
  have hB : ∀ p : E2, ∃ B : Finset E2, B ⊆ lc_far D u ρ₀ p ∧
      (B : Set E2).Pairwise (NormSep r) ∧
      ∀ e ∈ lc_far D u ρ₀ p, ∃ e' ∈ B, dist e e' < r ∨ dist e (-e') < r := by
    intro p
    obtain ⟨B, hBF, hBsep, hBcov⟩ := exists_maximal_normSep (lc_far D u ρ₀ p : Set E2)
      (fun e he => lc_far_unit h (Finset.mem_coe.mp he)) hr0
    exact ⟨B, Finset.coe_subset.mp hBF, hBsep, fun e he => hBcov e (Finset.mem_coe.mpr he)⟩
  choose B hBF hBsep hBcov using hB
  -- the separated points
  obtain ⟨S, hS⟩ : ∃ S : Finset E2, S = P.filter (fun p => |inner ℝ p u - t| ≤ 64 * r) :=
    ⟨_, rfl⟩
  rw [← hS]
  have hSP : S ⊆ P := by rw [hS]; exact Finset.filter_subset _ _
  obtain ⟨S', hS'S, hS'pair, hS'max⟩ := exists_maximal_pairwise S (fun a b => lam ≤ dist a b)
  have hcovS : ∀ q ∈ S, ∃ a ∈ S', dist q a ≤ lam := by
    intro q hq
    by_cases hqS' : q ∈ S'
    · exact ⟨q, hqS', by rw [dist_self]; linarith⟩
    · obtain ⟨j, hj, hR⟩ := hS'max q hq hqS'
      refine ⟨j, hj, ?_⟩
      rcases hR with hR | hR
      · exact (not_le.mp hR).le
      · rw [dist_comm]; exact (not_le.mp hR).le
  have hScard := lc_cover_card h S S' hSP (by linarith) hcovS
  have hS'line : ∀ a ∈ S', |inner ℝ a u - t| ≤ 64 * r := by
    intro a ha
    have := hS'S ha
    rw [hS, Finset.mem_filter] at this
    exact this.2
  have hsumlt := lc_family h hu hρ₀0.le (by linarith) hlam256 hlamθ.ge S' hS'line hS'pair
    B hBF hBsep
  have hsumB : (S'.card : ℝ) * (r ^ (2 * η - 1 / 2) / 4) ≤ ∑ a ∈ S', ((B a).card : ℝ) := by
    have h1 : ∀ a ∈ S', r ^ (2 * η - 1 / 2) / 4 ≤ ((B a).card : ℝ) := fun a ha =>
      lc_bush_lower h (hSP (hS'S ha)) hu hρ₀ hρ₀r (B a) (hBF a) (hBcov a)
    have := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  -- arithmetic
  have h3 : r ^ (-η) * (lam / r) * r ^ (-1 - ε₀) ≤
      10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η) * (r ^ (2 * η - 1 / 2) / 4) := by
    rw [hlamr]
    have hZ1 : r ^ (-η) * r ^ (-(4 * η)) * r ^ (-1 - ε₀) = r ^ (-1 - ε₀ - 5 * η) := by
      rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]; congr 1; ring
    have hZ2 : r ^ (-(1 / 2) - ε₀ - 7 * η) * r ^ (2 * η - 1 / 2) = r ^ (-1 - ε₀ - 5 * η) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    have hZ : 0 < r ^ (-1 - ε₀ - 5 * η) := by positivity
    calc r ^ (-η) * (8256 * r ^ (-(4 * η))) * r ^ (-1 - ε₀)
        = 8256 * (r ^ (-η) * r ^ (-(4 * η)) * r ^ (-1 - ε₀)) := by ring
      _ = 8256 * r ^ (-1 - ε₀ - 5 * η) := by rw [hZ1]
      _ ≤ (10 ^ 7 / 4) * r ^ (-1 - ε₀ - 5 * η) :=
          mul_le_mul_of_nonneg_right (by norm_num) hZ.le
      _ = (10 ^ 7 / 4) * (r ^ (-(1 / 2) - ε₀ - 7 * η) * r ^ (2 * η - 1 / 2)) := by rw [hZ2]
      _ = 10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η) * (r ^ (2 * η - 1 / 2) / 4) := by ring
  have hX : 0 ≤ r ^ (-η) * (lam / r) :=
    mul_nonneg (by positivity) (div_nonneg (by linarith) hr0.le)
  exact lc_final_arith hX (by positivity) hScard (lt_of_le_of_lt hsumB hsumlt) h3

/-! ### Points near a line through a point, on strips of its bush -/

theorem HalfData.near_line_degree {r ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : HalfData r ε₀ η P D) (hr : r ≤ 1 / 100) (hη : 0 < η) (hη1 : η ≤ 1 / 100)
    (p : E2) (hp : p ∈ P) (n p₀ : E2) (hn : ‖n‖ = 1)
    (hpl : |inner ℝ (p - p₀) n| ≤ 64 * r) {c d₀ : ℝ} (hd₀ : 0 < d₀) (hc : 64 * r ≤ c) :
    ((P.filter (fun q => d₀ ≤ dist q p ∧ |inner ℝ (q - p₀) n| < c ∧
        ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 64 * r)).card : ℝ) ≤
      10 ^ 9 * r ^ (-1 - ε₀ - 8 * η) * (c / d₀) ^ (1 / 2 : ℝ) := by
  classical
  have hr0 := h.r_pos
  have hc0 : 0 < c := by linarith
  obtain ⟨T, hT⟩ : ∃ T : Finset E2, T = P.filter (fun q => d₀ ≤ dist q p ∧
      |inner ℝ (q - p₀) n| < c ∧ ∃ e ∈ bushOf D p, |inner ℝ (q - p) e| < 64 * r) := ⟨_, rfl⟩
  rw [← hT]
  rcases T.eq_empty_or_nonempty with hTe | ⟨q₀, hq₀⟩
  · rw [hTe, Finset.card_empty, Nat.cast_zero]; positivity
  have hd8 : d₀ ≤ 8 := by
    rw [hT, Finset.mem_filter] at hq₀
    have h8 : dist q₀ p ≤ 8 := by
      rw [dist_eq_norm]; exact norm_le_eight_of_norm_le_four (h.P_norm _ hq₀.1) (h.P_norm _ hp)
    linarith [hq₀.2.1]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 8 * c / d₀ := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρr : r ≤ ρ := by
    rw [hρ, le_div_iff₀ hd₀]
    nlinarith
  -- the normals close to `± n`
  obtain ⟨E, hE⟩ : ∃ E : Finset E2, E = (bushOf D p).filter (fun e => dist e n ≤ ρ) ∪
      (bushOf D p).filter (fun e => dist e (-n) ≤ ρ) := ⟨_, rfl⟩
  have hEcard : (E.card : ℝ) ≤ 2 * (r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ)) := by
    have h1 := h.D_kt p hp n hn ρ hρr
    have h2 := h.D_kt p hp (-n) (by rw [norm_neg, hn]) ρ hρr
    have h3 : (E.card : ℝ) ≤ (((bushOf D p).filter (fun e => dist e n ≤ ρ)).card : ℝ) +
        (((bushOf D p).filter (fun e => dist e (-n) ≤ ρ)).card : ℝ) := by
      rw [hE]; exact_mod_cast Finset.card_union_le _ _
    linarith
  have hEbush : ∀ e ∈ E, e ∈ bushOf D p := by
    intro e he
    rw [hE, Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at he
    rcases he with he | he
    · exact he.1
    · exact he.1
  -- every point lies on a strip with normal in `E`
  have hTsub : T ⊆ E.biUnion
      (fun e => P.filter (fun x => |inner ℝ x e - inner ℝ p e| ≤ 64 * r)) := by
    intro q hq
    rw [hT, Finset.mem_filter] at hq
    obtain ⟨hqP, hqd, hqn, e, he, hqe⟩ := hq
    rw [Finset.mem_biUnion]
    have heu : ‖e‖ = 1 := (h.D_mem _ (mem_bushOf.mp he)).2
    refine ⟨e, ?_, ?_⟩
    · have hw : d₀ ≤ ‖q - p‖ := by rw [← dist_eq_norm]; exact hqd
      have hwe : |inner ℝ (q - p) e| ≤ 2 * c := by linarith
      have hwn : |inner ℝ (q - p) n| ≤ 2 * c := by
        have : inner ℝ (q - p) n = inner ℝ (q - p₀) n - inner ℝ (p - p₀) n := by
          rw [← inner_sub_left]; congr 1; abel
        rw [this]
        calc _ ≤ |inner ℝ (q - p₀) n| + |inner ℝ (p - p₀) n| := abs_sub _ _
          _ ≤ 2 * c := by linarith
      have hcl := lc_normal_close hd₀ hw heu hn hwe hwn
      rw [hE, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, hρ]
      rcases hcl with h1 | h1
      · exact Or.inl ⟨he, h1⟩
      · exact Or.inr ⟨he, h1⟩
    · rw [Finset.mem_filter, ← inner_sub_left]
      exact ⟨hqP, hqe.le⟩
  have hstrip : ∀ e ∈ E,
      (((P.filter (fun x => |inner ℝ x e - inner ℝ p e| ≤ 64 * r)).card : ℕ) : ℝ) ≤
        10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η) := by
    intro e he
    have heu : ‖e‖ = 1 := (h.D_mem _ (mem_bushOf.mp (hEbush e he))).2
    exact h.line_count hr hη hη1 e heu (inner ℝ p e)
  have hTcard : (T.card : ℝ) ≤ E.card * (10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η)) := by
    have hc1 := (Finset.card_le_card hTsub).trans Finset.card_biUnion_le
    have hc3 := Finset.sum_le_sum hstrip
    rw [Finset.sum_const, nsmul_eq_mul] at hc3
    have hc4 : (T.card : ℝ) ≤ ∑ e ∈ E,
        (((P.filter (fun x => |inner ℝ x e - inner ℝ p e| ≤ 64 * r)).card : ℕ) : ℝ) := by
      exact_mod_cast hc1
    linarith
  -- the square root
  have hX : (ρ / r) ^ (1 / 2 : ℝ) ≤ 3 * (c / d₀) ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
    have hA0 : 0 ≤ (ρ / r) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (div_nonneg hρ0 hr0.le) _
    have hB0 : 0 ≤ 3 * (c / d₀) ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by positivity
    rw [← sq_le_sq₀ hA0 hB0]
    rw [mul_pow, mul_pow, lc_sq_rpow_half (y := ρ / r) (div_nonneg hρ0 hr0.le),
      lc_sq_rpow_half (y := c / d₀) (by positivity)]
    have hr2 : (r ^ (-(1 / 2 : ℝ))) ^ 2 = r⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le, ← Real.rpow_neg_one]
      norm_num
    rw [hr2, hρ]
    have hnn : 0 ≤ c / d₀ * r⁻¹ := by positivity
    have e1 : 8 * c / d₀ / r = 8 * (c / d₀ * r⁻¹) := by ring
    have e2 : (3 : ℝ) ^ 2 * (c / d₀) * r⁻¹ = 9 * (c / d₀ * r⁻¹) := by ring
    rw [e1, e2]
    linarith
  have hexp : r ^ (-(1 / 2) - ε₀ - 7 * η) * r ^ (-η) * r ^ (-(1 / 2 : ℝ)) =
      r ^ (-1 - ε₀ - 8 * η) := by
    rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]; congr 1; ring
  have hL0 : 0 ≤ 10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η) := by positivity
  have hY0 : 0 ≤ (c / d₀) ^ (1 / 2 : ℝ) := by positivity
  have hZ0 : 0 ≤ r ^ (-1 - ε₀ - 8 * η) := by positivity
  calc (T.card : ℝ) ≤ E.card * (10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η)) := hTcard
    _ ≤ (2 * (r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ))) * (10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η)) :=
        mul_le_mul_of_nonneg_right hEcard hL0
    _ ≤ (2 * (r ^ (-η) * (3 * (c / d₀) ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))))) *
          (10 ^ 7 * r ^ (-(1 / 2) - ε₀ - 7 * η)) := by gcongr
    _ = 6 * 10 ^ 7 * (r ^ (-(1 / 2) - ε₀ - 7 * η) * r ^ (-η) * r ^ (-(1 / 2 : ℝ))) *
          (c / d₀) ^ (1 / 2 : ℝ) := by ring
    _ = 6 * 10 ^ 7 * r ^ (-1 - ε₀ - 8 * η) * (c / d₀) ^ (1 / 2 : ℝ) := by rw [hexp]
    _ ≤ 10 ^ 9 * r ^ (-1 - ε₀ - 8 * η) * (c / d₀) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hZ0) hY0

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
