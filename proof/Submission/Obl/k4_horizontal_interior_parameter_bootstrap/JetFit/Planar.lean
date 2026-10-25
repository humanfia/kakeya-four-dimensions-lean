import Submission.WZ.Obl.wz_ad_projection_dichotomy
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Cover

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The planar input without expansion

Paper Theorem 5.5 (`a04:planar-input`) is `WangZahlLot.wz_ad_projection_dichotomy`.
In the proof of Proposition 5.4 its expansion alternative is impossible, because all the
dot products `a · (b - b')` of the collision triples lie within `e ≤ Kδ` of a set `Σ` with
local upper `d`-count. `nearLine_of_dot_count` records the remaining line alternative for
the first set.
-/

open Metric Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

/-- The regularity hypothesis of the planar input, with constant `C`. -/
def PlanarRegular (F : Set E2) (δ C : ℝ) : Prop :=
  ∀ (x : E2) (ρ r : ℝ), δ ≤ ρ → ρ ≤ r → ∃ (m : ℕ) (cc : Fin m → E2),
    F ∩ ball x r ⊆ ⋃ j, closedBall (cc j) ρ ∧ (m : ℝ) ≤ C * (r / ρ)

/-- The line alternative of the planar input, for the first set only. -/
def NearLine (F : Set E2) (δ ε : ℝ) : Prop :=
  ∃ (e : E2) (c : ℝ), ‖e‖ = 1 ∧ ∀ (m : ℕ) (cc : Fin m → E2),
    thickening δ {a | inner ℝ a e = c} ∩ F ⊆ ⋃ j, closedBall (cc j) δ → δ ^ (ε - 1) ≤ m

/-- A set of reals has local upper `d`-count with constant `K` above scale `δ`. -/
def LocalCount (S : Set ℝ) (δ K d : ℝ) : Prop :=
  ∀ a L s : ℝ, δ ≤ s → s ≤ L → ∃ (m : ℕ) (cc : Fin m → ℝ),
    S ∩ Icc a (a + L) ⊆ ⋃ j, closedBall (cc j) s ∧ (m : ℝ) ≤ K * (L / s) ^ d

/-- Covering a fattened cover: if `X ⊆ ⋃ closedBall (c j) s` and every point of `Y` is within
`e ≤ K s` of `X`, then `Y` is covered by `m (⌈K⌉ + 1)` closed `s`-balls. -/
theorem cover_fatten {m : ℕ} (cc : Fin m → ℝ) {s e K : ℝ} (hs : 0 < s) (he : e ≤ K * s)
    {X Y : Set ℝ} (hX : X ⊆ ⋃ j, closedBall (cc j) s) (hY : ∀ y ∈ Y, ∃ x ∈ X, |y - x| ≤ e) :
    ∃ cc' : Fin (m * (⌈K⌉₊ + 1)) → ℝ, Y ⊆ ⋃ j, closedBall (cc' j) s := by
  set M : ℕ := ⌈K⌉₊ + 1 with hM
  have hMpos : 0 < M := by omega
  let f : Fin m × Fin M → ℝ := fun ji => cc ji.1 - s - e + (2 * (ji.2 : ℝ) + 1) * s
  refine ⟨fun k => f (finProdFinEquiv.symm k), ?_⟩
  intro y hy
  obtain ⟨x, hxX, hyx⟩ := hY y hy
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hX hxX)
  rw [mem_closedBall, Real.dist_eq] at hj
  -- `y` lies in `[cc j - s - e, cc j + s + e]`
  set t : ℝ := y - (cc j - s - e) with ht
  have ht0 : 0 ≤ t := by
    have := (abs_le.1 hyx).1; have := (abs_le.1 hj).1; linarith
  have hKs : e ≤ (⌈K⌉₊ : ℝ) * s := he.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil K) hs.le)
  have ht2 : t ≤ 2 * (M : ℝ) * s := by
    have := (abs_le.1 hyx).2; have := (abs_le.1 hj).2
    simp only [hM]; push_cast; nlinarith
  set i : ℕ := min (⌊t / (2 * s)⌋₊) (M - 1) with hi
  have hiM : i < M := by omega
  refine mem_iUnion.2 ⟨finProdFinEquiv (j, ⟨i, hiM⟩), ?_⟩
  simp only [Equiv.symm_apply_apply, f, mem_closedBall, Real.dist_eq]
  have h2s : 0 < 2 * s := by linarith
  have hfl := Nat.floor_le (div_nonneg ht0 h2s.le)
  have hfl2 := Nat.lt_floor_add_one (t / (2 * s))
  rw [abs_le]
  by_cases hcase : ⌊t / (2 * s)⌋₊ ≤ M - 1
  · have hieq : (i : ℝ) = ⌊t / (2 * s)⌋₊ := by rw [hi, min_eq_left hcase]
    rw [hieq]
    rw [le_div_iff₀ h2s] at hfl
    rw [div_lt_iff₀ h2s] at hfl2
    constructor <;> nlinarith
  · push Not at hcase
    have hieq : (i : ℝ) = ((M - 1 : ℕ) : ℝ) := by rw [hi, min_eq_right hcase.le]
    rw [hieq]
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hM1]
    have hlow : (M : ℝ) - 1 + 1 ≤ t / (2 * s) := by
      have : ((M - 1 : ℕ) : ℝ) + 1 ≤ (⌊t / (2 * s)⌋₊ : ℝ) := by exact_mod_cast hcase
      rw [hM1] at this; linarith
    rw [le_div_iff₀ h2s] at hlow
    constructor <;> nlinarith

/-- **The planar input without expansion.** If every dot product of the collision triples is
within `e ≤ Kδ` of a set with local upper `d`-count `K`, and `K` is below the small power
`δ^(-η(1-ε-d))`, the first set lies near a line in the sense of the planar input. -/
theorem nearLine_of_dot_count {ε d : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) (hεd : ε + d < 1) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ K : ℝ, 1 ≤ K →
      3 * K ^ 2 * (K + 2) < δ ^ (-η * (1 - ε - d)) →
      ∀ F G : Set E2, (∀ a ∈ F, ∀ i : Fin 2, 0 ≤ a i ∧ a i ≤ 1) →
      (∀ b ∈ G, ∀ i : Fin 2, 0 ≤ b i ∧ b i ≤ 1) →
      PlanarRegular F δ (δ ^ (-η)) → PlanarRegular G δ (δ ^ (-η)) →
      ∀ Q : Set (E2 × E2 × E2), Q ⊆ F ×ˢ (G ×ˢ G) →
      (∀ (m : ℕ) (cc : Fin m → E2 × E2 × E2), Q ⊆ ⋃ j, closedBall (cc j) δ → δ ^ (η - 3) ≤ m) →
      ∀ (S : Set ℝ) (e : ℝ), e ≤ K * δ →
      (∀ h ∈ Q, ∃ σ ∈ S, |inner ℝ h.1 (h.2.1 - h.2.2) - σ| ≤ e) →
      LocalCount S δ K d → NearLine F δ ε := by
  obtain ⟨η, δ₀, hη, hδ₀, hWZ⟩ := WangZahlLot.wz_ad_projection_dichotomy ε hε
  refine ⟨η, min δ₀ 1, hη, lt_min hδ₀ one_pos, ?_⟩
  intro δ hδ hδδ₀ K hK hKsmall F G hF hG hregF hregG Q hQ hQcov S e heK hdots hcount
  have hδ1 : δ ≤ 1 := hδδ₀.trans (min_le_right _ _)
  rcases hWZ δ hδ (hδδ₀.trans (min_le_left _ _)) F G hF hG hregF hregG with
    ⟨e', b₀, c, he1, hF1, -⟩ | hAlt2
  · exact ⟨e', c, he1, hF1⟩
  exfalso
  obtain ⟨ρ, a, L, hδρ, hρL, hcov⟩ := hAlt2 Q hQ hQcov
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hpow1 : 1 ≤ δ ^ (-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hρL' : ρ ≤ L := le_trans (by nlinarith) hρL
  have hL : 0 < L := hρ.trans_le hρL'
  have heρ : e ≤ K * ρ := heK.trans (mul_le_mul_of_nonneg_left hδρ (by linarith))
  -- `e ≥ 0`, since otherwise `Q` would be empty
  have he0 : 0 ≤ e := by
    by_contra hneg
    push Not at hneg
    have hQe : Q = ∅ := by
      ext h; simp only [mem_empty_iff_false, iff_false]
      intro hh; obtain ⟨σ, -, hσ⟩ := hdots h hh
      linarith [abs_nonneg (inner ℝ h.1 (h.2.1 - h.2.2) - σ)]
    have := hQcov 0 (fun i => i.elim0) (by rw [hQe]; exact empty_subset _)
    have hpos : 0 < δ ^ (η - 3) := Real.rpow_pos_of_pos hδ _
    simp at this; linarith
  -- the count cover of `S` near the interval
  obtain ⟨m₀, cc₀, hcov₀, hm₀⟩ := hcount (a - e) (L + 2 * e) ρ hδρ (by linarith)
  have hdotsI : ∀ y ∈ Icc a (a + L) ∩ {t : ℝ | ∃ h ∈ Q, t = inner ℝ h.1 (h.2.1 - h.2.2)},
      ∃ x ∈ S ∩ Icc (a - e) (a - e + (L + 2 * e)), |y - x| ≤ e := by
    rintro y ⟨hyI, h, hhQ, rfl⟩
    obtain ⟨σ, hσS, hσ⟩ := hdots h hhQ
    refine ⟨σ, ⟨hσS, ?_⟩, hσ⟩
    rw [mem_Icc] at hyI ⊢
    constructor <;> linarith [(abs_le.1 hσ).1, (abs_le.1 hσ).2]
  obtain ⟨cc', hcc'⟩ := cover_fatten cc₀ hρ heρ hcov₀ hdotsI
  have hbig := hcov _ cc' hcc'
  push_cast at hbig
  -- compare the two counts
  have hLρ : 1 ≤ L / ρ := by rw [le_div_iff₀ hρ]; linarith
  have hM : ((⌈K⌉₊ : ℝ) + 1) ≤ K + 2 := by linarith [Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ K)]
  have hratio : (L + 2 * e) / ρ ≤ 3 * K * (L / ρ) := by
    rw [div_le_iff₀ hρ]
    have : L + 2 * e ≤ L + 2 * K * ρ := by linarith
    have h2 : L / ρ * ρ = L := div_mul_cancel₀ L hρ.ne'
    nlinarith
  have hd1 : d ≤ 1 := by linarith
  have hpowd : ((L + 2 * e) / ρ) ^ d ≤ 3 * K * (L / ρ) ^ d := by
    have h0 : 0 ≤ (L + 2 * e) / ρ := by
      have : 0 ≤ L + 2 * e := by linarith
      positivity
    calc ((L + 2 * e) / ρ) ^ d ≤ (3 * K * (L / ρ)) ^ d := Real.rpow_le_rpow h0 hratio hd
      _ = (3 * K) ^ d * (L / ρ) ^ d := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ 3 * K * (L / ρ) ^ d := by
          gcongr
          calc (3 * K) ^ d ≤ (3 * K) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) hd1
            _ = 3 * K := Real.rpow_one _
  have hchain : (L / ρ) ^ (1 - ε) ≤ 3 * K ^ 2 * (K + 2) * (L / ρ) ^ d := by
    calc (L / ρ) ^ (1 - ε) ≤ (m₀ : ℝ) * ((⌈K⌉₊ : ℝ) + 1) := hbig
      _ ≤ K * ((L + 2 * e) / ρ) ^ d * (K + 2) := by
          apply mul_le_mul hm₀ hM (by positivity) (by positivity)
      _ ≤ K * (3 * K * (L / ρ) ^ d) * (K + 2) := by gcongr
      _ = 3 * K ^ 2 * (K + 2) * (L / ρ) ^ d := by ring
  have hsplit : (L / ρ) ^ (1 - ε) = (L / ρ) ^ (1 - ε - d) * (L / ρ) ^ d := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  rw [hsplit] at hchain
  have hdpos : 0 < (L / ρ) ^ d := Real.rpow_pos_of_pos (by linarith) d
  have h1 : (L / ρ) ^ (1 - ε - d) ≤ 3 * K ^ 2 * (K + 2) := le_of_mul_le_mul_right hchain hdpos
  have h2 : δ ^ (-η * (1 - ε - d)) ≤ (L / ρ) ^ (1 - ε - d) := by
    rw [Real.rpow_mul hδ.le]
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    rw [le_div_iff₀ hρ]; exact hρL
  linarith

theorem inner_pt (u w : ℝ) (e : E2) : inner ℝ (pt u w) e = u * e 0 + w * e 1 := by
  simp [pt, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]; ring

theorem norm_one_E2 {e : E2} (h : ‖e‖ = 1) : e 0 ^ 2 + e 1 ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq] at h
  simpa [Fin.sum_univ_two] using h

/-- A point in the `δ`-thickening of the line `⟪a, e⟫ = c` (with `‖e‖ = 1`) has
`|⟪a, e⟫ - c| < δ`. -/
theorem abs_inner_sub_lt_of_mem_thickening {e a : E2} {c δ : ℝ} (he : ‖e‖ = 1)
    (ha : a ∈ thickening δ {b : E2 | inner ℝ b e = c}) : |inner ℝ a e - c| < δ := by
  obtain ⟨b, hb, hab⟩ := mem_thickening_iff.1 ha
  simp only [Set.mem_ofPred_eq] at hb
  have : inner ℝ a e - c = inner ℝ (a - b) e := by rw [inner_sub_left, hb]
  rw [this]
  calc |inner ℝ (a - b) e| ≤ ‖a - b‖ * ‖e‖ := abs_real_inner_le_norm _ _
    _ = dist a b := by rw [he, mul_one, dist_eq_norm]
    _ < δ := hab

theorem line_coeff_bounds {e0 e1 K δ D G : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ) (hD : 8 * δ ≤ D)
    (hnorm : e0 ^ 2 + e1 ^ 2 = 1) (hG : |G| ≤ K * (D + δ)) (hsum : |e0 * D + e1 * G| < 2 * δ) :
    |e0| ≤ 1 / 4 + 2 * K * |e1| ∧ 1 / (4 * K + 2) ≤ |e1| := by
  have hDpos : 0 < D := by linarith
  have h1 : |e0| * D < 2 * δ + |e1| * (K * (D + δ)) := by
    have a1 : |e0| * D = |e0 * D| := by rw [abs_mul, abs_of_pos hDpos]
    have a2 : |e1 * G| ≤ |e1| * (K * (D + δ)) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hG (abs_nonneg _)
    have a3 : |e0 * D| ≤ |e0 * D + e1 * G| + |e1 * G| := by
      have := abs_add_le (e0 * D + e1 * G) (-(e1 * G))
      rw [abs_neg, add_neg_cancel_right] at this; exact this
    linarith
  have hratio : |e0| ≤ 1 / 4 + 2 * K * |e1| := by
    have b1 : |e1| * (K * (D + δ)) ≤ 2 * K * |e1| * D := by
      have : D + δ ≤ 2 * D := by linarith
      have hk0 : 0 ≤ |e1| * K := mul_nonneg (abs_nonneg _) (by linarith)
      calc |e1| * (K * (D + δ)) = (|e1| * K) * (D + δ) := by ring
        _ ≤ (|e1| * K) * (2 * D) := mul_le_mul_of_nonneg_left this hk0
        _ = 2 * K * |e1| * D := by ring
    have b2 : 2 * δ ≤ 1 / 4 * D := by linarith
    have b3 : |e0| * D < (1 / 4 + 2 * K * |e1|) * D := by nlinarith
    exact (lt_of_mul_lt_mul_right b3 hDpos.le).le
  refine ⟨hratio, ?_⟩
  by_contra hlt
  push Not at hlt
  have h4K : 0 < 4 * K + 2 := by linarith
  have c1 : 2 * K * |e1| < 1 / 2 := by
    have : 2 * K * |e1| < 2 * K * (1 / (4 * K + 2)) := by
      apply mul_lt_mul_of_pos_left hlt; linarith
    have h5 : 2 * K * (1 / (4 * K + 2)) < 1 / 2 := by
      rw [mul_one_div, div_lt_iff₀ h4K]; linarith
    linarith
  have c2 : |e0| < 3 / 4 := by linarith
  have c3 : |e1| < 1 / 6 := by
    have : 1 / (4 * K + 2) ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have a1 : e0 ^ 2 = |e0| ^ 2 := (sq_abs _).symm
  have a2 : e1 ^ 2 = |e1| ^ 2 := (sq_abs _).symm
  have d1 : |e0| ^ 2 < 9 / 16 := by nlinarith [abs_nonneg e0]
  have d2 : |e1| ^ 2 < 1 / 36 := by nlinarith [abs_nonneg e1]
  nlinarith

theorem slope_bound {e0 e1 K : ℝ} (hK : 1 ≤ K) (h1 : |e0| ≤ 1 / 4 + 2 * K * |e1|)
    (h2 : 1 / (4 * K + 2) ≤ |e1|) : |-e0 / e1| ≤ 3 * K + 1 := by
  have h4K : 0 < 4 * K + 2 := by linarith
  have he1pos : 0 < |e1| := lt_of_lt_of_le (by positivity) h2
  rw [abs_div, abs_neg, div_le_iff₀ he1pos]
  have : (1 / 4 : ℝ) ≤ (K + 1) * |e1| := by
    have h3 : (1 / 4 : ℝ) ≤ (K + 1) * (1 / (4 * K + 2)) := by
      rw [mul_one_div, le_div_iff₀ h4K]; linarith
    exact h3.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
  nlinarith

/-- **From the line alternative to an affine fit.** Let `F` be the graph over `T ⊆ [0,1]` of
a function with `|g u - g u'| ≤ K (|u - u'| + δ)`. If `F` lies near a line in the sense of the
planar input, then on at least `δ^(ε-1)/((4K+5)(8K+9))` time bins of width `δ` some point of
`T` satisfies `|g u - (c + σ u)| ≤ (4K+2) δ`, with `|σ| ≤ 3K + 1`. -/
theorem affine_of_nearLine {T : Set ℝ} {g : ℝ → ℝ} {K δ ε : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ)
    (hT : ∀ u ∈ T, 0 ≤ u ∧ u ≤ 1)
    (hg : ∀ u ∈ T, ∀ u' ∈ T, |g u - g u'| ≤ K * (|u - u'| + δ))
    (hsmall : 10 * ((4 * K + 5) * (8 * K + 9)) * δ ≤ δ ^ ε)
    (hNL : NearLine {a | ∃ u ∈ T, a = pt u (g u)} δ ε) :
    ∃ σ c : ℝ, |σ| ≤ 3 * K + 1 ∧ ∃ J : Finset ℕ,
      δ ^ (ε - 1) ≤ (J.card : ℝ) * ((4 * K + 5) * (8 * K + 9)) ∧
      ∀ j ∈ J, ∃ u ∈ T, ⌊u / δ⌋₊ = j ∧ |g u - (c + σ * u)| ≤ (4 * K + 2) * δ := by
  classical
  obtain ⟨e, c, he, hcov⟩ := hNL
  set line : Set E2 := {b : E2 | inner ℝ b e = c} with hline
  set F : Set E2 := {a | ∃ u ∈ T, a = pt u (g u)} with hF
  set C₀ : ℝ := (4 * K + 5) * (8 * K + 9) with hC₀
  have hC₀pos : 0 < C₀ := by rw [hC₀]; positivity
  -- the occupied near-line bins
  set J : Finset ℕ := (Finset.range (⌊1 / δ⌋₊ + 1)).filter
    (fun j => ∃ u ∈ T, ⌊u / δ⌋₊ = j ∧ pt u (g u) ∈ thickening δ line) with hJ
  -- a cover of each bin's part of the graph
  have hbin : ∀ j ∈ J, ∃ (m : ℕ) (cc : Fin m → E2), (m : ℝ) ≤ C₀ ∧
      ∀ u ∈ T, ⌊u / δ⌋₊ = j → pt u (g u) ∈ ⋃ i, closedBall (cc i) δ := by
    intro j hj
    obtain ⟨u₀, hu₀T, hu₀j, -⟩ := (Finset.mem_filter.1 hj).2
    obtain ⟨m, ⟨cc, hcc⟩, hm⟩ := graph_coveredBy (T := T) (ψ := g) (by linarith) hg hδ le_rfl
      (show δ ≤ (2 * K + 2) * δ by nlinarith) (pt u₀ (g u₀))
    refine ⟨m, cc, ?_, ?_⟩
    · calc (m : ℝ) ≤ (4 * K + 5) * (4 * ((2 * K + 2) * δ) / δ + 1) := hm
        _ = C₀ := by rw [hC₀]; field_simp; ring
    · intro u huT huj
      apply hcc
      refine ⟨⟨u, huT, rfl⟩, ?_⟩
      -- both times lie in the bin `[jδ, (j+1)δ)`
      have hu0 := (hT u huT).1
      have hu00 := (hT u₀ hu₀T).1
      have h1 := Nat.floor_le (div_nonneg hu0 hδ.le)
      have h2 := Nat.lt_floor_add_one (u / δ)
      have h3 := Nat.floor_le (div_nonneg hu00 hδ.le)
      have h4 := Nat.lt_floor_add_one (u₀ / δ)
      rw [huj] at h1 h2; rw [hu₀j] at h3 h4
      rw [le_div_iff₀ hδ] at h1 h3; rw [div_lt_iff₀ hδ] at h2 h4
      have hdu : |u - u₀| ≤ δ := by rw [abs_le]; constructor <;> nlinarith
      have hdg : |g u - g u₀| ≤ 2 * K * δ := by
        calc |g u - g u₀| ≤ K * (|u - u₀| + δ) := hg u huT u₀ hu₀T
          _ ≤ K * (δ + δ) := by gcongr
          _ = 2 * K * δ := by ring
      rw [mem_ball]
      have hle := dist_E2_le_of (x := pt u (g u)) (y := pt u₀ (g u₀)) (a := δ) (b := 2 * K * δ)
        (ρ := (2 * K + 1) * δ) (by simpa using hdu) (by simpa using hdg) (by nlinarith) (by positivity)
      linarith
  choose! mJ ccJ hmJ hccJ using hbin
  -- the near-line part is covered by the bin covers
  have hcover : thickening δ line ∩ F ⊆
      ⋃ c' ∈ J.biUnion (fun j => Finset.univ.image (ccJ j)), closedBall c' δ := by
    rintro a ⟨ha, u, huT, rfl⟩
    have hu := hT u huT
    have hjr : ⌊u / δ⌋₊ ∈ Finset.range (⌊1 / δ⌋₊ + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor (div_le_div_of_nonneg_right hu.2 hδ.le)
    have hjJ : ⌊u / δ⌋₊ ∈ J := Finset.mem_filter.2 ⟨hjr, u, huT, rfl, ha⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hccJ _ hjJ u huT rfl)
    exact mem_iUnion₂.2 ⟨ccJ _ i, Finset.mem_biUnion.2 ⟨_, hjJ, Finset.mem_image.2
      ⟨i, Finset.mem_univ _, rfl⟩⟩, hi⟩
  obtain ⟨cc, hcc⟩ := coveredBy_of_finset _ hcover
  have hcount := hcov _ cc hcc
  have hcard : ((J.biUnion (fun j => Finset.univ.image (ccJ j))).card : ℝ) ≤ J.card * C₀ := by
    calc ((J.biUnion (fun j => Finset.univ.image (ccJ j))).card : ℝ)
        ≤ ((∑ j ∈ J, (Finset.univ.image (ccJ j)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ j ∈ J, (mJ j : ℝ) := by
          push_cast
          exact Finset.sum_le_sum (fun j _ => by
            exact_mod_cast (Finset.card_image_le.trans (by simp)))
      _ ≤ ∑ _j ∈ J, C₀ := Finset.sum_le_sum (fun j hj => hmJ j hj)
      _ = J.card * C₀ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hJbig : δ ^ (ε - 1) ≤ (J.card : ℝ) * C₀ := hcount.trans hcard
  -- many bins: two near-line points far apart in time
  have hJcard : 10 ≤ (J.card : ℝ) := by
    have h1 : δ ^ (ε - 1) = δ ^ ε / δ := by
      rw [Real.rpow_sub hδ, Real.rpow_one]
    rw [h1, div_le_iff₀ hδ] at hJbig
    have h2 := le_trans hsmall hJbig
    have hpos : 0 < C₀ * δ := mul_pos hC₀pos hδ
    have h3 : 10 * (C₀ * δ) ≤ (J.card : ℝ) * (C₀ * δ) := by linarith
    exact le_of_mul_le_mul_right h3 hpos
  obtain ⟨jmin, hjmin, hjmin_le⟩ := J.exists_min_image id (Finset.card_pos.1 (by
    have : (0:ℝ) < J.card := by linarith
    exact_mod_cast this))
  obtain ⟨jmax, hjmax, hjmax_ge⟩ := J.exists_max_image id (Finset.card_pos.1 (by
    have : (0:ℝ) < J.card := by linarith
    exact_mod_cast this))
  have hspan : (J.card : ℝ) ≤ (jmax : ℝ) - jmin + 1 := by
    have hsub : J ⊆ Finset.Icc jmin jmax := fun j hj =>
      Finset.mem_Icc.2 ⟨hjmin_le j hj, hjmax_ge j hj⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    have h' : jmin ≤ jmax := hjmin_le jmax hjmax
    have : ((J.card : ℕ) : ℝ) ≤ ((jmax + 1 - jmin : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; linarith
  obtain ⟨u₁, hu₁T, hu₁j, hu₁L⟩ := (Finset.mem_filter.1 hjmin).2
  obtain ⟨u₂, hu₂T, hu₂j, hu₂L⟩ := (Finset.mem_filter.1 hjmax).2
  have hsep : 8 * δ ≤ u₂ - u₁ := by
    have h1 := Nat.lt_floor_add_one (u₁ / δ)
    have h2 := Nat.floor_le (div_nonneg (hT u₂ hu₂T).1 hδ.le)
    rw [hu₁j] at h1; rw [hu₂j] at h2
    rw [div_lt_iff₀ hδ] at h1; rw [le_div_iff₀ hδ] at h2
    have hj8 : (9:ℝ) ≤ (jmax : ℝ) - jmin := by linarith
    have : 9 * δ ≤ ((jmax : ℝ) - jmin) * δ := mul_le_mul_of_nonneg_right hj8 hδ.le
    nlinarith
  -- the line is a graph over time
  have hl1 := abs_inner_sub_lt_of_mem_thickening he hu₁L
  have hl2 := abs_inner_sub_lt_of_mem_thickening he hu₂L
  rw [inner_pt] at hl1 hl2
  have hnorm := norm_one_E2 he
  have hdg : |g u₂ - g u₁| ≤ K * ((u₂ - u₁) + δ) := by
    have := hg u₂ hu₂T u₁ hu₁T
    rwa [abs_of_pos (by linarith : 0 < u₂ - u₁)] at this
  have hsum : |e 0 * (u₂ - u₁) + e 1 * (g u₂ - g u₁)| < 2 * δ := by
    have : e 0 * (u₂ - u₁) + e 1 * (g u₂ - g u₁) =
        (u₂ * e 0 + g u₂ * e 1 - c) - (u₁ * e 0 + g u₁ * e 1 - c) := by ring
    rw [this]
    calc _ ≤ |u₂ * e 0 + g u₂ * e 1 - c| + |u₁ * e 0 + g u₁ * e 1 - c| := abs_sub _ _
      _ < δ + δ := add_lt_add hl2 hl1
      _ = 2 * δ := by ring
  obtain ⟨hratio, he1⟩ := line_coeff_bounds hK hδ hsep (norm_one_E2 he) hdg hsum
  have he1pos : 0 < |e 1| := lt_of_lt_of_le (by positivity) he1
  have he1ne : e 1 ≠ 0 := abs_pos.1 he1pos
  refine ⟨-(e 0) / e 1, c / e 1, slope_bound hK hratio he1, J, hJbig, ?_⟩
  intro j hj
  obtain ⟨u, huT, huj, huL⟩ := (Finset.mem_filter.1 hj).2
  refine ⟨u, huT, huj, ?_⟩
  have hl := abs_inner_sub_lt_of_mem_thickening he huL
  rw [inner_pt] at hl
  have : g u - (c / e 1 + -(e 0) / e 1 * u) = (u * e 0 + g u * e 1 - c) / e 1 := by
    field_simp; ring
  rw [this, abs_div, div_le_iff₀ he1pos]
  have h4 : (1:ℝ) ≤ (4 * K + 2) * |e 1| := by
    have h4K : 0 < 4 * K + 2 := by linarith
    have := mul_le_mul_of_nonneg_left he1 h4K.le
    rwa [mul_one_div_cancel h4K.ne'] at this
  have h5 : δ ≤ (4 * K + 2) * δ * |e 1| := by nlinarith
  linarith

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
