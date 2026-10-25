import Submission.Obl.k4_scalar_pair_atlas_assembly.Dyadic
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds

/-!
# Geometry of the source-frame coefficient bins

Elementary estimates for the known-atlas assembly:

* three-node and tensor nine-node bounds for quadratics;
* floor codes of a predictor at the nine nodes of a static `q₁`-box (frame);
* same code ⇒ the two predictors are close on the whole static strip;
* whole-box agreement of two predictors ⇒ neighbouring codes;
* whole-block extrapolation of an old fine-block fit and of the old spatial strip.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_pair_atlas_assembly

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
  (IsQuad2 isQuad2_eval quad_three_point_bound)

noncomputable section

/-! ## Quadratics in one and two variables -/

/-- Symmetric three-node bound for a quadratic in one variable. -/
lemma quad_sym_bound {a b c s₀ h M : ℝ} (hh : 0 < h)
    (h₁ : |a + b * (s₀ - h) + c * (s₀ - h) ^ 2| ≤ M)
    (h₂ : |a + b * s₀ + c * s₀ ^ 2| ≤ M)
    (h₃ : |a + b * (s₀ + h) + c * (s₀ + h) ^ 2| ≤ M) (s : ℝ) :
    |a + b * s + c * s ^ 2| ≤ 3 * M * (3 + |s - s₀| / h) ^ 2 := by
  have key := quad_three_point_bound hh (by linarith) (by linarith) h₁ h₂ h₃ s
  refine key.trans ?_
  have hM : 0 ≤ M := (abs_nonneg _).trans h₂
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (div_nonneg (by have := abs_nonneg (s - (s₀ - h)); linarith) hh.le)
  have habs : |s - (s₀ - h)| ≤ |s - s₀| + h := by
    calc |s - (s₀ - h)| = |(s - s₀) + h| := by ring_nf
      _ ≤ |s - s₀| + |h| := abs_add_le _ _
      _ = |s - s₀| + h := by rw [abs_of_pos hh]
  rw [div_le_iff₀ hh, add_mul, div_mul_cancel₀ _ hh.ne']
  linarith

/-- A linear function bounded at two points grows at most linearly away from them. -/
lemma linear_two_point_bound {a b s₁ q M : ℝ} (hq : 0 < q)
    (h₁ : |a + b * s₁| ≤ M) (h₂ : |a + b * (s₁ + q)| ≤ M) (s : ℝ) :
    |a + b * s| ≤ M * (1 + 2 * |s - s₁| / q) := by
  have hb : |b| * q ≤ 2 * M := by
    have : b * q = (a + b * (s₁ + q)) - (a + b * s₁) := by ring
    calc |b| * q = |b * q| := by rw [abs_mul, abs_of_pos hq]
      _ = |(a + b * (s₁ + q)) - (a + b * s₁)| := by rw [this]
      _ ≤ |a + b * (s₁ + q)| + |a + b * s₁| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hsplit : a + b * s = (a + b * s₁) + b * (s - s₁) := by ring
  have hM : 0 ≤ M := (abs_nonneg _).trans h₁
  rw [hsplit]
  calc |(a + b * s₁) + b * (s - s₁)| ≤ |a + b * s₁| + |b| * |s - s₁| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ M + 2 * M * |s - s₁| / q := by
        have : |b| * |s - s₁| ≤ 2 * M * |s - s₁| / q := by
          rw [le_div_iff₀ hq]
          calc |b| * |s - s₁| * q = (|b| * q) * |s - s₁| := by ring
            _ ≤ 2 * M * |s - s₁| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        linarith
    _ = M * (1 + 2 * |s - s₁| / q) := by ring

/-- The real number `(m : ℕ) - 1` for a node index `m : Fin 3`. -/
abbrev off (m : Fin 3) : ℝ := ((m : ℕ) : ℝ) - 1

lemma off_zero : off 0 = -1 := by simp [off]
lemma off_one : off 1 = 0 := by simp [off]
lemma off_two : off 2 = 1 := by norm_num [off]

lemma abs_off_le (m : Fin 3) : |off m| ≤ 1 := by
  fin_cases m <;> norm_num [off]

/-- Tensor three-by-three node bound for a quadratic of total degree at most two. -/
lemma tensor_nine_bound {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) {t₀ ht y₀ hy M : ℝ}
    (hht : 0 < ht) (hhy : 0 < hy)
    (hnode : ∀ m m' : Fin 3, |f (t₀ + off m * ht) (y₀ + off m' * hy)| ≤ M)
    (t z : ℝ) :
    |f t z| ≤ 9 * M * (3 + |t - t₀| / ht) ^ 2 * (3 + |z - y₀| / hy) ^ 2 := by
  obtain ⟨c, hc⟩ := hf
  have hrow : ∀ m : Fin 3,
      |f (t₀ + off m * ht) z| ≤ 3 * M * (3 + |z - y₀| / hy) ^ 2 := by
    intro m
    set τ := t₀ + off m * ht with hτ
    have e : ∀ w, f τ w = (c 0 + c 1 * τ + c 3 * τ ^ 2) + (c 2 + c 4 * τ) * w + c 5 * w ^ 2 := by
      intro w; rw [hc]; ring
    have n0 := hnode m 0
    have n1 := hnode m 1
    have n2 := hnode m 2
    rw [off_zero, e] at n0
    rw [off_one, e] at n1
    rw [off_two, e] at n2
    rw [e]
    refine quad_sym_bound hhy ?_ ?_ ?_ z
    · convert n0 using 2; ring
    · convert n1 using 2; ring
    · convert n2 using 2; ring
  set M' := 3 * M * (3 + |z - y₀| / hy) ^ 2 with hM'
  have e : ∀ s, f s z = (c 0 + c 2 * z + c 5 * z ^ 2) + (c 1 + c 4 * z) * s + c 3 * s ^ 2 := by
    intro s; rw [hc]; ring
  have r0 := hrow 0
  have r1 := hrow 1
  have r2 := hrow 2
  rw [off_zero, e] at r0
  rw [off_one, e] at r1
  rw [off_two, e] at r2
  rw [e]
  have r0' : |(c 0 + c 2 * z + c 5 * z ^ 2) + (c 1 + c 4 * z) * (t₀ - ht) +
      c 3 * (t₀ - ht) ^ 2| ≤ M' := by convert r0 using 2; ring
  have r1' : |(c 0 + c 2 * z + c 5 * z ^ 2) + (c 1 + c 4 * z) * t₀ +
      c 3 * t₀ ^ 2| ≤ M' := by convert r1 using 2; ring
  have r2' : |(c 0 + c 2 * z + c 5 * z ^ 2) + (c 1 + c 4 * z) * (t₀ + ht) +
      c 3 * (t₀ + ht) ^ 2| ≤ M' := by convert r2 using 2; ring
  have := quad_sym_bound hht r0' r1' r2' t
  calc _ ≤ 3 * M' * (3 + |t - t₀| / ht) ^ 2 := this
    _ = 9 * M * (3 + |t - t₀| / ht) ^ 2 * (3 + |z - y₀| / hy) ^ 2 := by rw [hM']; ring

/-! ## Floor codes -/

lemma abs_sub_lt_of_floor_div_eq {a b Δ : ℝ} (hΔ : 0 < Δ) (h : ⌊a / Δ⌋ = ⌊b / Δ⌋) :
    |a - b| < Δ := by
  have h1 := Int.floor_le (a / Δ)
  have h2 := Int.lt_floor_add_one (a / Δ)
  have h3 := Int.floor_le (b / Δ)
  have h4 := Int.lt_floor_add_one (b / Δ)
  rw [h] at h1 h2
  have hlt : |a / Δ - b / Δ| < 1 := by rw [abs_lt]; constructor <;> linarith
  rwa [← sub_div, abs_div, abs_of_pos hΔ, div_lt_one hΔ] at hlt

lemma abs_floor_div_sub_le_one {a b Δ : ℝ} (hΔ : 0 < Δ) (h : |a - b| ≤ Δ) :
    |⌊a / Δ⌋ - ⌊b / Δ⌋| ≤ 1 := by
  have h' : |a / Δ - b / Δ| ≤ 1 := by
    rwa [← sub_div, abs_div, abs_of_pos hΔ, div_le_one hΔ]
  rw [abs_le] at h'
  have h1 := Int.floor_le (a / Δ)
  have h2 := Int.lt_floor_add_one (a / Δ)
  have h3 := Int.floor_le (b / Δ)
  have h4 := Int.lt_floor_add_one (b / Δ)
  have u1 : ((⌊a / Δ⌋ - ⌊b / Δ⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
  have u2 : (-2 : ℝ) < ((⌊a / Δ⌋ - ⌊b / Δ⌋ : ℤ) : ℝ) := by push_cast; linarith
  have v1 : ⌊a / Δ⌋ - ⌊b / Δ⌋ < 2 := by exact_mod_cast u1
  have v2 : -2 < ⌊a / Δ⌋ - ⌊b / Δ⌋ := by exact_mod_cast u2
  rw [abs_le]
  constructor <;> omega

/-- Floor code of a predictor at the nine nodes `(t₀ + off m * ht, y₀ + off m' * hy)`. -/
def nodeCode (Δ t₀ ht y₀ hy : ℝ) (P : MvPolynomial (Fin 2) ℝ) (m m' : Fin 3) : ℤ :=
  ⌊MvPolynomial.eval ![t₀ + off m * ht, y₀ + off m' * hy] P / Δ⌋

/-- Equal codes: the two predictors are uniformly close on the whole plane, with tensor
quadratic growth. -/
lemma nodeCode_eq_bound {Δ t₀ ht y₀ hy : ℝ} (hΔ : 0 < Δ) (hht : 0 < ht) (hhy : 0 < hy)
    {P P' : MvPolynomial (Fin 2) ℝ} (hP : P.totalDegree ≤ 2) (hP' : P'.totalDegree ≤ 2)
    (hcode : nodeCode Δ t₀ ht y₀ hy P = nodeCode Δ t₀ ht y₀ hy P') (t z : ℝ) :
    |MvPolynomial.eval ![t, z] P - MvPolynomial.eval ![t, z] P'| ≤
      9 * Δ * (3 + |t - t₀| / ht) ^ 2 * (3 + |z - y₀| / hy) ^ 2 := by
  have hq : IsQuad2 (fun t z => MvPolynomial.eval ![t, z] P - MvPolynomial.eval ![t, z] P') := by
    obtain ⟨c, hc⟩ := isQuad2_eval P hP
    obtain ⟨c', hc'⟩ := isQuad2_eval P' hP'
    refine ⟨c - c', fun t z => ?_⟩
    have h1 := hc t z
    have h2 := hc' t z
    simp only [Pi.sub_apply] at h1 h2 ⊢
    linear_combination h1 - h2
  refine tensor_nine_bound hq hht hhy (fun m m' => ?_) t z
  have := congrFun (congrFun hcode m) m'
  exact (abs_sub_lt_of_floor_div_eq hΔ this).le

/-- Close node values give neighbouring codes. -/
lemma nodeCode_near {Δ t₀ ht y₀ hy : ℝ} (hΔ : 0 < Δ) {P P' : MvPolynomial (Fin 2) ℝ}
    (hclose : ∀ m m' : Fin 3,
      |MvPolynomial.eval ![t₀ + off m * ht, y₀ + off m' * hy] P -
        MvPolynomial.eval ![t₀ + off m * ht, y₀ + off m' * hy] P'| ≤ Δ)
    (m m' : Fin 3) :
    |nodeCode Δ t₀ ht y₀ hy P m m' - nodeCode Δ t₀ ht y₀ hy P' m m'| ≤ 1 :=
  abs_floor_div_sub_le_one hΔ (hclose m m')


/-! ## Static frames and block codes -/

/-- Frame index of a spatial center `c` at width `q`: `c ∈ [d q / 4, (d + 1) q / 4)`. -/
def frameIdx (q c : ℝ) : ℤ := ⌊4 * c / q⌋

/-- Center of the static frame `d` at width `q`. -/
def frameCenter (q : ℝ) (d : ℤ) : ℝ := (d : ℝ) * q / 4

lemma frameCenter_le {q c : ℝ} (hq : 0 < q) : frameCenter q (frameIdx q c) ≤ c := by
  unfold frameCenter frameIdx
  have h := Int.floor_le (4 * c / q)
  have : (⌊4 * c / q⌋ : ℝ) * q ≤ 4 * c := by
    calc (⌊4 * c / q⌋ : ℝ) * q ≤ 4 * c / q * q := mul_le_mul_of_nonneg_right h hq.le
      _ = 4 * c := div_mul_cancel₀ _ hq.ne'
  linarith

lemma lt_frameCenter_add {q c : ℝ} (hq : 0 < q) : c < frameCenter q (frameIdx q c) + q / 4 := by
  unfold frameCenter frameIdx
  have h := Int.lt_floor_add_one (4 * c / q)
  have : 4 * c < ((⌊4 * c / q⌋ : ℝ) + 1) * q := by
    calc 4 * c = 4 * c / q * q := (div_mul_cancel₀ _ hq.ne').symm
      _ < ((⌊4 * c / q⌋ : ℝ) + 1) * q := mul_lt_mul_of_pos_right h hq
  linarith

lemma abs_sub_frameCenter_le {q c : ℝ} (hq : 0 < q) :
    |c - frameCenter q (frameIdx q c)| ≤ q / 4 := by
  have h1 := frameCenter_le (c := c) hq
  have h2 := lt_frameCenter_add (c := c) hq
  rw [abs_le]
  constructor <;> linarith

lemma mid_eq (T : ℕ) (b : Fin (2 ^ T)) : mid T b = ((b : ℝ) + 1 / 2) * width T := by
  unfold mid width
  rw [div_eq_mul_inv]

lemma abs_sub_mid_le {T : ℕ} {b : Fin (2 ^ T)} {t : ℝ} (ht : t ∈ I T b) :
    |t - mid T b| ≤ width T / 2 := by
  rw [I_eq] at ht
  rw [mid_eq, abs_le]
  have hw := width_pos T
  constructor <;> nlinarith [ht.1, ht.2]

lemma node_mem_I (T : ℕ) (b : Fin (2 ^ T)) (m : Fin 3) :
    mid T b + off m * (width T / 2) ∈ I T b := by
  rw [I_eq, mid_eq]
  have hw := width_pos T
  fin_cases m <;> simp only [off] <;> norm_num <;> constructor <;> nlinarith

/-- Source frame of a chart with center `u + mid * v` on the coarse block `b`. -/
def srcFrame (T₁ : ℕ) (b : Fin (2 ^ T₁)) (u v : ℝ) : ℤ :=
  frameIdx (width T₁) (u + mid T₁ b * v)

/-- Code of a predictor on the static box of block `b` and frame `d`: floors of its values at
three times (block start, middle, end) and three heights (frame center and `± q₁ / 2`). -/
def blockCode (Δ : ℝ) (T₁ : ℕ) (b : Fin (2 ^ T₁)) (d : ℤ) (P : MvPolynomial (Fin 2) ℝ) :
    Fin 3 → Fin 3 → ℤ :=
  nodeCode Δ (mid T₁ b) (width T₁ / 2) (frameCenter (width T₁) d) (width T₁ / 2) P

/-- Equal block codes: the predictors are close on the whole block, with quadratic growth in the
distance to the frame center. -/
lemma blockCode_eq_bound {Δ : ℝ} (hΔ : 0 < Δ) {T₁ : ℕ} {b : Fin (2 ^ T₁)} {d : ℤ}
    {P P' : MvPolynomial (Fin 2) ℝ} (hP : P.totalDegree ≤ 2) (hP' : P'.totalDegree ≤ 2)
    (hcode : blockCode Δ T₁ b d P = blockCode Δ T₁ b d P') {t : ℝ} (ht : t ∈ I T₁ b) (z : ℝ) :
    |MvPolynomial.eval ![t, z] P - MvPolynomial.eval ![t, z] P'| ≤
      144 * Δ * (3 + 2 * |z - frameCenter (width T₁) d| / width T₁) ^ 2 := by
  have hw := width_pos T₁
  have hw2 : 0 < width T₁ / 2 := by positivity
  have key := nodeCode_eq_bound hΔ hw2 hw2 hP hP' hcode t z
  refine key.trans ?_
  have h1 : |t - mid T₁ b| / (width T₁ / 2) ≤ 1 := by
    rw [div_le_one hw2]; exact abs_sub_mid_le ht
  have h2 : |z - frameCenter (width T₁) d| / (width T₁ / 2) =
      2 * |z - frameCenter (width T₁) d| / width T₁ := by
    field_simp
  rw [h2]
  have h3 : (3 + |t - mid T₁ b| / (width T₁ / 2)) ^ 2 ≤ 16 := by
    have : 0 ≤ |t - mid T₁ b| / (width T₁ / 2) := by positivity
    nlinarith
  have h4 : 0 ≤ (3 + 2 * |z - frameCenter (width T₁) d| / width T₁) ^ 2 := by positivity
  calc 9 * Δ * (3 + |t - mid T₁ b| / (width T₁ / 2)) ^ 2 *
        (3 + 2 * |z - frameCenter (width T₁) d| / width T₁) ^ 2
      ≤ 9 * Δ * 16 * (3 + 2 * |z - frameCenter (width T₁) d| / width T₁) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ h4
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 144 * Δ * (3 + 2 * |z - frameCenter (width T₁) d| / width T₁) ^ 2 := by ring

/-- Whole-box agreement of a source predictor with a witness predictor gives neighbouring codes
at the source frame. -/
lemma blockCode_near_of_agrees {p : Code} {k T₁ n : ℕ} {u v : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ} {a e : ℝ} {b : Fin (2 ^ T₁)} {i i' : Fin n}
    (hA : Agrees p k T₁ n u v P a e b i i') (hΔ : 0 < N p k ^ (-L p + a * e)) (m m' : Fin 3) :
    |blockCode (N p k ^ (-L p + a * e)) T₁ b (srcFrame T₁ b (u i) (v i)) (P i) m m' -
      blockCode (N p k ^ (-L p + a * e)) T₁ b (srcFrame T₁ b (u i) (v i)) (P i') m m'| ≤ 1 := by
  unfold blockCode
  refine nodeCode_near hΔ (fun m m' => ?_) m m'
  have hw := width_pos T₁
  have hnode := node_mem_I T₁ b m
  have hz : |frameCenter (width T₁) (srcFrame T₁ b (u i) (v i)) + off m' * (width T₁ / 2) -
      (u i + mid T₁ b * v i)| ≤ ((2 : ℝ) ^ T₁)⁻¹ := by
    have hc := abs_sub_frameCenter_le (c := u i + mid T₁ b * v i) hw
    have ho := abs_off_le m'
    unfold srcFrame
    set F := frameCenter (width T₁) (frameIdx (width T₁) (u i + mid T₁ b * v i))
    have : |off m' * (width T₁ / 2)| ≤ width T₁ / 2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < width T₁ / 2)]
      nlinarith [abs_nonneg (off m')]
    calc |F + off m' * (width T₁ / 2) - (u i + mid T₁ b * v i)|
        = |off m' * (width T₁ / 2) - ((u i + mid T₁ b * v i) - F)| := by ring_nf
      _ ≤ |off m' * (width T₁ / 2)| + |(u i + mid T₁ b * v i) - F| := abs_sub _ _
      _ ≤ width T₁ / 2 + width T₁ / 4 := add_le_add this hc
      _ ≤ ((2 : ℝ) ^ T₁)⁻¹ := by change _ ≤ width T₁; linarith
  have := hA _ hnode _ hz
  rwa [map_sub] at this

/-! ## Whole-block extrapolation of an old fine-block chart -/

lemma abs_sub_le_width_of_mem {T : ℕ} {b : Fin (2 ^ T)} {s t : ℝ} (hs : s ∈ I T b)
    (ht : t ∈ I T b) : |t - s| ≤ width T := by
  rw [I_eq] at hs ht
  rw [abs_le]
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

/-- An old fine-block strip and fit extend to the whole coarse block, with the linear loss
`3 R` for the strip and the quadratic loss `48 R ^ 2` for the fit, `R = 2 ^ (T - T₁)`. -/
lemma fine_to_coarse {T₁ T : ℕ} (hT : T₁ ≤ T) {b : Fin (2 ^ T₁)} {j : Fin (2 ^ T)}
    (hj : I T j ⊆ I T₁ b) (l : ℕ × (Fin 5 → ℝ)) (u v M₁ M₂ : ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (hfit : ∀ t ∈ I T j, |y l t - u - t * v| ≤ M₁ ∧
      |x l t - MvPolynomial.eval ![t, y l t] P| ≤ M₂) :
    ∀ t ∈ I T₁ b, |y l t - u - t * v| ≤ 3 * (2 : ℝ) ^ (T - T₁) * M₁ ∧
      |x l t - MvPolynomial.eval ![t, y l t] P| ≤ 48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * M₂ := by
  intro t ht
  have hw := width_pos T
  have hR : (1 : ℝ) ≤ (2 : ℝ) ^ (T - T₁) := one_le_pow₀ (by norm_num)
  have hsplit := width_split hT
  set w := width T with hw_def
  set R := (2 : ℝ) ^ (T - T₁) with hR_def
  set s₁ : ℝ := (j : ℝ) * w with hs₁
  have hs₁mem : s₁ ∈ I T j := mem_I_left T j
  have hs₃mem : s₁ + w ∈ I T j := by
    have := mem_I_right T j
    convert this using 1
    rw [hs₁]; ring
  have hs₂mem : s₁ + w / 2 ∈ I T j := by
    rw [I_eq]
    constructor <;> rw [hs₁] <;> nlinarith
  have hdist : |t - s₁| ≤ R * w := by
    rw [hsplit]
    exact abs_sub_le_width_of_mem (hj hs₁mem) ht
  have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans (hfit s₁ hs₁mem).1
  have hM₂ : 0 ≤ M₂ := (abs_nonneg _).trans (hfit s₁ hs₁mem).2
  constructor
  · -- the strip is affine in time
    have e : ∀ s, y l s - u - s * v = (l.2 0 - u) + (l.2 1 - v) * s := by
      intro s; simp only [y]; ring
    have h1 := (hfit s₁ hs₁mem).1
    have h3 := (hfit (s₁ + w) hs₃mem).1
    rw [e] at h1 h3 ⊢
    have key := linear_two_point_bound hw h1 h3 t
    refine key.trans ?_
    have : 2 * |t - s₁| / w ≤ 2 * R := by
      rw [div_le_iff₀ hw]; nlinarith
    nlinarith
  · -- the fit residual is quadratic in time
    obtain ⟨a₀, b₀, c₀, hline⟩ := (isQuad2_eval P hP).line 0 1 (l.2 0) (l.2 1)
    have e : ∀ s, x l s - MvPolynomial.eval ![s, y l s] P =
        (l.2 2 - a₀) + (l.2 3 - b₀) * s + (l.2 4 - c₀) * s ^ 2 := by
      intro s
      have := hline s
      simp only [zero_add, one_mul] at this
      simp only [x, y, mul_comm s (l.2 1)]
      rw [this]; ring
    have h1 := (hfit s₁ hs₁mem).2
    have h2 := (hfit (s₁ + w / 2) hs₂mem).2
    have h3 := (hfit (s₁ + w) hs₃mem).2
    rw [e] at h1 h2 h3 ⊢
    have hw2 : 0 < w / 2 := by positivity
    have key := quad_three_point_bound hw2 (le_of_eq rfl) (by linarith) h1 h2 h3 t
    refine key.trans ?_
    have hfrac : (|t - s₁| + (s₁ + w - s₁)) / (w / 2) ≤ 4 * R := by
      rw [div_le_iff₀ hw2]; nlinarith
    have hfrac0 : 0 ≤ (|t - s₁| + (s₁ + w - s₁)) / (w / 2) := by
      apply div_nonneg _ hw2.le; have := abs_nonneg (t - s₁); linarith
    have : ((|t - s₁| + (s₁ + w - s₁)) / (w / 2)) ^ 2 ≤ (4 * R) ^ 2 :=
      pow_le_pow_left₀ hfrac0 hfrac 2
    nlinarith

/-- Frame localization: a trajectory in an old strip around `u + t v` stays within the strip
loss plus `|v| q₁ / 2 + q₁ / 4` of its source frame center on the whole coarse block. -/
lemma frame_localization {T₁ : ℕ} {b : Fin (2 ^ T₁)} {t : ℝ} (ht : t ∈ I T₁ b)
    (l : ℕ × (Fin 5 → ℝ)) (u v M : ℝ) (hstrip : |y l t - u - t * v| ≤ M) :
    |y l t - frameCenter (width T₁) (srcFrame T₁ b u v)| ≤
      M + |v| * (width T₁ / 2) + width T₁ / 4 := by
  have hw := width_pos T₁
  have hc := abs_sub_frameCenter_le (c := u + mid T₁ b * v) hw
  have hm := abs_sub_mid_le ht
  unfold srcFrame
  set F := frameCenter (width T₁) (frameIdx (width T₁) (u + mid T₁ b * v))
  have hv : |v * (t - mid T₁ b)| ≤ |v| * (width T₁ / 2) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hm (abs_nonneg v)
  calc |y l t - F| = |(y l t - u - t * v) + v * (t - mid T₁ b) + ((u + mid T₁ b * v) - F)| := by
        ring_nf
    _ ≤ |y l t - u - t * v| + |v * (t - mid T₁ b)| + |(u + mid T₁ b * v) - F| :=
        abs_add_three _ _ _
    _ ≤ M + |v| * (width T₁ / 2) + width T₁ / 4 := by linarith

end

end Submission.Obl.k4_scalar_pair_atlas_assembly
