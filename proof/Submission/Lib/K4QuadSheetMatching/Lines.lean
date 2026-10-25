import Mathlib
import Submission.Lib.K4QuadSheetMatching.Jets
-- Adapted from: here:o078 (session x0262, branch x0262 of o078).

/-!
# Quadratic sheets along lines

One-variable quadratics and their iterated derivatives; the three line families (along
`e₁`, `e₂`, `e₁ + e₂`) with measure-preserving transverse coordinates; and, for each of the
five jet quantities, the line family and derivative order along which the jet quantity is the
difference of iterated derivatives of the restricted sheets.
-/

namespace Submission.Lib.K4QuadSheetMatching

open MeasureTheory Set

/-! ### One-variable quadratics -/

lemma hasDerivAt_quad1 (A B C s : ℝ) :
    HasDerivAt (fun s : ℝ => A + B * s + C * s ^ 2) (B + 2 * C * s) s := by
  have h1 := ((hasDerivAt_id s).const_mul B).const_add A
  have h2 := (hasDerivAt_pow 2 s).const_mul C
  convert h1.add h2 using 1
  · ext x; simp
  · simp; ring

lemma deriv_quad1 (A B C : ℝ) :
    deriv (fun s : ℝ => A + B * s + C * s ^ 2) = fun s => B + 2 * C * s :=
  funext fun s => (hasDerivAt_quad1 A B C s).deriv

lemma deriv_lin1 (B C : ℝ) : deriv (fun s : ℝ => B + 2 * C * s) = fun _ => 2 * C := by
  funext s
  have := (((hasDerivAt_id s).const_mul (2 * C)).const_add B)
  simp

lemma iteratedDeriv_quad1_one (A B C : ℝ) :
    iteratedDeriv 1 (fun s : ℝ => A + B * s + C * s ^ 2) = fun s => B + 2 * C * s := by
  rw [iteratedDeriv_one, deriv_quad1]

lemma iteratedDeriv_quad1_two (A B C : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => A + B * s + C * s ^ 2) = fun _ => 2 * C := by
  rw [iteratedDeriv_succ, iteratedDeriv_quad1_one, deriv_lin1]

lemma iteratedDeriv_quad1_add_three (A B C : ℝ) (n : ℕ) :
    iteratedDeriv (n + 3) (fun s : ℝ => A + B * s + C * s ^ 2) = fun _ => 0 := by
  induction n with
  | zero =>
    rw [iteratedDeriv_succ, iteratedDeriv_quad1_two]
    funext s; simp
  | succ n ih =>
    rw [show n + 1 + 3 = (n + 3) + 1 by ring, iteratedDeriv_succ, ih]
    funext s; simp

/-- Derivative bounds for a one-variable quadratic bounded by `M` on `[0, 1]`. -/
lemma abs_iteratedDeriv_quad1_le {A B C M : ℝ}
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, |A + B * s + C * s ^ 2| ≤ M) (j : ℕ) (hj : j ≤ 4)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    |iteratedDeriv j (fun s : ℝ => A + B * s + C * s ^ 2) s| ≤ 26 * M := by
  have h0 := hM 0 ⟨le_rfl, zero_le_one⟩
  have hh := hM (1 / 2) ⟨by norm_num, by norm_num⟩
  have h1 := hM 1 ⟨zero_le_one, le_rfl⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) h0
  have hA : |A| ≤ M := by simpa using h0
  have hC : |C| ≤ 8 * M := by
    have e : C = 2 * ((A + B * 0 + C * 0 ^ 2) - 2 * (A + B * (1 / 2) + C * (1 / 2) ^ 2) +
        (A + B * 1 + C * 1 ^ 2)) := by ring
    have a0 := abs_le.mp h0
    have a1 := abs_le.mp hh
    have a2 := abs_le.mp h1
    rw [e, abs_le]
    constructor <;> linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2]
  have hBe : B = (A + B * 1 + C * 1 ^ 2) - A - C := by ring
  have hB : |B| ≤ 10 * M := by
    rw [hBe]
    have := abs_sub (A + B * 1 + C * 1 ^ 2 - A) C
    have := abs_sub (A + B * 1 + C * 1 ^ 2) A
    linarith
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · interval_cases j
    · simp only [iteratedDeriv_zero]; linarith [hM s hs]
    · rw [iteratedDeriv_quad1_one]
      have : |2 * C * s| ≤ 16 * M := by
        rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hs.1]
        nlinarith [hs.2, abs_nonneg C]
      calc |B + 2 * C * s| ≤ |B| + |2 * C * s| := abs_add_le _ _
        _ ≤ 26 * M := by linarith
    · rw [iteratedDeriv_quad1_two]
      simp only [abs_mul, abs_two]
      linarith
  · obtain ⟨n, rfl⟩ : ∃ n, j = n + 3 := ⟨j - 3, by omega⟩
    rw [iteratedDeriv_quad1_add_three]
    simp only [abs_zero]
    linarith

/-! ### Sheets on the unit square and beyond -/

/-- The closed unit square of base coordinates. -/
def unitSq : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

/-- The region reached by lines through the unit square in the three directions. -/
def extR : Set (ℝ × ℝ) :=
  {z | (z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (-1 : ℝ) 2) ∨ (z.1 ∈ Icc (-1 : ℝ) 2 ∧ z.2 ∈ Icc (0 : ℝ) 1)}

/-- A sheet bounded by `A` on the unit square is bounded by `108 A` on `extR`. -/
lemma qev_ext_bound {c : Fin 6 → ℝ} {A : ℝ} (hA : ∀ z ∈ unitSq, |qev c z.1 z.2| ≤ A) :
    ∀ z ∈ extR, |qev c z.1 z.2| ≤ 108 * A := by
  rintro ⟨t, y⟩ hz
  have key : ∀ (a b c' : ℝ) (x : ℝ), x ∈ Icc (-1 : ℝ) 2 →
      (∀ u ∈ Icc (0 : ℝ) 1, |a + b * u + c' * u ^ 2| ≤ A) → |a + b * x + c' * x ^ 2| ≤ 108 * A := by
    intro a b c' x hx hu
    have := quad_three_point_bound (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) + 1 / 2 ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 ≤ 1 by norm_num) (hu 0 ⟨le_rfl, zero_le_one⟩)
      (hu (1 / 2) ⟨by norm_num, by norm_num⟩) (hu 1 ⟨zero_le_one, le_rfl⟩) x
    have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hu 0 ⟨le_rfl, zero_le_one⟩)
    have hx' : |x - 0| + (1 - 0) ≤ 3 := by
      have : |x| ≤ 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [sub_zero, sub_zero]; linarith
    calc |a + b * x + c' * x ^ 2| ≤ 3 * A * ((|x - 0| + (1 - 0)) / (1 / 2)) ^ 2 := this
      _ ≤ 3 * A * (3 / (1 / 2)) ^ 2 := by
          gcongr
      _ = 108 * A := by ring
  rcases hz with ⟨ht, hy⟩ | ⟨ht, hy⟩
  · have := key (c 0 + c 1 * t + c 3 * t ^ 2) (c 2 + c 4 * t) (c 5) y hy (fun u hu => by
      have := hA (t, u) ⟨ht, hu⟩
      simp only [qev] at this
      convert this using 2; ring)
    simp only [qev]
    convert this using 2; ring
  · have := key (c 0 + c 2 * y + c 5 * y ^ 2) (c 1 + c 4 * y) (c 3) t ht (fun u hu => by
      have := hA (u, y) ⟨hu, hy⟩
      simp only [qev] at this
      convert this using 2; ring)
    simp only [qev]
    convert this using 2; ring

/-! ### Line families adapted to the five jet quantities -/

/-- A line family `s ↦ P ζ s` with measure-preserving transverse coordinates `Q`, along which
the jet quantity `k` of a difference of sheets is the difference of `ord`-th derivatives of the
restricted sheets. -/
structure JetLine (k : Fin 5) where
  P : ℝ → ℝ → ℝ × ℝ
  Q : ℝ × ℝ → ℝ × ℝ
  ord : ℕ
  hQm : Measurable Q
  hPm : Measurable (fun p : ℝ × ℝ => P p.1 p.2)
  hQ : MeasurePreserving Q volume volume
  hPQ : ∀ z, P (Q z).1 (Q z).2 = z
  hrange : ∀ z ∈ unitSq, (Q z).1 ∈ Icc (-1 : ℝ) 1
  hs : ∀ ζ s, P ζ s ∈ unitSq → s ∈ Icc (0 : ℝ) 1
  hext : ∀ ζ ∈ Icc (-1 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, P ζ s ∈ extR
  hord1 : 1 ≤ ord
  hord2 : ord ≤ 2
  hform : ∀ (c : Fin 6 → ℝ) (ζ : ℝ), ∃ A B C : ℝ,
    (fun s => qev c (P ζ s).1 (P ζ s).2) = fun s => A + B * s + C * s ^ 2
  hjet : ∀ (c c' : Fin 6 → ℝ) (ζ s : ℝ),
    |iteratedDeriv ord (fun s => qev c (P ζ s).1 (P ζ s).2) s -
      iteratedDeriv ord (fun s => qev c' (P ζ s).1 (P ζ s).2) s| =
      jetq (c - c') (P ζ s).1 (P ζ s).2 k

lemma form0 (c : Fin 6 → ℝ) (ζ : ℝ) : (fun s => qev c ((s, ζ) : ℝ × ℝ).1 ((s, ζ) : ℝ × ℝ).2) =
    fun s => (c 0 + c 2 * ζ + c 5 * ζ ^ 2) + (c 1 + c 4 * ζ) * s + c 3 * s ^ 2 := by
  funext s; simp only [qev]; ring

lemma form1 (c : Fin 6 → ℝ) (ζ : ℝ) : (fun s => qev c ((ζ, s) : ℝ × ℝ).1 ((ζ, s) : ℝ × ℝ).2) =
    fun s => (c 0 + c 1 * ζ + c 3 * ζ ^ 2) + (c 2 + c 4 * ζ) * s + c 5 * s ^ 2 := by
  funext s; simp only [qev]; ring

lemma form2 (c : Fin 6 → ℝ) (ζ : ℝ) :
    (fun s => qev c ((s, s - ζ) : ℝ × ℝ).1 ((s, s - ζ) : ℝ × ℝ).2) =
    fun s => (c 0 - c 2 * ζ + c 5 * ζ ^ 2) + (c 1 + c 2 - c 4 * ζ - 2 * c 5 * ζ) * s +
      (c 3 + c 4 + c 5) * s ^ 2 := by
  funext s; simp only [qev]; ring

lemma mp_swap : MeasurePreserving (fun z : ℝ × ℝ => (z.2, z.1)) volume volume := by
  rw [Measure.volume_eq_prod]; exact Measure.measurePreserving_swap

lemma mp_shear : MeasurePreserving (fun z : ℝ × ℝ => (z.1 - z.2, z.1)) volume volume := by
  rw [Measure.volume_eq_prod]
  have h1 := measurePreserving_sub_prod (volume : Measure ℝ) (volume : Measure ℝ)
  have h2 := measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)
  have := h2.comp h1
  convert this using 1
  funext z; simp

lemma unitSq_mem {z : ℝ × ℝ} (hz : z ∈ unitSq) : z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1 := hz

/-- Line family along `e₁` with derivative order `o`. -/
def jetLineE1 (k : Fin 5) (o : ℕ) (ho1 : 1 ≤ o) (ho2 : o ≤ 2)
    (hj : ∀ (c c' : Fin 6 → ℝ) (ζ s : ℝ),
      |iteratedDeriv o (fun s => qev c ((s, ζ) : ℝ × ℝ).1 ((s, ζ) : ℝ × ℝ).2) s -
        iteratedDeriv o (fun s => qev c' ((s, ζ) : ℝ × ℝ).1 ((s, ζ) : ℝ × ℝ).2) s| =
        jetq (c - c') s ζ k) : JetLine k where
  P := fun ζ s => (s, ζ)
  Q := fun z => (z.2, z.1)
  ord := o
  hQm := by fun_prop
  hPm := by fun_prop
  hQ := mp_swap
  hPQ := fun z => rfl
  hrange := fun z hz => ⟨by linarith [hz.2.1], hz.2.2⟩
  hs := fun ζ s h => h.1
  hext := fun ζ hζ s hs => Or.inl ⟨hs, by linarith [hζ.1], by linarith [hζ.2]⟩
  hord1 := ho1
  hord2 := ho2
  hform := fun c ζ => ⟨_, _, _, form0 c ζ⟩
  hjet := hj

/-- Line family along `e₂` with derivative order `o`. -/
def jetLineE2 (k : Fin 5) (o : ℕ) (ho1 : 1 ≤ o) (ho2 : o ≤ 2)
    (hj : ∀ (c c' : Fin 6 → ℝ) (ζ s : ℝ),
      |iteratedDeriv o (fun s => qev c ((ζ, s) : ℝ × ℝ).1 ((ζ, s) : ℝ × ℝ).2) s -
        iteratedDeriv o (fun s => qev c' ((ζ, s) : ℝ × ℝ).1 ((ζ, s) : ℝ × ℝ).2) s| =
        jetq (c - c') ζ s k) : JetLine k where
  P := fun ζ s => (ζ, s)
  Q := fun z => z
  ord := o
  hQm := measurable_id
  hPm := by fun_prop
  hQ := MeasurePreserving.id _
  hPQ := fun z => rfl
  hrange := fun z hz => ⟨by linarith [hz.1.1], hz.1.2⟩
  hs := fun ζ s h => h.2
  hext := fun ζ hζ s hs => Or.inr ⟨⟨hζ.1, by linarith [hζ.2]⟩, hs⟩
  hord1 := ho1
  hord2 := ho2
  hform := fun c ζ => ⟨_, _, _, form1 c ζ⟩
  hjet := hj

/-- Line family along `e₁ + e₂` with derivative order two. -/
def jetLineDiag : JetLine 4 where
  P := fun ζ s => (s, s - ζ)
  Q := fun z => (z.1 - z.2, z.1)
  ord := 2
  hQm := by fun_prop
  hPm := by fun_prop
  hQ := mp_shear
  hPQ := fun z => by simp
  hrange := fun z hz => ⟨by linarith [hz.1.1, hz.2.2], by linarith [hz.1.2, hz.2.1]⟩
  hs := fun ζ s h => h.1
  hext := fun ζ hζ s hs => Or.inl ⟨hs, by linarith [hs.1, hζ.2], by linarith [hs.2, hζ.1]⟩
  hord1 := by norm_num
  hord2 := le_rfl
  hform := fun c ζ => ⟨_, _, _, form2 c ζ⟩
  hjet := fun c c' ζ s => by
    rw [form2, form2, iteratedDeriv_quad1_two, iteratedDeriv_quad1_two]
    simp only [jetq, qddd, Pi.sub_apply, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
    congr 1; ring

/-- The line family adapted to each jet quantity. -/
def jetLine : (k : Fin 5) → JetLine k
  | 0 => jetLineE1 0 1 le_rfl (by norm_num) (fun c c' ζ s => by
      rw [form0, form0, iteratedDeriv_quad1_one, iteratedDeriv_quad1_one]
      simp only [jetq, qdt, Pi.sub_apply, Matrix.cons_val_zero]
      congr 1; ring)
  | 1 => jetLineE2 1 1 le_rfl (by norm_num) (fun c c' ζ s => by
      rw [form1, form1, iteratedDeriv_quad1_one, iteratedDeriv_quad1_one]
      simp only [jetq, qdy, Pi.sub_apply, Matrix.cons_val_one, Matrix.head_cons]
      congr 1; ring)
  | 2 => jetLineE1 2 2 (by norm_num) le_rfl (fun c c' ζ s => by
      rw [form0, form0, iteratedDeriv_quad1_two, iteratedDeriv_quad1_two]
      simp only [jetq, qdtt, Pi.sub_apply, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      congr 1; ring)
  | 3 => jetLineE2 3 2 (by norm_num) le_rfl (fun c c' ζ s => by
      rw [form1, form1, iteratedDeriv_quad1_two, iteratedDeriv_quad1_two]
      simp only [jetq, qdyy, Pi.sub_apply, Matrix.cons_val_three, Matrix.tail_cons,
        Matrix.head_cons]
      congr 1; ring)
  | 4 => jetLineDiag

end Submission.Lib.K4QuadSheetMatching
