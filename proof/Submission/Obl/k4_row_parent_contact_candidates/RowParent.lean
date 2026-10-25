/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/RowParent.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.Zoom
import Submission.Obl.k4_row_parent_contact_candidates.Descendants

/-!
# Row parents

A *row parent* is the output of the narrow-interval row reduction (paper
Prop. 8.5): a true parent label `Q` at depth `r`, its zoom, and a dense set `G`
of its incidences on which the zoomed transverse velocity obeys the fitted row
equation

`|b₄' - B₀ - B₁ b₃ + λ b₀'| ≤ E`.

Dividing by `λ` gives the contact equation of the contact principle; this file
treats the cases where no division is needed. If `|λ|` times the relative
block length is smaller than the target strip width (a power-small skew, or a
strict rate gap `ℓ < κ`), every descendant of `Q` at a slightly larger depth
carries an explicit velocity strip, and the pigeonhole over descendants gives a
strip candidate of the frozen form.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Lib.K4ContactNormalization (point)

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- Left end of a dyadic block. -/
def blockStart (T : ℕ) (j : Fin (2 ^ T)) : ℝ := (j : ℝ) / (2 : ℝ) ^ T

theorem blockStart_mem (T : ℕ) (j : Fin (2 ^ T)) : blockStart T j ∈ interval T j := by
  exact ⟨le_rfl, interval_nonempty T j⟩

theorem q_pos (a : PreparedModel α) (k : ℕ) (s : ℝ) : 0 < a.q k s := by
  unfold q; positivity

theorem interval_eq (T : ℕ) (j : Fin (2 ^ T)) :
    interval T j = Icc (blockStart T j) (blockStart T j + (2 : ℝ) ^ (-(T : ℤ))) := by
  unfold interval blockStart
  congr 1
  rw [zpow_neg, zpow_natCast, add_div, div_eq_mul_inv (1 : ℝ), one_mul]

/-- The zoom of a parent label: block start and length, major centre at the
block start, the tilted transverse box, and hidden width `a_r`. -/
def parentZoom (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) : Zoom where
  t₀ := blockStart (a.T k r) (a.j k r Q)
  q := a.q k r
  z₀ := a.c k r Q 0 + blockStart (a.T k r) (a.j k r Q) * a.c k r Q 1
  c₂ := a.c k r Q 2
  c₃ := a.c k r Q 3
  c₄ := a.c k r Q 4
  w := a.q k r * narrow p k r
  h₀ := 0
  a := width p k r

theorem narrow_pos (p : Parameters) (hp : p.Valid) (k : ℕ) (s : ℝ) : 0 < narrow p k s := by
  unfold narrow
  exact Real.rpow_pos_of_pos (by linarith [hp.1 k]) _

theorem width_pos (p : Parameters) (hp : p.Valid) (k : ℕ) (s : ℝ) : 0 < width p k s := by
  unfold width
  exact Real.rpow_pos_of_pos (by linarith [hp.1 k]) _

theorem parentZoom_ok (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) : (parentZoom p a k r Q).Ok where
  q_ne := (q_pos a k r).ne'
  w_ne := (mul_pos (q_pos a k r) (narrow_pos p hp k r)).ne'
  a_ne := (width_pos p hp k r).ne'

end PreparedModel

open PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- A zoomed parent with a dense set of incidences obeying a fitted row. -/
structure RowParent (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (E M : ℝ) where
  /-- the parent label -/
  Q : Fin (a.n k r)
  /-- the constant row -/
  B : Fin 2 → ℝ
  /-- the skew coefficient -/
  lam : ℝ
  /-- incidences where the row equation holds -/
  G : Set (α × ℝ)
  measurable_G : MeasurableSet G
  G_sub : G ⊆ a.B k r Q ×ˢ a.block k r Q
  mass : ENNReal.ofReal (a.q k r / M) * a.nu k (a.A k r Q) ≤ a.rho k G
  B_le : |B 0| + |B 1| ≤ M
  lam_le : |lam| ≤ M
  row : ∀ z ∈ G,
    |(parentZoom p a k r Q).coeff (a.b k z.1) 4 - B 0 - B 1 * a.b k z.1 3 +
      lam * (parentZoom p a k r Q).coeff (a.b k z.1) 0| ≤ E

/-! ## The explicit strip of a descendant -/

/-- Row equation plus a descendant's major box give a strip in velocity space. -/
theorem descendant_strip {b : Fin 6 → ℝ} {t₀ q g z₀ c₃ c₄ B₀ B₁ lam E : ℝ}
    {ti ci₀ ci₁ Kq : ℝ} (hq : 0 < q) (hg : 0 < g)
    (hrow : |q * (b 4 - c₃ - c₄ * b 3) / (q * g) - B₀ - B₁ * b 3 +
      lam * ((b 0 + t₀ * b 3 - z₀) / q)| ≤ E)
    (hbox : |b 0 + ti * b 3 - ci₀ - ti * ci₁| ≤ Kq) :
    |b 4 - (c₃ + g * B₀ - g * lam * ((ci₀ + ti * ci₁ - z₀) / q)) -
        (c₄ + g * B₁ + g * lam * ((ti - t₀) / q)) * b 3| ≤
      g * (|lam| * (Kq / q) + E) := by
  have hqg : q * g ≠ 0 := (mul_pos hq hg).ne'
  have hv : q * (b 4 - c₃ - c₄ * b 3) / (q * g) = (b 4 - c₃ - c₄ * b 3) / g := by
    field_simp
  rw [hv] at hrow
  set δ := b 0 + ti * b 3 - ci₀ - ti * ci₁
  have key : b 4 - (c₃ + g * B₀ - g * lam * ((ci₀ + ti * ci₁ - z₀) / q)) -
        (c₄ + g * B₁ + g * lam * ((ti - t₀) / q)) * b 3 =
      g * ((b 4 - c₃ - c₄ * b 3) / g - B₀ - B₁ * b 3 + lam * ((b 0 + t₀ * b 3 - z₀) / q)) -
        g * lam * (δ / q) := by
    simp only [δ]
    field_simp
    ring
  rw [key]
  calc |g * ((b 4 - c₃ - c₄ * b 3) / g - B₀ - B₁ * b 3 + lam * ((b 0 + t₀ * b 3 - z₀) / q)) -
        g * lam * (δ / q)|
      ≤ |g * ((b 4 - c₃ - c₄ * b 3) / g - B₀ - B₁ * b 3 +
          lam * ((b 0 + t₀ * b 3 - z₀) / q))| + |g * lam * (δ / q)| := abs_sub _ _
    _ ≤ g * E + g * (|lam| * (Kq / q)) := by
        rw [abs_mul, abs_of_pos hg, abs_mul, abs_mul, abs_of_pos hg, abs_div, abs_of_pos hq]
        have h1 : g * |(b 4 - c₃ - c₄ * b 3) / g - B₀ - B₁ * b 3 +
            lam * ((b 0 + t₀ * b 3 - z₀) / q)| ≤ g * E := mul_le_mul_of_nonneg_left hrow hg.le
        have h2 : g * |lam| * (|δ| / q) ≤ g * (|lam| * (Kq / q)) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hg.le
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact div_le_div_of_nonneg_right hbox hq.le
        linarith
    _ = g * (|lam| * (Kq / q) + E) := by ring

/-! ## Accessors for one atlas level -/

namespace PreparedModel

variable {p : Parameters} {a : PreparedModel α} {R : ℝ} {k : ℕ} {s : ℝ}

theorem AtlasAt.measurable_A (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    MeasurableSet (a.A k s i) := (h.2.2.1 i).1

theorem AtlasAt.B_sub_A (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    a.B k s i ⊆ a.A k s i := (h.2.2.1 i).2.2

theorem AtlasAt.disjoint (h : a.AtlasAt p R k s) :
    ∀ i i', i ≠ i' → a.j k s i = a.j k s i' → Disjoint (a.A k s i) (a.A k s i') :=
  h.2.2.2.1

theorem AtlasAt.prior_lower (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    ENNReal.ofReal (width p k s ^ p.d * a.q k s ^ 2 * narrow p k s / p.K k) ≤
      a.nu k (a.A k s i) := (h.2.2.2.2.1 i).1

theorem AtlasAt.c_le (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) (e : Fin 5) :
    |a.c k s i e| ≤ p.K k := (h.2.2.2.2.1 i).2.2.2.1 e

theorem AtlasAt.major_box (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) {l : α}
    (hl : l ∈ a.A k s i) {t : ℝ} (ht : t ∈ a.block k s i) :
    |a.b k l 0 + t * a.b k l 3 - a.c k s i 0 - t * a.c k s i 1| ≤ p.K k * a.q k s := by
  have := (((h.2.2.2.2.1 i).2.2.2.2.2.1 l hl t ht).1)
  simpa [PreparedModel.x, point] using this

theorem AtlasAt.cover (h : a.AtlasAt p R k s) :
    ∀ᵐ z ∂a.mu k, ∃ i, z.1 ∈ a.B k s i ∧ z.2 ∈ a.block k s i := h.2.2.2.2.2.1

theorem Common.dom {a : PreparedModel α} (h : a.Common p) (k : ℕ) :
    a.mu k ≤ ENNReal.ofReal (p.K k) • (a.nu k).prod volume := (h k).2.2.2.1

theorem Common.rho_le {a : PreparedModel α} (h : a.Common p) (k : ℕ) :
    a.rho k ≤ a.mu k := (h k).2.2.2.2.1

theorem Common.prob {a : PreparedModel α} (h : a.Common p) (k : ℕ) :
    IsProbabilityMeasure (a.nu k) := (h k).2.1

theorem q_le_of_block_subset {a : PreparedModel α} {k : ℕ} {r s : ℝ}
    {Q : Fin (a.n k r)} {i : Fin (a.n k s)} (h : a.block k s i ⊆ a.block k r Q) :
    a.q k s ≤ a.q k r := by
  have h' : interval (a.T k s) (a.j k s i) ⊆ interval (a.T k r) (a.j k r Q) := h
  rw [interval_eq, interval_eq] at h'
  have hne : (Icc (blockStart (a.T k s) (a.j k s i))
      (blockStart (a.T k s) (a.j k s i) + (2 : ℝ) ^ (-(a.T k s : ℤ)))).Nonempty :=
    nonempty_Icc.mpr (by have : (0 : ℝ) < (2 : ℝ) ^ (-(a.T k s : ℤ)) := by positivity
                         linarith)
  obtain ⟨h1, h2⟩ := (Icc_subset_Icc_iff (nonempty_Icc.mp hne)).mp h'
  unfold q
  linarith

theorem blockStart_bounds {a : PreparedModel α} {k : ℕ} {r s : ℝ}
    {Q : Fin (a.n k r)} {i : Fin (a.n k s)} (h : a.block k s i ⊆ a.block k r Q) :
    blockStart (a.T k r) (a.j k r Q) ≤ blockStart (a.T k s) (a.j k s i) ∧
      blockStart (a.T k s) (a.j k s i) ≤ blockStart (a.T k r) (a.j k r Q) + a.q k r := by
  have hm : blockStart (a.T k s) (a.j k s i) ∈ a.block k r Q := h (blockStart_mem _ _)
  have : a.block k r Q = Icc (blockStart (a.T k r) (a.j k r Q))
      (blockStart (a.T k r) (a.j k r Q) + a.q k r) := interval_eq _ _
  rw [this] at hm
  exact hm

end PreparedModel

/-! ## The strip candidate of a row parent -/

/-- The strip coefficients attached to a descendant. -/
def stripCoeff (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) {E M : ℝ}
    (RP : RowParent p a k r E M) (s : ℝ) (i : Fin (a.n k s)) : Fin 2 → ℝ :=
  let Z := parentZoom p a k r RP.Q
  let g := narrow p k r
  let ti := blockStart (a.T k s) (a.j k s i)
  ![Z.c₃ + g * RP.B 0 - g * RP.lam * ((a.c k s i 0 + ti * a.c k s i 1 - Z.z₀) / Z.q),
    Z.c₄ + g * RP.B 1 + g * RP.lam * ((ti - Z.t₀) / Z.q)]

/-- On a row parent, every incidence of a descendant obeys the explicit strip. -/
theorem rowParent_strip_bound {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    {k : ℕ} {r s R E M : ℝ} (RP : RowParent p a k r E M)
    (hats : a.AtlasAt p R k s) {i : Fin (a.n k s)} {w : α × ℝ}
    (hwG : w ∈ RP.G) (hwB : w.1 ∈ a.B k s i) :
    |a.b k w.1 4 - stripCoeff p a k r RP s i 0 - stripCoeff p a k r RP s i 1 * a.b k w.1 3| ≤
      narrow p k r * (|RP.lam| * (p.K k * a.q k s / a.q k r) + E) := by
  have hq := q_pos a k r
  have hg := narrow_pos p hp k r
  have hrow := RP.row w hwG
  have hbox := hats.major_box i (hats.B_sub_A i hwB) (blockStart_mem (a.T k s) (a.j k s i))
  have := descendant_strip (b := a.b k w.1) (t₀ := (parentZoom p a k r RP.Q).t₀)
    (z₀ := (parentZoom p a k r RP.Q).z₀) (c₃ := (parentZoom p a k r RP.Q).c₃)
    (c₄ := (parentZoom p a k r RP.Q).c₄) (B₀ := RP.B 0) (B₁ := RP.B 1) (lam := RP.lam)
    hq hg (by simpa [Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff, parentZoom] using hrow) hbox
  simpa [stripCoeff, parentZoom] using this

theorem narrow_le_one (p : Parameters) (hp : p.Valid) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    narrow p k r ≤ 1 := by
  unfold narrow
  apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k])
  have := hp.2.2.2.2.2.2.2.1
  nlinarith

/-- The centre of a descendant, seen from the parent's zoom, moves by at most
three parent widths. -/
theorem descendant_centre_shift {p : Parameters} {a : PreparedModel α} {k : ℕ} {r s R : ℝ}
    (hatr : a.AtlasAt p R k r) (hats : a.AtlasAt p R k s) {Q : Fin (a.n k r)}
    {i : Fin (a.n k s)} (hdesc : a.A k s i ⊆ a.A k r Q ∧ a.block k s i ⊆ a.block k r Q)
    {l : α} (hl : l ∈ a.A k s i) :
    |a.c k s i 0 + blockStart (a.T k s) (a.j k s i) * a.c k s i 1 -
        (a.c k r Q 0 + blockStart (a.T k r) (a.j k r Q) * a.c k r Q 1)| ≤
      3 * p.K k * a.q k r := by
  set ti := blockStart (a.T k s) (a.j k s i)
  set t₀ := blockStart (a.T k r) (a.j k r Q)
  have hti : ti ∈ a.block k s i := blockStart_mem _ _
  have h1 := hats.major_box i hl hti
  have h2 := hatr.major_box Q (hdesc.1 hl) (hdesc.2 hti)
  have hqs := q_le_of_block_subset hdesc.2
  obtain ⟨hb1, hb2⟩ := blockStart_bounds hdesc.2
  have hc1 := hatr.c_le Q 1
  have hK : 0 ≤ p.K k := by
    have := abs_nonneg (a.c k r Q 1); linarith
  have hqr := q_pos a k r
  have e : a.c k s i 0 + ti * a.c k s i 1 - (a.c k r Q 0 + t₀ * a.c k r Q 1) =
      -(a.b k l 0 + ti * a.b k l 3 - a.c k s i 0 - ti * a.c k s i 1) +
        (a.b k l 0 + ti * a.b k l 3 - a.c k r Q 0 - ti * a.c k r Q 1) +
        (ti - t₀) * a.c k r Q 1 := by ring
  rw [e]
  have h3 : |(ti - t₀) * a.c k r Q 1| ≤ a.q k r * p.K k := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul (by linarith) hc1 (abs_nonneg _) hqr.le
  have h4 : p.K k * a.q k s ≤ p.K k * a.q k r := mul_le_mul_of_nonneg_left hqs hK
  calc |-(a.b k l 0 + ti * a.b k l 3 - a.c k s i 0 - ti * a.c k s i 1) +
        (a.b k l 0 + ti * a.b k l 3 - a.c k r Q 0 - ti * a.c k r Q 1) +
        (ti - t₀) * a.c k r Q 1|
      ≤ |-(a.b k l 0 + ti * a.b k l 3 - a.c k s i 0 - ti * a.c k s i 1)| +
          |a.b k l 0 + ti * a.b k l 3 - a.c k r Q 0 - ti * a.c k r Q 1| +
          |(ti - t₀) * a.c k r Q 1| := abs_add_three _ _ _
    _ ≤ p.K k * a.q k r + p.K k * a.q k r + a.q k r * p.K k := by
        rw [abs_neg]; linarith
    _ = 3 * p.K k * a.q k r := by ring

/-- The strip coefficients are bounded in terms of the box constants, the row
and the skew. -/
theorem stripCoeff_le {p : Parameters} (hp : p.Valid) {a : PreparedModel α} {k : ℕ}
    {r s R E M : ℝ} (hr : 0 ≤ r) (RP : RowParent p a k r E M)
    (hatr : a.AtlasAt p R k r) (hats : a.AtlasAt p R k s) {i : Fin (a.n k s)}
    (hdesc : a.A k s i ⊆ a.A k r RP.Q ∧ a.block k s i ⊆ a.block k r RP.Q)
    {l : α} (hl : l ∈ a.A k s i) (e : Fin 2) :
    |stripCoeff p a k r RP s i e| ≤ p.K k + M + 3 * p.K k * M := by
  have hg := narrow_pos p hp k r
  have hg1 := narrow_le_one p hp k hr
  have hq := q_pos a k r
  have hB := RP.B_le
  have hl' := RP.lam_le
  have hB0 := abs_nonneg (RP.B 0)
  have hB1 := abs_nonneg (RP.B 1)
  have hlam := abs_nonneg RP.lam
  have hK1 : 0 ≤ p.K k := le_trans (abs_nonneg _) (hatr.c_le RP.Q 0)
  have hM : 0 ≤ M := le_trans hlam hl'
  have hshift := descendant_centre_shift hatr hats hdesc hl
  obtain ⟨hb1, hb2⟩ := blockStart_bounds hdesc.2
  fin_cases e
  · simp only [stripCoeff, parentZoom, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    have hc3 := hatr.c_le RP.Q 3
    have h1 : |narrow p k r * RP.B 0| ≤ M := by
      rw [abs_mul, abs_of_pos hg]; nlinarith
    have h2 : |narrow p k r * RP.lam *
        ((a.c k s i 0 + blockStart (a.T k s) (a.j k s i) * a.c k s i 1 -
          (a.c k r RP.Q 0 + blockStart (a.T k r) (a.j k r RP.Q) * a.c k r RP.Q 1)) /
            a.q k r)| ≤ 3 * p.K k * M := by
      rw [abs_mul, abs_mul, abs_of_pos hg, abs_div, abs_of_pos hq]
      have : |a.c k s i 0 + blockStart (a.T k s) (a.j k s i) * a.c k s i 1 -
          (a.c k r RP.Q 0 + blockStart (a.T k r) (a.j k r RP.Q) * a.c k r RP.Q 1)| / a.q k r ≤
            3 * p.K k := by
        rw [div_le_iff₀ hq]; linarith
      calc narrow p k r * |RP.lam| *
            (|a.c k s i 0 + blockStart (a.T k s) (a.j k s i) * a.c k s i 1 -
              (a.c k r RP.Q 0 + blockStart (a.T k r) (a.j k r RP.Q) * a.c k r RP.Q 1)| /
                a.q k r)
          ≤ 1 * M * (3 * p.K k) := by
            apply mul_le_mul (mul_le_mul hg1 hl' hlam zero_le_one) this (by positivity)
              (by positivity)
        _ = 3 * p.K k * M := by ring
    calc _ ≤ |a.c k r RP.Q 3 + narrow p k r * RP.B 0| + |narrow p k r * RP.lam *
          ((a.c k s i 0 + blockStart (a.T k s) (a.j k s i) * a.c k s i 1 -
            (a.c k r RP.Q 0 + blockStart (a.T k r) (a.j k r RP.Q) * a.c k r RP.Q 1)) /
              a.q k r)| := abs_sub _ _
      _ ≤ (|a.c k r RP.Q 3| + |narrow p k r * RP.B 0|) + 3 * p.K k * M :=
          add_le_add (abs_add_le _ _) h2
      _ ≤ p.K k + M + 3 * p.K k * M := by linarith
  · simp only [stripCoeff, parentZoom, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    have hc4 := hatr.c_le RP.Q 4
    have h1 : |narrow p k r * RP.B 1| ≤ M := by
      rw [abs_mul, abs_of_pos hg]; nlinarith
    have h2 : |narrow p k r * RP.lam *
        ((blockStart (a.T k s) (a.j k s i) - blockStart (a.T k r) (a.j k r RP.Q)) / a.q k r)| ≤
          M := by
      rw [abs_mul, abs_mul, abs_of_pos hg, abs_div, abs_of_pos hq]
      have : |blockStart (a.T k s) (a.j k s i) - blockStart (a.T k r) (a.j k r RP.Q)| /
          a.q k r ≤ 1 := by
        rw [div_le_one hq, abs_of_nonneg (by linarith)]; linarith
      calc narrow p k r * |RP.lam| *
            (|blockStart (a.T k s) (a.j k s i) - blockStart (a.T k r) (a.j k r RP.Q)| / a.q k r)
          ≤ 1 * M * 1 := by
            apply mul_le_mul (mul_le_mul hg1 hl' hlam zero_le_one) this (by positivity)
              (by positivity)
        _ = M := by ring
    have h3 : M ≤ 3 * p.K k * M := by
      have hK1' : 1 ≤ p.K k := (hp.2.2.1).1 k
      nlinarith
    calc _ ≤ |a.c k r RP.Q 4 + narrow p k r * RP.B 1| + |narrow p k r * RP.lam *
          ((blockStart (a.T k s) (a.j k s i) - blockStart (a.T k r) (a.j k r RP.Q)) /
            a.q k r)| := abs_add_le _ _
      _ ≤ (|a.c k r RP.Q 4| + |narrow p k r * RP.B 1|) + M := add_le_add (abs_add_le _ _) h2
      _ ≤ p.K k + M + 3 * p.K k * M := by linarith

/-- **Strip candidate of a row parent.** If the skew times the relative block
length, plus the row error, fits in the target strip width, a descendant at
depth `s` carries a strip candidate of the frozen form. -/
theorem rowParent_strip_candidate {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (hcommon : a.Common p) {k : ℕ} {r s R E M v ε : ℝ} (hr : 0 ≤ r)
    (RP : RowParent p a k r E M)
    (hatr : a.AtlasAt p R k r) (hats : a.AtlasAt p R k s)
    (hnest : ∀ i : Fin (a.n k s), ∃ h : Fin (a.n k r),
      a.A k s i ⊆ a.A k r h ∧ a.block k s i ⊆ a.block k r h)
    (hM : 0 < M)
    (hwidth : narrow p k r * (|RP.lam| * (p.K k * a.q k s / a.q k r) + E) ≤
      p.N k ^ ε * p.N k ^ (-p.ell * s - v))
    (hmass : p.N k ^ (-ε) ≤ 1 / (2 * M))
    (hz : p.K k + M + 3 * p.K k * M ≤ p.N k ^ R) :
    ∃ i : Fin (a.n k s), ∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ p.N k ^ R) ∧
      ENNReal.ofReal (p.N k ^ (-ε) / (2 : ℝ) ^ a.T k s) * a.nu k (a.A k s i) ≤
        a.rho k {w | w.1 ∈ a.B k s i ∧ w.2 ∈ a.block k s i ∧
          |a.b k w.1 4 - z 0 - z 1 * a.b k w.1 3| ≤ p.N k ^ ε * p.N k ^ (-p.ell * s - v)} := by
  have := hcommon.prob k
  have hqr := q_pos a k r
  have hqs := q_pos a k s
  -- the parent prior is positive and finite
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one ((hp.2.2.1).1 k)
  have hνQ0 : 0 < a.nu k (a.A k r RP.Q) := by
    refine lt_of_lt_of_le ?_ (hatr.prior_lower RP.Q)
    apply ENNReal.ofReal_pos.mpr
    have := width_pos p hp k r
    have := narrow_pos p hp k r
    positivity
  have hνQt : a.nu k (a.A k r RP.Q) ≠ ⊤ := measure_ne_top _ _
  -- a heavy descendant
  have hGsub : RP.G ⊆ a.A k r RP.Q ×ˢ interval (a.T k r) (a.j k r RP.Q) := by
    intro w hw
    obtain ⟨h1, h2⟩ := RP.G_sub hw
    exact ⟨hatr.B_sub_A RP.Q h1, h2⟩
  have hheavy : ENNReal.ofReal (1 / (2 * M)) *
      (ENNReal.ofReal ((2 : ℝ) ^ (-(a.T k r : ℤ))) * a.nu k (a.A k r RP.Q)) < a.rho k RP.G := by
    refine lt_of_lt_of_le ?_ RP.mass
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.mul_lt_mul_left hνQ0.ne' hνQt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    change 1 / (2 * M) * a.q k r < a.q k r / M
    rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) hM]
    nlinarith
  obtain ⟨i, hi, hiheavy⟩ := exists_heavy_desc (hcommon.dom k) (hcommon.rho_le k)
    (a.A k s) (a.B k s) (a.j k s) hats.measurable_A hats.B_sub_A hats.disjoint hats.cover
    (a.A k r) (a.j k r) hatr.disjoint hnest RP.Q RP.G hGsub (ENNReal.ofReal (1 / (2 * M)))
    hheavy
  have hdesc := mem_descSet.mp hi
  -- the heavy part is nonempty, giving a witness line
  have hne : (RP.G ∩ (a.B k s i ×ˢ interval (a.T k s) (a.j k s i))).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty] at hiheavy
    exact absurd hiheavy (not_lt.mpr zero_le)
  obtain ⟨w₀, hw₀G, hw₀B, _⟩ := hne
  refine ⟨i, stripCoeff p a k r RP s i, ?_, ?_⟩
  · intro e
    exact (stripCoeff_le hp hr RP hatr hats hdesc (hats.B_sub_A i hw₀B) e).trans hz
  · -- the strip set contains the heavy part
    have hsub : RP.G ∩ (a.B k s i ×ˢ interval (a.T k s) (a.j k s i)) ⊆
        {w | w.1 ∈ a.B k s i ∧ w.2 ∈ a.block k s i ∧
          |a.b k w.1 4 - stripCoeff p a k r RP s i 0 - stripCoeff p a k r RP s i 1 * a.b k w.1 3| ≤
            p.N k ^ ε * p.N k ^ (-p.ell * s - v)} := by
      rintro w ⟨hwG, hwB, hwI⟩
      refine ⟨hwB, hwI, ?_⟩
      exact (rowParent_strip_bound hp RP hats hwG hwB).trans hwidth
    refine le_trans ?_ ((le_of_lt hiheavy).trans (measure_mono hsub))
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    gcongr
    change p.N k ^ (-ε) / (2 : ℝ) ^ a.T k s ≤ 1 / (2 * M) * a.q k s
    have : p.N k ^ (-ε) / (2 : ℝ) ^ a.T k s = p.N k ^ (-ε) * a.q k s := by
      simp only [PreparedModel.q, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [this]
    exact mul_le_mul_of_nonneg_right hmass hqs.le

end

end Submission.Obl.k4_row_parent_contact_candidates
