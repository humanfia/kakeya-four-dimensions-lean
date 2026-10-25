/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactWitness.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactLabels

/-!
# Bounded box constants of zoomed descendants

The transverse box constants of a descendant, read in the parent's normalized
chart, are bounded only if the descendant carries two trajectories with
separated major velocities: the two velocity strips then pin the difference of
the rows. Such witnesses exist in every retained descendant because its
residual mass exceeds what three palette bins of the scale can carry.

* `zoomBox_bound`: algebraic bound of all five zoomed constants from two
  witnesses with velocity gap `ε`;
* `exists_velocity_witnesses`: two retained incidences of a retained
  descendant with velocity gap at least `N^(-v)`.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel

noncomputable section

/-- **Algebra of the zoomed box constants.** Two trajectories lying in both the
descendant box `c` and the parent box `cQ`, with velocity gap `ε`, bound the
zoomed constants. -/
theorem zoomBox_bound {Z : Zoom} {B : Fin 2 → ℝ} {lam : ℝ} {c cQ : Fin 5 → ℝ}
    {b b' : Fin 6 → ℝ} {t q g K M₁ ε : ℝ}
    (hq : 0 < q) (hg : 0 < g) (hε : 0 < ε) (hK1 : 1 ≤ K) (hM₁ : 0 ≤ M₁)
    (hZq : Z.q = q) (hZw : Z.w = q * g) (hZ2 : Z.c₂ = cQ 2) (hZ3 : Z.c₃ = cQ 3)
    (hZ4 : Z.c₄ = cQ 4) (hZz : Z.z₀ = cQ 0 + Z.t₀ * cQ 1)
    (ht : Z.t₀ ≤ t) (ht' : t ≤ Z.t₀ + q)
    (hBle : |B 0| + |B 1| ≤ M₁) (hlam : |lam⁻¹| ≤ M₁) (hcQ1 : |cQ 1| ≤ K) (hc1 : |c 1| ≤ K)
    -- major boxes at time `t`
    (hm : |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q)
    (hmQ : |b 0 + t * b 3 - cQ 0 - t * cQ 1| ≤ K * q)
    -- transverse boxes at time `t`
    (htr : |(b 1 + t * b 4) - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g)
    (htrQ : |(b 1 + t * b 4) - cQ 2 - t * cQ 3 - cQ 4 * (b 0 + t * b 3)| ≤ K * q * g)
    -- strips for both trajectories
    (hs : |b 4 - c 3 - c 4 * b 3| ≤ K * g) (hsQ : |b 4 - cQ 3 - cQ 4 * b 3| ≤ K * g)
    (hs' : |b' 4 - c 3 - c 4 * b' 3| ≤ K * g) (hsQ' : |b' 4 - cQ 3 - cQ 4 * b' 3| ≤ K * g)
    (hb3 : |b 3| ≤ K) (hsep : ε ≤ |b 3 - b' 3|) :
    ∀ e, |Zoom.zoomBox Z B lam c e| ≤ 4 * K + M₁ * (4 * K + 12 * K ^ 2 / ε + M₁) := by
  have hK : 0 ≤ K := by linarith
  -- differences of the rows
  set Δ3 := c 3 - cQ 3
  set Δ4 := c 4 - cQ 4
  have hrow : ∀ (u4 u3 : ℝ), |u4 - c 3 - c 4 * u3| ≤ K * g → |u4 - cQ 3 - cQ 4 * u3| ≤ K * g →
      |Δ3 + Δ4 * u3| ≤ 2 * K * g := by
    intro u4 u3 h1 h2
    have : Δ3 + Δ4 * u3 = (u4 - cQ 3 - cQ 4 * u3) - (u4 - c 3 - c 4 * u3) := by ring
    rw [this]
    calc _ ≤ |u4 - cQ 3 - cQ 4 * u3| + |u4 - c 3 - c 4 * u3| := abs_sub _ _
      _ ≤ _ := by linarith
  have r1 := hrow (b 4) (b 3) hs hsQ
  have r2 := hrow (b' 4) (b' 3) hs' hsQ'
  have hΔ4 : |Δ4| ≤ 4 * K * g / ε := by
    have e : Δ4 * (b 3 - b' 3) = (Δ3 + Δ4 * b 3) - (Δ3 + Δ4 * b' 3) := by ring
    have h : |Δ4| * |b 3 - b' 3| ≤ 4 * K * g := by
      rw [← abs_mul, e]
      calc _ ≤ |Δ3 + Δ4 * b 3| + |Δ3 + Δ4 * b' 3| := abs_sub _ _
        _ ≤ _ := by linarith
    rw [le_div_iff₀ hε]
    calc |Δ4| * ε ≤ |Δ4| * |b 3 - b' 3| := mul_le_mul_of_nonneg_left hsep (abs_nonneg _)
      _ ≤ _ := h
  have hΔ3 : |Δ3| ≤ 2 * K * g + K * (4 * K * g / ε) := by
    have e : Δ3 = (Δ3 + Δ4 * b 3) - Δ4 * b 3 := by ring
    rw [e]
    calc _ ≤ |Δ3 + Δ4 * b 3| + |Δ4 * b 3| := abs_sub _ _
      _ ≤ 2 * K * g + (4 * K * g / ε) * K := by
          rw [abs_mul]; gcongr
      _ = _ := by ring
  have hgq : 0 < q * g := mul_pos hq hg
  have hl0 : 0 ≤ |lam⁻¹| := abs_nonneg _
  intro e
  fin_cases e
  · -- `c₀'`: shift of the major centre
    simp only [Zoom.zoomBox, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [hZz, hZq, abs_div, abs_of_pos hq, div_le_iff₀ hq]
    have e1 : c 0 + Z.t₀ * c 1 - (cQ 0 + Z.t₀ * cQ 1) =
        -(b 0 + t * b 3 - c 0 - t * c 1) + (b 0 + t * b 3 - cQ 0 - t * cQ 1) -
          (t - Z.t₀) * (c 1 - cQ 1) := by ring
    rw [e1]
    have h3 : |(t - Z.t₀) * (c 1 - cQ 1)| ≤ q * (2 * K) := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ t - Z.t₀ by linarith)]
      apply mul_le_mul (by linarith) _ (abs_nonneg _) hq.le
      calc |c 1 - cQ 1| ≤ |c 1| + |cQ 1| := abs_sub _ _
        _ ≤ 2 * K := by linarith
    calc _ ≤ |-(b 0 + t * b 3 - c 0 - t * c 1)| + |b 0 + t * b 3 - cQ 0 - t * cQ 1| +
          |(t - Z.t₀) * (c 1 - cQ 1)| := by
          calc _ ≤ |-(b 0 + t * b 3 - c 0 - t * c 1) + (b 0 + t * b 3 - cQ 0 - t * cQ 1)| +
                |(t - Z.t₀) * (c 1 - cQ 1)| := abs_sub _ _
            _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ K * q + K * q + q * (2 * K) := by rw [abs_neg]; linarith
      _ ≤ (4 * K + M₁ * (4 * K + 12 * K ^ 2 / ε + M₁)) * q := by
          have : 0 ≤ M₁ * (4 * K + 12 * K ^ 2 / ε + M₁) := by positivity
          nlinarith
  · simp only [Zoom.zoomBox, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    have : 0 ≤ M₁ * (4 * K + 12 * K ^ 2 / ε + M₁) := by positivity
    linarith
  · -- `c₂'`: transverse intercept
    simp only [Zoom.zoomBox, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    rw [hZ2, hZ3, hZ4, hZw]
    -- the intercept difference at the common point
    set x1 := b 0 + t * b 3
    have hpt : |(c 2 - cQ 2) + Δ3 * t + Δ4 * x1| ≤ 2 * K * q * g := by
      have e : (c 2 - cQ 2) + Δ3 * t + Δ4 * x1 =
          ((b 1 + t * b 4) - cQ 2 - t * cQ 3 - cQ 4 * x1) -
            ((b 1 + t * b 4) - c 2 - t * c 3 - c 4 * x1) := by simp only [Δ3, Δ4]; ring
      rw [e]
      calc _ ≤ |(b 1 + t * b 4) - cQ 2 - t * cQ 3 - cQ 4 * x1| +
            |(b 1 + t * b 4) - c 2 - t * c 3 - c 4 * x1| := abs_sub _ _
        _ ≤ _ := by linarith
    have hx1 : |x1 - Z.z₀| ≤ 2 * K * q := by
      rw [hZz]
      have e : x1 - (cQ 0 + Z.t₀ * cQ 1) = (b 0 + t * b 3 - cQ 0 - t * cQ 1) + (t - Z.t₀) * cQ 1 := by
        simp only [x1]; ring
      rw [e]
      calc _ ≤ |b 0 + t * b 3 - cQ 0 - t * cQ 1| + |(t - Z.t₀) * cQ 1| := abs_add_le _ _
        _ ≤ K * q + q * K := by
            rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ t - Z.t₀ by linarith)]
            gcongr
            linarith
        _ = 2 * K * q := by ring
    have e2 : (c 2 - cQ 2) + (c 3 - cQ 3) * Z.t₀ + (c 4 - cQ 4) * Z.z₀ =
        ((c 2 - cQ 2) + Δ3 * t + Δ4 * x1) - Δ3 * (t - Z.t₀) - Δ4 * (x1 - Z.z₀) := by
      simp only [Δ3, Δ4]; ring
    have hnum : |(c 2 - cQ 2) + (c 3 - cQ 3) * Z.t₀ + (c 4 - cQ 4) * Z.z₀| ≤
        q * g * (4 * K + 12 * K ^ 2 / ε) := by
      rw [e2]
      have h1 : |Δ3 * (t - Z.t₀)| ≤ (2 * K * g + K * (4 * K * g / ε)) * q := by
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ t - Z.t₀ by linarith)]
        exact mul_le_mul hΔ3 (by linarith) (by linarith) (by positivity)
      have h2 : |Δ4 * (x1 - Z.z₀)| ≤ (4 * K * g / ε) * (2 * K * q) := by
        rw [abs_mul]; exact mul_le_mul hΔ4 hx1 (abs_nonneg _) (by positivity)
      calc _ ≤ |(c 2 - cQ 2) + Δ3 * t + Δ4 * x1| + |Δ3 * (t - Z.t₀)| + |Δ4 * (x1 - Z.z₀)| := by
            calc _ ≤ |(c 2 - cQ 2) + Δ3 * t + Δ4 * x1 - Δ3 * (t - Z.t₀)| +
                  |Δ4 * (x1 - Z.z₀)| := abs_sub _ _
              _ ≤ _ := by gcongr; exact abs_sub _ _
        _ ≤ 2 * K * q * g + (2 * K * g + K * (4 * K * g / ε)) * q +
              (4 * K * g / ε) * (2 * K * q) := by linarith
        _ = q * g * (4 * K + 12 * K ^ 2 / ε) := by field_simp; ring
    rw [div_eq_mul_inv, abs_mul, mul_inv, abs_mul, abs_inv, abs_of_pos hgq]
    calc |(c 2 - cQ 2) + (c 3 - cQ 3) * Z.t₀ + (c 4 - cQ 4) * Z.z₀| * ((q * g)⁻¹ * |lam⁻¹|)
        ≤ q * g * (4 * K + 12 * K ^ 2 / ε) * ((q * g)⁻¹ * M₁) := by
          gcongr
      _ = M₁ * (4 * K + 12 * K ^ 2 / ε) := by field_simp
      _ ≤ _ := by
          have h0 : 0 ≤ M₁ * M₁ := by positivity
          have e : M₁ * (4 * K + 12 * K ^ 2 / ε + M₁) =
              M₁ * (4 * K + 12 * K ^ 2 / ε) + M₁ * M₁ := by ring
          linarith
  · -- `c₃'`
    simp only [Zoom.zoomBox, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    have hwq : Z.w / Z.q = g := by rw [hZw, hZq]; field_simp
    rw [hwq, hZ3, div_eq_mul_inv, abs_mul]
    have hB0 : |B 0| ≤ M₁ := by linarith [abs_nonneg (B 1)]
    calc |(c 3 - cQ 3) / g - B 0| * |lam⁻¹| ≤ (|Δ3| / g + M₁) * M₁ := by
          gcongr
          calc |(c 3 - cQ 3) / g - B 0| ≤ |(c 3 - cQ 3) / g| + |B 0| := abs_sub _ _
            _ ≤ _ := by rw [abs_div, abs_of_pos hg]; linarith
      _ ≤ (2 * K + 4 * K ^ 2 / ε + M₁) * M₁ := by
          gcongr
          rw [div_le_iff₀ hg]
          calc |Δ3| ≤ 2 * K * g + K * (4 * K * g / ε) := hΔ3
            _ = (2 * K + 4 * K ^ 2 / ε) * g := by field_simp
      _ ≤ _ := by
          have h1 : 0 ≤ 4 * K := by linarith
          have h2 : 4 * K ^ 2 / ε ≤ 12 * K ^ 2 / ε :=
            div_le_div_of_nonneg_right (by have := sq_nonneg K; linarith) hε.le
          have h3 : 2 * K ≤ 4 * K := by linarith
          have h4 : (2 * K + 4 * K ^ 2 / ε + M₁) * M₁ ≤ (4 * K + 12 * K ^ 2 / ε + M₁) * M₁ :=
            mul_le_mul_of_nonneg_right (by linarith) hM₁
          have e : M₁ * (4 * K + 12 * K ^ 2 / ε + M₁) = (4 * K + 12 * K ^ 2 / ε + M₁) * M₁ := by
            ring
          linarith
  · -- `c₄'`
    simp only [Zoom.zoomBox, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    have hwq : Z.w / Z.q = g := by rw [hZw, hZq]; field_simp
    rw [hwq, hZ4, div_eq_mul_inv, abs_mul]
    have hB1 : |B 1| ≤ M₁ := by linarith [abs_nonneg (B 0)]
    calc |(c 4 - cQ 4) / g - B 1| * |lam⁻¹| ≤ (|Δ4| / g + M₁) * M₁ := by
          gcongr
          calc |(c 4 - cQ 4) / g - B 1| ≤ |(c 4 - cQ 4) / g| + |B 1| := abs_sub _ _
            _ ≤ _ := by rw [abs_div, abs_of_pos hg]; linarith
      _ ≤ (4 * K / ε + M₁) * M₁ := by
          apply mul_le_mul_of_nonneg_right _ hM₁
          have : |Δ4| / g ≤ 4 * K / ε := by
            rw [div_le_iff₀ hg]
            calc |Δ4| ≤ 4 * K * g / ε := hΔ4
              _ = 4 * K / ε * g := by ring
          linarith
      _ ≤ _ := by
          have hKK : 4 * K ≤ 12 * K ^ 2 := by
            have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 3 * K by linarith)
              (show (0 : ℝ) ≤ 4 * K by linarith)
            calc 4 * K = 4 * K * 1 := by ring
              _ ≤ 4 * K * (3 * K) := h
              _ = 12 * K ^ 2 := by ring
          have h2 : 4 * K / ε ≤ 12 * K ^ 2 / ε := div_le_div_of_nonneg_right hKK hε.le
          have h3 : 0 ≤ 4 * K := by linarith
          have h4 : (4 * K / ε + M₁) * M₁ ≤ (4 * K + 12 * K ^ 2 / ε + M₁) * M₁ :=
            mul_le_mul_of_nonneg_right (by linarith) hM₁
          have e : M₁ * (4 * K + 12 * K ^ 2 / ε + M₁) = (4 * K + 12 * K ^ 2 / ε + M₁) * M₁ := by
            ring
          linarith

theorem sep_of_floor_gap {x y ε : ℝ} (hε : 0 < ε) (h : 2 ≤ |⌊x / ε⌋ - ⌊y / ε⌋|) :
    ε ≤ |x - y| := by
  have hx1 := Int.floor_le (x / ε)
  have hx2 := Int.lt_floor_add_one (x / ε)
  have hy1 := Int.floor_le (y / ε)
  have hy2 := Int.lt_floor_add_one (y / ε)
  rcases le_abs'.mp h with h' | h'
  · -- `⌊x/ε⌋ ≤ ⌊y/ε⌋ - 2`
    have hc : ((⌊x / ε⌋ : ℤ) : ℝ) ≤ (⌊y / ε⌋ : ℝ) - 2 := by
      have : ⌊x / ε⌋ ≤ ⌊y / ε⌋ - 2 := by omega
      exact_mod_cast this
    have : x / ε + 1 ≤ y / ε := by linarith
    rw [abs_sub_comm, le_abs]
    left
    have e : (y - x) / ε ≥ 1 := by rw [sub_div]; linarith
    rwa [ge_iff_le, le_div_iff₀ hε, one_mul] at e
  · have hc : (⌊y / ε⌋ : ℝ) + 2 ≤ ((⌊x / ε⌋ : ℤ) : ℝ) := by
      have : ⌊y / ε⌋ + 2 ≤ ⌊x / ε⌋ := by omega
      exact_mod_cast this
    have : y / ε + 1 ≤ x / ε := by linarith
    rw [le_abs]
    left
    have e : (x - y) / ε ≥ 1 := by rw [sub_div]; linarith
    rwa [ge_iff_le, le_div_iff₀ hε, one_mul] at e

namespace ZoomInput

variable {α : Type} [MeasurableSpace α]
variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- **Velocity witnesses.** A retained descendant carries two trajectories of its
assignment, with bounded major velocity, whose major velocities differ by at
least the palette scale `N^(-v)`, as soon as three palette bins cannot carry its
residual floor. -/
theorem exists_velocity_witnesses (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hnest : ∀ j j' : Fin I.M, j < j' → ∀ i : Fin (a.n I.k (I.depth j')),
      ∃ h : Fin (a.n I.k (I.depth j)),
        a.A I.k (I.depth j') i ⊆ a.A I.k (I.depth j) h ∧
          a.block I.k (I.depth j') i ⊆ a.block I.k (I.depth j) h)
    (hθ : 0 ≤ I.θ) {j : Fin I.M} (x : I.Ret j) {v : ℝ} (hv1 : R⁻¹ ≤ v) (hv2 : v ≤ R)
    (hpi : ∀ m : ℤ, a.pi I.k {w | ⌊w / p.N I.k ^ (-v)⌋ = m} ≤
      ENNReal.ofReal (p.K I.k * p.N I.k ^ (-p.S * v)))
    (hgap : 3 * (p.K I.k * (p.K I.k * p.N I.k ^ (-p.S * v))) <
      I.θ * (1 / 4 : ℝ) ^ (j : ℕ) / 2) :
    ∃ l l' : α, l ∈ a.B I.k (I.depth j) x.1.1 ∧ l' ∈ a.B I.k (I.depth j) x.1.1 ∧
      |a.b I.k l 3| ≤ p.K I.k ∧ |a.b I.k l' 3| ≤ p.K I.k ∧
      p.N I.k ^ (-v) ≤ |a.b I.k l 3 - a.b I.k l' 3| := by
  classical
  have := hcommon.prob I.k
  set ε := p.N I.k ^ (-v) with hεdef
  have hε : 0 < ε := Real.rpow_pos_of_pos (by linarith [hp.1 I.k]) _
  have hK : 0 ≤ p.K I.k := le_trans zero_le_one (hp.2.2.1.1 I.k)
  have hqs := q_pos a I.k (I.depth j)
  set Xb := towerBox (⟨j, x.1⟩ : I.Label)
  -- the residual floor
  have hfl := tower_retained_floor (μ := a.mu I.k) (G := I.G) (lv := I.lv) (X := I.box)
    (w := I.wt) (anc := I.anc) (M := I.M) hθ (fun y => y.1.2)
    (fun y j' hj' => tower_desc_budget (fun jj => hats jj) y j' hj')
    (tower_generic (hcommon.dom I.k) (fun jj => hats jj) hnest I.G) x.2
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
  -- bounded velocities almost everywhere
  have hbnd : ∀ᵐ z ∂a.mu I.k, |a.b I.k z.1 3| ≤ p.K I.k := by
    have hν := (hcommon I.k).2.2.2.2.2.2.2.2.1
    apply ae_mono (hcommon.dom I.k)
    apply Measure.ae_smul_measure
    have hν' : ∀ᵐ l ∂a.nu I.k, |a.b I.k l 3| ≤ p.K I.k := by
      filter_upwards [hν] with l hl
      linarith [abs_nonneg (a.b I.k l 0), abs_nonneg (a.b I.k l 1), abs_nonneg (a.b I.k l 4)]
    exact (Measure.quasiMeasurePreserving_fst (μ := a.nu I.k)
      (ν := (volume : Measure ℝ))).ae hν'
  set E := I.keep ∩ Xb ∩ {z | |a.b I.k z.1 3| ≤ p.K I.k}
  have hEmass : a.mu I.k (I.keep ∩ Xb) ≤ a.mu I.k E := by
    apply measure_mono_ae
    filter_upwards [hbnd] with z hz hzE
    exact ⟨hzE, hz⟩
  have hνx : a.nu I.k (a.A I.k (I.depth j) x.1.1) ≠ 0 := (hats j).prior_pos hp _
  have hνxt : a.nu I.k (a.A I.k (I.depth j) x.1.1) ≠ ⊤ := measure_ne_top _ _
  set c := 3 * (p.K I.k * (p.K I.k * p.N I.k ^ (-p.S * v))) with hcdef
  set F := I.θ * (1 / 4 : ℝ) ^ (j : ℕ) / 2 with hFdef
  set X := ENNReal.ofReal (a.q I.k (I.depth j)) * a.nu I.k (a.A I.k (I.depth j) x.1.1)
  have hc0 : 0 ≤ c := by
    have : 0 ≤ p.N I.k ^ (-p.S * v) := Real.rpow_nonneg (by linarith [hp.1 I.k]) _
    positivity
  have hF0 : 0 < F := lt_of_le_of_lt hc0 hgap
  have hX0 : X ≠ 0 := mul_ne_zero (by simp [hqs]) hνx
  have hXt : X ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνxt
  have hfl' : ENNReal.ofReal F * X ≤ a.mu I.k (I.keep ∩ Xb) := hfl
  have hEpos : 0 < a.mu I.k E := by
    refine lt_of_lt_of_le ?_ (hfl'.trans hEmass)
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hF0).ne' hX0
  obtain ⟨z₀, hz₀⟩ := nonempty_of_measure_ne_zero hEpos.ne'
  obtain ⟨⟨_, hz₀B, _⟩, hz₀b⟩ := hz₀
  set m₀ := ⌊a.b I.k z₀.1 3 / ε⌋
  by_contra hcon
  push Not at hcon
  -- every retained incidence lies in the three bins around `m₀`
  have hsub : E ⊆ ⋃ m ∈ ({m₀ - 1, m₀, m₀ + 1} : Finset ℤ),
      {z | z.1 ∈ a.B I.k (I.depth j) x.1.1 ∧ z.2 ∈ a.block I.k (I.depth j) x.1.1 ∧
        ⌊a.b I.k z.1 3 / ε⌋ = m} := by
    rintro z ⟨⟨_, hzB, hzI⟩, hzb⟩
    have hclose : |⌊a.b I.k z.1 3 / ε⌋ - m₀| < 2 := by
      by_contra h
      push Not at h
      have := sep_of_floor_gap hε h
      exact absurd (hcon z.1 z₀.1 hzB hz₀B hzb hz₀b) (not_lt.mpr this)
    simp only [mem_iUnion, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨⌊a.b I.k z.1 3 / ε⌋, ?_, hzB, hzI, rfl⟩
    rw [abs_lt] at hclose
    omega
  have hup : a.mu I.k E ≤ ENNReal.ofReal c * X := by
    calc a.mu I.k E ≤ ∑ m ∈ ({m₀ - 1, m₀, m₀ + 1} : Finset ℤ),
          a.mu I.k {z | z.1 ∈ a.B I.k (I.depth j) x.1.1 ∧ z.2 ∈ a.block I.k (I.depth j) x.1.1 ∧
            ⌊a.b I.k z.1 3 / ε⌋ = m} :=
          (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _m ∈ ({m₀ - 1, m₀, m₀ + 1} : Finset ℤ),
          ENNReal.ofReal (p.K I.k * a.q I.k (I.depth j)) * a.nu I.k (a.A I.k (I.depth j) x.1.1) *
            ENNReal.ofReal (p.K I.k * p.N I.k ^ (-p.S * v)) := by
          apply Finset.sum_le_sum
          intro m _
          refine ((hats j).2.2.2.2.2.2 x.1.1 v m hv1 hv2).trans ?_
          gcongr
          exact hpi m
      _ ≤ 3 * (ENNReal.ofReal (p.K I.k * a.q I.k (I.depth j)) *
            a.nu I.k (a.A I.k (I.depth j) x.1.1) *
            ENNReal.ofReal (p.K I.k * p.N I.k ^ (-p.S * v))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          have : ({m₀ - 1, m₀, m₀ + 1} : Finset ℤ).card ≤ 3 := Finset.card_le_three
          exact_mod_cast this
      _ = ENNReal.ofReal c * X := by
          simp only [hcdef, X]
          have hN0 : 0 ≤ p.N I.k ^ (-p.S * v) := Real.rpow_nonneg (by linarith [hp.1 I.k]) _
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3), ENNReal.ofReal_mul hK,
            ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hK, ENNReal.ofReal_ofNat]
          ring_nf
          have hN0' : 0 ≤ p.N I.k ^ (-(p.S * v)) := Real.rpow_nonneg (by linarith [hp.1 I.k]) _
          rw [ENNReal.ofReal_mul hN0']
          ring
  have hle : ENNReal.ofReal F * X ≤ ENNReal.ofReal c * X := (hfl'.trans hEmass).trans hup
  have hle' : ENNReal.ofReal F ≤ ENNReal.ofReal c := (ENNReal.mul_le_mul_iff_left hX0 hXt).mp hle
  have := (ENNReal.ofReal_le_ofReal_iff hc0).mp hle'
  linarith

end ZoomInput

end

end Submission.Obl.k4_row_parent_contact_candidates
