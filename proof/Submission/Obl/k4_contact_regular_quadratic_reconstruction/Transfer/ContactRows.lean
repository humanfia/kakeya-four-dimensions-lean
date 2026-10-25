/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c872eb1b,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/ContactRows.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the o238 one (k4_critical_switching_state_preparation). -/
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.Model
import Submission.Obl.k4_contact_time_rate_rigidity.Geometry
import Submission.Obl.k4_contact_time_rate_rigidity.Palette
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation

/-- A single contact witness controls the centered constant once the pivot
has been located using two separated velocities. -/
theorem contact_row_center_bound {b : Fin 6 → ℝ} {t c₃ c₄ z K q g e D : ℝ}
    (hb : |b 3| ≤ K) (hcontact : |b 4 + b 0| ≤ e)
    (hrow : |b 4 - c₃ - c₄ * b 3| ≤ K * g)
    (hz : |b 0 + t * b 3 - z| ≤ K * q)
    (hpivot : |t - c₄| ≤ D) :
    |c₃ + z| + |c₄ - t| ≤ e + K * g + K * q + (K + 1) * D := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hb
  have hD : 0 ≤ D := (abs_nonneg _).trans hpivot
  have hprod : |(t - c₄) * b 3| ≤ D * K := by
    rw [abs_mul]
    exact mul_le_mul hpivot hb (abs_nonneg _) hD
  have hcenter : |c₃ + z| ≤ e + K * g + K * q + D * K := by
    calc
      _ = |(b 4 + b 0) - (b 4 - c₃ - c₄ * b 3) -
          (b 0 + t * b 3 - z) + (t - c₄) * b 3| := by congr 1; ring
      _ ≤ |b 4 + b 0| + |b 4 - c₃ - c₄ * b 3| +
          |b 0 + t * b 3 - z| + |(t - c₄) * b 3| := by
        exact (abs_add_le _ _).trans
          (add_le_add ((abs_sub _ _).trans
            (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (add_le_add hcontact hrow) hz) hprod
  rw [abs_sub_comm c₄ t]
  nlinarith only [hcenter, hpivot]

/-- Equal transverse and temporal widths turn the contact witnesses into a
centered row estimate, uniformly in the original affine intercepts. -/
theorem centered_contact_row_bound {b₀ b₁ : Fin 6 → ℝ}
    {t c₃ c₄ z K q g e δ : ℝ}
    (hK : 1 ≤ K) (hq : 0 ≤ q) (hg : 0 ≤ g)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hgq : g ≤ K * q) (he : e ≤ q)
    (hb₀ : |b₀ 3| ≤ K) (hsep : δ ≤ |b₀ 3 - b₁ 3|)
    (hcontact₀ : |b₀ 4 + b₀ 0| ≤ e)
    (hcontact₁ : |b₁ 4 + b₁ 0| ≤ e)
    (hrow₀ : |b₀ 4 - c₃ - c₄ * b₀ 3| ≤ K * g)
    (hrow₁ : |b₁ 4 - c₃ - c₄ * b₁ 3| ≤ K * g)
    (hz₀ : |b₀ 0 + t * b₀ 3 - z| ≤ K * q)
    (hz₁ : |b₁ 0 + t * b₁ 3 - z| ≤ K * q) :
    |c₃ + z| + |c₄ - t| ≤ 20 * K ^ 3 * q / δ := by
  have hK₀ : 0 ≤ K := by linarith
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hKpow : K ^ 2 ≤ K ^ 3 := by nlinarith [sq_nonneg K]
  have hKg : K * g ≤ K ^ 2 * q := by
    have hh := mul_le_mul_of_nonneg_left hgq hK₀
    nlinarith only [hh]
  have hKq : K * q ≤ K ^ 2 * q := mul_le_mul_of_nonneg_right hKK hq
  have hqK : q ≤ K ^ 2 * q := le_mul_of_one_le_left hq (by nlinarith)
  have hpivot := Submission.Obl.k4_contact_time_rate_rigidity.pivot_bound
    hδ hsep hcontact₀ hcontact₁ hrow₀ hrow₁ hz₀ hz₁
  have htime := Submission.Obl.k4_contact_time_rate_rigidity.time_radius_le
    hK hg hq hδ hδ₁ hgq he
  rw [show 2 * K * g + 2 * K * q + 2 * e =
    2 * K * q + 2 * K * g + 2 * e by ring] at htime
  have hpivot' : |t - c₄| ≤ 7 * K ^ 2 * q / δ := by
    linarith only [hpivot, htime, hg]
  have hcenter := contact_row_center_bound hb₀ hcontact₀ hrow₀ hz₀ hpivot'
  have hpart : (e + K * g + K * q) * δ ≤ 3 * K ^ 3 * q := by
    have hsum : e + K * g + K * q ≤ 3 * K ^ 2 * q := by linarith
    calc
      _ ≤ (3 * K ^ 2 * q) * δ := mul_le_mul_of_nonneg_right hsum hδ.le
      _ ≤ 3 * K ^ 2 * q := mul_le_of_le_one_right (by positivity) hδ₁
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith only [hKpow]) hq
  have hlast : (K + 1) * (7 * K ^ 2 * q) ≤ 14 * K ^ 3 * q := by
    have hh := mul_le_mul_of_nonneg_right (show K + 1 ≤ 2 * K by linarith)
      (show 0 ≤ 7 * K ^ 2 * q by positivity)
    nlinarith only [hh]
  apply hcenter.trans
  apply (le_div_iff₀ hδ).mpr
  have heq : (e + K * g + K * q + (K + 1) * (7 * K ^ 2 * q / δ)) * δ =
      (e + K * g + K * q) * δ + (K + 1) * (7 * K ^ 2 * q) := by
    field_simp <;> ring
  rw [heq]
  nlinarith only [hpart, hlast, mul_nonneg (pow_nonneg hK₀ 3) hq]

/-- Original prior bounds pass to the incidence law through the stated product
domination, including when the residual law is not normalized. -/
theorem ContactProblem.ae_incidence_horizontal_bounds {α : Type}
    [MeasurableSpace α] {cfg : Data α} (h : ContactProblem cfg) (k : ℕ) :
    ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 0| + |cfg.b k p.1 1| +
      |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k := by
  obtain ⟨_, hν, _, hdom, _, _, _, _, hbnd, _⟩ := h.basic k
  letI : IsProbabilityMeasure (cfg.ν k) := hν
  exact (ae_mono hdom) (Measure.ae_smul_measure (Measure.quasiMeasurePreserving_fst.ae hbnd) _)

/-- The original false-flag atlas acquires the horizontal row centering at
every fixed positive depth range inside the contact-error margin. The bound
uses the original palette numerator and original assignment mass floor. -/
theorem ContactProblem.eventually_centered_rows {α : Type} [MeasurableSpace α]
    {cfg : Data α} (h : ContactProblem cfg) {ε R : ℝ}
    (hε : 0 < ε) (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U →
      cfg.κ * s ≤ cfg.e₀ / 2 → ∀ i : Fin (cfg.n k s),
      let q : ℝ := ((2 : ℝ) ^ cfg.T k s)⁻¹
      let m : ℝ := ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q
      |cfg.c k s i 3 + cfg.c k s i 0 + m * cfg.c k s i 1| +
        |cfg.c k s i 4 - m| ≤ cfg.N k ^ ε * q := by
  let p := h.parameters
  have hN₁ : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [p.scale k]
  let v : ℝ := ε / 2
  have hv : 0 < v := by dsimp [v]; positivity
  let R' : ℝ := 2 + R + v + v⁻¹
  have hR' : 1 < R' := by dsimp [R']; linarith [inv_pos.mpr hv]
  have hR'₀ : 0 < R' := by linarith
  have hRR' : R ≤ R' := by dsimp [R']; linarith [inv_pos.mpr hv]
  have hRRinv : R'⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by linarith : 0 < R) hRR'
  have hvR : R'⁻¹ ≤ v := by
    have hh : v⁻¹ ≤ R' := by dsimp [R']; linarith [inv_pos.mpr hv]
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hv) hh
  have hvR' : v ≤ R' := by dsimp [R']; linarith [inv_pos.mpr hv]
  have hR'₁ : R'⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hR'.le
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ p.scale_limit p.subpower.1 p.subpower.2 3
    (a := -cfg.S * v) (b := 0) (by nlinarith [p.palette_pos])
    (A := 6) (by norm_num)
  have hbudget := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ p.scale_limit p.subpower.1 p.subpower.2 3
    (a := v) (b := ε) (by dsimp [v]; linarith) (A := 20) (by norm_num)
  simp only [Real.rpow_zero] at hsmall
  filter_upwards [h.caps R' hR', h.atlas R' hR', hsmall, hbudget,
    p.subpower.2 (cfg.e₀ / 2) (by linarith [p.defect_pos])]
    with k hcapk hlabk hsmallk hbudgetk hKexp
  intro s hs hsU hse i
  have hN : 0 < cfg.N k := by linarith [p.scale k]
  have hK : 1 ≤ cfg.K k := p.subpower.1 k
  have hK₀ : 0 < cfg.K k := by linarith
  obtain ⟨hTlo, hTup, hA, _, hlabel, _, hpal⟩ :=
    hlabk s (hRRinv.trans hs) hsU
  simp only [zpow_neg, zpow_natCast] at hTlo hTup hA hlabel hpal
  let q : ℝ := ((2 : ℝ) ^ cfg.T k s)⁻¹
  let g : ℝ := cfg.N k ^ (-cfg.κ * s)
  let δ : ℝ := cfg.N k ^ (-v)
  let m : ℝ := ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q
  have hq : 0 < q := by dsimp [q]; positivity
  have htwo : 0 < (2 : ℝ) ^ cfg.T k s := by positivity
  have hg : 0 < g := Real.rpow_pos_of_pos hN _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  have hδ₁ : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN₁ k) (by linarith)
  have hgq : g ≤ cfg.K k * q := by
    change g ≤ cfg.K k / (2 : ℝ) ^ cfg.T k s
    apply (le_div_iff₀ htwo).mpr
    calc
      _ ≤ g * (cfg.K k * cfg.N k ^ (cfg.κ * s)) :=
        mul_le_mul_of_nonneg_left hTup hg.le
      _ = cfg.K k := by
        dsimp [g]
        rw [mul_left_comm, ← Real.rpow_add hN]
        rw [show -cfg.κ * s + cfg.κ * s = 0 by ring, Real.rpow_zero, mul_one]
  have he : cfg.N k ^ (-cfg.e₀) ≤ q := by
    have ht : (2 : ℝ) ^ cfg.T k s ≤ cfg.N k ^ cfg.e₀ := by
      calc
        _ ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) := hTup
        _ ≤ cfg.N k ^ (cfg.e₀ / 2) * cfg.N k ^ (cfg.e₀ / 2) := by
          exact mul_le_mul hKexp (Real.rpow_le_rpow_of_exponent_le (hN₁ k) hse)
            (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
        _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
    simpa only [one_div, Real.rpow_neg hN.le] using
      one_div_le_one_div_of_le htwo ht
  have hfactor : 20 * cfg.K k ^ 3 / δ ≤ cfg.N k ^ ε := by
    dsimp [δ]
    rw [Real.rpow_neg hN.le, div_inv_eq_mul]
    exact hbudgetk.le
  obtain ⟨_, hν, _, _, _, _, _, _, _, _⟩ := h.basic k
  letI : IsProbabilityMeasure (cfg.ν k) := hν
  have hpos : cfg.ν k (cfg.A k s i) ≠ 0 := by
    have hh : 0 < ENNReal.ofReal
        ((cfg.N k ^ (-s)) ^ cfg.d * q ^ 2 * cfg.N k ^ (-cfg.ℓ * s) / cfg.K k) := by
      apply ENNReal.ofReal_pos.mpr
      positivity
    exact ne_of_gt (hh.trans_le (hlabel i).1)
  have hπcap := (hcapk 1 0 v hR'₁ hR'.le (by norm_num) (by linarith) hvR hvR').1
  have hgood : ∀ᵐ p ∂cfg.μ k,
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) ∧
      |cfg.b k p.1 3| ≤ cfg.K k := by
    filter_upwards [h.contact k, h.ae_incidence_horizontal_bounds k] with p hp hb
    refine ⟨hp, ?_⟩
    have h₀ := abs_nonneg (cfg.b k p.1 0)
    have h₁ := abs_nonneg (cfg.b k p.1 1)
    have h₄ := abs_nonneg (cfg.b k p.1 4)
    linarith
  obtain ⟨p₀, p₁, hp₀, hp₁, hsep⟩ :=
    Submission.Obl.k4_contact_time_rate_rigidity.label_witnesses
      (cfg.μ k) (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i))
      {p | |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) ∧
        |cfg.b k p.1 3| ≤ cfg.K k}
      (fun p => cfg.b k p.1 3) hK hq hδ
      (show 0 ≤ cfg.N k ^ (-cfg.S * v) by positivity)
      (cfg.ν k (cfg.A k s i)) hpos (measure_ne_top _ _) (hlabel i).2.2.1
      (by
        intro a
        have hh := (hpal i v a hvR hvR').trans
          (mul_le_mul' (le_refl (ENNReal.ofReal (cfg.K k * q) * cfg.ν k (cfg.A k s i)))
            (hπcap a))
        simpa only [Set.mem_prod, and_assoc, δ] using hh)
      hsmallk hgood
  have hm : m ∈ Data.I (cfg.T k s) (cfg.j k s i) := by
    change ((cfg.j k s i : ℕ) : ℝ) * q ≤
        (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * q ∧
      (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * q ≤
        (((cfg.j k s i : ℕ) : ℝ) + 1) * q
    constructor <;> nlinarith only [hq.le]
  have ha₀ := (hA i).2.2 hp₀.1.1
  have ha₁ := (hA i).2.2 hp₁.1.1
  have hgeom₀ := (hlabel i).2.2.2.2.2.1 p₀.1 ha₀ m hm
  have hgeom₁ := (hlabel i).2.2.2.2.2.1 p₁.1 ha₁ m hm
  have hrow₀ : |cfg.b k p₀.1 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k p₀.1 3| ≤
      cfg.K k * g := by simpa only [h.equal_rates] using hgeom₀.2.2
  have hrow₁ : |cfg.b k p₁.1 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k p₁.1 3| ≤
      cfg.K k * g := by simpa only [h.equal_rates] using hgeom₁.2.2
  have hbound := centered_contact_row_bound hK hq.le hg.le hδ hδ₁ hgq he
    hp₀.2.2 hsep.le hp₀.2.1 hp₁.2.1 hrow₀ hrow₁
    (z := cfg.c k s i 0 + m * cfg.c k s i 1)
    (by simpa only [Data.x, Matrix.cons_val_one, Matrix.cons_val_zero,
      sub_add_eq_sub_sub] using hgeom₀.1)
    (by simpa only [Data.x, Matrix.cons_val_one, Matrix.cons_val_zero,
      sub_add_eq_sub_sub] using hgeom₁.1)
  apply (show |cfg.c k s i 3 + cfg.c k s i 0 + m * cfg.c k s i 1| +
    |cfg.c k s i 4 - m| ≤ 20 * cfg.K k ^ 3 * q / δ by
      simpa only [add_assoc] using hbound).trans
  convert mul_le_mul_of_nonneg_right hfactor hq.le using 1 <;> ring

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
