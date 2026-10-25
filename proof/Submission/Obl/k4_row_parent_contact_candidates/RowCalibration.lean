/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/RowCalibration.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.RowContact
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration

/-!
# Calibration of the parent sheet restriction

The base correction `Gb = P(base, L(base))` of a parent affine hidden sheet `L`
needs a fixed-power coefficient bound. It follows from the accepted mesh
calibration (o242 `k4_quadratic_mesh_coefficient_calibration`) applied to the
base law of the retained incidences:

* `base_cell_cap`: base mesh caps from the native caps at hidden scale one
  (`|P| ≤ K` at incidences, so `2K + 4` unit native bins per cell);
* `base_calibration`: coefficients of a base polynomial bounded at the
  incidences of a set of original mass `m`;
* `sheet_coeff_bound`: `‖P(base, L(base))‖ ≤ N^(6((3κ+d+ℓ)r+1)+1)` for a row
  parent with a parent affine sheet fit, at one index;
* `result_of_rowParents_affine`: frequent row parents with non-small skew and a
  parent affine sheet fit give the frozen `Result` (no calibration input).
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point baseCalibratedTest affineBase
  affineSheetRestriction)
open Submission.Lib.K4ChartLifting (coeffL1)
open Submission.Lib.K4MovingMeshBoxes (baseMesh)

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Incidence laws of a common model are finite. -/
theorem mu_finite {p : Parameters} {a : PreparedModel α} (hcommon : a.Common p) (k : ℕ) :
    IsFiniteMeasure (a.mu k) := by
  have := hcommon.prob k
  constructor
  have h0 := (hcommon k).2.2.2.2.2.1
  have hdom := hcommon.dom k
  rw [Measure.le_iff'] at hdom
  have hS : a.mu k univ ≤ a.mu k (univ ×ˢ Icc (0 : ℝ) 1) := by
    calc a.mu k univ = a.mu k ((univ ×ˢ Icc (0 : ℝ) 1) ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) := by
          rw [union_compl_self]
      _ ≤ a.mu k (univ ×ˢ Icc (0 : ℝ) 1) + a.mu k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ :=
          measure_union_le _ _
      _ = a.mu k (univ ×ˢ Icc (0 : ℝ) 1) := by rw [h0, add_zero]
  calc a.mu k univ ≤ a.mu k (univ ×ˢ Icc (0 : ℝ) 1) := hS
    _ ≤ (ENNReal.ofReal (p.K k) • (a.nu k).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := hdom _
    _ = ENNReal.ofReal (p.K k) * (a.nu k univ * volume (Icc (0 : ℝ) 1)) := by
        rw [Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    _ < ⊤ := by
        rw [measure_univ, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.one_lt_top ENNReal.ofReal_lt_top)

/-- Native values at incidences are bounded by `K`. -/
theorem ae_native_value {p : Parameters} {a : PreparedModel α} (hcommon : a.Common p) (k : ℕ) :
    ∀ᵐ w ∂a.mu k, |eval (a.x k w.1 w.2) (a.P k)| ≤ p.K k := by
  have hsupp : ∀ᵐ w ∂a.mu k, w.2 ∈ Icc (0 : ℝ) 1 := by
    have h0 := (hcommon k).2.2.2.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
    simp only [mem_compl_iff, not_not, mem_prod, mem_univ, true_and] at hw
    exact hw
  filter_upwards [hsupp, (hcommon k).2.2.2.2.2.2.2.2.2] with w hw hP
  exact (hP.1 w.2 hw).1

/-- **Base cell caps** from the native caps at hidden scale one: on incidences
`|P| ≤ K`, so a base cell meets at most `2K + 4` unit native bins. -/
theorem base_cell_cap {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (hcommon : a.Common p) {k : ℕ} {r' : ℝ}
    (hcell : ∀ (q : Fin 3 → ℤ) (j : ℤ), a.mu k {w | a.cell (p.N k) r' k w = q ∧
      ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-(0 : ℝ))⌋ = j} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * r' - p.d * 0)))
    (q : Fin 3 → ℤ) :
    a.mu k {w | baseMesh (p.N k ^ (-r')) (Zoom.baseOf (a.b k w.1) w.2) = q} ≤
      ENNReal.ofReal ((2 * p.K k + 4) * p.K k * (p.N k ^ (-r')) ^ 3) := by
  classical
  have hK1 := hp.2.2.1.1 k
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  set n₀ : ℕ := ⌈p.K k⌉₊ with hn₀
  set J : Finset ℤ := Finset.Icc (-(n₀ : ℤ) - 1) (n₀ : ℤ) with hJ
  have hsub : {w : α × ℝ | baseMesh (p.N k ^ (-r')) (Zoom.baseOf (a.b k w.1) w.2) = q} ≤ᵐ[a.mu k]
      ⋃ j ∈ J, {w | a.cell (p.N k) r' k w = q ∧
        ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-(0 : ℝ))⌋ = j} := by
    filter_upwards [ae_native_value hcommon k] with w hw hwq
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨⌊eval (a.x k w.1 w.2) (a.P k)⌋, ?_, ?_, ?_⟩
    · rw [hJ, Finset.mem_Icc]
      have hc : p.K k ≤ (n₀ : ℝ) := Nat.le_ceil _
      have hab := abs_le.mp hw
      constructor
      · have : (-(n₀ : ℝ) - 1) < (⌊eval (a.x k w.1 w.2) (a.P k)⌋ : ℝ) + 1 := by
          have := Int.lt_floor_add_one (eval (a.x k w.1 w.2) (a.P k))
          linarith
        have : -(n₀ : ℤ) - 1 < ⌊eval (a.x k w.1 w.2) (a.P k)⌋ + 1 := by exact_mod_cast this
        omega
      · have : (⌊eval (a.x k w.1 w.2) (a.P k)⌋ : ℝ) ≤ n₀ := by
          have := Int.floor_le (eval (a.x k w.1 w.2) (a.P k))
          linarith
        exact_mod_cast this
    · rw [cell_eq_baseMesh]; exact hwq
    · simp
  calc a.mu k {w | baseMesh (p.N k ^ (-r')) (Zoom.baseOf (a.b k w.1) w.2) = q}
      ≤ a.mu k (⋃ j ∈ J, {w | a.cell (p.N k) r' k w = q ∧
          ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-(0 : ℝ))⌋ = j}) := measure_mono_ae hsub
    _ ≤ ∑ j ∈ J, a.mu k {w | a.cell (p.N k) r' k w = q ∧
          ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-(0 : ℝ))⌋ = j} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ J, ENNReal.ofReal (p.K k * p.N k ^ (-3 * r' - p.d * 0)) :=
        Finset.sum_le_sum fun j _ => hcell q j
    _ = (J.card : ℝ≥0∞) * ENNReal.ofReal (p.K k * p.N k ^ (-3 * r' - p.d * 0)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((2 * p.K k + 4) * p.K k * (p.N k ^ (-r')) ^ 3) := by
        have hcard : (J.card : ℝ) ≤ 2 * p.K k + 4 := by
          rw [hJ, Int.card_Icc]
          have hc : (n₀ : ℝ) ≤ p.K k + 1 := (Nat.ceil_lt_add_one (by linarith)).le
          have : ((n₀ : ℤ) + 1 - (-(n₀ : ℤ) - 1)).toNat = 2 * n₀ + 2 := by omega
          rw [this]
          push_cast
          linarith
        have he : p.N k ^ (-3 * r' - p.d * 0) = (p.N k ^ (-r')) ^ 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
        rw [he, show ((J.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal (J.card : ℝ) by simp,
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h0 : 0 ≤ p.K k * (p.N k ^ (-r')) ^ 3 := by positivity
        calc (J.card : ℝ) * (p.K k * (p.N k ^ (-r')) ^ 3)
            ≤ (2 * p.K k + 4) * (p.K k * (p.N k ^ (-r')) ^ 3) :=
              mul_le_mul_of_nonneg_right hcard h0
          _ = (2 * p.K k + 4) * p.K k * (p.N k ^ (-r')) ^ 3 := by ring

/-- The calibration constant of the accepted mesh calibration (o242). -/
def CalibrationBound (C₂ : ℝ) : Prop :=
  ∀ K β m E δ : ℝ, 1 ≤ K → 0 < β → 0 < m → 0 ≤ E → 0 < δ →
    C₂ * (1 + K) ^ C₂ * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2 →
    ∀ μ : Measure (Fin 3 → ℝ), IsFiniteMeasure μ → ENNReal.ofReal m ≤ μ univ →
    (∀ q : Fin 3 → ℤ, μ {z | (fun i : Fin 3 => ⌊z i / δ⌋) = q} ≤ ENNReal.ofReal (β * δ ^ (3 : ℕ))) →
    ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
    (∀ᵐ z ∂μ, (∀ i, |z i| ≤ K) ∧ |MvPolynomial.eval z G| ≤ E) →
    ∀ e, |G.coeff e| ≤ C₂ * (1 + K) ^ C₂ * (1 + β / m) ^ (6 : ℕ) * E

theorem exists_calibrationBound : ∃ C₂ : ℝ, 1 ≤ C₂ ∧ CalibrationBound C₂ :=
  Submission.k4_quadratic_mesh_coefficient_calibration

/-- **Calibration of a base correction from the original caps.** A base polynomial
bounded by `E` at the incidences of a set of original mass `m` has coefficients at
most `C₂ (K+2)^C₂ (1 + (2K+4)K/m)^6 E`, given the native caps at hidden scale one on
a mesh fine enough for the accepted mesh calibration (o242). -/
theorem base_calibration {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (hcommon : a.Common p) {k : ℕ} {C₂ : ℝ} (hcal : CalibrationBound C₂) {r' : ℝ}
    (hcell : ∀ (q : Fin 3 → ℤ) (j : ℤ), a.mu k {w | a.cell (p.N k) r' k w = q ∧
      ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-(0 : ℝ))⌋ = j} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * r' - p.d * 0)))
    (G : Set (α × ℝ)) (hG : MeasurableSet G) {m : ℝ} (hm : 0 < m)
    (hmass : ENNReal.ofReal m ≤ a.mu k G) (Gb : MvPolynomial (Fin 3) ℝ)
    (hdeg : Gb.totalDegree ≤ 2) {E : ℝ} (hE : 0 ≤ E)
    (hbd : ∀ z ∈ G, |eval (Zoom.baseOf (a.b k z.1) z.2) Gb| ≤ E)
    (hmesh : C₂ * (1 + (p.K k + 1)) ^ C₂ * (1 + (2 * p.K k + 4) * p.K k / m) ^ (6 : ℕ) *
      p.N k ^ (-r') ≤ 1 / 2) :
    ∀ e, |Gb.coeff e| ≤
      C₂ * (1 + (p.K k + 1)) ^ C₂ * (1 + (2 * p.K k + 4) * p.K k / m) ^ (6 : ℕ) * E := by
  have hK1 := hp.2.2.1.1 k
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hb := (hcommon k).1
  have := mu_finite hcommon k
  set base : α × ℝ → Fin 3 → ℝ := fun z => Zoom.baseOf (a.b k z.1) z.2 with hbase
  have hbm : Measurable base := by
    have hc : ∀ e, Measurable (fun z : α × ℝ => a.b k z.1 e) :=
      fun e => (measurable_pi_apply e).comp (hb.comp measurable_fst)
    apply Measurable.of_eval
    intro i
    fin_cases i <;> simp [hbase, Zoom.baseOf]
    · exact measurable_snd
    · exact (hc 0).add (measurable_snd.mul (hc 3))
    · exact (hc 1).add (measurable_snd.mul (hc 4))
  set μb : Measure (Fin 3 → ℝ) := Measure.map base ((a.mu k).restrict G) with hμb
  have hfin : IsFiniteMeasure μb := by rw [hμb]; infer_instance
  have hmass' : ENNReal.ofReal m ≤ μb univ := by
    rw [hμb, Measure.map_apply hbm MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
    exact hmass
  have hδ : 0 < p.N k ^ (-r') := Real.rpow_pos_of_pos hN0 _
  have hcaps : ∀ q : Fin 3 → ℤ, μb {z | (fun i : Fin 3 => ⌊z i / p.N k ^ (-r')⌋) = q} ≤
      ENNReal.ofReal ((2 * p.K k + 4) * p.K k * (p.N k ^ (-r')) ^ (3 : ℕ)) := by
    intro q
    have hms : MeasurableSet {z : Fin 3 → ℝ | (fun i : Fin 3 => ⌊z i / p.N k ^ (-r')⌋) = q} :=
      (Submission.Lib.K4AffineMeshCaps.measurable_baseMesh _) (measurableSet_singleton q)
    rw [hμb, Measure.map_apply hbm hms]
    refine (Measure.restrict_le_self _).trans (le_trans (le_of_eq rfl) ?_)
    exact base_cell_cap hp hcommon hcell q
  have hae : ∀ᵐ z ∂μb, (∀ i, |z i| ≤ p.K k + 1) ∧ |MvPolynomial.eval z Gb| ≤ E := by
    have hcl : MeasurableSet {z : Fin 3 → ℝ | (∀ i, |z i| ≤ p.K k + 1) ∧
        |MvPolynomial.eval z Gb| ≤ E} := by
      have h1 : IsClosed {z : Fin 3 → ℝ | (∀ i, |z i| ≤ p.K k + 1) ∧
          |MvPolynomial.eval z Gb| ≤ E} := by
        have : {z : Fin 3 → ℝ | (∀ i, |z i| ≤ p.K k + 1) ∧ |MvPolynomial.eval z Gb| ≤ E} =
            (⋂ i, {z : Fin 3 → ℝ | |z i| ≤ p.K k + 1}) ∩ {z | |MvPolynomial.eval z Gb| ≤ E} := by
          ext z; simp
        rw [this]
        exact (isClosed_iInter fun i => isClosed_le (continuous_abs.comp (continuous_apply i))
          continuous_const).inter
          (isClosed_le (continuous_abs.comp (MvPolynomial.continuous_eval Gb)) continuous_const)
      exact h1.measurableSet
    rw [hμb, ae_map_iff hbm.aemeasurable hcl, ae_restrict_iff' hG]
    filter_upwards [ae_base_bounded hp hcommon k] with w hw hwG
    exact ⟨hw, hbd w hwG⟩
  have hβ : 0 < (2 * p.K k + 4) * p.K k := by positivity
  exact hcal (p.K k + 1) ((2 * p.K k + 4) * p.K k) m E (p.N k ^ (-r')) (by linarith) hβ hm hE hδ
    hmesh μb hfin hmass' hcaps Gb hdeg hae


/-- Mass floor of a row parent in fixed-power form. -/
theorem rowParent_mass_floor {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {r E M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hatr : a.AtlasAt p R k r) (RP : RowParent p a k r E M) :
    ENNReal.ofReal (a.q k r ^ 3 * width p k r ^ p.d * narrow p k r / (p.K k * M)) ≤
      a.mu k RP.G := by
  have hK0 : 0 < p.K k := by linarith [hp.2.2.1.1 k]
  have hq := q_pos a k r
  have h1 := hatr.prior_lower RP.Q
  refine le_trans ?_ (RP.mass.trans (hcommon.rho_le k RP.G))
  calc ENNReal.ofReal (a.q k r ^ 3 * width p k r ^ p.d * narrow p k r / (p.K k * M))
      = ENNReal.ofReal (a.q k r / M) * ENNReal.ofReal (width p k r ^ p.d * a.q k r ^ 2 *
          narrow p k r / p.K k) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (a.q k r / M) * a.nu k (a.A k r RP.Q) := by gcongr

/-- **Calibrated native restriction of a parent affine sheet at one index.** -/
theorem sheet_coeff_bound {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (hcommon : a.Common p) {C₂ : ℝ} (hC₂ : 1 ≤ C₂) (hcal : CalibrationBound C₂) {R : ℝ} {k : ℕ}
    {r E : ℝ} (hr : 0 < r) (hatr : a.AtlasAt p R k r) {M : ℝ} (hM1 : 1 ≤ M)
    (RP : RowParent p a k r E M) (L : Fin 4 → ℝ)
    (hfit : ∀ z ∈ RP.G, ∀ t ∈ a.block k r RP.Q,
      |eval (point (a.b k z.1) t) (affineBase L) - point (a.b k z.1) t 3| ≤ M * width p k r)
    (hcell : ∀ (q : Fin 3 → ℤ) (j : ℤ), a.mu k {w |
      a.cell (p.N k) (6 * ((3 * p.kappa + p.d + p.ell) * r + 1) + 3) k w = q ∧
      ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-(0 : ℝ))⌋ = j} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * (6 * ((3 * p.kappa + p.d + p.ell) * r + 1) + 3) -
          p.d * 0)))
    (hKM : p.K k ^ 4 * M ≤ p.N k)
    (hbr : 27 * 3 * 7 ^ 6 * C₂ * (p.K k + 2) ^ C₂ * p.K k ^ 13 * M ^ 2 ≤ p.N k) :
    coeffL1 (affineSheetRestriction L (a.P k)) ≤
      p.N k ^ (6 * ((3 * p.kappa + p.d + p.ell) * r + 1) + 1) := by
  have hK1 := hp.2.2.1.1 k
  have hK0 : 0 < p.K k := by linarith
  have hN2 := hp.1 k
  have hN0 : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := by linarith
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hd : 0 ≤ p.d := hp.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hM0 : 0 < M := by linarith
  set cm := (3 * p.kappa + p.d + p.ell) * r + 1 with hcm
  set r' := 6 * cm + 3 with hr'
  set m₀ := a.q k r ^ 3 * width p k r ^ p.d * narrow p k r / (p.K k * M) with hm₀
  have hq := q_pos a k r
  have hw := width_pos p hp k r
  have hg := narrow_pos p hp k r
  have hm₀pos : 0 < m₀ := by positivity
  -- the mass floor in fixed-power form
  have hm₀low : p.N k ^ (-cm) ≤ m₀ := by
    have hql := atlas_q_lower hp hatr
    have hq3 : (p.N k ^ (-(p.kappa * r)) / p.K k) ^ 3 ≤ a.q k r ^ 3 :=
      pow_le_pow_left₀ (by positivity) hql 3
    have hwd : width p k r ^ p.d = p.N k ^ (-(r * p.d)) := by
      unfold width; rw [← Real.rpow_mul hN0.le]; ring_nf
    have hgn : narrow p k r = p.N k ^ (-(p.ell * r)) := by unfold narrow; ring_nf
    have hlow : p.N k ^ (-(3 * p.kappa + p.d + p.ell) * r) / (p.K k ^ 4 * M) ≤ m₀ := by
      rw [hm₀, hwd, hgn]
      have h3 : (p.N k ^ (-(p.kappa * r))) ^ (3 : ℕ) = p.N k ^ (-(3 * (p.kappa * r))) := by
        rw [← Real.rpow_natCast (p.N k ^ (-(p.kappa * r))) 3, ← Real.rpow_mul hN0.le]; ring_nf
      have hsplit : p.N k ^ (-(3 * p.kappa + p.d + p.ell) * r) =
          p.N k ^ (-(3 * (p.kappa * r))) * p.N k ^ (-(r * p.d)) * p.N k ^ (-(p.ell * r)) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
      have e : p.N k ^ (-(3 * p.kappa + p.d + p.ell) * r) / (p.K k ^ 4 * M) =
          (p.N k ^ (-(p.kappa * r)) / p.K k) ^ 3 * p.N k ^ (-(r * p.d)) *
            p.N k ^ (-(p.ell * r)) / (p.K k * M) := by
        rw [div_pow, h3, hsplit]
        field_simp
      rw [e]
      gcongr
    calc p.N k ^ (-cm) = p.N k ^ (-(3 * p.kappa + p.d + p.ell) * r) / p.N k := by
          rw [hcm, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN0]; ring_nf
      _ ≤ p.N k ^ (-(3 * p.kappa + p.d + p.ell) * r) / (p.K k ^ 4 * M) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hKM
      _ ≤ m₀ := hlow
  -- the restricted incidence set and its mass
  set RPn := RP.native hcommon with hRPn
  have hmass : ENNReal.ofReal m₀ ≤ a.mu k RPn.G := rowParent_mass_floor hp hcommon hr hM0 hatr RPn
  -- the value bound of the native restriction at incidences
  set Gb := affineSheetRestriction L (a.P k) with hGb
  have hPdeg : (a.P k).totalDegree ≤ 2 := (hcommon k).2.2.2.2.2.2.2.1
  have hGdeg : Gb.totalDegree ≤ 2 :=
    (Submission.Lib.K4ContactNormalization.affineSheetRestriction_degree L _).trans hPdeg
  have hw1 : width p k r ≤ 1 := by
    unfold width; exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  set E₀ := p.K k + 2 * M ^ 2 * p.K k with hE₀
  have hbd : ∀ z ∈ RPn.G, |eval (Zoom.baseOf (a.b k z.1) z.2) Gb| ≤ E₀ := by
    intro z hz
    have hzG : z ∈ RP.G := hz.1
    have hzN : z.1 ∈ nativeLines p a k := hz.2.1
    have hzb : z.2 ∈ a.block k r RP.Q := (RP.G_sub hzG).2
    have hz01 : z.2 ∈ Icc (0 : ℝ) 1 := interval_sub_unit _ _ hzb
    have hsig := signal_of_sheet (a.P k) hPdeg L (a.b k z.1) (a.block k r RP.Q) hM0.le hK0.le
      hw.le hw1
      (fun t ht => ⟨(hzN t (interval_sub_unit _ _ ht)).2.1, (hzN t (interval_sub_unit _ _ ht)).2.2⟩)
      (hfit z hzG) z.2 hzb
    rw [Submission.Lib.K4ContactNormalization.eval_baseCalibratedTest, point_castSucc] at hsig
    have hP := (hzN z.2 hz01).1
    have hdiff : |eval (Zoom.baseOf (a.b k z.1) z.2) Gb| ≤
        |eval (point (a.b k z.1) z.2) (a.P k)| +
          |eval (point (a.b k z.1) z.2) (a.P k) - eval (Zoom.baseOf (a.b k z.1) z.2) Gb| := by
      have := abs_sub (eval (point (a.b k z.1) z.2) (a.P k))
        (eval (point (a.b k z.1) z.2) (a.P k) - eval (Zoom.baseOf (a.b k z.1) z.2) Gb)
      simpa using this
    have hsig' : (M * p.K k + M ^ 2 * p.K k) * width p k r ≤ 2 * M ^ 2 * p.K k := by
      have hMM : M ≤ M ^ 2 := by nlinarith
      have : M * p.K k + M ^ 2 * p.K k ≤ 2 * M ^ 2 * p.K k := by nlinarith
      calc (M * p.K k + M ^ 2 * p.K k) * width p k r ≤ (M * p.K k + M ^ 2 * p.K k) * 1 :=
            mul_le_mul_of_nonneg_left hw1 (by positivity)
        _ ≤ 2 * M ^ 2 * p.K k := by linarith
    linarith
  -- numerical control
  set X := 1 + (2 * p.K k + 4) * p.K k / m₀ with hX
  have hNcm : 1 ≤ p.N k ^ cm := Real.one_le_rpow hN1 (by positivity)
  have hinv : 1 / m₀ ≤ p.N k ^ cm := by
    rw [div_le_iff₀ hm₀pos]
    calc (1 : ℝ) = p.N k ^ cm * p.N k ^ (-cm) := by
          rw [← Real.rpow_add hN0]; simp
      _ ≤ p.N k ^ cm * m₀ := mul_le_mul_of_nonneg_left hm₀low (by positivity)
  have hX1 : 1 ≤ X := by
    have : 0 ≤ (2 * p.K k + 4) * p.K k / m₀ := by positivity
    linarith
  have hXle : X ≤ 7 * p.K k ^ 2 * p.N k ^ cm := by
    have h1 : (2 * p.K k + 4) * p.K k ≤ 6 * p.K k ^ 2 := by nlinarith
    have h2 : (2 * p.K k + 4) * p.K k / m₀ ≤ 6 * p.K k ^ 2 * p.N k ^ cm := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul h1 hinv (by positivity) (by positivity)
    have h3 : 1 ≤ p.K k ^ 2 * p.N k ^ cm :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) hNcm
    linarith
  have hX6 : X ^ 6 ≤ 7 ^ 6 * p.K k ^ 12 * p.N k ^ (6 * cm) := by
    calc X ^ 6 ≤ (7 * p.K k ^ 2 * p.N k ^ cm) ^ 6 := pow_le_pow_left₀ (by linarith) hXle 6
      _ = 7 ^ 6 * p.K k ^ 12 * (p.N k ^ cm) ^ 6 := by ring
      _ = 7 ^ 6 * p.K k ^ 12 * p.N k ^ (6 * cm) := by
          rw [← Real.rpow_natCast (p.N k ^ cm) 6, ← Real.rpow_mul hN0.le]; ring_nf
  have hKC : 0 < (p.K k + 2) ^ C₂ := Real.rpow_pos_of_pos (by linarith) _
  have hcore : C₂ * (p.K k + 2) ^ C₂ * (7 ^ 6 * p.K k ^ 12) ≤ p.N k := by
    have h1 : 1 ≤ 27 * 3 * p.K k * M ^ 2 := by
      have : 1 ≤ M ^ 2 := one_le_pow₀ hM1
      nlinarith
    have h0 : 0 ≤ C₂ * (p.K k + 2) ^ C₂ * (7 ^ 6 * p.K k ^ 12) := by positivity
    calc C₂ * (p.K k + 2) ^ C₂ * (7 ^ 6 * p.K k ^ 12)
        ≤ C₂ * (p.K k + 2) ^ C₂ * (7 ^ 6 * p.K k ^ 12) * (27 * 3 * p.K k * M ^ 2) :=
          le_mul_of_one_le_right h0 h1
      _ = 27 * 3 * 7 ^ 6 * C₂ * (p.K k + 2) ^ C₂ * p.K k ^ 13 * M ^ 2 := by ring
      _ ≤ p.N k := hbr
  have hmesh : C₂ * (1 + (p.K k + 1)) ^ C₂ * X ^ (6 : ℕ) * p.N k ^ (-r') ≤ 1 / 2 := by
    rw [show 1 + (p.K k + 1) = p.K k + 2 by ring]
    calc C₂ * (p.K k + 2) ^ C₂ * X ^ (6 : ℕ) * p.N k ^ (-r')
        ≤ C₂ * (p.K k + 2) ^ C₂ * (7 ^ 6 * p.K k ^ 12 * p.N k ^ (6 * cm)) * p.N k ^ (-r') := by
          gcongr
      _ = C₂ * (p.K k + 2) ^ C₂ * (7 ^ 6 * p.K k ^ 12) * (p.N k ^ (6 * cm) * p.N k ^ (-r')) := by
          ring
      _ ≤ p.N k * (p.N k ^ (6 * cm) * p.N k ^ (-r')) := by gcongr
      _ = p.N k ^ (-2 : ℝ) := by
          rw [show p.N k * (p.N k ^ (6 * cm) * p.N k ^ (-r')) =
            p.N k ^ ((1 : ℝ) + (6 * cm + -r')) by
              rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]]
          congr 1
          rw [hr']; ring
      _ ≤ 1 / 2 := by
          rw [Real.rpow_neg hN0.le, Real.rpow_two, one_div]
          apply inv_anti₀ (by norm_num)
          nlinarith
  have hcoef := base_calibration hp hcommon hcal hcell RPn.G RPn.measurable_G hm₀pos hmass Gb
    hGdeg (by positivity) hbd hmesh
  have hL1 := Submission.Lib.K4ChartLifting.coeffL1_le_of_coeff_le Gb hGdeg _ hcoef
  norm_num at hL1
  refine hL1.trans ?_
  rw [show 1 + (p.K k + 1) = p.K k + 2 by ring]
  have hE₀ : E₀ ≤ 3 * M ^ 2 * p.K k := by
    have : p.K k ≤ M ^ 2 * p.K k := by
      have : 1 ≤ M ^ 2 := one_le_pow₀ hM1
      nlinarith
    rw [hE₀]; linarith
  calc 27 * (C₂ * (p.K k + 2) ^ C₂ * X ^ 6 * E₀)
      ≤ 27 * (C₂ * (p.K k + 2) ^ C₂ * (7 ^ 6 * p.K k ^ 12 * p.N k ^ (6 * cm)) *
          (3 * M ^ 2 * p.K k)) := by gcongr
    _ = (27 * 3 * 7 ^ 6 * C₂ * (p.K k + 2) ^ C₂ * p.K k ^ 13 * M ^ 2) * p.N k ^ (6 * cm) := by
        ring
    _ ≤ p.N k * p.N k ^ (6 * cm) := by gcongr
    _ = p.N k ^ (6 * cm + 1) := by
        rw [Real.rpow_add hN0, Real.rpow_one]; ring


/-- Powers of subpower sequences are subpower. -/
theorem Subpower.pow {N L : ℕ → ℝ} (hN1 : ∀ k, 1 ≤ N k) (h : Subpower N L) (h0 : ∀ k, 0 ≤ L k)
    (n : ℕ) : Subpower N (fun k => L k ^ n) := by
  have hN : ∀ k, 0 < N k := fun k => lt_of_lt_of_le zero_lt_one (hN1 k)
  induction n with
  | zero =>
    intro ε hε
    filter_upwards with k
    simp only [pow_zero]
    exact Real.one_le_rpow (hN1 k) hε.le
  | succ n ih =>
    have := Subpower.mul hN ih h (fun k => pow_nonneg (h0 k) n)
    exact this.mono (fun k => by rw [pow_succ])

/-- Real powers of subpower sequences bounded below by one are subpower. -/
theorem Subpower.rpow {N L : ℕ → ℝ} (hN1 : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (h : Subpower N L) (h1 : ∀ k, 1 ≤ L k) {c : ℝ} (hc : 0 < c) :
    Subpower N (fun k => (L k + 2) ^ c) := by
  have hN : ∀ k, 0 < N k := fun k => lt_of_lt_of_le zero_lt_one (hN1 k)
  intro ε hε
  filter_upwards [h (ε / (2 * c)) (by positivity),
    ((tendsto_rpow_atTop (half_pos hε)).comp hNt).eventually_ge_atTop ((3 : ℝ) ^ c)]
    with k hk h3
  have hL : L k + 2 ≤ 3 * L k := by linarith [h1 k]
  calc (L k + 2) ^ c ≤ (3 * L k) ^ c :=
        Real.rpow_le_rpow (by linarith [h1 k]) hL hc.le
    _ = (3 : ℝ) ^ c * L k ^ c := Real.mul_rpow (by norm_num) (by linarith [h1 k])
    _ ≤ N k ^ (ε / 2) * (N k ^ (ε / (2 * c))) ^ c :=
        mul_le_mul (show (3 : ℝ) ^ c ≤ N k ^ (ε / 2) from h3)
          (Real.rpow_le_rpow (by linarith [h1 k]) hk hc.le)
          (Real.rpow_nonneg (by linarith [h1 k]) _) (Real.rpow_nonneg (hN k).le _)
    _ = N k ^ ε := by
        rw [← Real.rpow_mul (hN k).le, ← Real.rpow_add (hN k)]
        congr 1
        field_simp
        ring



/-- **Row parents with non-small skew and a parent affine hidden sheet give the
frozen result**, with no calibration input: the native restriction
`P(base, L(base))` is calibrated here from the original native caps and the
parent mass floor (accepted mesh calibration o242). -/
theorem result_of_rowParents_affine {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (ha : a.Valid p) (hCMP : ContactModelPrinciple) {r e₀ : ℝ} (hr : 0 < r) (hrU : r < p.U)
    (he₀ : 0 < e₀) (M : ℕ → ℝ) (hM1 : ∀ k, 1 ≤ M k) (hM : Subpower p.N M)
    (hfreq : ∃ᶠ k in atTop, ∃ RP : RowParent p a k r (M k * p.N k ^ (-e₀)) (M k),
      ∃ L : Fin 4 → ℝ, RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M k ∧
        ∀ z ∈ RP.G, ∀ t ∈ a.block k r RP.Q,
          |eval (point (a.b k z.1) t) (affineBase L) - point (a.b k z.1) t 3| ≤
            M k * width p k r) :
    a.Result p := by
  obtain ⟨C₂, hC₂, hcal⟩ := exists_calibrationBound
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hd : 0 ≤ p.d := hp.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  have hN : ∀ k, 0 < p.N k := hp.N_pos
  set cm := (3 * p.kappa + p.d + p.ell) * r + 1 with hcm
  have hcm0 : 0 < cm := by positivity
  set r' := 6 * cm + 3 with hr'
  set R := r' + r⁻¹ + 2 with hRdef
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hR1 : 1 < R := by linarith
  have hRr : R⁻¹ ≤ r := by
    have : r⁻¹ ≤ R := by linarith
    have := inv_anti₀ hri this
    rwa [inv_inv] at this
  have hRr' : R⁻¹ ≤ r' := by
    have : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1.le
    linarith
  -- the subpower bracket
  have hK0 : ∀ k, 0 ≤ p.K k := fun k => le_trans zero_le_one (hp.2.2.1.1 k)
  have hM0 : ∀ k, 0 ≤ M k := fun k => le_trans zero_le_one (hM1 k)
  have hbrsub : Subpower p.N (fun k => 27 * 3 * 7 ^ 6 * C₂ * (p.K k + 2) ^ C₂ * p.K k ^ 13 *
      M k ^ 2) := by
    have h1 := Subpower.const hp.2.1 (27 * 3 * 7 ^ 6 * C₂)
    have h2 := Subpower.rpow hN1 hp.2.1 hp.K_subpower (hp.2.2.1.1) (by linarith : (0 : ℝ) < C₂)
    have h3 := Subpower.pow hN1 hp.K_subpower hK0 13
    have h4 := Subpower.pow hN1 hM hM0 2
    have h12 := Subpower.mul hN h1 h2 (fun _ => by positivity)
    have h123 := Subpower.mul hN h12 h3
      (fun k => mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [hK0 k]) _))
    have h1234 := Subpower.mul hN h123 h4
      (fun k => mul_nonneg (mul_nonneg (by positivity)
        (Real.rpow_nonneg (by linarith [hK0 k]) _)) (pow_nonneg (hK0 k) _))
    exact h1234
  have hKMsub : Subpower p.N (fun k => p.K k ^ 4 * M k) :=
    Subpower.mul hN (Subpower.pow hN1 hp.K_subpower hK0 4) hM (fun k => pow_nonneg (hK0 k) _)
  have hev : ∀ᶠ k in atTop, a.AtlasAt p R k r ∧
      (∀ (q : Fin 3 → ℤ) (j : ℤ), a.mu k {w | a.cell (p.N k) r' k w = q ∧
        ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-(0 : ℝ))⌋ = j} ≤
          ENNReal.ofReal (p.K k * p.N k ^ (-3 * r' - p.d * 0))) ∧
      p.K k ^ 4 * M k ≤ p.N k ∧
      27 * 3 * 7 ^ 6 * C₂ * (p.K k + 2) ^ C₂ * p.K k ^ 13 * M k ^ 2 ≤ p.N k := by
    filter_upwards [ha.2.2.1 R hR1, ha.2.1 R hR1, hKMsub 1 one_pos, hbrsub 1 one_pos]
      with k hat hcaps hkm hbr
    refine ⟨hat r hRr hrU.le, ?_, by simpa using hkm, by simpa using hbr⟩
    intro q j
    have h := ((hcaps r' 0 1 hRr' (by linarith) le_rfl (by linarith)
      (inv_le_one_of_one_le₀ hR1.le) hR1.le).2.1 true q j)
    simpa only [↓reduceIte] using h
  refine result_of_rowParents_sheet hp ha hCMP hr hrU he₀ (c₁ := 6 * cm + 1) (by positivity)
    M hM1 hM ?_
  refine (hfreq.and_eventually hev).mono ?_
  rintro k ⟨⟨RP, L, hlam, hlamM, hfit⟩, hatr, hcell, hKM, hbr⟩
  exact ⟨RP, L, hlam, hlamM,
    sheet_coeff_bound hp ha.1 hC₂ hcal hr hatr (hM1 k) RP L hfit hcell hKM hbr, hfit⟩

end

end Submission.Obl.k4_row_parent_contact_candidates
