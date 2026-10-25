import Mathlib
import Submission.Lib.K4ContactTransfer.ContactSheet
import Submission.Lib.K4ContactNormalization.HomogeneousCorrection

/-!
# Base-corrected native polynomial of the zoomed contact instance

The zoomed instance's native polynomial is `nPush (P - Gb(base))` for a base
polynomial `Gb` (e.g. `Gb = P(base, L(base))` for a parent affine hidden sheet
`L`, `Submission.Lib.K4ContactNormalization.affineSheetRestriction`): hidden
derivatives are those of the original `P`, values are `(P - Gb)/a_r`.

* `abs_eval_sub_le`: Lipschitz bound of polynomial evaluation by the `ℓ¹` norm;
* `offset_bin_cap_on`: offset bins when the offset varies little on the bounded
  part of each fine cell; `ae_base_bounded`: incidences have bounded base;
* `ZoomInput.zoom_corr_cap`: zoomed `h = true` caps from the ORIGINAL `P`-bin
  caps on a finer mesh (only `‖Gb‖` enters, no bound on the sheet);
* `ZoomInput.zoom_corr_common`: the `Common` conditions of the corrected
  polynomial from the original ones and a value bound `|P - Gb| ≤ Kz a_r` on
  the retained lines over the parent block.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point)
open Submission.Lib.K4ChartLifting (coeffL1 coeffL1_nonneg coeffL1_X coeffL1_C coeffL1_add_le
  coeffL1_bind₁_le)

noncomputable section

/-- Evaluation minus the constant coefficient is small near the origin. -/
theorem abs_eval_sub_constantCoeff_le {n : ℕ} (q : MvPolynomial (Fin n) ℝ) (h : Fin n → ℝ)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hh : ∀ i, |h i| ≤ δ) :
    |eval h q - constantCoeff q| ≤ coeffL1 q * δ := by
  classical
  have hc : constantCoeff q = ∑ m ∈ q.support, q.coeff m * (if m = 0 then 1 else 0) := by
    rw [Finset.sum_eq_single 0]
    · simp [constantCoeff_eq]
    · intro m _ hm; simp [hm]
    · intro h0
      simp [notMem_support_iff.mp h0]
  have hev : eval h q = ∑ m ∈ q.support, eval h (monomial m (q.coeff m)) := by
    conv_lhs => rw [q.as_sum]
    rw [map_sum]
  rw [hev, hc, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [coeffL1, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  rw [eval_monomial, ← mul_sub, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  by_cases h0 : m = 0
  · subst h0; simp [hδ0]
  · rw [if_neg h0, sub_zero, Finsupp.prod, Finset.abs_prod]
    calc ∏ i ∈ m.support, |h i ^ m i| ≤ ∏ i ∈ m.support, δ ^ m i := by
          apply Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
          intro i _
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hh i) _
      _ = δ ^ (∑ i ∈ m.support, m i) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ δ := by
          apply pow_le_of_le_one hδ0 hδ1
          intro hs
          apply h0
          ext i
          by_contra hi
          simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
          have hmem : i ∈ m.support := Finsupp.mem_support_iff.mpr hi
          have h2 : m i ≤ ∑ j ∈ m.support, m j :=
            Finset.single_le_sum (f := fun j => m j) (fun _ _ => Nat.zero_le _) hmem
          omega

/-- **Lipschitz bound** for polynomial evaluation near a bounded point. -/
theorem abs_eval_sub_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) {R δ : ℝ}
    (hR : 0 ≤ R) (hy : ∀ i, |y i| ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hxy : ∀ i, |x i - y i| ≤ δ) :
    |eval x p - eval y p| ≤ coeffL1 p * (1 + R) ^ p.totalDegree * δ := by
  set q := bind₁ (fun i => X i + C (y i)) p with hq
  have e1 : eval (fun i => x i - y i) q = eval x p := by
    rw [hq, Submission.Lib.K4ChartLifting.eval_bind₁']
    have : (fun i => eval (fun i => x i - y i) (X i + C (y i) : MvPolynomial (Fin n) ℝ)) = x := by
      funext i; simp
    rw [this]
  have e2 : constantCoeff q = eval y p := by
    rw [← eval_zero, hq, Submission.Lib.K4ChartLifting.eval_bind₁']
    have : (fun i => eval 0 (X i + C (y i) : MvPolynomial (Fin n) ℝ)) = y := by
      funext i; simp
    rw [this]
  have h1 := abs_eval_sub_constantCoeff_le q (fun i => x i - y i) hδ0 hδ1 hxy
  rw [e1, e2] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hδ0)
  refine coeffL1_bind₁_le _ (1 + R) (by linarith) (fun i => ?_) p
  calc coeffL1 (X i + C (y i) : MvPolynomial (Fin n) ℝ)
      ≤ coeffL1 (X i : MvPolynomial (Fin n) ℝ) + coeffL1 (C (y i) : MvPolynomial (Fin n) ℝ) :=
        coeffL1_add_le _ _
    _ = 1 + |y i| := by rw [coeffL1_X, coeffL1_C]
    _ ≤ 1 + R := by linarith [hy i]

open Submission.Lib.K4MovingMeshBoxes (baseMesh)
open Submission.Lib.K4AffineMeshCaps (meshBox_coordinate_distance)
open Submission.Lib.K4ContactNormalization (baseCalibratedTest eval_baseCalibratedTest
  pderiv_baseCalibratedTest second_pderiv_baseCalibratedTest baseCalibratedTest_degree)

/-- **Offset bins on a region.** The offset only has to vary by at most `η` on the
part of each `δ`-cell inside a region `S` containing the event's base points. -/
theorem offset_bin_cap_on {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (base : Ω → Fin 3 → ℝ) (h : Ω → ℝ) (F : (Fin 3 → ℝ) → ℝ) (S : Set (Fin 3 → ℝ))
    (extra : Ω → Prop) {δ η : ℝ} (hη : 0 < η)
    (hF : ∀ y ∈ S, ∀ y' ∈ S, baseMesh δ y = baseMesh δ y' → |F y - F y'| ≤ η) {C : ℝ≥0∞}
    (hcap : ∀ (z : Fin 3 → ℤ) (j : ℤ),
      μ {w | baseMesh δ (base w) = z ∧ ⌊h w / η⌋ = j ∧ extra w} ≤ C)
    (z : Fin 3 → ℤ) (j : ℤ) :
    μ {w | baseMesh δ (base w) = z ∧ ⌊(h w - F (base w)) / η⌋ = j ∧
      (base w ∈ S ∧ extra w)} ≤ 4 * C := by
  classical
  by_cases hne : ∃ w₀, baseMesh δ (base w₀) = z ∧ ⌊(h w₀ - F (base w₀)) / η⌋ = j ∧
      (base w₀ ∈ S ∧ extra w₀)
  · obtain ⟨w₀, hw₀1, -, hw₀S, -⟩ := hne
    set c := base w₀ with hcdef
    set j₀ : ℤ := ⌊(j : ℝ) + F c / η⌋ with hj₀
    have hsub : {w | baseMesh δ (base w) = z ∧ ⌊(h w - F (base w)) / η⌋ = j ∧
        (base w ∈ S ∧ extra w)} ⊆
        ⋃ i ∈ Finset.range 4,
          {w | baseMesh δ (base w) = z ∧ ⌊h w / η⌋ = j₀ - 1 + (i : ℤ) ∧ extra w} := by
      rintro w ⟨hw1, hw2, hwS, hw3⟩
      have hFv := abs_le.mp (hF (base w) hwS c hw₀S (hw1.trans hw₀1.symm))
      rw [Int.floor_eq_iff, le_div_iff₀ hη, div_lt_iff₀ hη] at hw2
      obtain ⟨h1, h2⟩ := hw2
      have hu1 := Int.floor_le ((j : ℝ) + F c / η)
      have hu2 := Int.lt_floor_add_one ((j : ℝ) + F c / η)
      rw [← hj₀] at hu1 hu2
      have e1 : ((j : ℝ) + F c / η) * η = j * η + F c := by
        rw [add_mul, div_mul_cancel₀ _ hη.ne']
      have hA : (j₀ : ℝ) * η ≤ j * η + F c := by
        rw [← e1]; exact mul_le_mul_of_nonneg_right hu1 hη.le
      have hB : j * η + F c < ((j₀ : ℝ) + 1) * η := by
        rw [← e1]; exact mul_lt_mul_of_pos_right hu2 hη
      have hfl1 : j₀ - 1 ≤ ⌊h w / η⌋ := by
        rw [Int.le_floor, le_div_iff₀ hη]; push_cast; nlinarith
      have hfl2 : ⌊h w / η⌋ < j₀ + 3 := by
        rw [Int.floor_lt, div_lt_iff₀ hη]; push_cast; nlinarith
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq]
      exact ⟨(⌊h w / η⌋ - (j₀ - 1)).toNat, by omega, hw1, by omega, hw3⟩
    calc μ {w | baseMesh δ (base w) = z ∧ ⌊(h w - F (base w)) / η⌋ = j ∧
          (base w ∈ S ∧ extra w)}
        ≤ μ (⋃ i ∈ Finset.range 4,
            {w | baseMesh δ (base w) = z ∧ ⌊h w / η⌋ = j₀ - 1 + (i : ℤ) ∧ extra w}) :=
          measure_mono hsub
      _ ≤ ∑ i ∈ Finset.range 4,
            μ {w | baseMesh δ (base w) = z ∧ ⌊h w / η⌋ = j₀ - 1 + (i : ℤ) ∧ extra w} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ Finset.range 4, C := Finset.sum_le_sum fun i _ => hcap z _
      _ = 4 * C := by simp
  · push Not at hne
    have : {w | baseMesh δ (base w) = z ∧ ⌊(h w - F (base w)) / η⌋ = j ∧
        (base w ∈ S ∧ extra w)} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨h1, h2, h3⟩
      exact hne w h1 h2 h3.1 h3.2
    rw [this, measure_empty]
    exact zero_le

variable {α : Type} [MeasurableSpace α]

/-- Trajectory points depend continuously on the coefficients. -/
theorem continuous_point_left (t : ℝ) : Continuous (fun b : Fin 6 → ℝ => point b t) := by
  unfold point
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- Lines on which a polynomial stays bounded over unit time form a measurable set. -/
theorem measurableSet_unit_bound {β : α → Fin 6 → ℝ} (hβ : Measurable β)
    (P : MvPolynomial (Fin 4) ℝ) (K : ℝ) :
    MeasurableSet {l : α | ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (point (β l) t) P| ≤ K} := by
  have hC : IsClosed {b : Fin 6 → ℝ | ∀ t ∈ Icc (0 : ℝ) 1,
      |MvPolynomial.eval (point b t) P| ≤ K} := by
    have : {b : Fin 6 → ℝ | ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (point b t) P| ≤ K} =
        ⋂ t ∈ Icc (0 : ℝ) 1, {b | |MvPolynomial.eval (point b t) P| ≤ K} := by
      ext b; simp
    rw [this]
    exact isClosed_biInter fun t _ => isClosed_le
      (continuous_abs.comp ((MvPolynomial.continuous_eval P).comp (continuous_point_left t)))
      continuous_const
  exact hC.measurableSet.preimage hβ


/-- Base coordinates of incidences of a common model are bounded by `K + 1`. -/
theorem ae_base_bounded {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (hcommon : a.Common p) (k : ℕ) :
    ∀ᵐ w ∂a.mu k, Zoom.baseOf (a.b k w.1) w.2 ∈ {y : Fin 3 → ℝ | ∀ i, |y i| ≤ p.K k + 1} := by
  have hK1 := hp.2.2.1.1 k
  have hsupp : ∀ᵐ w ∂a.mu k, w.2 ∈ Icc (0 : ℝ) 1 := by
    have h0 := (hcommon k).2.2.2.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
    simp only [mem_compl_iff, not_not, mem_prod, mem_univ, true_and] at hw
    exact hw
  have hcoef : ∀ᵐ w ∂a.mu k,
      |a.b k w.1 0| + |a.b k w.1 1| + |a.b k w.1 3| + |a.b k w.1 4| ≤ p.K k := by
    have hν := (hcommon k).2.2.2.2.2.2.2.2.1
    rw [ae_iff] at hν ⊢
    set A := {l : α | ¬(|a.b k l 0| + |a.b k l 1| + |a.b k l 3| + |a.b k l 4| ≤ p.K k)}
    have hset : {w : α × ℝ | ¬(|a.b k w.1 0| + |a.b k w.1 1| + |a.b k w.1 3| +
        |a.b k w.1 4| ≤ p.K k)} = A ×ˢ univ := by
      ext w; simp [A]
    rw [hset]
    have hdom := hcommon.dom k
    rw [Measure.le_iff'] at hdom
    refine le_antisymm ((hdom _).trans ?_) zero_le
    rw [Measure.smul_apply, Measure.prod_prod, hν, zero_mul, smul_zero]
  filter_upwards [hsupp, hcoef] with w ht hc
  intro i
  have h0 := abs_nonneg (a.b k w.1 0)
  have h1 := abs_nonneg (a.b k w.1 1)
  have h3 := abs_nonneg (a.b k w.1 3)
  have h4 := abs_nonneg (a.b k w.1 4)
  have ht1 : |w.2| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  fin_cases i
  · simp only [Zoom.baseOf]; simp; linarith
  · simp only [Zoom.baseOf]
    simp
    calc |a.b k w.1 0 + w.2 * a.b k w.1 3| ≤ |a.b k w.1 0| + |w.2| * |a.b k w.1 3| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |a.b k w.1 0| + 1 * |a.b k w.1 3| := by gcongr
      _ ≤ p.K k + 1 := by linarith
  · simp only [Zoom.baseOf]
    simp
    calc |a.b k w.1 1 + w.2 * a.b k w.1 4| ≤ |a.b k w.1 1| + |w.2| * |a.b k w.1 4| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |a.b k w.1 1| + 1 * |a.b k w.1 4| := by gcongr
      _ ≤ p.K k + 1 := by linarith

/-- Trajectory points restricted to the first three coordinates are the base coordinates. -/
theorem point_castSucc (b : Fin 6 → ℝ) (t : ℝ) :
    (point b t) ∘ Fin.castSucc = Zoom.baseOf b t := by
  funext i; fin_cases i <;> rfl

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- Zoomed bins of the base-corrected native polynomial are original offset bins of
the native signal. -/
theorem corr_bin_zoom (hp : p.Valid) (hlam : I.lam ≠ 0) (Gb : MvPolynomial (Fin 3) ℝ)
    (b : Fin 6 → ℝ) (t s' : ℝ) (j : ℤ) :
    ⌊eval (point (Zoom.nCoeff I.Z I.B I.lam b) ((t - I.Z.t₀) / I.Z.q))
        (Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb)) / p.N I.k ^ (-s')⌋ = j ↔
      ⌊(eval (point b t) (a.P I.k) - eval (Zoom.baseOf b t) Gb) /
        p.N I.k ^ (-(r + s'))⌋ = j := by
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  have hw := width_pos p hp I.k r
  rw [Zoom.eval_nPush (I.Z_ok hp) hlam]
  have hu : I.Z.untime ((t - I.Z.t₀) / I.Z.q) = t := by
    have := Zoom.untime_time (I.Z_ok hp) t
    simpa only [Zoom.time] using this
  rw [hu, eval_baseCalibratedTest, point_castSucc]
  have e : I.Z.a⁻¹ * (eval (point b t) (a.P I.k) - eval (Zoom.baseOf b t) Gb) /
      p.N I.k ^ (-s') =
      (eval (point b t) (a.P I.k) - eval (Zoom.baseOf b t) Gb) / p.N I.k ^ (-(r + s')) := by
    have hw' : width p I.k r = p.N I.k ^ (-r) := rfl
    rw [I.Z_a, show -(r + s') = -r + -s' by ring, Real.rpow_add hN0, ← hw']
    field_simp
  rw [e]

/-- **Zoomed caps of the base-corrected native polynomial** (`h = true`), with an
extra line event `E`. -/
theorem zoom_corr_cap (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r) (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) (hr : 0 ≤ r) (hlam : I.lam ≠ 0) {M₁ : ℝ} (hM₁ : 1 ≤ M₁)
    (hlamM : |I.lam⁻¹| ≤ M₁) (hlamM' : |I.lam| ≤ M₁) (hBle : |I.B 0| + |I.B 1| ≤ M₁)
    (Gb : MvPolynomial (Fin 3) ℝ) (hGb : Gb.totalDegree ≤ 2) {r' r'' s' C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hres : (2 * p.K I.k + M₁ + 1) * M₁ * p.N I.k ^ (-r'') ≤
      a.q I.k r * narrow p I.k r * p.N I.k ^ (-r'))
    (hvar : coeffL1 Gb * (2 + p.K I.k) ^ 2 * p.N I.k ^ (-r'') ≤ p.N I.k ^ (-(r + s')))
    (hδ1 : p.N I.k ^ (-r'') ≤ 1)
    (E : α → Prop) (hE : MeasurableSet {l | E l})
    (horig : ∀ (z : Fin 3 → ℤ) (j : ℤ), a.mu I.k {w | a.cell (p.N I.k) r'' I.k w = z ∧
      ⌊eval (a.x I.k w.1 w.2) (a.P I.k) / p.N I.k ^ (-(r + s'))⌋ = j ∧ E w.1} ≤
        ENNReal.ofReal (C₀ * p.N I.k ^ (-3 * r'')))
    (z' : Fin 3 → ℤ) (j : ℤ) :
    zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W
      {w | baseMesh (p.N I.k ^ (-r'))
          (Zoom.baseOf (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) = z' ∧
        ⌊eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2)
          (Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb)) / p.N I.k ^ (-s')⌋ = j ∧
        E w.1} ≤
      ENNReal.ofReal (27 * p.K I.k * M₁ * (4 * C₀) * p.N I.k ^ (p.d * r) *
        p.N I.k ^ (-3 * r')) := by
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  have hK1 := hp.2.2.1.1 I.k
  have hb := (hcommon I.k).1
  have hδ : 0 < p.N I.k ^ (-r'') := Real.rpow_pos_of_pos hN0 _
  have hη : 0 < p.N I.k ^ (-(r + s')) := Real.rpow_pos_of_pos hN0 _
  set S : Set (Fin 3 → ℝ) := {y | ∀ i, |y i| ≤ p.K I.k + 1} with hS
  have hF : ∀ y ∈ S, ∀ y' ∈ S, baseMesh (p.N I.k ^ (-r'')) y = baseMesh (p.N I.k ^ (-r'')) y' →
      |eval y Gb - eval y' Gb| ≤ p.N I.k ^ (-(r + s')) := by
    intro y _ y' hy' hyy
    have hd : ∀ i, |y i - y' i| ≤ p.N I.k ^ (-r'') := fun i =>
      meshBox_coordinate_distance hδ (q := baseMesh (p.N I.k ^ (-r'')) y') hyy rfl i
    have h1 := abs_eval_sub_le Gb y y' (R := p.K I.k + 1) (by linarith) hy' hδ.le hδ1 hd
    refine h1.trans (le_trans ?_ hvar)
    have hG0 := coeffL1_nonneg Gb
    have hpow : (1 + (p.K I.k + 1)) ^ Gb.totalDegree ≤ (2 + p.K I.k) ^ 2 := by
      rw [show 1 + (p.K I.k + 1) = 2 + p.K I.k by ring]
      exact pow_le_pow_right₀ (by linarith) hGb
    gcongr
  have hΦm : MeasurableSet {w : α × ℝ | ⌊eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2)
      (Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb)) / p.N I.k ^ (-s')⌋ = j ∧
        E w.1} :=
    ((measurableSet_singleton j).preimage (Int.measurable_floor.comp
      ((I.measurable_eval_line hb _).div_const _))).inter (hE.preimage measurable_fst)
  refine I.zoom_cap hp hcommon hatr hats hGm hr hlam hM₁ hlamM hlamM' hBle
    (C := 4 * C₀) (by positivity) hres
    (fun w => ⌊(eval (point (a.b I.k w.1) w.2) (a.P I.k) -
      eval (Zoom.baseOf (a.b I.k w.1) w.2) Gb) / p.N I.k ^ (-(r + s'))⌋ = j ∧ E w.1)
    (fun w => ⌊eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2)
      (Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb)) / p.N I.k ^ (-s')⌋ = j ∧
        E w.1)
    (fun w => and_congr (I.corr_bin_zoom hp hlam Gb (a.b I.k w.1) w.2 s' j) Iff.rfl)
    hΦm ?_ z'
  intro z
  have hae := ae_base_bounded hp hcommon I.k
  have h4 := offset_bin_cap_on (a.mu I.k) (fun w => Zoom.baseOf (a.b I.k w.1) w.2)
    (fun w => eval (point (a.b I.k w.1) w.2) (a.P I.k)) (fun y => eval y Gb) S (fun w => E w.1)
    hη hF (C := ENNReal.ofReal (C₀ * p.N I.k ^ (-3 * r''))) (fun z j => by
      have := horig z j
      simp only [cell_eq_baseMesh] at this
      exact this) z j
  calc a.mu I.k {w | a.cell (p.N I.k) r'' I.k w = z ∧
        (⌊(eval (point (a.b I.k w.1) w.2) (a.P I.k) - eval (Zoom.baseOf (a.b I.k w.1) w.2) Gb) /
          p.N I.k ^ (-(r + s'))⌋ = j ∧ E w.1)}
      ≤ a.mu I.k {w | baseMesh (p.N I.k ^ (-r'')) (Zoom.baseOf (a.b I.k w.1) w.2) = z ∧
          ⌊(eval (point (a.b I.k w.1) w.2) (a.P I.k) - eval (Zoom.baseOf (a.b I.k w.1) w.2) Gb) /
            p.N I.k ^ (-(r + s'))⌋ = j ∧ (Zoom.baseOf (a.b I.k w.1) w.2 ∈ S ∧ E w.1)} := by
        apply measure_mono_ae
        filter_upwards [hae] with w hw hw'
        obtain ⟨h1, h2, h3⟩ := hw'
        refine ⟨?_, h2, hw, h3⟩
        rw [← cell_eq_baseMesh]
        exact h1
    _ ≤ 4 * ENNReal.ofReal (C₀ * p.N I.k ^ (-3 * r'')) := h4
    _ = ENNReal.ofReal (4 * C₀ * p.N I.k ^ (-3 * r'')) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        ring_nf

end ZoomInput

/-- Dyadic blocks lie in unit time. -/
theorem interval_sub_unit (T : ℕ) (j : Fin (2 ^ T)) : interval T j ⊆ Icc (0 : ℝ) 1 := by
  intro t ht
  have h2 : (0 : ℝ) < 2 ^ T := by positivity
  have hj : ((j : ℕ) : ℝ) + 1 ≤ 2 ^ T := by
    have := j.2
    exact_mod_cast this
  refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
  rw [div_le_one h2]
  exact hj

/-- Lines on which three polynomials stay bounded over unit time form a measurable set. -/
theorem measurableSet_unit_bound₃ {β : α → Fin 6 → ℝ} (hβ : Measurable β)
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) ℝ) (K : ℝ) :
    MeasurableSet {l : α | ∀ t ∈ Icc (0 : ℝ) 1, |eval (point (β l) t) Q₁| ≤ K ∧
      |eval (point (β l) t) Q₂| ≤ K ∧ |eval (point (β l) t) Q₃| ≤ K} := by
  have hc : ∀ (Q : MvPolynomial (Fin 4) ℝ) (t : ℝ),
      Continuous (fun b : Fin 6 → ℝ => |eval (point b t) Q|) := fun Q t =>
    continuous_abs.comp ((MvPolynomial.continuous_eval Q).comp (continuous_point_left t))
  have hC : IsClosed {b : Fin 6 → ℝ | ∀ t ∈ Icc (0 : ℝ) 1, |eval (point b t) Q₁| ≤ K ∧
      |eval (point b t) Q₂| ≤ K ∧ |eval (point b t) Q₃| ≤ K} := by
    have : {b : Fin 6 → ℝ | ∀ t ∈ Icc (0 : ℝ) 1, |eval (point b t) Q₁| ≤ K ∧
        |eval (point b t) Q₂| ≤ K ∧ |eval (point b t) Q₃| ≤ K} =
        ⋂ t ∈ Icc (0 : ℝ) 1, ({b | |eval (point b t) Q₁| ≤ K} ∩
          ({b | |eval (point b t) Q₂| ≤ K} ∩ {b | |eval (point b t) Q₃| ≤ K})) := by
      ext b; simp
    rw [this]
    exact isClosed_biInter fun t _ =>
      (isClosed_le (hc Q₁ t) continuous_const).inter
        ((isClosed_le (hc Q₂ t) continuous_const).inter (isClosed_le (hc Q₃ t) continuous_const))
  exact hC.measurableSet.preimage hβ

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- **Common conditions of the base-corrected native polynomial** in the zoomed chart. -/
theorem zoom_corr_common (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hats : ∀ j, a.AtlasAt p R I.k (I.depth j)) (hGm : MeasurableSet I.G) (hr : 0 ≤ r)
    (hlam : I.lam ≠ 0) (Gb : MvPolynomial (Fin 3) ℝ) {Kz : ℝ} (hKz : p.K I.k ≤ Kz)
    (hsig : ∀ z ∈ I.G, ∀ t ∈ a.block I.k r I.Q,
      |eval (point (a.b I.k z.1) t) (baseCalibratedTest (a.P I.k) Gb)| ≤ Kz * width p I.k r) :
    ∀ᵐ z ∂zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W,
      (∀ t ∈ Icc (0 : ℝ) 1,
        |eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) t)
          (Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb))| ≤ Kz ∧
        |eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) t)
          (pderiv 3 (Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb)))| ≤ Kz ∧
        |eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) t)
          (pderiv 3 (pderiv 3 (Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb))))| ≤
            Kz) ∧
      Kz⁻¹ ≤ |eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) z.2)
        (pderiv 3 (Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb)))| := by
  set Pn := Zoom.nPush I.Z I.B I.lam (baseCalibratedTest (a.P I.k) Gb) with hPn
  have hK1 := hp.2.2.1.1 I.k
  have hK0 : 0 < p.K I.k := by linarith
  have hN1 : 1 ≤ p.N I.k := by linarith [hp.1 I.k]
  have hb := (hcommon I.k).1
  have hβ : Measurable (fun l => Zoom.nCoeff I.Z I.B I.lam (a.b I.k l)) :=
    I.continuous_nCoeff.measurable.comp hb
  have hZ := I.Z_ok hp
  have hw := width_pos p hp I.k r
  have hw1 : width p I.k r ≤ 1 := by
    unfold width
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hq := q_pos a I.k r
  have hmeas : MeasurableSet {z : α × ℝ | (∀ t ∈ Icc (0 : ℝ) 1,
      |eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) t) Pn| ≤ Kz ∧
      |eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) t) (pderiv 3 Pn)| ≤ Kz ∧
      |eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) t) (pderiv 3 (pderiv 3 Pn))| ≤ Kz) ∧
      Kz⁻¹ ≤ |eval (point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) z.2) (pderiv 3 Pn)|} :=
    ((measurableSet_unit_bound₃ hβ _ _ _ Kz).preimage measurable_fst).inter
      (measurableSet_le measurable_const (I.measurable_eval_line hb _).abs)
  apply ae_zoomLaw _ (I.measurable_keep hats hGm) _ _ _ hmeas
  have hP0 := (hcommon I.k).2.2.2.2.2.2.2.2.2
  filter_upwards [hP0] with w hw0 hwk
  obtain ⟨hline, hlow⟩ := hw0
  have hwG := I.keep_subset hwk
  have hblock : ∀ t ∈ Icc (0 : ℝ) 1, I.Z.untime t ∈ a.block I.k r I.Q := by
    intro t ht
    rw [I.block_eq]
    simp only [Zoom.untime]
    constructor
    · have : 0 ≤ I.Z.q * t := mul_nonneg (by rw [I.Z_q]; exact hq.le) ht.1
      linarith
    · have : I.Z.q * t ≤ I.Z.q := by
        have := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ I.Z.q by rw [I.Z_q]; exact hq.le)
        linarith
      linarith
  have hunit : ∀ t ∈ Icc (0 : ℝ) 1, I.Z.untime t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    interval_sub_unit _ _ (hblock t ht)
  refine ⟨fun t ht => ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [zoomTime]
    rw [hPn, Zoom.eval_nPush hZ hlam, abs_mul, I.Z_a, abs_of_pos (inv_pos.mpr hw)]
    have := hsig w hwG _ (hblock t ht)
    calc (width p I.k r)⁻¹ * |eval (point (a.b I.k w.1) (I.Z.untime t))
          (baseCalibratedTest (a.P I.k) Gb)|
        ≤ (width p I.k r)⁻¹ * (Kz * width p I.k r) :=
          mul_le_mul_of_nonneg_left this (inv_pos.mpr hw).le
      _ = Kz := by field_simp
  · simp only [zoomTime]
    rw [hPn, Zoom.eval_pderiv_nPush hZ hlam, pderiv_baseCalibratedTest]
    exact ((hline _ (hunit t ht)).2.1).trans hKz
  · simp only [zoomTime]
    rw [hPn, Zoom.eval_pderiv_pderiv_nPush hZ hlam, second_pderiv_baseCalibratedTest, abs_mul,
      I.Z_a, abs_of_pos hw]
    have h3 := (hline _ (hunit t ht)).2.2
    calc width p I.k r * |eval (point (a.b I.k w.1) (I.Z.untime t))
          (pderiv 3 (pderiv 3 (a.P I.k)))| ≤ 1 * p.K I.k :=
          mul_le_mul hw1 h3 (abs_nonneg _) zero_le_one
      _ ≤ Kz := by linarith
  · simp only [zoomTime]
    rw [hPn, Zoom.eval_pderiv_nPush hZ hlam, pderiv_baseCalibratedTest]
    have hu : I.Z.untime ((w.2 - I.Z.t₀) / I.Z.q) = w.2 := by
      have := Zoom.untime_time hZ w.2
      simpa only [Zoom.time] using this
    rw [hu]
    exact le_trans (inv_anti₀ hK0 hKz) hlow

end ZoomInput

end

end Submission.Lib.K4ContactTransfer
