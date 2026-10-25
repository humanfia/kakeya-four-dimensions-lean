/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ParentNativeSheets.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.NativeTwoPass
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedParentSupport
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentNativePartition

/-!
# Native sheets of one true parent of the prepared model

Accepted o253 (`k4_general_parent_projected_layers`) normalizes the full original incidence law
of a true parent `(k, s, i)` by its support zoom: `parentNativeLaw` (the conditional law on
`B × block`), `parentSupportZoom` (hidden coordinate unscaled), the chart bounds
(`parentNativeLaw_good`), the small base (`parentNativeLaw_small`), the transported base caps
(`parentNativeLaw_meshCap`, `rootMeshCap_nativePoint`) and the filling bound
(`parentNativeLaw_filling`).

`native_sheets_nativeLaw` is `native_sheets_two_pass` for a law of native points.
`parent_native_sheets` applies it to the zoomed parent law: the crude cap is accepted o253's
parent filling (a fixed power), and the native-bin cap is `442368 K⁶` (`parentBinCap`), because
the original parent mass is at least `a^d q³ g / K²` while the zoom's Jacobian is
`16384 K³ q³ g`. The result: two native sheets per parent (by the sign of `∂_w F`), on complex
balls of radius `4ρ`, `ρ ≥ (2K · 442368 K⁶)^(-n)`, around the zoomed base of every incidence of
the parent outside a set of relative mass `(2K H₀)^(-A) + (2K B)^(-A)`, within `32 (2K)⁹ a` of
the native signal.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open scoped ENNReal

noncomputable section

/-! ### Laws of native points -/

theorem snoc_rootBase (p : NativePoint) :
    (Fin.snoc (rootBaseCoordinates p) (p 3) : Fin 4 → ℝ) = fun i => p i := by
  funext i; fin_cases i <;> rfl

theorem abs_rootBase_le {p : NativePoint} {K : ℝ} (h : ‖nativeBase p‖ ≤ K) (i : Fin 3) :
    |rootBaseCoordinates p i| ≤ K := by
  have : rootBaseCoordinates p i = nativeBase p i := by fin_cases i <;> rfl
  rw [this, ← Real.norm_eq_abs]
  exact (PiLp.norm_apply_le (nativeBase p) i).trans h

theorem nchart_of_goodSet {K a : ℝ} {F S : MvPolynomial (Fin 4) ℝ} {p : NativePoint}
    (hp : p ∈ goodSet K a F S) : NChart K a F S (rootBaseCoordinates p) (p 3) := by
  obtain ⟨hn, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  refine ⟨abs_rootBase_le hn, ?_, ?_, ?_, h4, ?_, ?_, h7⟩ <;> rw [snoc_rootBase]
  · exact h1
  · exact h2
  · exact h3
  · exact h5
  · exact h6

theorem measurable_coord3 : Measurable fun p : NativePoint => p 3 := by
  fun_prop

/-- **Native sheets for a law of native points.** -/
theorem native_sheets_nativeLaw :
    ∃ α β : ℕ, 1 ≤ β ∧ ∀ (A : ℕ) (K H₀ B a σ₀ σ₁ : ℝ), 2 ≤ K → 1 ≤ H₀ → 1 ≤ B → 0 < a → a ≤ 1 →
      0 < σ₀ → 0 < σ₁ → (K * H₀) ^ (α * A + β) * σ₀ ≤ 1 →
      (K * H₀) ^ (α * A + β) * σ₁ ≤ a → (K * B) ^ (α * A + β) * σ₁ ≤ 1 →
      ∀ (F S : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      ∀ (ν : Measure NativePoint), IsProbabilityMeasure ν → RootMeshCap ν H₀ σ₀ →
      (∀ (q : Fin 3 → ℤ) (x₀ : ℤ), ν {p | Submission.Lib.K4MovingMeshBoxes.baseMesh σ₁
          (rootBaseCoordinates p) = q ∧ ⌊value S p / a⌋ = x₀} ≤
          ENNReal.ofReal (B * σ₁ ^ 3)) →
      (∀ᵐ p ∂ν, p ∈ goodSet K a F S) →
      ∃ (ρ : ℝ) (R : MvPolynomial (Fin 4) ℂ) (g : Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
        (E : Set NativePoint),
        ((K * B) ^ (α * A + β))⁻¹ ≤ ρ ∧ ρ ≤ 1 ∧ R ≠ 0 ∧ R.totalDegree ≤ 4 ∧ MeasurableSet E ∧
        ν E ≤ ENNReal.ofReal (((K * H₀) ^ A)⁻¹ + ((K * B) ^ A)⁻¹) ∧
        ∀ᵐ p ∂ν, p ∉ E →
          SheetOn R (g (branch F (rootBaseCoordinates p) (p 3))) (toEuc (rootBaseCoordinates p))
            (4 * ρ) ((K * B) ^ (α * A + β)) ∧
          |value S p - (g (branch F (rootBaseCoordinates p) (p 3))
            (emb (toEuc (rootBaseCoordinates p)))).re| ≤ 32 * K ^ 9 * a := by
  obtain ⟨α, β, hβ, h2⟩ := native_sheets_two_pass
  refine ⟨α, β, hβ, ?_⟩
  intro A K H₀ B a σ₀ σ₁ hK hH₀ hB ha ha1 hσ₀ hσ₁ hm₀ hm₁ hm₂ F S hF hS ν hν hcap₀ hcapS hgood
  have hcapS' : ∀ (q : Fin 3 → ℤ) (x₀ : ℤ), ν {p | (fun i => ⌊rootBaseCoordinates p i / σ₁⌋) = q ∧
      ⌊eval (Fin.snoc (rootBaseCoordinates p) (p 3)) S / a⌋ = x₀} ≤
      ENNReal.ofReal (B * σ₁ ^ 3) := by
    intro q x₀
    simp_rw [snoc_rootBase]
    exact hcapS q x₀
  obtain ⟨ρ, R, g, E, hρ, hρ1, hR, hRd, hEm, hE, hae⟩ := h2 A K H₀ B a σ₀ σ₁ hK hH₀ hB ha ha1
    hσ₀ hσ₁ hm₀ hm₁ hm₂ F S hF hS NativePoint ν hν rootBaseCoordinates (fun p => p 3)
    measurable_rootBaseCoordinates measurable_coord3 (fun q => hcap₀ q) hcapS'
    (hgood.mono fun p hp => nchart_of_goodSet hp)
  refine ⟨ρ, R, g, E, hρ, hρ1, hR, hRd, hEm, hE, ?_⟩
  filter_upwards [hae] with p hp hpE
  obtain ⟨h1, h2⟩ := hp hpE
  rw [snoc_rootBase] at h2
  exact ⟨h1, h2⟩

/-! ### One true parent -/

/-- The native-bin cell constant of a full parent in its support zoom. -/
def parentBinCap (K : ℝ) : ℝ := 442368 * K ^ 6

/-- The zoomed native point of an incidence of a parent. -/
def parentZoomPoint {α : Type} [MeasurableSpace α] (p : Parameters) (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) (z : α × ℝ) : NativePoint :=
  (a.parentSupportZoom p k s i).nativePoint (a.nativePoint k z)

theorem parentBinCap_ge (K : ℝ) (hK : 1 ≤ K) : 1 ≤ parentBinCap K := by
  unfold parentBinCap
  have : (1 : ℝ) ≤ K ^ 6 := one_le_pow₀ hK
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Native sheets of one true parent.** -/
theorem parent_native_sheets :
    ∃ αc βc : ℕ, 1 ≤ βc ∧ ∀ (A : ℕ) {α : Type} [MeasurableSpace α] (p : Parameters), p.Valid →
      ∀ a : PreparedModel α, a.Common p → ∀ (R : ℝ) (k : ℕ) (s : ℝ), 0 ≤ s →
      a.AtlasAt p R k s → ∀ i : Fin (a.n k s), ∀ δ₀ σ₀ δ₁ σ₁ : ℝ,
      0 < δ₀ → 0 < σ₀ → 0 < δ₁ → 0 < σ₁ →
      (∀ e, (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * δ₀) ≤ σ₀) →
      (∀ e, (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * δ₁) ≤ σ₁) →
      (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ (αc * A + βc) * σ₀ ≤ 1 →
      (2 * p.K k * parentFilling (p.K k) (width p k s)) ^ (αc * A + βc) * σ₁ ≤ width p k s →
      (2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc) * σ₁ ≤ 1 →
      (∀ q : Fin 3 → ℤ, a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₀
          (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q} ≤
        ENNReal.ofReal ((4 * p.K k + 2) * p.K k * δ₀ ^ 3)) →
      (∀ (q : Fin 3 → ℤ) (x₀ : ℤ), a.mu k {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₁
          (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q ∧
          ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋ = x₀} ≤
        ENNReal.ofReal (p.K k * width p k s ^ p.d * δ₁ ^ 3)) →
      ∃ (ρ : ℝ) (Rel : MvPolynomial (Fin 4) ℂ) (g : Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
        (E : Set (α × ℝ)),
        ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc))⁻¹ ≤ ρ ∧ ρ ≤ 1 ∧ Rel ≠ 0 ∧
        Rel.totalDegree ≤ 4 ∧ MeasurableSet E ∧
        a.mu k (a.parentSet k s i ∩ E) ≤ a.mu k (a.parentSet k s i) *
          ENNReal.ofReal (((2 * p.K k * parentFilling (p.K k) (width p k s)) ^ A)⁻¹ +
            ((2 * p.K k * parentBinCap (p.K k)) ^ A)⁻¹) ∧
        ∀ᵐ z ∂a.mu k, z ∈ a.parentSet k s i → z ∉ E →
          SheetOn Rel (g (branch ((a.parentSupportZoom p k s i).push (a.F k s i))
              (rootBaseCoordinates (parentZoomPoint p a k s i z))
              (parentZoomPoint p a k s i z 3)))
            (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))) (4 * ρ)
            ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc)) ∧
          |eval (a.x k z.1 z.2) (a.P k) -
            (g (branch ((a.parentSupportZoom p k s i).push (a.F k s i))
              (rootBaseCoordinates (parentZoomPoint p a k s i z))
              (parentZoomPoint p a k s i z 3))
              (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))))).re| ≤
            32 * (2 * p.K k) ^ 9 * width p k s := by
  obtain ⟨αc, βc, hβc, hnat⟩ := native_sheets_nativeLaw
  refine ⟨αc, βc, hβc, ?_⟩
  intro A α _ p hp a hcommon R k s hs hatlas i δ₀ σ₀ δ₁ σ₁ hδ₀ hσ₀ hδ₁ hσ₁ hres₀ hres₁ hm₀ hm₁
    hm₂ hcap₀ hcapS
  -- notation
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hK0 : 0 < p.K k := lt_of_lt_of_le zero_lt_one hK
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have ha1 : width p k s ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k]) (by linarith)
  have hq : 0 < a.q k s := by unfold PreparedModel.q; positivity
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have : IsFiniteMeasure (a.mu k) := a.incidence_finite p hcommon k
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = a.parentSupportZoom p k s i := ⟨_, rfl⟩
  have hZ : Z.Ok := hZdef ▸ a.parentSupportZoom_ok p hp k s i
  have haZ : Z.a = 1 := hZdef ▸ a.parentSupportZoom_hidden p k s i
  set E₀ := a.parentSet k s i with hE₀
  have hE₀m : MeasurableSet E₀ := a.measurableSet_parentSet p hatlas i
  have hE₀pos : 0 < a.mu k E₀ := a.original_parent_mass_pos p hp hatlas i
  have hE₀top : a.mu k E₀ ≠ ⊤ := measure_ne_top _ _
  have hnp : Measurable (a.nativePoint k) := a.measurable_nativePoint k (hcommon k).1
  set ν₀ := a.parentNativeLaw k s i with hν₀
  haveI : IsProbabilityMeasure ν₀ := a.parentNativeLaw_probability p hp hcommon hatlas i
  set ν := Measure.map Z.nativePoint ν₀ with hν
  haveI : IsProbabilityMeasure ν := inferInstance
  set H₀ := parentFilling (p.K k) (width p k s) with hH₀
  have hH₀1 : 1 ≤ H₀ := by
    have h := native_power_le_parentFilling hK ha ha1
    have : (1 : ℝ) ≤ (2 * p.K k) ^ 16 := one_le_pow₀ (by linarith)
    linarith
  have hB1 := parentBinCap_ge (p.K k) hK
  -- the crude cap
  have hcap₀' : RootMeshCap ν H₀ σ₀ := by
    have h1 := a.parentNativeLaw_meshCap p hp hcommon hatlas i hcap₀
    have h2 := Z.rootMeshCap_nativePoint (μ := ν₀) hZ hδ₀ hσ₀ (by positivity)
      (hZdef ▸ hres₀) h1
    have hfill := a.parentNativeLaw_filling p hp hcommon hs hatlas i
    rw [← hZdef] at hfill
    exact RootMeshCap.mono h2 hfill hσ₀.le
  -- the native-bin cap
  set m := (a.mu k E₀).toReal with hm
  have hmass : width p k s ^ p.d * a.q k s ^ 3 * narrow p k s / p.K k ^ 2 ≤ m :=
    a.original_parent_mass_toReal_lower p hp hcommon hatlas i
  have hmpos : 0 < m := ENNReal.toReal_pos hE₀pos.ne' hE₀top
  have hcapν₀ : ∀ (q : Fin 3 → ℤ) (x₀ : ℤ), ν₀ {x | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₁
      (rootBaseCoordinates x) = q ∧ ⌊value (a.P k) x / width p k s⌋ = x₀} ≤
      ENNReal.ofReal (p.K k * width p k s ^ p.d / m * δ₁ ^ 3) := by
    intro q x₀
    have hmeasS : MeasurableSet {x : NativePoint | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₁
        (rootBaseCoordinates x) = q ∧ ⌊value (a.P k) x / width p k s⌋ = x₀} := by
      refine (measurableSet_eq_fun ((Submission.Lib.K4AffineMeshCaps.measurable_baseMesh δ₁).comp
        measurable_rootBaseCoordinates) measurable_const).inter ?_
      exact measurableSet_eq_fun (((continuous_value (a.P k)).measurable.div_const _).floor)
        measurable_const
    rw [hν₀, PreparedModel.parentNativeLaw, conditionalNativeLaw, Measure.map_apply hnp hmeasS,
      cond_apply hE₀m]
    have hsub : E₀ ∩ a.nativePoint k ⁻¹' {x | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₁
        (rootBaseCoordinates x) = q ∧ ⌊value (a.P k) x / width p k s⌋ = x₀} ⊆
        {z | Submission.Lib.K4MovingMeshBoxes.baseMesh δ₁
          (Submission.Lib.K4MovingMeshBoxes.basePoint (a.b k z.1) z.2) = q ∧
          ⌊eval (a.x k z.1 z.2) (a.P k) / width p k s⌋ = x₀} := by
      intro z hz
      obtain ⟨-, h1, h2⟩ := hz
      refine ⟨?_, ?_⟩
      · rw [a.nativePoint_base k z] at h1; exact h1
      · rw [← a.nativePoint_value k z]; exact h2
    have hinv : (a.mu k E₀)⁻¹ = ENNReal.ofReal m⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hmpos, hm, ENNReal.ofReal_toReal hE₀top]
    calc (a.mu k E₀)⁻¹ * a.mu k (E₀ ∩ a.nativePoint k ⁻¹' _)
        ≤ (a.mu k E₀)⁻¹ * ENNReal.ofReal (p.K k * width p k s ^ p.d * δ₁ ^ 3) :=
          mul_le_mul' le_rfl ((measure_mono hsub).trans (hcapS q x₀))
      _ = ENNReal.ofReal (p.K k * width p k s ^ p.d / m * δ₁ ^ 3) := by
          rw [hinv, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have hcapν : ∀ (q : Fin 3 → ℤ) (x₀ : ℤ), ν {x | Submission.Lib.K4MovingMeshBoxes.baseMesh σ₁
      (rootBaseCoordinates x) = q ∧ ⌊value (Z.push (a.P k)) x / width p k s⌋ = x₀} ≤
      ENNReal.ofReal (parentBinCap (p.K k) * σ₁ ^ 3) := by
    intro q x₀
    have hmeasS : MeasurableSet {x : NativePoint | Submission.Lib.K4MovingMeshBoxes.baseMesh σ₁
        (rootBaseCoordinates x) = q ∧ ⌊value (Z.push (a.P k)) x / width p k s⌋ = x₀} := by
      refine (measurableSet_eq_fun ((Submission.Lib.K4AffineMeshCaps.measurable_baseMesh σ₁).comp
        measurable_rootBaseCoordinates) measurable_const).inter ?_
      exact measurableSet_eq_fun (((continuous_value _).measurable.div_const _).floor)
        measurable_const
    rw [hν, Measure.map_apply Z.measurable_nativePoint hmeasS]
    have hset : Z.nativePoint ⁻¹' {x | Submission.Lib.K4MovingMeshBoxes.baseMesh σ₁
        (rootBaseCoordinates x) = q ∧ ⌊value (Z.push (a.P k)) x / width p k s⌋ = x₀} =
        {x | Submission.Lib.K4MovingMeshBoxes.baseMesh σ₁
          (Submission.Lib.K4AffineMeshCaps.affineBase Z.baseMatrix Z.baseShift
            (rootBaseCoordinates x)) = q ∧
          ⌊value (a.P k) x / width p k s⌋ = x₀} := by
      ext x
      simp only [mem_preimage, mem_setOf_eq, Z.nativePoint_base,
        Z.value_push_nativePoint hZ, haZ, inv_one, one_mul]
    rw [hset]
    have h := Submission.Lib.K4AffineMeshCaps.affine_mesh_cell_cap ν₀ rootBaseCoordinates
      (fun x => ⌊value (a.P k) x / width p k s⌋ = x₀) Z.baseMatrix Z.baseShift
      (Z.baseMatrix_det_ne_zero hZ) hδ₁ hσ₁ (by positivity) (hZdef ▸ hres₁)
      (fun q' => hcapν₀ q' x₀) q
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    -- the constant
    have hjac : |Z.baseMatrix.det|⁻¹ = 16384 * p.K k ^ 3 * a.q k s ^ 3 * narrow p k s := by
      rw [hZdef]; exact a.parentSupportZoom_jacobian p hp k s i
    rw [hjac]
    have hwd : 0 < width p k s ^ p.d := Real.rpow_pos_of_pos ha _
    have hkey : p.K k * width p k s ^ p.d / m * (16384 * p.K k ^ 3 * a.q k s ^ 3 *
        narrow p k s) ≤ 16384 * p.K k ^ 6 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hmpos]
      have h1 : width p k s ^ p.d * a.q k s ^ 3 * narrow p k s ≤ p.K k ^ 2 * m := by
        rw [div_le_iff₀ (by positivity)] at hmass
        linarith
      calc p.K k * width p k s ^ p.d * (16384 * p.K k ^ 3 * a.q k s ^ 3 * narrow p k s)
          = 16384 * p.K k ^ 4 * (width p k s ^ p.d * a.q k s ^ 3 * narrow p k s) := by ring
        _ ≤ 16384 * p.K k ^ 4 * (p.K k ^ 2 * m) := by gcongr
        _ = 16384 * p.K k ^ 6 * m := by ring
    calc 27 * (p.K k * width p k s ^ p.d / m) * (16384 * p.K k ^ 3 * a.q k s ^ 3 *
          narrow p k s) * σ₁ ^ 3
        = 27 * (p.K k * width p k s ^ p.d / m * (16384 * p.K k ^ 3 * a.q k s ^ 3 *
          narrow p k s)) * σ₁ ^ 3 := by ring
      _ ≤ 27 * (16384 * p.K k ^ 6) * σ₁ ^ 3 := by gcongr
      _ = parentBinCap (p.K k) * σ₁ ^ 3 := by unfold parentBinCap; ring
  -- the chart bounds in the zoom
  have hFdeg : (a.F k s i).totalDegree ≤ 2 := (hatlas.2.2.2.2.1 i).2.2.2.2.1
  have hPdeg : (a.P k).totalDegree ≤ 2 := (hcommon k).2.2.2.2.2.2.2.1
  have hgoodν : ∀ᵐ x ∂ν, x ∈ goodSet (2 * p.K k) (width p k s) (Z.push (a.F k s i))
      (Z.push (a.P k)) := by
    have hgood₀ := a.parentNativeLaw_good p hp hcommon hatlas i
    have hsmall₀ := a.parentNativeLaw_small p hp hcommon hatlas i
    rw [← hZdef] at hsmall₀
    rw [hν]
    apply (ae_map_iff Z.measurable_nativePoint.aemeasurable (measurableSet_goodSet _ _ _ _)).mpr
    filter_upwards [hgood₀, hsmall₀] with x hx hxs
    exact Z.goodSet_nativePoint hZ haZ (a.F k s i) (a.P k) hFdeg hPdeg hx
      ((norm_nativeBase_le_one_of_small hxs).trans (by linarith))
  -- the sheets
  obtain ⟨ρ, Rel, g, Eν, hρ, hρ1, hRel, hReld, hEνm, hEν, hae⟩ := hnat A (2 * p.K k) H₀
    (parentBinCap (p.K k)) (width p k s) σ₀ σ₁ (by linarith) hH₀1 hB1 ha ha1 hσ₀ hσ₁ hm₀ hm₁ hm₂
    (Z.push (a.F k s i)) (Z.push (a.P k)) ((Z.push_degree _).trans hFdeg)
    ((Z.push_degree _).trans hPdeg) ν inferInstance hcap₀' hcapν hgoodν
  have hfm : Measurable (fun z => Z.nativePoint (a.nativePoint k z)) :=
    Z.measurable_nativePoint.comp hnp
  refine ⟨ρ, Rel, g, (fun z => Z.nativePoint (a.nativePoint k z)) ⁻¹' Eν, hρ, hρ1, hRel, hReld,
    hfm hEνm, ?_, ?_⟩
  · -- the deleted mass
    have h1 : ν Eν = (a.mu k E₀)⁻¹ * a.mu k (E₀ ∩ (fun z => Z.nativePoint (a.nativePoint k z)) ⁻¹' Eν) := by
      rw [hν, Measure.map_apply Z.measurable_nativePoint hEνm, hν₀,
        PreparedModel.parentNativeLaw, conditionalNativeLaw,
        Measure.map_apply hnp (Z.measurable_nativePoint hEνm), cond_apply hE₀m]
      rfl
    have h2 : a.mu k (E₀ ∩ (fun z => Z.nativePoint (a.nativePoint k z)) ⁻¹' Eν) =
        a.mu k E₀ * ν Eν := by
      rw [h1, ← mul_assoc, ENNReal.mul_inv_cancel hE₀pos.ne' hE₀top, one_mul]
    rw [h2]
    exact mul_le_mul' le_rfl hEν
  · -- the sheets at the incidences
    have hae₀ : ∀ᵐ x ∂ν₀, Z.nativePoint x ∉ Eν →
        SheetOn Rel (g (branch (Z.push (a.F k s i)) (rootBaseCoordinates (Z.nativePoint x))
            (Z.nativePoint x 3))) (toEuc (rootBaseCoordinates (Z.nativePoint x))) (4 * ρ)
            ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc)) ∧
          |value (Z.push (a.P k)) (Z.nativePoint x) -
            (g (branch (Z.push (a.F k s i)) (rootBaseCoordinates (Z.nativePoint x))
              (Z.nativePoint x 3)) (emb (toEuc (rootBaseCoordinates (Z.nativePoint x))))).re| ≤
            32 * (2 * p.K k) ^ 9 * width p k s :=
      ae_of_ae_map Z.measurable_nativePoint.aemeasurable hae
    have hae₁ : ∀ᵐ z ∂cond (a.mu k) E₀, Z.nativePoint (a.nativePoint k z) ∉ Eν →
        SheetOn Rel (g (branch (Z.push (a.F k s i))
            (rootBaseCoordinates (Z.nativePoint (a.nativePoint k z)))
            (Z.nativePoint (a.nativePoint k z) 3)))
            (toEuc (rootBaseCoordinates (Z.nativePoint (a.nativePoint k z)))) (4 * ρ)
            ((2 * p.K k * parentBinCap (p.K k)) ^ (αc * A + βc)) ∧
          |value (Z.push (a.P k)) (Z.nativePoint (a.nativePoint k z)) -
            (g (branch (Z.push (a.F k s i))
              (rootBaseCoordinates (Z.nativePoint (a.nativePoint k z)))
              (Z.nativePoint (a.nativePoint k z) 3))
              (emb (toEuc (rootBaseCoordinates (Z.nativePoint (a.nativePoint k z)))))).re| ≤
            32 * (2 * p.K k) ^ 9 * width p k s := by
      have := hae₀
      rw [hν₀, PreparedModel.parentNativeLaw, conditionalNativeLaw] at this
      exact ae_of_ae_map hnp.aemeasurable this
    have habs : (a.mu k).restrict E₀ ≪ cond (a.mu k) E₀ :=
      Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr hE₀top)
    have hae₂ := (ae_restrict_iff' hE₀m).mp (habs.ae_le hae₁)
    filter_upwards [hae₂] with z hz hzE hzn
    obtain ⟨h1, h2⟩ := hz hzE hzn
    rw [Z.value_push_nativePoint hZ, haZ, inv_one, one_mul, a.nativePoint_value k z] at h2
    simp only [parentZoomPoint, ← hZdef]
    exact ⟨h1, h2⟩

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
