/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalGlobalFilling.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalGlobalPreparation
import Submission.Obl.k4_scalar_graph_residual_discovery.GlobalStripFilling
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalRoundedSupport
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryScaleGrid
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldGlobalFilling

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal NNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Lib.K4ContinuousKakeya
open Submission.Obl.k4_initial_horizon_bound
open WangZahlLot.Obl.wz_slab_local_linearity

namespace ScalarData

noncomputable section

/-- The literal original caps, finite mesh counts, long entries and final
global floors construct the complete GLOBAL filling certificate.
No filling, breadth or hereditary-list oracle is assumed. -/
theorem prepData.original_global_filling_of_floors {D : ScalarData}
    {H₀ Hg : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ Eg : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    {L B : ℝ} {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    (hprep : D.prepData H₀ θ E₀) (hgraph : D.graphData E₀ L Hg B G Eg)
    (hbase : D.base) (hcaps : D.caps) (hN : ∀ k, 2 ≤ D.N k)
    (hd : 0 ≤ D.d) (hd₁ : D.d ≤ 1)
    (J C : ℕ) (hJ : 1 ≤ J) (Cmk : ℝ) (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 2 Cmk) :
    ∀ T : ℝ, 1 < T → ∀ᶠ k in atTop, ∀ (g : Fin (D.W k)) (a τ : ℝ),
      T⁻¹ ≤ a → a + C + 1 / (D.prepMesh hprep k : ℝ) ≤ T →
      T⁻¹ ≤ τ → τ ≤ T →
      let u := fun i : Fin (C * J + 1) => upperGridExponent (D.prepMesh hprep k) (a + (i : ℝ) / J)
      let β := fun i => D.N k ^ (-u i)
      let ρ := D.N k ^ (-a)
      let b := D.N k ^ (-B)
      let ζ := D.N k ^ (-(C : ℝ))
      let μ := (D.ρ k g).restrict (E₀ k g)
      let old := (D.ρ k g).restrict (Eg k g)
      ∀ (P R : Set ScalarIncidence), MeasurableSet P → MeasurableSet R → R ⊆ P → P ⊆ Eg k g →
      (∀ i, b ≤ β i) →
      (∀ i j, ∀ z ∈ R, μ {p | D.phys k (u i) p = D.phys k (u i) z ∧
        D.phys k (u j) p = D.phys k (u j) z} ≠ 0) →
      ∀ (Kbase Kgeom Lfill ηdur ηstrip : ℝ) (ηstate : ℝ≥0∞),
      0 < Kbase → 0 < Kgeom → 0 < Lfill → 0 < ηdur → 0 < ηstrip →
      3 * H₀ k ≤ Kbase → H₀ k / (ηdur * ηstrip) ≤ Kbase →
      200 * Cmk * Kbase ^ 4 * (1 + H₀ k) ^ 2 ≤ Lfill * D.N k ^ (-τ) → Lfill ≤ Kgeom →
      ηstate ≠ 0 → ηstate ≠ ∞ →
      5 * (ENNReal.ofReal (Hg k) / ηstate) * ENNReal.ofReal (D.K k * D.N k ^ (-D.S * τ)) ≤ 1 / 2 →
      (∀ w, R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' {w} = ∅ ∨
        ηstate * old ((fun z => cell b (scalarPosition z)) ⁻¹' {w}) <
          μ (R ∩ (fun z => cell b (scalarPosition z)) ⁻¹' {w})) →
      ∀ row : (Fin 3 → ℤ) → Fin 2 → ℝ,
      (∀ z ∈ R, ∀ i : Fin (C * J + 1), ENNReal.ofReal (ηdur * ρ) ≤ incidenceDuration
        (P ∩ stripRecord b ρ (ρ * powerWidth (D.N k) J i) row ⁻¹'
          {stripRecord b ρ (ρ * powerWidth (D.N k) J i) row z}) z.1) →
      (∀ (i : Fin (C * J + 1)) vj, R ∩ stripRecord b ρ (ρ * powerWidth (D.N k) J i) row ⁻¹' {vj} = ∅ ∨
        ENNReal.ofReal ηstrip * μ (P ∩ stripRecord b ρ (ρ * powerWidth (D.N k) J i) row ⁻¹' {vj}) <
          μ (R ∩ stripRecord b ρ (ρ * powerWidth (D.N k) J i) row ⁻¹' {vj})) →
      ∀ A : ℝ, (∀ v, 5 + |row v 0| + |row v 1| ≤ A) →
      18 * (A + 1) * (13824 * H₀ k ^ 7) ≤ Kgeom → 2 * A + 2 ≤ Kgeom →
      ∃ filling : Zoom.GlobalWorldFilling R ρ b ζ D.d,
        filling.row = row ∧ filling.Q = D.N k ^ (1 / (J : ℝ)) ∧
          filling.K = Kgeom ∧ filling.A = A ∧ filling.B = 13824 * H₀ k ^ 7 := by
  classical
  obtain ⟨M, hM, hmesh, hhered⟩ := hprep.original_rounded_assigned_support hN hd hd₁
  subst M
  have hpoints := (Classical.choose_spec hprep.2).2 2 (by norm_num)
  intro T hT
  filter_upwards [hhered T hT, hgraph.2.2 T hT, hcaps T hT,
    hprep.original_density_caps, hpoints] with k hh hg hc hden hpt
  intro g a τ halo hahi hτlo hτhi
  dsimp only
  intro P R hP hR hRP hPE hbβ hpositive Kbase Kgeom Lfill ηdur ηstrip ηstate
    hKbase hKgeom hLfill hηdur hηstrip hU hprior hfillbudget hLgeom hη₀ hηt hsmall hstate
    row hlong hstrip A hA hbudget hoverlap
  let ρ := D.N k ^ (-a)
  let b := D.N k ^ (-B)
  let ζ := D.N k ^ (-(C : ℝ))
  let μ := (D.ρ k g).restrict (E₀ k g)
  let old := (D.ρ k g).restrict (Eg k g)
  let u := fun i : Fin (C * J + 1) => upperGridExponent (D.prepMesh hprep k) (a + (i : ℝ) / J)
  let β := fun i => D.N k ^ (-u i)
  let scales := fun i : Fin (C * J + 1) => powerWidth (D.N k) J i
  let grid := Set.range scales
  haveI : IsFiniteMeasure (D.ρ k g) := ⟨lt_top_iff_ne_top.mpr (rho_finite hbase k g)⟩
  haveI := (hbase k).2.2.1 g |>.1
  haveI : IsFiniteMeasure (θ k g) := isFiniteMeasure_of_le (D.ν k g) (hpt.2 g).1
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hN₁ : 1 < D.N k := by linarith [hN k]
  have hH : 1 ≤ H₀ k := hprep.1.1 k
  have hH₀ : 0 ≤ H₀ k := by linarith
  have ha : 0 < a := (inv_pos.mpr (by linarith : 0 < T)).trans_le halo
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hN₀ _
  have hρ₁ : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN₁.le (by linarith)
  have hb : 0 < b := Real.rpow_pos_of_pos hN₀ _
  have hζ : 0 < ζ := Real.rpow_pos_of_pos hN₀ _
  have hζ₁ : ζ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN₁.le (by simp [ζ])
  have hw (i : Fin (C * J + 1)) := discovery_prepared_scale hN₁.le ha.le
    (hM k).1 hJ (hM k).2 i
  have hscales (i : Fin (C * J + 1)) : ζ ≤ scales i ∧ scales i ≤ 1 :=
    discovery_scale_bounds hN₁.le hJ i
  have hspos (i : Fin (C * J + 1)) : 0 < scales i := Real.rpow_pos_of_pos hN₀ _
  have hbρ : b ≤ ρ := (hbβ ⟨0, by omega⟩).trans
    ((hw ⟨0, by omega⟩).2.2.1.trans_eq (by
      simp only [powerWidth, Fin.val_zero, Nat.cast_zero, zero_div, neg_zero, Real.rpow_zero, mul_one]
      rfl))
  have hEgprep : Eg k g ⊆ E₀ k g := (hg.2 g).2.1
  have hRprep : R ⊆ E₀ k g := hRP.trans (hPE.trans hEgprep)
  have hcoeff : ∀ p ∈ P, ∀ e, |p.1.2 e| ≤ H₀ k :=
    fun p hp => ((hpt.2 g).2.2.2.1 p (hEgprep (hPE hp))).2
  have htime : ∀ p ∈ P, p.2 ∈ Icc (0 : ℝ) 1 :=
    fun p hp => ((hpt.2 g).2.2.2.1 p (hEgprep (hPE hp))).1
  have hcur : μ.restrict R ≤ old := by
    dsimp only [μ, old]
    rw [Measure.restrict_restrict_of_subset hRprep]
    exact Measure.restrict_mono_set _ (hRP.trans hPE)
  let U : ℝ≥0 := ⟨H₀ k, hH₀⟩
  have hUdom : μ.restrict R ≤ U • (θ k g).prod volume := by
    have hdom := (Measure.restrict_le_self : μ.restrict R ≤ μ).trans (hden g).1
    rw [← Measure.coe_nnreal_smul, ENNReal.coe_nnreal_eq]
    exact hdom
  have hprod : ∀ S : Set ScalarIncidence, MeasurableSet S → S ⊆ P →
      ((θ k g).prod volume) S ≤ ENNReal.ofReal (H₀ k) * μ S :=
    fun S hS hSP => (hden g).2 S hS (hSP.trans (hPE.trans hEgprep))
  have hpalette : ∀ c : ℤ, scalarPaletteMeasure (D.π k g) (D.N k ^ (-τ)) {c} ≤
      ENNReal.ofReal (D.K k * D.N k ^ (-D.S * τ)) := by
    intro c
    rw [scalarPaletteMeasure_singleton]
    exact (hc g τ τ τ hτlo hτhi hτlo hτhi hτlo hτhi).1 c
  have hgraphcap : ∀ (w : Fin 3 → ℤ) (c : ℤ),
      old {z | cell b (scalarPosition z) = w ∧ (⌊z.1.2 1 / D.N k ^ (-τ)⌋ : ℤ) = c} ≤
        ENNReal.ofReal (Hg k) * old ((fun z => cell b (scalarPosition z)) ⁻¹' {w}) *
          scalarPaletteMeasure (D.π k g) (D.N k ^ (-τ)) {c} := by
    intro w c
    rw [scalarPaletteMeasure_singleton]
    exact (hg.2 g).2.2.2.2 τ hτlo hτhi w c
  have hfill : ∀ r ∈ grid, ∀ v j,
      (∃ z ∈ R, assignedCell ρ b z = v ∧ assignedNormalBin ρ b r (row v) z = j) →
        (ρ / (ρ * r)) ^ 2 / Kgeom ≤
          ((normalStripPhysicalCells (assignedPosition b) {z ∈ R | assignedCell ρ b z = v}
            (row v) (ρ * r) j).ncard : ℝ) := by
    rintro r ⟨i, rfl⟩ v j hocc
    have hp : 0 < ρ * scales i := mul_pos hρ (hspos i)
    have hp₁ : ρ * scales i ≤ 1 :=
      (mul_le_mul_of_nonneg_left (hscales i).2 hρ.le).trans (by simpa using hρ₁)
    have hraw := global_assigned_filling_of_original_floors (θ k g) μ old
      (scalarPaletteMeasure (D.π k g) (D.N k ^ (-τ))) hP hR hRP hb hp
      ((hbβ i).trans (hw i).2.2.1) hp₁ hρ hH hKbase hCmk hMK
      (Real.rpow_pos_of_pos hN₀ _) hLfill hηdur hηstrip U hU hUdom hcur hcoeff htime hprod
      (ENNReal.ofReal (Hg k)) ηstate (ENNReal.ofReal (D.K k * D.N k ^ (-D.S * τ)))
      hη₀ hηt hgraphcap hstate hpalette hsmall row (fun z hz => hlong z hz i) (hstrip i)
      hprior hfillbudget v j (by
        obtain ⟨z, hz, hv, hj⟩ := hocc
        refine ⟨z, hz, ?_⟩
        change (assignedCell ρ b z,
          ⌊normalCoordinate (row (assignedCell ρ b z)) (assignedPosition b z) / (ρ * scales i)⌋) = (v, j)
        rw [hv]
        exact Prod.ext rfl hj)
    exact (div_le_div_of_nonneg_left (sq_nonneg _) hLfill hLgeom).trans hraw
  have hhereditary : ∀ r ∈ grid, ∀ R' ∈ grid, 0 < r → r ≤ R' → ∀ q',
      ∃ F' : Finset (Fin 3 → ℤ), (F'.card : ℝ) ≤ (13824 * H₀ k ^ 7) * (R' / r) ^ (2 + D.d) ∧
        ∀ z ∈ R, cell (ρ * R') (assignedPosition b z) = q' →
          cell (ρ * r) (assignedPosition b z) ∈ F' := by
    rintro r ⟨i, rfl⟩ R' ⟨j, rfl⟩ hr hrR q'
    have hulo : T⁻¹ ≤ u i := halo.trans (hw i).1
    have huhi : u i ≤ T := (hw i).2.1.trans hahi
    have hvlo : T⁻¹ ≤ u j := halo.trans (hw j).1
    have hvu : u j ≤ u i := discovery_prepared_scale_antitone hN₁ (hM k).1 hJ hrR
    exact hh g (u i) (u j) hulo huhi hvlo hvu
      (upperGridExponent_on_grid _ _) (upperGridExponent_on_grid _ _) b hb (hbβ i) R
      (fun z hz => hpositive i j z hz) ρ (scales i) (scales j) hρ hr (hspos j)
      (hw i).2.2.1 (hw i).2.2.2 (hw j).2.2.1 (hw j).2.2.2 q'
  have hlists : ∀ (r R' : ℝ) (q' : Fin 3 → ℤ), ∃ F' : Finset (Fin 3 → ℤ),
      (r ∈ grid → R' ∈ grid → 0 < r → r ≤ R' →
        (F'.card : ℝ) ≤ (13824 * H₀ k ^ 7) * (R' / r) ^ (2 + D.d) ∧
          ∀ z ∈ R, cell (ρ * R') (assignedPosition b z) = q' →
            cell (ρ * r) (assignedPosition b z) ∈ F') := by
    intro r R' q'
    by_cases hgood : r ∈ grid ∧ R' ∈ grid ∧ 0 < r ∧ r ≤ R'
    · obtain ⟨F', hF', hm⟩ := hhereditary r hgood.1 R' hgood.2.1 hgood.2.2.1 hgood.2.2.2 q'
      exact ⟨F', fun _ _ _ _ => ⟨hF', hm⟩⟩
    · exact ⟨∅, fun hr hR' hp hle => (hgood ⟨hr, hR', hp, hle⟩).elim⟩
  choose hereditary hhereditary' using hlists
  refine ⟨{
    Q := D.N k ^ (1 / (J : ℝ))
    K := Kgeom
    A := A
    B := 13824 * H₀ k ^ 7
    one_le_Q := Real.one_le_rpow hN₁.le (by positivity)
    K_pos := hKgeom
    grid := grid
    unit := ⟨⟨0, by omega⟩, by simp [scales, powerWidth]⟩
    grid_bounds := by rintro _ ⟨i, rfl⟩; exact hscales i
    rounding := discovery_scale_rounding hN₁ J C hJ
    row := row
    row_bound := hA
    hereditary := hereditary
    count := fun r hr R' hR' hp hle q' => (hhereditary' r R' q' hr hR' hp hle).1
    mem := fun r hr R' hR' hp hle z hz => (hhereditary' r R' _ hr hR' hp hle).2 z hz rfl
    budget := hbudget
    overlap := hoverlap
    filling := hfill
  }, rfl, rfl, rfl, rfl, rfl⟩

end

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
