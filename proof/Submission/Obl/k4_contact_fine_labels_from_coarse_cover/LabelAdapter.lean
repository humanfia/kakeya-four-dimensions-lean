-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/LabelAdapter.lean
import Mathlib
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.LabelBounds
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.CubePalette

/-!
# The label adapter: from a frozen true label to three original affine entries

`label_palette` takes the data of one true label in the frozen prepared model, in its original
coordinates: block `[t₀, t₀ + q]`, constants `c`, test `F`, transverse width `g ≤ K q`, hidden
width `a`; the set `SA` of the label's trajectories (box bounds), `SB ⊆ SA` (whole-block fit),
`SW ⊆ SB` (witness trajectories: contact error `ε ≤ q` and velocity at most `K`); a base set `E₀`
of label points of volume at least `λ q⁴`, each with three witnesses within sup-distance `δ`,
`θ`-separated in velocity, the first with an event. It returns three affine entries
`L u : Fin 4 → ℝ` such that every trajectory of `SB` with one event follows one entry on its
whole block, with error `cubeErr Cs Λ * a`, where `Λ = labelΛ K θ λ`.

The proof normalizes the label with the chart of `LabelChart` (`μ = 100 K³ / θ`), checks the
hypotheses of `cube_palette` (`LabelBounds`, `volume_chartPoint_image`), and maps the affine
predictors back (`affine_of_chart`). The smallness conditions are those of x0777's
`sff_frame_bound` for the normalized contact error `ε / (q μ)` and mesh `7 K δ / q²`.
-/

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set MeasureTheory
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The linear part of the chart. -/
def chartMatrix (t₀ q μ Z₀ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q⁻¹, 0, 0; 0, (q * μ)⁻¹, 0; Z₀ / (q ^ 2 * μ) - 1 / (2 * q), -t₀ / (q ^ 2 * μ), (q ^ 2 * μ)⁻¹]

theorem chartPoint_eq_linear (t₀ q μ Z₀ Y₀ : ℝ) (hq : 0 < q) (hμ : 0 < μ) (x : Fin 3 → ℝ) :
    chartPoint t₀ q μ Z₀ Y₀ x =
      Matrix.toLin' (chartMatrix t₀ q μ Z₀) x + chartPoint t₀ q μ Z₀ Y₀ 0 := by
  funext i
  fin_cases i <;>
    simp [chartPoint, chartMatrix, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_three] <;> field_simp <;> ring

theorem volume_chartPoint_image (t₀ q μ Z₀ Y₀ : ℝ) (hq : 0 < q) (hμ : 0 < μ)
    (E₀ : Set (Fin 3 → ℝ)) :
    volume (chartPoint t₀ q μ Z₀ Y₀ '' E₀) =
      ENNReal.ofReal (1 / (q ^ 4 * μ ^ 2)) * volume E₀ := by
  have himg : chartPoint t₀ q μ Z₀ Y₀ '' E₀ =
      (fun y => y + chartPoint t₀ q μ Z₀ Y₀ 0) '' (Matrix.toLin' (chartMatrix t₀ q μ Z₀) '' E₀) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact chartPoint_eq_linear t₀ q μ Z₀ Y₀ hq hμ x
  rw [himg, Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin', Matrix.det_fin_three]
  congr 2
  simp only [chartMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.tail_cons, Matrix.head_fin_const]
  simp only [mul_zero, zero_mul, sub_zero, add_zero]
  rw [abs_of_pos (show (0:ℝ) < q⁻¹ * (q * μ)⁻¹ * (q ^ 2 * μ)⁻¹ by positivity)]
  field_simp
/-- Affine functions of the chart are affine functions of the original base point. -/
theorem affine_of_chart (t₀ q μ Z₀ Y₀ a c₀ : ℝ) (c : Fin 3 → ℝ) (hq : q ≠ 0) (hμ : μ ≠ 0) :
    ∃ L : Fin 4 → ℝ, ∀ x : Fin 3 → ℝ,
      a * affineFn c₀ c (chartPoint t₀ q μ Z₀ Y₀ x) = L 0 + L 1 * x 0 + L 2 * x 1 + L 3 * x 2 := by
  refine ⟨![a * (c₀ - c 0 * t₀ / q + c 1 * (1 / 2 - Z₀ / (q * μ)) +
      c 2 * (-Y₀ / (q ^ 2 * μ) + t₀ / (2 * q) + 3 / 4)),
    a * (c 0 / q + c 2 * Z₀ / (q ^ 2 * μ) - c 2 / (2 * q)),
    a * (c 1 / (q * μ) - c 2 * t₀ / (q ^ 2 * μ)),
    a * (c 2 / (q ^ 2 * μ))], fun x => ?_⟩
  simp only [affineFn, dot3, chartPoint, Matrix.cons_val]
  field_simp
  ring

/-- The contact scaling and the global loss of the label adapter. -/
def labelΛ (K θ lam : ℝ) : ℝ := 4 * 10 ^ 4 * K ^ 6 / (lam * θ ^ 3)

set_option maxHeartbeats 4000000 in
/-- **Label adapter.** Three original affine entries fit every trajectory of the label with one
event, on its whole block, with error `cubeErr Cs (labelΛ K θ λ) * a`. -/
theorem label_palette (K a q g ε θ δ lam t₀ : ℝ) (c : Fin 5 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
    (SA SB SW : Set (Fin 6 → ℝ)) (E₀ : Set (Fin 3 → ℝ))
    (hK : 1 ≤ K) (ha : 0 < a) (hq : 0 < q) (hq1 : q ≤ 1) (hgq : g ≤ K * q) (hg0 : 0 ≤ g)
    (hε : 0 ≤ ε) (hεq : ε ≤ q) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hc : ∀ e, |c e| ≤ K) (hF : F.totalDegree ≤ 2)
    (hbox : ∀ b ∈ SA, ∀ t ∈ Icc t₀ (t₀ + q), |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q ∧
        |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g ∧
        |b 4 - c 3 - c 4 * b 3| ≤ K * g)
    (hBA : SB ⊆ SA) (hWB : SW ⊆ SB)
    (hfit : ∀ b ∈ SB, ∀ t ∈ Icc t₀ (t₀ + q), |eval (point b t) F| ≤ K * a ∧
        |eval (point b t) (pderiv 3 F)| ≤ K ∧
        |eval (point b t) (pderiv 3 (pderiv 3 F))| ≤ K / a)
    (hW : ∀ b ∈ SW, |b 4 + b 0| ≤ ε ∧ |b 3| ≤ K)
    (hE₀ : ∀ p ∈ E₀, p 0 ∈ Icc t₀ (t₀ + q)) (hδq : 56 * K * δ ≤ q ^ 2)
    (hvol : ENNReal.ofReal (lam * q ^ 4) ≤ volume E₀)
    (hwit : ∀ p ∈ E₀, ∃ b₁ ∈ SW, ∃ b₂ ∈ SW, ∃ b₃ ∈ SW,
      ∃ τ₁ ∈ Icc t₀ (t₀ + q), ∃ τ₂ ∈ Icc t₀ (t₀ + q), ∃ τ₃ ∈ Icc t₀ (t₀ + q),
        (∀ i, |basePt b₁ τ₁ i - p i| ≤ δ) ∧ (∀ i, |basePt b₂ τ₂ i - p i| ≤ δ) ∧
        (∀ i, |basePt b₃ τ₃ i - p i| ≤ δ) ∧
        θ ≤ |b₁ 3 - b₂ 3| ∧ θ ≤ |b₁ 3 - b₃ 3| ∧ θ ≤ |b₂ 3 - b₃ 3| ∧
        K⁻¹ ≤ |eval (point b₁ τ₁) (pderiv 3 F)|)
    (Cs : ℝ) (hCs : CoefCtrl Cs) (hCs0 : 0 < Cs)
    (hs1 : 4 * Cs * remezC 4 (labelΛ K θ lam) * (7 * K * δ / q ^ 2) ≤ 1)
    (hs2 : 8 * discBudget Cs (labelΛ K θ lam) * (7 * K * δ / q ^ 2) * labelΛ K θ lam ^ 2 ≤ 1)
    (hs3 : 192 * Cs * sffKappa Cs (labelΛ K θ lam) *
      (ε / (q * labelμ K θ) + 7 * K * δ / q ^ 2) * labelΛ K θ lam ^ 2 ≤ 1) :
    ∃ L : Fin 3 → Fin 4 → ℝ, ∀ b ∈ SB,
      (∃ τ ∈ Icc t₀ (t₀ + q), K⁻¹ ≤ |eval (point b τ) (pderiv 3 F)|) →
      ∃ u : Fin 3, ∀ t ∈ Icc t₀ (t₀ + q),
        |point b t 3 - (L u 0 + L u 1 * t + L u 2 * point b t 1 + L u 3 * point b t 2)| ≤
          cubeErr Cs (labelΛ K θ lam) * a := by
  have hK0 : 0 < K := by linarith
  set μ := labelμ K θ with hμdef
  set Λ := labelΛ K θ lam with hΛdef
  set Z₀ := labelZ₀ t₀ c with hZ₀def
  set Y₀ := labelY₀ t₀ c with hY₀def
  have hμpos : 0 < μ := by rw [hμdef, labelμ]; positivity
  have hμ1 : 1 ≤ μ := by
    rw [hμdef, labelμ, le_div_iff₀ hθ]; nlinarith [pow_pos hK0 3, pow_le_pow_left₀ zero_le_one hK 3]
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have hK6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
  have hθ3 : θ ^ 3 ≤ θ := by nlinarith [pow_pos hθ 2]
  have hθ2 : θ ^ 3 ≤ θ ^ 2 := by nlinarith [pow_pos hθ 2]
  have hθ3le : θ ^ 3 ≤ 1 := pow_le_one₀ hθ.le hθ1
  have hlt1 : lam * θ ^ 3 ≤ 1 := mul_le_one₀ hlam1 (by positivity) hθ3le
  have hΛK : K ≤ Λ := by
    rw [hΛdef, labelΛ, le_div_iff₀ (by positivity)]
    have h2 : K * (lam * θ ^ 3) ≤ K := mul_le_of_le_one_right hK0.le hlt1
    have h3 : K ≤ K ^ 6 := le_self_pow₀ hK (by norm_num)
    nlinarith [pow_pos hK0 6]
  have hΛ1 : 1 ≤ Λ := le_trans hK hΛK
  have hΛ0 : 0 < Λ := by linarith
  have hΛμθ : μ / θ ≤ Λ := by
    rw [hμdef, hΛdef, labelμ, labelΛ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : lam * θ ^ 3 ≤ θ * θ := by
      have e1 : lam * θ ^ 3 ≤ θ ^ 3 := mul_le_of_le_one_left (by positivity) hlam1
      have e2 : θ ^ 3 ≤ θ * θ := by nlinarith [pow_pos hθ 2]
      linarith
    have h2 : 200 * K ^ 3 * (lam * θ ^ 3) ≤ 200 * K ^ 3 * (θ * θ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 200 * K ^ 3 ≤ 4 * 10 ^ 4 * K ^ 6 := by
      have : K ^ 6 = K ^ 3 * K ^ 3 := by ring
      nlinarith [pow_pos hK0 3]
    have h4 : 200 * K ^ 3 * (θ * θ) ≤ 4 * 10 ^ 4 * K ^ 6 * (θ * θ) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith
  -- volume of the normalized witness set
  set E := chartPoint t₀ q μ Z₀ Y₀ '' E₀ with hEdef
  have hEv : ENNReal.ofReal Λ⁻¹ ≤ volume E := by
    rw [hEdef, volume_chartPoint_image t₀ q μ Z₀ Y₀ hq hμpos]
    calc ENNReal.ofReal Λ⁻¹ ≤ ENNReal.ofReal (1 / (q ^ 4 * μ ^ 2)) * ENNReal.ofReal (lam * q ^ 4) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [hΛdef, labelΛ, hμdef, labelμ]
          have hq4 : (0:ℝ) < q ^ 4 := by positivity
          rw [inv_div, div_le_iff₀ (by positivity)]
          field_simp
          nlinarith [pow_pos hK0 6, pow_pos hθ 2]
      _ ≤ _ := by gcongr
  -- the label constants are pinned by two witnesses
  have hEne : E₀.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty] at hvol
    exact absurd hvol (not_le.mpr (ENNReal.ofReal_pos.mpr (by positivity)))
  obtain ⟨p₀, hp₀⟩ := hEne
  obtain ⟨w₁, hw₁, w₂, hw₂, -, -, -, -, -, -, -, -, -, -, -, hsep₁₂, -, -, -⟩ := hwit p₀ hp₀
  have ht₀I : t₀ ∈ Icc t₀ (t₀ + q) := ⟨le_rfl, by linarith⟩
  have hbox₁ := hbox w₁ (hBA (hWB hw₁)) t₀ ht₀I
  have hbox₂ := hbox w₂ (hBA (hWB hw₂)) t₀ ht₀I
  obtain ⟨hrate4, hrate3⟩ := label_rate_rigidity K q g ε t₀ θ c w₁ w₂ hK hθ hbox₁.1 hbox₁.2.2
    (hW w₁ hw₁).1 hbox₂.1 hbox₂.2.2 (hW w₂ hw₂).1 hsep₁₂ (hW w₁ hw₁).2
  have hcubeA : ∀ b ∈ SA, ∀ t ∈ Icc t₀ (t₀ + q),
      chartPoint t₀ q μ Z₀ Y₀ (basePt b t) ∈ Icc (0 : Fin 3 → ℝ) 1 := by
    intro b hb t ht
    exact chartPoint_mem_cube K q g ε θ t₀ c b t hK hq hgq hg0 hε hεq hθ hθ1 (hc 1) hrate4 hrate3
      ht (hbox b hb t ht).1 (hbox b hb t ht).2.1
  -- times of the block
  have hσt : ∀ σ ∈ Icc (0 : ℝ) 1, t₀ + q * σ ∈ Icc t₀ (t₀ + q) := by
    intro σ hσ
    exact ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩
  have htσ : ∀ t ∈ Icc t₀ (t₀ + q), (t - t₀) / q ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨div_nonneg (by linarith [ht.1]) hq.le, by rw [div_le_one hq]; linarith [ht.2]⟩
  have htσ' : ∀ t : ℝ, t₀ + q * ((t - t₀) / q) = t := by
    intro t; field_simp; ring
  -- the normalized test
  set γ' := chartGamma t₀ q μ Z₀ Y₀ a F
  set β' := chartBeta t₀ q μ Z₀ Y₀ F
  set α' := chartAlpha a F
  have hγ' : γ'.totalDegree ≤ 2 := chartGamma_degree t₀ q μ Z₀ Y₀ a F hF
  have hβ' : β'.totalDegree ≤ 1 := chartBeta_degree t₀ q μ Z₀ Y₀ F hF
  have hq0 : q ≠ 0 := hq.ne'
  have hμ0 : μ ≠ 0 := hμpos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hfitN : ∀ b ∈ SB, ∀ σ ∈ Icc (0 : ℝ) 1,
      |testVal α' β' γ' (chartCoeff t₀ q μ Z₀ Y₀ a b) σ| ≤ Λ ∧
        |testDer α' β' (chartCoeff t₀ q μ Z₀ Y₀ a b) σ| ≤ Λ := by
    intro b hb σ hσ
    have hf := hfit b hb _ (hσt σ hσ)
    rw [testVal_chartCoeff t₀ q μ Z₀ Y₀ a F hF hq0 hμ0 ha0,
      testDer_chartCoeff t₀ q μ Z₀ Y₀ a F hF hq0 hμ0 ha0]
    refine ⟨?_, hf.2.1.trans hΛK⟩
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
    nlinarith [hf.1]
  have hα' : |2 * α'| ≤ Λ := by
    have hb := hWB hw₁
    have hf := hfit w₁ hb t₀ ht₀I
    rw [two_chartAlpha a F hF (point w₁ t₀), abs_mul, abs_of_pos ha]
    have : a * |eval (point w₁ t₀) (pderiv 3 (pderiv 3 F))| ≤ a * (K / a) :=
      mul_le_mul_of_nonneg_left hf.2.2 ha.le
    rw [mul_div_cancel₀ K ha0] at this
    linarith
  have hcubeN : ∀ b ∈ SA, ∀ σ ∈ Icc (0 : ℝ) 1,
      lineP (chartCoeff t₀ q μ Z₀ Y₀ a b) σ ∈ Icc (0 : Fin 3 → ℝ) 1 := by
    intro b hb σ hσ
    rw [lineP_chartCoeff t₀ q μ Z₀ Y₀ a hq0 hμ0]
    exact hcubeA b hb _ (hσt σ hσ)
  set S := chartCoeff t₀ q μ Z₀ Y₀ a '' SW with hSdef
  set T := chartCoeff t₀ q μ Z₀ Y₀ a '' SB with hTdef
  have hfitS : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α' β' γ' b σ| ≤ Λ ∧ |testDer α' β' b σ| ≤ Λ := by
    rintro _ ⟨b, hb, rfl⟩ σ hσ; exact hfitN b (hWB hb) σ hσ
  have hfitT : ∀ b ∈ T, ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α' β' γ' b σ| ≤ Λ ∧ |testDer α' β' b σ| ≤ Λ := by
    rintro _ ⟨b, hb, rfl⟩ σ hσ; exact hfitN b hb σ hσ
  have hcubeS : ∀ b ∈ S, ∀ σ ∈ Icc (0 : ℝ) 1, lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1 := by
    rintro _ ⟨b, hb, rfl⟩ σ hσ; exact hcubeN b (hBA (hWB hb)) σ hσ
  have hcubeT : ∀ b ∈ T, ∀ σ ∈ Icc (0 : ℝ) 1, lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1 := by
    rintro _ ⟨b, hb, rfl⟩ σ hσ; exact hcubeN b (hBA hb) σ hσ
  have hconS : ∀ b ∈ S, |b 4 + b 0| ≤ ε / (q * μ) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [chartCoeff_contact t₀ q μ Z₀ Y₀ a hq0 hμ0, abs_div,
      abs_of_pos (show (0:ℝ) < q * μ by positivity)]
    exact div_le_div_of_nonneg_right (hW b hb).1 (by positivity)
  have hvelS : ∀ b ∈ S, |b 3| ≤ Λ := by
    rintro _ ⟨b, hb, rfl⟩
    rw [chartCoeff_three, abs_div, abs_of_pos hμpos]
    have : |b 3| / μ ≤ K / 1 := div_le_div₀ hK0.le (hW b hb).2 zero_lt_one hμ1
    rw [div_one] at this
    exact this.trans hΛK
  have hZ₀ : |Z₀| ≤ 2 * K := by
    rw [hZ₀def, labelZ₀]
    have := hc 0; have := hc 1
    calc |c 0 + t₀ * c 1| ≤ |c 0| + |t₀ * c 1| := abs_add_le _ _
      _ ≤ K + 1 * K := by
          rw [abs_mul]; gcongr; rw [abs_le]; constructor <;> linarith [ht₀.1, ht₀.2]
      _ = 2 * K := by ring
  have ht₀abs : |t₀| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht₀.1, ht₀.2]
  have hEc : E ⊆ Icc (0 : Fin 3 → ℝ) 1 := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨b₁, hb₁, -, -, -, -, τ₁, hτ₁, -, -, -, -, hd₁, -⟩ := hwit p hp
    have hb₁A := hBA (hWB hb₁)
    have hnear : l1dist (chartPoint t₀ q μ Z₀ Y₀ (basePt b₁ τ₁)) (chartPoint t₀ q μ Z₀ Y₀ p) ≤
        1 / 8 := by
      refine (l1dist_chartPoint_le K q μ t₀ Z₀ Y₀ δ hK hq hq1 hμ1 ht₀abs hZ₀ _ _ hd₁).trans ?_
      rw [div_le_iff₀ (by positivity)]; linarith
    exact chartPoint_mem_cube_of_near K q g ε θ t₀ c b₁ τ₁ hK hq hgq hg0 hε hεq hθ hθ1 (hc 1)
      hrate4 hrate3 hτ₁ (hbox b₁ hb₁A τ₁ hτ₁).1 (hbox b₁ hb₁A τ₁ hτ₁).2.1 p (hE₀ p hp) hnear
  have hwitN : ∀ p ∈ E, ∃ b₁ ∈ S, ∃ b₂ ∈ S, ∃ b₃ ∈ S,
      ∃ σ₁ ∈ Icc (0 : ℝ) 1, ∃ σ₂ ∈ Icc (0 : ℝ) 1, ∃ σ₃ ∈ Icc (0 : ℝ) 1,
        l1dist (lineP b₁ σ₁) p ≤ 7 * K * δ / q ^ 2 ∧ l1dist (lineP b₂ σ₂) p ≤ 7 * K * δ / q ^ 2 ∧
        l1dist (lineP b₃ σ₃) p ≤ 7 * K * δ / q ^ 2 ∧
        Λ⁻¹ ≤ |b₁ 3 - b₂ 3| ∧ Λ⁻¹ ≤ |b₁ 3 - b₃ 3| ∧ Λ⁻¹ ≤ |b₂ 3 - b₃ 3| ∧
        Λ⁻¹ ≤ |testDer α' β' b₁ σ₁| := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, τ₁, hτ₁, τ₂, hτ₂, τ₃, hτ₃, hd₁, hd₂, hd₃,
      hs12, hs13, hs23, hev⟩ := hwit p hp
    have hdist : ∀ b τ, (∀ i, |basePt b τ i - p i| ≤ δ) →
        l1dist (lineP (chartCoeff t₀ q μ Z₀ Y₀ a b) ((τ - t₀) / q)) (chartPoint t₀ q μ Z₀ Y₀ p) ≤
          7 * K * δ / q ^ 2 := by
      intro b τ hd
      rw [lineP_chartCoeff t₀ q μ Z₀ Y₀ a hq0 hμ0, htσ' τ]
      exact l1dist_chartPoint_le K q μ t₀ Z₀ Y₀ δ hK hq hq1 hμ1 ht₀abs hZ₀ _ _ hd
    have hsepN : ∀ b b' : Fin 6 → ℝ, θ ≤ |b 3 - b' 3| →
        Λ⁻¹ ≤ |chartCoeff t₀ q μ Z₀ Y₀ a b 3 - chartCoeff t₀ q μ Z₀ Y₀ a b' 3| := by
      intro b b' hs
      rw [chartCoeff_three, chartCoeff_three, ← sub_div, abs_div, abs_of_pos hμpos]
      calc Λ⁻¹ ≤ (μ / θ)⁻¹ := inv_anti₀ (by positivity) hΛμθ
        _ = θ / μ := by rw [inv_div]
        _ ≤ |b 3 - b' 3| / μ := div_le_div_of_nonneg_right hs hμpos.le
    refine ⟨_, ⟨b₁, hb₁, rfl⟩, _, ⟨b₂, hb₂, rfl⟩, _, ⟨b₃, hb₃, rfl⟩,
      _, htσ τ₁ hτ₁, _, htσ τ₂ hτ₂, _, htσ τ₃ hτ₃,
      hdist b₁ τ₁ hd₁, hdist b₂ τ₂ hd₂, hdist b₃ τ₃ hd₃,
      hsepN _ _ hs12, hsepN _ _ hs13, hsepN _ _ hs23, ?_⟩
    rw [testDer_chartCoeff t₀ q μ Z₀ Y₀ a F hF hq0 hμ0 ha0, htσ' τ₁]
    exact le_trans (inv_anti₀ hK0 hΛK) hev
  have hε1 : ε / (q * μ) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hρ : 0 ≤ 7 * K * δ / q ^ 2 := by positivity
  obtain ⟨c₀, cc, hpal⟩ := cube_palette α' β' γ' hβ' hγ' Cs Λ (ε / (q * μ)) (7 * K * δ / q ^ 2)
    S T E hCs hCs0 hΛ1 hα' hfitS hcubeS hconS hvelS hEc hEv hwitN hε1 hρ hs1 hs2 hs3 T hfitT hcubeT
  -- back to the original coordinates
  have hL : ∀ u : Fin 3, ∃ L : Fin 4 → ℝ, ∀ x : Fin 3 → ℝ,
      a * affineFn (c₀ u) (cc u) (chartPoint t₀ q μ Z₀ Y₀ x) =
        L 0 + L 1 * x 0 + L 2 * x 1 + L 3 * x 2 :=
    fun u => affine_of_chart t₀ q μ Z₀ Y₀ a (c₀ u) (cc u) hq0 hμ0
  choose L hLeq using hL
  refine ⟨L, fun b hb hev => ?_⟩
  obtain ⟨τ, hτ, hevτ⟩ := hev
  have hevN : Λ⁻¹ ≤ |testDer α' β' (chartCoeff t₀ q μ Z₀ Y₀ a b) ((τ - t₀) / q)| := by
    rw [testDer_chartCoeff t₀ q μ Z₀ Y₀ a F hF hq0 hμ0 ha0, htσ' τ]
    exact le_trans (inv_anti₀ hK0 hΛK) hevτ
  obtain ⟨u, hu⟩ := hpal _ ⟨b, hb, rfl⟩ _ (htσ τ hτ) hevN
  refine ⟨u, fun t ht => ?_⟩
  have h := hu _ (htσ t ht)
  rw [lineP_chartCoeff t₀ q μ Z₀ Y₀ a hq0 hμ0, htσ' t] at h
  have hw : a * lineW (chartCoeff t₀ q μ Z₀ Y₀ a b) ((t - t₀) / q) = b 2 + t * b 5 := by
    rw [lineW_chartCoeff t₀ q μ Z₀ Y₀ a ha0, htσ' t]
  have hpt : point b t 3 = b 2 + t * b 5 := rfl
  have key : L u 0 + L u 1 * t + L u 2 * point b t 1 + L u 3 * point b t 2 =
      a * affineFn (c₀ u) (cc u) (chartPoint t₀ q μ Z₀ Y₀ (basePt b t)) := by
    rw [hLeq u (basePt b t)]
    rfl
  rw [key, hpt, ← hw, ← mul_sub, abs_mul, abs_of_pos ha, mul_comm]
  exact mul_le_mul_of_nonneg_right h ha.le

end

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
