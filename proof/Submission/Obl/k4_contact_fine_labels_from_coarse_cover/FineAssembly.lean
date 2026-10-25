import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ParentWitnesses
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.HeavyFilling
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.MeasurableResidual
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.MeasurableCore
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.LabelPaletteBudget
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.BlockGeometry
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelScales
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.PaletteAssembly
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.AsymptoticBudget

/-!
# Single-depth fine palettes from the coarse cover

Every true label at a shallow depth `s` receives three full-block affine entries:

* the coarse cover gives the label a heavy measurable state
  (`exists_heavy_measurable_label_state`), with no label discarded;
* its recovered fine density fills a time-aligned base region (`eventually_heavy_filling`);
* deep labels nested in the same shallow label put three actual witnesses with separated
  velocities near every point of that region (`eventually_parent_nearby_velocities`);
* the deterministic label adapter (`label_palette_budget`) then predicts EVERY trajectory of
  the shallow `B` with one regular event.

Almost every incidence lies in some shallow `B × I` and carries a regular event there, so the
palette event is conull: no deletion is charged at all.
-/

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Submission.Lib.K4QuadraticSheetCore

open Set Filter MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization

/-- The universal constant of the label palette adapter. -/
noncomputable def paletteConst : ℝ := Classical.choose label_palette_budget

theorem one_le_paletteConst : 1 ≤ paletteConst :=
  (Classical.choose_spec label_palette_budget).1

theorem paletteConst_spec :
    ∀ (K a q g ε θ δ lam t₀ : ℝ) (c : Fin 5 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
      (SA SB SW : Set (Fin 6 → ℝ)) (E₀ : Set (Fin 3 → ℝ)),
    1 ≤ K → 0 < a → 0 < q → q ≤ 1 → g ≤ K * q → 0 ≤ g → 0 ≤ ε → ε ≤ q → 0 < θ → θ ≤ 1 →
    0 ≤ δ → 0 < lam → lam ≤ 1 → t₀ ∈ Icc (0 : ℝ) 1 → (∀ e, |c e| ≤ K) → F.totalDegree ≤ 2 →
    (∀ b ∈ SA, ∀ t ∈ Icc t₀ (t₀ + q), |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q ∧
        |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g ∧
        |b 4 - c 3 - c 4 * b 3| ≤ K * g) →
    SB ⊆ SA → SW ⊆ SB →
    (∀ b ∈ SB, ∀ t ∈ Icc t₀ (t₀ + q), |eval (point b t) F| ≤ K * a ∧
        |eval (point b t) (pderiv 3 F)| ≤ K ∧
        |eval (point b t) (pderiv 3 (pderiv 3 F))| ≤ K / a) →
    (∀ b ∈ SW, |b 4 + b 0| ≤ ε ∧ |b 3| ≤ K) →
    (∀ p ∈ E₀, p 0 ∈ Icc t₀ (t₀ + q)) →
    ENNReal.ofReal (lam * q ^ 4) ≤ volume E₀ →
    (∀ p ∈ E₀, ∃ b₁ ∈ SW, ∃ b₂ ∈ SW, ∃ b₃ ∈ SW,
      ∃ τ₁ ∈ Icc t₀ (t₀ + q), ∃ τ₂ ∈ Icc t₀ (t₀ + q), ∃ τ₃ ∈ Icc t₀ (t₀ + q),
        (∀ i, |basePt b₁ τ₁ i - p i| ≤ δ) ∧ (∀ i, |basePt b₂ τ₂ i - p i| ≤ δ) ∧
        (∀ i, |basePt b₃ τ₃ i - p i| ≤ δ) ∧
        θ ≤ |b₁ 3 - b₂ 3| ∧ θ ≤ |b₁ 3 - b₃ 3| ∧ θ ≤ |b₂ 3 - b₃ 3| ∧
        K⁻¹ ≤ |eval (point b₁ τ₁) (pderiv 3 F)|) →
    paletteConst * labelΛ K θ lam ^ 80 * (ε / (q * labelμ K θ) + 7 * K * δ / q ^ 2) ≤ 1 →
    ∃ L : Fin 3 → Fin 4 → ℝ, ∀ b ∈ SB,
      (∃ τ ∈ Icc t₀ (t₀ + q), K⁻¹ ≤ |eval (point b τ) (pderiv 3 F)|) →
      ∃ u : Fin 3, ∀ t ∈ Icc t₀ (t₀ + q),
        |point b t 3 - (L u 0 + L u 1 * t + L u 2 * point b t 1 + L u 3 * point b t 2)| ≤
          paletteConst * labelΛ K θ lam ^ 80 * a :=
  (Classical.choose_spec label_palette_budget).2

theorem fineLoss_eq_labelΛ (C K H θ : ℝ) :
    fineLoss C K H θ = C * labelΛ K θ (fineLam K H) ^ 80 := rfl

theorem one_le_labelμ {K θ : ℝ} (hK : 1 ≤ K) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    1 ≤ labelμ K θ := by
  rw [labelμ, le_div_iff₀ hθ]
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  nlinarith

theorem fineLam_pos {K H : ℝ} (hK : 1 ≤ K) (hH : 1 ≤ H) : 0 < fineLam K H := by
  rw [fineLam]
  have : 0 < K := by linarith
  have : 0 < H := by linarith
  positivity

theorem fineLam_le_one {K H : ℝ} (hK : 1 ≤ K) (hH : 1 ≤ H) : fineLam K H ≤ 1 := by
  rw [fineLam]
  apply inv_le_one_of_one_le₀
  have hK7 : 1 ≤ K ^ 7 := one_le_pow₀ hK
  nlinarith

theorem fineLam_eq {K H : ℝ} (hK : 0 < K) (hH : 0 < H) :
    1 / (2 * K * H) / (8640 * K ^ 6) = fineLam K H := by
  rw [fineLam]
  field_simp
  ring

namespace Model

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem base_eq_basePt (k : ℕ) (w : α × ℝ) :
    basePt (p.b k w.1) w.2 = p.base k w := by
  funext c
  fin_cases c <;> simp [basePt, Model.base, Model.x, point]

/-- **One label, deterministically.** Given a filled base region of the label whose points
all have three nearby separated witnesses in the label's own `B`, three affine entries predict
every trajectory of `B` with one regular event, on the whole block. -/
theorem label_entries_of_witnessed_region (hp : p.Valid) {k : ℕ} {s : ℝ}
    {i : Fin (p.n k s)} (hi : p.Label k s i)
    (hlo : p.N k ^ (p.κ * s) / p.K k ≤ (2 : ℝ) ^ p.T k s)
    (hhi : (2 : ℝ) ^ p.T k s ≤ p.K k * p.N k ^ (p.κ * s))
    (hAB : p.B k s i ⊆ p.A k s i)
    {θ δ lam : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hεq : p.N k ^ (-p.e₀) ≤ p.q k s)
    (hsmall : paletteConst * labelΛ (p.K k) θ lam ^ 80 *
      (p.N k ^ (-p.e₀) / (p.q k s * labelμ (p.K k) θ) + 7 * p.K k * δ / p.q k s ^ 2) ≤ 1)
    (E : Set (Fin 3 → ℝ))
    (hEt : ∀ z ∈ E, z 0 ∈ p.I k s i)
    (hvol : ENNReal.ofReal (lam * p.q k s ^ 4) ≤ volume E)
    (hwit : ∀ z ∈ E, ∃ w : Fin 3 → α × ℝ,
      (∀ e, (w e).1 ∈ p.B k s i ∧ (w e).2 ∈ p.I k s i ∧ p.GoodPoint k (w e) ∧
        (p.K k)⁻¹ ≤ |eval (p.x k (w e).1 (w e).2) (pderiv 3 (p.F k s i))| ∧
        ∀ c, |p.base k (w e) c - z c| ≤ δ) ∧
      ∀ e e', e ≠ e' → θ ≤ |p.b k (w e).1 3 - p.b k (w e').1 3|) :
    ∃ L : Fin 3 → Fin 4 → ℝ, ∀ l ∈ p.B k s i,
      (∃ τ ∈ p.I k s i, (p.K k)⁻¹ ≤ |eval (p.x k l τ) (pderiv 3 (p.F k s i))|) →
      ∃ u : Fin 3, ∀ t ∈ p.I k s i,
        |p.x k l t 3 - (L u 0 + L u 1 * t + L u 2 * p.x k l t 1 + L u 3 * p.x k l t 2)| ≤
          paletteConst * labelΛ (p.K k) θ lam ^ 80 * p.a k s := by
  obtain ⟨_, _, _, hc, hF, hgeo, hfit, _⟩ := hi
  have hK1 : 1 ≤ p.K k := hp.K_ge k
  have ha := Valid.a_pos p hp k s
  have hq := p.q_pos k s
  obtain ⟨ht₀, hq1⟩ := p.block_geometry k s i
  have hgq : p.g k s ≤ p.K k * p.q k s := (equal_rate_width_bounds p hp hlo hhi).1
  have hg0 : 0 ≤ p.g k s := (Valid.g_pos p hp k s).le
  have hI := p.I_eq_block k s i
  have hε0 : 0 ≤ p.N k ^ (-p.e₀) := Real.rpow_nonneg (Valid.N_pos p hp k).le _
  let SA : Set (Fin 6 → ℝ) := p.b k '' p.A k s i
  let SB : Set (Fin 6 → ℝ) := p.b k '' p.B k s i
  let SW : Set (Fin 6 → ℝ) :=
    {b | ∃ w : α × ℝ, w.1 ∈ p.B k s i ∧ p.GoodPoint k w ∧ p.b k w.1 = b}
  have hbox : ∀ b ∈ SA, ∀ t ∈ Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s),
      |b 0 + t * b 3 - p.c k s i 0 - t * p.c k s i 1| ≤ p.K k * p.q k s ∧
      |b 1 + t * b 4 - p.c k s i 2 - t * p.c k s i 3 - p.c k s i 4 * (b 0 + t * b 3)| ≤
        p.K k * p.q k s * p.g k s ∧
      |b 4 - p.c k s i 3 - p.c k s i 4 * b 3| ≤ p.K k * p.g k s := by
    rintro b ⟨l, hl, rfl⟩ t ht
    have h := hgeo l hl t (by rw [hI]; exact ht)
    simpa [Model.x, point] using h
  have hBA : SB ⊆ SA := image_mono hAB
  have hWB : SW ⊆ SB := by
    rintro b ⟨w, hw, _, rfl⟩
    exact ⟨w.1, hw, rfl⟩
  have hfitB : ∀ b ∈ SB, ∀ t ∈ Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s),
      |eval (point b t) (p.F k s i)| ≤ p.K k * p.a k s ∧
      |eval (point b t) (pderiv 3 (p.F k s i))| ≤ p.K k ∧
      |eval (point b t) (pderiv 3 (pderiv 3 (p.F k s i)))| ≤ p.K k / p.a k s := by
    rintro b ⟨l, hl, rfl⟩ t ht
    exact hfit l hl t (by rw [hI]; exact ht)
  have hW : ∀ b ∈ SW, |b 4 + b 0| ≤ p.N k ^ (-p.e₀) ∧ |b 3| ≤ p.K k := by
    rintro b ⟨w, _, hw, rfl⟩
    exact ⟨hw.contact, hw.velocity⟩
  have hE₀ : ∀ z ∈ E, z 0 ∈ Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s) := by
    intro z hz
    rw [← hI]
    exact hEt z hz
  have hwit' : ∀ z ∈ E, ∃ b₁ ∈ SW, ∃ b₂ ∈ SW, ∃ b₃ ∈ SW,
      ∃ τ₁ ∈ Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s),
      ∃ τ₂ ∈ Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s),
      ∃ τ₃ ∈ Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s),
        (∀ c, |basePt b₁ τ₁ c - z c| ≤ δ) ∧ (∀ c, |basePt b₂ τ₂ c - z c| ≤ δ) ∧
        (∀ c, |basePt b₃ τ₃ c - z c| ≤ δ) ∧
        θ ≤ |b₁ 3 - b₂ 3| ∧ θ ≤ |b₁ 3 - b₃ 3| ∧ θ ≤ |b₂ 3 - b₃ 3| ∧
        (p.K k)⁻¹ ≤ |eval (point b₁ τ₁) (pderiv 3 (p.F k s i))| := by
    intro z hz
    obtain ⟨w, hw, hsep⟩ := hwit z hz
    have hSW (e : Fin 3) : p.b k (w e).1 ∈ SW := ⟨w e, (hw e).1, (hw e).2.2.1, rfl⟩
    have hT (e : Fin 3) : (w e).2 ∈ Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s) := by
      rw [← hI]
      exact (hw e).2.1
    have hD (e : Fin 3) : ∀ c, |basePt (p.b k (w e).1) (w e).2 c - z c| ≤ δ := by
      intro c
      rw [p.base_eq_basePt k (w e)]
      exact (hw e).2.2.2.2 c
    exact ⟨_, hSW 0, _, hSW 1, _, hSW 2, _, hT 0, _, hT 1, _, hT 2, hD 0, hD 1, hD 2,
      hsep 0 1 (by decide), hsep 0 2 (by decide), hsep 1 2 (by decide), (hw 0).2.2.2.1⟩
  obtain ⟨L, hL⟩ := paletteConst_spec (p.K k) (p.a k s) (p.q k s) (p.g k s)
    (p.N k ^ (-p.e₀)) θ δ lam (p.blockStart k s i) (p.c k s i) (p.F k s i) SA SB SW E
    hK1 ha hq hq1 hgq hg0 hε0 hεq hθ hθ1 hδ hlam hlam1 ht₀ hc hF hbox hBA hWB hfitB hW hE₀
    hvol hwit' hsmall
  refine ⟨L, fun l hl hev => ?_⟩
  obtain ⟨τ, hτ, hτev⟩ := hev
  obtain ⟨u, hu⟩ := hL (p.b k l) ⟨l, hl, rfl⟩ ⟨τ, by rw [← hI]; exact hτ, hτev⟩
  exact ⟨u, fun t ht => hu t (by rw [← hI]; exact ht)⟩

/-- The fixed-power original mass floor of one heavy coarse branch of a shallow label. -/
theorem eventually_heavy_branch_mass (hp : p.Valid) (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, p.N k ^ (-6 * s) ≤
      1 / (2 * p.K k * H k) * ((p.K k)⁻¹ ^ (4 : ℕ) * p.N k ^ (-(p.d + 4 * p.κ) * s)) := by
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.N_ge k]
  have hKH1 : ∀ k, 1 ≤ p.K k * H k := fun k => by nlinarith [hp.K_ge k, hH k]
  have hKHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k * H k ≤ p.N k ^ ε :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul
      (fun k => Valid.N_pos p hp k) (fun k => by linarith [hp.K_ge k])
      (fun k => by linarith [hH k]) hp.K_sub hHsub
  filter_upwards [Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.N_lim hKH1 hKHsub 5 (show -6 * s < -5 * s by linarith)
    (show (0 : ℝ) ≤ 2 by norm_num)] with k hk
  have hN := Valid.N_pos p hp k
  have hK := Valid.K_pos p hp k
  have hK1 := hp.K_ge k
  have hH0 : 0 < H k := by linarith [hH k]
  have hexp : -5 * s ≤ -(p.d + 4 * p.κ) * s := by
    have := hp.d_lt_one
    have := hp.κ_le_one
    nlinarith
  have hpow : p.N k ^ (-5 * s) ≤ p.N k ^ (-(p.d + 4 * p.κ) * s) :=
    Real.rpow_le_rpow_of_exponent_le (hN1 k) hexp
  have hKH5 : p.K k ^ 5 * H k ≤ (p.K k * H k) ^ 5 := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc H k = H k ^ 1 := (pow_one _).symm
      _ ≤ H k ^ 5 := pow_le_pow_right₀ (hH k) (by norm_num)
  have hlhs : 2 * (p.K k ^ 5 * H k) * p.N k ^ (-6 * s) ≤ p.N k ^ (-(p.d + 4 * p.κ) * s) := by
    have h6 : 0 ≤ p.N k ^ (-6 * s) := Real.rpow_nonneg hN.le _
    calc 2 * (p.K k ^ 5 * H k) * p.N k ^ (-6 * s)
        ≤ 2 * (p.K k * H k) ^ 5 * p.N k ^ (-6 * s) := by gcongr
      _ ≤ p.N k ^ (-5 * s) := hk.le
      _ ≤ _ := hpow
  have heq : 1 / (2 * p.K k * H k) * ((p.K k)⁻¹ ^ (4 : ℕ) * p.N k ^ (-(p.d + 4 * p.κ) * s)) =
      p.N k ^ (-(p.d + 4 * p.κ) * s) / (2 * (p.K k ^ 5 * H k)) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  linarith

/-- The reciprocal integer mesh `⌈N^(40s)⌉` resolves the fixed fine base mesh of the label. -/
theorem eventually_fine_mesh_count (hp : p.Valid) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, 2 * p.K k * p.N k ^ (-99 * s) ≤ p.N k ^ (-40 * s) := by
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.N_ge k]
  filter_upwards [Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.N_lim hp.K_ge hp.K_sub 1 (show -99 * s < -40 * s by linarith)
    (show (0 : ℝ) ≤ 2 by norm_num)] with k hk
  simpa only [pow_one] using hk.le

theorem mesh_count_bounds (hp : p.Valid) {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hlo : p.N k ^ (p.κ * s) / p.K k ≤ (2 : ℝ) ^ p.T k s)
    (hhi : (2 : ℝ) ^ p.T k s ≤ p.K k * p.N k ^ (p.κ * s))
    (hmesh : 2 * p.K k * p.N k ^ (-99 * s) ≤ p.N k ^ (-40 * s)) :
    0 < ⌈p.N k ^ (40 * s)⌉₊ ∧
      p.N k ^ (-100 * s) / p.q k s ≤ ((⌈p.N k ^ (40 * s)⌉₊ : ℕ) : ℝ)⁻¹ ∧
      ((⌈p.N k ^ (40 * s)⌉₊ : ℕ) : ℝ)⁻¹ ≤ p.N k ^ (-40 * s) := by
  have hN := Valid.N_pos p hp k
  have hN1 : 1 ≤ p.N k := by linarith [hp.N_ge k]
  have hK := Valid.K_pos p hp k
  have hP : 0 < p.N k ^ (40 * s) := Real.rpow_pos_of_pos hN _
  have hP1 : 1 ≤ p.N k ^ (40 * s) := Real.one_le_rpow hN1 (by linarith)
  have hMpos : 0 < ⌈p.N k ^ (40 * s)⌉₊ := Nat.ceil_pos.mpr hP
  have hMge : p.N k ^ (40 * s) ≤ (⌈p.N k ^ (40 * s)⌉₊ : ℝ) := Nat.le_ceil _
  have hMle : (⌈p.N k ^ (40 * s)⌉₊ : ℝ) ≤ 2 * p.N k ^ (40 * s) := by
    have := Nat.ceil_lt_add_one hP.le
    linarith
  have hMposR : (0 : ℝ) < (⌈p.N k ^ (40 * s)⌉₊ : ℝ) := by exact_mod_cast hMpos
  refine ⟨hMpos, ?_, ?_⟩
  · have hq := (q_bounds_of_resolution p hp hlo hhi).1
    have hqpos := p.q_pos k s
    have hinvq : (p.q k s)⁻¹ ≤ p.K k * p.N k ^ s := by
      have hlo' : 0 < (p.K k)⁻¹ * p.N k ^ (-p.κ * s) := by positivity
      calc (p.q k s)⁻¹ ≤ ((p.K k)⁻¹ * p.N k ^ (-p.κ * s))⁻¹ := inv_anti₀ hlo' hq
        _ = p.K k * p.N k ^ (p.κ * s) := by
          rw [mul_inv_rev, inv_inv, show -p.κ * s = -(p.κ * s) by ring,
            Real.rpow_neg hN.le, inv_inv]
          ring
        _ ≤ p.K k * p.N k ^ s := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow_of_exponent_le hN1
          nlinarith [hp.κ_le_one]
    have hstep : p.N k ^ (-100 * s) / p.q k s ≤ p.K k * p.N k ^ (-99 * s) := by
      rw [div_eq_mul_inv]
      calc p.N k ^ (-100 * s) * (p.q k s)⁻¹ ≤ p.N k ^ (-100 * s) * (p.K k * p.N k ^ s) :=
            mul_le_mul_of_nonneg_left hinvq (Real.rpow_nonneg hN.le _)
        _ = p.K k * (p.N k ^ (-100 * s) * p.N k ^ s) := by ring
        _ = p.K k * p.N k ^ (-99 * s) := by
          rw [← Real.rpow_add hN]
          congr 2
          ring
    have hinvM : (2 * p.N k ^ (40 * s))⁻¹ ≤ ((⌈p.N k ^ (40 * s)⌉₊ : ℕ) : ℝ)⁻¹ :=
      inv_anti₀ hMposR hMle
    have hhalf : (2 * p.N k ^ (40 * s))⁻¹ = p.N k ^ (-40 * s) / 2 := by
      rw [show -40 * s = -(40 * s) by ring, Real.rpow_neg hN.le]
      field_simp
    calc p.N k ^ (-100 * s) / p.q k s ≤ p.K k * p.N k ^ (-99 * s) := hstep
      _ ≤ p.N k ^ (-40 * s) / 2 := by linarith
      _ = (2 * p.N k ^ (40 * s))⁻¹ := hhalf.symm
      _ ≤ _ := hinvM
  · calc ((⌈p.N k ^ (40 * s)⌉₊ : ℕ) : ℝ)⁻¹ ≤ (p.N k ^ (40 * s))⁻¹ := inv_anti₀ hP hMge
      _ = p.N k ^ (-40 * s) := by
        rw [show -40 * s = -(40 * s) by ring, Real.rpow_neg hN.le]

/-- **Single-depth fine palettes.** At a fixed shallow depth `s`, with a deeper depth `t`
(`30 s < κ t`) for the witnesses, a velocity separation `N^(-v)` with `240 v < s`, and `2 s < e₀`:
eventually every true label has three full-block affine entries, and almost every original
incidence follows one of the entries of a label containing it, with error
`fineLoss paletteConst K H N^(-v)` times the hidden width. -/
theorem eventually_fine_palette (hp : p.Valid) (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    (hcov : ∀ᶠ k in atTop, ∃ (M : ℕ) (L : Fin M → Fin 4 → ℝ), (M : ℝ) ≤ H k ∧
      ∀ᵐ u ∂p.μ k, ∃ a : Fin M, ∀ t ∈ Icc (0 : ℝ) 1,
        |p.x k u.1 t 3 - (L a 0 + L a 1 * t + L a 2 * p.x k u.1 t 1 +
          L a 3 * p.x k u.1 t 2)| ≤ H k)
    {s t v : ℝ} (hs : 0 < s) (hdeep : 30 * s < p.κ * t) (htU : t ≤ p.U)
    (hv : 0 < v) (hvs : 240 * v < s) (he₀ : 2 * s < p.e₀) :
    ∀ᶠ k in atTop, ∃ L : Fin (p.n k s) → Fin 3 → Fin 4 → ℝ,
      ∀ᵐ u ∂p.μ k, u ∈ paletteEvent (fun l τ => point (p.b k l) τ) (p.B k s)
        (fun i => p.I k s i) L (p.a k s)
        (fineLoss paletteConst (p.K k) (H k) (p.N k ^ (-v))) := by
  classical
  have hκ := hp.κ_pos
  have hκ1 := hp.κ_le_one
  have ht : 0 < t := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hst : s < t := by nlinarith
  have hsU : s ≤ p.U := hst.le.trans htU
  let R : ℝ := 2 + s⁻¹ + t⁻¹
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hR : 1 < R := by dsimp [R]; linarith
  have hsR : R⁻¹ ≤ s := by
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hsi hle
  have htR : R⁻¹ ≤ t := by
    have hle : t⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hti hle
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.N_ge k]
  filter_upwards [hp.labels R hR,
    eventually_parent_nearby_velocities p hp hs hst htU hv,
    eventually_heavy_filling p hp H hH hHsub hs,
    hcov,
    eventually_fine_proximity p.N p.K hN1 hp.N_lim hp.K_ge hp.K_sub hs hdeep,
    eventually_fine_smallness p.N p.K hN1 hp.N_lim hp.K_ge hp.K_sub hs hκ1 he₀,
    eventually_fine_loss p.N p.K H hN1 hp.N_lim hp.K_ge hH hp.K_sub hHsub
      (le_trans zero_le_one one_le_paletteConst) hvs,
    eventually_heavy_branch_mass p hp H hH hHsub hs,
    eventually_fine_mesh_count p hp hs]
    with k hlab hwit hfill hcovk hprox hsmallk hloss hmassk hmeshk
  unfold Model.ParentNearbyVelocities at hwit
  obtain ⟨hTlo, hThi, hABs, _, hLab, hcover, _⟩ := hlab s hsR hsU
  obtain ⟨hTlot, hThit, _, _, _, _, _⟩ := hlab t htR htU
  obtain ⟨Mc, Lc, hMc, hcovae⟩ := hcovk
  have hN := Valid.N_pos p hp k
  have hK := Valid.K_pos p hp k
  have hK1 := hp.K_ge k
  have hH1 := hH k
  have hHpos : 0 < H k := by linarith
  have hqt : p.q k t ≤ p.K k * p.N k ^ (-p.κ * t) :=
    (q_bounds_of_resolution p hp hTlot hThit).2
  have hqs : (p.K k)⁻¹ * p.N k ^ (-p.κ * s) ≤ p.q k s :=
    (q_bounds_of_resolution p hp hTlo hThi).1
  have hθ : 0 < p.N k ^ (-v) := Real.rpow_pos_of_pos hN _
  have hθ1 : p.N k ^ (-v) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith)
  have hμ1 : 1 ≤ labelμ (p.K k) (p.N k ^ (-v)) := one_le_labelμ hK1 hθ hθ1
  have hloss0 : 0 ≤ fineLoss paletteConst (p.K k) (H k) (p.N k ^ (-v)) := by
    rw [fineLoss_eq_labelΛ]
    exact mul_nonneg (le_trans zero_le_one one_le_paletteConst) (by positivity)
  obtain ⟨hεq, hsm⟩ := hsmallk (p.q k s) (labelμ (p.K k) (p.N k ^ (-v)))
    (fineLoss paletteConst (p.K k) (H k) (p.N k ^ (-v))) (p.q_pos k s) hqs hμ1 hloss0 hloss
  obtain ⟨hMpos, hres, hM40⟩ := mesh_count_bounds p hp hs hTlo hThi hmeshk
  -- The good set: original good points, away from the dyadic endpoints of depth `s`,
  -- with a regular event and three parent witnesses in every shallow label containing them.
  let G : Set (α × ℝ) := {u | p.GoodPoint k u ∧
    (∀ a : ℤ, u.2 ≠ (a : ℝ) / (2 : ℝ) ^ p.T k s) ∧
    ∀ i : Fin (p.n k s), u.1 ∈ p.B k s i → u.2 ∈ p.I k s i →
      (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 (p.F k s i))| ∧
      ∃ w : Fin 3 → α × ℝ,
        (∀ e, (w e).1 ∈ p.B k s i ∧ (w e).2 ∈ p.I k s i ∧
          p.GoodPoint k (w e) ∧
          (p.K k)⁻¹ ≤ |eval (p.x k (w e).1 (w e).2) (pderiv 3 (p.F k s i))| ∧
          ‖p.base k (w e) - p.base k u‖ ≤ 6 * p.K k ^ 2 * p.q k t) ∧
        ∀ e e', e ≠ e' → p.N k ^ (-v) < |p.b k (w e).1 3 - p.b k (w e').1 3|}
  have hGae : ∀ᵐ u ∂p.μ k, u ∈ G := by
    have : IsProbabilityMeasure (p.ν k) := (hp.basic k).2.1
    filter_upwards [Valid.ae_good p hp k,
      ae_time_away_from_endpoints (p.μ k) (p.ν k) (ENNReal.ofReal (p.K k))
        (hp.basic k).2.2.2.1 (p.T k s), hwit] with u hg haway hw
    exact ⟨hg, haway, hw⟩
  obtain ⟨C₀, hC₀m, hC₀G, hC₀ae⟩ := exists_measurable_conull_core (p.μ k) G hGae
  have hlabel : ∀ i : Fin (p.n k s), ∃ L : Fin 3 → Fin 4 → ℝ, ∀ l ∈ p.B k s i,
      (∃ τ ∈ p.I k s i, (p.K k)⁻¹ ≤ |eval (p.x k l τ) (pderiv 3 (p.F k s i))|) →
      ∃ u : Fin 3, ∀ τ ∈ p.I k s i,
        |p.x k l τ 3 - (L u 0 + L u 1 * τ + L u 2 * p.x k l τ 1 + L u 3 * p.x k l τ 2)| ≤
          fineLoss paletteConst (p.K k) (H k) (p.N k ^ (-v)) * p.a k s := by
    intro i
    have hi := hLab i
    obtain ⟨a, hCm, hCmass⟩ := exists_heavy_measurable_label_state p hp hi hHpos hMc Lc
      hcovae (hABs i).2.1 C₀ hC₀m hC₀ae
    set Cs := ((p.B k s i ×ˢ p.I k s i) ∩ C₀) ∩ p.residualEvent k (Lc a) (H k) with hCsdef
    have hCsG : ∀ u ∈ Cs, u ∈ G := fun u hu => hC₀G hu.1.2
    have hCsBI : ∀ u ∈ Cs, u.1 ∈ p.B k s i ∧ u.2 ∈ p.I k s i := fun u hu => hu.1.1
    -- The heavy branch carries a fixed power of the original mass.
    have hmass6 : ENNReal.ofReal (p.N k ^ (-6 * s)) ≤ p.μ k Cs := by
      have hfloor := label_reference_floor p hp hi hThi
      calc ENNReal.ofReal (p.N k ^ (-6 * s))
          ≤ ENNReal.ofReal (1 / (2 * p.K k * H k) *
              ((p.K k)⁻¹ ^ (4 : ℕ) * p.N k ^ (-(p.d + 4 * p.κ) * s))) :=
            ENNReal.ofReal_le_ofReal hmassk
        _ = ENNReal.ofReal (1 / (2 * p.K k * H k)) *
              ENNReal.ofReal ((p.K k)⁻¹ ^ (4 : ℕ) * p.N k ^ (-(p.d + 4 * p.κ) * s)) :=
            ENNReal.ofReal_mul (by positivity)
        _ ≤ ENNReal.ofReal (1 / (2 * p.K k * H k)) *
              (ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i)) := mul_le_mul le_rfl hfloor bot_le bot_le
        _ ≤ p.μ k Cs := hCmass
    have hgoodC : ∀ u ∈ Cs, p.GoodPoint k u := fun u hu => (hCsG u hu).1
    have hcloseC : ∀ u ∈ Cs,
        |p.x k u.1 u.2 3 - eval (p.x k u.1 u.2) (affineBase (Lc a))| ≤ H k :=
      fun u hu => hu.2
    have hfitC : ∀ u ∈ Cs, |eval (p.x k u.1 u.2) (p.F k s i)| ≤ p.K k * p.a k s ∧
        |eval (p.x k u.1 u.2) (pderiv 3 (p.F k s i))| ≤ p.K k ∧
        |eval (p.x k u.1 u.2) (pderiv 3 (pderiv 3 (p.F k s i)))| ≤ p.K k / p.a k s ∧
        (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 (p.F k s i))| := by
      intro u hu
      obtain ⟨hub, hut⟩ := hCsBI u hu
      have hf := hi.2.2.2.2.2.2.1 u.1 hub u.2 hut
      exact ⟨hf.1, hf.2.1, hf.2.2, ((hCsG u hu).2.2 i hub hut).1⟩
    have htimeC : ∀ u ∈ Cs, p.base k u 0 ∈
        Ico (p.blockStart k s i) (p.blockStart k s i + p.q k s) := by
      intro u hu
      have h0 : p.base k u 0 = u.2 := by simp [Model.base]
      rw [h0]
      exact p.time_mem_Ico_of_away (hCsBI u hu).2 (hCsG u hu).2.1
    obtain ⟨E, _, hEt, hEvol, hEnear⟩ := hfill i hi (p.block_geometry k s i).2
      (equal_rate_width_bounds p hp hTlo hThi).2 Cs hCm hmass6
      (1 / (2 * p.K k * H k)) (by positivity) hCmass (Lc a) (p.F k s i)
      hi.2.2.2.2.1 hgoodC hcloseC hfitC (p.blockStart k s i) htimeC
      ⌈p.N k ^ (40 * s)⌉₊ hMpos hres
    have hvol : ENNReal.ofReal (fineLam (p.K k) (H k) * p.q k s ^ 4) ≤ volume E := by
      rw [← fineLam_eq hK hHpos]
      exact hEvol
    have hEt' : ∀ z ∈ E, z 0 ∈ p.I k s i := by
      intro z hz
      rw [p.I_eq_block]
      exact hEt z hz
    have hwitE : ∀ z ∈ E, ∃ w : Fin 3 → α × ℝ,
        (∀ e, (w e).1 ∈ p.B k s i ∧ (w e).2 ∈ p.I k s i ∧ p.GoodPoint k (w e) ∧
          (p.K k)⁻¹ ≤ |eval (p.x k (w e).1 (w e).2) (pderiv 3 (p.F k s i))| ∧
          ∀ c, |p.base k (w e) c - z c| ≤ p.N k ^ (-30 * s)) ∧
        ∀ e e', e ≠ e' → p.N k ^ (-v) ≤ |p.b k (w e).1 3 - p.b k (w e').1 3| := by
      intro z hz
      obtain ⟨u, hu, hzu⟩ := hEnear z hz
      obtain ⟨hub, hut⟩ := hCsBI u hu
      obtain ⟨_, w, hw, hsep⟩ := (hCsG u hu).2.2 i hub hut
      refine ⟨w, fun e => ⟨(hw e).1, (hw e).2.1, (hw e).2.2.1, (hw e).2.2.2.1, fun c => ?_⟩,
        fun e e' hne => (hsep e e' hne).le⟩
      have h1 : |p.base k (w e) c - p.base k u c| ≤ 6 * p.K k ^ 2 * p.q k t := by
        have := norm_le_pi_norm (p.base k (w e) - p.base k u) c
        rw [Real.norm_eq_abs, Pi.sub_apply] at this
        exact this.trans (hw e).2.2.2.2
      have h2 : |p.base k u c - z c| ≤ ((⌈p.N k ^ (40 * s)⌉₊ : ℕ) : ℝ)⁻¹ := by
        rw [abs_sub_comm]
        exact hzu c
      have h3 := hprox (p.q k t) hqt
      calc |p.base k (w e) c - z c|
          = |(p.base k (w e) c - p.base k u c) + (p.base k u c - z c)| := by
            congr 1; ring
        _ ≤ |p.base k (w e) c - p.base k u c| + |p.base k u c - z c| := abs_add_le _ _
        _ ≤ 6 * p.K k ^ 2 * p.q k t + p.N k ^ (-40 * s) := by linarith
        _ ≤ p.N k ^ (-30 * s) := by linarith
    have hsmall' : paletteConst * labelΛ (p.K k) (p.N k ^ (-v)) (fineLam (p.K k) (H k)) ^ 80 *
        (p.N k ^ (-p.e₀) / (p.q k s * labelμ (p.K k) (p.N k ^ (-v))) +
          7 * p.K k * p.N k ^ (-30 * s) / p.q k s ^ 2) ≤ 1 := by
      rw [← fineLoss_eq_labelΛ]
      exact hsm
    obtain ⟨L, hL⟩ := label_entries_of_witnessed_region p hp hi hTlo hThi (hABs i).2.2 hθ hθ1
      (Real.rpow_nonneg hN.le _) (fineLam_pos hK1 hH1) (fineLam_le_one hK1 hH1) hεq hsmall'
      E hEt' hvol hwitE
    refine ⟨L, fun l hl hev => ?_⟩
    obtain ⟨u, hu⟩ := hL l hl hev
    refine ⟨u, fun τ hτ => (hu τ hτ).trans_eq ?_⟩
    rw [fineLoss_eq_labelΛ]
  choose L hL using hlabel
  refine ⟨L, ?_⟩
  have hreg : ∀ᵐ u ∂p.μ k, ∀ i : Fin (p.n k s), u.1 ∈ p.B k s i → u.2 ∈ p.I k s i →
      (p.K k)⁻¹ ≤ |eval (p.x k u.1 u.2) (pderiv 3 (p.F k s i))| :=
    ae_all_iff.mpr (fun i => (hLab i).2.2.2.2.2.2.2)
  filter_upwards [hcover, hreg] with u hu hr
  obtain ⟨i, hui, huti⟩ := hu
  obtain ⟨w, hw⟩ := hL i u.1 hui ⟨u.2, huti, hr i hui huti⟩
  exact ⟨i, w, hui, huti, hw⟩

end Model

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
