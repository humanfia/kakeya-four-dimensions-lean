import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.SlicePreparation
import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.NativeChoices
import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.ShortLayers
import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.ProjectedOffsets
import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.BandCaps
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativePaletteSupport
import Submission.Obl.k4_general_wide_layer_offset_comparison.FinalHeight
import Submission.Obl.k4_general_wide_layer_offset_comparison.FinalFloors

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter
open Submission.Obl.k4_contact_affine_residual_candidate_transfer
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Actual dense pointwise-good table data, from the native lists and the
literal three layers. The stored-witness threshold is chosen before the
final fiber height, and its inverse remains intrinsic and subpower. -/
theorem exists_actual_good_data (hp : p.Valid)
    (hMatch : Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Matching)
    {r u v m : ℝ} (hr : 0 < r) (hu : 0 < u) (hv : 0 ≤ v) (hvu : v ≤ u)
    (hU : r + u ≤ p.U) (hm0 : 0 < m) (hm : (p.κ + p.ℓ) * r < m)
    (hgap : (10 / (1 - p.d) + 1 + p.ℓ) * u < p.κ * r)
    (H Hnat : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k) (hKH : ∀ k, p.K k ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    (hHnat : ∀ k, 1 ≤ Hnat k)
    (hHnats : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Hnat k ≤ p.N k ^ ε)
    (σ : ℕ → Measure (α × ℝ)) (hσ : ∀ k, σ k ≤ p.ρ k)
    (L : ℕ → Fin 3 → ProjectedLayer α)
    (hL : ∀ k a, (L k a).Valid p k (![r, r + u, r + v] a) m (H k))
    (hβg : ∀ k a, (L k a).β ≤ p.N k ^ (-p.ℓ * r))
    (hcover : ∀ k a, (L k a).Covers (σ k))
    (hcoeff : ∀ᶠ k in atTop, ∀ a i e, |((L k a).G i).coeff e| ≤ p.N k ^ (m / 1000))
    (hnative : ∀ᶠ k in atTop, Nonempty (p.NativeParentLists k r m (Hnat k) (L k 0) (σ k))) :
    ∃ δ : ℕ → ℝ, (∀ k, 0 < δ k) ∧ (∀ k, δ k ≤ 1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (δ k)⁻¹ ≤ p.N k ^ ε) ∧
      ∀ (Hf : ℕ → ℝ), (∀ k, 2 ≤ Hf k) → (∀ k, p.K k ≤ Hf k) →
        (∀ k, H k ≤ Hf k) →
        (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Hf k ≤ p.N k ^ ε) →
        ∀ᶠ k in atTop, ∃ t : p.GoodTableData k r u v m (H k) (Hf k),
          t.layers = L k ∧ t.δ = δ k ∧ t.Knat = Hnat k ∧
          ENNReal.ofReal ((4 * Hnat k)⁻¹) ≤ t.law univ := by
  classical
  let δ : ℕ → ℝ := fun k => (2880 * Hnat k * H k ^ 3)⁻¹
  have hδ (k : ℕ) : 0 < δ k := by
    have h1 := zero_lt_one.trans_le (hH k)
    have h2 := zero_lt_one.trans_le (hHnat k)
    dsimp [δ]
    positivity
  have hδ1 (k : ℕ) : δ k ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have hp : 1 ≤ H k ^ 3 := one_le_pow₀ (hH k)
    calc
      (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ 2880 * Hnat k * H k ^ 3 := by gcongr <;> nlinarith [hHnat k]
  have hN0 : ∀ k, 0 ≤ p.N k := fun k => by linarith [hp.scale k]
  have hHs' : Small p.N H := ⟨Eventually.of_forall (fun k => by linarith [hH k]), hHs⟩
  have hHnats' : Small p.N Hnat :=
    ⟨Eventually.of_forall (fun k => by linarith [hHnat k]), hHnats⟩
  have hδs : Small p.N (fun k => (δ k)⁻¹) := by
    have hc := Small.const hp.scale_limit (by norm_num : (0 : ℝ) ≤ 2880)
    have hs := (hc.mul hN0 hHnats').mul hN0 (hHs'.pow hN0 hp.scale_limit 3)
    simpa only [δ, inv_inv] using hs
  let ν : ℕ → Measure (α × ℝ) := fun k =>
    if h : Nonempty (p.NativeParentLists k r m (Hnat k) (L k 0) (σ k))
      then (Classical.choice h).law else 0
  have hν (k : ℕ) : ν k ≤ σ k := by
    dsimp only [ν]
    split_ifs with h
    · exact (Classical.choice h).le_source
    · exact bot_le
  let Fits (k : ℕ) : Prop := ∀ a,
    (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) ≤ (L k a).β
  have hθchoice (k : ℕ) : ∃ θ : Measure (α × ℝ), θ ≤ ν k ∧
      (Fits k → ν k univ ≤ θ univ + ENNReal.ofReal (720 * δ k * H k ^ 3) ∧
        ∀ᵐ ω ∂θ, p.StoredWitnessAt k r u v m (δ k) (L k) θ ω) := by
    by_cases hfit : Fits k
    · obtain ⟨θ, hθ, hmθ, hwθ⟩ := p.exists_stored_short_witnesses hp (hH k) (hδ k)
        (L k) (hL k) hfit (hβg k) (ν k) ((hν k).trans (hσ k))
        (fun a => (hcover k a).filter_mono (ae_mono (hν k)))
      exact ⟨θ, hθ, fun _ => ⟨hmθ, hwθ⟩⟩
    · exact ⟨0, bot_le, fun h => (hfit h).elim⟩
  choose θ hθ hθdata using hθchoice
  have hθρ (k : ℕ) : θ k ≤ p.ρ k := (hθ k).trans ((hν k).trans (hσ k))
  have hθcover (k : ℕ) (a : Fin 3) : (L k a).Covers (θ k) :=
    (hcover k a).filter_mono (ae_mono ((hθ k).trans (hν k)))
  let R : ℝ := 2 + r + m + r⁻¹ + m⁻¹
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hminv : 0 < m⁻¹ := inv_pos.mpr hm0
  have hR : 1 < R := by dsimp [R]; linarith
  have hRr : R⁻¹ ≤ r := by
    have hh := inv_anti₀ hrinv (show r⁻¹ ≤ R by dsimp [R]; linarith)
    simpa only [inv_inv] using hh
  have hRm : R⁻¹ ≤ m := by
    have hh := inv_anti₀ hminv (show m⁻¹ ≤ R by dsimp [R]; linarith)
    simpa only [inv_inv] using hh
  have hmR : m ≤ R := by dsimp [R]; linarith
  have hC : 0 ≤ 10 / (1 - p.d) := by have := hp.dimension_lt_one; positivity
  have hshort := p.eventually_short_layer_geometry hp hu.le hvu
    (show p.ℓ * u < p.κ * r by nlinarith) hm H hH hKH hHs L hL
  have hgeom : ∀ᶠ k in atTop, p.AtDepth k r R ∧
      p.N k ^ (-m) ≤ (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) ∧
      p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r) ∧ Fits k := by
    filter_upwards [hp.prepared R hR, hshort] with k hk hs
    have hat := hk r hRr (by linarith)
    exact ⟨hat, hs R hat⟩
  have hmassθ : ∀ᶠ k in atTop, ENNReal.ofReal ((2 * Hnat k)⁻¹) ≤ θ k univ := by
    filter_upwards [hgeom, hnative] with k hg hn
    have hθk := hθdata k hg.2.2.2
    have hmassν : ENNReal.ofReal ((Hnat k)⁻¹) ≤ ν k univ := by
      simpa only [ν, dif_pos hn] using (Classical.choice hn).mass_lower
    letI : IsFiniteMeasure (p.μ k) := Basic.finite_mu p hp.basic k
    haveI : IsFiniteMeasure (ν k) :=
      isFiniteMeasure_of_le (p.μ k) ((hν k).trans ((hσ k).trans (hp.basic k).2.2.2.2.1))
    have hHp : 0 < H k := zero_lt_one.trans_le (hH k)
    have hHnp : 0 < Hnat k := zero_lt_one.trans_le (hHnat k)
    have hcost : 720 * δ k * H k ^ 3 = (4 * Hnat k)⁻¹ := by
      dsimp only [δ]
      field_simp
      ring
    have hsmall : 720 * δ k * H k ^ 3 ≤ (Hnat k)⁻¹ / 2 := by
      rw [hcost, mul_inv]
      norm_num
      nlinarith [inv_nonneg.mpr hHnp.le]
    have hh := half_mass_of_loss_budget (ν k) (θ k) (hθ k) (by positivity)
      (by positivity) hmassν hθk.1 hsmall
    convert hh using 1 <;> congr 1 <;> field_simp
  refine ⟨δ, hδ, hδ1, hδs.2, ?_⟩
  intro Hf hHf hKHf hHH hHfs
  obtain ⟨c, hc, hproj⟩ := p.eventually_projected_table_offsets hp hMatch hr hu hv hvu
    hU hm0 hm hgap H Hf hH hKH hHs hHf hKHf hHH hHfs θ hθρ L hL hθcover
  have hsmall := eventually_power_loss_le_inverse
    (fun k => by linarith [hp.scale k] : ∀ k, 1 ≤ p.N k) hp.scale_limit
    hHnat hHnats hc (by norm_num : (0 : ℝ) < 8)
  have hbands := p.eventually_short_band_cap hp hr (by linarith) hm
    (show 0 ≤ r + u by linarith)
  filter_upwards [hgeom, hnative, hmassθ, hproj, hsmall, hcoeff, hbands]
    with k hg hn hmθ hpk hsk hck hbk
  obtain ⟨E, hE, hbad, hoffsets⟩ := hpk
  let law := (θ k).restrict Eᶜ
  let n := Classical.choice hn
  have hνeq : ν k = n.law := by simp only [ν, dif_pos hn, n]
  have hlθ : law ≤ θ k := Measure.restrict_le_self
  have hlν : law ≤ ν k := hlθ.trans (hθ k)
  have hlρ : law ≤ p.ρ k := hlθ.trans (hθρ k)
  have hlμ : law ≤ p.μ k := hlρ.trans (hp.basic k).2.2.2.2.1
  have hfiniteμ : IsFiniteMeasure (p.μ k) := Basic.finite_mu p hp.basic k
  letI := hfiniteμ
  haveI : IsFiniteMeasure (θ k) := isFiniteMeasure_of_le (p.μ k)
    ((hθρ k).trans (hp.basic k).2.2.2.2.1)
  have hHnp : 0 < Hnat k := zero_lt_one.trans_le (hHnat k)
  have hbadSmall : 2 * p.N k ^ (-c) ≤ ((2 * Hnat k)⁻¹) / 2 := by
    calc
      _ ≤ 2 * (8 * Hnat k)⁻¹ := mul_le_mul_of_nonneg_left hsk (by norm_num)
      _ = _ := by field_simp; ring
  have hbudget : θ k univ ≤ law univ + ENNReal.ofReal (2 * p.N k ^ (-c)) := by
    have heq : θ k univ = law univ + θ k E := by
      simpa only [law, Measure.restrict_apply_univ, add_comm] using
        (measure_add_measure_compl hE (μ := θ k)).symm
    rw [heq]
    exact add_le_add le_rfl hbad
  have hmass := half_mass_of_loss_budget (θ k) law hlθ (by positivity)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (hN0 k) _))
    hmθ hbudget hbadSmall
  have hmass' : ENNReal.ofReal ((4 * Hnat k)⁻¹) ≤ law univ := by
    convert hmass using 1 <;> congr 1 <;> field_simp <;> norm_num
  have hpalette := (AtDepth.ae_positive_palette p hp.basic hg.1 (by linarith [hp.subpower.1 k]) hRm hmR).filter_mono
    (ae_mono hlμ)
  have hlNative : law ≤ n.law := by simpa only [hνeq] using hlν
  have hnativeAll := (n.ae_all_choices hp.basic
    ((hσ k).trans (hp.basic k).2.2.2.2.1) hg.1 (hL k 0)).filter_mono
      (ae_mono hlNative)
  obtain ⟨t, htlaw, htlayers, -, htδ, htKnat⟩ := p.exists_goodTableData_of_ae hp hg.1
    hg.2.1 hg.2.2.1 (L k) (hL k) hck law hlρ
    (fun a => (hcover k a).filter_mono (ae_mono (hlν.trans (hν k))))
    hpalette (hoffsets.mono fun ω hω => hω R hg.1) (θ k)
    ((hθρ k).trans (hp.basic k).2.2.2.2.1) (hδ k)
    ((hθdata k hg.2.2.2).2.filter_mono (ae_mono hlθ))
    (Hnat k) n.forwardByCode n.reverseByCode
    (fun Q c => n.coarse_card Q c.1) (fun i c => n.reverse_card c.1 c.2 i) hnativeAll
    (r + u) (by
      intro c
      fin_cases c
      · exact le_rfl
      · change r + v ≤ r + u
        linarith)
    (hbk (θ k) ((hθρ k).trans (hp.basic k).2.2.2.2.1))
  refine ⟨t, htlayers, htδ, htKnat, ?_⟩
  rw [htlaw]
  exact hmass'

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
