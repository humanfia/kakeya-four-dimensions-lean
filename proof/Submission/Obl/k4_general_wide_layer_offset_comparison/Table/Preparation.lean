import Submission.Obl.k4_general_wide_layer_offset_comparison.TableCore
import Submission.Obl.k4_general_wide_layer_offset_comparison.ActualNativeParentLists
import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.ActualGoodData
import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.BoundedTable
import Submission.Obl.k4_local_algebraic_graph_matching

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter
open Submission.Obl.k4_contact_affine_residual_candidate_transfer

noncomputable section

/-- Actual original comparisons and the finite reference budgets give the
single-height table preparation required for simultaneous floor renewal. -/
theorem tablePreparation : TablePreparation := by
  classical
  intro hMatch α _ p hp r u v m hexp H₀ σ L₀ hH₀ hH₀s hσ hL₀ hcover₀ hcoeff₀
  rcases hexp with ⟨⟨hr, hv, hvr, h100, hℓm, htop⟩, hu, hur, hvsmall, hmr, hgap⟩
  have hd := hp.dimension_nonneg
  have hd1 := hp.dimension_lt_one
  have hℓ := hp.transverse_pos
  have hκ := hp.rate_pos
  have hκ1 := hp.rate_le_one
  have hm : 0 < m := by nlinarith
  have hvu : v ≤ u := by nlinarith [mul_nonneg hd hu.le]
  have hκr : p.κ * r ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hκ1 hr.le
  have hmroom : (p.κ + p.ℓ) * r < m := by nlinarith [mul_pos hℓ hr]
  have huκ : u * p.κ ≤ u := by nlinarith
  have hu3m : u ≤ 3 * m / p.κ := (le_div_iff₀ hκ).mpr (by nlinarith)
  have hU : r + u ≤ p.U := by linarith
  have hgap' : (10 / (1 - p.d) + 1 + p.ℓ) * u < p.κ * r := by nlinarith
  have hC : 0 ≤ 10 / (1 - p.d) := by positivity
  have hℓu : p.ℓ * u < p.κ * r := by nlinarith
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.scale k]
  have hN0 : ∀ k, 0 ≤ p.N k := fun k => zero_le_one.trans (hN1 k)
  let H : ℕ → ℝ := fun k => H₀ k ^ 2
  have hH₀H (k : ℕ) : H₀ k ≤ H k := by dsimp [H]; nlinarith [(hH₀ k).1]
  have hH2 (k : ℕ) : 2 ≤ H k := (hH₀ k).1.trans (hH₀H k)
  have hH (k : ℕ) : 1 ≤ H k := by linarith [hH2 k]
  have hKH (k : ℕ) : p.K k ≤ H k := (hH₀ k).2.trans (hH₀H k)
  have hH₀small : Small p.N H₀ :=
    ⟨Eventually.of_forall (fun k => by linarith [(hH₀ k).1]), hH₀s⟩
  have hHsmall : Small p.N H := hH₀small.pow hN0 hp.scale_limit 2
  let L : ℕ → Fin 3 → ProjectedLayer α := fun k a =>
    (L₀ k a).withWidth (min (L₀ k a).β (p.N k ^ (-p.ℓ * r)))
  have hL (k : ℕ) (a : Fin 3) : (L k a).Valid p k (![r, r + u, r + v] a) m (H k) := by
    apply ProjectedLayer.cap_at_depth_valid hp (hL₀ k a)
      (by linarith [(hH₀ k).1])
    fin_cases a
    · exact le_rfl
    · change r ≤ r + u
      linarith
    · change r ≤ r + v
      linarith
  have hβg (k : ℕ) (a : Fin 3) : (L k a).β ≤ p.N k ^ (-p.ℓ * r) := min_le_right _ _
  have hcover (k : ℕ) (a : Fin 3) : (L k a).Covers (σ k) := hcover₀ k a
  have hcoeff : ∀ᶠ k in atTop, ∀ a i e, |((L k a).G i).coeff e| ≤ p.N k ^ (m / 1000) := hcoeff₀
  have hmass (k : ℕ) : ENNReal.ofReal ((H k)⁻¹) ≤ σ k univ :=
    (ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith [(hH₀ k).1]) (hH₀H k))).trans (hσ k).2
  have hLzero (k : ℕ) : (L k 0).Valid p k r m (H k) := hL k 0
  obtain ⟨J, hJ, hJs, hnative⟩ := p.actual_native_parent_lists hp hMatch hr (by linarith)
    hmroom H hH2 hKH hHsmall.2 (fun k => L k 0) hLzero σ
    (fun k => (hσ k).1) hmass (fun k => hcover k 0)
  have hJ1 (k : ℕ) : 1 ≤ J k := by linarith [(hJ k).1]
  have hGraph : Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Matching :=
    Submission.k4_local_algebraic_graph_matching hMatch
  obtain ⟨δ, hδ, hδ1, hδs, hgood⟩ := p.exists_actual_good_data hp hGraph hr hu hv.le hvu
    hU hm hmroom hgap' H J hH hKH hHsmall.2 hJ1 hJs σ
    (fun k => (hσ k).1) L hL hβg hcover hcoeff hnative
  have hD1 (k : ℕ) : 1 ≤ (δ k)⁻¹ := by
    simpa only [inv_one] using inv_anti₀ (hδ k) (hδ1 k)
  let F : ℕ → ℝ := fun k => finalTableHeight (p.K k) (H k) p.d (J k) (δ k)⁻¹
  let R : ℕ → ℝ := fun k => tableReferenceBudget (p.K k) (H k) p.d (J k) (δ k)⁻¹
  have hspec (k : ℕ) := finalTableHeight_spec (hp.subpower.1 k) (hH k) hd (hJ1 k) (hD1 k)
  have hKsmall : Small p.N p.K :=
    ⟨Eventually.of_forall (fun k => zero_le_one.trans (hp.subpower.1 k)), hp.subpower.2⟩
  have hJsmall : Small p.N J :=
    ⟨Eventually.of_forall (fun k => by linarith [hJ1 k]), hJs⟩
  have hDsmall : Small p.N (fun k => (δ k)⁻¹) :=
    ⟨Eventually.of_forall (fun k => (inv_pos.mpr (hδ k)).le), hδs⟩
  have hFsmall := (finalTableHeight_small hN1 hp.scale_limit hd hKsmall hHsmall hJsmall hDsmall).2
  have hgoodF := hgood F (fun k => (hspec k).1) (fun k => (hspec k).2.1)
    (fun k => (hspec k).2.2.1) hFsmall.2
  have hshort := p.eventually_short_layer_geometry hp hu.le hvu hℓu hmroom
    H hH hKH hHsmall.2 L hL
  intro ε hε
  filter_upwards [hgoodF, hshort, hFsmall.2 ε hε] with k hgoodk hshortk hFk
  obtain ⟨t, htL, htδ, htJ, hmass⟩ := hgoodk
  rcases hspec k with ⟨hF2, hKF, hHF, h3HF, h10KF, hR1, hfloor, hco, hfi, hoff, hrev⟩
  have htshort : ∀ a, (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) ≤ (t.layers a).β := by
    intro a
    rw [htL]
    exact (hshortk t.R t.atDepth).2.2 a
  have htβg : ∀ a, (t.layers a).β ≤ p.N k ^ (-p.ℓ * r) := by
    intro a
    rw [htL]
    exact hβg k a
  obtain ⟨table, htlaw⟩ := t.exists_budgeted_table hF2 (hH k) hHF h3HF h10KF
    hu.le hv.le hd (by rw [htJ]; linarith [hJ1 k])
    (by simpa only [htJ] using hco)
    (by simpa only [htδ] using hfi)
    (by simpa only [htδ] using hoff)
    (by simpa only [htJ, htδ] using hrev) htshort htβg
  have htable : ∃ t' : p.ComparisonTable k r u v m (F k) (R k),
      ENNReal.ofReal ((4 * J k)⁻¹) ≤ t'.law univ := by
    have hR : tableReferenceBudget (p.K k) (H k) p.d t.Knat t.δ⁻¹ = R k := by
      rw [htJ, htδ]
    have htransport {R₀ R₁ : ℝ} (h : R₀ = R₁)
        (s : p.ComparisonTable k r u v m (F k) R₀) : (h ▸ s).law = s.law := by
      subst R₁
      rfl
    refine ⟨hR ▸ table, ?_⟩
    rw [htransport hR table, htlaw]
    exact hmass
  exact ⟨F k, 4 * J k, R k, hKF, hFk, by linarith [hJ1 k], hR1, hfloor, htable⟩

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
