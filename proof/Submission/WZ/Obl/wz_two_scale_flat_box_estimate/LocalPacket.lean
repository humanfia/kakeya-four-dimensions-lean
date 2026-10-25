-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.LocalPacket.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Analytic
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Scalars
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.PacketNumerics
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxRegularization
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxSlabs
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.HullDensity
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.ParentSelection
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Reindex

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridKeys gridCell gridUnion gridUnion_measurable gridUnion_volume_ne_top)
open WangZahlLot.Obl.wz_flat_factored_improvement (BodySlabCount flatMap)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (closedTube)

set_option maxHeartbeats 1200000 in
/-- One occupied box produces a dense union of short-scale cubes, together with
one uniform lower bound for the density of the original shading in every cube. -/
theorem local_box_packet {σ ω ε A η d δ ρ a b c D F Fmax : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hA : 0 < A)
    (H : FineBoxBound σ ω ε A η d)
    (hδ : 0 < δ) (hδd : δ ≤ d) (hδa : δ ≤ a) (hρ : 0 < ρ) (hρa : ρ ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hc : 1 ≤ c) (hc8 : c ≤ 8) (haSmall : a ≤ 1 / 100)
    (hD : 432 ≤ D) (hF : 0 < F) (hFmax : 0 < Fmax)
    (K Kc : ℕ) (hK : 0 < K) (hreg : 224 * (K : ℝ) ≤ D)
    (hlog : (10 : ℝ) ^ (16 : ℕ) * (Kc + 1 : ℕ) ≤ D)
    (hbottom : (1 / 2 : ℝ) ^ Kc ≤ δ / 16)
    (hcut : 432 * (1 / D) ^ K * a * b ≤ (1 / D ^ (2 : ℕ)) * δ ^ 2 / 2)
    (hη : δ ^ η ≤ 1 / D ^ (3 : ℕ))
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space)
    {n N : ℕ} (hn : 0 < n) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (y w : Fin N → Space) (f : Fin n → Fin N)
    (hnmax : (n : ℝ) ≤ δ ^ (-100 : ℝ))
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1)
    (hdist : Distinct δ n x v) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hden : ∀ i, ENNReal.ofReal ((1 / D ^ (2 : ℕ)) * δ ^ 2) ≤ volume (Y i))
    (hconv : WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount δ D n x v)
    (hw : ∀ k, ‖w k‖ = 1)
    (hcontain : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i)))
    (hbox : ∀ k, Tube ρ (y k) (w k) ⊆ Box a b c z e)
    (hmeet : ∀ k, (Tube ρ (y k) (w k) ∩ ball (0 : Space) 1).Nonempty)
    (hraw : ∀ W, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {k | Tube ρ (y k) (w k) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (D * N / (a * b * c)) * volume W)
    (hbelow : ∀ k (u : Space) (s r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | f i = k ∧ Tube δ (x i) (v i) ⊆
        {p | |inner ℝ u p - s| ≤ r}} : ℝ) *
        volume (Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤
      ENNReal.ofReal (D * Fmax) * volume
        (Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩
          {p | |inner ℝ u p - s| ≤ r}))
    (hparent : ∀ k, (Set.ncard {i | f i = k} : ℝ) ≤ Fmax)
    (hsize : F ≤ D ^ (3 : ℕ) * n) (hbudget : Fmax * N ≤ D ^ (5 : ℕ) * F) :
    ∃ s : Finset (Fin 3 → ℤ), s ⊆ gridKeys a ∧
      gridUnion a s ⊆ Box (6 * a) (6 * b) (6 * c) z e ∧
      ENNReal.ofReal (a * b / D ^ (19 : ℕ)) ≤ volume (gridUnion a s) ∧
      ∀ k ∈ s, cellProfile σ ω ε A δ a b F D * a ^ 3 ≤
        volume.real ((⋃ i, Y i) ∩ gridCell a k) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hDpos : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have hTbox (i : Fin n) : Tube δ (x i) (v i) ⊆ Box a b c z e :=
    (hcontain i).trans (hbox (f i))
  obtain ⟨s, t, M, j, hs, hsmeet, ht, hM, hj, hret, hind, hcell, hupper⟩ :=
    box_regularization hδ hδa hab haSmall (by positivity : 0 < 1 / D ^ (2 : ℕ))
      (by positivity : 0 < 1 / D) hK hcut z e hn x v Y hv hYm hYT
      (fun i => (hYT i).trans (hball i)) (fun i => (hYT i).trans (hTbox i)) hden
  obtain ⟨hsizeM, hdenM⟩ := regularization_losses hDpos hK hreg (Nat.cast_nonneg M) hsize hret
  let Z := fun i : Fin M => Y (j i) ∩ gridUnion a s
  have hZd (i : Fin M) : ENNReal.ofReal ((1 / D ^ (3 : ℕ)) * δ ^ 2) ≤ volume (Z i) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hdenM (sq_nonneg δ))).trans (hind i)
  have hMmax : (M : ℝ) ≤ δ ^ (-100 : ℝ) := by
    have hh : M ≤ n := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective j hj
    exact (Nat.cast_le.mpr hh).trans hnmax
  have hbalanceM : Fmax * N ≤ D ^ (11 : ℕ) * M := by
    have hh := mul_le_mul_of_nonneg_left hsizeM (by positivity : 0 ≤ D ^ 5)
    nlinarith only [hh, hbudget]
  have hbelowM : ∀ k (u : Space) (s' r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | f (j i) = k ∧ Tube δ (x (j i)) (v (j i)) ⊆
        {p | |inner ℝ u p - s'| ≤ r}} : ℝ) *
        volume (Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤
      ENNReal.ofReal (D * Fmax) * volume
        (Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩
          {p | |inner ℝ u p - s'| ≤ r}) := by
    intro k u s' r hu hr
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr
      (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.count_subfamily j hj
        (fun i => f i = k ∧ Tube δ (x i) (v i) ⊆ {p | |inner ℝ u p - s'| ≤ r})))) le_rfl).trans
      (hbelow k u s' r hu hr)
  have hslab0 := box_slab_composition hδ hρ (by linarith) ha hb hab (by linarith) hc
    hDpos.le hDpos.le hFmax.le (by positivity : 0 ≤ D ^ (11 : ℕ))
    (x ∘ j) (v ∘ j) y w (f ∘ j) z e hw (fun i => hcontain (j i))
    hbox hmeet hraw hbelowM hbalanceM Kc hbottom
  have hslab : BodySlabCount (fun i => flatMap (normalFrame b z e) a (min b 2) ha
      (lt_min hb (by norm_num)) '' closedTube δ (x (j i)) (v (j i))) (D ^ (14 : ℕ)) := by
    intro u s' r hu hr
    exact (hslab0 u s' r hu hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (slab_coefficient_budget hD1 hlog) (Nat.cast_nonneg M)) hr.le))
  have hnorm (i : Fin M) : Tube δ (x (j i)) (v (j i)) ⊆ normalFrame b z e ''
      WangZahlLot.Obl.wz_flat_factored_improvement.StandardPrism a (min b 2) := by
    intro p hp
    exact box_unitBall_subset_normalPrism ha.le hb.le z e
      ⟨hTbox (j i) hp, ball_subset_closedBall (hball (j i) hp)⟩
  have hfine := H δ a (min b 2) D (D ^ (14 : ℕ)) hδ hδd hδa
    (le_min hab (by linarith)) (min_le_right _ _) haSmall hD1 (one_le_pow₀ hD1)
    (normalFrame b z e) M (x ∘ j) (v ∘ j) Z hM hMmax
    (fun i => hv (j i)) (fun i => hball (j i)) hnorm
    (fun i k hik => hdist (j i) (j k) (fun he => hik (hj he)))
    (fun i => (hYm (j i)).inter (gridUnion_measurable a s))
    (fun i => inter_subset_left.trans (hYT (j i)))
    (fun i => (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hη (sq_nonneg δ))).trans (hZd i))
    (convexCount_subfamily x v hconv j hj) hslab
  have hVfin : volume (⋃ i, Z i) ≠ ⊤ := ne_top_of_le_ne_top (gridUnion_volume_ne_top ha s)
    (measure_mono (iUnion_subset fun _ => inter_subset_right))
  have hfine' : fineProfile σ ω ε A δ a b F / D ^ 22 ≤ volume.real (⋃ i, Z i) := by
    apply (ENNReal.ofReal_le_iff_le_toReal hVfin).mp
    exact (ENNReal.ofReal_le_ofReal (fine_scalar_lower hσ hσhalf hA hδ ha hb (hbc.trans hc8)
      hF (by linarith) (by exact_mod_cast hM) hsizeM)).trans hfine
  have htlow : cellProfile σ ω ε A δ a b F D ≤ t :=
    cellProfile_le hA hδ ha hb hF hD ht.le hfine' hupper
  have hparentM (k : Fin N) : (Set.ncard {i | f (j i) = k} : ℝ) ≤ Fmax :=
    (Nat.cast_le.mpr (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.count_subfamily j hj
      (fun i => f i = k))).trans (hparent k)
  obtain ⟨P, l, hP, hl, hPlower, _⟩ := select_distinct_parents hM (f ∘ j) hparentM
  have hNP : (N : ℝ) ≤ D ^ (11 : ℕ) * P :=
    parent_selection_losses hDpos hFmax hsizeM hbudget hPlower
  have hrawP : ∀ W, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Tube ρ (y (f (j (l i)))) (w (f (j (l i)))) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (D ^ (12 : ℕ) * P / (a * b)) * volume W := by
    intro W hW
    have hcoef : D * N / (a * b * c) ≤ D ^ (12 : ℕ) * P / (a * b) := by
      calc
        _ ≤ D * N / (a * b) := div_le_div_of_nonneg_left (by positivity) (by positivity)
          (le_mul_of_one_le_right (mul_nonneg ha.le hb.le) hc)
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith only [mul_le_mul_of_nonneg_left hNP hDpos.le]
    exact (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr
      (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.count_subfamily ((f ∘ j) ∘ l) hl
        (fun k => Tube ρ (y k) (w k) ⊆ W)))).trans
      ((hraw W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl))
  have hhull := coarse_parent_hull_density hδ hρ hδa hρa hab hbc hc8 haSmall
    (by positivity : 0 < 1 / D ^ (3 : ℕ)) (one_le_pow₀ hD1 : 1 ≤ D ^ (12 : ℕ)) z e hP
    (fun i => x (j (l i))) (fun i => v (j (l i)))
    (fun i => y (f (j (l i)))) (fun i => w (f (j (l i)))) (fun i => Z (l i)) s
    (fun i => hv (j (l i))) (fun i => hw (f (j (l i)))) (fun i => hbox (f (j (l i))))
    (fun i => inter_subset_left.trans (hYT (j (l i))))
    (fun i => inter_subset_left.trans ((hYT (j (l i))).trans (hcontain (j (l i)))))
    (fun _ => inter_subset_right) (fun i => hZd (l i)) hrawP Kc (hbottom.trans (by linarith))
  refine ⟨s, hs, gridUnion_box_subset ha hab hbc z e s hsmeet,
    (ENNReal.ofReal_le_ofReal (hull_density_budget hDpos ha hb hlog)).trans hhull, ?_⟩
  intro k hk
  exact (mul_le_mul_of_nonneg_right htlow (by positivity : 0 ≤ a ^ 3)).trans (hcell k hk)

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
