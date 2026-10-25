-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedPrismStage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedWiden
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedNet
import Submission.WZ.Obl.wz_broad_grains_improvement.PrismSelection
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketCore
import Submission.WZ.Obl.wz_coarse_subtube_selection.Reindex
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorDyadic

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses G)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData G_iff_data)
open WangZahlLot.Obl.wz_coarse_subtube_selection (reindex reindex_mem reindex_injective sum_reindex)

set_option maxHeartbeats 1000000

/-- Extending the angular scale costs only its fixed dilation to the broadness
exponent, including the radii larger than the original scale. -/
theorem aligned_broad_enlarge {d h h' ρ β : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hh : 0 ≤ h) (hρ : 0 < ρ) (hβ : 0 ≤ β)
    (hbudget : d^(-h) * (10000:ℝ)^β ≤ d^(-h'))
    {n : ℕ} {v : Fin n → V} {W : Fin n → Set V}
    (hbroad : ∀ p u r, ‖u‖ = 1 → d ≤ r → r ≤ ρ →
      q n {i | p ∈ W i ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ≤
        d^(-h)*(r/ρ)^β*q n {i | p ∈ W i}) :
    ∀ p u r, ‖u‖ = 1 → d ≤ r → r ≤ 10000*ρ →
      q n {i | p ∈ W i ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ≤
        d^(-h')*(r/(10000*ρ))^β*q n {i | p ∈ W i} := by
  intro p u r hu hr _
  have hr0 : 0 < r := hd.trans_le hr
  apply WangZahlLot.Obl.wz_move_two_dense_broad_prisms.broad_scale_change
    (B := d^(-h)) (β := β) hr0 hρ (by positivity : 0 < 10000*ρ) ?_ ?_
  · simpa only [mul_div_cancel_right₀ (10000:ℝ) hρ.ne'] using hbudget
  · by_cases hrρ : r ≤ ρ
    · exact hbroad p u r hu hr hrρ
    · have hB : 1 ≤ d^(-h) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith)
      have hpow : 1 ≤ (r/ρ)^β := Real.one_le_rpow (by
        rw [le_div_iff₀ hρ]
        linarith) hβ
      have hcount : q n {i | p ∈ W i ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ≤
          q n {i | p ∈ W i} := by
        exact_mod_cast Set.ncard_mono (show {i : Fin n | p ∈ W i ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ⊆ {i | p ∈ W i} from fun i hi => hi.1)
      exact hcount.trans (le_mul_of_one_le_left (by positivity)
        (one_le_mul_of_one_le_of_one_le hB hpow))

/-- Scalar-aligned fine families have strict stage-one coarse covers for
prisms of length at most one. The loss consists of fixed grid, width and angular factors. -/
theorem aligned_prism_stage_one_data {d h h' ρ c ω ζ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : 0 ≤ h) (hβ : 0 ≤ ω*ζ/100)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/100000000)
    (hretain : alignedGridCost * d^h' ≤ d^h)
    (hdensity : 10000*d^h' ≤ d^h)
    (hbroadbudget : d^(-h)*(10000:ℝ)^(ω*ζ/100) ≤ d^(-h'))
    {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {u : V} {t : ℝ}
    (hunit : ∀ i, ‖v i‖ = 1) (hcap : ∀ i, ‖v i-u‖ ≤ 1/10)
    (hmid : ∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1)
    (halign : ∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = t)
    (hYfin : ∀ i, μ (Y i) ≠ ⊤) (hYpos : 0 < ∑ i, volume.real (Y i))
    (D₀ : PrismData n) (hG : D₀.Valid ω ζ d h ρ c x v Y 0) :
    ∃ D' : PrismData n, D'.Valid ω ζ d h' (10000*ρ) c x v Y 1 ∧ PrismSelection D₀ D' := by
  classical
  rcases D₀ with ⟨a, s, L, N, z, e, W, y, w, γ⟩
  obtain ⟨hda, haρ, hρc, hc1,
    hW, hmass, hdense, hcross, hbroad, _, _, _, _⟩ := hG
  have ha : 0 < a := hd.trans_le hda
  have hc : 0 < c := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hρ.le (le_of_not_gt hn)
    linarith
  have h4 : 4*d ≤ c := by
    have hr := mul_le_mul_of_nonneg_right hρsmall hc.le
    nlinarith
  have hWfin (i : Fin n) (j : Fin L) : μ (W i j) ≠ ⊤ :=
    ne_top_of_le_ne_top (hYfin i) (measure_mono ((hW i j).2.1.trans inter_subset_left))
  have hbox (b : ℝ) (hb : 0 ≤ b) (j : Fin L) : μ (P a b c (z j) (e j)) = O (a*b*c) :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.box_volume ha.le hb hc.le (z j) (e j)
  have hrepresent (j : Fin L) : ∃ i, (W i j).Nonempty := by
    have hvol : 0 < μ (P a (ρ*c) c (z j) (e j)) := by
      rw [hbox (ρ*c) (mul_pos hρ hc).le]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    have hpos : 0 < μ (⋃ i, W i j) := (ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hd _), hvol⟩).trans_le (hdense j)
    have hne : (⋃ i, W i j).Nonempty := Set.nonempty_iff_ne_empty.mpr (by
      intro he
      simpa [he] using hpos)
    obtain ⟨p, hp⟩ := hne
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨i, p, hi⟩
  let ref : Fin L → Fin n := fun j => (hrepresent j).choose
  have href (j : Fin L) : (W (ref j) j).Nonempty := (hrepresent j).choose_spec
  have hrefcross (j : Fin L) : Crosses d a (ρ*c) c (x (ref j)) (v (ref j)) (z j) (e j) :=
    (hcross (ref j) j (href j)).2
  let weight (j : Fin L) : ℝ := ∑ i, volume.real (W i j)
  have hmassReal : d^h * (∑ i, volume.real (Y i)) ≤ ∑ j, weight j := by
    have hf : (∑ i, ∑ j, μ (W i j)) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.sum_ne_top.mpr (fun j _ => hWfin i j))
    have hr := ENNReal.toReal_mono hf hmass
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hd.le _),
      ENNReal.toReal_sum (fun i _ => hYfin i),
      ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr (fun j _ => hWfin i j))] at hr
    simp_rw [ENNReal.toReal_sum (fun j _ => hWfin _ j)] at hr
    rw [Finset.sum_comm] at hr
    exact hr
  obtain ⟨S, N', rep, f, _, hN', hrepS, hselected, hcell, hnet⟩ :=
    aligned_grid_selection hρ hρsmall (x ∘ ref) (v ∘ ref)
      (fun j => hunit _) (fun j => hcap _) (fun j => hmid _) (fun j => halign _)
      Finset.univ weight (by
        simpa using (mul_pos (Real.rpow_pos_of_pos hd _) hYpos).trans_le hmassReal)
  let τ := reindex S
  let y' : Fin N' → V := x ∘ ref ∘ rep
  let w' : Fin N' → V := v ∘ ref ∘ rep
  have hmassSelected : d^h'*(∑ i, volume.real (Y i)) ≤ ∑ j ∈ S, weight j := by
    have hb := mul_le_mul_of_nonneg_right hretain hYpos.le
    have htot : (∑ j, weight j) ≤ alignedGridCost * ∑ j ∈ S, weight j := by
      simpa only [Finset.mem_univ, Finset.sum_const_zero, Finset.sum_attach] using hselected
    nlinarith [alignedGridCost_pos]
  have hsub (j : Fin L) : P a (ρ*c) c (z j) (e j) ⊆
      P a ((10000*ρ)*c) c (z j) (e j) := by
    intro p hp
    exact ⟨hp.1, hp.2.1.trans (by nlinarith), hp.2.2⟩
  have hcover (i : Fin n) (j : Fin L) (hj : j ∈ S) (hij : (W i j).Nonempty) :
      T d (x i) (v i) ⊆ T (10000*ρ) (y' (f j)) (w' (f j)) := by
    have h₁ := aligned_crossing_tube_cover hd hda haρ hρ (by linarith) hc1 h4
      (hunit i) (hunit (ref j)) (hcap i) (hcap (ref j)) (hmid i)
      ((halign i).trans (halign (ref j)).symm) (hcross i j hij).2 (hrefcross j)
    have h₂ := aligned_cell_tube_subset (s := 4096*ρ) hρ (hcell j hj)
    exact h₁.trans (h₂.trans (thickening_mono (by linarith) _))
  let D' : PrismData n := ⟨a, 10000*ρ, S.card, N', z ∘ τ, e ∘ τ,
    (fun i j => W i (τ j)), y', w', (fun j => f (τ j))⟩
  refine ⟨D', ?_, rfl, τ, reindex_injective S, rfl, rfl, fun _ => rfl⟩
  refine ⟨hda, ?_, ?_, hc1, ?_, ?_, ?_, ?_, ?_,
    aligned_net_distinct hρ hρsmall (fun k => hunit _) hnet, (fun k => hunit _), ?_, ?_⟩
  · nlinarith
  · nlinarith
  · intro i j
    refine ⟨(hW i (τ j)).1, fun p hp => ⟨((hW i (τ j)).2.1 hp).1,
      hsub _ ((hW i (τ j)).2.1 hp).2⟩, ?_⟩
    intro j' hjj'
    exact (hW i (τ j)).2.2 (τ j') (fun he => hjj' (reindex_injective S he))
  · have hleftfin : O (d^h')*(∑ i, μ (Y i)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i))
    have hrightfin : (∑ i, ∑ j : Fin S.card, μ (W i (τ j))) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.sum_ne_top.mpr (fun j _ => hWfin i (τ j)))
    apply (ENNReal.toReal_le_toReal hleftfin hrightfin).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hd.le _),
      ENNReal.toReal_sum (fun i _ => hYfin i),
      ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr (fun j _ => hWfin i (τ j)))]
    simp_rw [ENNReal.toReal_sum (fun j _ => hWfin _ (τ j))]
    rw [Finset.sum_comm]
    change d^h'*(∑ i, volume.real (Y i)) ≤ ∑ j, weight (reindex S j)
    rw [sum_reindex]
    exact hmassSelected
  · intro j
    apply le_trans (b := O (d^h)*μ (P a (ρ*c) c (z (τ j)) (e (τ j)))) ?_ (hdense (τ j))
    change O (d^h')*μ (P a ((10000*ρ)*c) c (z (τ j)) (e (τ j))) ≤
      O (d^h)*μ (P a (ρ*c) c (z (τ j)) (e (τ j)))
    rw [hbox ((10000*ρ)*c) (by positivity), hbox (ρ*c) (by positivity),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_le_mul_of_nonneg_right hdensity (show 0 ≤ a*(ρ*c)*c by positivity)]
  · intro i j hij
    exact ⟨hcover i (τ j) (reindex_mem S j) hij,
      aligned_crossing_widen hρ.le hc (hcross i (τ j) hij).2⟩
  · intro j
    exact aligned_broad_enlarge hd hd1 hh hρ hβ hbroadbudget (hbroad (τ j))
  · intro _
    refine ⟨rfl, fun j => ?_⟩
    exact aligned_widened_prism_carrier hd hda haρ hρ hc1 h4
      (hunit _) (hrefcross (τ j)) (hcell (τ j) (reindex_mem S j))
  · omega

/-- The stage-one conclusion without the prism-selection witnesses. -/
theorem aligned_prism_stage_one {d h h' ρ c ω ζ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : 0 ≤ h) (hβ : 0 ≤ ω*ζ/100)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/100000000)
    (hretain : alignedGridCost * d^h' ≤ d^h)
    (hdensity : 10000*d^h' ≤ d^h)
    (hbroadbudget : d^(-h)*(10000:ℝ)^(ω*ζ/100) ≤ d^(-h'))
    {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {u : V} {t : ℝ}
    (hunit : ∀ i, ‖v i‖ = 1) (hcap : ∀ i, ‖v i-u‖ ≤ 1/10)
    (hmid : ∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1)
    (halign : ∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = t)
    (hYfin : ∀ i, μ (Y i) ≠ ⊤) (hYpos : 0 < ∑ i, volume.real (Y i))
    (hG : G ω ζ d h ρ c n x v Y 0) :
    G ω ζ d h' (10000*ρ) c n x v Y 1 := by
  obtain ⟨D, hD⟩ := G_iff_data.mp hG
  obtain ⟨D', hD', _⟩ := aligned_prism_stage_one_data hd hd1 hh hβ hρ hρsmall
    hretain hdensity hbroadbudget hunit hcap hmid halign hYfin hYpos D hD
  exact G_iff_data.mpr ⟨D', hD'⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
