-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.SourcePreparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.PreparedMesh
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.ColorBudget

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts)
open WangZahlLot.Obl.wz_tower_balanced_refinement (enumerate enumerate_mem enumerate_injective)

/-- Prepare a balanced buffered source tower from any nonempty subfamily. Its
height is chosen before the prescribed loss exponent. -/
theorem prepare_source_tower {a : ℝ} (ha : 0 < a) :
    ∃ B : ℕ, 0 < B ∧ ∀ u : ℝ, 0 < u →
      ∃ η : ℝ, 0 < η ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ (n : ℕ) (x v : Fin n → Space),
        (∀ i, ‖v i‖ = 1 ∧ Tube δ (x i) (v i) ⊆ ball 0 1) →
        (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
          (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
        CoverSupply δ η n x v → ∀ G : Finset (Fin n), G.Nonempty →
        ∃ (m : ℕ) (c : Fin m → Fin n) (D : Space ≃ᵃⁱ[ℝ] Space),
          (∀ i, c i ∈ G) ∧ δ ^ u * (G.card : ℝ) ≤ (m : ℝ) ∧
          SourceTower Tube δ a u B m (fun i => D (x (c i))) (fun i => D.linear (v (c i))) := by
  classical
  obtain ⟨J, hJ, t, ht, htJ, hta⟩ := choose_mesh_depth ha
  let B := J + 2
  refine ⟨B, by dsimp [B]; omega, ?_⟩
  intro u hu
  obtain ⟨dMesh, hdMesh, hmesh⟩ := mesh_cutoff ht hta
  obtain ⟨dCount, hdCount, hcountcut⟩ := source_count_cutoff hu
  obtain ⟨dColor, hdColor, hcolors⟩ := regularization_color_budget (show 0 < u / 2 by positivity) B
  obtain ⟨K, hK, hcell⟩ := dense_parameter_cell (show (0 : ℝ) < 1 / 12800 by norm_num)
  obtain ⟨dK, hdK, hKsmall⟩ := constant_power_cutoff (show (0 : ℝ) < K by exact_mod_cast hK)
    (show 0 < u / 2 by positivity)
  let η := min (t / 2) (min 1 (u / 10))
  have hη : 0 < η := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hηt : η ≤ t / 2 := min_le_left _ _
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηu : 10 * η ≤ u := by
    have hh : η ≤ u / 10 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  let d := min (1 / 6400) (min dMesh (min dCount (min dColor dK)))
  have hd : 0 < d := lt_min (by norm_num) (lt_min hdMesh (lt_min hdCount (lt_min hdColor hdK)))
  refine ⟨η, hη, d, hd, ?_⟩
  intro δ hδ hδd n x v htubes hsep hsupply G hG
  have hδlocal : δ ≤ 1 / 6400 := hδd.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδd' := hδd.trans (min_le_right _ _)
  have hδMesh : δ ≤ dMesh := hδd'.trans (min_le_left _ _)
  have hδCount : δ ≤ dCount := (hδd'.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδColor : δ ≤ dColor :=
    ((hδd'.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδK : δ ≤ dK :=
    ((hδd'.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hv (i) := (htubes i).1
  have hx (i) : ‖x i‖ ≤ 1 := by
    have hh := (htubes i).2 (self_subset_thickening hδ _ (left_mem_segment ℝ (x i) (x i + v i)))
    exact (show ‖x i‖ < 1 by simpa only [mem_ball, dist_zero_right] using hh).le
  obtain ⟨S, hSG, hS, hGS, hparam⟩ := hcell n x v (fun i => ⟨hx i, (hv i).le⟩) G hG
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  obtain ⟨D, y₀, w₀, hw₀, hrootball, hroot⟩ := translated_cell_in_root hS hparam hv
    (show δ + 2 * (1 / 12800 : ℝ) ≤ 1 / 3200 by linarith)
  let e₀ : Fin S.card → Fin n := enumerate S
  let xd : Fin S.card → Space := fun i => D (x (e₀ i))
  let vd : Fin S.card → Space := fun i => D.linear (v (e₀ i))
  have hvd (i) : ‖vd i‖ = 1 := rigid_unit D (hv (e₀ i))
  have hroot' (i) : Tube δ (xd i) (vd i) ⊆ Tube (1 / 3200 : ℝ) y₀ w₀ :=
    hroot (e₀ i) (enumerate_mem S i)
  have hrootball' : Tube (1 / 100 : ℝ) y₀ w₀ ⊆ ball 0 (3 / 4 : ℝ) :=
    (tube_ball_enlargement (show (0 : ℝ) < 1 / 3200 by norm_num) hrootball).trans
      (ball_subset_ball (by norm_num))
  obtain ⟨hcountbudget, hcountdata⟩ := hcountcut δ η hδ hδCount hη hη1 hηu
  obtain ⟨hglobal, hn⟩ := hcountdata n x v hv (fun i => (htubes i).2) hsep hsupply
  have hScard : (S.card : ℝ) ≤ δ ^ (-7 : ℝ) := by
    apply le_trans _ hn
    exact_mod_cast (show S.card ≤ n by simpa only [Fintype.card_fin] using Finset.card_le_univ S)
  have hfine : Counts δ (δ ^ (-u)) S.card xd vd :=
    counts_rigid D (counts_injective x v e₀ (enumerate_injective S) hglobal)
  have hsupplyd : CoverSupply δ η S.card xd vd := cover_supply_rigid_subfamily D e₀ hsupply
  let b : ℝ := δ ^ t
  have hb : 0 < b := Real.rpow_pos_of_pos hδ _
  have hb1 : b ≤ 1 := Real.rpow_le_one hδ.le hδ1 ht.le
  have hbJ : b ^ J = δ := by
    dsimp only [b]
    rw [← Real.rpow_mul_natCast hδ.le, htJ, Real.rpow_one]
  obtain ⟨hsmall, hgap, htop⟩ := hmesh δ η hδ hδ1 hδMesh hη hηt
  obtain ⟨s, H, hs0, hsJ, hn0, ⟨e, he⟩, hs, hball⟩ := prepared_assigned_mesh
    hδ hδ1 hu hη hJ hSpos hb hb1 hbJ hsmall hcountbudget xd vd hvd hsupplyd hfine
    y₀ w₀ hw₀ hroot' hrootball'
  have hq : 1 ≤ δ ^ (-η) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -η ≤ 0 by linarith)
  obtain ⟨hr0, hrJ, hscale, _, hedge⟩ := buffered_mesh hδ hJ hb hb1 hbJ hq hsmall hgap s hs0 hsJ hs
  obtain ⟨Q, hQ, hQbound, color, hcolor⟩ := hcolors δ S.card hδ hδ1 hδColor hSpos hScard
  obtain ⟨m, c, hc, hmass, hsource⟩ := regularize_assigned_covers hδ hJ (le_refl B) hQ
    xd vd hSpos hvd s (fun j => if j < J then 32 * s j else δ) H e he hn0 hr0 hrJ htop hScard
    hscale hball hedge color hcolor
  refine ⟨m, e₀ ∘ c, D, (fun i => hSG (enumerate_mem S (c i))), ?_, ?_⟩
  · have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hQsmall : (Q : ℝ) ^ (J + 1) ≤ δ ^ (-(u / 2)) :=
      (pow_le_pow_right₀ hQ1 (show J + 1 ≤ B by dsimp [B]; omega)).trans hQbound
    have hcoef : (K : ℝ) * (Q : ℝ) ^ (J + 1) ≤ δ ^ (-u) := by
      calc
        (K : ℝ) * (Q : ℝ) ^ (J + 1) ≤ δ ^ (-(u / 2)) * δ ^ (-(u / 2)) :=
          mul_le_mul (hKsmall δ hδ hδK) hQsmall (by positivity) (Real.rpow_nonneg hδ.le _)
        _ = δ ^ (-u) := by rw [← Real.rpow_add hδ]; congr 1; ring
    have hmass' : (G.card : ℝ) ≤ ((K : ℝ) * (Q : ℝ) ^ (J + 1)) * m := by
      have hGS' : (G.card : ℝ) ≤ (K : ℝ) * S.card := by exact_mod_cast hGS
      have hh : (S.card : ℝ) ≤ (Q : ℝ) ^ (J + 1) * m := by exact_mod_cast hmass
      calc
        (G.card : ℝ) ≤ (K : ℝ) * S.card := hGS'
        _ ≤ (K : ℝ) * ((Q : ℝ) ^ (J + 1) * m) :=
          mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
        _ = _ := by ring
    have hi : δ ^ u * δ ^ (-u) = 1 := by rw [← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero]
    calc
      δ ^ u * (G.card : ℝ) ≤ δ ^ u * ((δ ^ (-u)) * m) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
        exact hmass'.trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))
      _ = m := by rw [← mul_assoc, hi, one_mul]
  · exact hsource

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
