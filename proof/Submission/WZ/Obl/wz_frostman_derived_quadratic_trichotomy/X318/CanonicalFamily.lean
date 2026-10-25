-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.CanonicalFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Canonical
-- Copied from session x0318 (o070 branch, commit 2c4a35f, file CanonicalFamily.lean), namespace renamed.

/-!
# Pruned canonical families

Heavily overlapping canonical tubes have nearby lines, so accepted o032 bounds the number of
conflicts of each canonical tube; a greedy independent set keeps a fixed fraction of the family.
`exists_canonical_family` assembles the canonicalization with all counting transfers.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
open Set Metric MeasureTheory
open scoped ENNReal

/-- If every point of the first axis within `2δ` of `S₂` has parameter within `21/200` of
`θ₀`, the tube meets `thickening δ S₂` in volume at most `23/25 δ²`. -/
lemma overlap_volume_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) {p₁ w₁ : Space}
    (hw₁ : ‖w₁‖ = 1) (S₂ : Set Space) {θ₀ : ℝ}
    (hspread : ∀ θ ∈ Icc (0 : ℝ) 1, p₁ + θ • w₁ ∈ thickening (2 * δ) S₂ →
      |θ - θ₀| ≤ 21 / 200) :
    volume (Tube δ p₁ w₁ ∩ thickening δ S₂) ≤ ENNReal.ofReal (23 / 25 * δ ^ 2) := by
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hw₁
  let lo : Fin 3 → ℝ := ![θ₀ - 21 / 200 - δ, -δ, -δ]
  let hi : Fin 3 → ℝ := ![θ₀ + 21 / 200 + δ, δ, δ]
  have hbox : Tube δ p₁ w₁ ∩ thickening δ S₂ ⊆
      {y | ∀ i, lo i ≤ b.repr (y - p₁) i ∧ b.repr (y - p₁) i ≤ hi i} := by
    rintro y ⟨hy₁, hy₂⟩
    obtain ⟨a, ha, hya⟩ := mem_thickening_iff.mp hy₁
    rw [segment_unit_eq] at ha
    obtain ⟨θ, hθ, rfl⟩ := ha
    obtain ⟨c, hc, hyc⟩ := mem_thickening_iff.mp hy₂
    have hθS : p₁ + θ • w₁ ∈ thickening (2 * δ) S₂ := by
      refine mem_thickening_iff.mpr ⟨c, hc, ?_⟩
      calc dist (p₁ + θ • w₁) c ≤ dist (p₁ + θ • w₁) y + dist y c := dist_triangle _ _ _
        _ < δ + δ := by rw [dist_comm] at hya; exact add_lt_add hya hyc
        _ = 2 * δ := by ring
    have hθ₀ := abs_le.mp (hspread θ hθ hθS)
    have hrep : ∀ i, b.repr (y - p₁) i =
        b.repr (y - (p₁ + θ • w₁)) i + θ * (if i = 0 then 1 else 0) := by
      intro i
      have : y - p₁ = (y - (p₁ + θ • w₁)) + θ • b 0 := by rw [hb]; abel
      rw [this, map_add, map_smul, OrthonormalBasis.repr_self]
      simp
    have hcoord : ∀ i, |b.repr (y - (p₁ + θ • w₁)) i| < δ := fun i =>
      (repr_abs_le_norm b _ i).trans_lt (by rw [← dist_eq_norm]; exact hya)
    intro i
    fin_cases i
    · have h0 := abs_lt.mp (hcoord 0)
      simp only [lo, hi, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hrep 0]
      simp only [ite_true, mul_one]
      constructor <;> linarith
    · have h1 := abs_lt.mp (hcoord 1)
      simp only [lo, hi, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hrep 1]
      simp only [show (1 : Fin 3) ≠ 0 by decide, ite_false, mul_zero, add_zero]
      constructor <;> linarith
    · have h2 := abs_lt.mp (hcoord 2)
      simp only [lo, hi, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      rw [hrep 2]
      simp only [show (2 : Fin 3) ≠ 0 by decide, ite_false, mul_zero, add_zero]
      constructor <;> linarith
  calc volume (Tube δ p₁ w₁ ∩ thickening δ S₂)
      ≤ volume {y | ∀ i, lo i ≤ b.repr (y - p₁) i ∧ b.repr (y - p₁) i ≤ hi i} :=
        measure_mono hbox
    _ = ENNReal.ofReal ((21 / 100 + 2 * δ) * (2 * δ) * (2 * δ)) := by
        rw [WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
        simp only [Fin.prod_univ_three, lo, hi, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by nlinarith)]
        congr 1; ring
    _ ≤ ENNReal.ofReal (23 / 25 * δ ^ 2) := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- Heavy overlap forces two far-apart parameters of the first axis close to `S₂`. -/
lemma spread_of_heavy_overlap {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) {p₁ w₁ : Space}
    (hw₁ : ‖w₁‖ = 1) (S₂ : Set Space)
    (hov : ENNReal.ofReal (23 / 25 * δ ^ 2) < volume (Tube δ p₁ w₁ ∩ thickening δ S₂)) :
    ∃ θ ∈ Icc (0 : ℝ) 1, ∃ θ' ∈ Icc (0 : ℝ) 1, 21 / 200 < θ' - θ ∧
      p₁ + θ • w₁ ∈ thickening (2 * δ) S₂ ∧ p₁ + θ' • w₁ ∈ thickening (2 * δ) S₂ := by
  by_contra hno
  have key : ∃ θ₀ : ℝ, ∀ θ ∈ Icc (0 : ℝ) 1, p₁ + θ • w₁ ∈ thickening (2 * δ) S₂ →
      |θ - θ₀| ≤ 21 / 200 := by
    by_cases hex : ∃ θ₀ ∈ Icc (0 : ℝ) 1, p₁ + θ₀ • w₁ ∈ thickening (2 * δ) S₂
    · obtain ⟨θ₀, hθ₀, hθ₀S⟩ := hex
      refine ⟨θ₀, fun θ hθ hθS => abs_le.mpr ⟨?_, ?_⟩⟩
      · by_contra h
        exact hno ⟨θ, hθ, θ₀, hθ₀, by linarith, hθS, hθ₀S⟩
      · by_contra h
        exact hno ⟨θ₀, hθ₀, θ, hθ, by linarith, hθ₀S, hθS⟩
    · exact ⟨0, fun θ hθ hθS => absurd ⟨θ, hθ, hθS⟩ hex⟩
  obtain ⟨θ₀, hspread⟩ := key
  exact absurd (overlap_volume_le hδ hδ1 hw₁ S₂ hspread) (not_le.mpr hov)

/-- Two far-apart points of the first axis near the second segment make the second line
stay close to the first one in a bounded region. -/
lemma line_close {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) {p₁ w₁ p₂ w₂ : Space}
    (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (hS₂ : segment ℝ p₂ (p₂ + w₂) ⊆ closedBall (0 : Space) 1)
    {θ θ' : ℝ} (hθθ' : 21 / 200 < θ' - θ)
    (h₁ : p₁ + θ • w₁ ∈ thickening (2 * δ) (segment ℝ p₂ (p₂ + w₂)))
    (h₂ : p₁ + θ' • w₁ ∈ thickening (2 * δ) (segment ℝ p₂ (p₂ + w₂)))
    (ν : ℝ) (hz : ‖p₂ + ν • w₂‖ ≤ 2) :
    ∃ t : ℝ, ‖p₂ + ν • w₂ - (p₁ + t • w₁)‖ < 200 * δ := by
  obtain ⟨b, hb, hab⟩ := mem_thickening_iff.mp h₁
  obtain ⟨b', hb', hab'⟩ := mem_thickening_iff.mp h₂
  have hbn : ‖b‖ ≤ 1 := mem_closedBall_zero_iff.mp (hS₂ hb)
  rw [segment_unit_eq] at hb hb'
  obtain ⟨μ, hμ, rfl⟩ := hb
  obtain ⟨μ', hμ', rfl⟩ := hb'
  rw [dist_eq_norm] at hab hab'
  have hA : ‖(p₂ + μ • w₂) - (p₁ + θ • w₁)‖ < 2 * δ := by rw [norm_sub_rev]; exact hab
  have hB : ‖(p₂ + μ' • w₂) - (p₁ + θ' • w₁)‖ < 2 * δ := by rw [norm_sub_rev]; exact hab'
  have hdiff : (13 : ℝ) / 200 < |μ' - μ| := by
    have hn : ‖(p₂ + μ' • w₂) - (p₂ + μ • w₂)‖ = |μ' - μ| := by
      rw [show (p₂ + μ' • w₂) - (p₂ + μ • w₂) = (μ' - μ) • w₂ by module, norm_smul, hw₂,
        mul_one, Real.norm_eq_abs]
    have hna : ‖(p₁ + θ' • w₁) - (p₁ + θ • w₁)‖ = θ' - θ := by
      rw [show (p₁ + θ' • w₁) - (p₁ + θ • w₁) = (θ' - θ) • w₁ by module, norm_smul, hw₁,
        mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have htri : ‖(p₁ + θ' • w₁) - (p₁ + θ • w₁)‖ ≤ ‖(p₂ + μ' • w₂) - (p₁ + θ' • w₁)‖ +
        ‖(p₂ + μ' • w₂) - (p₂ + μ • w₂)‖ + ‖(p₂ + μ • w₂) - (p₁ + θ • w₁)‖ := by
      have e : (p₁ + θ' • w₁) - (p₁ + θ • w₁) = -((p₂ + μ' • w₂) - (p₁ + θ' • w₁)) +
          ((p₂ + μ' • w₂) - (p₂ + μ • w₂)) + ((p₂ + μ • w₂) - (p₁ + θ • w₁)) := by abel
      rw [e]
      calc _ ≤ ‖-((p₂ + μ' • w₂) - (p₁ + θ' • w₁)) + ((p₂ + μ' • w₂) - (p₂ + μ • w₂))‖ +
            ‖(p₂ + μ • w₂) - (p₁ + θ • w₁)‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact (norm_add_le _ _).trans (by rw [norm_neg])
    rw [hn, hna] at htri
    linarith
  have hμne : μ' - μ ≠ 0 := by
    intro h; rw [h, abs_zero] at hdiff; linarith
  set lam : ℝ := (ν - μ) / (μ' - μ) with hlam_def
  refine ⟨θ + lam * (θ' - θ), ?_⟩
  have hν : ν = μ + lam * (μ' - μ) := by rw [hlam_def]; field_simp; ring
  have key : p₂ + ν • w₂ - (p₁ + (θ + lam * (θ' - θ)) • w₁) =
      ((p₂ + μ • w₂) - (p₁ + θ • w₁)) +
        lam • (((p₂ + μ' • w₂) - (p₁ + θ' • w₁)) - ((p₂ + μ • w₂) - (p₁ + θ • w₁))) := by
    rw [hν]; module
  have hνμ : |ν - μ| ≤ 3 := by
    have hn : ‖(p₂ + ν • w₂) - (p₂ + μ • w₂)‖ = |ν - μ| := by
      rw [show (p₂ + ν • w₂) - (p₂ + μ • w₂) = (ν - μ) • w₂ by module, norm_smul, hw₂,
        mul_one, Real.norm_eq_abs]
    rw [← hn]
    calc _ ≤ ‖p₂ + ν • w₂‖ + ‖p₂ + μ • w₂‖ := norm_sub_le _ _
      _ ≤ 2 + 1 := add_le_add hz hbn
      _ = 3 := by norm_num
  have hlam : |lam| ≤ 47 := by
    rw [hlam_def, abs_div, div_le_iff₀ (abs_pos.mpr hμne)]
    nlinarith
  rw [key]
  calc _ ≤ ‖(p₂ + μ • w₂) - (p₁ + θ • w₁)‖ +
        ‖lam • (((p₂ + μ' • w₂) - (p₁ + θ' • w₁)) - ((p₂ + μ • w₂) - (p₁ + θ • w₁)))‖ :=
        norm_add_le _ _
    _ ≤ 2 * δ + 47 * (2 * δ + 2 * δ) := by
        rw [norm_smul, Real.norm_eq_abs]
        have h3 := norm_sub_le ((p₂ + μ' • w₂) - (p₁ + θ' • w₁)) ((p₂ + μ • w₂) - (p₁ + θ • w₁))
        have h4 : ‖((p₂ + μ' • w₂) - (p₁ + θ' • w₁)) - ((p₂ + μ • w₂) - (p₁ + θ • w₁))‖ ≤
            2 * δ + 2 * δ := by linarith
        have h5 := mul_le_mul hlam h4 (norm_nonneg _) (by norm_num)
        linarith
    _ < 200 * δ := by linarith

/-- The part of the unit ball within `r` of the line through `p` with direction `w`. -/
def lineNbhd (r : ℝ) (p w : Space) : Set Space :=
  thickening r (range fun t : ℝ => p + t • w) ∩ ball (0 : Space) 1

lemma lineNbhd_convex (r : ℝ) (p w : Space) : Convex ℝ (lineNbhd r p w) := by
  have hline : Convex ℝ (range fun t : ℝ => p + t • w) := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ a b ha hb hab
    refine ⟨a * s + b * t, ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only
    module
  exact (hline.thickening r).inter (convex_ball 0 1)

lemma lineNbhd_subset_ball (r : ℝ) (p w : Space) : lineNbhd r p w ⊆ ball (0 : Space) 1 :=
  inter_subset_right

lemma lineNbhd_volume_le {r : ℝ} (hr : 0 ≤ r) {p w : Space} (hp : ‖p‖ ≤ 1) (hw : ‖w‖ = 1) :
    volume (lineNbhd r p w) ≤ ENNReal.ofReal (16 * r ^ 2) := by
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hw
  let lo : Fin 3 → ℝ := ![-2, -r, -r]
  let hi : Fin 3 → ℝ := ![2, r, r]
  have hbox : lineNbhd r p w ⊆
      {y | ∀ i, lo i ≤ b.repr (y - p) i ∧ b.repr (y - p) i ≤ hi i} := by
    rintro y ⟨hy, hyb⟩
    obtain ⟨_, ⟨t, rfl⟩, hyt⟩ := mem_thickening_iff.mp hy
    have hrep : ∀ i, b.repr (y - p) i =
        b.repr (y - (p + t • w)) i + t * (if i = 0 then 1 else 0) := by
      intro i
      have : y - p = (y - (p + t • w)) + t • b 0 := by rw [hb]; abel
      rw [this, map_add, map_smul, OrthonormalBasis.repr_self]
      simp
    have hcoord : ∀ i, |b.repr (y - (p + t • w)) i| < r := fun i =>
      (repr_abs_le_norm b _ i).trans_lt (by rw [← dist_eq_norm]; exact hyt)
    have h0 : |b.repr (y - p) 0| ≤ 2 := by
      refine (repr_abs_le_norm b _ 0).trans ?_
      have := mem_ball_zero_iff.mp hyb
      calc ‖y - p‖ ≤ ‖y‖ + ‖p‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add this.le hp
        _ = 2 := by norm_num
    intro i
    fin_cases i
    · simp only [lo, hi, Fin.zero_eta, Matrix.cons_val_zero]
      exact abs_le.mp h0
    · have h1 := abs_lt.mp (hcoord 1)
      simp only [lo, hi, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hrep 1]
      simp only [show (1 : Fin 3) ≠ 0 by decide, ite_false, mul_zero, add_zero]
      constructor <;> linarith
    · have h2 := abs_lt.mp (hcoord 2)
      simp only [lo, hi, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      rw [hrep 2]
      simp only [show (2 : Fin 3) ≠ 0 by decide, ite_false, mul_zero, add_zero]
      constructor <;> linarith
  calc volume (lineNbhd r p w)
      ≤ volume {y | ∀ i, lo i ≤ b.repr (y - p) i ∧ b.repr (y - p) i ≤ hi i} :=
        measure_mono hbox
    _ = ENNReal.ofReal (4 * (2 * r) * (2 * r)) := by
        rw [WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
        simp only [Fin.prod_univ_three, lo, hi, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by nlinarith)]
        congr 1; ring
    _ = ENNReal.ofReal (16 * r ^ 2) := by congr 1; ring

/-- An original tube whose canonical tube overlaps a fixed canonical tube heavily lies in a thin
neighbourhood of the fixed tube's line. -/
lemma subset_lineNbhd_of_overlap {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    {p₁ w₁ p₂ w₂ : Space} (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (hS₂ : segment ℝ p₂ (p₂ + w₂) ⊆ closedBall (0 : Space) 1)
    (hov : ENNReal.ofReal (23 / 25 * δ ^ 2) < volume (Tube δ p₁ w₁ ∩ Tube δ p₂ w₂))
    {A : Set Space} (hAball : A ⊆ ball (0 : Space) 1)
    (hA : ∀ y ∈ A, ∃ ν : ℝ, ‖y - (p₂ + ν • w₂)‖ < δ) :
    A ⊆ lineNbhd (201 * δ) p₁ w₁ := by
  obtain ⟨θ, -, θ', -, hlt, h₁, h₂⟩ := spread_of_heavy_overlap hδ hδ1 hw₁ _ hov
  intro y hy
  obtain ⟨ν, hν⟩ := hA y hy
  have hy1 := mem_ball_zero_iff.mp (hAball hy)
  have hz : ‖p₂ + ν • w₂‖ ≤ 2 := by
    have := norm_sub_norm_le (p₂ + ν • w₂) y
    rw [norm_sub_rev] at this
    linarith
  obtain ⟨t, ht⟩ := line_close hδ hδ1 hw₁ hw₂ hS₂ hlt h₁ h₂ ν hz
  refine ⟨mem_thickening_iff.mpr ⟨p₁ + t • w₁, ⟨t, rfl⟩, ?_⟩, hAball hy⟩
  rw [dist_eq_norm]
  calc ‖y - (p₁ + t • w₁)‖ ≤ ‖y - (p₂ + ν • w₂)‖ + ‖p₂ + ν • w₂ - (p₁ + t • w₁)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ + 200 * δ := add_lt_add hν ht
    _ = 201 * δ := by ring

/-- Essentially distinct unit tubes inside one line neighbourhood are boundedly many. -/
theorem card_in_lineNbhd_le : ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space), (∀ i, ‖v i‖ = 1) →
      Distinct (fun i => Tube δ (x i) (v i)) →
      ∀ p w : Space, ‖p‖ ≤ 1 → ‖w‖ = 1 →
        ncard {i | Tube δ (x i) (v i) ⊆ lineNbhd (201 * δ) p w} ≤ D := by
  classical
  have h032 := WangZahlLot.wz_convex_container_tube_packing
  simp only at h032
  obtain ⟨C, hC1, hC⟩ := h032
  refine ⟨⌈C * (16 * 201 ^ 2) ^ 2⌉₊, ?_⟩
  intro δ hδ hδ1 n x v hv hdist p w hp hw
  set s : Finset (Fin n) := Finset.univ.filter
    (fun i => Tube δ (x i) (v i) ⊆ lineNbhd (201 * δ) p w) with hs
  have hncard : ncard {i | Tube δ (x i) (v i) ⊆ lineNbhd (201 * δ) p w} = s.card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext i; simp [hs]
  rw [hncard]
  let e : Fin s.card ≃ s := s.equivFin.symm
  let f : Fin s.card → Fin n := fun j => (e j : Fin n)
  have hf : Function.Injective f := fun a b h => e.injective (Subtype.ext h)
  have hmem : ∀ j, Tube δ (x (f j)) (v (f j)) ⊆ lineNbhd (201 * δ) p w := by
    intro j
    have hj : (e j : Fin n) ∈ s := (e j).2
    exact (Finset.mem_filter.mp hj).2
  have hpack := hC δ hδ hδ1 s.card (fun j => x (f j)) (fun j => v (f j))
    (lineNbhd (201 * δ) p w) (lineNbhd_convex _ _ _) (lineNbhd_subset_ball _ _ _)
    (fun j => hv (f j)) hmem (fun i j hij => hdist (f i) (f j) (hf.ne hij))
  have hvol := lineNbhd_volume_le (by positivity : (0 : ℝ) ≤ 201 * δ) hp hw
  have hsq : (volume (lineNbhd (201 * δ) p w)) ^ 2 ≤
      ENNReal.ofReal ((16 * (201 * δ) ^ 2) ^ 2) := by
    rw [ENNReal.ofReal_pow (by positivity)]
    exact pow_le_pow_left₀ zero_le hvol 2
  have hle : ENNReal.ofReal ((s.card : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal (C * (16 * 201 ^ 2) ^ 2 * δ ^ 4) := by
    calc ENNReal.ofReal ((s.card : ℝ) * δ ^ 4)
        ≤ ENNReal.ofReal C * (volume (lineNbhd (201 * δ) p w)) ^ 2 := hpack
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((16 * (201 * δ) ^ 2) ^ 2) := by gcongr
      _ = ENNReal.ofReal (C * (16 * 201 ^ 2) ^ 2 * δ ^ 4) := by
          rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; ring
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hδ4 : 0 < δ ^ 4 := by positivity
  have hcard : (s.card : ℝ) ≤ C * (16 * 201 ^ 2) ^ 2 := le_of_mul_le_mul_right hreal hδ4
  have hfin : (s.card : ℝ) ≤ (⌈C * (16 * 201 ^ 2) ^ 2⌉₊ : ℝ) := hcard.trans (Nat.le_ceil _)
  exact_mod_cast hfin

/-- A symmetric relation with degrees at most `D` has an independent subset of any finite set
containing at least a `1/(D+1)` fraction of it. -/
lemma exists_independent_subset {k D : ℕ} (r : Fin k → Fin k → Prop) [DecidableRel r]
    (hsymm : ∀ a b, r a b → r b a)
    (hdeg : ∀ a, (Finset.univ.filter (r a)).card ≤ D) :
    ∀ s : Finset (Fin k), ∃ t ⊆ s, (∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ r a b) ∧
      s.card ≤ (D + 1) * t.card := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    · set s' := s.filter (fun b => b ≠ a ∧ ¬ r a b) with hs'
      have hss' : s' ⊂ s := by
        refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
        have := h ha
        simp [hs'] at this
      obtain ⟨t', ht's', hind, hcard⟩ := ih s' hss'
      have ha' : a ∉ t' := fun h => by
        have := ht's' h
        simp [hs'] at this
      refine ⟨insert a t', ?_, ?_, ?_⟩
      · exact Finset.insert_subset ha (ht's'.trans (Finset.filter_subset _ _))
      · intro x hx y hy hxy
        rw [Finset.mem_insert] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact (Finset.mem_filter.mp (ht's' hy)).2.2
        · exact fun h => (Finset.mem_filter.mp (ht's' hx)).2.2 (hsymm _ _ h)
        · exact hind x hx y hy hxy
      · rw [Finset.card_insert_of_notMem ha']
        have hsplit : s.card ≤ s'.card + 1 + D := by
          have hsub : s ⊆ s' ∪ insert a (Finset.univ.filter (r a)) := by
            intro b hb
            by_cases hba : b = a
            · subst hba; simp
            · by_cases hrab : r a b
              · simp [hrab]
              · simp [hs', hb, hba, hrab]
          calc s.card ≤ (s' ∪ insert a (Finset.univ.filter (r a))).card :=
                Finset.card_le_card hsub
            _ ≤ s'.card + (insert a (Finset.univ.filter (r a))).card := Finset.card_union_le _ _
            _ ≤ s'.card + ((Finset.univ.filter (r a)).card + 1) := by
                gcongr; exact Finset.card_insert_le _ _
            _ ≤ s'.card + 1 + D := by linarith [hdeg a]
        nlinarith

/-- **Canonicalization of a tube family.** Every tube of an essentially distinct family of unit
`δ`-tubes in the unit ball is replaced by the unit tube on the same line that starts (left) or
ends (right) on the sphere of radius `1 - δ`, choosing the side carrying at least half of the
shading `Y i`; reversing the right ones, every canonical tube starts on that sphere. After pruning
heavily overlapping canonical tubes, at least a `1/(D+1)` fraction remains, the canonical tubes
are essentially distinct, and convex counts and slab counts transfer with fixed constants. -/
theorem exists_canonical_family : ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
      Distinct (fun i => Tube δ (x i) (v i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
      ∃ (k : ℕ) (g : Fin k → Fin n) (x' v' : Fin k → Space),
        Function.Injective g ∧ n ≤ (D + 1) * k ∧
        (∀ j, ‖v' j‖ = 1) ∧ (∀ j, ‖x' j‖ = 1 - δ) ∧
        (∀ j, Tube δ (x' j) (v' j) ⊆ ball (0 : Space) 1) ∧
        Distinct (fun j => Tube δ (x' j) (v' j)) ∧
        (∀ j, volume (Y (g j)) ≤ 2 * volume (Y (g j) ∩ Tube δ (x' j) (v' j))) ∧
        (∀ M : ℝ, (∀ W : Set Space, Convex ℝ W →
            ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
              ENNReal.ofReal M * volume W) →
          ∀ W : Set Space, Convex ℝ W →
            ENNReal.ofReal (ncard {j | Tube δ (x' j) (v' j) ⊆ W} : ℝ) ≤
              ENNReal.ofReal (48 ^ 3 * M) * volume W) ∧
        (∀ L : ℝ, 0 ≤ L → (∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
            ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆
                ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r}} : ℝ) ≤
              ENNReal.ofReal L * volume (ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r})) →
          ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
            ENNReal.ofReal (ncard {j | Tube δ (x' j) (v' j) ⊆
                ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r}} : ℝ) ≤
              ENNReal.ofReal (16000 * L) *
                volume (ball (0 : Space) 1 ∩ {y | |inner ℝ u y - t| ≤ r})) := by
  classical
  obtain ⟨D, hD⟩ := card_in_lineNbhd_le
  refine ⟨D, ?_⟩
  intro δ hδ hδ1 n x v Y hv hball hdist hYT
  have hδ1' : δ ≤ 1 := by linarith
  set R : ℝ := 1 - δ with hR
  have hR1 : R ≤ 1 := by linarith
  have hseg : ∀ i, segment ℝ (x i) (x i + v i) ⊆ closedBall (0 : Space) R :=
    fun i => segment_subset_closedBall_of_tube hδ hδ1' (hball i)
  let left : Fin n → Prop := fun i =>
    volume (Y i) ≤ 2 * volume (Y i ∩ Tube δ (leftStart R (x i) (v i)) (v i))
  let p : Fin n → Space := fun i =>
    if left i then leftStart R (x i) (v i) else rightStart R (x i) (v i) + v i
  let w : Fin n → Space := fun i => if left i then v i else -v i
  have hright : ∀ i, ¬ left i →
      Tube δ (p i) (w i) = Tube δ (rightStart R (x i) (v i)) (v i) := by
    intro i h
    simp only [p, w, h, ite_false]
    exact (canonical_tube_reverse δ _ _).symm
  have hw : ∀ i, ‖w i‖ = 1 := by
    intro i
    by_cases h : left i
    · simp only [w, h, ite_true]; exact hv i
    · simp only [w, h, ite_false, norm_neg]; exact hv i
  have hp : ∀ i, ‖p i‖ = R := by
    intro i
    by_cases h : left i
    · simp only [p, h, ite_true]; exact norm_leftStart (hv i) (hseg i)
    · simp only [p, h, ite_false]; exact norm_rightEnd (hv i) (hseg i)
  have hpseg : ∀ i, segment ℝ (p i) (p i + w i) ⊆ closedBall (0 : Space) R := by
    intro i
    by_cases h : left i
    · simp only [p, w, h, ite_true]; exact left_segment_subset (hv i) (hseg i)
    · simp only [p, w, h, ite_false]
      rw [show rightStart R (x i) (v i) + v i + -v i = rightStart R (x i) (v i) by abel,
        segment_symm]
      exact right_segment_subset (hv i) (hseg i)
  have hpball : ∀ i, Tube δ (p i) (w i) ⊆ ball (0 : Space) 1 := fun i =>
    tube_subset_ball_of_segment (hpseg i)
  have hpseg1 : ∀ i, segment ℝ (p i) (p i + w i) ⊆ closedBall (0 : Space) 1 :=
    fun i => (hpseg i).trans (closedBall_subset_closedBall hR1)
  have hshift : ∀ i, ∃ s : ℝ, |s| ≤ 1 ∧
      ∀ y ∈ Tube δ (x i) (v i), y - s • w i ∈ Tube δ (p i) (w i) := by
    intro i
    obtain ⟨hl, hr⟩ := chord_shift_bounds (hv i) hR1 (hseg i)
    by_cases h : left i
    · refine ⟨-chordLow R (x i) (v i), hl, fun y hy => ?_⟩
      simp only [p, w, h, ite_true]
      rw [eq_leftStart_add R (x i) (v i)] at hy
      exact tube_shift hy
    · refine ⟨-(1 - chordHigh R (x i) (v i)), by rwa [abs_neg], fun y hy => ?_⟩
      rw [eq_rightStart_add R (x i) (v i)] at hy
      have hy' := tube_shift hy
      rw [hright i h]
      convert hy' using 1
      simp only [w, h, ite_false]
      module
  have hhalf : ∀ i, volume (Y i) ≤ 2 * volume (Y i ∩ Tube δ (p i) (w i)) := by
    intro i
    by_cases h : left i
    · simp only [p, w, h, ite_true]; exact h
    · have hcov : Y i ⊆ (Y i ∩ Tube δ (leftStart R (x i) (v i)) (v i)) ∪
          (Y i ∩ Tube δ (rightStart R (x i) (v i)) (v i)) := by
        intro y hy
        rcases tube_cover (hv i) hR1 (hseg i) (hYT i hy) with h1 | h1
        · exact Or.inl ⟨hy, h1⟩
        · exact Or.inr ⟨hy, h1⟩
      have hsum : volume (Y i) ≤ volume (Y i ∩ Tube δ (leftStart R (x i) (v i)) (v i)) +
          volume (Y i ∩ Tube δ (rightStart R (x i) (v i)) (v i)) :=
        (measure_mono hcov).trans (measure_union_le _ _)
      rw [hright i h]
      set a := volume (Y i ∩ Tube δ (leftStart R (x i) (v i)) (v i))
      set b := volume (Y i ∩ Tube δ (rightStart R (x i) (v i)) (v i))
      have hlt : 2 * a < volume (Y i) := not_le.mp h
      have hab : a ≤ b := by
        by_contra hba
        have hba' := (not_le.mp hba).le
        have : volume (Y i) < volume (Y i) :=
          calc volume (Y i) ≤ a + b := hsum
            _ ≤ a + a := add_le_add le_rfl hba'
            _ = 2 * a := (two_mul a).symm
            _ < volume (Y i) := hlt
        exact lt_irrefl _ this
      calc volume (Y i) ≤ a + b := hsum
        _ ≤ b + b := add_le_add hab le_rfl
        _ = 2 * b := (two_mul b).symm
  let r : Fin n → Fin n → Prop := fun i i' => i ≠ i' ∧
    ¬ (volume (Tube δ (p i) (w i) ∩ Tube δ (p i') (w i')) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (p i) (w i)) ∧
      volume (Tube δ (p i') (w i') ∩ Tube δ (p i) (w i)) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (p i') (w i')))
  have hsymm : ∀ a b, r a b → r b a := by
    rintro a b ⟨hab, h⟩
    exact ⟨hab.symm, fun hh => h ⟨hh.2, hh.1⟩⟩
  have hlow : ∀ j, ENNReal.ofReal (23 / 25 * δ ^ 2) <
      (1 / 2 : ENNReal) * volume (Tube δ (p j) (w j)) := by
    intro j
    have hv0 := tube_volume_lower_box hδ (p j) (hw j)
    have hδ2 : 0 < δ ^ 2 := by positivity
    calc ENNReal.ofReal (23 / 25 * δ ^ 2) < ENNReal.ofReal (49 / 50 * δ ^ 2) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith)
      _ = (1 / 2 : ENNReal) * ENNReal.ofReal (49 / 25 * δ ^ 2) := by
          rw [show (49 / 50 * δ ^ 2 : ℝ) = (1 / 2) * (49 / 25 * δ ^ 2) by ring,
            ENNReal.ofReal_mul (by norm_num)]
          congr 1
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]
          simp
      _ ≤ (1 / 2 : ENNReal) * volume (Tube δ (p j) (w j)) := by gcongr
  have hheavy : ∀ i i', r i i' → ENNReal.ofReal (23 / 25 * δ ^ 2) <
      volume (Tube δ (p i) (w i) ∩ Tube δ (p i') (w i')) := by
    rintro i i' ⟨-, h⟩
    rw [not_and_or] at h
    rcases h with h | h
    · exact (hlow i).trans (not_le.mp h)
    · rw [inter_comm]; exact (hlow i').trans (not_le.mp h)
  have hdeg : ∀ i, (Finset.univ.filter (r i)).card ≤ D := by
    intro i
    have hsub : ∀ i', r i i' → Tube δ (x i') (v i') ⊆ lineNbhd (201 * δ) (p i) (w i) := by
      intro i' hr
      refine subset_lineNbhd_of_overlap hδ hδ1 (hw i) (hw i') (hpseg1 i')
        (hheavy i i' hr) (hball i') ?_
      intro y hy
      obtain ⟨s, -, hs⟩ := hshift i'
      obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp (hs y hy)
      rw [segment_unit_eq] at hz
      obtain ⟨θ, -, rfl⟩ := hz
      refine ⟨s + θ, ?_⟩
      rw [dist_eq_norm] at hyz
      convert hyz using 2
      module
    have hle := hD δ hδ hδ1 n x v hv hdist (p i) (w i) (by rw [hp i]; linarith) (hw i)
    calc (Finset.univ.filter (r i)).card
        ≤ (Finset.univ.filter
            (fun i' => Tube δ (x i') (v i') ⊆ lineNbhd (201 * δ) (p i) (w i))).card :=
          Finset.card_le_card (fun i' hi' => by
            rw [Finset.mem_filter] at hi' ⊢
            exact ⟨hi'.1, hsub i' hi'.2⟩)
      _ = ncard {i' | Tube δ (x i') (v i') ⊆ lineNbhd (201 * δ) (p i) (w i)} := by
          rw [← Set.ncard_coe_finset]; congr 1; ext; simp
      _ ≤ D := hle
  obtain ⟨t, -, hind, hcard⟩ := exists_independent_subset r hsymm hdeg Finset.univ
  let e : Fin t.card ≃ t := t.equivFin.symm
  let g : Fin t.card → Fin n := fun j => (e j : Fin n)
  have hg : Function.Injective g := fun a b h => e.injective (Subtype.ext h)
  refine ⟨t.card, g, fun j => p (g j), fun j => w (g j), hg, ?_, fun j => hw (g j),
    fun j => hp (g j), fun j => hpball (g j), ?_, fun j => hhalf (g j), ?_, ?_⟩
  · simpa using hcard
  · intro j j' hjj'
    have hne : g j ≠ g j' := hg.ne hjj'
    have hnr := hind (g j) (e j).2 (g j') (e j').2 hne
    have hh : volume (Tube δ (p (g j)) (w (g j)) ∩ Tube δ (p (g j')) (w (g j'))) ≤
          (1 / 2 : ENNReal) * volume (Tube δ (p (g j)) (w (g j))) ∧
        volume (Tube δ (p (g j')) (w (g j')) ∩ Tube δ (p (g j)) (w (g j))) ≤
          (1 / 2 : ENNReal) * volume (Tube δ (p (g j')) (w (g j'))) := by
      by_contra hc
      exact hnr ⟨hne, hc⟩
    exact hh.1
  · intro M hM
    refine convex_count_transfer (fun i => Tube δ (x i) (v i))
      (fun j => Tube δ (p (g j)) (w (g j))) g hg (fun j => ?_) (fun j => hpball (g j))
      (fun j => ?_) hM
    · refine ⟨p (g j), ?_⟩
      have hopen : IsOpen (Tube δ (p (g j)) (w (g j))) := isOpen_thickening
      rw [hopen.interior_eq]
      exact left_mem_tube hδ _ _
    · obtain ⟨s, hs, hmem⟩ := hshift (g j)
      refine ⟨p (g j) + w (g j), right_mem_tube hδ _ _, p (g j), left_mem_tube hδ _ _, s, hs,
        fun y hy => ?_⟩
      rw [add_sub_cancel_left]
      exact hmem y hy
  · intro L hL hcount
    exact slab_count_transfer hδ (fun i => Tube δ (x i) (v i)) (fun j => p (g j))
      (fun j => w (g j)) g hg (fun j => hw (g j)) (fun j => hpseg1 (g j)) hball
      (fun j => hshift (g j)) hL hcount


/-- **Canonical derived family.** From an admissible family (unit directions, tubes in the unit
ball, essentially distinct, measurable shadings inside the tubes of individual density `d`) that
is Frostman with constant `M`, canonicalization gives a derived family of `k ≥ n/(D+1)` tubes
starting on the sphere of radius `1 - δ` whose shadings `Z j = Y (g j) ∩ T'_j` keep individual
density `d/2`, lie in the old union, and which is Frostman with constant `48³ (D+1) M`. -/
theorem canonical_derived_family : ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (d M : ℝ),
      0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
      Distinct (fun i => Tube δ (x i) (v i)) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ Tube δ (x i) (v i)) → (∀ i, ENNReal.ofReal d ≤ volume (Y i)) → 0 ≤ M →
      (∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
          ENNReal.ofReal (M * n) * volume W) →
      ∃ (k : ℕ) (y u : Fin k → Space) (Z : Fin k → Set Space),
        0 < k ∧ (n : ℝ) ≤ (D + 1) * k ∧
        (∀ j, ‖u j‖ = 1) ∧ (∀ j, ‖y j‖ = 1 - δ) ∧
        (∀ j, Tube δ (y j) (u j) ⊆ Metric.ball 0 1) ∧
        Distinct (fun j => Tube δ (y j) (u j)) ∧
        (∀ j, MeasurableSet (Z j)) ∧ (∀ j, Z j ⊆ Tube δ (y j) (u j)) ∧
        (∀ j, ENNReal.ofReal (d / 2) ≤ volume (Z j)) ∧
        (⋃ j, Z j) ⊆ (⋃ i, Y i) ∧
        (∀ W : Set Space, Convex ℝ W →
          ENNReal.ofReal (ncard {j | Tube δ (y j) (u j) ⊆ W} : ℝ) ≤
            ENNReal.ofReal (48 ^ 3 * ((D + 1) * M) * k) * volume W) := by
  obtain ⟨D, hD⟩ := exists_canonical_family
  refine ⟨D, ?_⟩
  intro δ hδ hδ1 n x v Y d M hn hv hball hsep hYm hYT hdens hM hF
  obtain ⟨k, g, y, u, hg, hk, hu, hy, hyball, hysep, hhalf, hconv, -⟩ :=
    hD δ hδ hδ1 n x v Y hv hball hsep hYT
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; omega
    · exact h
  have hkR : (n : ℝ) ≤ (D + 1) * k := by exact_mod_cast hk
  refine ⟨k, y, u, fun j => Y (g j) ∩ Tube δ (y j) (u j), hkpos, hkR, hu, hy, hyball, hysep,
    fun j => (hYm (g j)).inter Metric.isOpen_thickening.measurableSet,
    fun j => inter_subset_right, ?_, ?_, ?_⟩
  · intro j
    have h1 := hhalf j
    have h2 := hdens (g j)
    calc ENNReal.ofReal (d / 2) ≤ volume (Y (g j)) / 2 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
          exact ENNReal.div_le_div_right h2 2
      _ ≤ volume (Y (g j) ∩ Tube δ (y j) (u j)) := by
          rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
          rw [mul_comm]; exact h1
  · intro p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨g j, hj.1⟩
  · intro W hW
    have := hconv (M * n) hF W hW
    refine this.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
    have hM0 : 0 ≤ 48 ^ 3 * M := by positivity
    calc 48 ^ 3 * (M * n) = (48 ^ 3 * M) * n := by ring
      _ ≤ (48 ^ 3 * M) * ((D + 1) * k) := mul_le_mul_of_nonneg_left hkR hM0
      _ = 48 ^ 3 * ((D + 1) * M) * k := by ring

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
