/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 11e20d7dc2731eb500dab3f1bb8f7513adc19fde, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeMenuCount.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMenuStatement

/-!
# Whole original domains: the menu count

`native_original_menu_counting : NativeOriginalMenuCounting`. For one old sheet `h` and one
native time block, every paired native `i` names a successful mark `r` whose full original
witness `W_r` (fitted native domain × time block × the old group's static/velocity cell) has
original mass `≥ δ q D² a^d π(G₀)`. By the true affine fit (`affinePredictor_fit`) and the
whole-product comparison, almost every point of `W_r` lies in the `2M` graph band of the old
sheet over that cell and block (`original_old_band`, the original-law version of
`observed_integrated_band`: mass `≤ 25200 K (2M)^d π(G₀) q D²`). The native domains of one block
are disjoint, so the menu has at most `50400 K (M/a)^d / δ` entries.
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

attribute [local instance] sum_measurableSingletonClass

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- The old sheet is bounded on its whole static box. -/
theorem old_box_bound (h : Fin c.m) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc ((c.group h 1 : ℝ) * c.D) ((c.group h 1 : ℝ) * c.D + c.D),
      ∀ v ∈ Icc ((c.group h 2 : ℝ) * c.D) ((c.group h 2 : ℝ) * c.D + c.D),
        |predictor (c.hH h) t u v| ≤ cfg.N k ^ c.ε := by
  intro t ht u hu v hv
  exact (c.layer.2.2.1 h).2.1 t ht u ⟨hu.1, by linarith [hu.2]⟩ v ⟨hv.1, by linarith [hv.2]⟩

theorem block_mem {t : ℝ} {block : Fin (2 ^ cfg.T k s)}
    (ht : t ∈ Data.I (cfg.T k s) block) :
    t ∈ Icc (0 : ℝ) 1 ∧ t ∈ Icc (((block : ℕ) : ℝ) * cfg.timeLength k s)
      ((((block : ℕ) : ℝ) + 1) * cfg.timeLength k s) := by
  have hb : t ∈ Icc (((block : ℕ) : ℝ) * cfg.timeLength k s)
      ((((block : ℕ) : ℝ) + 1) * cfg.timeLength k s) := by
    simpa only [Data.I, Data.timeLength, div_eq_mul_inv] using ht
  refine ⟨⟨?_, ?_⟩, hb⟩
  · have : (0 : ℝ) ≤ ((block : ℕ) : ℝ) * cfg.timeLength k s := by
      unfold Data.timeLength; positivity
    linarith [hb.1]
  · have hlt : ((block : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ cfg.T k s := by
      have := block.isLt
      exact_mod_cast this
    have hq : (((block : ℕ) : ℝ) + 1) * cfg.timeLength k s ≤ 1 := by
      unfold Data.timeLength
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      exact hlt
    linarith [hb.2]

/-- **The original law of the old sheet's graph band** over its static/velocity cell and one
native time block. -/
theorem original_old_band (h : Fin c.m) (block : Fin (2 ^ cfg.T k s))
    (r : Fin c.support.table.count) (hr : c.support.table.old r = h)
    (hrb : cfg.j k s (c.support.table.native r) = block)
    {w : ℝ} (hw : cfg.N k ^ (-c.R) ≤ w) (hw1 : w ≤ 1)
    (hround : 2 * (4 * (cfg.N k ^ c.ε + c.M * (1 + 6 * cfg.K k))) * cfg.N k ^ (-c.re) +
      (6 * (4 * (cfg.N k ^ c.ε + c.M * (1 + 6 * cfg.K k))) / c.D) *
        (cfg.N k ^ (-cfg.e₀) + (3 * cfg.K k + 1) * cfg.N k ^ (-c.re)) ≤ w) :
    cfg.μ k {p | p.2 ∈ Data.I (cfg.T k s) block ∧
      ⌊cfg.b k p.1 3 / cfg.N k ^ (-cfg.e₀)⌋ = c.group h 0 ∧
      ⌊cfg.b k p.1 0 / c.D⌋ = c.group h 1 ∧ ⌊cfg.b k p.1 1 / c.D⌋ = c.group h 2 ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) ∧
      |cfg.b k p.1 0| ≤ 3 * cfg.K k ∧
      |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
        predictor (c.hH h) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ w} ≤
      ENNReal.ofReal (25200 * cfg.K k * w ^ cfg.d *
        binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (c.group h 0) *
          cfg.timeLength k s * c.D ^ 2) := by
  letI := c.finite_palette
  set χ := cfg.N k ^ (-cfg.e₀) with hχdef
  set g := c.group h with hgdef
  set f := c.hH h with hfdef
  set B := cfg.N k ^ c.ε + c.M * (1 + 6 * cfg.K k) with hBdef
  have hN := c.N_pos
  have hK := c.K_one
  have hD := c.D_pos
  have hD1 := c.D_one
  have hM := c.M_nonneg
  have hpow : 0 ≤ cfg.N k ^ c.ε := Real.rpow_nonneg hN.le _
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hNB : cfg.N k ^ c.ε ≤ B := by rw [hBdef]; nlinarith
  have hwp : 0 < w := (Real.rpow_pos_of_pos hN _).trans_le hw
  set C := cfg.K k * w ^ cfg.d * binWeight (cfg.π k) χ (g 0) with hCdef
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hwp.le _))
    (binWeight_nonneg _ _ _)
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hδ : 0 < cfg.N k ^ (-c.re) := Real.rpow_pos_of_pos hN _
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  have hχD : χ ≤ c.D := c.velocity_width
  have hδD' : cfg.N k ^ (-c.re) ≤ c.D := by
    have hh := c.mesh_parameter
    have : cfg.N k ^ (-c.re) ≤ 3 * cfg.K k * cfg.N k ^ (-c.re) := by nlinarith
    linarith
  set condition : α × ℝ → Prop := fun p => p.2 ∈ Data.I (cfg.T k s) block ∧
    ⌊cfg.b k p.1 3 / χ⌋ = g 0 ∧ ⌊cfg.b k p.1 0 / c.D⌋ = g 1 ∧ ⌊cfg.b k p.1 1 / c.D⌋ = g 2 ∧
    |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ ∧ |cfg.b k p.1 0| ≤ 3 * cfg.K k with hcondition
  have hbox := c.old_box_bound h
  have hcellmem : ∀ p, condition p →
      cfg.b k p.1 0 ∈ Icc ((g 1 : ℝ) * c.D) ((g 1 : ℝ) * c.D + c.D) ∧
      cfg.b k p.1 1 ∈ Icc ((g 2 : ℝ) * c.D) ((g 2 : ℝ) * c.D + c.D) := by
    intro p hp
    obtain ⟨-, -, h1, h2, -, -⟩ := hp
    have e1 := Int.floor_eq_iff.mp h1
    have e2 := Int.floor_eq_iff.mp h2
    rw [le_div_iff₀ hD, div_lt_iff₀ hD] at e1 e2
    exact ⟨⟨e1.1, by nlinarith only [e1.2]⟩, ⟨e2.1, by nlinarith only [e2.2]⟩⟩
  have hcond : ∀ p, condition p → p.2 ∈ Icc (0 : ℝ) 1 ∧
      |cfg.b k p.1 3 - χ * (g 0 : ℝ)| ≤ χ ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ ∧ |cfg.b k p.1 0| ≤ 3 * cfg.K k ∧
      |predictorTimeSlope f (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ 2 * (4 * B) := by
    intro p hp
    have hm := hcellmem p hp
    obtain ⟨ht, hv, -, -, hc, hb0⟩ := hp
    refine ⟨(NativeComparisonData.block_mem (cfg := cfg) ht).1, ?_, hc, hb0, ?_⟩
    · simpa only [floorPoint, hv] using floorPoint_error hχ (cfg.b k p.1 3)
    · have hs := predictor_timeSlope_bound (fun t ht => hbox t ht _ hm.1 _ hm.2)
      exact hs.trans (by nlinarith only [hNB, hB])
  have hgrad : ∀ τ ∈ Icc (0 : ℝ) 1,
      |f 2 + f 3 * τ| ≤ 2 * (4 * B) / c.D ∧ |f 4 + f 5 * τ| ≤ 2 * (4 * B) / c.D := by
    intro τ hτ
    have hg := predictor_gradients_extended hD
      (show τ ∈ Icc (-1 : ℝ) 2 from ⟨by linarith [hτ.1], by linarith [hτ.2]⟩) hbox
    have e : 2 * (4 * B) / c.D = 8 * B / c.D := by ring
    rw [e]
    exact ⟨hg.1.trans (div_le_div_of_nonneg_right (by linarith only [hNB]) hD.le),
      hg.2.trans (div_le_div_of_nonneg_right (by linarith only [hNB]) hD.le)⟩
  have href := cfg.observed_reference_bounds c.layer c.support.table hK hD hD1 hχ
    (hχD.trans hD1) rfl c.support.coefficients
    (c.support.table.source c.group (cfg.j k s) r)
  have hcol : c.support.table.colour c.group (cfg.j k s)
      (c.support.table.source c.group (cfg.j k s) r) = (g, block) := by
    change (c.group (c.support.table.old r), cfg.j k s (c.support.table.native r)) = (g, block)
    rw [hr, hrb]
  rw [hcol] at href
  have hcell (q : Fin 3 → ℤ) (j : ℤ) :
      cfg.μ k {p | baseMesh (cfg.N k ^ (-c.re)) (physicalBase (cfg.b k p.1) p.2) = q ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / w⌋ = j ∧ condition p} ≤
          ENNReal.ofReal (C * (cfg.N k ^ (-c.re)) ^ 3) := by
    have hh := joint_cell_cap_in_palette (cfg.μ k) (cfg.μ k) le_rfl (cfg.π k) (cfg.b k)
      hN (by linarith) c.caps c.re_lower c.re_upper c.velocity_lower c.velocity_upper hw hw1
      condition (g 0) (fun p hp => hp.2.1) q j
    exact hh.trans_eq (ENNReal.ofReal_mul hC).symm
  have hb := integrated_parameter_graph_cap (cfg.μ k) (cfg.b k) f condition hδ hwp c.mesh_time
    (by linarith : 0 ≤ 3 * cfg.K k) hC (by positivity : 0 ≤ 4 * B) hD
    (((block : ℕ) : ℝ) * cfg.timeLength k s) (c.D * (g 1 : ℝ)) (c.D * (g 2 : ℝ))
    (χ * (g 0 : ℝ)) c.D 0 href.1 href.1 href.2.1
    ⟨by linarith, by linarith⟩
    ⟨by have := c.mesh_parameter; linarith, by have := c.mesh_parameter; linarith⟩
    hcond hgrad hround hcell
  apply le_trans (measure_mono ?_) (hb.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro p hp
    obtain ⟨ht, hv, h1, h2, hc, hb0, hband⟩ := hp
    have hcp : condition p := ⟨ht, hv, h1, h2, hc, hb0⟩
    have hm := hcellmem p hcp
    have hblock := (NativeComparisonData.block_mem (cfg := cfg) ht).2
    refine ⟨?_, ?_, ?_, ?_, hcp⟩
    · rw [abs_of_nonneg (by linarith only [hblock.1])]
      nlinarith only [hblock.2]
    · rw [abs_le]; constructor <;> nlinarith only [hm.1.1, hm.1.2]
    · rw [abs_le]; constructor <;> nlinarith only [hm.2.1, hm.2.2]
    · simpa only [add_zero] using hband
  · have hm : (c.D + χ) * (2 * c.D + χ) ≤ 6 * c.D ^ 2 := by
      exact (mul_le_mul (by linarith : c.D + χ ≤ 2 * c.D)
        (by linarith : 2 * c.D + χ ≤ 3 * c.D) (by positivity) (by positivity)).trans_eq
        (by ring)
    calc 4200 * C * cfg.timeLength k s * (c.D + χ) * (2 * c.D + χ)
        = 4200 * C * cfg.timeLength k s * ((c.D + χ) * (2 * c.D + χ)) := by ring
      _ ≤ 4200 * C * cfg.timeLength k s * (6 * c.D ^ 2) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by rw [hCdef]; ring

/-- Original coefficient bounds hold for almost every original incidence. -/
theorem original_coefficient_ae (hbasic : cfg.Basic) :
    ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 0| ≤ cfg.K k := by
  obtain ⟨-, -, -, hdom, -, -, -, -, hν, -⟩ := hbasic k
  have hbad : (cfg.ν k) {l | ¬ (|cfg.b k l 0| + |cfg.b k l 1| + |cfg.b k l 3| +
      |cfg.b k l 4| ≤ cfg.K k)} = 0 := ae_iff.mp hν
  rw [ae_iff]
  apply le_antisymm _ bot_le
  calc cfg.μ k {p | ¬ |cfg.b k p.1 0| ≤ cfg.K k}
      ≤ cfg.μ k ({l | ¬ (|cfg.b k l 0| + |cfg.b k l 1| + |cfg.b k l 3| +
          |cfg.b k l 4| ≤ cfg.K k)} ×ˢ univ) := by
        apply measure_mono
        intro p hp
        refine ⟨fun hsum => hp ?_, trivial⟩
        have h1 := abs_nonneg (cfg.b k p.1 1)
        have h3 := abs_nonneg (cfg.b k p.1 3)
        have h4 := abs_nonneg (cfg.b k p.1 4)
        linarith
    _ ≤ (ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
        ({l | ¬ (|cfg.b k l 0| + |cfg.b k l 1| + |cfg.b k l 3| +
          |cfg.b k l 4| ≤ cfg.K k)} ×ˢ univ) := hdom _
    _ = 0 := by rw [Measure.smul_apply, Measure.prod_prod, hbad, zero_mul, smul_zero]

end NativeComparisonData

/-- **The whole-original-domain menu count.** -/
theorem native_original_menu_counting : NativeOriginalMenuCounting := by
  intro α _ cfg k s σ c hbasic lev hμ ha hd0 hd1 M δ hAM h2M hδ hprod h block
  classical
  set χ := cfg.N k ^ (-cfg.e₀) with hχdef
  set g := c.group h with hgdef
  set S : Set (Fin (cfg.n k s)) := {i | c.paired M δ h i ∧ cfg.j k s i = block} with hSdef
  have hN := c.N_pos
  have hK := c.K_one
  have hD := c.D_pos
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  have ha0 : 0 < c.a := by rw [ha]; exact Real.rpow_pos_of_pos hN _
  have hA0 : 0 < c.A := (Real.rpow_pos_of_pos hN _).trans_le c.width_lower
  have hM0 : 0 < M := hA0.trans_le hAM
  have hrhs : 0 ≤ (100800 * cfg.K k * (M / c.a) ^ cfg.d) / δ := by
    have : 0 ≤ (M / c.a) ^ cfg.d := Real.rpow_nonneg (div_nonneg hM0.le ha0.le) _
    have : 0 ≤ 100800 * cfg.K k := by linarith
    positivity
  rcases S.eq_empty_or_nonempty with hSe | ⟨i₀, hi₀⟩
  · change ((S.ncard : ℕ) : ℝ) ≤ _
    rw [hSe, Set.ncard_empty, Nat.cast_zero]; exact hrhs
  -- the marks of the menu
  have hmk : ∀ i ∈ S, ∃ r : Fin c.support.table.count, c.support.table.old r = h ∧
      c.support.table.native r = i ∧ r ∉ c.badMarks M ∧
      0 < binWeight (cfg.π k) χ ((c.witnessOfMark r).val.2 0) ∧
      ENNReal.ofReal (δ * c.witnessWeight (c.witnessOfMark r)) ≤
        cfg.μ k (c.originalWitness (c.witnessOfMark r)) := fun i hi => hi.1
  haveI : Nonempty (Fin c.support.table.count) := ⟨(hmk i₀ hi₀).choose⟩
  choose! rk hrold hrnat hrgood hrpal hrfloor using hmk
  have hval : ∀ i ∈ S, (c.witnessOfMark (rk i)).val = (i, g) := by
    intro i hi
    change (c.support.table.native (rk i), c.group (c.support.table.old (rk i))) = (i, g)
    rw [hrnat i hi, hrold i hi]
  set ω := cfg.timeLength k s * c.D ^ 2 * c.a ^ cfg.d * binWeight (cfg.π k) χ (g 0) with hω
  have hweight : ∀ i ∈ S, c.witnessWeight (c.witnessOfMark (rk i)) = ω := by
    intro i hi
    simp only [NativeComparisonData.witnessWeight, hval i hi]
    exact hω.symm
  have hω0 : 0 < ω := by
    have hp := hrpal i₀ hi₀
    simp only [hval i₀ hi₀] at hp
    have : 0 < c.a ^ cfg.d := Real.rpow_pos_of_pos ha0 _
    rw [hω]; positivity
  set W : Fin (cfg.n k s) → Set (α × ℝ) := fun i => c.originalWitness (c.witnessOfMark (rk i))
    with hWdef
  have hWm : ∀ i, MeasurableSet (W i) := fun i => c.measurable_originalWitness lev _
  have hWfloor : ∀ i ∈ S, ENNReal.ofReal (δ * ω) ≤ cfg.μ k (W i) := by
    intro i hi
    rw [← hweight i hi]; exact hrfloor i hi
  have hWmem : ∀ i ∈ S, ∀ p ∈ W i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) block ∧
      ⌊cfg.b k p.1 3 / χ⌋ = g 0 ∧ ⌊cfg.b k p.1 0 / c.D⌋ = g 1 ∧
      ⌊cfg.b k p.1 1 / c.D⌋ = g 2 := by
    intro i hi p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hp
    simp only [hval i hi] at h1 h2 h3 h4 h5
    rw [hi.2] at h2
    exact ⟨h1, h2, h3, h4, h5⟩
  have hdisj : ((S.toFinset : Finset (Fin (cfg.n k s))) : Set (Fin (cfg.n k s))).PairwiseDisjoint W := by
    intro i hi i' hi' hne
    rw [Finset.mem_coe, Set.mem_toFinset] at hi hi'
    refine Set.disjoint_left.mpr fun p hp hp' => ?_
    have h1 := (hWmem i hi p hp).1
    have h2 := (hWmem i' hi' p hp').1
    have hd := lev.disjoint i i' hne (hi.2.trans hi'.2.symm)
    exact Set.disjoint_left.mp hd (lev.fitted_subset i h1) (lev.fitted_subset i' h2)
  -- almost every witness point lies in the old sheet's `2M` band
  set Band : Set (α × ℝ) := {p | p.2 ∈ Data.I (cfg.T k s) block ∧
      ⌊cfg.b k p.1 3 / cfg.N k ^ (-cfg.e₀)⌋ = c.group h 0 ∧
      ⌊cfg.b k p.1 0 / c.D⌋ = c.group h 1 ∧ ⌊cfg.b k p.1 1 / c.D⌋ = c.group h 2 ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) ∧
      |cfg.b k p.1 0| ≤ 3 * cfg.K k ∧
      |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
        predictor (c.hH h) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ 2 * M} with hBand
  have hsubBand : (⋃ i ∈ S.toFinset, W i) ≤ᵐ[cfg.μ k] Band := by
    filter_upwards [lev.horizontal_equation i₀,
      NativeComparisonData.original_coefficient_ae (k := k) hbasic] with p hc hb hp
    obtain ⟨i, hi, hpW⟩ := mem_iUnion₂.mp hp
    rw [Set.mem_toFinset] at hi
    obtain ⟨hB, ht, h3, h4, h5⟩ := hWmem i hi p hpW
    refine ⟨ht, h3, h4, h5, hc, by linarith, ?_⟩
    have ht' : p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) := by rw [hi.2]; exact ht
    have ht01 := (NativeComparisonData.block_mem (cfg := cfg) ht).1
    have hvel : |cfg.b k p.1 3 - χ * (g 0 : ℝ)| ≤ χ := by
      simpa only [floorPoint, h3] using floorPoint_error hχ (cfg.b k p.1 3)
    have hfit := affinePredictor_fit (c.L i) (cfg.b k p.1) (v := χ * (g 0 : ℝ)) ht01 hvel hc
      (c.slopes i 1) (c.slopes i 2) (c.true_fit i p.1 hB p.2 ht')
    have hcellb : ∀ (e : ℤ) (u : ℝ), ⌊u / c.D⌋ = e →
        u ∈ Icc ((e : ℝ) * c.D) (((e : ℝ) + 1) * c.D) := by
      intro e u hu
      have hh := Int.floor_eq_iff.mp hu
      rw [le_div_iff₀ hD, div_lt_iff₀ hD] at hh
      exact ⟨hh.1, hh.2.le⟩
    have hcmp := hprod (rk i) (hrgood i hi) p.2 (by rw [hrnat i hi]; exact ht')
      (cfg.b k p.1 0) (by rw [hrold i hi]; exact hcellb _ _ h4)
      (cfg.b k p.1 1) (by rw [hrold i hi]; exact hcellb _ _ h5)
    have hphys : c.physical (c.support.table.witness c.group (cfg.j k s) (rk i)) =
        affinePredictor (c.L i) (χ * (g 0 : ℝ)) := by
      change affinePredictor (c.L (c.support.table.native (rk i)))
        (c.frame (c.group (c.support.table.old (rk i)),
          cfg.j k s (c.support.table.native (rk i)))).velocity = _
      rw [hrnat i hi, hrold i hi]
      rfl
    rw [hphys, hrold i hi] at hcmp
    have hwf := c.witness_fit
    calc |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
          predictor (c.hH h) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)|
        ≤ |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
            predictor (affinePredictor (c.L i) (χ * (g 0 : ℝ))) p.2 (cfg.b k p.1 0)
              (cfg.b k p.1 1)| +
          |predictor (affinePredictor (c.L i) (χ * (g 0 : ℝ))) p.2 (cfg.b k p.1 0)
              (cfg.b k p.1 1) - predictor (c.hH h) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| :=
          abs_sub_le _ _ _
      _ ≤ (cfg.K k * c.a + 2 * c.M * χ) + M := add_le_add hfit hcmp
      _ ≤ 2 * M := by linarith
  -- the band cap
  have hround := c.round_cell
  simp only at hround
  have hband := c.original_old_band h block (rk i₀) (hrold i₀ hi₀)
    (by rw [hrnat i₀ hi₀]; exact hi₀.2) (w := 2 * M)
    (by linarith [c.width_lower]) h2M (by linarith)
  have hsum : (S.toFinset.card : ENNReal) * ENNReal.ofReal (δ * ω) ≤
      ENNReal.ofReal (25200 * cfg.K k * (2 * M) ^ cfg.d *
        binWeight (cfg.π k) χ (g 0) * cfg.timeLength k s * c.D ^ 2) := by
    calc (S.toFinset.card : ENNReal) * ENNReal.ofReal (δ * ω)
        = ∑ _i ∈ S.toFinset, ENNReal.ofReal (δ * ω) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S.toFinset, cfg.μ k (W i) :=
          Finset.sum_le_sum fun i hi => hWfloor i (Set.mem_toFinset.mp hi)
      _ = cfg.μ k (⋃ i ∈ S.toFinset, W i) :=
          (measure_biUnion_finset hdisj fun i _ => hWm i).symm
      _ ≤ cfg.μ k Band := measure_mono_ae hsubBand
      _ ≤ _ := hband
  have hpos : 0 ≤ 25200 * cfg.K k * (2 * M) ^ cfg.d *
      binWeight (cfg.π k) χ (g 0) * cfg.timeLength k s * c.D ^ 2 := by
    have : 0 ≤ (2 * M) ^ cfg.d := Real.rpow_nonneg (by linarith) _
    have := binWeight_nonneg (cfg.π k) χ (g 0)
    have : 0 ≤ 25200 * cfg.K k := by linarith
    positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hpos] at hsum
  -- arithmetic
  have hbin : 0 < binWeight (cfg.π k) χ (g 0) := by
    have hp := hrpal i₀ hi₀
    simp only [hval i₀ hi₀] at hp
    exact hp
  have had : 0 < c.a ^ cfg.d := Real.rpow_pos_of_pos ha0 _
  have h2d : (2 * M) ^ cfg.d ≤ 2 * M ^ cfg.d := by
    rw [Real.mul_rpow (by norm_num) hM0.le]
    have : (2 : ℝ) ^ cfg.d ≤ 2 := by
      calc (2 : ℝ) ^ cfg.d ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hM0.le _)
  have hMa : (M / c.a) ^ cfg.d = M ^ cfg.d / c.a ^ cfg.d := Real.div_rpow hM0.le ha0.le _
  have hcard : (S.ncard : ℝ) = S.toFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
  change (S.ncard : ℝ) ≤ _
  rw [hcard, hMa, le_div_iff₀ hδ]
  have key : (S.toFinset.card : ℝ) * δ * ω ≤
      25200 * cfg.K k * (2 * M) ^ cfg.d * binWeight (cfg.π k) χ (g 0) *
        cfg.timeLength k s * c.D ^ 2 := by
    calc (S.toFinset.card : ℝ) * δ * ω = (S.toFinset.card : ℝ) * (δ * ω) := by ring
      _ ≤ _ := hsum
  have hωe : ω = (binWeight (cfg.π k) χ (g 0) * cfg.timeLength k s * c.D ^ 2) * c.a ^ cfg.d := by
    rw [hω]; ring
  have hX : 0 < binWeight (cfg.π k) χ (g 0) * cfg.timeLength k s * c.D ^ 2 := by positivity
  rw [hωe] at key
  have key2 : (S.toFinset.card : ℝ) * δ * c.a ^ cfg.d ≤ 25200 * cfg.K k * (2 * M) ^ cfg.d := by
    have := key
    have e : (S.toFinset.card : ℝ) * δ *
        ((binWeight (cfg.π k) χ (g 0) * cfg.timeLength k s * c.D ^ 2) * c.a ^ cfg.d) =
        ((S.toFinset.card : ℝ) * δ * c.a ^ cfg.d) *
          (binWeight (cfg.π k) χ (g 0) * cfg.timeLength k s * c.D ^ 2) := by ring
    have e2 : 25200 * cfg.K k * (2 * M) ^ cfg.d * binWeight (cfg.π k) χ (g 0) *
        cfg.timeLength k s * c.D ^ 2 = (25200 * cfg.K k * (2 * M) ^ cfg.d) *
          (binWeight (cfg.π k) χ (g 0) * cfg.timeLength k s * c.D ^ 2) := by ring
    rw [e, e2] at this
    exact le_of_mul_le_mul_right this hX
  have hK0 : 0 ≤ 25200 * cfg.K k := by linarith
  have hdiv : (S.toFinset.card : ℝ) * δ ≤
      (25200 * cfg.K k * (2 * M) ^ cfg.d) / c.a ^ cfg.d :=
    (le_div_iff₀ had).mpr key2
  have hmul : (25200 * cfg.K k * (2 * M) ^ cfg.d) / c.a ^ cfg.d ≤
      (25200 * cfg.K k * (2 * M ^ cfg.d)) / c.a ^ cfg.d :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2d hK0) had.le
  have hratio : 0 ≤ M ^ cfg.d / c.a ^ cfg.d :=
    div_nonneg (Real.rpow_nonneg hM0.le _) had.le
  have heq : (25200 * cfg.K k * (2 * M ^ cfg.d)) / c.a ^ cfg.d =
      50400 * cfg.K k * (M ^ cfg.d / c.a ^ cfg.d) := by ring
  rw [heq] at hmul
  exact hdiv.trans (hmul.trans (mul_le_mul_of_nonneg_right
    (by linarith only [hK] : 50400 * cfg.K k ≤ 100800 * cfg.K k) hratio))

end

end Submission.Obl.k4_horizontal_strict_parameter_step
