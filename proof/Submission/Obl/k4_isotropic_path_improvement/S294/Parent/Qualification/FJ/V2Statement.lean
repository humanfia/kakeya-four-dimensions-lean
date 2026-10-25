-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Statement, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Statement.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Statement.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Statement.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2FirstJet
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.FirstJet
import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

set_option autoImplicit false

/-!
# The version-2 first-jet statement from the range kernel

The `j = 2` counterparts of x0260's `ScalarFiniteFirstJet.lean`, `ScalarPositiveFirstJet.lean`
and of the positive case of `ScalarDesignatedFirstJet.lean` (o078, branch `x0260` at `206ab988`),
and the bridge from the interface `Jets2.ScalarNormal` (paper Def. `a04:scalar-data`, `j = 2`) to
the hypotheses `UpperHyp` used by the first-jet argument:

* `v2ClipRow K F`: the row clipped componentwise to `[-K, K]` (equal to `F` at labelled times);
* `upperHyp_of_scalarNormal`: `ScalarNormal … K …` gives `UpperHyp … (v2ClipRow K F) (8K) …` (the
  spatial cap on closed boxes of any side from the cap on half-open cubes of side `≤ 1`);
* `finite_v2_first_jet_between_powers`: finite thresholds (`∃ α N₀`) for the first jet at
  power-range levels (x0662/x0260's sequence-to-threshold argument,
  `k4_scalar_mesh_block_reduction.uniformity_of_sequence`);
* `v2_first_jet_at_positive_exponents`: designated levels within a factor `K` of fixed powers;
* **`firstJetStatement_of_range : RangeFitStatement → Jets2.FirstJetStatement`**.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-! ### Clipping the row -/

/-- The row clipped componentwise to `[-K, K]`. -/
def v2ClipRow (K : ℝ) (F : ℝ → Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  fun i => max (-K) (min K (F t i))

theorem measurable_v2ClipRow {K : ℝ} {F : ℝ → Fin 2 → ℝ} (hF : Measurable F) :
    Measurable (v2ClipRow K F) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_const.max (measurable_const.min ((measurable_pi_apply i).comp hF))

theorem v2ClipRow_eq {K : ℝ} {F : ℝ → Fin 2 → ℝ} {t : ℝ} (h : ‖F t‖ ≤ K) :
    v2ClipRow K F t = F t := by
  funext i
  have hi := abs_le.mp ((abs_le_norm (F t) i).trans h)
  simp only [v2ClipRow]
  rw [min_eq_right hi.2, max_eq_right hi.1]

theorem norm_v2ClipRow_le {K : ℝ} (hK : 0 ≤ K) (F : ℝ → Fin 2 → ℝ) (t : ℝ) :
    ‖v2ClipRow K F t‖ ≤ K := by
  refine norm_le_of_abs_le hK fun i => ?_
  simp only [v2ClipRow]
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-! ### From the interface to the upper hypotheses -/

theorem norm_zpos_sub_le (c c' : Fin 7 → ℝ) (t t' : ℝ) :
    ‖zpos c t - zpos c' t'‖ ≤
      |t - t'| + |zx c t - zx c' t'| + |zy c t 0 - zy c' t' 0| + |zy c t 1 - zy c' t' 1| := by
  refine norm_le_of_abs_le (by positivity) fun i => ?_
  fin_cases i <;> simp [zpos] <;> linarith [abs_nonneg (t - t'), abs_nonneg (zx c t - zx c' t'),
    abs_nonneg (c 3 + c 4 * t - (c' 3 + c' 4 * t')), abs_nonneg (c 5 + c 6 * t - (c' 5 + c' 6 * t'))]

/-- **The interface gives the upper hypotheses** of the first jet, for the clipped row and the
constant `8K`. -/
theorem upperHyp_of_scalarNormal {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}
    {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ}
    {K ζ d : ℝ} (h : ScalarNormal ν c E F piece K ζ d) (hd0 : 0 ≤ d) (hd : d ≤ 1) :
    UpperHyp ν c E (v2ClipRow K F) (8 * K) ζ d := by
  have hK := h.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hKK : K ≤ 8 * K := by linarith
  letI := h.prob
  have hclip : ∀ p ∈ E, v2ClipRow K F p.2 = F p.2 := fun p hp => v2ClipRow_eq (h.row_le p hp)
  refine ⟨h.measurable_c, h.measurableSet_E, measurable_v2ClipRow h.measurable_F,
    fun p hp => ⟨mem_univ _, h.time_mem p hp⟩,
    fun p hp e => (h.coeff_le p hp e).trans hKK,
    fun t => (norm_v2ClipRow_le hK0 F t).trans hKK, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq
    rw [hclip p hp, hclip q hq]
    exact (h.row_cmp p hp q hq).trans
      (mul_le_mul_of_nonneg_right hKK (by have := h.zeta_pos; positivity))
  · intro p hp q hq
    have hR : ∀ r ∈ E, zR (v2ClipRow K F) (c r.1) r.2 = zR F (c r.1) r.2 := by
      intro r hr
      simp only [zR, hclip r hr]
    rw [hR p hp, hR q hq]
    refine (h.resid_cmp p hp q hq).trans ?_
    have hz := norm_zpos_sub_le (c p.1) (c q.1) p.2 q.2
    have hζ := h.zeta_pos
    calc K * (‖zpos (c p.1) p.2 - zpos (c q.1) q.2‖ + ζ)
        ≤ K * (|p.2 - q.2| + |zx (c p.1) p.2 - zx (c q.1) q.2| +
            |zy (c p.1) p.2 0 - zy (c q.1) q.2 0| + |zy (c p.1) p.2 1 - zy (c q.1) q.2 1| + ζ) :=
          mul_le_mul_of_nonneg_left (by linarith) hK0
      _ ≤ 8 * K * (|p.2 - q.2| + |zx (c p.1) p.2 - zx (c q.1) q.2| +
            |zy (c p.1) p.2 0 - zy (c q.1) q.2 0| + |zy (c p.1) p.2 1 - zy (c q.1) q.2 1| + ζ) :=
          mul_le_mul_of_nonneg_right hKK (by positivity)
  · intro t
    have hset : scalarSupport c (v2ClipRow K F) E t = {s | ∃ l, (l, t) ∈ E ∧ zS F (c l) t = s} := by
      ext s
      constructor
      · rintro ⟨l, hl, rfl⟩
        refine ⟨l, hl, ?_⟩
        simp only [zS, hclip (l, t) hl]
      · rintro ⟨l, hl, rfl⟩
        refine ⟨l, hl, ?_⟩
        simp only [zS, hclip (l, t) hl]
    rw [hset]
    exact CellProofs.Assouad.mono_constant h.zeta_pos (h.support t) hKK
  · intro t a b₀ b₁ r hr
    have hr0 : 0 < r := h.zeta_pos.trans_le hr
    by_cases h2r : 2 * r ≤ 1
    · let b : Fin 2 → ℝ := ![b₀, b₁]
      have hsub : {l | (l, t) ∈ E ∧ zx (c l) t ∈ Icc a (a + r) ∧ zy (c l) t 0 ∈ Icc b₀ (b₀ + r) ∧
          zy (c l) t 1 ∈ Icc b₁ (b₁ + r)} ⊆ {l | (l, t) ∈ E ∧ InCube (c l) t a b (2 * r)} := by
        rintro l ⟨hl, hx, hy0, hy1⟩
        refine ⟨hl, ⟨hx.1, by linarith [hx.2]⟩, fun i => ?_⟩
        fin_cases i
        · show zy (c l) t 0 ∈ Ico b₀ (b₀ + 2 * r)
          exact ⟨hy0.1, by linarith [hy0.2]⟩
        · show zy (c l) t 1 ∈ Ico b₁ (b₁ + 2 * r)
          exact ⟨hy1.1, by linarith [hy1.2]⟩
      have hcap := h.abs_cap t a b (2 * r) (by linarith) h2r
      have hfin : ν {l | (l, t) ∈ E ∧ InCube (c l) t a b (2 * r)} ≠ ⊤ := measure_ne_top ν _
      have hreal : ν.real {l | (l, t) ∈ E ∧ InCube (c l) t a b (2 * r)} ≤
          K * (2 * r) ^ (2 + d) := by
        have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap
        rw [ENNReal.toReal_ofReal (by positivity)] at hh
        exact hh
      have hpow : (2 * r) ^ (2 + d) ≤ 8 * r ^ (2 + d) := by
        rw [Real.mul_rpow (by norm_num) hr0.le]
        have h2 : (2 : ℝ) ^ (2 + d) ≤ 2 ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
        rw [h8] at h2
        exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hr0.le _)
      calc _ ≤ ν.real {l | (l, t) ∈ E ∧ InCube (c l) t a b (2 * r)} :=
            measureReal_mono hsub hfin
        _ ≤ K * (2 * r) ^ (2 + d) := hreal
        _ ≤ K * (8 * r ^ (2 + d)) := mul_le_mul_of_nonneg_left hpow hK0
        _ = 8 * K * r ^ (2 + d) := by ring
    · push_neg at h2r
      have hone : ν.real {l | (l, t) ∈ E ∧ zx (c l) t ∈ Icc a (a + r) ∧
          zy (c l) t 0 ∈ Icc b₀ (b₀ + r) ∧ zy (c l) t 1 ∈ Icc b₁ (b₁ + r)} ≤ 1 := by
        calc _ ≤ ν.real univ := measureReal_mono (subset_univ _) (measure_ne_top ν _)
          _ = 1 := by simp [Measure.real]
      have hr8 : 1 ≤ 8 * r ^ (2 + d) := by
        by_cases hr1 : r ≤ 1
        · have h3 : r ^ (3 : ℝ) ≤ r ^ (2 + d) :=
            Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
          have hcube : (1 / 2 : ℝ) ^ (3 : ℝ) ≤ r ^ (3 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
          have h18 : (1 / 2 : ℝ) ^ (3 : ℝ) = 1 / 8 := by norm_num
          rw [h18] at hcube
          linarith
        · push_neg at hr1
          have h1 : (1 : ℝ) ≤ r ^ (2 + d) := Real.one_le_rpow hr1.le (by linarith)
          linarith
      calc _ ≤ 1 := hone
        _ ≤ 8 * r ^ (2 + d) := hr8
        _ ≤ K * (8 * r ^ (2 + d)) := by nlinarith [Real.rpow_nonneg hr0.le (2 + d)]
        _ = 8 * K * r ^ (2 + d) := by ring

theorem scalarNormal_dense_real {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}
    {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ}
    {K ζ d : ℝ} (h : ScalarNormal ν c E F piece K ζ d) : K⁻¹ ≤ (ν.prod volume).real E := by
  letI := h.prob
  have hfinite := original_unit_incidence_ne_top ν h.measurableSet_E
    (fun p hp => ⟨mem_univ _, h.time_mem p hp⟩)
  have hreal := ENNReal.toReal_mono hfinite h.dense
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (zero_le_one.trans h.one_le_K))] at hreal
  exact hreal

/-! ### Finite thresholds -/

/-- The first jet at power-range levels for every world with constants up to `N^α`. -/
def V2FirstJetUniformAt (a b d : ℝ) (m : ℕ) (ε α N : ℝ) : Prop :=
  ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) [IsProbabilityMeasure ν]
    (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (K ζ : ℝ)
    (start : Fin m → ℕ) (read : Fin m),
    1 ≤ K → K ≤ N ^ α → UpperHyp ν c E F K ζ d → 0 < ζ →
    K⁻¹ ≤ (ν.prod volume).real E → ζ ≤ N ^ (-(4 * b)) →
    (∀ i, N ^ (-b) ≤ scalarDyadicLength (start i)) →
    (∀ i, scalarDyadicLength (start i) ≤ N ^ (-a)) →
    V2FirstJetOutput ν c E F start read d (N ^ ε)

/-- **Finite thresholds for the version-2 first jet** (x0260's sequence argument). -/
theorem finite_v2_first_jet_between_powers (hker : RangeFitStatement)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → V2FirstJetUniformAt a b d m ε α N := by
  obtain ⟨α, hα, N₀, hN₀, hfinite⟩ :=
    Submission.Obl.k4_scalar_mesh_block_reduction.uniformity_of_sequence
      (Model := fun _ _ => Unit) (fun _ _ _ => True)
      (fun α N _ => V2FirstJetUniformAt a b d m ε α N) (by
        intro η Ns hη hηlim hNtwo hNt model _
        have hN : ∀ k, 1 ≤ Ns k := fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hNtwo k)
        let Ks : ℕ → ℝ := fun k => Ns k ^ η k
        obtain ⟨hKs, hKssub⟩ :=
          Submission.Obl.k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
            Ns η hN (fun k => (hη k).le) hηlim
        obtain ⟨H, hH, hHsub, hgood⟩ :=
          uniform_v2_first_jet_between_powers_all_labels hker Ns Ks hN hNt hKs hKssub
            ha hab hd0 hd m
        obtain ⟨k, hk, hsmall⟩ := (hgood.and (hHsub ε hε)).exists
        refine ⟨k, ?_⟩
        intro Λ _ ν _ c E F K ζ start read hK hKN hnormal hζ hmass hζN hlow hhigh
        have hnormalk : UpperHyp ν c E F (Ks k) ζ d := hnormal.increase_constant hζ hKN
        have hmassk : (Ks k)⁻¹ ≤ (ν.prod volume).real E :=
          (inv_anti₀ (zero_lt_one.trans_le hK) hKN).trans hmass
        have houtput := hk Λ ν c E F ζ start read hnormalk hζ hmassk hζN hlow hhigh
        exact houtput.mono (zero_lt_one.trans_le (hH k)) hsmall)
  exact ⟨α, hα, N₀, hN₀, fun N hN => hfinite N hN () trivial⟩

/-- **The version-2 first jet at designated levels within a factor `K` of fixed powers**, for
the interface `ScalarNormal` (with the clipped row). -/
theorem v2_first_jet_at_positive_exponents (hker : RangeFitStatement) {d ε : ℝ} (hd0 : 0 ≤ d)
    (hd : d < 1) {m : ℕ} (γ : Fin m → ℝ) (b : ℝ) (read : Fin m)
    (hγ : ∀ i, 0 < γ i) (hγb : ∀ i, γ i ≤ b) (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 7 → ℝ)
        (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Λ → Fin 7 → ℤ) (K ζ : ℝ)
        (start : Fin m → ℕ),
        K ≤ N ^ α → ScalarNormal ν c E F piece K ζ d → ζ ≤ N ^ (-(8 * b)) →
        (∀ i, N ^ (-γ i) / K ≤ scalarDyadicLength (start i)) →
        (∀ i, scalarDyadicLength (start i) ≤ K * N ^ (-γ i)) →
        V2FirstJetOutput ν c E (v2ClipRow K F) start read d (N ^ ε) := by
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ γ ⟨read, Finset.mem_univ _⟩
  let a := γ imin
  have ha : 0 < a := hγ imin
  have hab : a ≤ b := hγb imin
  have hamin : ∀ i, a ≤ γ i := fun i => hmin i (Finset.mem_univ _)
  obtain ⟨αf, hαf, Nf, hNf, hfinite⟩ :=
    finite_v2_first_jet_between_powers hker (a := a / 2) (b := 2 * b) (by positivity)
      (by linarith) hd0 hd m hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      8 (a := αf / 2) (b := αf) (by linarith))
  let α := min (αf / 2) (a / 4)
  have hα : 0 < α := lt_min (by positivity) (by positivity)
  refine ⟨α, hα, max Nf M, hNf.trans (le_max_left _ _), ?_⟩
  intro N hN Λ _ ν c E F piece K ζ start hKN hSN hζN hlow hhigh
  letI := hSN.prob
  have hK := hSN.one_le_K
  have hNNf : Nf ≤ N := (le_max_left Nf M).trans hN
  have hNM : M ≤ N := (le_max_right Nf M).trans hN
  have hNtwo : 2 ≤ N := hNf.trans hNNf
  have hN1 : 1 ≤ N := by linarith
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKhalf : K ≤ N ^ (αf / 2) :=
    hKN.trans (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _))
  have hKprepared : 8 * K ≤ N ^ αf :=
    (mul_le_mul_of_nonneg_left hKhalf (by norm_num : (0 : ℝ) ≤ 8)).trans (hM N hNM)
  have hKsmall : K ≤ N ^ (a / 4) :=
    hKN.trans (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _))
  have hrange (i : Fin m) : N ^ (-(2 * b)) ≤ scalarDyadicLength (start i) ∧
      scalarDyadicLength (start i) ≤ N ^ (-(a / 2)) :=
    scalar_factor_power_range hN1 hK ha hab (hamin i) (hγb i) hKsmall (hlow i) (hhigh i)
  have hmassPrepared : (8 * K)⁻¹ ≤ (ν.prod volume).real E :=
    (inv_anti₀ hKpos (by linarith : K ≤ 8 * K)).trans (scalarNormal_dense_real hSN)
  have hfloor : ζ ≤ N ^ (-(4 * (2 * b))) := by
    simpa only [show (4 * (2 * b) : ℝ) = 8 * b by ring] using hζN
  exact hfinite N hNNf Λ ν c E (v2ClipRow K F) (8 * K) ζ start read
    (by linarith : 1 ≤ 8 * K) hKprepared (upperHyp_of_scalarNormal hSN hd0 hd.le) hSN.zeta_pos
    hmassPrepared hfloor (fun i => (hrange i).1) (fun i => (hrange i).2)

/-! ### The first-jet statement -/

theorem scalarDyadicLength_eq_inv (T : ℕ) : scalarDyadicLength T = ((2 : ℝ) ^ T)⁻¹ := by
  rw [scalarDyadicLength_eq]; push_cast; ring

theorem jet_leafRows_one (F A : ℝ → Fin 2 → ℝ) (c : Fin 7 → ℝ) (t : ℝ) :
    jet (leafRows F A t) c t 1 = v2FirstJet c F A t := by
  simp only [jet, leafRows, xder, v2FirstJet, zR, Nat.cast_one, one_mul, Nat.sub_self,
    one_ne_zero, if_false, if_true]
  ring

/-- **The version-2 first-jet statement**, given the range form of the planar kernel. -/
theorem firstJetStatement_of_range (hker : RangeFitStatement) : FirstJetStatement := by
  intro d hd0 hd1 r γ γ₀ hγ hγ₀ hγ₀pos
  let Γ : Fin (r + 1) → ℝ := Fin.cases γ₀ γ
  have hΓ : ∀ i, 0 < Γ i := fun i => Fin.cases hγ₀pos (fun j => hγ j) i
  have hΓupper : ∀ i, Γ i ≤ γ₀ := fun i => Fin.cases le_rfl (fun j => hγ₀ j) i
  refine ⟨8 * γ₀, by positivity, ?_⟩
  intro ε hε
  obtain ⟨α, hα, N₀, hN₀2, hpos⟩ := v2_first_jet_at_positive_exponents hker hd0 hd1 Γ γ₀ 0 hΓ
    hΓupper hε
  refine ⟨α, hα, N₀, ?_⟩
  intro N hN Λ _ ν c E F piece K ζ Tl T₀ hKN hζN hlevels hT₀lo hT₀hi _ hSN
  let start : Fin (r + 1) → ℕ := Fin.cases T₀ Tl
  have hlowΓ : ∀ i, N ^ (-Γ i) / K ≤ scalarDyadicLength (start i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Γ, start, Fin.cases_zero, scalarDyadicLength_eq_inv] using hT₀lo
    · simpa only [Γ, start, Fin.cases_succ, scalarDyadicLength_eq_inv] using (hlevels j).1
  have hhighΓ : ∀ i, scalarDyadicLength (start i) ≤ K * N ^ (-Γ i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Γ, start, Fin.cases_zero, scalarDyadicLength_eq_inv] using hT₀hi
    · simpa only [Γ, start, Fin.cases_succ, scalarDyadicLength_eq_inv] using (hlevels j).2
  have hζ' : ζ ≤ N ^ (-(8 * γ₀)) := hζN
  obtain ⟨E₁, hE₁E, hE₁m, hmass, A, hAm, hAb, hTaylor, L, hL, hcover⟩ :=
    hpos N hN Λ ν c E F piece K ζ start hKN hSN hζ' hlowΓ hhighΓ
  have hN0 : 0 ≤ N := by linarith
  have hclip : ∀ p ∈ E, v2ClipRow K F p.2 = F p.2 := fun p hp => v2ClipRow_eq (hSN.row_le p hp)
  refine ⟨E₁, hE₁E, hE₁m, ?_, A, hAm, hAb, ?_, ?_⟩
  · rw [Real.rpow_neg hN0]; exact hmass
  · intro i j p hp p' hp' h1 h2
    have hh := hTaylor i.succ j p hp p' hp' h1 h2
    rw [hclip p (hE₁E hp), hclip p' (hE₁E hp')] at hh
    simpa only [start, Fin.cases_succ, scalarDyadicLength_eq_inv] using hh
  · intro t
    refine ⟨L t, fun σ => Nat.le_floor (hL t σ), ?_⟩
    intro l _ hlt
    obtain ⟨v, hv, hdist⟩ := hcover (l, t) hlt
    have hFt : v2ClipRow K F t = F t := hclip (l, t) (hE₁E hlt)
    have hS : zS (v2ClipRow K F) (c l) t = zS F (c l) t := by simp only [zS, hFt]
    have hJ : v2FirstJet (c l) (v2ClipRow K F) A t = jet (leafRows F A t) (c l) t 1 := by
      rw [jet_leafRows_one]; simp only [v2FirstJet, zR, hFt]
    refine ⟨v, ?_, ?_⟩
    · show v ∈ L t ⌊zS F (c l) t / ((2 : ℝ) ^ T₀)⁻¹⌋
      simpa only [hS, start, Fin.cases_zero, scalarDyadicLength_eq_inv] using hv
    · show |jet (leafRows F A t) (c l) t 1 - v| ≤ N ^ ε * (((2 : ℝ) ^ T₀)⁻¹) ^ ((1 - d) / 32)
      rw [← hJ]
      simpa only [start, Fin.cases_zero, scalarDyadicLength_eq_inv] using hdist

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
