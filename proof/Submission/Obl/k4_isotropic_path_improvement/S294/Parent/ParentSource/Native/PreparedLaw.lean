-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PreparedLaw, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PreparedLaw.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PreparedLaw.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PreparedLaw.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/PreparedLaw.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PreparedFamily
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Histories
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.VelocityPalette

/-! Normalize the surviving original world mixture once, retaining its world
label. Every later restriction can refer to this same probability law. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable def labelledResidual {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X) :
    Measure (Fin W × X) :=
  ∑ w, ENNReal.ofReal (ω w) • (μ w |>.restrict (H w)).map (Prod.mk w)

def labelledSupport {W : ℕ} {X : Type*} (H : Fin W → Set X) : Set (Fin W × X) :=
  {z | z.2 ∈ H z.1}

theorem measurableSet_labelledSupport {W : ℕ} {X : Type*} [MeasurableSpace X]
    (H : Fin W → Set X) (hH : ∀ w, MeasurableSet (H w)) :
    MeasurableSet (labelledSupport H) := by
  have heq : labelledSupport H = ⋃ w, ({w} ×ˢ H w) := by ext z; simp [labelledSupport]
  rw [heq]
  exact MeasurableSet.iUnion (fun w => (measurableSet_singleton w).prod (hH w))

theorem labelledResidual_apply {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (D : Set (Fin W × X)) (hD : MeasurableSet D) :
    labelledResidual μ ω H D = ∑ w, ENNReal.ofReal (ω w) *
      μ w (H w ∩ {x | (w, x) ∈ D}) := by
  classical
  simp only [labelledResidual, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [Measure.map_apply measurable_prodMk_left hD,
    Measure.restrict_apply (hD.preimage measurable_prodMk_left), Set.inter_comm]
  rfl

theorem labelledResidual_univ {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X) :
    labelledResidual μ ω H univ = ∑ w, ENNReal.ofReal (ω w) * μ w (H w) := by
  rw [labelledResidual_apply μ ω H _ MeasurableSet.univ]
  simp

theorem labelledResidual_support {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (hH : ∀ w, MeasurableSet (H w)) :
    labelledResidual μ ω H (labelledSupport H)ᶜ = 0 := by
  rw [labelledResidual_apply μ ω H _ (measurableSet_labelledSupport H hH).compl]
  have heq (w : Fin W) : H w ∩ {x | (w, x) ∈ (labelledSupport H)ᶜ} = ∅ := by
    ext x
    simp [labelledSupport]
  simp only [heq, measure_empty, mul_zero, Finset.sum_const_zero]

noncomputable def preparedResidualLaw {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X) :
    Measure (Fin W × X) := ProbabilityTheory.cond (labelledResidual μ ω H) univ

theorem preparedResidualLaw_apply {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (D : Set (Fin W × X)) (hD : MeasurableSet D) :
    preparedResidualLaw μ ω H D =
      (∑ w, ENNReal.ofReal (ω w) * μ w (H w ∩ {x | (w, x) ∈ D})) /
        (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) := by
  simp only [preparedResidualLaw, ProbabilityTheory.cond, Measure.restrict_univ,
    Measure.smul_apply, smul_eq_mul, labelledResidual_univ,
    labelledResidual_apply μ ω H D hD, div_eq_mul_inv, mul_comm]

theorem preparedResidualLaw_support {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (hH : ∀ w, MeasurableSet (H w)) :
    preparedResidualLaw μ ω H (labelledSupport H)ᶜ = 0 := by
  simp only [preparedResidualLaw, ProbabilityTheory.cond, Measure.restrict_univ,
    Measure.smul_apply, smul_eq_mul, labelledResidual_support μ ω H hH, mul_zero]

theorem preparedResidualLaw_probability {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1) (hμ : ∀ w, μ w (H w) ≤ 1)
    {a : ℝ} (ha : 0 < a)
    (hmass : ENNReal.ofReal a ≤ ∑ w, ENNReal.ofReal (ω w) * μ w (H w)) :
    IsProbabilityMeasure (preparedResidualLaw μ ω H) := by
  have htotal : labelledResidual μ ω H univ ≤ 1 := by
    rw [labelledResidual_univ]
    calc
      _ ≤ ∑ w, ENNReal.ofReal (ω w) := Finset.sum_le_sum fun w _ => by
        simpa using mul_le_mul_of_nonneg_left (hμ w)
          (show (0 : ENNReal) ≤ ENNReal.ofReal (ω w) from zero_le)
      _ = 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω w), hsum]
        norm_num
  have hpos : 0 < labelledResidual μ ω H univ := by
    rw [labelledResidual_univ]
    exact (ENNReal.ofReal_pos.mpr ha).trans_le hmass
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite hpos.ne'
    (ne_top_of_le_ne_top (by simp) htotal)

/-- A probability floor under the single prepared law becomes a floor under
the ORIGINAL world mixture after undoing its one normalization. -/
theorem prepared_cut_original_floor {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (D : Set (Fin W × X)) (hD : MeasurableSet D) {a b : ℝ} (ha : 0 < a)
    (htop : (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) ≠ ∞)
    (hmass : ENNReal.ofReal a ≤ ∑ w, ENNReal.ofReal (ω w) * μ w (H w))
    (hkeep : ENNReal.ofReal b ≤ preparedResidualLaw μ ω H D) :
    ENNReal.ofReal (a * b) ≤
      ∑ w, ENNReal.ofReal (ω w) * μ w (H w ∩ {x | (w, x) ∈ D}) := by
  let total := ∑ w, ENNReal.ofReal (ω w) * μ w (H w)
  have hzero : total ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos.mpr ha).trans_le hmass)
  have hid : total * preparedResidualLaw μ ω H D =
      ∑ w, ENNReal.ofReal (ω w) * μ w (H w ∩ {x | (w, x) ∈ D}) := by
    rw [preparedResidualLaw_apply μ ω H D hD, div_eq_mul_inv]
    change total * (_ * total⁻¹) = _
    rw [mul_left_comm, ENNReal.mul_inv_cancel hzero htop, mul_one]
  calc
    _ = ENNReal.ofReal a * ENNReal.ofReal b := ENNReal.ofReal_mul ha.le
    _ ≤ total * preparedResidualLaw μ ω H D := mul_le_mul hmass hkeep zero_le zero_le
    _ = _ := hid

/-- Choose a window under the single prepared original law, using the actual
finite supplied packet histories. This does not condition anew at each depth. -/
theorem prepared_histories_good_velocity_window
    {W P : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1) (hμ : ∀ w, μ w (H w) ≤ 1)
    (hH : ∀ w, MeasurableSet (H w)) {a : ℝ} (ha : 0 < a)
    (hmass : ENNReal.ofReal a ≤ ∑ w, ENNReal.ofReal (ω w) * μ w (H w))
    (lev : Fin P → ℕ) (γ : Fin P → Fin W) (F : Fin P → Set X)
    (hF : ∀ b, MeasurableSet (F b)) (V : Fin W × X → Fin 2 → ℝ)
    (hVm : Measurable V) (q C : ℕ) (hC : 1 ≤ C) (A : Finset ℕ)
    (hA : ∀ k ∈ A, k < q ∧ k + C ≤ q)
    (N σ u τ α : ℝ) (hN : 1 ≤ N) (hσ : 0 ≤ σ) (hu : 0 ≤ u)
    (hτ : 0 ≤ τ) (hα : 0 ≤ α)
    (hV : ∀ w x, x ∈ H w → ∀ j, |V (w, x) j| ≤ N ^ σ)
    (hbudget : (C : ℝ) * (2 * Real.log 10 + 2 * (σ + u) * Real.log N) + (q : ℝ) <
      (A.card : ℝ) * (τ * Real.log N * α)) :
    ∃ k ∈ A, Submission.Obl.k4_matching_cofinal_palette_selection.badMass
      (preparedResidualLaw μ ω H) (labelledSupport H) (finitePacketHistory lev γ F)
      (fun x => velocityPalette (N ^ (-u)) (V x)) C k (N ^ τ) ≤ ENNReal.ofReal α := by
  letI := preparedResidualLaw_probability μ ω H hω hsum hμ ha hmass
  apply exists_good_velocity_window (preparedResidualLaw μ ω H) (labelledSupport H)
    (measurableSet_labelledSupport H hH) (preparedResidualLaw_support μ ω H hH)
    (finitePacketHistory lev γ F) V q C hC
    (fun k _ => measurable_finitePacketHistory lev γ F hF k)
    (fun k _ => (finite_finitePacketHistory_range lev γ F k).subset (Set.image_subset_range _ _))
    (fun _ _ hij _ _ _ _ _ heq => finitePacketHistory_nested lev γ F hij heq)
    hVm A hA N σ u τ α hN hσ hu hτ hα _ hbudget
  rintro ⟨w, x⟩ hx j
  exact hV w x hx j

def nativeVelocityResidual {W : ℕ}
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (K : ℝ)
    (w : Fin W) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  H w ∩ {z | ‖v z.1‖ ≤ K}

/-- The native bounds are only almost everywhere in the original statement.
Removing their null exception gives pointwise velocity bounds and costs no
original incidence mass, even before any residual normalization. -/
theorem ProblemData.Valid.clean_native_velocity {d : ProblemData} (h : d.Valid)
    (k : ℕ) (H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hH : ∀ w, MeasurableSet (H w)) :
    (∀ w, MeasurableSet (nativeVelocityResidual H (d.K k) w) ∧
      nativeVelocityResidual H (d.K k) w ⊆ H w ∧
      ∀ z ∈ nativeVelocityResidual H (d.K k) w, ∀ j, |v z.1 j| ≤ d.K k) ∧
    ∀ w, ((d.ν k w).prod volume) (nativeVelocityResidual H (d.K k) w) =
      ((d.ν k w).prod volume) (H w) := by
  have hvc : Continuous v :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.continuous_planarVelocity
  have hgood : MeasurableSet {z : (ℕ × (Fin 6 → ℝ)) × ℝ | ‖v z.1‖ ≤ d.K k} :=
    measurableSet_le (hvc.norm.measurable.comp measurable_fst) measurable_const
  refine ⟨?_, ?_⟩
  · intro w
    refine ⟨(hH w).inter hgood, inter_subset_left, ?_⟩
    intro z hz j
    have hj : |v z.1 j| ≤ ‖v z.1‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v z.1) j
    exact hj.trans hz.2
  · intro w
    have hv : ∀ᵐ l ∂d.ν k w, ‖v l‖ ≤ d.K k := by
      filter_upwards [h.native_bounds k w] with l hl
      have hzero := hl 0 ⟨le_rfl, zero_le_one⟩
      linarith [norm_nonneg (y l 0)]
    have hnull : d.ν k w {l | ¬ ‖v l‖ ≤ d.K k} = 0 := ae_iff.mp hv
    have hnullprod : ((d.ν k w).prod volume)
        {z : (ℕ × (Fin 6 → ℝ)) × ℝ | ‖v z.1‖ ≤ d.K k}ᶜ = 0 := by
      have heq : {z : (ℕ × (Fin 6 → ℝ)) × ℝ | ‖v z.1‖ ≤ d.K k}ᶜ =
          {l | ¬ ‖v l‖ ≤ d.K k} ×ˢ (univ : Set ℝ) := by ext z; simp
      rw [heq, Measure.prod_prod, hnull, zero_mul]
    exact measure_inter_conull hnullprod

section ValidPath

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.residual_world_mass_le_one
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hν : ∀ w, IsProbabilityMeasure (ν w))
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (w : Fin W) : ((ν w).prod volume) (H w) ≤ 1 := by
  have := hν w
  have hsub : H w ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
    intro z hz
    obtain ⟨b, _, _, hb⟩ := hH w hz
    rcases h.2.2.2.2.2.2.2 b with ⟨_, hj, _, _, _, _, _, _, _, _, _, _, hF, _⟩
    refine ⟨mem_univ _, ?_⟩
    exact Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_subset_unit
      (p.T (p.lev b)) ⟨p.j b, hj⟩ (hF z hb).2.2.1
  calc
    _ ≤ ((ν w).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hsub
    _ = 1 := by simp [Measure.prod_prod, Real.volume_Icc]

end ValidPath

/-- The entropy window preparation applies uniformly to every supplied path
and substantial residual of the frozen problem after one late cutoff. -/
theorem ProblemData.Valid.prepare_path_velocity_window {d : ProblemData} (hd : d.Valid)
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σpath : ℝ)
    (q C : ℕ) (hC : 1 ≤ C) (A : Finset ℕ)
    (hA : ∀ k ∈ A, k < q ∧ k + C ≤ q)
    (σvel u τ α : ℝ) (hσvel : 0 < σvel) (hu : 0 ≤ u)
    (hτ : 0 ≤ τ) (hα : 0 ≤ α)
    (hgap : 2 * (C : ℝ) * (σvel + u) < (A.card : ℝ) * (τ * α)) :
    ∀ᶠ k in Filter.atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σpath →
      ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      (∀ w, ((d.ν k w).prod volume) (nativeVelocityResidual H (d.K k) w) =
        ((d.ν k w).prod volume) (H w)) ∧
      IsProbabilityMeasure (preparedResidualLaw (fun w => (d.ν k w).prod volume)
        (d.ω k) (nativeVelocityResidual H (d.K k))) ∧
      ∃ i ∈ A, Submission.Obl.k4_matching_cofinal_palette_selection.badMass
        (preparedResidualLaw (fun w => (d.ν k w).prod volume)
          (d.ω k) (nativeVelocityResidual H (d.K k)))
        (labelledSupport (nativeVelocityResidual H (d.K k)))
        (finitePacketHistory p.lev p.γ p.F)
        (fun z => velocityPalette (d.N k ^ (-u)) (fun j => v z.2.1 j))
        C i (d.N k ^ τ) ≤ ENNReal.ofReal α := by
  have hK := hd.2.2.1.2 σvel hσvel
  have hbudget := eventually_velocity_window_budget d.N hd.tendsto A q C σvel u τ α hgap
  filter_upwards [hK, hbudget] with k hKk hbudgetk
  intro p hp H hH hcover hmass
  have hclean := hd.clean_native_velocity k H hH
  let H₀ := nativeVelocityResidual H (d.K k)
  have hH₀ : ∀ w, MeasurableSet (H₀ w) := fun w => (hclean.1 w).1
  have hcover₀ : ∀ w, H₀ w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b} :=
    fun w => (hclean.1 w).2.1.trans (hcover w)
  have hmass₀ : ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H₀ w) := by
    simpa only [H₀, hclean.2] using hmass
  obtain ⟨hω, hsum, hν⟩ := hd.weights k
  have hworld := hp.residual_world_mass_le_one hν H₀ hcover₀
  have ha : 0 < p.κ⁻¹ / 2 := by have hκ := hp.1; positivity
  have hprob := preparedResidualLaw_probability (fun w => (d.ν k w).prod volume)
    (d.ω k) H₀ hω hsum hworld ha hmass₀
  refine ⟨hclean.2, hprob, ?_⟩
  have hF : ∀ b, MeasurableSet (p.F b) := by
    intro b
    rcases hp.2.2.2.2.2.2.2 b with ⟨_, _, _, _, _, _, _, _, _, hFb, _⟩
    exact hFb
  have hvc : Continuous v :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.continuous_planarVelocity
  have hVm : Measurable (fun z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
      fun j => v z.2.1 j) := by
    apply Measurable.of_eval
    intro j
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).comp hvc).measurable.comp
      (measurable_fst.comp measurable_snd)
  exact prepared_histories_good_velocity_window (fun w => (d.ν k w).prod volume)
    (d.ω k) H₀ hω hsum hworld hH₀ ha hmass₀ p.lev p.γ p.F hF _ hVm q C hC A hA
    (d.N k) σvel u τ α (by linarith [hd.1 k]) hσvel.le hu hτ hα
    (fun w x hx j => ((hclean.1 w).2.2 x hx j).trans hKk) hbudgetk

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
