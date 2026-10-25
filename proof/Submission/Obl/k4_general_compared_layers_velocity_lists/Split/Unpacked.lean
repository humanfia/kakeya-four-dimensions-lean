-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Split.Unpacked; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Split.Reindex

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Split

open MeasureTheory Set Filter
open Parent (block)
noncomputable section

namespace Unpacked

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def Validity : Prop :=
  (∀ k, 2 ≤ p.N k) ∧ Filter.Tendsto p.N Filter.atTop Filter.atTop ∧
  ((∀ k, 1 ≤ p.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, p.K k ≤ p.N k ^ ε) ∧
  0 ≤ p.d ∧ p.d < 1 ∧ 0 < p.κ ∧ p.κ ≤ 1 ∧ 0 < p.ℓ ∧ 0 < p.S ∧
  p.S ≤ 1 ∧ 0 < p.U ∧ 0 < p.e₀ ∧ p.Basic ∧ p.Caps ∧ p.Prepared ∧ p.Nested

def FrameConditions (k : ℕ) (r v m ε : ℝ)
    (parent : Fin (p.n k r)) (t₀ q z₀ zv : ℝ)
    (background : MvPolynomial (Fin 3) ℝ) (prior : MeasureTheory.Measure α)
    (law : MeasureTheory.Measure (α × ℝ)) (coeff : α → Fin 5 → ℝ)
    (good : Set α) (lists : ℤ → Finset ((Fin 2 → ℤ) × ℤ)) : Prop :=
  (MeasurableSet good) ∧
  (good ⊆ p.B k r parent) ∧
  (Measurable coeff) ∧
  (IsProbabilityMeasure prior) ∧
  (law ≤ ENNReal.ofReal (p.N k ^ ε) • (prior.prod volume)) ∧
  (law (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) ∧
  (∀ᵐ ω ∂law, ω.1 ∈ good) ∧
  (∀ l i, |coeff l i| ≤ p.N k ^ ε) ∧
  (ENNReal.ofReal (p.N k ^ (-ε)) ≤ law univ) ∧
  (0 < q) ∧
  (q = ((2 : ℝ) ^ p.T k r)⁻¹) ∧
  (block (p.T k r) (p.j k r parent) = Icc t₀ (t₀ + q)) ∧
  (background.totalDegree ≤ 2) ∧
  ((∑ e ∈ background.support, |background.coeff e|) ≤ p.N k ^ (m / 10)) ∧
  (1 + |q⁻¹| * (2 + |t₀| + |z₀| + |zv|) ≤ p.N k ^ (m / 10)) ∧
  (∀ l ∈ good, ∀ u,
    scalarY (coeff l) u = (p.x k l (t₀ + q * u) 1 - z₀ - zv * (t₀ + q * u)) / q) ∧
  (∀ l ∈ good, ∀ u,
    scalarX (coeff l) u = p.signal k l (t₀ + q * u) -
      MvPolynomial.eval (p.base k l (t₀ + q * u)) background) ∧
  ((ENNReal.ofReal q * p.ν k (p.A k r parent)) •
      law.map (fun ω => (ω.1, t₀ + q * ω.2)) ≤ p.ρ k) ∧
  (∀ a : ℤ, ((lists a).card : ℝ) * (p.N k ^ (-m)) ^ 2 ≤
    p.N k ^ ε * p.N k ^ (p.d * v)) ∧
  (∀ᵐ ω ∂law,
    (scalarCell (coeff ω.1) ω.2 (p.N k ^ (-m)),
      ⌊scalarX (coeff ω.1) ω.2 / p.N k ^ (-r - v)⌋) ∈
      lists ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋)

def Frames (k : ℕ) (r v m ε : ℝ) : Prop :=
  ∃ (parent : Fin (p.n k r)) (t₀ q z₀ zv : ℝ)
    (background : MvPolynomial (Fin 3) ℝ) (prior : MeasureTheory.Measure α)
    (law : MeasureTheory.Measure (α × ℝ)) (coeff : α → Fin 5 → ℝ)
    (good : Set α) (lists : ℤ → Finset ((Fin 2 → ℤ) × ℤ)), FrameConditions p k r v m ε parent t₀ q z₀ zv background prior law coeff good lists

theorem validity_of_valid (h : p.Valid) : Validity p := by
  exact ⟨h.scale, h.scale_limit, h.subpower, h.dimension_nonneg, h.dimension_lt_one, h.rate_pos, h.rate_le_one, h.transverse_pos, h.palette_pos, h.palette_le_one, h.depth_pos, h.defect_pos, h.basic, h.caps, h.prepared, h.nested⟩

theorem valid_of_validity (h : Validity p) : p.Valid := by
  rcases h with ⟨h_scale, h_scale_limit, h_subpower, h_dimension_nonneg, h_dimension_lt_one, h_rate_pos, h_rate_le_one, h_transverse_pos, h_palette_pos, h_palette_le_one, h_depth_pos, h_defect_pos, h_basic, h_caps, h_prepared, h_nested⟩
  exact {
    scale := h_scale
    scale_limit := h_scale_limit
    subpower := h_subpower
    dimension_nonneg := h_dimension_nonneg
    dimension_lt_one := h_dimension_lt_one
    rate_pos := h_rate_pos
    rate_le_one := h_rate_le_one
    transverse_pos := h_transverse_pos
    palette_pos := h_palette_pos
    palette_le_one := h_palette_le_one
    depth_pos := h_depth_pos
    defect_pos := h_defect_pos
    basic := h_basic
    caps := h_caps
    prepared := h_prepared
    nested := h_nested
  }

theorem frames_of_frame {k : ℕ} {r v m ε : ℝ}
    (f : p.ListFrame k r v m ε) : Frames p k r v m ε := by
  exact ⟨f.parent, f.t₀, f.q, f.z₀, f.zv, f.background, f.prior, f.law, f.coeff, f.good, f.lists, f.good_measurable, f.good_subset, f.coeff_measurable, f.prior_probability, f.law_domination, f.time_support, f.good_ae, f.coeff_bound, f.mass_lower, f.q_pos, f.q_eq, f.time_eq, f.background_degree, f.background_bound, f.frame_bound, f.scalarY_eq, f.scalarX_eq, f.original_domination, f.lists_bound, f.lists_ae⟩

theorem frame_of_frames {k : ℕ} {r v m ε : ℝ}
    (h : Frames p k r v m ε) : Nonempty (p.ListFrame k r v m ε) := by
  rcases h with ⟨parent, t₀, q, z₀, zv, background, prior, law, coeff, good, lists, h⟩
  rcases h with ⟨h_good_measurable, h_good_subset, h_coeff_measurable, h_prior_probability, h_law_domination, h_time_support, h_good_ae, h_coeff_bound, h_mass_lower, h_q_pos, h_q_eq, h_time_eq, h_background_degree, h_background_bound, h_frame_bound, h_scalarY_eq, h_scalarX_eq, h_original_domination, h_lists_bound, h_lists_ae⟩
  exact ⟨{
    parent := parent
    t₀ := t₀
    q := q
    z₀ := z₀
    zv := zv
    background := background
    prior := prior
    law := law
    coeff := coeff
    good := good
    lists := lists
    good_measurable := h_good_measurable
    good_subset := h_good_subset
    coeff_measurable := h_coeff_measurable
    prior_probability := h_prior_probability
    law_domination := h_law_domination
    time_support := h_time_support
    good_ae := h_good_ae
    coeff_bound := h_coeff_bound
    mass_lower := h_mass_lower
    q_pos := h_q_pos
    q_eq := h_q_eq
    time_eq := h_time_eq
    background_degree := h_background_degree
    background_bound := h_background_bound
    frame_bound := h_frame_bound
    scalarY_eq := h_scalarY_eq
    scalarX_eq := h_scalarX_eq
    original_domination := h_original_domination
    lists_bound := h_lists_bound
    lists_ae := h_lists_ae }⟩


end Unpacked
end
end Submission.Obl.k4_general_compared_layers_velocity_lists.Split
