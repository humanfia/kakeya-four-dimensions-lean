-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.Core; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.FiberLists

/-!
# Two core steps of the common-field application

* `group_cell_cap_weight`: the original mass of a normalized base cell of side `δ` on the two
  native-signal groups of a block is at most `67200 K^3 N^(r - s) δ^2` times the block's
  reference weight, when the groups confine the native signal to `N^(-s)` on the cell's
  transverse slabs.
* `ConsensusLaw.keep_groups`: restricting a consensus law to the native states keeping at
  least half of their mass on a set `G` of small original loss keeps a quarter of the mass
  floor (`1 / (8 H)` of the block's weight), keeps conditional palette domination with a
  factor two, and is carried by `G`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- **The base cell cap on the groups, in units of the block's reference weight.** -/
theorem group_cell_cap_weight (h : p.Valid) {k : ℕ} {r : ℝ} (a : ParentGeometry p k r)
    (Q : Fin (p.n k r)) {E : Fin 2 → Set (α × ℝ)}
    (hEsub : ∀ e, E e ⊆ p.B k r Q ×ˢ block (p.T k r) (p.j k r Q))
    {δ δU δf s : ℝ} (hδ : 0 < δ) (hδU : 0 < δU) (hδf : 0 < δf) (hs : s ≤ r)
    (hosc : ∀ e, ∀ z ∈ E e, ∀ z' ∈ E e,
      (∀ c : Fin 3, |p.base k z.1 z.2 c - p.base k z'.1 z'.2 c| ≤
        (p.K k + 1) ^ 2 * p.blockLen k r * δ + p.blockWidth k r * δU) →
      |p.signal k z.1 z.2 - p.signal k z'.1 z'.2| ≤ p.N k ^ (-s))
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      p.μ k {ω | (fun i => ⌊p.finePoint k ω i / δf⌋) = q ∧
        ⌊p.signal k ω.1 ω.2 / p.N k ^ (-s)⌋ = j} ≤
        ENNReal.ofReal (p.K k * (p.N k ^ (-s)) ^ p.d * δf ^ 3))
    (hfine1 : (p.K k + p.K k ^ 2) * δf ≤ p.blockLen k r * δ)
    (hfine2 : (p.K k + p.K k ^ 2) * δf ≤ p.blockWidth k r * δU)
    (hshear : p.K k * p.blockLen k r * δ ≤ p.blockWidth k r * δU) (hδUK : δU ≤ p.K k)
    (q0 q1 : ℤ) :
    p.μ k ({ω | ⌊p.tauN k r Q ω / δ⌋ = q0 ∧ ⌊p.zetaN k r Q ω / δ⌋ = q1} ∩ ⋃ e, E e) ≤
      ENNReal.ofReal (67200 * p.K k ^ 3 * p.N k ^ (r - s) * δ ^ 2) * p.blockWeight k r Q := by
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [h.scale k]
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hK0 : 0 < p.K k := by linarith
  have hq := p.common_blockLen_pos k r
  have hg : 0 < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hN _
  have hw : p.blockWidth k r = p.blockLen k r * p.N k ^ (-p.ℓ * r) := rfl
  have hw0 : 0 < p.blockWidth k r := by rw [hw]; positivity
  have hΔ : 0 < p.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hd0 := h.dimension_nonneg
  have hd1 := h.dimension_lt_one.le
  have hcc := group_cell_cap h a Q hEsub hδ hδU hδf hΔ hosc hcap hfine1 hfine2 q0 q1
  refine hcc.trans ?_
  set K := p.K k
  set q := p.blockLen k r
  set w := p.blockWidth k r
  set g := p.N k ^ (-p.ℓ * r)
  set Δd := (p.N k ^ (-s)) ^ p.d with hΔd
  set ad := (p.N k ^ (-r)) ^ p.d with had
  have hΔd0 : 0 ≤ Δd := by positivity
  have had0 : 0 < ad := by positivity
  -- the dimension factor
  have hdim : Δd ≤ p.N k ^ (r - s) * ad := by
    rw [hΔd, had, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    nlinarith
  -- the real bound
  have h2 : 2 * K / δU + 2 ≤ 4 * K / δU := by
    have : 2 ≤ 2 * K / δU := by
      rw [le_div_iff₀ hδU]
      linarith
    have he : 4 * K / δU = 2 * K / δU + 2 * K / δU := by ring
    linarith
  have hslab : K * q * δ + w * δU ≤ 2 * (w * δU) := by linarith
  have hreal : (2 * K / δU + 2) * 2 * (4200 * (K * Δd) * (q * δ) * (q * δ) *
      (K * q * δ + w * δU)) ≤ 67200 * K ^ 3 * p.N k ^ (r - s) * δ ^ 2 * (q * (ad * q ^ 2 * g / K)) := by
    calc (2 * K / δU + 2) * 2 * (4200 * (K * Δd) * (q * δ) * (q * δ) * (K * q * δ + w * δU)) ≤
          (4 * K / δU) * 2 * (4200 * (K * Δd) * (q * δ) * (q * δ) * (2 * (w * δU))) := by
          gcongr
      _ = 67200 * K ^ 2 * Δd * q ^ 2 * δ ^ 2 * w := by
          field_simp
          ring
      _ ≤ 67200 * K ^ 2 * (p.N k ^ (r - s) * ad) * q ^ 2 * δ ^ 2 * w := by gcongr
      _ = 67200 * K ^ 3 * p.N k ^ (r - s) * δ ^ 2 * (q * (ad * q ^ 2 * g / K)) := by
          rw [hw]
          field_simp
  have hprior := a.prior_lower Q
  have hq' : ((2 : ℝ) ^ p.T k r)⁻¹ = q := rfl
  rw [hq'] at hprior
  calc ENNReal.ofReal ((2 * K / δU + 2) * 2 * (4200 * (K * Δd) * (q * δ) * (q * δ) *
        (K * q * δ + w * δU))) ≤
      ENNReal.ofReal (67200 * K ^ 3 * p.N k ^ (r - s) * δ ^ 2 * (q * (ad * q ^ 2 * g / K))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (67200 * K ^ 3 * p.N k ^ (r - s) * δ ^ 2) *
          (ENNReal.ofReal q * ENNReal.ofReal (ad * q ^ 2 * g / K)) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 67200 * K ^ 3 * p.N k ^ (r - s) * δ ^ 2),
          ENNReal.ofReal_mul hq.le]
    _ ≤ ENNReal.ofReal (67200 * K ^ 3 * p.N k ^ (r - s) * δ ^ 2) * p.blockWeight k r Q := by
        gcongr
        unfold blockWeight
        exact mul_le_mul' le_rfl hprior

/-- **Keeping half-states on a set of small loss.** -/
theorem ConsensusLaw.keep_groups (h : p.Valid) {k : ℕ} {r u v m H : ℝ}
    {s : p.ComparedSample k r u v m H} {βb w mv E C : ℝ} (c : p.ConsensusLaw k s βb w mv E C)
    {G : Set (α × ℝ)} (hG : MeasurableSet G) {Lf : ℝ}
    (hBm : MeasurableSet (p.B k r c.block))
    (hBA : p.B k r c.block ⊆ p.A k r c.block)
    (hloss : p.μ k ((p.B k r c.block ×ˢ Parent.block (p.T k r) (p.j k r c.block)) \ G) ≤
      p.μ k (p.B k r c.block ×ˢ Parent.block (p.T k r) (p.j k r c.block)) * ENNReal.ofReal Lf)
    (hnum : 24 * p.K k * H * Lf ≤ 1) (hH : 0 < H) :
    ∃ Keep : Set (α × ℝ), MeasurableSet Keep ∧ Keep ⊆ G ∧
      ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block ≤ c.law Keep ∧
      ∀ (σ : Fin 4 → ℤ) (j : ℤ),
        (c.law.restrict Keep) {ω | p.nativeState k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) ω = σ ∧
            ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋ = j} ≤
          2 * ENNReal.ofReal C *
            (c.law.restrict Keep) {ω | p.nativeState k r c.block (p.N k ^ (-βb))
              (p.N k ^ (-w)) ω = σ} *
            p.π k {x | ⌊x / p.N k ^ (-mv)⌋ = j} := by
  have := c.finite
  have hK : 1 ≤ p.K k := h.subpower.1 k
  set ns := p.nativeState k r c.block (p.N k ^ (-βb)) (p.N k ^ (-w)) with hns
  have hnsm : Measurable ns := p.measurable_nativeState (h.basic k).1 r c.block _ _
  set Keep := FieldCommon.keepSet c.law ns G ∩ G with hKeep
  have hKeepm : MeasurableSet Keep := (FieldCommon.measurableSet_keepSet c.law hnsm G).inter hG
  refine ⟨Keep, hKeepm, inter_subset_right, ?_, ?_⟩
  · -- the mass floor
    set P := p.B k r c.block ×ˢ Parent.block (p.T k r) (p.j k r c.block) with hP
    have hPm : MeasurableSet P := hBm.prod measurableSet_Icc
    have hsupp : c.law Pᶜ = 0 := by
      have hae : ∀ᵐ ω ∂c.law, ω ∈ P := by
        filter_upwards [c.support] with ω hω
        exact ⟨hω.1, hω.2.1⟩
      exact ae_iff.mp hae
    have hle : c.law ≤ p.μ k := c.le_law.trans (s.le_rho.trans (h.basic k).2.2.2.2.1)
    have hbad : c.law Gᶜ ≤ ENNReal.ofReal (p.K k * Lf) * p.blockWeight k r c.block := by
      calc c.law Gᶜ = c.law (Gᶜ ∩ P) := (measure_inter_conull hsupp).symm
        _ ≤ p.μ k (Gᶜ ∩ P) := hle _
        _ = p.μ k (P \ G) := by rw [sdiff_eq_compl_inter]
        _ ≤ p.μ k P * ENNReal.ofReal Lf := hloss
        _ ≤ ENNReal.ofReal (p.K k) * (ENNReal.ofReal ((2 : ℝ) ^ p.T k r)⁻¹ *
              p.ν k (p.A k r c.block)) * ENNReal.ofReal Lf := by
            gcongr
            exact h.block_mass_le c.block hBA
        _ = ENNReal.ofReal (p.K k * Lf) * p.blockWeight k r c.block := by
            rw [ENNReal.ofReal_mul (by linarith)]
            unfold blockWeight blockLen
            ring
    have hmass := FieldCommon.keepSet_mass c.law hnsm hG
    have hfloor := c.mass_lower
    have hbw : p.blockWeight k r c.block ≠ ⊤ := blockWeight_ne_top h k r c.block
    have hsplit : ENNReal.ofReal (1 / (4 * H)) =
        ENNReal.ofReal (1 / (8 * H)) + ENNReal.ofReal (1 / (8 * H)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    have h3 : 3 * ENNReal.ofReal (p.K k * Lf) ≤ ENNReal.ofReal (1 / (8 * H)) := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hkey : ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block +
        ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block ≤
        c.law Keep + ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block := by
      calc ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block +
            ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block =
            ENNReal.ofReal (1 / (4 * H)) * p.blockWeight k r c.block := by
            rw [hsplit, add_mul]
        _ ≤ c.law univ := hfloor
        _ ≤ c.law Keep + 3 * c.law Gᶜ := hmass
        _ ≤ c.law Keep + 3 * (ENNReal.ofReal (p.K k * Lf) * p.blockWeight k r c.block) := by
            gcongr
        _ = c.law Keep + (3 * ENNReal.ofReal (p.K k * Lf)) * p.blockWeight k r c.block := by
            ring
        _ ≤ c.law Keep + ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block := by
            gcongr
    have hfin : ENNReal.ofReal (1 / (8 * H)) * p.blockWeight k r c.block ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbw
    rw [add_comm (c.law Keep)] at hkey
    exact (ENNReal.add_le_add_iff_left hfin).mp hkey
  · -- domination
    intro σ j
    exact FieldCommon.half_domination c.law (c.law.restrict Keep) Measure.restrict_le_self ns
      (fun ω => ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋) (fun j => p.π k {x | ⌊x / p.N k ^ (-mv)⌋ = j})
      (ENNReal.ofReal C) (FieldCommon.keepSet_half c.law hnsm hG) c.domination σ j

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
