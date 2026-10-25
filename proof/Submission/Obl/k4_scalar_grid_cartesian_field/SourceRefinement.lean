import Submission.Obl.k4_scalar_grid_cartesian_field.SourcePacket
import Submission.Obl.k4_scalar_grid_cartesian_field.RegisteredSupport
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketCellBudget
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketPalette

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial

noncomputable def fineCellBudget (K L H₀ : ℝ) : ℝ := 8000 * L ^ 3 * H₀ ^ 4 * K
noncomputable def sourcePaletteBudget (K L H₀ H : ℝ) : ℝ := 32 * K * fineCellBudget K L H₀ * H

/-- The first fine-cell pruning keeps qualified low-gradient incidences and restores their original palette. -/
structure SourceRefinement {data : Data} {k M : ℕ}
    {G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (data.W k) → Set Incidence} {B ε L H : ℝ}
    (s : SourcePacket data k M G E B ε L H) (H₀ : ℝ) (Band : Set ℝ) where
  S₀ : Set Incidence
  measurable_S₀ : MeasurableSet S₀
  subset_source : S₀ ⊆ s.S
  mass_floor : ENNReal.ofReal (1 / (16 * H)) *
    (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 s.i) (data.A k 1 s.i)) ≤
      data.ρ k (data.γ k 1 s.i) S₀
  fine_cells : Finset (Fin 3 → ℤ)
  fine_cover : ∀ᵐ x ∂(data.ρ k (data.γ k 1 s.i)).restrict S₀,
    physCube (data.N k) B x ∈ fine_cells
  fine_budget : ENNReal.ofReal ((data.N k ^ (-B)) ^ (2 + data.d)) * fine_cells.card ≤
    ENNReal.ofReal (fineCellBudget (data.K k) L H₀) *
      (ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 s.i) (data.A k 1 s.i))
  palette : ∀ r ∈ Band, ∀ (q : Fin 3 → ℤ) (c : ℤ),
    (data.ρ k (data.γ k 1 s.i)).restrict S₀ {x | physCube (data.N k) B x = q ∧
      x.1.2 1 ∈ vel data k r c} ≤
      ENNReal.ofReal (sourcePaletteBudget (data.K k) L H₀ H) *
        (data.ρ k (data.γ k 1 s.i)).restrict S₀ {x | physCube (data.N k) B x = q} *
          data.π k (data.γ k 1 s.i) (vel data k r c)

/-- Hereditary original support counts pay for a mass-preserving palette restoration on the source packet. -/
theorem refine_source_packet {data : Data} {k M : ℕ}
    {G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    {E : (k : ℕ) → Fin (data.W k) → Set Incidence} {B ε L H H₀ : ℝ}
    (s : SourcePacket data k M G E B ε L H) (hN : 2 ≤ data.N k) (hκ : data.κ ≤ 1)
    (hd : 0 ≤ data.d) (hdone : data.d ≤ 1) (hH₀ : 1 ≤ H₀) (hH : 1 ≤ H)
    (hL : 2 * data.K k ≤ L) (hB : 50 ≤ B) (m : ℕ) (hm : 1 ≤ m)
    (hstep : data.N k ^ (1 / (m : ℝ)) ≤ H₀) (E₀ : Set Incidence) (hsource : s.S ⊆ E₀)
    (hprep : RegisteredSupportControl ((data.ρ k (data.γ k 1 s.i)).restrict E₀)
      (fun x => ![x.2, scalarY x.1 x.2]) (fun x => scalarX x.1 x.2)
      (data.N k) H₀ data.d m (B + 2)) (Band : Set ℝ)
    (hcap : ∀ r ∈ Band, ∀ (q : Fin 3 → ℤ) (c : ℤ), data.ρ k (data.γ k 1 s.i)
      {x | physCube (data.N k) B x = q ∧ x.1.2 1 ∈ vel data k r c} ≤
      ENNReal.ofReal (data.K k * (data.N k ^ (-B)) ^ (2 + data.d)) *
        data.π k (data.γ k 1 s.i) (vel data k r c)) : Nonempty (SourceRefinement s H₀ Band) := by
  classical
  let ρ := data.ρ k (data.γ k 1 s.i)
  let μ := ρ.restrict s.S
  let P := ENNReal.ofReal (packetLength data k) * data.ν k (data.γ k 1 s.i) (data.A k 1 s.i)
  let J := fineCellBudget (data.K k) L H₀
  have hNp : 0 < data.N k := by linarith
  have hK := s.original.budget_one
  have hKpos : 0 < data.K k := by linarith
  have hKL : data.K k ≤ L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hHpos : 0 < H := by linarith
  have hJpos : 0 < J := by dsimp [J, fineCellBudget]; positivity
  have hh := s.original.positive_horizon
  have hδ : 0 < data.N k ^ (-1 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hbB : 0 < data.N k ^ (-B) := Real.rpow_pos_of_pos hNp _
  have hscale : data.N k ^ (-1 : ℝ) ≤ L * packetLength data k := by
    have hδκ : data.N k ^ (-1 : ℝ) ≤ data.N k ^ (-data.κ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ data.N k) (by linarith)
    have hs := (div_le_iff₀ hKpos).mp s.original.horizon_lower
    have hδh : data.N k ^ (-1 : ℝ) ≤ data.K k * packetLength data k := by nlinarith
    exact hδh.trans (mul_le_mul_of_nonneg_right hKL hh.le)
  have hbase : ∀ x ∈ s.S, ∀ e, |(![x.2, scalarY x.1 x.2] : Fin 2 → ℝ) e -
      originalOrigin data k s.i e| ≤ L * packetLength data k := by
    intro x hx e
    have hp := s.subset_packet hx
    have hn := s.original.normalized_bound x.1 hp.1 x.2 hp.2 e
    change |((![x.2, scalarY x.1 x.2] : Fin 2 → ℝ) e - originalOrigin data k s.i e) /
      packetLength data k| ≤ 2 * data.K k at hn
    rw [abs_div, abs_of_pos hh] at hn
    exact ((div_le_iff₀ hh).mp hn).trans (mul_le_mul_of_nonneg_right hL hh.le)
  have hfit : ∀ x ∈ s.S, |scalarX x.1 x.2 - eval ![x.2, scalarY x.1 x.2] (data.F k 1 s.i)| ≤
      L * data.N k ^ (-1 : ℝ) := by
    intro x hx
    have hp := s.subset_packet hx
    exact ((s.original.fit x.1 hp.1 x.2 hp.2).2).trans (mul_le_mul_of_nonneg_right hKL hδ.le)
  have hμ : μ ≤ ρ.restrict E₀ := Measure.restrict_mono_set _ hsource
  have hsupport : μ s.Sᶜ = 0 := ae_iff.mp (ae_restrict_mem s.measurable_S)
  obtain ⟨hfin, hcount⟩ := registered_packet_fine_count (B := B) (R := B + 2) (ρ.restrict E₀) μ hμ s.S hsupport
    (fun x => ![x.2, scalarY x.1 x.2]) (fun x => scalarX x.1 x.2) (data.F k 1 s.i)
    s.original.quadratic hN hH₀ hm hstep hd hdone hh hLone hscale (by linarith) (by linarith)
    (originalOrigin data k s.i) hbase hfit s.gradient hprep
  let F := hfin.toFinset
  have hcover : ∀ᵐ x ∂μ, physCube (data.N k) B x ∈ F := by
    filter_upwards [ae_active_code μ (physCube (data.N k) B)] with x hx
    exact hfin.mem_toFinset.mpr hx
  have hnum : (F.card : ℝ) ≤ (8000 * L ^ 3 * H₀ ^ 4) *
      (packetLength data k / data.N k ^ (-B)) ^ 2 * (data.N k ^ (-1 : ℝ) / data.N k ^ (-B)) ^ data.d := by
    simpa only [F, ← Set.ncard_eq_toFinset_card _ hfin] using hcount
  have hδd : (data.N k ^ (-1 : ℝ)) ^ data.d = data.N k ^ (-data.d) := by
    rw [← Real.rpow_mul hNp.le]
    congr 1
    ring
  have hprior : ENNReal.ofReal ((data.N k ^ (-1 : ℝ)) ^ data.d * packetLength data k / data.K k) ≤
      data.ν k (data.γ k 1 s.i) (data.A k 1 s.i) := by simpa only [hδd] using s.original.prior_lower
  have hbudget : ENNReal.ofReal ((data.N k ^ (-B)) ^ (2 + data.d)) * F.card ≤ ENNReal.ofReal J * P := by
    have h := packet_cell_count_budget (by positivity : 0 ≤ 8000 * L ^ 3 * H₀ ^ 4) hKpos hh.le hδ hbB
      F.card (data.ν k (data.γ k 1 s.i) (data.A k 1 s.i)) hnum hprior
    calc
      _ ≤ ENNReal.ofReal (J * packetLength data k) * data.ν k (data.γ k 1 s.i) (data.A k 1 s.i) := h
      _ = _ := by rw [ENNReal.ofReal_mul hJpos.le, mul_assoc]
  letI := s.original.probability_ν
  have hPtop : P ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  let Index := Band × ℤ
  let event : Index → Set Incidence := fun v => {x | x.1.2 1 ∈ vel data k v.1.val v.2}
  let prior : Index → ENNReal := fun v => data.π k (data.γ k 1 s.i) (vel data k v.1.val v.2)
  have hraw (q : Fin 3 → ℤ) (v : Index) : μ ((physCube (data.N k) B) ⁻¹' {q} ∩ event v) ≤
      ENNReal.ofReal (data.K k * (data.N k ^ (-B)) ^ (2 + data.d)) * prior v :=
    (Measure.restrict_le_self _).trans (hcap v.1.val v.1.property q v.2)
  have hmass : ENNReal.ofReal (1 / (8 * H)) * P ≤ μ univ := by
    simpa only [μ, Measure.restrict_apply_univ] using s.mass_floor
  obtain ⟨Keep, hKeep, hkept, hpalette⟩ := packet_palette_pruning μ (physCube (data.N k) B)
    (measurable_physCube _ _) F hcover P hPtop (by positivity : 0 < 1 / (8 * H)) hJpos hKpos.le
    (Real.rpow_pos_of_pos hbB _) hmass hbudget event prior hraw
  let S₀ := Keep ∩ s.S
  have heq : μ.restrict Keep = ρ.restrict S₀ := Measure.restrict_restrict hKeep
  have hratio : 4 * data.K k * J / (1 / (8 * H)) = sourcePaletteBudget (data.K k) L H₀ H := by
    dsimp [sourcePaletteBudget]
    field_simp
    <;> ring
  refine ⟨⟨S₀, hKeep.inter s.measurable_S, inter_subset_right, ?_, F, ?_, hbudget, ?_⟩⟩
  · have hhalf : (1 / (8 * H)) / 2 = 1 / (16 * H) := by ring
    simpa only [heq, Measure.restrict_apply_univ, hhalf] using hkept
  · exact hcover.filter_mono (ae_mono (by rw [← heq]; exact Measure.restrict_le_self))
  · intro r hr q c
    have h := hpalette q ((⟨r, hr⟩, c) : Index)
    simpa only [heq, hratio, event, prior, Set.preimage, Set.mem_singleton_iff, Set.setOf_and] using h

end Submission.Obl.k4_scalar_grid_cartesian_field
