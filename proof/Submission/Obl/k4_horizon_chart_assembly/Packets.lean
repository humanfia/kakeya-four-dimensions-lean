import Submission.Obl.k4_horizon_chart_assembly.Defs
import Submission.Lib.K4FinitePlankAtlases

/-!
The supplied greedy hypothesis is repackaged using the accepted atlas geometry.
Assignments and all floors retain the original incidence law.
-/

namespace Submission.Obl.k4_horizon_chart_assembly

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Lib.K4FinitePlankAtlases
open Submission.Lib.K4ContinuousPlanks (InFullTracePlank)

noncomputable section

def packetAssignment {α : Type*} {D m : ℕ} (U : Set α) (b u : α → Plane)
    (p : Fin m → PhysicalPlank D) (i : Fin m) : Set α :=
  U ∩ firstAssignment (fun j => (p j).fitSet b u) i

def packetResidual {α : Type*} {D m : ℕ} (U : Set α) (b u : α → Plane)
    (p : Fin m → PhysicalPlank D) : Set α :=
  {z | z ∈ U ∧ ∀ i, z ∉ (p i).fitSet b u}

theorem packetAssignment_measurable {α : Type*} [MeasurableSpace α] {D m : ℕ}
    {U : Set α} (hU : MeasurableSet U) (b u : α → Plane)
    (hb : Measurable b) (hu : Measurable u) (p : Fin m → PhysicalPlank D) (i : Fin m) :
    MeasurableSet (packetAssignment U b u p i) :=
  hU.inter (measurableSet_firstAssignment _
    (fun j => measurableSet_fullTracePlank b u hb hu _ _ _ _ _ _) i)

theorem packetAssignment_disjoint {α : Type*} {D m : ℕ} (U : Set α)
    (b u : α → Plane) (p : Fin m → PhysicalPlank D) :
    Pairwise (fun i j => Disjoint (packetAssignment U b u p i) (packetAssignment U b u p j)) :=
  fun _ _ h => (firstAssignment_disjoint _ h).mono inter_subset_right inter_subset_right

theorem packetResidual_measurable {α : Type*} [MeasurableSpace α] {D m : ℕ}
    {U : Set α} (hU : MeasurableSet U) (b u : α → Plane)
    (hb : Measurable b) (hu : Measurable u) (p : Fin m → PhysicalPlank D) :
    MeasurableSet (packetResidual U b u p) := by
  have heq : packetResidual U b u p = U ∩ ⋂ i, ((p i).fitSet b u)ᶜ := by
    ext z
    simp [packetResidual]
  rw [heq]
  exact hU.inter (MeasurableSet.iInter (fun i =>
    (measurableSet_fullTracePlank b u hb hu _ _ _ _ _ _).compl))

/-- The finite priority pieces and their residual partition the initial group. -/
theorem packet_mass_identity {α : Type*} [MeasurableSpace α] {D m : ℕ}
    (μ : Measure α) {U : Set α} (hU : MeasurableSet U) (b u : α → Plane)
    (hb : Measurable b) (hu : Measurable u) (p : Fin m → PhysicalPlank D) :
    (∑ i, μ (packetAssignment U b u p i)) + μ (packetResidual U b u p) = μ U := by
  have hpart : (⋃ i, packetAssignment U b u p i) ∪ packetResidual U b u p = U := by
    have hcov : (⋃ i, packetAssignment U b u p i) = U ∩ ⋃ i, (p i).fitSet b u := by
      simp only [packetAssignment, ← inter_iUnion, iUnion_firstAssignment]
    rw [hcov]
    ext z
    simp only [mem_union, mem_inter_iff, mem_iUnion, packetResidual, mem_setOf_eq]
    tauto
  have hdisj : Disjoint (⋃ i, packetAssignment U b u p i) (packetResidual U b u p) := by
    apply Set.disjoint_left.mpr
    intro z hz hr
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact hr.2 i hi.2.1
  have heq := congrArg (fun A => μ A) hpart
  rw [measure_union hdisj (packetResidual_measurable hU b u hb hu p),
    measure_iUnion (packetAssignment_disjoint U b u p)
      (packetAssignment_measurable hU b u hb hu p), tsum_fintype] at heq
  exact heq

/-- Replace the primitive tuple in the hypothesis by physical plank objects. -/
theorem greedy_packets (H : GreedyKernel) {ε : ℝ} (hε : 0 < ε) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ D : ℕ, 2 ≤ D →
    ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
      (b u : α → Plane), Measurable b → Measurable u →
    ∀ U : Set α, MeasurableSet U → (∀ z ∈ U, ‖b z‖ ≤ 1 ∧ ‖u z‖ ≤ 1) →
    ∀ E Gd : Set (α × ℝ), MeasurableSet E → MeasurableSet Gd →
      E ⊆ univ ×ˢ Icc (0 : ℝ) 1 →
    ∀ τ₀ s : ℝ, 0 < τ₀ → (D : ℝ) ^ (-η) ≤ s →
    ∀ F : Finset (ℤ × (Fin 2 → ℤ)),
      (∀ z ∈ E ∩ Gd, z.1 ∈ U →
        (⌊z.2 * (D : ℝ)⌋, fun i : Fin 2 => ⌊(D : ℝ) * (b z.1 + z.2 • u z.1) i⌋) ∈ F) →
    ∃ m : ℕ, ∃ p : Fin m → PhysicalPlank D,
      (∀ i, 2 / (D : ℝ) ≤ (p i).narrow) ∧
      (∀ i, ENNReal.ofReal (τ₀ * (p i).narrow * (p i).wide) ≤
        (ν.prod volume) (E ∩ (packetAssignment U b u p i ×ˢ univ))) ∧
      (ν.prod volume) (E ∩ (packetResidual U b u p ×ˢ univ)) ≤
        (ν.prod volume) (E ∩ Gdᶜ ∩ (packetResidual U b u p ×ˢ univ)) +
        ENNReal.ofReal s * ν (packetResidual U b u p) +
        ENNReal.ofReal (C * τ₀ * (D : ℝ) ^ ε / (s * (D : ℝ) ^ 3) * (F.card : ℝ)) := by
  obtain ⟨η, C, hη, hC, hH⟩ := H ε hε
  refine ⟨η, C, hη, hC, ?_⟩
  intro D hD α _ ν _ b u hb hu U hU hbu E Gd hE hGd hunit τ₀ s hτ₀ hs F hF
  obtain ⟨m, c, w, e₁, e₂, a, β, hwidth, hfloor, hres⟩ :=
    hH D hD α ν b u hb hu U hU hbu E Gd hE hGd hunit τ₀ s hτ₀ hs F hF
  have hD₀ : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  let p : Fin m → PhysicalPlank D := fun i =>
    ⟨c i, w i, e₁ i, e₂ i, a i, β i, (hwidth i).1, (hwidth i).2.1,
      (hwidth i).2.2.1,
      ((div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hD₀.le).trans (hwidth i).2.2.2.1),
      (hwidth i).2.2.2.2.1, (hwidth i).2.2.2.2.2⟩
  refine ⟨m, p, fun i => (hwidth i).2.2.2.1, ?_, ?_⟩
  · exact hfloor
  · exact hres

/-- Integrating out the bounded time interval never exceeds the old prior. -/
theorem incidence_group_le_prior {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] {E : Set (α × ℝ)}
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (A : Set α) :
    (ν.prod volume) (E ∩ (A ×ˢ univ)) ≤ ν A := by
  calc
    _ ≤ (ν.prod volume) (A ×ˢ Icc (0 : ℝ) 1) := by
      apply measure_mono
      intro z hz
      exact ⟨hz.2.1, (hunit hz.1).2⟩
    _ = ν A := by simp [Measure.prod_prod]

/-- The projection is only an integration device: its values are original masses. -/
theorem incidence_projection_apply {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (E : Set (α × ℝ)) {A : Set α} (hA : MeasurableSet A) :
    (((ν.prod volume).restrict E).map Prod.fst) A =
      (ν.prod volume) (E ∩ (A ×ˢ univ)) := by
  rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  tauto

/-- Selected incidence mass plus uncovered incidence mass is exact, without normalization. -/
theorem packet_incidence_identity {α : Type*} [MeasurableSpace α] {D m : ℕ}
    (ν : Measure α) (E : Set (α × ℝ)) {U : Set α} (hU : MeasurableSet U)
    (b u : α → Plane) (hb : Measurable b) (hu : Measurable u)
    (p : Fin m → PhysicalPlank D) :
    (∑ i, (ν.prod volume) (E ∩ (packetAssignment U b u p i ×ˢ univ))) +
      (ν.prod volume) (E ∩ (packetResidual U b u p ×ˢ univ)) =
      (ν.prod volume) (E ∩ (U ×ˢ univ)) := by
  have h := packet_mass_identity (((ν.prod volume).restrict E).map Prod.fst) hU b u hb hu p
  simpa only [incidence_projection_apply ν E hU,
    incidence_projection_apply ν E (packetAssignment_measurable hU b u hb hu p _),
    incidence_projection_apply ν E (packetResidual_measurable hU b u hb hu p)] using h

/-- The number of selected packets is charged to the prior mass of this group.
This bound can be summed over disjoint groups without a group-count loss. -/
theorem packet_count_bound {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] {D m : ℕ} (hD : 2 ≤ D)
    (E : Set (α × ℝ)) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {U : Set α} (hU : MeasurableSet U) (b u : α → Plane)
    (hb : Measurable b) (hu : Measurable u) (p : Fin m → PhysicalPlank D)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hwidth : ∀ i, 2 / (D : ℝ) ≤ (p i).narrow)
    (hfloor : ∀ i, ENNReal.ofReal (τ₀ * (p i).narrow * (p i).wide) ≤
      (ν.prod volume) (E ∩ (packetAssignment U b u p i ×ˢ univ))) :
    (m : ℝ) ≤ (D : ℝ) ^ 2 / (4 * τ₀) * ν.real U := by
  have hD₀ : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  let floor := τ₀ * (2 / (D : ℝ)) ^ 2
  have hf : 0 < floor := by dsimp [floor]; positivity
  have hlow (i : Fin m) : floor ≤ τ₀ * (p i).narrow * (p i).wide := by
    dsimp [floor]
    rw [mul_assoc, pow_two]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hwidth i) ((hwidth i).trans (p i).narrow_le_wide)
        (by positivity) ((by positivity : 0 < 2 / (D : ℝ)).le.trans (hwidth i))) hτ₀.le
  have hsum : ENNReal.ofReal (floor * (m : ℝ)) ≤ ν U := by
    calc
      _ = ∑ i : Fin m, ENNReal.ofReal floor := by
        simp [mul_comm, ENNReal.ofReal_mul hf.le]
      _ ≤ ∑ i : Fin m, (ν.prod volume) (E ∩ (packetAssignment U b u p i ×ˢ univ)) := by
        exact Finset.sum_le_sum (fun i _ => (ENNReal.ofReal_le_ofReal (hlow i)).trans (hfloor i))
      _ ≤ (ν.prod volume) (E ∩ (U ×ˢ univ)) := by
        rw [← packet_incidence_identity ν E hU b u hb hu p]
        exact le_self_add
      _ ≤ ν U := incidence_group_le_prior ν hunit U
  have hmul : floor * (m : ℝ) ≤ ν.real U :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν U)).mp hsum
  have hdiv : (m : ℝ) ≤ ν.real U / floor :=
    (le_div_iff₀ hf).mpr (by simpa only [mul_comm] using hmul)
  convert hdiv using 1 <;> dsimp [floor] <;> field_simp <;> ring

/-- Recenter the containing frame at a member of an arbitrary measurable packet.
This extends the finite-set recentering API to the continuous packets here. -/
theorem physicalPlank_chart_on_set {α : Type*} {D : ℕ} (p : PhysicalPlank D)
    (b u : α → Plane) (A : Set α) (hA : A.Nonempty)
    (hbounded : ∀ z ∈ A, ‖b z‖ ≤ 1 ∧ ‖u z‖ ≤ 1)
    (hfit : A ⊆ p.fitSet b u) (ha : 0 < p.narrow) :
    ∃ c w : Plane, ‖c‖ ≤ 1 ∧ ‖w‖ ≤ 1 ∧ ∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin ((plankFrame (2 * p.narrow) (2 * p.wide) p.axis₁ p.axis₂)⁻¹)
        (b z + t • u z - c - t • w)‖ ≤ 2 := by
  obtain ⟨z₀, hz₀⟩ := hA
  refine ⟨b z₀, u z₀, (hbounded z₀ hz₀).1, (hbounded z₀ hz₀).2, ?_⟩
  intro z hz t ht
  have hd : b z + t • u z - b z₀ - t • u z₀ =
      (b z + t • u z - p.center - t • p.speed) -
      (b z₀ + t • u z₀ - p.center - t • p.speed) := by abel
  rw [hd]
  apply plankFrame_fit (by positivity) (by have := ha.trans_le p.narrow_le_wide; positivity)
    p.unit₁ p.unit₂ p.orthogonal
  · rw [inner_sub_left]
    exact (abs_sub _ _).trans (by linarith [(hfit hz t ht).1, (hfit hz₀ t ht).1])
  · rw [inner_sub_left]
    exact (abs_sub _ _).trans (by linarith [(hfit hz t ht).2, (hfit hz₀ t ht).2])

/-- All selected frames have one common polynomial bound at the mesh scale. -/
theorem doubled_frame_bounds {D : ℕ} (hD : 2 ≤ D) (p : PhysicalPlank D)
    (hwidth : 2 / (D : ℝ) ≤ p.narrow) :
    (∑ i : Fin 2, ∑ j : Fin 2, |plankFrame (2 * p.narrow) (2 * p.wide) p.axis₁ p.axis₂ i j|) ≤ 16 ∧
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|plankFrame (2 * p.narrow) (2 * p.wide) p.axis₁ p.axis₂ i j| +
        |(plankFrame (2 * p.narrow) (2 * p.wide) p.axis₁ p.axis₂)⁻¹ i j|)) ≤ 16 * (D : ℝ) := by
  have hD₀ : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD₂ : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have ha : 0 < p.narrow := (div_pos (by norm_num) hD₀).trans_le hwidth
  have hβ : 0 < p.wide := ha.trans_le p.narrow_le_wide
  have ha₂ := p.narrow_le_wide.trans p.wide_le_two
  have hinv (a : ℝ) (ha : 0 < a) (hlow : 2 / (D : ℝ) ≤ a) : (2 * a)⁻¹ ≤ (D : ℝ) / 4 := by
    rw [← one_div, div_le_iff₀ (by positivity : 0 < 2 * a)]
    have h := (div_le_iff₀ hD₀).mp hlow
    nlinarith
  constructor
  · apply (plankFrame_entries (by positivity) (by positivity) p.unit₁ p.unit₂).trans
    nlinarith [p.wide_le_two]
  · apply (plankFrame_entry_budget (by positivity) (by positivity) p.unit₁ p.unit₂ p.orthogonal).trans
    have hi₁ := hinv p.narrow ha hwidth
    have hi₂ := hinv p.wide hβ (hwidth.trans p.narrow_le_wide)
    nlinarith [p.wide_le_two]

/-- Turn every positive incidence packet into a bounded matrix chart, keeping its
original geometric priority assignment and original determinant floor. -/
theorem packet_matrix_charts {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {D m : ℕ} (hD : 2 ≤ D) (E : Set (α × ℝ))
    {U : Set α} (b u : α → Plane)
    (hbu : ∀ z ∈ U, ‖b z‖ ≤ 1 ∧ ‖u z‖ ≤ 1) (p : Fin m → PhysicalPlank D)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hwidth : ∀ i, 2 / (D : ℝ) ≤ (p i).narrow)
    (hfloor : ∀ i, ENNReal.ofReal (τ₀ * (p i).narrow * (p i).wide) ≤
      (ν.prod volume) (E ∩ (packetAssignment U b u p i ×ˢ univ))) :
    ∃ c w : Fin m → Plane, ∃ Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ,
      ∀ i, Matrix.det (Q i) ≠ 0 ∧ ‖c i‖ + ‖w i‖ ≤ 2 ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, (|Q i e e'| + |(Q i)⁻¹ e e'|)) ≤ 16 * D ∧
        (∑ e : Fin 2, ∑ e' : Fin 2, |Q i e e'|) ≤ 16 ∧
        (∀ z ∈ packetAssignment U b u p i, ∀ t ∈ Icc (0 : ℝ) 1,
          ‖Matrix.toEuclideanLin ((Q i)⁻¹) (b z + t • u z - c i - t • w i)‖ ≤ 2) ∧
        ENNReal.ofReal ((τ₀ / 4) * |Matrix.det (Q i)|) ≤
          (ν.prod volume) (E ∩ (packetAssignment U b u p i ×ˢ univ)) := by
  have hD₀ : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have ha (i : Fin m) : 0 < (p i).narrow :=
    (div_pos (by norm_num) hD₀).trans_le (hwidth i)
  have hβ (i : Fin m) : 0 < (p i).wide := (ha i).trans_le (p i).narrow_le_wide
  have hgeom (i : Fin m) : ∃ c w : Plane, ‖c‖ ≤ 1 ∧ ‖w‖ ≤ 1 ∧
      ∀ z ∈ packetAssignment U b u p i, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖Matrix.toEuclideanLin
          ((plankFrame (2 * (p i).narrow) (2 * (p i).wide) (p i).axis₁ (p i).axis₂)⁻¹)
          (b z + t • u z - c - t • w)‖ ≤ 2 := by
    have hne : (packetAssignment U b u p i).Nonempty := by
      by_contra h
      have hmass := hfloor i
      rw [Set.not_nonempty_iff_eq_empty.mp h] at hmass
      simp only [empty_prod, inter_empty, measure_empty] at hmass
      have : 0 < ENNReal.ofReal (τ₀ * (p i).narrow * (p i).wide) :=
        ENNReal.ofReal_pos.mpr (mul_pos (mul_pos hτ₀ (ha i)) (hβ i))
      exact (not_le_of_gt this) hmass
    exact physicalPlank_chart_on_set (p i) b u _ hne
      (fun z hz => hbu z hz.1) (fun z hz => hz.2.1) (ha i)
  choose c w hc hw hfit using hgeom
  let Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ := fun i =>
    plankFrame (2 * (p i).narrow) (2 * (p i).wide) (p i).axis₁ (p i).axis₂
  have hdet (i : Fin m) : |Matrix.det (Q i)| = 4 * (p i).narrow * (p i).wide := by
    change |Matrix.det (plankFrame (2 * (p i).narrow) (2 * (p i).wide) (p i).axis₁ (p i).axis₂)| = _
    rw [plankFrame_abs_det (mul_pos (by norm_num) (ha i))
      (mul_pos (by norm_num) (hβ i)) (p i).unit₁ (p i).unit₂ (p i).orthogonal]
    ring
  refine ⟨c, w, Q, fun i => ?_⟩
  have hbounds := doubled_frame_bounds hD (p i) (hwidth i)
  refine ⟨abs_pos.mp (by rw [hdet]; exact mul_pos (mul_pos (by norm_num) (ha i)) (hβ i)), by linarith [hc i, hw i],
    hbounds.2, hbounds.1, hfit i, ?_⟩
  have heq : (τ₀ / 4) * |Matrix.det (Q i)| = τ₀ * (p i).narrow * (p i).wide := by
    rw [hdet]
    ring
  rw [heq]
  exact hfloor i

end
end Submission.Obl.k4_horizon_chart_assembly
